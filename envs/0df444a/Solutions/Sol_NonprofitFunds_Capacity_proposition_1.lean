-- Prove2me | solution 1 for NonprofitFunds.Capacity.proposition_1
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T22:42:07.07791+00:00
-- url     : https://prove2.me/submissions/e3ce17d1-8d37-4d8a-8239-56f034230c60

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

set_option autoImplicit false

/-!
Counterexample to `NonprofitFunds.Capacity.proposition_1`.

Data: `r = 1/100`, `B1 = 2`, `psi1 = 2`, `m ≡ 1`, `delta = sqrt`, `phi x = 1 + 99 x (2 - x)`,
`μ = Exp(1/10)`.  All standing assumptions hold, and every `k1 ≥ 0` is admissible.

* At `k1 = 0` the cap `θ = 0` forces `p = 0`, and `B̂2 = f - 1 ≥ 0` forces `a = 0`: the optimum has
  `a = 0`, so clause (a) forces `kl ≤ 0`.
* At `k1 = 17/10` every optimum has `a > 0` (the point `p = 22/25, a = 9/100, f = 3/100` beats every
  allocation with `a = 0`) and `(r+1) p < θ = 101/100` (the cap would need `p = 1`, hence `a = 0`).
  Since `kl ≤ 0 < 17/10`, clauses (b) and (c) both demand `a = 0`: contradiction.
-/

namespace NPF657

open MeasureTheory ProbabilityTheory Filter Topology NonprofitFunds.Capacity

/-! ### Generic `Emin` facts under `Standing` -/

section Generic

variable (P : Params)

lemma st_prob (hP : P.Standing) : IsProbabilityMeasure P.μ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -, -, -⟩ := hP
  exact h

lemma st_neg (hP : P.Standing) : P.μ (Set.Iio 0) = 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -, -⟩ := hP
  exact h

lemma ae_nonneg (hP : P.Standing) : ∀ᵐ x ∂P.μ, 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  exact st_neg P hP

lemma integrable_min (hP : P.Standing) (y : ℝ) : Integrable (fun x => min x y) P.μ := by
  haveI := st_prob P hP
  refine Integrable.mono' (integrable_const (|y|))
    (by fun_prop : Continuous fun x : ℝ => min x y).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg P hP] with x hx
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rcases le_total 0 y with hy | hy
    · exact le_min (by linarith [abs_nonneg y]) (by linarith [abs_nonneg y])
    · rw [abs_of_nonpos hy]; exact le_min (by linarith) (by linarith)
  · exact (min_le_right x y).trans (le_abs_self y)

lemma Emin_sub (hP : P.Standing) (y1 y2 : ℝ) :
    P.Emin y2 - P.Emin y1 = ∫ x, (min x y2 - min x y1) ∂P.μ := by
  unfold Params.Emin
  rw [integral_sub (integrable_min P hP y2) (integrable_min P hP y1)]

lemma Emin_mono (hP : P.Standing) {y1 y2 : ℝ} (h : y1 ≤ y2) : P.Emin y1 ≤ P.Emin y2 :=
  integral_mono (integrable_min P hP y1) (integrable_min P hP y2)
    (fun x => min_le_min_left x h)

lemma Emin_super (hP : P.Standing) (y z : ℝ) :
    P.Emin z ≤ P.Emin y + P.μ.real (Set.Ioi y) * (z - y) := by
  haveI := st_prob P hP
  have h := Emin_sub P hP y z
  have hle : ∫ x, (min x z - min x y) ∂P.μ ≤
      ∫ x, (Set.Ioi y).indicator (fun _ => z - y) x ∂P.μ := by
    refine integral_mono ((integrable_min P hP z).sub (integrable_min P hP y))
      ((integrable_const (z - y)).indicator measurableSet_Ioi) (fun x => ?_)
    simp only
    by_cases hx : x ∈ Set.Ioi y
    · rw [Set.indicator_of_mem hx]
      have hx' : y < x := hx
      rw [min_eq_right hx'.le]; linarith [min_le_right x z]
    · rw [Set.indicator_of_notMem hx]
      have hx' : x ≤ y := not_lt.1 hx
      rw [min_eq_left hx']; linarith [min_le_left x z]
  rw [integral_indicator_const _ measurableSet_Ioi, smul_eq_mul] at hle
  linarith

end Generic

/-! ### The counterexample -/

/-- The donation multiplier `φ(x) = 1 + 99 x (2 - x)`. -/
noncomputable def phiC (x : ℝ) : ℝ := 1 + 99 * (x * (2 - x))

/-- The counterexample parameters. -/
noncomputable def Pc : Params where
  r := 1 / 100
  B1 := 2
  psi1 := 2
  m := fun _ => 1
  delta := fun a => Real.sqrt a
  phi := phiC
  μ := expMeasure (1 / 10)

lemma Pc_r : Pc.r = 1 / 100 := rfl
lemma Pc_B1 : Pc.B1 = 2 := rfl
lemma Pc_psi1 : Pc.psi1 = 2 := rfl
lemma Pc_m (x : ℝ) : Pc.m x = 1 := rfl
lemma Pc_delta (x : ℝ) : Pc.delta x = Real.sqrt x := rfl
lemma Pc_phi (x : ℝ) : Pc.phi x = 1 + 99 * (x * (2 - x)) := rfl
lemma Pc_mu : Pc.μ = expMeasure (1 / 10) := rfl

instance : IsProbabilityMeasure (expMeasure (1 / 10)) :=
  isProbabilityMeasure_expMeasure (by norm_num)

/-- The tail of `Exp(1/10)`. -/
lemma tail_eq {y : ℝ} (hy : 0 ≤ y) :
    (expMeasure (1 / 10)).real (Set.Ioi y) = Real.exp (-(1 / 10 * y)) := by
  have h1 := cdf_expMeasure_eq (r := 1 / 10) (by norm_num) y
  rw [cdf_eq_real, if_pos hy] at h1
  rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, h1]
  ring

lemma Iic0 : (expMeasure (1 / 10)) (Set.Iic 0) = 0 := by
  have h1 := cdf_expMeasure_eq (r := 1 / 10) (by norm_num) 0
  rw [cdf_eq_real, if_pos le_rfl, mul_zero, neg_zero, Real.exp_zero, sub_self] at h1
  rw [measureReal_def] at h1
  rcases (ENNReal.toReal_eq_zero_iff _).1 h1 with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

lemma deriv_sqrt_eq {x : ℝ} (hx : 0 < x) : deriv (fun a => Real.sqrt a) x = (2 * Real.sqrt x)⁻¹ := by
  rw [(Real.hasDerivAt_sqrt hx.ne').deriv, one_div]

lemma sqrt_deriv_tendsto : Tendsto (deriv (fun a => Real.sqrt a)) (𝓝[>] 0) atTop := by
  have h2 : Tendsto (fun x : ℝ => 2 * Real.sqrt x) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun x : ℝ => 2 * Real.sqrt x) (𝓝 0) (𝓝 (2 * Real.sqrt 0)) :=
        (continuous_const.mul Real.continuous_sqrt).tendsto 0
      rw [Real.sqrt_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
      show 0 < 2 * Real.sqrt x
      linarith
  have h3 := tendsto_inv_nhdsGT_zero.comp h2
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [deriv_sqrt_eq hx]
  rfl

lemma Pc_standing : Pc.Standing := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Pc_r]; norm_num
  · rw [Pc_B1]; norm_num
  · rw [Pc_psi1]; norm_num
  · exact convexOn_const 1 (convex_Ici 0)
  · intro x _ y _ _; simp [Pc_m]
  · rw [Pc_m]; norm_num
  · rw [Pc_delta]; exact Real.sqrt_zero
  · exact Real.strictConcaveOn_sqrt
  · intro x hx y _ hxy
    exact Real.sqrt_lt_sqrt hx hxy
  · exact sqrt_deriv_tendsto
  · rw [Pc_phi]; norm_num
  · intro x hx
    rw [Pc_phi]
    have h0 : 0 < x := hx.1
    have h1 : x ≤ 1 := hx.2
    nlinarith
  · intro x hx y hy hxy
    rw [Pc_phi, Pc_phi]
    have := hx.2; have := hy.2
    nlinarith
  · refine ⟨convex_Icc 0 1, fun x _ y _ hxy a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, Pc_phi]
    have hab' : b = 1 - a := by linarith
    subst hab'
    have hd : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hxy
      positivity
    have hp : 0 < a * (1 - a) * (x - y) ^ 2 := mul_pos (mul_pos ha hb) hd
    nlinarith
  · exact continuousOn_const
  · exact contDiffOn_const
  · exact Real.continuous_sqrt.continuousOn
  · intro x hx
    exact (Real.contDiffAt_sqrt (ne_of_gt hx)).contDiffWithinAt
  · show ContinuousOn phiC _
    unfold phiC
    fun_prop
  · show ContDiffOn ℝ 2 phiC _
    unfold phiC
    exact ContDiff.contDiffOn (by fun_prop)
  · show IsProbabilityMeasure (expMeasure (1 / 10))
    infer_instance
  · show expMeasure (1 / 10) (Set.Iio 0) = 0
    exact measure_mono_null Set.Iio_subset_Iic_self Iic0
  · show expMeasure (1 / 10) ≪ volume
    unfold expMeasure gammaMeasure
    exact withDensity_absolutelyContinuous _ _
  · intro x hx
    show 0 < expMeasure (1 / 10) (Set.Ioi x)
    have h := tail_eq hx
    rw [measureReal_def] at h
    have hpos : 0 < ((expMeasure (1 / 10)) (Set.Ioi x)).toReal := by
      rw [h]; exact Real.exp_pos _
    exact ENNReal.toReal_pos_iff.1 hpos |>.1

lemma Pc_bhat1 (k : ℝ) : Pc.Bhat1 k = 1 := by
  unfold Params.Bhat1; rw [Pc_B1, Pc_m]; norm_num

lemma Pc_adm {k : ℝ} (hk : 0 ≤ k) : Pc.Admissible k := ⟨hk, by rw [Pc_m, Pc_B1]; norm_num⟩

/-- At `k1 = 0` every feasible allocation has `a = 0`. -/
lemma feas0 {p a f : ℝ} (h : Pc.Feasible2 0 p a f) : a = 0 := by
  obtain ⟨hp, ha, hf, hsum, hth, hb2, -⟩ := h
  rw [Pc_bhat1] at hsum
  have htheta : Pc.theta 0 = 0 := by
    unfold Params.theta; rw [Pc_psi1, Pc_bhat1, Pc_r]; norm_num
  rw [htheta, Pc_r] at hth
  have hp0 : p = 0 := by nlinarith
  subst hp0
  unfold Params.Bhat2 Params.D at hb2
  rw [Pc_m, zero_div, Pc_phi] at hb2
  norm_num at hb2
  linarith

/-- The value of the special allocation `(22/25, 9/100, 3/100)` at `k1 = 17/10`. -/
lemma special_Y :
    (Pc.r + 1) * Pc.Bhat2 (17 / 10) (22 / 25) (9 / 100) (3 / 100) = 12355027 / 6250000 := by
  unfold Params.Bhat2 Params.D
  rw [Pc_m, Pc_phi, Pc_r]
  norm_num

lemma special_feas : Pc.Feasible2 (17 / 10) (22 / 25) (9 / 100) (3 / 100) := by
  have hth : Pc.theta (17 / 10) = 101 / 100 := by
    unfold Params.theta; rw [Pc_psi1, Pc_bhat1, Pc_r]; norm_num
  have hY := special_Y
  have hs : Real.sqrt (9 / 100) = 3 / 10 := by
    rw [show (9 / 100 : ℝ) = (3 / 10) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [Pc_bhat1]; norm_num
  · rw [hth, Pc_r]; norm_num
  · unfold Params.Bhat2 Params.D
    rw [Pc_m, Pc_phi]
    norm_num
  · rw [hY, Pc_delta, hs]; norm_num

/-- At `k1 = 17/10` every optimum has `a > 0`. -/
lemma opt_a_pos {p a f : ℝ} (h : Pc.IsOptimal2 (17 / 10) p a f) : 0 < a := by
  have hP := Pc_standing
  obtain ⟨hfe, hmax⟩ := h
  have hsp := hmax _ _ _ special_feas
  by_contra hneg
  have ha0 : a = 0 := le_antisymm (not_lt.1 hneg) hfe.2.1
  subst ha0
  obtain ⟨hp, -, hf, hsum, hth, hb0, hcap⟩ := hfe
  have hth' : Pc.theta (17 / 10) = 101 / 100 := by
    unfold Params.theta; rw [Pc_psi1, Pc_bhat1, Pc_r]; norm_num
  rw [hth'] at hth
  rw [Pc_delta, Real.sqrt_zero, add_zero] at hcap
  -- value of the a = 0 optimum is at most 101/100 + Emin(17/10)
  have hE1 : Pc.Emin ((Pc.r + 1) * Pc.Bhat2 (17 / 10) p 0 f) ≤ Pc.Emin (17 / 10) :=
    Emin_mono Pc hP hcap
  -- value of the special point
  set Y : ℝ := 12355027 / 6250000 with hYdef
  have hsup := Emin_super Pc hP Y (17 / 10)
  have hG : 1 - Y / 10 ≤ Pc.μ.real (Set.Ioi Y) := by
    rw [Pc_mu, tail_eq (by rw [hYdef]; norm_num)]
    have := Real.add_one_le_exp (-(1 / 10 * Y))
    linarith
  have hgap : (0 : ℝ) < Y - 17 / 10 := by rw [hYdef]; norm_num
  have hprod : (1 - Y / 10) * (Y - 17 / 10) ≤ Pc.μ.real (Set.Ioi Y) * (Y - 17 / 10) :=
    mul_le_mul_of_nonneg_right hG hgap.le
  have hnum : (101 / 100 : ℝ) < (Pc.r + 1) * (22 / 25) + (1 - Y / 10) * (Y - 17 / 10) := by
    rw [Pc_r, hYdef]; norm_num
  unfold Params.obj2 at hsp
  rw [special_Y] at hsp
  rw [← hYdef] at hsp
  nlinarith

/-- At `k1 = 17/10` every optimum has `(r+1) p < θ`. -/
lemma opt_p_lt {p a f : ℝ} (h : Pc.IsOptimal2 (17 / 10) p a f) :
    (Pc.r + 1) * p < Pc.theta (17 / 10) := by
  have ha := opt_a_pos h
  obtain ⟨⟨hp, -, hf, hsum, -⟩, -⟩ := h
  rw [Pc_bhat1] at hsum
  have hth' : Pc.theta (17 / 10) = 101 / 100 := by
    unfold Params.theta; rw [Pc_psi1, Pc_bhat1, Pc_r]; norm_num
  rw [hth', Pc_r]
  nlinarith

theorem not_prop1 : ¬ (∀ (P : Params) (hP : P.Standing),
    (∀ k1, P.Admissible k1 → ∃ p a f, P.IsOptimal2 k1 p a f) ∧
    ∃ kl kh : ℝ, kl ≤ kh ∧ ∀ k1, P.Admissible k1 → ∀ p a f, P.IsOptimal2 k1 p a f →
      (k1 < kl → 0 < a ∧ (P.r + 1) * P.Bhat2 k1 p a f = k1 + P.delta a) ∧
      (kl ≤ k1 → k1 < kh →
        (P.r + 1) * P.Bhat2 k1 p a f = k1 + P.delta a ∧ ((P.r + 1) * p < P.theta k1 → a = 0)) ∧
      (kh ≤ k1 → a = 0 ∧ (P.r + 1) * P.Bhat2 k1 p a f ≤ k1) ∧
      (kh < k1 → (P.r + 1) * P.Bhat2 k1 p a f < k1)) := by
  intro H
  obtain ⟨hex, kl, kh, -, hcl⟩ := H Pc Pc_standing
  obtain ⟨p0, a0, f0, hopt0⟩ := hex 0 (Pc_adm le_rfl)
  have ha0 : a0 = 0 := feas0 hopt0.1
  have hkl : kl ≤ 0 := by
    by_contra hlt
    push_neg at hlt
    have := ((hcl 0 (Pc_adm le_rfl) p0 a0 f0 hopt0).1 hlt).1
    linarith
  obtain ⟨p, a, f, hopt⟩ := hex (17 / 10) (Pc_adm (by norm_num))
  have ha := opt_a_pos hopt
  have hp := opt_p_lt hopt
  obtain ⟨-, h2, h3, -⟩ := hcl (17 / 10) (Pc_adm (by norm_num)) p a f hopt
  by_cases hk : (17 / 10 : ℝ) < kh
  · have := (h2 (by linarith) hk).2 hp
    linarith
  · have := (h3 (not_lt.1 hk)).1
    linarith

end NPF657

open NonprofitFunds.Capacity in
theorem solution : ¬ (∀ (P : Params) (hP : P.Standing),
    (∀ k1, P.Admissible k1 → ∃ p a f, P.IsOptimal2 k1 p a f) ∧
    ∃ kl kh : ℝ, kl ≤ kh ∧ ∀ k1, P.Admissible k1 → ∀ p a f, P.IsOptimal2 k1 p a f →
      (k1 < kl → 0 < a ∧ (P.r + 1) * P.Bhat2 k1 p a f = k1 + P.delta a) ∧
      (kl ≤ k1 → k1 < kh →
        (P.r + 1) * P.Bhat2 k1 p a f = k1 + P.delta a ∧ ((P.r + 1) * p < P.theta k1 → a = 0)) ∧
      (kh ≤ k1 → a = 0 ∧ (P.r + 1) * P.Bhat2 k1 p a f ≤ k1) ∧
      (kh < k1 → (P.r + 1) * P.Bhat2 k1 p a f < k1)) := by
  exact NPF657.not_prop1
