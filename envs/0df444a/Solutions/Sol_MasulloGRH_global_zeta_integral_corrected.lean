-- Prove2me | solution 1 for MasulloGRH.global_zeta_integral_corrected
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T07:57:10.902064+00:00
-- url     : https://prove2.me/submissions/4e34416f-54df-4b55-aadb-ad26e2427eb0

import Definitions.Def_MasulloGRH_ZetaIntegrals
import Theorems.Thm_MasulloGRH_idele_group_topology
import Theorems.Thm_MasulloGRH_idele_class_group_topology
import Theorems.Thm_MasulloGRH_idele_class_group_norm_one_compact
import Theorems.Thm_MasulloGRH_tamagawa_measures_wellDefined
import Theorems.Thm_MasulloGRH_adelic_theta_absolute_bounds
import Theorems.Thm_MasulloGRH_adelic_riemann_roch

/-!
# Tate's computation on a measure space with a logarithmic norm

`(X, μ)` is a measure space with a measurable `L : X → ℝ` whose push-forward of `μ` is
`V • Lebesgue`, and a measure-preserving involution `ι` with `L ∘ ι = -L`.  Given two functions
`θ, θ'` related by a Riemann–Roch identity, we continue `∫ θ κ e^{sL}` meromorphically.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace TZAna

/-! ### elementary estimates -/

lemma integrable_exp_neg_abs {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun u : ℝ => Real.exp (-δ * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-δ * |u|)) (Ioi 0) := by
    refine (exp_neg_integrableOn_Ioi 0 hδ).congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [abs_of_pos (mem_Ioi.1 hu)]
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-δ * |u|)) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic hδ 0).congr_fun (fun u hu => ?_) measurableSet_Iic
    simp only [abs_of_nonpos (mem_Iic.1 hu)]
    ring_nf
  have := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at this

lemma abs_mul_exp_le {η t : ℝ} (hη : 0 < η) (ht : 0 ≤ t) :
    t * Real.exp (-η * t) ≤ 2 / η * Real.exp (-(η / 2) * t) := by
  have h1 : η / 2 * t ≤ Real.exp (η / 2 * t) := by linarith [Real.add_one_le_exp (η / 2 * t)]
  have h2 : Real.exp (-η * t) = Real.exp (-(η / 2) * t) * Real.exp (-(η / 2) * t) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (η / 2 * t) * Real.exp (-(η / 2) * t) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have h4 : t ≤ 2 / η * Real.exp (η / 2 * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hη]; linarith
  calc t * Real.exp (-η * t)
      = t * Real.exp (-(η / 2) * t) * Real.exp (-(η / 2) * t) := by rw [h2]; ring
    _ ≤ 2 / η * Real.exp (η / 2 * t) * Real.exp (-(η / 2) * t) * Real.exp (-(η / 2) * t) := by
        gcongr
    _ = 2 / η * Real.exp (-(η / 2) * t) := by
        rw [mul_assoc (2 / η), h3]; ring

lemma norm_cexp_mul (w : ℂ) (t : ℝ) : ‖cexp (w * (t : ℂ))‖ = Real.exp (w.re * t) := by
  rw [Complex.norm_exp]; congr 1; simp

/-- a continuous multiplicative function on `ℝ` is an exponential -/
lemma exists_exp_of_continuous_mul {ψ : ℝ → ℂ} (hc : Continuous ψ)
    (hmul : ∀ u v, ψ (u + v) = ψ u * ψ v) (h0 : ψ 0 = 1) :
    ∃ z : ℂ, ∀ u : ℝ, ψ u = cexp (z * (u : ℂ)) := by
  set I : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, ψ t with hI
  have hId : ∀ u, HasDerivAt I (ψ u) u := fun u =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hδ⟩ : ∃ δ, I δ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hI0 : I = fun _ => 0 := funext hne
    have h1 := hId 0
    rw [hI0] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have hkey : ∀ u, ψ u * I δ = I (u + δ) - I u := by
    intro u
    have e1 : ψ u * I δ = ∫ t in (0 : ℝ)..δ, ψ (u + t) := by
      simp only [hI]
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => (hmul u t).symm
    have e2 : ∫ t in (0 : ℝ)..δ, ψ (u + t) = ∫ t in (u + 0)..(u + δ), ψ t :=
      intervalIntegral.integral_comp_add_left ψ u
    rw [e1, e2, add_zero]
    simp only [hI]
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  set z : ℂ := (ψ δ - 1) / I δ with hz
  have hψd : ∀ u, HasDerivAt ψ (ψ u * z) u := by
    intro u
    have h1 : HasDerivAt (fun u => I (u + δ)) (ψ (u + δ)) u :=
      HasDerivAt.comp_add_const u δ (hId (u + δ))
    have h2 : HasDerivAt (fun u => (I (u + δ) - I u) / I δ) ((ψ (u + δ) - ψ u) / I δ) u :=
      (h1.sub (hId u)).div_const _
    have e : ψ = fun u => (I (u + δ) - I u) / I δ := by
      funext u; rw [← hkey u]; field_simp
    have h3 : HasDerivAt ψ ((ψ (u + δ) - ψ u) / I δ) u :=
      h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => congrFun e v)
    refine h3.congr_deriv ?_
    rw [hmul u δ, hz]; ring
  set g : ℝ → ℂ := fun u => ψ u * cexp (-z * (u : ℂ)) with hg
  have hgd : ∀ u, HasDerivAt g 0 u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => cexp (-z * (u : ℂ))) (cexp (-z * (u : ℂ)) * (-z * 1)) u :=
      (((hasDerivAt_id u).ofReal_comp).const_mul (-z)).cexp
    have h2 := (hψd u).mul h1
    refine h2.congr_deriv ?_
    ring
  have hconst : ∀ u, g u = g 0 :=
    fun u => is_const_of_deriv_eq_zero (fun u => (hgd u).differentiableAt)
      (fun u => (hgd u).deriv) u 0
  refine ⟨z, fun u => ?_⟩
  have h1 := hconst u
  simp only [hg, h0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h1
  have h2 : cexp (-z * (u : ℂ)) * cexp (z * (u : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  calc ψ u = ψ u * (cexp (-z * (u : ℂ)) * cexp (z * (u : ℂ))) := by rw [h2, mul_one]
    _ = (ψ u * cexp (-z * (u : ℂ))) * cexp (z * (u : ℂ)) := by ring
    _ = cexp (z * (u : ℂ)) := by rw [h1, one_mul]

lemma eq_zero_of_cexp_mul_eq_one {w : ℂ} (h : ∀ t : ℝ, cexp (w * (t : ℂ)) = 1) : w = 0 := by
  have h1 : HasDerivAt (fun t : ℝ => cexp (w * (t : ℂ))) (cexp (w * ((0 : ℝ) : ℂ)) * (w * 1)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul w).cexp
  have h2 : (fun t : ℝ => cexp (w * (t : ℂ))) = fun _ => (1 : ℂ) := funext h
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using h3

/-- the two-sided weight: `e^{-A u}` for `u ≥ 0`, `e^{-B u}` for `u < 0` -/
noncomputable def wt (A B u : ℝ) : ℝ := if 0 ≤ u then Real.exp (-A * u) else Real.exp (-B * u)

lemma wt_nonneg (A B u : ℝ) : 0 ≤ wt A B u := by
  unfold wt; split_ifs <;> positivity

lemma wt_of_nonneg {A B u : ℝ} (hu : 0 ≤ u) : wt A B u = Real.exp (-A * u) := by
  unfold wt; rw [if_pos hu]

lemma wt_of_neg {A B u : ℝ} (hu : u < 0) : wt A B u = Real.exp (-B * u) := by
  unfold wt; rw [if_neg (not_le.2 hu)]

lemma wt_mul_exp_le {A B η r u : ℝ} (h1 : B + η ≤ r) (h2 : r ≤ A - η) :
    wt A B u * Real.exp (r * u) ≤ Real.exp (-η * |u|) := by
  unfold wt
  split_ifs with hu
  · rw [← Real.exp_add, abs_of_nonneg hu]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (sub_nonneg.2 h2) hu]
  · push_neg at hu
    rw [← Real.exp_add, abs_of_neg hu]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (sub_nonneg.2 h1) (neg_nonneg.2 hu.le)]

/-! ### the base setting -/

variable {X : Type*} [MeasurableSpace X]

/-- `L` pushes `μ` forward to `V` times Lebesgue measure -/
structure Base (μ : Measure X) (L : X → ℝ) (V : ℝ) : Prop where
  measL : Measurable L
  Vpos : 0 < V
  map : Measure.map L μ = ENNReal.ofReal V • (volume : Measure ℝ)

variable {μ : Measure X} {L : X → ℝ} {V : ℝ}

lemma Base.integrable_comp (hB : Base μ L V) {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun x => g (L x)) μ := by
  have h1 : Integrable g (Measure.map L μ) := by
    rw [hB.map]; exact hg.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_measure h1.aestronglyMeasurable hB.measL.aemeasurable).1 h1

lemma Base.integrable_of_bound (hB : Base μ L V) {F : X → ℂ} (hF : AEStronglyMeasurable F μ)
    {C δ : ℝ} (hδ : 0 < δ) (h : ∀ x, ‖F x‖ ≤ C * Real.exp (-δ * |L x|)) : Integrable F μ := by
  have h1 : Integrable (fun x => C * Real.exp (-δ * |L x|)) μ :=
    hB.integrable_comp (g := fun u => C * Real.exp (-δ * |u|))
      ((integrable_exp_neg_abs hδ).const_mul C)
  exact h1.mono' hF (Filter.Eventually.of_forall h)

lemma Base.measure_zero (hB : Base μ L V) : μ {x | L x = 0} = 0 := by
  have h : μ (L ⁻¹' {0}) = (Measure.map L μ) {0} :=
    (Measure.map_apply hB.measL (measurableSet_singleton 0)).symm
  have h2 : {x | L x = 0} = L ⁻¹' {0} := rfl
  rw [h2, h, hB.map]
  simp

lemma Base.exists_pos (hB : Base μ L V) : ∃ x, 0 < L x := by
  by_contra hne
  push_neg at hne
  have h : μ (L ⁻¹' Ioi 0) = (Measure.map L μ) (Ioi 0) :=
    (Measure.map_apply hB.measL measurableSet_Ioi).symm
  have he : L ⁻¹' Ioi 0 = ∅ := by
    ext x; simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false, not_lt]; exact hne x
  rw [he, measure_empty, hB.map] at h
  have : (ENNReal.ofReal V • (volume : Measure ℝ)) (Ioi 0) = ∞ := by
    rw [Measure.smul_apply, Real.volume_Ioi, smul_eq_mul]
    exact ENNReal.mul_top (by simpa using hB.Vpos)
  rw [this] at h
  exact ENNReal.top_ne_zero h.symm

lemma measurable_cexp_mul (hB : Base μ L V) (w : ℂ) :
    Measurable (fun x => cexp (w * (L x : ℂ))) :=
  Complex.continuous_exp.measurable.comp
    (measurable_const.mul (Complex.measurable_ofReal.comp hB.measL))

/-- the transform `∫ H(x) e^{w L(x)} dμ(x)` -/
noncomputable def tr (μ : Measure X) (L : X → ℝ) (H : X → ℂ) (w : ℂ) : ℂ :=
  ∫ x, H x * cexp (w * (L x : ℂ)) ∂μ

/-- the transform converges and is holomorphic in the strip given by the weight -/
theorem Base.strip (hB : Base μ L V) {H : X → ℂ} (hH : Measurable H) {A B C : ℝ}
    (hb : ∀ x, ‖H x‖ ≤ C * wt A B (L x)) {w : ℂ} (h1 : B < w.re) (h2 : w.re < A) :
    Integrable (fun x => H x * cexp (w * (L x : ℂ))) μ ∧
      DifferentiableAt ℂ (tr μ L H) w := by
  have hb' : ∀ x, ‖H x‖ ≤ |C| * wt A B (L x) := fun x =>
    (hb x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (wt_nonneg _ _ _))
  set η : ℝ := min (A - w.re) (w.re - B) / 2 with hη
  have hη0 : 0 < η := by
    have : 0 < min (A - w.re) (w.re - B) := lt_min (by linarith) (by linarith)
    positivity
  have hηA : η ≤ (A - w.re) / 2 := by
    rw [hη]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hηB : η ≤ (w.re - B) / 2 := by
    rw [hη]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hmeas : ∀ w' : ℂ, AEStronglyMeasurable (fun x => H x * cexp (w' * (L x : ℂ))) μ :=
    fun w' => (hH.mul (measurable_cexp_mul hB w')).aestronglyMeasurable
  have hkey : ∀ w' : ℂ, B + η ≤ w'.re → w'.re ≤ A - η → ∀ x,
      ‖H x‖ * Real.exp (w'.re * L x) ≤ |C| * Real.exp (-η * |L x|) := by
    intro w' hw1 hw2 x
    calc ‖H x‖ * Real.exp (w'.re * L x)
        ≤ |C| * wt A B (L x) * Real.exp (w'.re * L x) :=
          mul_le_mul_of_nonneg_right (hb' x) (Real.exp_pos _).le
      _ = |C| * (wt A B (L x) * Real.exp (w'.re * L x)) := by ring
      _ ≤ |C| * Real.exp (-η * |L x|) :=
          mul_le_mul_of_nonneg_left (wt_mul_exp_le hw1 hw2) (abs_nonneg C)
  have hint : Integrable (fun x => H x * cexp (w * (L x : ℂ))) μ := by
    refine hB.integrable_of_bound (hmeas w) hη0 (C := |C|) fun x => ?_
    rw [norm_mul, norm_cexp_mul]
    exact hkey w (by linarith) (by linarith) x
  refine ⟨hint, ?_⟩
  have hball : ∀ w' ∈ Metric.ball w η, B + η ≤ w'.re ∧ w'.re ≤ A - η := by
    intro w' hw'
    rw [Metric.mem_ball, dist_eq_norm] at hw'
    have h3 : |w'.re - w.re| ≤ ‖w' - w‖ := by
      have := Complex.abs_re_le_norm (w' - w)
      simpa using this
    have h4 := abs_lt.1 (lt_of_le_of_lt h3 hw')
    constructor <;> linarith [h4.1, h4.2]
  have hbound : Integrable (fun x => |C| * (2 / η) * Real.exp (-(η / 2) * |L x|)) μ :=
    hB.integrable_comp (g := fun u => |C| * (2 / η) * Real.exp (-(η / 2) * |u|))
      ((integrable_exp_neg_abs (half_pos hη0)).const_mul _)
  have hder := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (w' : ℂ) (x : X) => H x * cexp (w' * (L x : ℂ)))
    (F' := fun (w' : ℂ) (x : X) => H x * ((L x : ℂ) * cexp (w' * (L x : ℂ))))
    (x₀ := w) (s := Metric.ball w η)
    (bound := fun x => |C| * (2 / η) * Real.exp (-(η / 2) * |L x|))
    (Metric.ball_mem_nhds w hη0)
    (Filter.Eventually.of_forall hmeas) hint
    ((hH.mul ((Complex.measurable_ofReal.comp hB.measL).mul
      (measurable_cexp_mul hB w))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x w' hw' => by
      obtain ⟨hw1, hw2⟩ := hball w' hw'
      rw [norm_mul, norm_mul, norm_cexp_mul, Complex.norm_real, Real.norm_eq_abs]
      have e1 := hkey w' hw1 hw2 x
      have e2 := abs_mul_exp_le hη0 (abs_nonneg (L x))
      calc ‖H x‖ * (|L x| * Real.exp (w'.re * L x))
          = |L x| * (‖H x‖ * Real.exp (w'.re * L x)) := by ring
        _ ≤ |L x| * (|C| * Real.exp (-η * |L x|)) :=
            mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        _ = |C| * (|L x| * Real.exp (-η * |L x|)) := by ring
        _ ≤ |C| * (2 / η * Real.exp (-(η / 2) * |L x|)) :=
            mul_le_mul_of_nonneg_left e2 (abs_nonneg C)
        _ = |C| * (2 / η) * Real.exp (-(η / 2) * |L x|) := by ring)
    hbound
    (Filter.Eventually.of_forall fun x w' _ => by
      have h := (((hasDerivAt_id w').mul_const (L x : ℂ)).cexp).const_mul (H x)
      refine h.congr_deriv ?_
      simp only [id_eq, one_mul]
      ring)
  exact hder.2.differentiableAt

/-! ### the data -/

variable {ι : X → X}

/-- a measure-preserving involution reversing `L` -/
structure Inv (μ : Measure X) (L : X → ℝ) (ι : X → X) : Prop where
  meas : Measurable ι
  map : Measure.map ι μ = μ
  neg : ∀ x, L (ι x) = -L x
  invol : ∀ x, ι (ι x) = x

/-- two functions related by a Riemann–Roch identity, with a multiplier `κ` -/
structure Dat (L : X → ℝ) (ι : X → X) where
  θ : X → ℂ
  θ' : X → ℂ
  κ : X → ℂ
  a : ℂ
  b : ℂ
  σ : ℝ
  mθ : Measurable θ
  mθ' : Measurable θ'
  mκ : Measurable κ
  nκ : ∀ x, ‖κ x‖ = Real.exp (σ * L x)
  κι : ∀ x, κ (ι x) * κ x = 1
  rr : ∀ x, θ x = cexp (-(L x : ℂ)) * θ' (ι x) + cexp (-(L x : ℂ)) * b - a
  decay : ∀ N : ℕ, ∃ C : ℝ, ∀ x, 0 ≤ L x → ‖θ x‖ ≤ C * Real.exp (-(N : ℝ) * L x)
  decay' : ∀ N : ℕ, ∃ C : ℝ, ∀ x, 0 ≤ L x → ‖θ' x‖ ≤ C * Real.exp (-(N : ℝ) * L x)
  small : ∃ C : ℝ, ∀ x, L x ≤ 0 → ‖θ x‖ ≤ C * Real.exp (-L x)
  small' : ∃ C : ℝ, ∀ x, L x ≤ 0 → ‖θ' x‖ ≤ C * Real.exp (-L x)

namespace Dat

variable (D : Dat L ι)

lemma κ_ne (x : X) : D.κ x ≠ 0 := by
  intro h
  have := D.nκ x
  rw [h, norm_zero] at this
  exact (Real.exp_pos _).ne this

lemma nκinv (x : X) : ‖(D.κ x)⁻¹‖ = Real.exp (-D.σ * L x) := by
  rw [norm_inv, D.nκ, ← Real.exp_neg]; congr 1; ring

/-- bound for `θ κ` on `L ≥ 0` -/
lemma bound_pos (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, 0 ≤ L x →
    ‖D.θ x * D.κ x‖ ≤ C * Real.exp (-A * L x) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (A + D.σ)
  obtain ⟨C, hC⟩ := D.decay N
  refine ⟨|C|, abs_nonneg _, fun x hx => ?_⟩
  rw [norm_mul, D.nκ]
  calc ‖D.θ x‖ * Real.exp (D.σ * L x)
      ≤ C * Real.exp (-(N : ℝ) * L x) * Real.exp (D.σ * L x) :=
        mul_le_mul_of_nonneg_right (hC x hx) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (-(N : ℝ) * L x) * Real.exp (D.σ * L x) := by
        gcongr; exact le_abs_self C
    _ = |C| * Real.exp ((-(N : ℝ) + D.σ) * L x) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ |C| * Real.exp (-A * L x) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg (sub_nonneg.2 hN) hx]

/-- bound for `θ' κ⁻¹` on `L ≥ 0` -/
lemma bound_pos' (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, 0 ≤ L x →
    ‖D.θ' x * (D.κ x)⁻¹‖ ≤ C * Real.exp (-A * L x) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (A - D.σ)
  obtain ⟨C, hC⟩ := D.decay' N
  refine ⟨|C|, abs_nonneg _, fun x hx => ?_⟩
  rw [norm_mul, D.nκinv]
  calc ‖D.θ' x‖ * Real.exp (-D.σ * L x)
      ≤ C * Real.exp (-(N : ℝ) * L x) * Real.exp (-D.σ * L x) :=
        mul_le_mul_of_nonneg_right (hC x hx) (Real.exp_pos _).le
    _ ≤ |C| * Real.exp (-(N : ℝ) * L x) * Real.exp (-D.σ * L x) := by
        gcongr; exact le_abs_self C
    _ = |C| * Real.exp ((-(N : ℝ) - D.σ) * L x) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ |C| * Real.exp (-A * L x) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        apply Real.exp_le_exp.2
        nlinarith [mul_nonneg (sub_nonneg.2 hN) hx]

/-- the part of the transform over `L ≥ 0` -/
noncomputable def Ep (μ : Measure X) (s : ℂ) : ℂ :=
  tr μ L ({x | 0 ≤ L x}.indicator fun x => D.θ x * D.κ x) s

/-- the part of the dual transform over `L > 0` -/
noncomputable def Em (μ : Measure X) (s : ℂ) : ℂ :=
  tr μ L ({x | 0 < L x}.indicator fun x => D.θ' x * (D.κ x)⁻¹) (1 - s)

/-- the full transform -/
noncomputable def W (μ : Measure X) (s : ℂ) : ℂ := tr μ L (fun x => D.θ x * D.κ x) s

/-- the polar integral -/
noncomputable def P (μ : Measure X) (s : ℂ) : ℂ := tr μ L ({x | L x < 0}.indicator D.κ) s

/-! ### holomorphy of the pieces -/

lemma measSet_nonneg (hB : Base μ L V) : MeasurableSet {x | 0 ≤ L x} :=
  measurableSet_le measurable_const hB.measL

lemma measSet_pos (hB : Base μ L V) : MeasurableSet {x | 0 < L x} :=
  measurableSet_lt measurable_const hB.measL

lemma measSet_neg (hB : Base μ L V) : MeasurableSet {x | L x < 0} :=
  measurableSet_lt hB.measL measurable_const

theorem Ep_strip (hB : Base μ L V) (s : ℂ) :
    Integrable (fun x => ({x | 0 ≤ L x}.indicator (fun x => D.θ x * D.κ x)) x *
      cexp (s * (L x : ℂ))) μ ∧ DifferentiableAt ℂ (D.Ep μ) s := by
  obtain ⟨C, hC0, hC⟩ := D.bound_pos (s.re + 1)
  refine hB.strip ((D.mθ.mul D.mκ).indicator (measSet_nonneg hB)) (A := s.re + 1)
    (B := s.re - 1) (C := C) (fun x => ?_) (by linarith) (by linarith)
  by_cases hx : 0 ≤ L x
  · rw [Set.indicator_of_mem (show x ∈ {x | 0 ≤ L x} from hx), wt_of_nonneg hx]
    exact hC x hx
  · rw [Set.indicator_of_notMem (show x ∉ {x | 0 ≤ L x} from hx), norm_zero]
    exact mul_nonneg hC0 (wt_nonneg _ _ _)

theorem Em_strip (hB : Base μ L V) (w : ℂ) :
    Integrable (fun x => ({x | 0 < L x}.indicator (fun x => D.θ' x * (D.κ x)⁻¹)) x *
      cexp (w * (L x : ℂ))) μ ∧
      DifferentiableAt ℂ (tr μ L ({x | 0 < L x}.indicator fun x => D.θ' x * (D.κ x)⁻¹)) w := by
  obtain ⟨C, hC0, hC⟩ := D.bound_pos' (w.re + 1)
  refine hB.strip ((D.mθ'.mul D.mκ.inv).indicator (measSet_pos hB)) (A := w.re + 1)
    (B := w.re - 1) (C := C) (fun x => ?_) (by linarith) (by linarith)
  by_cases hx : 0 < L x
  · rw [Set.indicator_of_mem (show x ∈ {x | 0 < L x} from hx), wt_of_nonneg hx.le]
    exact hC x hx.le
  · rw [Set.indicator_of_notMem (show x ∉ {x | 0 < L x} from hx), norm_zero]
    exact mul_nonneg hC0 (wt_nonneg _ _ _)

theorem Ep_differentiable (hB : Base μ L V) : Differentiable ℂ (D.Ep μ) :=
  fun s => (D.Ep_strip hB s).2

theorem Em_differentiable (hB : Base μ L V) : Differentiable ℂ (D.Em μ) := by
  intro s
  have h1 := (D.Em_strip hB (1 - s)).2
  have h2 : DifferentiableAt ℂ (fun s : ℂ => 1 - s) s := by fun_prop
  exact DifferentiableAt.comp s h1 h2

theorem W_strip (hB : Base μ L V) {s : ℂ} (hs : 1 - D.σ < s.re) :
    Integrable (fun x => D.θ x * D.κ x * cexp (s * (L x : ℂ))) μ ∧
      DifferentiableAt ℂ (D.W μ) s := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := D.bound_pos (s.re + 1)
  obtain ⟨C₂, hC₂⟩ := D.small
  refine hB.strip (D.mθ.mul D.mκ) (A := s.re + 1) (B := 1 - D.σ) (C := C₁ + |C₂|)
    (fun x => ?_) hs (by linarith)
  by_cases hx : 0 ≤ L x
  · rw [wt_of_nonneg hx]
    exact (hC₁ x hx).trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C₂])
      (Real.exp_pos _).le)
  · push_neg at hx
    change ‖D.θ x * D.κ x‖ ≤ _
    rw [wt_of_neg hx, norm_mul, D.nκ]
    calc ‖D.θ x‖ * Real.exp (D.σ * L x)
        ≤ C₂ * Real.exp (-L x) * Real.exp (D.σ * L x) :=
          mul_le_mul_of_nonneg_right (hC₂ x hx.le) (Real.exp_pos _).le
      _ ≤ |C₂| * Real.exp (-L x) * Real.exp (D.σ * L x) := by
          gcongr; exact le_abs_self C₂
      _ = |C₂| * Real.exp (-(1 - D.σ) * L x) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ (C₁ + |C₂|) * Real.exp (-(1 - D.σ) * L x) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- with exponential decay at both ends the full transform is entire -/
theorem W_strip_of_exp (hB : Base μ L V)
    (hexp : ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖D.θ x‖ ≤ C * Real.exp (-(N : ℝ) * |L x|)) (s : ℂ) :
    Integrable (fun x => D.θ x * D.κ x * cexp (s * (L x : ℂ))) μ ∧
      DifferentiableAt ℂ (D.W μ) s := by
  obtain ⟨N, hN⟩ := exists_nat_ge (|s.re + 1 + D.σ| + |s.re - 1 + D.σ|)
  obtain ⟨C, hC⟩ := hexp N
  have hN1 : s.re + 1 + D.σ ≤ N :=
    (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg _)).trans hN)
  have hN2 : -(s.re - 1 + D.σ) ≤ N :=
    (neg_le_abs _).trans ((le_add_of_nonneg_left (abs_nonneg _)).trans hN)
  refine hB.strip (D.mθ.mul D.mκ) (A := s.re + 1) (B := s.re - 1) (C := |C|)
    (fun x => ?_) (by linarith) (by linarith)
  have h0 : ‖D.θ x * D.κ x‖ ≤ |C| * Real.exp (-(N : ℝ) * |L x| + D.σ * L x) := by
    rw [norm_mul, D.nκ, Real.exp_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((hC x).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)) (Real.exp_pos _).le
  refine h0.trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg C))
  by_cases hx : 0 ≤ L x
  · rw [wt_of_nonneg hx, abs_of_nonneg hx]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (sub_nonneg.2 hN1) hx]
  · push_neg at hx
    rw [wt_of_neg hx, abs_of_neg hx]
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (sub_nonneg.2 hN2) (neg_nonneg.2 hx.le)]

/-! ### the splitting identity -/

lemma κ_inv_ι (x : X) : (D.κ (ι x))⁻¹ = D.κ x :=
  (eq_inv_of_mul_eq_one_right (D.κι x)).symm

theorem W_eq (hB : Base μ L V) (hI : Inv μ L ι) {s : ℂ} (hs : 1 - D.σ < s.re) :
    D.W μ s = D.Ep μ s + D.Em μ s + D.b * D.P μ (s - 1) - D.a * D.P μ s := by
  have hSp := measSet_nonneg hB
  have hSn := measSet_neg hB
  have hcompl : {x | 0 ≤ L x}ᶜ = {x | L x < 0} := by
    ext x; simp only [mem_compl_iff, mem_ofPred_eq, not_le]
  set f₀ : X → ℂ := fun x => D.θ x * D.κ x * cexp (s * (L x : ℂ)) with hf₀
  set g₁ : X → ℂ := fun x => D.θ' (ι x) * D.κ x * cexp ((s - 1) * (L x : ℂ)) with hg₁
  set g₂ : X → ℂ := fun x => D.κ x * cexp ((s - 1) * (L x : ℂ)) with hg₂
  set g₃ : X → ℂ := fun x => D.κ x * cexp (s * (L x : ℂ)) with hg₃
  set G : X → ℂ := fun y => ({x | 0 < L x}.indicator (fun x => D.θ' x * (D.κ x)⁻¹)) y *
    cexp ((1 - s) * (L y : ℂ)) with hG
  have hf₀int : Integrable f₀ μ := (D.W_strip hB hs).1
  have hGint : Integrable G μ := (D.Em_strip hB (1 - s)).1
  have hGm : Measurable G :=
    ((D.mθ'.mul D.mκ.inv).indicator (measSet_pos hB)).mul (measurable_cexp_mul hB _)
  -- the three pieces on `L < 0`
  have hexp1 : ∀ x : X, cexp (-(L x : ℂ)) * cexp (s * (L x : ℂ)) = cexp ((s - 1) * (L x : ℂ)) := by
    intro x; rw [← Complex.exp_add]; congr 1; ring
  have hpt : ∀ x, f₀ x = g₁ x + D.b * g₂ x - D.a * g₃ x := by
    intro x
    simp only [hf₀, hg₁, hg₂, hg₃]
    rw [D.rr x, ← hexp1 x]
    ring
  have hG1 : ∀ x, {x | L x < 0}.indicator g₁ x = G (ι x) := by
    intro x
    simp only [hG]
    by_cases hx : L x < 0
    · have hx' : ι x ∈ {x | 0 < L x} := by
        change 0 < L (ι x); rw [hI.neg]; linarith
      rw [Set.indicator_of_mem (show x ∈ {x | L x < 0} from hx), Set.indicator_of_mem hx',
        D.κ_inv_ι, hI.neg]
      simp only [hg₁]
      congr 2
      push_cast; ring
    · have hx' : ι x ∉ {x | 0 < L x} := by
        change ¬ 0 < L (ι x); rw [hI.neg]; linarith
      rw [Set.indicator_of_notMem (show x ∉ {x | L x < 0} from hx),
        Set.indicator_of_notMem hx', zero_mul]
  have hi1 : IntegrableOn g₁ {x | L x < 0} μ := by
    rw [← integrable_indicator_iff hSn]
    have h1 : Integrable G (Measure.map ι μ) := by rw [hI.map]; exact hGint
    have h2 := (integrable_map_measure hGm.aestronglyMeasurable hI.meas.aemeasurable).1 h1
    exact h2.congr (Filter.Eventually.of_forall fun x => (hG1 x).symm)
  have hmg₂ : Measurable g₂ := D.mκ.mul (measurable_cexp_mul hB _)
  have hmg₃ : Measurable g₃ := D.mκ.mul (measurable_cexp_mul hB _)
  have hi2 : IntegrableOn g₂ {x | L x < 0} μ := by
    rw [← integrable_indicator_iff hSn]
    refine hB.integrable_of_bound (hmg₂.indicator hSn).aestronglyMeasurable
      (C := 1) (δ := D.σ + s.re - 1) (by linarith) fun x => ?_
    by_cases hx : L x < 0
    · rw [Set.indicator_of_mem (show x ∈ {x | L x < 0} from hx)]
      simp only [hg₂]
      rw [norm_mul, D.nκ, norm_cexp_mul, ← Real.exp_add, one_mul, abs_of_neg hx]
      apply Real.exp_le_exp.2
      simp only [Complex.sub_re, Complex.one_re]
      nlinarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | L x < 0} from hx), norm_zero]
      positivity
  have hi3 : IntegrableOn g₃ {x | L x < 0} μ := by
    rw [← integrable_indicator_iff hSn]
    refine hB.integrable_of_bound (hmg₃.indicator hSn).aestronglyMeasurable
      (C := 1) (δ := D.σ + s.re) (by linarith) fun x => ?_
    by_cases hx : L x < 0
    · rw [Set.indicator_of_mem (show x ∈ {x | L x < 0} from hx)]
      simp only [hg₃]
      rw [norm_mul, D.nκ, norm_cexp_mul, ← Real.exp_add, one_mul, abs_of_neg hx]
      apply Real.exp_le_exp.2
      nlinarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | L x < 0} from hx), norm_zero]
      positivity
  -- assemble
  have e0 : D.W μ s = ∫ x in {x | 0 ≤ L x}, f₀ x ∂μ + ∫ x in {x | L x < 0}, f₀ x ∂μ := by
    have := integral_add_compl hSp hf₀int
    rw [hcompl] at this
    exact this.symm
  have e1 : ∫ x in {x | 0 ≤ L x}, f₀ x ∂μ = D.Ep μ s := by
    rw [← integral_indicator hSp]
    unfold Dat.Ep tr
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf₀]
    exact Set.indicator_mul_left _ _ _
  have e2 : ∫ x in {x | L x < 0}, f₀ x ∂μ = ∫ x in {x | L x < 0}, g₁ x ∂μ +
      D.b * ∫ x in {x | L x < 0}, g₂ x ∂μ - D.a * ∫ x in {x | L x < 0}, g₃ x ∂μ := by
    have h : ∫ x in {x | L x < 0}, f₀ x ∂μ =
        ∫ x in {x | L x < 0}, (g₁ x + D.b * g₂ x - D.a * g₃ x) ∂μ :=
      setIntegral_congr_fun hSn fun x _ => hpt x
    have h12 : Integrable (fun x => g₁ x + D.b * g₂ x) (μ.restrict {x | L x < 0}) :=
      hi1.add (hi2.const_mul _)
    have h3 : Integrable (fun x => D.a * g₃ x) (μ.restrict {x | L x < 0}) := hi3.const_mul _
    have h2 : Integrable (fun x => D.b * g₂ x) (μ.restrict {x | L x < 0}) := hi2.const_mul _
    rw [h, integral_sub (f := fun x => g₁ x + D.b * g₂ x) (g := fun x => D.a * g₃ x) h12 h3,
      integral_add (f := g₁) (g := fun x => D.b * g₂ x) hi1 h2, integral_const_mul,
      integral_const_mul]
  have e3 : ∫ x in {x | L x < 0}, g₁ x ∂μ = D.Em μ s := by
    rw [← integral_indicator hSn]
    have h1 : ∫ x, {x | L x < 0}.indicator g₁ x ∂μ = ∫ x, G (ι x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hG1)
    have h2 : ∫ y, G y ∂(Measure.map ι μ) = ∫ x, G (ι x) ∂μ :=
      integral_map hI.meas.aemeasurable hGm.aestronglyMeasurable
    rw [h1, ← h2, hI.map]
    rfl
  have e4 : ∫ x in {x | L x < 0}, g₂ x ∂μ = D.P μ (s - 1) := by
    rw [← integral_indicator hSn]
    unfold Dat.P tr
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg₂]
    exact Set.indicator_mul_left _ _ _
  have e5 : ∫ x in {x | L x < 0}, g₃ x ∂μ = D.P μ s := by
    rw [← integral_indicator hSn]
    unfold Dat.P tr
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg₃]
    exact Set.indicator_mul_left _ _ _
  rw [e0, e1, e2, e3, e4, e5]
  ring

/-! ### the polar integrals -/

theorem P_triv (hB : Base μ L V) {s₀ s : ℂ} (hκ : ∀ x, D.κ x = cexp (-s₀ * (L x : ℂ)))
    (hs : 0 < (s - s₀).re) : D.P μ s = V / (s - s₀) := by
  set g : ℝ → ℂ := (Iio (0 : ℝ)).indicator (fun u : ℝ => cexp ((s - s₀) * (u : ℂ))) with hg
  have hgm : Measurable g :=
    (Complex.continuous_exp.measurable.comp
      (measurable_const.mul Complex.measurable_ofReal)).indicator measurableSet_Iio
  have h1 : D.P μ s = ∫ x, g (L x) ∂μ := by
    unfold Dat.P tr
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg]
    by_cases hx : L x < 0
    · rw [Set.indicator_of_mem (show x ∈ {x | L x < 0} from hx),
        Set.indicator_of_mem (show L x ∈ Iio (0 : ℝ) from hx), hκ x, ← Complex.exp_add]
      congr 1; ring
    · rw [Set.indicator_of_notMem (show x ∉ {x | L x < 0} from hx),
        Set.indicator_of_notMem (show L x ∉ Iio (0 : ℝ) from hx), zero_mul]
  have h2 : ∫ u, g u ∂(Measure.map L μ) = ∫ x, g (L x) ∂μ :=
    integral_map hB.measL.aemeasurable hgm.aestronglyMeasurable
  rw [h1, ← h2, hB.map, integral_smul_measure, ENNReal.toReal_ofReal hB.Vpos.le]
  simp only [hg]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Iic hs 0]
  simp [div_eq_mul_inv]

theorem P_nontriv (hB : Base μ L V) {τ : X → X} (hτ : Measurable τ)
    (hτμ : Measure.map τ μ = μ) (hτL : ∀ x, L (τ x) = L x) {k : ℂ} (hk : k ≠ 1)
    (hκ : ∀ x, D.κ (τ x) = k * D.κ x) (s : ℂ) : D.P μ s = 0 := by
  set Fn : X → ℂ := fun x => ({x | L x < 0}.indicator D.κ) x * cexp (s * (L x : ℂ)) with hFn
  have hFm : Measurable Fn := (D.mκ.indicator (measSet_neg hB)).mul (measurable_cexp_mul hB _)
  have h1 : ∀ x, Fn (τ x) = k * Fn x := by
    intro x
    simp only [hFn]
    by_cases hx : L x < 0
    · have hx' : τ x ∈ {x | L x < 0} := by change L (τ x) < 0; rw [hτL]; exact hx
      rw [Set.indicator_of_mem (show x ∈ {x | L x < 0} from hx), Set.indicator_of_mem hx',
        hκ, hτL]
      ring
    · have hx' : τ x ∉ {x | L x < 0} := by change ¬ L (τ x) < 0; rw [hτL]; exact hx
      rw [Set.indicator_of_notMem (show x ∉ {x | L x < 0} from hx),
        Set.indicator_of_notMem hx']
      simp
  have h2 : ∫ y, Fn y ∂(Measure.map τ μ) = ∫ x, Fn (τ x) ∂μ :=
    integral_map hτ.aemeasurable hFm.aestronglyMeasurable
  rw [hτμ] at h2
  simp_rw [h1] at h2
  rw [integral_const_mul] at h2
  have h3 : D.P μ s = ∫ x, Fn x ∂μ := rfl
  rw [h3]
  have h4 : (1 - k) * ∫ x, Fn x ∂μ = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd (sub_eq_zero.1 h).symm hk
  · exact h

/-- exponential decay at both ends when the polar terms vanish -/
lemma exp_of_polar_free (hι : ∀ x, L (ι x) = -L x) (ha : D.a = 0) (hb : D.b = 0) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖D.θ x‖ ≤ C * Real.exp (-(N : ℝ) * |L x|) := by
  intro N
  obtain ⟨C₁, hC₁⟩ := D.decay N
  obtain ⟨C₂, hC₂⟩ := D.decay' (N + 1)
  refine ⟨|C₁| + |C₂|, fun x => ?_⟩
  by_cases hx : 0 ≤ L x
  · rw [abs_of_nonneg hx]
    exact (hC₁ x hx).trans (mul_le_mul_of_nonneg_right
      ((le_abs_self C₁).trans (le_add_of_nonneg_right (abs_nonneg _))) (Real.exp_pos _).le)
  · push_neg at hx
    have hx' : 0 ≤ L (ι x) := by rw [hι]; linarith
    have h1 := hC₂ (ι x) hx'
    rw [hι] at h1
    have h2 : D.θ x = cexp (-(L x : ℂ)) * D.θ' (ι x) := by
      have := D.rr x
      rw [ha, hb] at this
      simpa using this
    rw [h2, norm_mul, abs_of_neg hx]
    have h3 : ‖cexp (-(L x : ℂ))‖ = Real.exp (-L x) := by
      rw [Complex.norm_exp]; simp
    rw [h3]
    calc Real.exp (-L x) * ‖D.θ' (ι x)‖
        ≤ Real.exp (-L x) * (C₂ * Real.exp (-((N + 1 : ℕ) : ℝ) * -L x)) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = C₂ * Real.exp (-(N : ℝ) * -L x) := by
          rw [mul_comm, mul_assoc, ← Real.exp_add]
          congr 2
          push_cast; ring
      _ ≤ (|C₁| + |C₂|) * Real.exp (-(N : ℝ) * -L x) :=
          mul_le_mul_of_nonneg_right
            ((le_abs_self C₂).trans (le_add_of_nonneg_left (abs_nonneg _))) (Real.exp_pos _).le

/-! ### duality -/

/-- the dual data: `θ ↔ θ'`, `a ↔ b`, `κ ↦ e^{L} κ⁻¹` -/
noncomputable def swap (hL : Measurable L) (hι : ∀ x, L (ι x) = -L x)
    (hιι : ∀ x, ι (ι x) = x) : Dat L ι where
  θ := D.θ'
  θ' := D.θ
  κ := fun x => cexp (L x : ℂ) * (D.κ x)⁻¹
  a := D.b
  b := D.a
  σ := 1 - D.σ
  mθ := D.mθ'
  mθ' := D.mθ
  mκ := (Complex.continuous_exp.measurable.comp (Complex.measurable_ofReal.comp hL)).mul
    D.mκ.inv
  nκ := fun x => by
    rw [norm_mul, Complex.norm_exp, Complex.ofReal_re, D.nκinv, ← Real.exp_add]
    congr 1; ring
  κι := fun x => by
    have h := D.κι x
    rw [hι x]
    have e : cexp ((-L x : ℝ) : ℂ) * cexp (L x : ℂ) = 1 := by
      rw [← Complex.exp_add]; simp
    calc cexp ((-L x : ℝ) : ℂ) * (D.κ (ι x))⁻¹ * (cexp (L x : ℂ) * (D.κ x)⁻¹)
        = (cexp ((-L x : ℝ) : ℂ) * cexp (L x : ℂ)) * (D.κ (ι x) * D.κ x)⁻¹ := by
          rw [mul_inv]; ring
      _ = 1 := by rw [e, h]; simp
  rr := fun x => by
    have h := D.rr (ι x)
    rw [hι x, hιι x] at h
    have e : cexp (-(L x : ℂ)) * cexp (-(((-L x : ℝ)) : ℂ)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [h]
    linear_combination (-(D.θ' x) - D.b) * e
  decay := D.decay'
  decay' := D.decay
  small := D.small'
  small' := D.small

lemma ae_ne_zero (hB : Base μ L V) : ∀ᵐ x ∂μ, L x ≠ 0 := by
  rw [ae_iff]
  simpa using hB.measure_zero

theorem swap_Ep (hB : Base μ L V) (hI : Inv μ L ι) (s : ℂ) :
    (D.swap hB.measL hI.neg hI.invol).Ep μ s = D.Em μ (-s) := by
  unfold Dat.Ep Dat.Em tr
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero hB] with x hx
  rcases lt_or_gt_of_ne hx with h | h
  · rw [Set.indicator_of_notMem (show x ∉ {x | 0 ≤ L x} from not_le.2 h),
      Set.indicator_of_notMem (show x ∉ {x | 0 < L x} from not_lt.2 h.le), zero_mul, zero_mul]
  · rw [Set.indicator_of_mem (show x ∈ {x | 0 ≤ L x} from h.le),
      Set.indicator_of_mem (show x ∈ {x | 0 < L x} from h)]
    change D.θ' x * (cexp (L x : ℂ) * (D.κ x)⁻¹) * cexp (s * (L x : ℂ)) =
      D.θ' x * (D.κ x)⁻¹ * cexp ((1 - -s) * (L x : ℂ))
    have e : cexp ((1 - -s) * (L x : ℂ)) = cexp (L x : ℂ) * cexp (s * (L x : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [e]; ring

theorem swap_Em (hB : Base μ L V) (hI : Inv μ L ι) (s : ℂ) :
    (D.swap hB.measL hI.neg hI.invol).Em μ s = D.Ep μ (-s) := by
  unfold Dat.Ep Dat.Em tr
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero hB] with x hx
  rcases lt_or_gt_of_ne hx with h | h
  · rw [Set.indicator_of_notMem (show x ∉ {x | 0 ≤ L x} from not_le.2 h),
      Set.indicator_of_notMem (show x ∉ {x | 0 < L x} from not_lt.2 h.le), zero_mul, zero_mul]
  · rw [Set.indicator_of_mem (show x ∈ {x | 0 ≤ L x} from h.le),
      Set.indicator_of_mem (show x ∈ {x | 0 < L x} from h)]
    change D.θ x * (cexp (L x : ℂ) * (D.κ x)⁻¹)⁻¹ * cexp ((1 - s) * (L x : ℂ)) =
      D.θ x * D.κ x * cexp (-s * (L x : ℂ))
    have e : cexp (-s * (L x : ℂ)) = (cexp (L x : ℂ))⁻¹ * cexp ((1 - s) * (L x : ℂ)) := by
      rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
    rw [e, mul_inv, inv_inv]; ring

/-! ### the continuation -/

theorem E_differentiable (hB : Base μ L V) :
    Differentiable ℂ (fun s => D.Ep μ s + D.Em μ s) :=
  (D.Ep_differentiable hB).add (D.Em_differentiable hB)

/-- the case of a multiplier that is not trivial on the fibres of `L` -/
theorem main_nontriv (hB : Base μ L V) (hI : Inv μ L ι) {τ : X → X} (hτ : Measurable τ)
    (hτμ : Measure.map τ μ = μ) (hτL : ∀ x, L (τ x) = L x) {k : ℂ} (hk : k ≠ 1)
    (hκ : ∀ x, D.κ (τ x) = k * D.κ x) :
    (∀ s : ℂ, 1 - D.σ < s.re → D.Ep μ s + D.Em μ s = D.W μ s) ∧
    (∀ s : ℂ, D.σ < s.re →
      D.Ep μ (-s) + D.Em μ (-s) = (D.swap hB.measL hI.neg hI.invol).W μ s) := by
  constructor
  · intro s hs
    rw [D.W_eq hB hI hs, D.P_nontriv hB hτ hτμ hτL hk hκ, D.P_nontriv hB hτ hτμ hτL hk hκ]
    ring
  · intro s hs
    set D' := D.swap hB.measL hI.neg hI.invol with hD'
    have hs' : 1 - D'.σ < s.re := by
      change 1 - (1 - D.σ) < s.re; linarith
    have hk' : k⁻¹ ≠ 1 := fun h => hk (inv_eq_one.1 h)
    have hκ' : ∀ x, D'.κ (τ x) = k⁻¹ * D'.κ x := by
      intro x
      change cexp (L (τ x) : ℂ) * (D.κ (τ x))⁻¹ = k⁻¹ * (cexp (L x : ℂ) * (D.κ x)⁻¹)
      rw [hτL, hκ, mul_inv]; ring
    rw [D'.W_eq hB hI hs', D'.P_nontriv hB hτ hτμ hτL hk' hκ',
      D'.P_nontriv hB hτ hτμ hτL hk' hκ', hD', D.swap_Ep hB hI, D.swap_Em hB hI]
    ring

/-- the polar part -/
noncomputable def pol (V : ℝ) (a b s₀ s : ℂ) : ℂ := b * V / (s - s₀ - 1) - a * V / (s - s₀)

/-- the continuation before normalization -/
noncomputable def Mf (μ : Measure X) (V : ℝ) (s₀ s : ℂ) : ℂ :=
  D.Ep μ s + D.Em μ s + pol V D.a D.b s₀ s

/-- the continuation, in normal form -/
noncomputable def Mt (μ : Measure X) (V : ℝ) (s₀ : ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (D.Mf μ V s₀) Set.univ

lemma re_s₀ (hB : Base μ L V) {s₀ : ℂ} (hκ : ∀ x, D.κ x = cexp (-s₀ * (L x : ℂ))) :
    s₀.re = -D.σ := by
  obtain ⟨x, hx⟩ := hB.exists_pos
  have h1 := D.nκ x
  rw [hκ x, norm_cexp_mul] at h1
  have h2 := Real.exp_injective h1
  simp only [Complex.neg_re] at h2
  have h3 : (-s₀.re - D.σ) * L x = 0 := by linarith
  rcases mul_eq_zero.1 h3 with h | h
  · linarith
  · exact absurd h hx.ne'

lemma pol_analyticAt (V : ℝ) (a b s₀ : ℂ) {s : ℂ} (h0 : s ≠ s₀) (h1 : s ≠ s₀ + 1) :
    AnalyticAt ℂ (pol V a b s₀) s := by
  have e1 : AnalyticAt ℂ (fun s : ℂ => b * V / (s - s₀ - 1)) s :=
    analyticAt_const.div ((analyticAt_id.sub analyticAt_const).sub analyticAt_const)
      (fun h => h1 (by linear_combination h))
  have e2 : AnalyticAt ℂ (fun s : ℂ => a * V / (s - s₀)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 h0)
  exact e1.sub e2

lemma pol_meromorphicAt (V : ℝ) (a b s₀ s : ℂ) : MeromorphicAt (pol V a b s₀) s := by
  have e1 : MeromorphicAt (fun s : ℂ => b * V / (s - s₀ - 1)) s :=
    (MeromorphicAt.const _ _).div (((MeromorphicAt.id s).sub (MeromorphicAt.const _ _)).sub
      (MeromorphicAt.const _ _))
  have e2 : MeromorphicAt (fun s : ℂ => a * V / (s - s₀)) s :=
    (MeromorphicAt.const _ _).div ((MeromorphicAt.id s).sub (MeromorphicAt.const _ _))
  exact e1.sub e2

lemma Mf_meromorphicOn (hB : Base μ L V) (s₀ : ℂ) : MeromorphicOn (D.Mf μ V s₀) Set.univ :=
  fun s _ => ((D.E_differentiable hB).analyticAt s).meromorphicAt.add
    (pol_meromorphicAt V D.a D.b s₀ s)

lemma Mf_analyticAt (hB : Base μ L V) (s₀ : ℂ) {s : ℂ} (h0 : s ≠ s₀) (h1 : s ≠ s₀ + 1) :
    AnalyticAt ℂ (D.Mf μ V s₀) s :=
  ((D.E_differentiable hB).analyticAt s).add (pol_analyticAt V D.a D.b s₀ h0 h1)

lemma Mt_eq (hB : Base μ L V) (s₀ : ℂ) {s : ℂ} (h0 : s ≠ s₀) (h1 : s ≠ s₀ + 1) :
    D.Mt μ V s₀ s = D.Mf μ V s₀ s := by
  unfold Dat.Mt
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt (D.Mf_meromorphicOn hB s₀) (Set.mem_univ s),
    toMeromorphicNFAt_eq_self.2 (D.Mf_analyticAt hB s₀ h0 h1).meromorphicNFAt]

/-- the case `κ = e^{-s₀ L}` -/
theorem main_triv (hB : Base μ L V) (hI : Inv μ L ι) {s₀ : ℂ}
    (hκ : ∀ x, D.κ x = cexp (-s₀ * (L x : ℂ))) :
    MeromorphicNFOn (D.Mt μ V s₀) Set.univ ∧
    MeromorphicNFOn (fun s => D.Mt μ V s₀ (-s)) Set.univ ∧
    (∀ s : ℂ, 1 - D.σ < s.re → D.Mt μ V s₀ s = D.W μ s) ∧
    (∀ s : ℂ, s ≠ s₀ → s ≠ s₀ + 1 → AnalyticAt ℂ (D.Mt μ V s₀) s) ∧
    Tendsto (fun s => (s - s₀) * D.Mt μ V s₀ s) (𝓝[≠] s₀) (𝓝 (-(V : ℂ) * D.a)) ∧
    Tendsto (fun s => (s - (s₀ + 1)) * D.Mt μ V s₀ s) (𝓝[≠] (s₀ + 1)) (𝓝 ((V : ℂ) * D.b)) ∧
    (∀ s : ℂ, D.σ < s.re →
      D.Mt μ V s₀ (-s) = (D.swap hB.measL hI.neg hI.invol).W μ s) := by
  have hre := D.re_s₀ hB hκ
  have hNF : MeromorphicNFOn (D.Mt μ V s₀) Set.univ :=
    meromorphicNFOn_toMeromorphicNFOn (D.Mf μ V s₀) Set.univ
  have hEc : Continuous (fun s => D.Ep μ s + D.Em μ s) := (D.E_differentiable hB).continuous
  refine ⟨hNF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _
    have h := hNF (Set.mem_univ (-s))
    exact MeromorphicNFAt.comp_analyticAt (g := fun s : ℂ => -s) h analyticAt_id.neg
  · intro s hs
    have h0 : s ≠ s₀ := fun h => by rw [h, hre] at hs; linarith
    have h1 : s ≠ s₀ + 1 := fun h => by
      rw [h] at hs; simp only [Complex.add_re, Complex.one_re] at hs; linarith
    rw [D.Mt_eq hB s₀ h0 h1, D.W_eq hB hI hs,
      D.P_triv hB hκ (s := s - 1) (by
        simp only [Complex.sub_re, Complex.one_re]; linarith),
      D.P_triv hB hκ (s := s) (by simp only [Complex.sub_re]; linarith)]
    unfold Dat.Mf pol
    have e : s - 1 - s₀ = s - s₀ - 1 := by ring
    rw [e]; ring
  · intro s h0 h1
    have hev : ∀ᶠ z in 𝓝 s, D.Mt μ V s₀ z = D.Mf μ V s₀ z := by
      have ho : IsOpen {z : ℂ | z ≠ s₀ ∧ z ≠ s₀ + 1} := isOpen_ne.inter isOpen_ne
      filter_upwards [ho.mem_nhds ⟨h0, h1⟩] with z hz
      exact D.Mt_eq hB s₀ hz.1 hz.2
    exact (D.Mf_analyticAt hB s₀ h0 h1).congr (Filter.EventuallyEq.symm hev)
  · have hev : (fun s => (s - s₀) * D.Mt μ V s₀ s) =ᶠ[𝓝[≠] s₀]
        fun s => (s - s₀) * (D.Ep μ s + D.Em μ s + D.b * V / (s - s₀ - 1)) - D.a * V := by
      have h1 := (D.Mf_meromorphicOn hB s₀).toMeromorphicNFOn_eq_self_on_nhdsNE
        (Set.mem_univ s₀)
      filter_upwards [h1, self_mem_nhdsWithin] with s hs hne
      have hne' : s - s₀ ≠ 0 := sub_ne_zero.2 hne
      change (s - s₀) * D.Mt μ V s₀ s = _
      unfold Dat.Mt
      rw [hs]
      unfold Dat.Mf pol
      field_simp
      ring
    have hc : ContinuousAt (fun s => (s - s₀) * (D.Ep μ s + D.Em μ s + D.b * V / (s - s₀ - 1))
        - D.a * V) s₀ := by
      have h2 : ContinuousAt (fun s : ℂ => D.b * V / (s - s₀ - 1)) s₀ :=
        continuousAt_const.div ((continuousAt_id.sub continuousAt_const).sub continuousAt_const)
          (by simp)
      exact (((continuousAt_id.sub continuousAt_const).mul (hEc.continuousAt.add h2)).sub
        continuousAt_const)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀}ᶜ))
    simp only [sub_self, zero_mul, zero_sub] at ht
    have ht' : Tendsto (fun s => (s - s₀) * (D.Ep μ s + D.Em μ s + D.b * V / (s - s₀ - 1))
        - D.a * V) (𝓝[≠] s₀) (𝓝 (-(V : ℂ) * D.a)) := by
      convert ht using 2; ring
    exact ht'.congr' hev.symm
  · have hev : (fun s => (s - (s₀ + 1)) * D.Mt μ V s₀ s) =ᶠ[𝓝[≠] (s₀ + 1)]
        fun s => (s - (s₀ + 1)) * (D.Ep μ s + D.Em μ s - D.a * V / (s - s₀)) + D.b * V := by
      have h1 := (D.Mf_meromorphicOn hB s₀).toMeromorphicNFOn_eq_self_on_nhdsNE
        (Set.mem_univ (s₀ + 1))
      filter_upwards [h1, self_mem_nhdsWithin] with s hs hne
      have hne' : s - s₀ - 1 ≠ 0 := fun h => hne (by
        change s = s₀ + 1; linear_combination h)
      change (s - (s₀ + 1)) * D.Mt μ V s₀ s = _
      unfold Dat.Mt
      rw [hs]
      unfold Dat.Mf pol
      field_simp
      ring
    have hc : ContinuousAt (fun s => (s - (s₀ + 1)) * (D.Ep μ s + D.Em μ s - D.a * V / (s - s₀))
        + D.b * V) (s₀ + 1) := by
      have h2 : ContinuousAt (fun s : ℂ => D.a * V / (s - s₀)) (s₀ + 1) :=
        continuousAt_const.div (continuousAt_id.sub continuousAt_const) (by simp)
      exact (((continuousAt_id.sub continuousAt_const).mul (hEc.continuousAt.sub h2)).add
        continuousAt_const)
    have ht := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {s₀ + 1}ᶜ))
    simp only [sub_self, zero_mul, zero_add] at ht
    have ht' : Tendsto (fun s => (s - (s₀ + 1)) * (D.Ep μ s + D.Em μ s - D.a * V / (s - s₀))
        + D.b * V) (𝓝[≠] (s₀ + 1)) (𝓝 ((V : ℂ) * D.b)) := by
      convert ht using 2; ring
    exact ht'.congr' hev.symm
  · intro s hs
    set D' := D.swap hB.measL hI.neg hI.invol with hD'
    have h0 : -s ≠ s₀ := fun h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re] at this
      rw [hre] at this; linarith
    have h1 : -s ≠ s₀ + 1 := fun h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.add_re, Complex.one_re] at this
      rw [hre] at this; linarith
    have hs' : 1 - D'.σ < s.re := by
      change 1 - (1 - D.σ) < s.re; linarith
    have hκ' : ∀ x, D'.κ x = cexp (-(-1 - s₀) * (L x : ℂ)) := by
      intro x
      change cexp (L x : ℂ) * (D.κ x)⁻¹ = _
      rw [hκ x, ← Complex.exp_neg, ← Complex.exp_add]
      congr 1; ring
    rw [D.Mt_eq hB s₀ h0 h1, D'.W_eq hB hI hs',
      D'.P_triv hB hκ' (s := s - 1) (by
        simp only [Complex.sub_re, Complex.one_re, Complex.neg_re]; rw [hre]; linarith),
      D'.P_triv hB hκ' (s := s) (by
        simp only [Complex.sub_re, Complex.one_re, Complex.neg_re]; rw [hre]; linarith),
      hD', D.swap_Ep hB hI, D.swap_Em hB hI]
    change D.Ep μ (-s) + D.Em μ (-s) + pol V D.a D.b s₀ (-s) =
      D.Em μ (-s) + D.Ep μ (-s) + D.a * (V / (s - 1 - (-1 - s₀))) - D.b * (V / (s - (-1 - s₀)))
    unfold pol
    have e1 : -s - s₀ - 1 = -(s - (-1 - s₀)) := by ring
    have e2 : -s - s₀ = -(s - 1 - (-1 - s₀)) := by ring
    rw [e1, e2, div_neg, div_neg]
    ring

end Dat

end TZAna

/-!
# The norm on idele classes, descent of invariant functions, quasi-characters
-/

open MasulloGRH NumberField IsDedekindDomain MeasureTheory Set Complex
open scoped ENNReal

namespace TZNB

variable (F : Type*) [Field F] [NumberField F]

instance instT2Idele : T2Space (IdeleGroup F) := (idele_group_topology F).1
instance instT2Class : T2Space (IdeleClassGroup F) := (idele_class_group_topology F).2.2.1
instance instLCClass : LocallyCompactSpace (IdeleClassGroup F) :=
  (idele_class_group_topology F).2.2.2.1

lemma continuous_ideleNorm : Continuous (ideleNorm : IdeleGroup F → ℝ) :=
  (idele_group_topology F).2.2.2.1

variable {F}

lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h :=
  (idele_group_topology F).2.2.2.2.1 g h

lemma ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g :=
  (idele_group_topology F).2.2.2.2.2.1 g

lemma ideleNorm_principal (ξ : Fˣ) : ideleNorm (principalIdele F ξ) = 1 :=
  (idele_class_group_topology F).2.2.2.2.1 ξ

lemma ideleNorm_one : ideleNorm (1 : IdeleGroup F) = 1 := by
  have := ideleNorm_principal (F := F) 1
  rwa [map_one] at this

lemma ideleNorm_inv (g : IdeleGroup F) : ideleNorm g⁻¹ = (ideleNorm g)⁻¹ := by
  have h := ideleNorm_mul g g⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- two ideles in the same class differ by a principal idele -/
lemma exists_principal {a b : IdeleGroup F}
    (h : (QuotientGroup.mk a : IdeleClassGroup F) = QuotientGroup.mk b) :
    ∃ ξ : Fˣ, b = principalIdele F ξ * a := by
  rw [QuotientGroup.eq] at h
  obtain ⟨ξ, hξ⟩ := h
  exact ⟨ξ, by rw [hξ, mul_comm (a⁻¹ * b) a, mul_inv_cancel_left]⟩

/-- a function invariant under principal ideles is constant on classes -/
lemma inv_desc {M : Type*} {φ : IdeleGroup F → M}
    (hφ : ∀ (ξ : Fˣ) (g : IdeleGroup F), φ (principalIdele F ξ * g) = φ g) {a b : IdeleGroup F}
    (h : (QuotientGroup.mk a : IdeleClassGroup F) = QuotientGroup.mk b) : φ a = φ b := by
  obtain ⟨ξ, rfl⟩ := exists_principal h
  exact (hφ ξ a).symm

lemma out_mk {M : Type*} {φ : IdeleGroup F → M}
    (hφ : ∀ (ξ : Fˣ) (g : IdeleGroup F), φ (principalIdele F ξ * g) = φ g) (g : IdeleGroup F) :
    φ (QuotientGroup.mk g : IdeleClassGroup F).out = φ g :=
  inv_desc hφ (QuotientGroup.out_eq' _)

lemma continuous_desc {M : Type*} [TopologicalSpace M] {φ : IdeleGroup F → M}
    (hφ : ∀ (ξ : Fˣ) (g : IdeleGroup F), φ (principalIdele F ξ * g) = φ g)
    (hc : Continuous φ) : Continuous (fun x : IdeleClassGroup F => φ x.out) := by
  rw [(QuotientGroup.isQuotientMap_mk (principalIdeles F)).continuous_iff]
  have : (fun x : IdeleClassGroup F => φ x.out) ∘
      (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) = φ := by
    funext g; exact out_mk hφ g
  rw [this]; exact hc

lemma ideleNorm_inv_principal (ξ : Fˣ) (g : IdeleGroup F) :
    ideleNorm (principalIdele F ξ * g) = ideleNorm g := by
  rw [ideleNorm_mul, ideleNorm_principal, one_mul]

/-- the logarithm of the norm of a class -/
noncomputable def lg (x : IdeleClassGroup F) : ℝ := Real.log (ideleNorm x.out)

lemma nb_mk (g : IdeleGroup F) :
    ideleNorm (QuotientGroup.mk g : IdeleClassGroup F).out = ideleNorm g :=
  out_mk ideleNorm_inv_principal g

lemma lg_mk (g : IdeleGroup F) : lg (QuotientGroup.mk g : IdeleClassGroup F) =
    Real.log (ideleNorm g) := by
  unfold lg; rw [nb_mk]

lemma continuous_lg : Continuous (lg : IdeleClassGroup F → ℝ) :=
  (continuous_desc ideleNorm_inv_principal (continuous_ideleNorm F)).log
    (fun x => (ideleNorm_pos _).ne')

lemma lg_inv (x : IdeleClassGroup F) : lg x⁻¹ = -lg x := by
  induction x using QuotientGroup.induction_on with | _ a => ?_
  rw [← QuotientGroup.mk_inv, lg_mk, lg_mk, ideleNorm_inv, Real.log_inv]

lemma lg_mul (x y : IdeleClassGroup F) : lg (x * y) = lg x + lg y := by
  induction x using QuotientGroup.induction_on with | _ a => ?_
  induction y using QuotientGroup.induction_on with | _ b => ?_
  rw [← QuotientGroup.mk_mul, lg_mk, lg_mk, lg_mk, ideleNorm_mul,
    Real.log_mul (ideleNorm_pos a).ne' (ideleNorm_pos b).ne']

lemma exists_norm_eq (t : ℝ) (ht : 0 < t) : ∃ g : IdeleGroup F, ideleNorm g = t :=
  (idele_class_group_topology F).2.2.2.2.2.1 t ht

lemma cexp_lg (g : IdeleGroup F) :
    cexp ((Real.log (ideleNorm g) : ℝ) : ℂ) = ((ideleNorm g : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log (ideleNorm_pos g)]

lemma cpow_eq (g : IdeleGroup F) (s : ℂ) :
    ((ideleNorm g : ℝ) : ℂ) ^ s = cexp (s * ((Real.log (ideleNorm g) : ℝ) : ℂ)) := by
  have hne : ((ideleNorm g : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ideleNorm_pos g).ne'
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log (ideleNorm_pos g).le, mul_comm]

end TZNB

/-!
# Quasi-characters and unfolding of zeta integrals
-/

open MasulloGRH NumberField IsDedekindDomain MeasureTheory Set Complex
open scoped ENNReal

namespace TZQC

open TZNB

variable {F : Type*} [Field F] [NumberField F]

/-! ### the measure-theoretic setting on `C_F` -/

lemma base : TZAna.Base (tamagawaIdeleClass F) (lg : IdeleClassGroup F → ℝ)
    (tamagawaClassVolume F) :=
  ⟨continuous_lg.measurable, dedekindZeta_residue_pos F,
    (tamagawa_measures_wellDefined F).2.2.2.2.1⟩

omit [Field F] [NumberField F] in
lemma inv_inv_aux {H : Type*} [Group H] (x : H) : x⁻¹⁻¹ = x := inv_inv x

lemma invI : TZAna.Inv (tamagawaIdeleClass F) (lg : IdeleClassGroup F → ℝ) (fun x => x⁻¹) :=
  ⟨continuous_inv.measurable, (tamagawa_measures_wellDefined F).2.2.2.2.2, lg_inv,
    fun x => inv_inv_aux x⟩

instance instHaarClass : (tamagawaIdeleClass F).IsHaarMeasure :=
  (tamagawa_measures_wellDefined F).1.1

/-! ### quasi-characters -/

variable {c : IdeleGroup F → ℂ}

lemma qc_one (hc : IsQuasiCharacter c) : c 1 = 1 := by
  have h := hc.2.1 1 1
  rw [mul_one] at h
  exact mul_left_cancel₀ (hc.2.2.1 1) (by rw [mul_one]; exact h.symm)

lemma qc_inv (hc : IsQuasiCharacter c) (g : IdeleGroup F) : c g⁻¹ = (c g)⁻¹ := by
  have h := hc.2.1 g g⁻¹
  rw [mul_inv_cancel, qc_one hc] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma qc_pow (hc : IsQuasiCharacter c) (g : IdeleGroup F) (n : ℕ) : c (g ^ n) = c g ^ n := by
  induction n with
  | zero => simp [qc_one hc]
  | succ n ih => rw [pow_succ, hc.2.1, ih, pow_succ]

lemma qc_principal (hc : IsQuasiCharacter c) (ξ : Fˣ) (g : IdeleGroup F) :
    c (principalIdele F ξ * g) = c g := by
  rw [hc.2.1, hc.2.2.2, one_mul]

lemma ideleNorm_pow (g : IdeleGroup F) (n : ℕ) : ideleNorm (g ^ n) = ideleNorm g ^ n := by
  induction n with
  | zero => simp [ideleNorm_one]
  | succ n ih => rw [pow_succ, ideleNorm_mul, ih, pow_succ]

lemma norm_eq_one_of_norm_one (hc : IsQuasiCharacter c) {g : IdeleGroup F}
    (hg : ideleNorm g = 1) : ‖c g‖ = 1 := by
  have hC1 := (idele_class_group_norm_one_compact F).1.2
  have hcont : Continuous (fun x : IdeleClassGroup F => ‖c x.out‖) :=
    (continuous_desc (qc_principal hc) hc.1).norm
  obtain ⟨B, hB⟩ := hC1.exists_bound_of_continuousOn hcont.continuousOn
  have key : ∀ g : IdeleGroup F, ideleNorm g = 1 → ‖c g‖ ≤ 1 := by
    intro g hg
    by_contra hlt
    push_neg at hlt
    have hpow : ∀ n : ℕ, ‖c g‖ ^ n ≤ B := by
      intro n
      have hmem : (QuotientGroup.mk (g ^ n) : IdeleClassGroup F) ∈
          (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' {g | ideleNorm g = 1} :=
        ⟨g ^ n, by change ideleNorm (g ^ n) = 1; rw [ideleNorm_pow, hg, one_pow], rfl⟩
      have := hB _ hmem
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), out_mk (qc_principal hc), qc_pow hc,
        norm_pow] at this
      exact this
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hlt
    exact absurd (hpow n) (not_le.2 hn)
  refine le_antisymm (key g hg) ?_
  have h2 := key g⁻¹ (by rw [ideleNorm_inv, hg, inv_one])
  rw [qc_inv hc, norm_inv] at h2
  have hpos : 0 < ‖c g‖ := norm_pos_iff.2 (hc.2.2.1 g)
  exact (inv_le_one₀ hpos).1 h2

/-- a quasi-character is `|·|^z` up to its restriction to the ideles of norm one -/
theorem exists_exp (hc : IsQuasiCharacter c) :
    ∃ z : ℂ, (∀ g : IdeleGroup F, ‖c g‖ = Real.exp (z.re * Real.log (ideleNorm g))) ∧
      ((∀ g : IdeleGroup F, ideleNorm g = 1 → c g = 1) →
        ∀ g : IdeleGroup F, c g = cexp (z * ((Real.log (ideleNorm g) : ℝ) : ℂ))) := by
  obtain ⟨σs, hσc, hσm, hσn⟩ := (idele_class_group_topology F).2.2.2.2.2.2
  set cb : IdeleClassGroup F → ℂ := fun x => c x.out with hcb
  have hcbc : Continuous cb := continuous_desc (qc_principal hc) hc.1
  have hcbmk : ∀ g : IdeleGroup F, cb (QuotientGroup.mk g) = c g := fun g =>
    out_mk (qc_principal hc) g
  have hcbmul : ∀ x y : IdeleClassGroup F, cb (x * y) = cb x * cb y := by
    intro x y
    induction x using QuotientGroup.induction_on with | _ a => ?_
    induction y using QuotientGroup.induction_on with | _ b => ?_
    rw [← QuotientGroup.mk_mul, hcbmk, hcbmk, hcbmk, hc.2.1]
  set ψ : ℝ → ℂ := fun u => cb (σs (Real.exp u)) with hψ
  have hψc : Continuous ψ :=
    hcbc.comp (hσc.comp_continuous Real.continuous_exp (fun u => Real.exp_pos u))
  have hψm : ∀ u v, ψ (u + v) = ψ u * ψ v := by
    intro u v
    simp only [hψ]
    rw [Real.exp_add, hσm _ _ (Real.exp_pos u) (Real.exp_pos v), hcbmul]
  have hψne : ∀ u, ψ u ≠ 0 := fun u => hc.2.2.1 _
  have hψ0 : ψ 0 = 1 := by
    have h := hψm 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (hψne 0) (by rw [mul_one]; exact h.symm)
  obtain ⟨z, hz⟩ := TZAna.exists_exp_of_continuous_mul hψc hψm hψ0
  have hdec : ∀ g : IdeleGroup F, ∃ h : IdeleGroup F, ideleNorm h = 1 ∧
      c g = c h * cexp (z * ((Real.log (ideleNorm g) : ℝ) : ℂ)) := by
    intro g
    set u := Real.log (ideleNorm g) with hu
    obtain ⟨g', hg'mk, hg'n⟩ := hσn (Real.exp u) (Real.exp_pos u)
    have hg'c : c g' = cexp (z * (u : ℂ)) := by
      rw [← hz u]
      simp only [hψ]
      rw [← hg'mk, hcbmk]
    refine ⟨g * g'⁻¹, ?_, ?_⟩
    · rw [ideleNorm_mul, ideleNorm_inv, hg'n, hu, Real.exp_log (ideleNorm_pos g)]
      exact mul_inv_cancel₀ (ideleNorm_pos g).ne'
    · rw [← hg'c, ← hc.2.1, inv_mul_cancel_right]
  refine ⟨z, fun g => ?_, fun htriv g => ?_⟩
  · obtain ⟨h, hh, hgh⟩ := hdec g
    rw [hgh, norm_mul, norm_eq_one_of_norm_one hc hh, one_mul, TZAna.norm_cexp_mul]
  · obtain ⟨h, hh, hgh⟩ := hdec g
    rw [hgh, htriv h hh, one_mul]

lemma abscissa_eq {c : IdeleGroup F → ℂ} {σ : ℝ}
    (h : ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ) : quasiAbscissa c = σ := by
  have hex : ∃ σ : ℝ, ∀ g : IdeleGroup F, ‖c g‖ = ideleNorm g ^ σ := ⟨σ, h⟩
  have hdef : quasiAbscissa c = hex.choose := by
    unfold quasiAbscissa
    exact dif_pos hex
  rw [hdef]
  obtain ⟨g, hg⟩ := exists_norm_eq (F := F) (Real.exp 1) (Real.exp_pos 1)
  have h1 := hex.choose_spec g
  rw [h g, hg, Real.exp_one_rpow, Real.exp_one_rpow] at h1
  exact (Real.exp_injective h1).symm

lemma rpow_eq_exp (g : IdeleGroup F) (σ : ℝ) :
    ideleNorm g ^ σ = Real.exp (σ * Real.log (ideleNorm g)) := by
  rw [Real.rpow_def_of_pos (ideleNorm_pos g), mul_comm]

lemma twist_eq (c : IdeleGroup F → ℂ) (s : ℂ) (g : IdeleGroup F) :
    quasiTwist c s g = c g * cexp (s * ((Real.log (ideleNorm g) : ℝ) : ℂ)) := by
  unfold quasiTwist normQuasiChar
  rw [cpow_eq]

lemma coe_principal_mul (ξ : Fˣ) (g : IdeleGroup F) :
    ((principalIdele F ξ * g : IdeleGroup F) : AdeleRing (𝓞 F) F) =
      algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F) := by
  rw [Units.val_mul]; rfl

/-- θ-series are invariant under principal ideles -/
lemma theta_principal (φ : AdeleRing (𝓞 F) F → ℂ) (ξ : Fˣ) (g : IdeleGroup F) :
    adelicThetaFun φ (principalIdele F ξ * g) = adelicThetaFun φ g := by
  unfold adelicThetaFun
  have e : ∀ η : Fˣ, algebraMap F (AdeleRing (𝓞 F) F) (η : F) *
      ((principalIdele F ξ * g : IdeleGroup F) : AdeleRing (𝓞 F) F) =
      algebraMap F (AdeleRing (𝓞 F) F) ((η * ξ : Fˣ) : F) * (g : AdeleRing (𝓞 F) F) := by
    intro η
    rw [coe_principal_mul, Units.val_mul, map_mul, mul_assoc]
  simp_rw [e]
  exact (Equiv.mulRight ξ).tsum_eq
    (fun η : Fˣ => φ (algebraMap F (AdeleRing (𝓞 F) F) (η : F) * (g : AdeleRing (𝓞 F) F)))

/-! ### unfolding -/

/-- absolute convergence on the ideles and unfolding to the idele classes -/
theorem unfold (φ : AdeleRing (𝓞 F) F → ℂ) (cq : IdeleGroup F → ℂ) (r : ℝ)
    (hφm : Measurable (fun g : IdeleGroup F => φ (g : AdeleRing (𝓞 F) F)))
    (habs : ∀ N : ℕ, ∃ C : ℝ, ∀ g : IdeleGroup F,
      Summable (fun ξ : Fˣ => ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
        (g : AdeleRing (𝓞 F) F))‖) ∧
      (1 ≤ ideleNorm g →
        ∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤
          C * ideleNorm g ^ (-(N : ℝ))) ∧
      (ideleNorm g ≤ 1 →
        ∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤
          C * (ideleNorm g)⁻¹))
    (hcc : Continuous cq) (hcinv : ∀ (ξ : Fˣ) (g : IdeleGroup F), cq (principalIdele F ξ * g) = cq g)
    (hcn : ∀ g : IdeleGroup F, ‖cq g‖ = Real.exp (r * Real.log (ideleNorm g))) (hr : 1 < r) :
    Integrable (fun g : IdeleGroup F => φ (g : AdeleRing (𝓞 F) F) * cq g) (tamagawaIdele F) ∧
    ∫ g : IdeleGroup F, φ (g : AdeleRing (𝓞 F) F) * cq g ∂(tamagawaIdele F) =
      ∫ x : IdeleClassGroup F, adelicThetaFun φ x.out * cq x.out ∂(tamagawaIdeleClass F) := by
  have hT := tamagawa_measures_wellDefined F
  have hlin := hT.2.2.1
  have hboch := hT.2.2.2.1
  set Φ : IdeleGroup F → ℂ := fun g => φ (g : AdeleRing (𝓞 F) F) * cq g with hΦ
  have hΦm : Measurable Φ := hφm.mul hcc.measurable
  have hΦξ : ∀ (ξ : Fˣ) (g : IdeleGroup F), Φ (principalIdele F ξ * g) =
      φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F)) * cq g := by
    intro ξ g
    simp only [hΦ]
    rw [coe_principal_mul, hcinv]
  obtain ⟨N, hN⟩ := exists_nat_ge (r + 1)
  obtain ⟨C, hC⟩ := habs N
  set η : ℝ := min (r - 1) 1 with hη
  have hη0 : 0 < η := lt_min (by linarith) one_pos
  have hη1 : η ≤ r - 1 := min_le_left _ _
  have hη2 : η ≤ 1 := min_le_right _ _
  have hpt : ∀ x : IdeleClassGroup F, ∑' ξ : Fˣ, ‖Φ (principalIdele F ξ * x.out)‖ₑ ≤
      ENNReal.ofReal (|C| * Real.exp (-η * |lg x|)) := by
    intro x
    set g := x.out with hg
    obtain ⟨hs, hb1, hb2⟩ := hC g
    have hpos := ideleNorm_pos g
    have e1 : ∀ ξ : Fˣ, ‖Φ (principalIdele F ξ * g)‖ₑ = ENNReal.ofReal
        (‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ * ‖cq g‖) := by
      intro ξ
      rw [hΦξ, ← ofReal_norm, norm_mul]
    simp_rw [e1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun ξ => by positivity) (hs.mul_right _), tsum_mul_right]
    apply ENNReal.ofReal_le_ofReal
    have hS : ∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
        (g : AdeleRing (𝓞 F) F))‖ ≤ |C| * TZAna.wt N 1 (lg x) := by
      by_cases hx : 0 ≤ lg x
      · have h1 : 1 ≤ ideleNorm g := by
          have : 0 ≤ Real.log (ideleNorm g) := hx
          exact (Real.log_nonneg_iff hpos).1 this
        rw [TZAna.wt_of_nonneg hx]
        refine (hb1 h1).trans ?_
        rw [rpow_eq_exp]
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
      · push_neg at hx
        have h1 : ideleNorm g ≤ 1 := by
          have : Real.log (ideleNorm g) < 0 := hx
          exact ((Real.log_neg_iff hpos).1 this).le
        rw [TZAna.wt_of_neg hx]
        refine (hb2 h1).trans ?_
        have e2 : (ideleNorm g)⁻¹ = Real.exp (-1 * lg x) := by
          change _ = Real.exp (-1 * Real.log (ideleNorm g))
          rw [neg_one_mul, Real.exp_neg, Real.exp_log hpos]
        rw [e2]
        exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    calc (∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
          (g : AdeleRing (𝓞 F) F))‖) * ‖cq g‖
        ≤ |C| * TZAna.wt N 1 (lg x) * Real.exp (r * lg x) := by
          rw [hcn g]
          exact mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le
      _ = |C| * (TZAna.wt N 1 (lg x) * Real.exp (r * lg x)) := by ring
      _ ≤ |C| * Real.exp (-η * |lg x|) :=
          mul_le_mul_of_nonneg_left (TZAna.wt_mul_exp_le (by linarith) (by linarith))
            (abs_nonneg C)
  have hbd : Integrable (fun x : IdeleClassGroup F => |C| * Real.exp (-η * |lg x|))
      (tamagawaIdeleClass F) :=
    (base (F := F)).integrable_comp (g := fun u => |C| * Real.exp (-η * |u|))
      ((TZAna.integrable_exp_neg_abs hη0).const_mul _)
  have hfin : HasFiniteIntegral Φ (tamagawaIdele F) := by
    change ∫⁻ g, ‖Φ g‖ₑ ∂(tamagawaIdele F) < ∞
    rw [hlin (fun g => ‖Φ g‖ₑ) hΦm.enorm]
    exact (lintegral_mono hpt).trans_lt hbd.lintegral_lt_top
  have hint : Integrable Φ (tamagawaIdele F) := ⟨hΦm.aestronglyMeasurable, hfin⟩
  refine ⟨hint, ?_⟩
  rw [hboch Φ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  simp_rw [hΦξ]
  rw [tsum_mul_right]
  rfl

end TZQC

/-!
# The corrected Theorem 3.2.2.1: assembly
-/

open MasulloGRH NumberField IsDedekindDomain MeasureTheory Set Complex Filter Topology
open scoped ENNReal

namespace TZMain

open TZNB TZQC

variable {F : Type*} [Field F] [NumberField F]

/-! ### the two θ-functions on classes -/

/-- `Φ_F(f)` on classes -/
noncomputable def th (f : AdelicSchwartz F) (x : IdeleClassGroup F) : ℂ := adelicTheta f x.out

/-- `Φ_F(\hat f)` on classes -/
noncomputable def th' (f : AdelicSchwartz F) (x : IdeleClassGroup F) : ℂ :=
  adelicThetaFun (adelicFourier f) x.out

variable (f : AdelicSchwartz F)

lemma continuous_th : Continuous (th f) :=
  continuous_desc (φ := adelicTheta f) (theta_principal f.eval)
    (adelic_theta_absolute_bounds F f).2.2.1

lemma cexp_neg_lg (x : IdeleClassGroup F) :
    cexp (-((lg x : ℝ) : ℂ)) = (((ideleNorm x.out)⁻¹ : ℝ) : ℂ) := by
  have hpos := ideleNorm_pos x.out
  change cexp (-((Real.log (ideleNorm x.out) : ℝ) : ℂ)) = _
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hpos]

/-- Riemann–Roch on classes -/
lemma rr_class (x : IdeleClassGroup F) :
    th f x = cexp (-((lg x : ℝ) : ℂ)) * th' f x⁻¹ +
      cexp (-((lg x : ℝ) : ℂ)) * adelicFourier f 0 - f.eval 0 := by
  have h := (adelic_riemann_roch F f x.out).2.2
  have e : adelicThetaFun (adelicFourier f) (x.out)⁻¹ = th' f x⁻¹ := by
    unfold th'
    refine inv_desc (theta_principal (adelicFourier f)) ?_
    rw [QuotientGroup.out_eq', QuotientGroup.mk_inv, QuotientGroup.out_eq']
  rw [cexp_neg_lg]
  unfold th
  rw [h, e]

lemma th'_eq (x : IdeleClassGroup F) :
    th' f x = cexp (-((lg x : ℝ) : ℂ)) * (th f x⁻¹ + f.eval 0) - adelicFourier f 0 := by
  have h := rr_class f x⁻¹
  have e0 : th' f (x⁻¹)⁻¹ = th' f x := congrArg (th' f) (inv_inv_aux x)
  rw [e0, lg_inv] at h
  have e : cexp (-((lg x : ℝ) : ℂ)) * cexp (-(((-lg x : ℝ)) : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [h]
  linear_combination (-(th' f x) - adelicFourier f 0) * e

lemma continuous_th' : Continuous (th' f) := by
  have : th' f = fun x => cexp (-((lg x : ℝ) : ℂ)) * (th f x⁻¹ + f.eval 0) - adelicFourier f 0 :=
    funext (th'_eq f)
  rw [this]
  have h1 : Continuous (fun x : IdeleClassGroup F => cexp (-((lg x : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.comp continuous_lg).neg
  exact (h1.mul (((continuous_th f).comp continuous_inv).add continuous_const)).sub
    continuous_const

/-- bounds for a θ-series from the bounds on the absolute sums -/
lemma theta_bounds (φ : AdeleRing (𝓞 F) F → ℂ)
    (habs : ∀ N : ℕ, ∃ C : ℝ, ∀ g : IdeleGroup F,
      Summable (fun ξ : Fˣ => ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
        (g : AdeleRing (𝓞 F) F))‖) ∧
      (1 ≤ ideleNorm g →
        ∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤
          C * ideleNorm g ^ (-(N : ℝ))) ∧
      (ideleNorm g ≤ 1 →
        ∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖ ≤
          C * (ideleNorm g)⁻¹)) :
    (∀ N : ℕ, ∃ C : ℝ, ∀ x : IdeleClassGroup F, 0 ≤ lg x →
      ‖adelicThetaFun φ x.out‖ ≤ C * Real.exp (-(N : ℝ) * lg x)) ∧
    (∃ C : ℝ, ∀ x : IdeleClassGroup F, lg x ≤ 0 →
      ‖adelicThetaFun φ x.out‖ ≤ C * Real.exp (-lg x)) := by
  have hle : ∀ g : IdeleGroup F, Summable (fun ξ : Fˣ =>
      ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * (g : AdeleRing (𝓞 F) F))‖) →
      ‖adelicThetaFun φ g‖ ≤ ∑' ξ : Fˣ, ‖φ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) *
        (g : AdeleRing (𝓞 F) F))‖ := fun g hs => norm_tsum_le_tsum_norm hs
  constructor
  · intro N
    obtain ⟨C, hC⟩ := habs N
    refine ⟨C, fun x hx => ?_⟩
    obtain ⟨hs, hb1, -⟩ := hC x.out
    have hpos := ideleNorm_pos x.out
    have h1 : 1 ≤ ideleNorm x.out := (Real.log_nonneg_iff hpos).1 hx
    refine (hle _ hs).trans ((hb1 h1).trans (le_of_eq ?_))
    rw [rpow_eq_exp]; rfl
  · obtain ⟨C, hC⟩ := habs 0
    refine ⟨C, fun x hx => ?_⟩
    obtain ⟨hs, -, hb2⟩ := hC x.out
    have hpos := ideleNorm_pos x.out
    have h1 : ideleNorm x.out ≤ 1 := by
      by_contra h
      push_neg at h
      have : 0 < Real.log (ideleNorm x.out) := Real.log_pos h
      exact absurd hx (not_le.2 this)
    refine (hle _ hs).trans ((hb2 h1).trans (le_of_eq ?_))
    change _ = C * Real.exp (-Real.log (ideleNorm x.out))
    rw [Real.exp_neg, Real.exp_log hpos]

/-! ### the data attached to `f` and a quasi-character -/

variable {c₀ : IdeleGroup F → ℂ}

lemma kappa_inv (hc : IsQuasiCharacter c₀) (x : IdeleClassGroup F) :
    c₀ (x⁻¹).out * c₀ x.out = 1 := by
  induction x using QuotientGroup.induction_on with | _ a => ?_
  rw [← QuotientGroup.mk_inv, out_mk (qc_principal hc), out_mk (qc_principal hc), qc_inv hc]
  exact inv_mul_cancel₀ (hc.2.2.1 a)

/-- the data of the abstract computation -/
noncomputable def dat (hc : IsQuasiCharacter c₀) (z : ℂ)
    (hz : ∀ g : IdeleGroup F, ‖c₀ g‖ = Real.exp (z.re * Real.log (ideleNorm g))) :
    TZAna.Dat (lg : IdeleClassGroup F → ℝ) (fun x => x⁻¹) where
  θ := th f
  θ' := th' f
  κ := fun x => c₀ x.out
  a := f.eval 0
  b := adelicFourier f 0
  σ := z.re
  mθ := (continuous_th f).measurable
  mθ' := (continuous_th' f).measurable
  mκ := (continuous_desc (qc_principal hc) hc.1).measurable
  nκ := fun x => hz x.out
  κι := fun x => kappa_inv hc x
  rr := fun x => rr_class f x
  decay := (theta_bounds f.eval (adelic_theta_absolute_bounds F f).2.2.2.1).1
  decay' := (theta_bounds (adelicFourier f) (adelic_theta_absolute_bounds F f).2.2.2.2).1
  small := (theta_bounds f.eval (adelic_theta_absolute_bounds F f).2.2.2.1).2
  small' := (theta_bounds (adelicFourier f) (adelic_theta_absolute_bounds F f).2.2.2.2).2

/-! ### twists -/

lemma twist_continuous {c : IdeleGroup F → ℂ} (hcc : Continuous c) (s : ℂ) :
    Continuous (quasiTwist c s) := by
  have : quasiTwist c s = fun g => c g * cexp (s * ((Real.log (ideleNorm g) : ℝ) : ℂ)) :=
    funext (twist_eq c s)
  rw [this]
  exact hcc.mul (Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp ((continuous_ideleNorm F).log
      (fun g => (ideleNorm_pos g).ne')))))

lemma twist_inv {c : IdeleGroup F → ℂ}
    (hcinv : ∀ (ξ : Fˣ) (g : IdeleGroup F), c (principalIdele F ξ * g) = c g) (s : ℂ) (ξ : Fˣ)
    (g : IdeleGroup F) : quasiTwist c s (principalIdele F ξ * g) = quasiTwist c s g := by
  rw [twist_eq, twist_eq, hcinv, ideleNorm_inv_principal]

lemma twist_norm {c : IdeleGroup F → ℂ} {ρ : ℝ}
    (hcn : ∀ g : IdeleGroup F, ‖c g‖ = Real.exp (ρ * Real.log (ideleNorm g))) (s : ℂ)
    (g : IdeleGroup F) :
    ‖quasiTwist c s g‖ = Real.exp ((ρ + s.re) * Real.log (ideleNorm g)) := by
  rw [twist_eq, norm_mul, hcn, TZAna.norm_cexp_mul, ← Real.exp_add]
  congr 1; ring

lemma dual_continuous (hc : IsQuasiCharacter c₀) : Continuous (quasiDual c₀) := by
  unfold quasiDual
  exact (Complex.continuous_ofReal.comp (continuous_ideleNorm F)).mul (hc.1.inv₀ hc.2.2.1)

lemma dual_inv (hc : IsQuasiCharacter c₀) (ξ : Fˣ) (g : IdeleGroup F) :
    quasiDual c₀ (principalIdele F ξ * g) = quasiDual c₀ g := by
  unfold quasiDual
  rw [qc_principal hc, ideleNorm_inv_principal]

lemma dual_norm {z : ℂ}
    (hz : ∀ g : IdeleGroup F, ‖c₀ g‖ = Real.exp (z.re * Real.log (ideleNorm g)))
    (g : IdeleGroup F) :
    ‖quasiDual c₀ g‖ = Real.exp ((1 - z.re) * Real.log (ideleNorm g)) := by
  have hpos := ideleNorm_pos g
  unfold quasiDual
  rw [norm_mul, norm_inv, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    ← Real.exp_neg,
    show (1 - z.re) * Real.log (ideleNorm g) =
      Real.log (ideleNorm g) + -(z.re * Real.log (ideleNorm g)) by ring,
    Real.exp_add, Real.exp_log hpos]

lemma W_eq_mellin (hc : IsQuasiCharacter c₀) (z : ℂ)
    (hz : ∀ g : IdeleGroup F, ‖c₀ g‖ = Real.exp (z.re * Real.log (ideleNorm g))) (s : ℂ) :
    (dat f hc z hz).W (tamagawaIdeleClass F) s = thetaMellin f (quasiTwist c₀ s) := by
  unfold TZAna.Dat.W TZAna.tr thetaMellin
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change th f x * c₀ x.out * cexp (s * ((lg x : ℝ) : ℂ)) =
    adelicTheta f x.out * quasiTwist c₀ s x.out
  rw [twist_eq]
  exact mul_assoc _ _ _

lemma swapW_eq (hc : IsQuasiCharacter c₀) (z : ℂ)
    (hz : ∀ g : IdeleGroup F, ‖c₀ g‖ = Real.exp (z.re * Real.log (ideleNorm g))) (s : ℂ) :
    ((dat f hc z hz).swap (base (F := F)).measL (invI (F := F)).neg (invI (F := F)).invol).W
        (tamagawaIdeleClass F) s =
      ∫ x : IdeleClassGroup F, adelicThetaFun (adelicFourier f) x.out *
        quasiTwist (quasiDual c₀) s x.out ∂(tamagawaIdeleClass F) := by
  unfold TZAna.Dat.W TZAna.tr
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := cexp_lg x.out
  change th' f x * (cexp ((Real.log (ideleNorm x.out) : ℝ) : ℂ) * (c₀ x.out)⁻¹) *
      cexp (s * ((Real.log (ideleNorm x.out) : ℝ) : ℂ)) =
    adelicThetaFun (adelicFourier f) x.out * quasiTwist (quasiDual c₀) s x.out
  rw [twist_eq, e]
  unfold quasiDual th'
  ring

/-! ### the theorem -/

theorem main (F : Type*) [Field F] [NumberField F] (f : AdelicSchwartz F)
    (c₀ : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c₀) :
    ((∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
        Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * quasiTwist c₀ s g)
          (tamagawaIdele F)) ∧
      DifferentiableOn ℂ (fun s : ℂ => zetaIntegral f (quasiTwist c₀ s))
        {s : ℂ | 1 < quasiAbscissa c₀ + s.re}) ∧
    (∃ M M' : ℂ → ℂ, MeromorphicNFOn M Set.univ ∧ MeromorphicNFOn M' Set.univ ∧
      (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re → M s = zetaIntegral f (quasiTwist c₀ s)) ∧
      (∀ s : ℂ, quasiTwist c₀ s ≠ (fun _ => 1) → quasiTwist c₀ s ≠ normQuasiChar 1 →
        AnalyticAt ℂ M s) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = (fun _ => 1) →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds (-(tamagawaClassVolume F : ℂ) * f.eval 0))) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = normQuasiChar 1 →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds ((tamagawaClassVolume F : ℂ) * adelicFourier f 0))) ∧
      (∀ s : ℂ, 1 < quasiAbscissa (quasiDual c₀) + s.re →
        M' s = zetaIntegralFun (adelicFourier f) (quasiTwist (quasiDual c₀) s)) ∧
      (∀ s : ℂ, M s = M' (-s)) ∧
      ((¬ ∀ g : IdeleGroup F, ideleNorm g = 1 → c₀ g = 1) → Differentiable ℂ M)) ∧
    (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
      Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
        (tamagawaIdeleClass F) ∧
      thetaMellin f (quasiTwist c₀ s) = zetaIntegral f (quasiTwist c₀ s)) ∧
    (f.IsPolarFree →
      (∀ s : ℂ,
        Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
          (tamagawaIdeleClass F)) ∧
      Differentiable ℂ (fun s : ℂ => thetaMellin f (quasiTwist c₀ s))) := by
  obtain ⟨z, hz1, hz2⟩ := exists_exp hc
  have hσ : quasiAbscissa c₀ = z.re := abscissa_eq (fun g => by rw [hz1, rpow_eq_exp])
  have hσd : quasiAbscissa (quasiDual c₀) = 1 - z.re :=
    abscissa_eq (fun g => by rw [dual_norm hz1, rpow_eq_exp])
  have hB := base (F := F)
  have hI := invI (F := F)
  set D := dat f hc z hz1 with hD
  have hDσ : D.σ = z.re := rfl
  have hT3 := adelic_theta_absolute_bounds F f
  have hptw : ∀ (s : ℂ) (x : IdeleClassGroup F), D.θ x * D.κ x * cexp (s * ((lg x : ℝ) : ℂ)) =
      adelicTheta f x.out * quasiTwist c₀ s x.out := by
    intro s x
    change th f x * c₀ x.out * cexp (s * ((lg x : ℝ) : ℂ)) = _
    rw [twist_eq]
    exact mul_assoc _ _ _
  -- the half-plane of convergence
  have hA : ∀ s : ℂ, 1 < z.re + s.re →
      Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * quasiTwist c₀ s g)
        (tamagawaIdele F) ∧
      Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
        (tamagawaIdeleClass F) ∧
      thetaMellin f (quasiTwist c₀ s) = zetaIntegral f (quasiTwist c₀ s) ∧
      zetaIntegral f (quasiTwist c₀ s) = D.W (tamagawaIdeleClass F) s := by
    intro s hs
    have hu := unfold f.eval (quasiTwist c₀ s) (z.re + s.re)
      (hT3.1.measurable.comp Units.continuous_val.measurable) hT3.2.2.2.1
      (twist_continuous hc.1 s) (twist_inv (qc_principal hc) s) (twist_norm hz1 s) hs
    have hs' : 1 - D.σ < s.re := by rw [hDσ]; linarith
    have hW := W_eq_mellin f hc z hz1 s
    have hint : Integrable (fun x : IdeleClassGroup F =>
        adelicTheta f x.out * quasiTwist c₀ s x.out) (tamagawaIdeleClass F) :=
      (D.W_strip hB hs').1.congr (Filter.Eventually.of_forall fun x => hptw s x)
    have hzm : zetaIntegral f (quasiTwist c₀ s) = thetaMellin f (quasiTwist c₀ s) := hu.2
    exact ⟨hu.1, hint, hzm.symm, hzm.trans hW.symm⟩
  have hAd : ∀ s : ℂ, z.re < s.re →
      zetaIntegralFun (adelicFourier f) (quasiTwist (quasiDual c₀) s) =
        (D.swap hB.measL hI.neg hI.invol).W (tamagawaIdeleClass F) s := by
    intro s hs
    have hu := unfold (adelicFourier f) (quasiTwist (quasiDual c₀) s) ((1 - z.re) + s.re)
      (hT3.2.1.comp Units.continuous_val.measurable) hT3.2.2.2.2
      (twist_continuous (dual_continuous hc) s) (twist_inv (dual_inv hc) s)
      (twist_norm (dual_norm hz1) s) (by linarith)
    exact hu.2.trans (swapW_eq f hc z hz1 s).symm
  refine ⟨⟨fun s hs => (hA s (by rw [hσ] at hs; exact hs)).1, ?_⟩, ?_,
    fun s hs => ⟨(hA s (by rw [hσ] at hs; exact hs)).2.1,
      (hA s (by rw [hσ] at hs; exact hs)).2.2.1⟩, ?_⟩
  · -- holomorphy on the half-plane
    intro s hs
    have hs' : 1 < z.re + s.re := by
      have : 1 < quasiAbscissa c₀ + s.re := hs
      rwa [hσ] at this
    have hdiff : DifferentiableAt ℂ (D.W (tamagawaIdeleClass F)) s :=
      (D.W_strip hB (by rw [hDσ]; linarith)).2
    refine (hdiff.congr_of_eventuallyEq ?_).differentiableWithinAt
    have ho : IsOpen {w : ℂ | 1 < z.re + w.re} :=
      isOpen_lt continuous_const (continuous_const.add Complex.continuous_re)
    filter_upwards [ho.mem_nhds hs'] with w hw
    exact (hA w hw).2.2.2
  · -- continuation
    by_cases htriv : ∀ g : IdeleGroup F, ideleNorm g = 1 → c₀ g = 1
    · have hc₀ := hz2 htriv
      set s₀ : ℂ := -z with hs₀
      have hκ : ∀ x, D.κ x = cexp (-s₀ * ((lg x : ℝ) : ℂ)) := fun x => by
        rw [hs₀, neg_neg]; exact hc₀ x.out
      obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := D.main_triv hB hI hκ
      have htw : ∀ (s : ℂ) (g : IdeleGroup F), quasiTwist c₀ s g =
          cexp ((s - s₀) * ((Real.log (ideleNorm g) : ℝ) : ℂ)) := by
        intro s g
        rw [twist_eq, hc₀, ← Complex.exp_add, hs₀]
        congr 1; ring
      have hone : ∀ s₁ : ℂ, quasiTwist c₀ s₁ = (fun _ => 1) → s₁ = s₀ := by
        intro s₁ h
        have : s₁ - s₀ = 0 := TZAna.eq_zero_of_cexp_mul_eq_one (fun t => by
          obtain ⟨g, hg⟩ := exists_norm_eq (F := F) (Real.exp t) (Real.exp_pos t)
          have h1 := congrFun h g
          rw [htw, hg, Real.log_exp] at h1
          exact h1)
        exact sub_eq_zero.1 this
      have hnrm : ∀ s₁ : ℂ, quasiTwist c₀ s₁ = normQuasiChar 1 → s₁ = s₀ + 1 := by
        intro s₁ h
        have : s₁ - s₀ - 1 = 0 := TZAna.eq_zero_of_cexp_mul_eq_one (fun t => by
          obtain ⟨g, hg⟩ := exists_norm_eq (F := F) (Real.exp t) (Real.exp_pos t)
          have h1 := congrFun h g
          rw [htw] at h1
          unfold normQuasiChar at h1
          rw [cpow_eq, hg, Real.log_exp, one_mul] at h1
          have e : cexp ((s₁ - s₀ - 1) * (t : ℂ)) =
              cexp ((s₁ - s₀) * (t : ℂ)) * (cexp (t : ℂ))⁻¹ := by
            rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
          rw [e, h1, mul_inv_cancel₀ (Complex.exp_ne_zero _)])
        linear_combination this
      refine ⟨D.Mt (tamagawaIdeleClass F) (tamagawaClassVolume F) s₀,
        fun s => D.Mt (tamagawaIdeleClass F) (tamagawaClassVolume F) s₀ (-s), m1, m2, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_⟩
      · intro s hs
        have hs' : 1 < z.re + s.re := by rwa [hσ] at hs
        exact (m3 s (by rw [hDσ]; linarith)).trans (hA s hs').2.2.2.symm
      · intro s h1 h2
        refine m4 s (fun h => h1 ?_) (fun h => h2 ?_)
        · funext g
          rw [h, htw, sub_self, zero_mul, Complex.exp_zero]
        · funext g
          rw [h, htw]
          unfold normQuasiChar
          rw [cpow_eq]
          congr 1; ring
      · intro s₁ h
        rw [hone s₁ h]
        exact m5
      · intro s₁ h
        rw [hnrm s₁ h]
        exact m6
      · intro s hs
        have hs' : z.re < s.re := by rw [hσd] at hs; linarith
        exact (m7 s hs').trans (hAd s hs').symm
      · intro s
        simp only [neg_neg]
      · intro hn
        exact absurd htriv hn
    · push_neg at htriv
      obtain ⟨h, hh1, hhc⟩ := htriv
      set τ : IdeleClassGroup F → IdeleClassGroup F :=
        fun x => (QuotientGroup.mk h : IdeleClassGroup F) * x with hτdef
      have hτ : Measurable τ :=
        (continuous_const_mul (QuotientGroup.mk h : IdeleClassGroup F)).measurable
      have hτμ : Measure.map τ (tamagawaIdeleClass F) = tamagawaIdeleClass F :=
        map_mul_left_eq_self (tamagawaIdeleClass F) (QuotientGroup.mk h : IdeleClassGroup F)
      have hτL : ∀ x, lg (τ x) = lg x := by
        intro x
        simp only [hτdef]
        rw [lg_mul, lg_mk, hh1, Real.log_one, zero_add]
      have hκτ : ∀ x, D.κ (τ x) = c₀ h * D.κ x := by
        intro x
        induction x using QuotientGroup.induction_on with | _ a => ?_
        change c₀ ((QuotientGroup.mk h : IdeleClassGroup F) * QuotientGroup.mk a).out =
          c₀ h * c₀ (QuotientGroup.mk a : IdeleClassGroup F).out
        rw [← QuotientGroup.mk_mul, out_mk (qc_principal hc), out_mk (qc_principal hc), hc.2.1]
      obtain ⟨n1, n2⟩ := D.main_nontriv hB hI hτ hτμ hτL hhc hκτ
      have hMd : Differentiable ℂ (fun s => D.Ep (tamagawaIdeleClass F) s +
          D.Em (tamagawaIdeleClass F) s) := D.E_differentiable hB
      have hMd' : Differentiable ℂ (fun s => D.Ep (tamagawaIdeleClass F) (-s) +
          D.Em (tamagawaIdeleClass F) (-s)) := hMd.comp differentiable_neg
      refine ⟨fun s => D.Ep (tamagawaIdeleClass F) s + D.Em (tamagawaIdeleClass F) s,
        fun s => D.Ep (tamagawaIdeleClass F) (-s) + D.Em (tamagawaIdeleClass F) (-s),
        fun s _ => (hMd.analyticAt s).meromorphicNFAt,
        fun s _ => (hMd'.analyticAt s).meromorphicNFAt, ?_, fun s _ _ => hMd.analyticAt s,
        ?_, ?_, ?_, ?_, fun _ => hMd⟩
      · intro s hs
        have hs' : 1 < z.re + s.re := by rwa [hσ] at hs
        exact (n1 s (by rw [hDσ]; linarith)).trans (hA s hs').2.2.2.symm
      · intro s₁ h1
        exfalso
        have h2 := congrFun h1 h
        rw [twist_eq, hh1, Real.log_one] at h2
        simp at h2
        exact hhc h2
      · intro s₁ h1
        exfalso
        have h2 := congrFun h1 h
        rw [twist_eq, hh1, Real.log_one] at h2
        unfold normQuasiChar at h2
        rw [hh1] at h2
        simp at h2
        exact hhc h2
      · intro s hs
        have hs' : z.re < s.re := by rw [hσd] at hs; linarith
        exact (n2 s hs').trans (hAd s hs').symm
      · intro s
        simp only [neg_neg]
  · -- the polar-free case
    intro hpf
    have hexp := D.exp_of_polar_free lg_inv hpf.1 hpf.2
    refine ⟨fun s => ?_, ?_⟩
    · exact (D.W_strip_of_exp hB hexp s).1.congr (Filter.Eventually.of_forall fun x => hptw s x)
    · have e : (fun s : ℂ => thetaMellin f (quasiTwist c₀ s)) = D.W (tamagawaIdeleClass F) :=
        funext fun s => (W_eq_mellin f hc z hz1 s).symm
      rw [e]
      exact fun s => (D.W_strip_of_exp hB hexp s).2

end TZMain

theorem solution (F : Type*) [Field F] [NumberField F]
    (f : AdelicSchwartz F) (c₀ : IdeleGroup F → ℂ) (hc : IsQuasiCharacter c₀) :
    ((∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
        Integrable (fun g : IdeleGroup F => f.eval (g : AdeleRing (𝓞 F) F) * quasiTwist c₀ s g)
          (tamagawaIdele F)) ∧
      DifferentiableOn ℂ (fun s : ℂ => zetaIntegral f (quasiTwist c₀ s))
        {s : ℂ | 1 < quasiAbscissa c₀ + s.re}) ∧
    (∃ M M' : ℂ → ℂ, MeromorphicNFOn M Set.univ ∧ MeromorphicNFOn M' Set.univ ∧
      (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re → M s = zetaIntegral f (quasiTwist c₀ s)) ∧
      (∀ s : ℂ, quasiTwist c₀ s ≠ (fun _ => 1) → quasiTwist c₀ s ≠ normQuasiChar 1 →
        AnalyticAt ℂ M s) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = (fun _ => 1) →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds (-(tamagawaClassVolume F : ℂ) * f.eval 0))) ∧
      (∀ s₀ : ℂ, quasiTwist c₀ s₀ = normQuasiChar 1 →
        Filter.Tendsto (fun s : ℂ => (s - s₀) * M s) (nhdsWithin s₀ {s₀}ᶜ)
          (nhds ((tamagawaClassVolume F : ℂ) * adelicFourier f 0))) ∧
      (∀ s : ℂ, 1 < quasiAbscissa (quasiDual c₀) + s.re →
        M' s = zetaIntegralFun (adelicFourier f) (quasiTwist (quasiDual c₀) s)) ∧
      (∀ s : ℂ, M s = M' (-s)) ∧
      ((¬ ∀ g : IdeleGroup F, ideleNorm g = 1 → c₀ g = 1) → Differentiable ℂ M)) ∧
    (∀ s : ℂ, 1 < quasiAbscissa c₀ + s.re →
      Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
        (tamagawaIdeleClass F) ∧
      thetaMellin f (quasiTwist c₀ s) = zetaIntegral f (quasiTwist c₀ s)) ∧
    (f.IsPolarFree →
      (∀ s : ℂ,
        Integrable (fun x : IdeleClassGroup F => adelicTheta f x.out * quasiTwist c₀ s x.out)
          (tamagawaIdeleClass F)) ∧
      Differentiable ℂ (fun s : ℂ => thetaMellin f (quasiTwist c₀ s))) :=
  TZMain.main F f c₀ hc
