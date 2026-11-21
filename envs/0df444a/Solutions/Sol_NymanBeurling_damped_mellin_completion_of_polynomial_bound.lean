-- Prove2me | solution 1 for NymanBeurling.damped_mellin_completion_of_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T05:44:10.853205+00:00
-- url     : https://prove2.me/submissions/2bb0637a-d232-4511-9c5d-859656809032

import Mathlib
import Definitions.Def_NymanBeurling_DampedMellinFrontiers
import Definitions.Def_NymanBeurling_DampedResidualLimits
import Theorems.Thm_GuthMaynard_mu_half_le_twentyseven_div_onesixtyfour
import Theorems.Thm_NymanBeurling_finite_remainder_mellin_plancherel

set_option autoImplicit false

open MeasureTheory Filter Topology Complex

namespace DampedSpectralAux

lemma continuous_zeta_comp (f : ℝ → ℂ) (hf : Continuous f) (h1 : ∀ t, f t ≠ 1) :
    Continuous (fun t => riemannZeta (f t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((differentiableAt_riemannZeta (h1 t)).continuousAt).comp hf.continuousAt

lemma line_ne_one (t c : ℝ) (hc : c ≠ 1/2) : (1/2:ℂ) - (t:ℂ)*I + (c:ℂ) ≠ 1 := by
  intro h
  apply hc
  have := congrArg Complex.re h
  simp at this
  linarith

lemma continuous_zeta_line (c : ℝ) (hc : c ≠ 1/2) :
    Continuous (fun t : ℝ => riemannZeta ((1/2:ℂ) - (t:ℂ)*I + (c:ℂ))) :=
  continuous_zeta_comp _ (by fun_prop) (fun t => line_ne_one t c hc)

lemma continuous_zeta_line0 :
    Continuous (fun t : ℝ => riemannZeta ((1/2:ℂ) - (t:ℂ)*I)) := by
  have := continuous_zeta_line 0 (by norm_num)
  simpa using this

lemma norm_line_ge (t : ℝ) : (1 + |t|)/4 ≤ ‖(1/2:ℂ) - (t:ℂ)*I‖ := by
  have h1 := Complex.abs_re_le_norm ((1/2:ℂ) - (t:ℂ)*I)
  have h2 := Complex.abs_im_le_norm ((1/2:ℂ) - (t:ℂ)*I)
  have hre : ((1/2:ℂ) - (t:ℂ)*I).re = 1/2 := by simp
  have him : ((1/2:ℂ) - (t:ℂ)*I).im = -t := by simp
  rw [hre] at h1
  rw [him, abs_neg] at h2
  have : |(1/2:ℝ)| = 1/2 := by norm_num
  linarith

lemma rpow_aux {x : ℝ} (hx : 0 < x) : (x^(1/4:ℝ))^2 / x^2 = x^(-(3/2:ℝ)) := by
  rw [← Real.rpow_natCast (x^(1/4:ℝ)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 2,
    ← Real.rpow_sub hx]
  norm_num

lemma sq_norm_div_le (w s : ℂ) (x K : ℝ) (hx : 0 < x) (_hK : 0 ≤ K)
    (hs : x/4 ≤ ‖s‖) (hw : ‖w‖ ≤ K * x^(1/4:ℝ)) :
    ‖w / s‖^2 ≤ 16 * K^2 * x^(-(3/2:ℝ)) := by
  have hx4 : 0 < x/4 := by positivity
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hx4 hs
  rw [norm_div, div_pow, ← rpow_aux hx]
  have hw2 : ‖w‖^2 ≤ (K * x^(1/4:ℝ))^2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hs2 : (x/4)^2 ≤ ‖s‖^2 := pow_le_pow_left₀ hx4.le hs 2
  rw [div_le_iff₀ (by positivity)]
  have hxne : x ≠ 0 := hx.ne'
  calc ‖w‖^2 ≤ (K * x^(1/4:ℝ))^2 := hw2
    _ = 16 * K^2 * ((x^(1/4:ℝ))^2 / x^2) * (x/4)^2 := by field_simp; ring
    _ ≤ 16 * K^2 * ((x^(1/4:ℝ))^2 / x^2) * ‖s‖^2 := by gcongr

lemma norm_zeta_line_eq (t : ℝ) :
    ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I)‖ = ‖riemannZeta ((1/2:ℂ) + ((|t|:ℝ):ℂ)*I)‖ := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    have : (1/2:ℂ) - (t:ℂ)*I = (starRingEnd ℂ) ((1/2:ℂ) + (t:ℂ)*I) := by
      apply Complex.ext <;> simp
    rw [this, riemannZeta_conj, Complex.norm_conj]
  · rw [abs_of_neg ht]
    congr 2
    push_cast
    ring

/-- Growth of `ζ` on the critical line, from the platform's proved bound `μ(1/2) ≤ 27/164`. -/
lemma zeta_line_growth : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I)‖ ≤ C * (1 + |t|)^(1/4:ℝ) := by
  have hmu := GuthMaynard.mu_half_le_twentyseven_div_onesixtyfour
  have hlt : LindelofHypothesis.mu (1/2) < ((1/4:ℝ):EReal) :=
    lt_of_le_of_lt hmu (EReal.coe_lt_coe_iff.2 (by norm_num))
  unfold LindelofHypothesis.mu at hlt
  obtain ⟨_, ⟨a, ha, rfl⟩, hab⟩ := sInf_lt_iff.1 hlt
  have hab' : a < 1/4 := EReal.coe_lt_coe_iff.1 hab
  simp only [Set.mem_ofPred_eq] at ha
  obtain ⟨c, hc⟩ := ha.bound
  rw [eventually_atTop] at hc
  obtain ⟨T₀, hT₀⟩ := hc
  have hcont : Continuous (fun u : ℝ => riemannZeta ((1/2:ℂ) + (u:ℂ)*I)) := by
    refine continuous_zeta_comp _ (by fun_prop) (fun u h => ?_)
    have := congrArg Complex.re h
    norm_num at this
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0:ℝ)) (b := max T₀ 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨|c| + |M|, by positivity, fun t => ?_⟩
  rw [norm_zeta_line_eq]
  have hu : 0 ≤ |t| := abs_nonneg t
  have h1 : 1 ≤ (1 + |t|)^(1/4:ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hcM : 0 ≤ |c| + |M| := by positivity
  rcases le_or_gt |t| (max T₀ 1) with h | h
  · have := hM |t| ⟨hu, h⟩
    calc _ ≤ M := this
      _ ≤ |M| := le_abs_self M
      _ ≤ (|c| + |M|) * 1 := by linarith [abs_nonneg c]
      _ ≤ _ := by gcongr
  · have hT : T₀ ≤ |t| := le_trans (le_max_left _ _) h.le
    have h1t : 1 ≤ |t| := le_trans (le_max_right _ _) h.le
    have := hT₀ |t| hT
    push_cast at this
    have hpow : ‖|t|^a‖ ≤ (1+|t|)^(1/4:ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu _)]
      calc |t|^a ≤ |t|^(1/4:ℝ) := Real.rpow_le_rpow_of_exponent_le h1t hab'.le
        _ ≤ (1+|t|)^(1/4:ℝ) := Real.rpow_le_rpow hu (by linarith) (by norm_num)
    calc _ ≤ c * ‖|t|^a‖ := this
      _ ≤ |c| * ‖|t|^a‖ := by gcongr; exact le_abs_self c
      _ ≤ |c| * (1+|t|)^(1/4:ℝ) := by gcongr
      _ ≤ _ := by gcongr; linarith [abs_nonneg M]

/-- The ordinates of zeros of `ζ` on the critical line form a countable set. -/
lemma countable_zeros_line : {t : ℝ | riemannZeta ((1/2:ℂ) - (t:ℂ)*I) = 0}.Countable := by
  have hZ : riemannZetaZeros.Countable :=
    IsLindelof.countable_of_isDiscrete
      (HereditarilyLindelofSpace.isHereditarilyLindelof_univ.isLindelof_subset
        (Set.subset_univ _)) isDiscrete_riemannZetaZeros
  have hinj : Function.Injective (fun t : ℝ => (1/2:ℂ) - (t:ℂ)*I) := by
    intro a b h
    have := congrArg Complex.im h
    simpa using this
  exact hZ.preimage hinj

lemma tendsto_inv_zeta_one_add :
    Tendsto (fun ε : ℝ => (riemannZeta (1 + (ε:ℂ)))⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hmap : Tendsto (fun ε : ℝ => (1:ℂ) + (ε:ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => (1:ℂ) + (ε:ℂ)) (𝓝 0) (𝓝 (1 + ((0:ℝ):ℂ))) :=
        (continuous_const.add Complex.continuous_ofReal).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
  have h1 := riemannZeta_residue_one.comp hmap
  have h2 : Tendsto (fun ε : ℝ => ((ε:ℂ) * riemannZeta (1 + (ε:ℂ)))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have := h1.inv₀ one_ne_zero
    rw [inv_one] at this
    refine this.congr (fun ε => ?_)
    simp only [Function.comp, add_sub_cancel_left]
  have h3 : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => (ε:ℂ)) (𝓝 0) (𝓝 ((0:ℝ):ℂ)) :=
      Complex.continuous_ofReal.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have h4 := h3.mul h2
  rw [zero_mul] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (ε:ℂ) ≠ 0 := by
    have : (0:ℝ) < ε := hε
    exact_mod_cast this.ne'
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hε0, one_mul]

end DampedSpectralAux

open MeasureTheory Filter Topology Complex
open scoped BigOperators

namespace DampedMellinAux
open NymanBeurling

lemma sum_Ioc_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, f d = ∑ n ∈ Finset.range N, f (n+1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_range_succ]

lemma abel_range (a b : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, a (n+1) * b (n+1) =
      (∑ n ∈ Finset.range N, a (n+1)) * b (N+1) +
      ∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n+1), a (m+1)) * (b (n+1) - b (n+1+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e1 : ∑ n ∈ Finset.range (N+1),
        (∑ m ∈ Finset.range (n+1), a (m+1)) * (b (n+1) - b (n+1+1)) =
        ∑ n ∈ Finset.range N, (∑ m ∈ Finset.range (n+1), a (m+1)) * (b (n+1) - b (n+1+1)) +
        (∑ m ∈ Finset.range (N+1), a (m+1)) * (b (N+1) - b (N+1+1)) := Finset.sum_range_succ _ _
    have e2 : ∑ n ∈ Finset.range (N+1), a (n+1) = ∑ n ∈ Finset.range N, a (n+1) + a (N+1) :=
      Finset.sum_range_succ _ _
    have e3 : ∑ n ∈ Finset.range (N+1), a (n+1) * b (n+1) =
        ∑ n ∈ Finset.range N, a (n+1) * b (n+1) + a (N+1) * b (N+1) := Finset.sum_range_succ _ _
    rw [e3, ih, e1, e2]
    ring

lemma D_range (N : ℕ) (z : ℂ) : moebiusDirichletPolynomial N z =
    ∑ n ∈ Finset.range N, (ArithmeticFunction.moebius (n+1) : ℂ) / (((n+1 : ℕ) : ℂ))^z := by
  unfold moebiusDirichletPolynomial
  rw [sum_Ioc_eq_sum_range]

lemma natCast_cpow_ne_zero (n : ℕ) (z : ℂ) : (((n+1 : ℕ) : ℂ))^z ≠ 0 := by
  have h : (((n+1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [Complex.cpow_def_of_ne_zero h]
  exact Complex.exp_ne_zero _

lemma differentiable_D (N : ℕ) : Differentiable ℂ (fun z => moebiusDirichletPolynomial N z) := by
  intro z
  simp_rw [D_range]
  apply DifferentiableAt.fun_sum
  intro n _
  have h : (((n+1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  exact (differentiableAt_const _).div ((differentiableAt_id).const_cpow (Or.inl h))
    (natCast_cpow_ne_zero n z)

/-- Real weights `r n = n^(-κ)`. -/
lemma weight_cast (κ : ℝ) (n : ℕ) :
    (((n+1 : ℕ) : ℂ))^((κ:ℝ):ℂ) * ((((n+1:ℕ):ℝ)^(-κ) : ℝ) : ℂ) = 1 := by
  have hpos : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := Nat.cast_nonneg _
  rw [Complex.ofReal_cpow hpos, Complex.ofReal_natCast, Complex.ofReal_neg, Complex.cpow_neg]
  exact mul_inv_cancel₀ (natCast_cpow_ne_zero n _)

lemma term_factor (κ : ℝ) (n : ℕ) (z : ℂ) :
    (ArithmeticFunction.moebius (n+1) : ℂ) / (((n+1 : ℕ) : ℂ))^z =
      ((ArithmeticFunction.moebius (n+1) : ℂ) / (((n+1 : ℕ) : ℂ))^(z - ((κ:ℝ):ℂ))) *
        ((((n+1:ℕ):ℝ)^(-κ) : ℝ) : ℂ) := by
  have h : (((n+1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hsplit : (((n+1 : ℕ) : ℂ))^z =
      (((n+1 : ℕ) : ℂ))^(z - ((κ:ℝ):ℂ)) * (((n+1 : ℕ) : ℂ))^((κ:ℝ):ℂ) := by
    rw [← Complex.cpow_add _ _ h, sub_add_cancel]
  have hw := weight_cast κ n
  have h1 := natCast_cpow_ne_zero n (z - ((κ:ℝ):ℂ))
  have h2 := natCast_cpow_ne_zero n ((κ:ℝ):ℂ)
  rw [hsplit]
  have hr : ((((n+1:ℕ):ℝ)^(-κ) : ℝ) : ℂ) = ((((n+1 : ℕ) : ℂ))^((κ:ℝ):ℂ))⁻¹ :=
    eq_inv_of_mul_eq_one_right hw
  rw [hr]
  field_simp

lemma rpow_neg_antitone {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    ((n+1+1:ℕ):ℝ)^(-κ) ≤ ((n+1:ℕ):ℝ)^(-κ) := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by push_cast; linarith) (by linarith)

lemma telescope_le {κ : ℝ} (_hκ : 0 < κ) (H : ℕ) :
    ∑ n ∈ Finset.range H, (((n+1:ℕ):ℝ)^(-κ) - ((n+1+1:ℕ):ℝ)^(-κ)) ≤ 1 := by
  have := Finset.sum_range_sub' (fun i : ℕ => ((i+1:ℕ):ℝ)^(-κ)) H
  rw [this]
  have h0 : ((0+1:ℕ):ℝ)^(-κ) = 1 := by simp
  have hH : 0 ≤ ((H+1:ℕ):ℝ)^(-κ) := by positivity
  linarith

lemma summable_telescope {κ : ℝ} (hκ : 0 < κ) :
    Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(-κ) - ((n+1+1:ℕ):ℝ)^(-κ)) :=
  summable_of_sum_range_le (fun n => sub_nonneg.2 (rpow_neg_antitone hκ n)) (telescope_le hκ)

lemma tendsto_weight {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)^(-κ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  exact (tendsto_rpow_neg_atTop hκ).comp h1

lemma tendsto_LSeries_moebius {z : ℂ} (hz : 1 < z.re) :
    Tendsto (fun N => moebiusDirichletPolynomial N z) atTop
      (𝓝 (LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) z)) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) z :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.2 hz
  have h := hs.hasSum.tendsto_sum_nat
  have h2 := (tendsto_add_atTop_iff_nat 1).2 h
  refine h2.congr (fun N => ?_)
  rw [Finset.sum_range_succ', LSeries.term_zero, add_zero, D_range]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n)]

lemma zeta_mul_LSeries_moebius {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) z * riemannZeta z = 1 := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hz
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hz] at h
  rw [mul_comm]
  exact h

/-- Under the polynomial bound, the Möbius partial sums converge to `1/ζ` on `Re > 1/2`. -/
lemma moebius_tendsto_inv_zeta (hpoly : MoebiusPolynomialBoundaryBound) (w₀ : ℂ)
    (hw : 1/2 < w₀.re) (hw1 : w₀ ≠ 1) :
    Tendsto (fun N => moebiusDirichletPolynomial N w₀) atTop (𝓝 (riemannZeta w₀)⁻¹) := by
  set θ : ℝ := w₀.re - 1/2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  set κ : ℝ := θ/4 with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨C, hC0, hC⟩ := hpoly (θ/4) (by positivity) 1 one_pos
  have hb : ∀ (N : ℕ) (z : ℂ), 1/2 + θ/4 < z.re →
      ‖moebiusDirichletPolynomial N z‖ ≤ C * (1 + |z.im|) := by
    intro N z hz
    have := hC N z.re z.im hz
    rw [Complex.re_add_im, Real.rpow_one] at this
    exact this
  set T : ℝ := |w₀.im| + 1 with hT
  have hT0 : 0 < T := by positivity
  set U : Set ℂ := {z : ℂ | 1/2 + θ/2 < z.re ∧ -T < z.im ∧ z.im < T} with hU
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  set B : ℝ := C * (1 + T) with hB
  have hA : ∀ (n : ℕ), ∀ z ∈ U, ‖moebiusDirichletPolynomial n (z - ((κ:ℝ):ℂ))‖ ≤ B := by
    intro n z hz
    obtain ⟨h1, h2, h3⟩ := hz
    have hre : (z - ((κ:ℝ):ℂ)).re = z.re - κ := by simp
    have him : (z - ((κ:ℝ):ℂ)).im = z.im := by simp
    have := hb n (z - ((κ:ℝ):ℂ)) (by rw [hre, hκ]; linarith)
    rw [him] at this
    have habs : |z.im| ≤ T := abs_le.2 ⟨by linarith, by linarith⟩
    calc _ ≤ C * (1 + |z.im|) := this
      _ ≤ B := by rw [hB]; gcongr
  set r : ℕ → ℝ := fun n => ((n:ℕ):ℝ)^(-κ) with hr
  set Fn : ℕ → ℂ → ℂ := fun n z =>
    moebiusDirichletPolynomial (n+1) (z - ((κ:ℝ):ℂ)) *
      (((r (n+1) : ℝ) : ℂ) - ((r (n+1+1) : ℝ) : ℂ)) with hFn
  set u : ℕ → ℝ := fun n => B * (r (n+1) - r (n+1+1)) with hu
  have hus : Summable u := (summable_telescope hκ0).mul_left B
  have hFle : ∀ n, ∀ z ∈ U, ‖Fn n z‖ ≤ u n := by
    intro n z hz
    simp only [hFn, hu, hr]
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.2 (rpow_neg_antitone hκ0 n))]
    exact mul_le_mul_of_nonneg_right (hA (n+1) z hz) (sub_nonneg.2 (rpow_neg_antitone hκ0 n))
  set L : ℂ → ℂ := fun z => ∑' n, Fn n z with hL
  have hLdiff : DifferentiableOn ℂ L U := by
    refine differentiableOn_tsum_of_summable_norm hus (fun n => ?_) hUopen hFle
    have hd := differentiable_D (n+1)
    exact ((hd.comp (differentiable_id.sub (differentiable_const _))).mul
      (differentiable_const _)).differentiableOn
  have hconv : ∀ z ∈ U, Tendsto (fun N => moebiusDirichletPolynomial N z) atTop (𝓝 (L z)) := by
    intro z hz
    have hsum : Summable (fun n => Fn n z) := Summable.of_norm_bounded hus (fun n => hFle n z hz)
    have h2 := hsum.hasSum.tendsto_sum_nat
    have h1 : Tendsto (fun N : ℕ => moebiusDirichletPolynomial N (z - ((κ:ℝ):ℂ)) *
        ((r (N+1) : ℝ) : ℂ)) atTop (𝓝 0) := by
      refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
      refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
        (by simpa using (tendsto_weight hκ0).const_mul B)
      have hr0 : 0 ≤ r (N+1) := by simp only [hr]; positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      calc _ ≤ B * r (N+1) := mul_le_mul_of_nonneg_right (hA N z hz) hr0
        _ = _ := by simp [hr]
    have h3 := h1.add h2
    rw [zero_add] at h3
    refine h3.congr (fun N => ?_)
    rw [D_range N z]
    have := abel_range (fun d => (ArithmeticFunction.moebius d : ℂ) /
        ((d : ℂ))^(z - ((κ:ℝ):ℂ))) (fun d => ((r d : ℝ) : ℂ)) N
    simp only at this
    rw [show (∑ n ∈ Finset.range N, (ArithmeticFunction.moebius (n+1) : ℂ) /
        (((n+1 : ℕ) : ℂ))^z) = ∑ n ∈ Finset.range N,
          (ArithmeticFunction.moebius (n+1) : ℂ) / (((n+1 : ℕ) : ℂ))^(z - ((κ:ℝ):ℂ)) *
            ((r (n+1) : ℝ) : ℂ) from Finset.sum_congr rfl (fun n _ => term_factor κ n z)]
    rw [this, ← D_range]
    congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [hFn]
    rw [← D_range]
  -- `L * ζ = 1` on the part of `U` to the right of `1`.
  have hright : ∀ z ∈ U, 1 < z.re → L z * riemannZeta z = 1 := by
    intro z hz hz1
    have := tendsto_nhds_unique (hconv z hz) (tendsto_LSeries_moebius hz1)
    rw [this]
    exact zeta_mul_LSeries_moebius hz1
  -- identity theorem on convex open pieces avoiding the pole
  have hident : ∀ V : Set ℂ, IsOpen V → Convex ℝ V → V ⊆ U → (1:ℂ) ∉ V → ∀ z₀ ∈ V,
      (∀ᶠ z in 𝓝 z₀, L z * riemannZeta z = 1) → ∀ z ∈ V, L z * riemannZeta z = 1 := by
    intro V hVo hVc hVU h1V z₀ hz₀ hev z hz
    have hf : AnalyticOnNhd ℂ (fun z => L z * riemannZeta z) V := by
      apply DifferentiableOn.analyticOnNhd _ hVo
      refine (hLdiff.mono hVU).mul (fun y hy => ?_)
      have hy1 : y ≠ 1 := fun h => h1V (h ▸ hy)
      exact (differentiableAt_riemannZeta hy1).differentiableWithinAt
    have := hf.eqOn_of_preconnected_of_eventuallyEq (analyticOnNhd_const (v := (1:ℂ)))
      hVc.isPreconnected hz₀ hev
    exact this hz
  have hevright : ∀ z₀ ∈ U, 1 < z₀.re → ∀ᶠ z in 𝓝 z₀, L z * riemannZeta z = 1 := by
    intro z₀ hz₀ h1
    have hopen : IsOpen (U ∩ {z : ℂ | 1 < z.re}) :=
      hUopen.inter (isOpen_lt continuous_const Complex.continuous_re)
    filter_upwards [hopen.mem_nhds ⟨hz₀, h1⟩] with z hz
    exact hright z hz.1 hz.2
  have hθ1 : 1/2 + θ/2 < w₀.re := by rw [hθ]; linarith
  have hTim : -T < w₀.im ∧ w₀.im < T := by
    constructor <;> [linarith [neg_abs_le w₀.im]; linarith [le_abs_self w₀.im]]
  have hw₀U : w₀ ∈ U := ⟨hθ1, hTim⟩
  -- upper and lower pieces
  set Vp : Set ℂ := {z : ℂ | 1/2 + θ/2 < z.re ∧ 0 < z.im ∧ z.im < T} with hVp
  set Vm : Set ℂ := {z : ℂ | 1/2 + θ/2 < z.re ∧ -T < z.im ∧ z.im < 0} with hVm
  have hVpo : IsOpen Vp :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hVmo : IsOpen Vm :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hVpc : Convex ℝ Vp :=
    (convex_halfSpace_re_gt _).inter ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  have hVmc : Convex ℝ Vm :=
    (convex_halfSpace_re_gt _).inter ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  have hVpU : Vp ⊆ U := fun z ⟨h1, h2, h3⟩ => ⟨h1, by linarith, h3⟩
  have hVmU : Vm ⊆ U := fun z ⟨h1, h2, h3⟩ => ⟨h1, h2, by linarith⟩
  have h1Vp : (1:ℂ) ∉ Vp := fun ⟨_, h, _⟩ => by simp at h
  have h1Vm : (1:ℂ) ∉ Vm := fun ⟨_, _, h⟩ => by simp at h
  have hzp : ((w₀.re + 1:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I ∈ Vp := by
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
  have hzm : ((w₀.re + 1:ℝ):ℂ) - ((T/2:ℝ):ℂ) * I ∈ Vm := by
    refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
  have hP := hident Vp hVpo hVpc hVpU h1Vp _ hzp
    (hevright _ (hVpU hzp) (by simp; linarith))
  have hM := hident Vm hVmo hVmc hVmU h1Vm _ hzm
    (hevright _ (hVmU hzm) (by simp; linarith))
  -- conclude by cases on the imaginary part of `w₀`
  have hfin : L w₀ * riemannZeta w₀ = 1 := by
    rcases lt_trichotomy w₀.im 0 with him | him | him
    · exact hM w₀ ⟨hθ1, hTim.1, him⟩
    · rcases lt_trichotomy w₀.re 1 with hre | hre | hre
      · set V0 : Set ℂ := {z : ℂ | 1/2 + θ/2 < z.re ∧ z.re < 1 ∧ -T < z.im ∧ z.im < T}
          with hV0
        have hV0o : IsOpen V0 :=
          (isOpen_lt continuous_const Complex.continuous_re).inter
            ((isOpen_lt Complex.continuous_re continuous_const).inter
              ((isOpen_lt continuous_const Complex.continuous_im).inter
                (isOpen_lt Complex.continuous_im continuous_const)))
        have hV0c : Convex ℝ V0 :=
          (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter
            ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)))
        have hV0U : V0 ⊆ U := fun z ⟨h1, _, h3, h4⟩ => ⟨h1, h3, h4⟩
        have h1V0 : (1:ℂ) ∉ V0 := fun ⟨_, h, _⟩ => by simp at h
        have hz1 : ((w₀.re:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I ∈ V0 := by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
        have hz1p : ((w₀.re:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I ∈ Vp := by
          refine ⟨?_, ?_, ?_⟩ <;> simp <;> linarith
        have hev : ∀ᶠ z in 𝓝 (((w₀.re:ℝ):ℂ) + ((T/2:ℝ):ℂ) * I), L z * riemannZeta z = 1 := by
          filter_upwards [hVpo.mem_nhds hz1p] with z hz
          exact hP z hz
        exact hident V0 hV0o hV0c hV0U h1V0 _ hz1 hev w₀ ⟨hθ1, hre, hTim.1, hTim.2⟩
      · exact absurd (Complex.ext (by simpa using hre) (by simpa using him)) hw1
      · exact hright w₀ hw₀U hre
    · exact hP w₀ ⟨hθ1, him, hTim.2⟩
  rw [← eq_inv_of_mul_eq_one_left hfin]
  exact hconv w₀ hw₀U

end DampedMellinAux

namespace DampedMellinAux
open NymanBeurling

noncomputable def sl (t : ℝ) : ℂ := (1/2:ℂ) - (t:ℂ)*I

noncomputable def Xf (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ k ∈ S, c k * (((k+2:ℕ):ℂ)⁻¹ - ((k+2:ℕ):ℂ)^(-sl t))

noncomputable def gf (S : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ S, c k * ((((n+1)%(k+2):ℕ):ℂ)/((k+2:ℕ):ℂ))

lemma frmp (S : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun t : ℝ => ‖(1 - Xf S c t * riemannZeta (sl t)) / sl t‖^2) ∧
    (∫ t : ℝ, ‖(1 - Xf S c t * riemannZeta (sl t)) / sl t‖^2) =
      2*Real.pi * ∑' n : ℕ, ‖1 - gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ)) :=
  NymanBeurling.finite_remainder_mellin_plancherel S c

lemma summable_w : Summable (fun n : ℕ => 1 / ((n+1:ℝ)*(n+2:ℝ))) := by
  refine summable_of_sum_range_le (c := 1) (fun n => by positivity) (fun H => ?_)
  have key : ∀ n : ℕ, 1 / ((n+1:ℝ)*(n+2:ℝ)) =
      (fun i : ℕ => 1/((i:ℝ)+1)) n - (fun i : ℕ => 1/((i:ℝ)+1)) (n+1) := by
    intro n
    simp only
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_range_sub']
  simp only [Nat.cast_zero, zero_add, div_one]
  have : 0 ≤ 1/((H:ℝ)+1) := by positivity
  linarith

lemma summable_bdd_w (f : ℕ → ℝ) (K : ℝ) (hf : ∀ n, |f n| ≤ K) :
    Summable (fun n : ℕ => (f n)^2 / ((n+1:ℝ)*(n+2:ℝ))) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_w.mul_left (K^2))
  have h2 : f n ^ 2 ≤ K^2 := by
    obtain ⟨h1, h2⟩ := abs_le.1 (hf n)
    exact sq_le_sq' h1 h2
  calc f n ^ 2 / ((n+1:ℝ)*(n+2:ℝ)) = f n ^ 2 * (1 / ((n+1:ℝ)*(n+2:ℝ))) := by ring
    _ ≤ K^2 * (1 / ((n+1:ℝ)*(n+2:ℝ))) := by gcongr

lemma gf_bound (S : Finset ℕ) (c : ℕ → ℂ) (n : ℕ) : ‖gf S c n‖ ≤ ∑ k ∈ S, ‖c k‖ := by
  unfold gf
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_mul]
  have h : ‖((((n+1)%(k+2):ℕ):ℂ)/((k+2:ℕ):ℂ))‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast,
      div_le_one (by positivity)]
    exact_mod_cast (Nat.mod_lt _ (by omega)).le
  calc ‖c k‖ * _ ≤ ‖c k‖ * 1 := by gcongr
    _ = ‖c k‖ := mul_one _

/-- Polarized finite Mellin--Plancherel identity (no constant term). -/
lemma iso (S : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun t : ℝ => ‖Xf S c t * riemannZeta (sl t) / sl t‖^2) ∧
    Summable (fun n : ℕ => ‖gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ))) ∧
    (∫ t : ℝ, ‖Xf S c t * riemannZeta (sl t) / sl t‖^2) =
      2*Real.pi * ∑' n : ℕ, ‖gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ)) := by
  obtain ⟨hi1, he1⟩ := frmp S c
  obtain ⟨hi2, he2⟩ := frmp S (fun k => -c k)
  obtain ⟨hi0, he0⟩ := frmp ∅ c
  have hXn : ∀ t, Xf S (fun k => -c k) t = - Xf S c t := by
    intro t; simp [Xf, neg_mul, Finset.sum_neg_distrib]
  have hgn : ∀ n, gf S (fun k => -c k) n = - gf S c n := by
    intro n; simp [gf, neg_mul, Finset.sum_neg_distrib]
  have hX0 : ∀ t, Xf ∅ c t = 0 := by intro t; simp [Xf]
  have hg0 : ∀ n, gf ∅ c n = 0 := by intro n; simp [gf]
  simp only [hXn, hgn] at hi2 he2
  simp only [hX0, hg0, zero_mul, sub_zero, norm_one, one_pow] at hi0 he0
  have hpt : ∀ t, ‖Xf S c t * riemannZeta (sl t) / sl t‖^2 =
      (‖(1 - Xf S c t * riemannZeta (sl t)) / sl t‖^2 +
        ‖(1 - -Xf S c t * riemannZeta (sl t)) / sl t‖^2)/2 - ‖1 / sl t‖^2 := by
    intro t
    have e1 : (1 - Xf S c t * riemannZeta (sl t)) / sl t =
        1 / sl t - Xf S c t * riemannZeta (sl t) / sl t := by ring
    have e2 : (1 - -Xf S c t * riemannZeta (sl t)) / sl t =
        1 / sl t + Xf S c t * riemannZeta (sl t) / sl t := by ring
    rw [e1, e2]
    have := parallelogram_law_with_norm ℝ (1 / sl t) (Xf S c t * riemannZeta (sl t) / sl t)
    linear_combination (-1/2:ℝ) * this
  have hfun : (fun t : ℝ => ‖Xf S c t * riemannZeta (sl t) / sl t‖^2) =
      fun t => (‖(1 - Xf S c t * riemannZeta (sl t)) / sl t‖^2 +
        ‖(1 - -Xf S c t * riemannZeta (sl t)) / sl t‖^2)/2 - ‖1 / sl t‖^2 := funext hpt
  have hK : ∀ n, |‖gf S c n‖| ≤ ∑ k ∈ S, ‖c k‖ := fun n => by
    rw [abs_of_nonneg (norm_nonneg _)]; exact gf_bound S c n
  have hK1 : ∀ n, |‖1 - gf S c n‖| ≤ 1 + ∑ k ∈ S, ‖c k‖ := fun n => by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [gf_bound S c n])
  have hK2 : ∀ n, |‖1 - -gf S c n‖| ≤ 1 + ∑ k ∈ S, ‖c k‖ := fun n => by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by rw [norm_one, norm_neg]; linarith [gf_bound S c n])
  have hs : Summable (fun n : ℕ => ‖gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ))) :=
    summable_bdd_w _ _ hK
  have hs1 := summable_bdd_w _ _ hK1
  have hs2 := summable_bdd_w _ _ hK2
  have hdpt : ∀ n : ℕ, ‖gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ)) =
      (‖1 - gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ)) + ‖1 - -gf S c n‖^2 / ((n+1:ℝ)*(n+2:ℝ)))/2
        - 1 / ((n+1:ℝ)*(n+2:ℝ)) := by
    intro n
    have := parallelogram_law_with_norm ℝ (1:ℂ) (gf S c n)
    rw [sub_neg_eq_add]
    rw [norm_one] at this
    field_simp
    linear_combination (-1:ℝ) * this
  refine ⟨?_, hs, ?_⟩
  · rw [hfun]
    exact ((hi1.add hi2).div_const 2).sub hi0
  · have hA : Integrable (fun t : ℝ => (‖(1 - Xf S c t * riemannZeta (sl t)) / sl t‖^2 +
        ‖(1 - -Xf S c t * riemannZeta (sl t)) / sl t‖^2)/2) := (hi1.add hi2).div_const 2
    rw [hfun, integral_sub hA hi0, integral_div,
      integral_add hi1 hi2, he1, he2, he0]
    rw [tsum_congr hdpt, ((hs1.add hs2).div_const 2).tsum_sub summable_w, tsum_div_const,
      hs1.tsum_add hs2]
    ring

lemma sum_trunc (y : ℕ → ℂ) (c : ℕ → ℂ) (N L : ℕ) (h : N ≤ L) :
    ∑ k ∈ Finset.range L, (if k < N then c k else 0) * y k = ∑ k ∈ Finset.range N, c k * y k := by
  rw [← Finset.sum_range_add_sum_Ico _ h]
  have h0 : ∑ k ∈ Finset.Ico N L, (if k < N then c k else 0) * y k = 0 := by
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    rw [if_neg (by omega), zero_mul]
  rw [h0, add_zero]
  exact Finset.sum_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.1 hk)])

lemma Xf_trunc_sub (c : ℕ → ℂ) (N M : ℕ) (t : ℝ) :
    Xf (Finset.range (N+M)) (fun k => (if k < N then c k else 0) - (if k < M then c k else 0)) t =
      Xf (Finset.range N) c t - Xf (Finset.range M) c t := by
  unfold Xf
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [sum_trunc _ _ N (N+M) (by omega), sum_trunc _ _ M (N+M) (by omega)]

lemma gf_trunc_sub (c : ℕ → ℂ) (N M : ℕ) (n : ℕ) :
    gf (Finset.range (N+M)) (fun k => (if k < N then c k else 0) - (if k < M then c k else 0)) n =
      gf (Finset.range N) c n - gf (Finset.range M) c n := by
  unfold gf
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [sum_trunc _ _ N (N+M) (by omega), sum_trunc _ _ M (N+M) (by omega)]

noncomputable def cr (ε : ℝ) (k : ℕ) : ℝ :=
  (ArithmeticFunction.moebius (k+2) : ℝ) / ((k:ℝ)+2)^ε

noncomputable def cc (ε : ℝ) (k : ℕ) : ℂ := -((cr ε k : ℝ) : ℂ)

lemma cc_eq (ε : ℝ) (k : ℕ) :
    cc ε k = -((ArithmeticFunction.moebius (k+2) : ℂ) / ((k+2:ℕ):ℂ)^(ε:ℂ)) := by
  have hpos : (0:ℝ) ≤ (k:ℝ)+2 := by positivity
  have hcast : ((((k:ℝ)+2)^ε : ℝ) : ℂ) = ((k+2:ℕ):ℂ)^(ε:ℂ) := by
    rw [Complex.ofReal_cpow hpos]
    congr 1
    push_cast
    ring
  simp only [cc, cr]
  rw [Complex.ofReal_div, Complex.ofReal_intCast, hcast]

lemma D_succ_shift (N : ℕ) (z : ℂ) : moebiusDirichletPolynomial (N+1) z =
    1 + ∑ k ∈ Finset.range N, (ArithmeticFunction.moebius (k+2) : ℂ) / (((k+2:ℕ):ℂ))^z := by
  rw [D_range, Finset.sum_range_succ', add_comm]
  congr 1
  simp

lemma term_link (ε : ℝ) (k : ℕ) (s : ℂ) :
    cc ε k * (((k+2:ℕ):ℂ)⁻¹ - ((k+2:ℕ):ℂ)^(-s)) =
      (ArithmeticFunction.moebius (k+2) : ℂ) / ((k+2:ℕ):ℂ)^(s + (ε:ℂ)) -
        (ArithmeticFunction.moebius (k+2) : ℂ) / ((k+2:ℕ):ℂ)^(1 + (ε:ℂ)) := by
  have hX : ((k+2:ℕ):ℂ) ≠ 0 := by exact_mod_cast (show k+2 ≠ 0 by omega)
  have hne : ∀ z : ℂ, ((k+2:ℕ):ℂ)^z ≠ 0 := fun z => by
    rw [Complex.cpow_def_of_ne_zero hX]; exact Complex.exp_ne_zero _
  rw [cc_eq, Complex.cpow_add _ _ hX, Complex.cpow_add _ _ hX, Complex.cpow_one,
    Complex.cpow_neg]
  have h1 := hne s
  have h2 := hne (ε:ℂ)
  field_simp
  ring

lemma Xf_link (ε : ℝ) (N : ℕ) (t : ℝ) :
    Xf (Finset.range N) (cc ε) t =
      moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ)) -
        moebiusDirichletPolynomial (N+1) (1 + (ε:ℂ)) := by
  rw [D_succ_shift, D_succ_shift]
  unfold Xf
  simp_rw [term_link]
  rw [Finset.sum_sub_distrib]
  ring

lemma gf_link (ε : ℝ) (N n : ℕ) :
    1 - gf (Finset.range N) (cc ε) n = ((dampedResidualFinite N ε (n+1) : ℝ) : ℂ) := by
  unfold gf dampedResidualFinite
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (ArithmeticFunction.moebius (k+2) : ℝ) /
    ((k:ℝ)+2)^ε * (((n+1) % (k+2) : ℕ) : ℝ) / ((k:ℝ)+2))]
  simp only [cc, cr]
  push_cast
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

lemma residual_tendsto_profile (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    Tendsto (fun M => dampedResidualFinite M ε m) atTop (𝓝 (dampedResidualProfile ε m)) := by
  set f : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / (d:ℝ)^(1+ε) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded
      (Real.summable_one_div_nat_rpow.2 (by linarith : (1:ℝ) < 1+ε)) (fun d => ?_)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (d:ℝ)^(1+ε))]
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast this
    gcongr
  have hE : Tendsto (fun M => ∑ k ∈ Finset.range M, f (k+2)) atTop (𝓝 (∑' d, f d - 1)) := by
    have h := ((hasSum_nat_add_iff' 2).2 hfs.hasSum).tendsto_sum_nat
    have hr : ∑ i ∈ Finset.range 2, f i = 1 := by
      simp [hf, Finset.sum_range_succ]
    rw [hr] at h
    exact h
  set g : ℕ → ℝ := fun d => (ArithmeticFunction.moebius d : ℝ) / (d:ℝ)^ε * ((m/d:ℕ):ℝ) with hg
  set Q : ℝ := ∑ k ∈ Finset.range m, g (k+2) with hQ
  have hQev : ∀ M, m ≤ M → ∑ k ∈ Finset.range M, g (k+2) = Q := by
    intro M hM
    rw [← Finset.sum_range_add_sum_Ico _ hM]
    have : ∑ k ∈ Finset.Ico m M, g (k+2) = 0 := by
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rw [Finset.mem_Ico] at hk
      simp only [hg, Nat.div_eq_of_lt (show m < k+2 by omega), Nat.cast_zero, mul_zero]
    rw [this, add_zero]
  have hR : ∀ M, dampedResidualFinite M ε m =
      1 + (m:ℝ) * ∑ k ∈ Finset.range M, f (k+2) - ∑ k ∈ Finset.range M, g (k+2) := by
    intro M
    unfold dampedResidualFinite
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (ArithmeticFunction.moebius (k+2) : ℝ) /
      ((k:ℝ)+2)^ε * ((m % (k+2) : ℕ) : ℝ) / ((k:ℝ)+2)), Finset.mul_sum, add_sub_assoc,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hx : (0:ℝ) < (k:ℝ)+2 := by positivity
    have hmod : ((m % (k+2) : ℕ) : ℝ) = (m:ℝ) - ((k:ℝ)+2) * ((m/(k+2):ℕ):ℝ) := by
      have := Nat.mod_add_div m (k+2)
      have h' : ((m % (k+2) : ℕ) : ℝ) + ((k+2:ℕ):ℝ) * ((m/(k+2):ℕ):ℝ) = (m:ℝ) := by
        exact_mod_cast this
      push_cast at h'
      linarith
    have hpow : ((k:ℝ)+2)^(1+ε) = ((k:ℝ)+2) * ((k:ℝ)+2)^ε := by
      rw [Real.rpow_add hx, Real.rpow_one]
    simp only [hf, hg]
    push_cast
    rw [hmod, hpow]
    have hne : ((k:ℝ)+2)^ε ≠ 0 := (Real.rpow_pos_of_pos hx ε).ne'
    field_simp
  have hlim : Tendsto (fun M => dampedResidualFinite M ε m) atTop
      (𝓝 (1 + (m:ℝ) * (∑' d, f d - 1) - Q)) := by
    have h1 := ((hE.const_mul (m:ℝ)).const_add 1).sub (tendsto_const_nhds (x := Q))
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop m] with M hM
    rw [hR M, hQev M hM]
  have hP : dampedResidualProfile ε m = 1 + (m:ℝ) * (∑' d, f d - 1) - Q := by
    unfold dampedResidualProfile
    have hIoc : ∑ d ∈ Finset.Ioc 0 m, (ArithmeticFunction.moebius d : ℝ) / (d:ℝ)^ε *
        ((m/d:ℕ):ℝ) = (m:ℝ) + Q := by
      have h1 : ∑ d ∈ Finset.Ioc 0 (m+1), g d = ∑ d ∈ Finset.Ioc 0 m, g d + g (m+1) :=
        Finset.sum_Ioc_succ_top (Nat.zero_le m) _
      have h2 : g (m+1) = 0 := by
        simp only [hg, Nat.div_eq_of_lt (show m < m+1 by omega), Nat.cast_zero, mul_zero]
      have h3 : ∑ d ∈ Finset.Ioc 0 (m+1), g d = g 1 + Q := by
        rw [sum_Ioc_eq_sum_range, Finset.sum_range_succ', add_comm, hQ]
      have h4 : g 1 = m := by simp [hg]
      rw [h2, add_zero, h3, h4] at h1
      rw [← h1]
    rw [hIoc]
    ring
  rw [hP]
  exact hlim

lemma sq_norm_div_le_gen (w s : ℂ) (x K a : ℝ) (hx : 1 ≤ x) (hK : 0 ≤ K)
    (hs : x/4 ≤ ‖s‖) (hw : ‖w‖ ≤ K * x^a) :
    ‖w / s‖^2 ≤ 16 * K^2 * x^(2*a - 2) := by
  have hx0 : 0 < x := by linarith
  have hx4 : 0 < x/4 := by positivity
  have hs0 : 0 < ‖s‖ := lt_of_lt_of_le hx4 hs
  have hrp : (x^a)^2 / x^2 = x^(2*a - 2) := by
    rw [← Real.rpow_natCast (x^a) 2, ← Real.rpow_mul hx0.le, ← Real.rpow_natCast x 2,
      ← Real.rpow_sub hx0]
    congr 1
    push_cast
    ring
  rw [norm_div, div_pow, ← hrp]
  have hw2 : ‖w‖^2 ≤ (K * x^a)^2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  have hs2 : (x/4)^2 ≤ ‖s‖^2 := pow_le_pow_left₀ hx4.le hs 2
  rw [div_le_iff₀ (by positivity)]
  have hxne : x ≠ 0 := hx0.ne'
  calc ‖w‖^2 ≤ (K * x^a)^2 := hw2
    _ = 16 * K^2 * ((x^a)^2 / x^2) * (x/4)^2 := by field_simp; ring
    _ ≤ 16 * K^2 * ((x^a)^2 / x^2) * ‖s‖^2 := by gcongr

lemma sq_norm_sub_le (a b : ℂ) : ‖a - b‖^2 ≤ 2*‖a‖^2 + 2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

lemma real_sq_sub_le (a b : ℝ) : (a - b)^2 ≤ 2*a^2 + 2*b^2 := by nlinarith [sq_nonneg (a+b)]

lemma abs_sq_sub_sq_le (a b l : ℝ) (hl : 0 < l) :
    |a^2 - b^2| ≤ (l*(a-b)^2 + (a+b)^2/l)/2 := by
  have e1 : (a-b)^2 = |a-b|^2 := (sq_abs _).symm
  have e2 : (a+b)^2 = |a+b|^2 := (sq_abs _).symm
  have hid : l*|a-b|^2 + |a+b|^2/l - 2*(|a-b| * |a+b|) = (l*|a-b| - |a+b|)^2 / l := by
    field_simp
    ring
  have hnn : 0 ≤ (l*|a-b| - |a+b|)^2 / l := div_nonneg (sq_nonneg _) hl.le
  have : |a^2 - b^2| = |a-b| * |a+b| := by
    rw [← abs_mul]; congr 1; ring
  rw [this, e1, e2]
  linarith

end DampedMellinAux

namespace DampedMellinAux
open NymanBeurling DampedSpectralAux

/-- The finite spectral residuals attached to the truncated damped Möbius coefficients. -/
noncomputable def FN (ε : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (1 - Xf (Finset.range N) (cc ε) t * riemannZeta (sl t)) / sl t

lemma sl_ne_zero (t : ℝ) : sl t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [sl] at this

lemma FN_tendsto (hpoly : MoebiusPolynomialBoundaryBound) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1/2) (t : ℝ) :
    Tendsto (fun N => FN ε N t) atTop (𝓝 (dampedSpectralResidual ε t)) := by
  have hw : Tendsto (fun N => moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ))) atTop
      (𝓝 (riemannZeta (sl t + ε))⁻¹) := by
    have := moebius_tendsto_inv_zeta hpoly (sl t + ε) (by simp [sl]; linarith) (by
      intro h
      have := congrArg Complex.re h
      simp [sl] at this
      linarith)
    exact (tendsto_add_atTop_iff_nat 1).2 this
  have h1 : Tendsto (fun N => moebiusDirichletPolynomial (N+1) (1 + (ε:ℂ))) atTop
      (𝓝 (riemannZeta (1 + ε))⁻¹) := by
    have := moebius_tendsto_inv_zeta hpoly (1 + ε) (by simp; linarith) (by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith)
    exact (tendsto_add_atTop_iff_nat 1).2 this
  have h := ((tendsto_const_nhds (x := (1:ℂ))).sub
    ((hw.sub h1).mul (tendsto_const_nhds (x := riemannZeta (sl t))))).div_const (sl t)
  simp only [FN, Xf_link]
  convert h using 2
  simp only [dampedSpectralResidual, sl]
  ring

lemma FN_continuous (ε : ℝ) (N : ℕ) : Continuous (fun t => FN ε N t) := by
  have hs : Continuous sl := by unfold sl; fun_prop
  have hc1 : Continuous (fun t => moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ))) :=
    (differentiable_D (N+1)).continuous.comp (hs.add continuous_const)
  have hz : Continuous (fun t => riemannZeta (sl t)) := continuous_zeta_line0
  simp only [FN, Xf_link]
  exact (continuous_const.sub ((hc1.sub continuous_const).mul hz)).div hs sl_ne_zero

lemma F_meas (ε : ℝ) (hε2 : ε < 1/2) (hε : 0 < ε) :
    Measurable (fun t => dampedSpectralResidual ε t) := by
  have c1 := continuous_zeta_line0
  have c2 := continuous_zeta_line ε (by linarith)
  have hs : Measurable (fun t : ℝ => (1/2:ℂ) - (t:ℂ)*I) := by fun_prop
  exact (measurable_const.sub (c1.measurable.mul (c2.measurable.inv.sub measurable_const))).div hs

lemma FN_bound (ε : ℝ) (hε : 0 < ε) (C₁ Cz : ℝ) (hC₁0 : 0 ≤ C₁) (hCz0 : 0 ≤ Cz)
    (hC₁ : ∀ (N : ℕ) (σ t : ℝ), 1/2 + ε/4 < σ →
      ‖moebiusDirichletPolynomial N ((σ:ℂ) + (t:ℂ) * I)‖ ≤ C₁ * (1 + |t|)^(1/8:ℝ))
    (hCz : ∀ t : ℝ, ‖riemannZeta ((1/2:ℂ) - (t:ℂ)*I)‖ ≤ Cz * (1 + |t|)^(1/4:ℝ)) (N : ℕ) (t : ℝ) :
    ‖FN ε N t‖^2 ≤ 16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ)) := by
  have hx1 : (1:ℝ) ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
  have hx0 : (0:ℝ) < 1 + |t| := by linarith
  have hDw : ‖moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ))‖ ≤ C₁ * (1+|t|)^(1/8:ℝ) := by
    have e : sl t + (ε:ℂ) = ((1/2+ε:ℝ):ℂ) + ((-t:ℝ):ℂ) * I := by
      apply Complex.ext <;> simp [sl]
    rw [e]
    have := hC₁ (N+1) (1/2+ε) (-t) (by linarith)
    rwa [abs_neg] at this
  have hD1 : ‖moebiusDirichletPolynomial (N+1) (1 + (ε:ℂ))‖ ≤ C₁ := by
    have e : (1 + (ε:ℂ)) = ((1+ε:ℝ):ℂ) + ((0:ℝ):ℂ) * I := by
      apply Complex.ext <;> simp
    rw [e]
    have := hC₁ (N+1) (1+ε) 0 (by linarith)
    simpa using this
  have hq8 : 1 ≤ (1+|t|)^(1/8:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hq38 : 1 ≤ (1+|t|)^(3/8:ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hX : ‖moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ)) -
      moebiusDirichletPolynomial (N+1) (1 + (ε:ℂ))‖ ≤ 2*C₁*(1+|t|)^(1/8:ℝ) := by
    refine (norm_sub_le _ _).trans ?_
    nlinarith
  have hZ : ‖riemannZeta (sl t)‖ ≤ Cz * (1+|t|)^(1/4:ℝ) := hCz t
  have hprod : (1+|t|)^(1/8:ℝ) * (1+|t|)^(1/4:ℝ) = (1+|t|)^(3/8:ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hnum : ‖1 - (moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ)) -
      moebiusDirichletPolynomial (N+1) (1 + (ε:ℂ))) * riemannZeta (sl t)‖ ≤
        (1 + 2*C₁*Cz) * (1+|t|)^(3/8:ℝ) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_mul]
    have hm : ‖moebiusDirichletPolynomial (N+1) (sl t + (ε:ℂ)) -
        moebiusDirichletPolynomial (N+1) (1 + (ε:ℂ))‖ * ‖riemannZeta (sl t)‖ ≤
          (2*C₁*(1+|t|)^(1/8:ℝ)) * (Cz * (1+|t|)^(1/4:ℝ)) :=
      mul_le_mul hX hZ (norm_nonneg _) (by positivity)
    have : (2*C₁*(1+|t|)^(1/8:ℝ)) * (Cz * (1+|t|)^(1/4:ℝ)) = 2*C₁*Cz*(1+|t|)^(3/8:ℝ) := by
      rw [← hprod]; ring
    nlinarith
  have := sq_norm_div_le_gen _ (sl t) (1+|t|) (1 + 2*C₁*Cz) (3/8) hx1 (by positivity)
    (by exact norm_line_ge t) hnum
  rw [show (2*(3/8:ℝ) - 2) = -(5/4) by norm_num] at this
  simp only [FN, Xf_link]
  exact this

lemma main_package (hpoly : MoebiusPolynomialBoundaryBound) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1/2) :
    (∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
        (∑ n ∈ Finset.range H,
          (dampedResidualFinite N ε (n+1) - dampedResidualProfile ε (n+1))^2 /
              ((n+1 : ℝ)*(n+2 : ℝ))) < δ) ∧
    (Summable (fun n : ℕ => (dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))) ∧
      Integrable (fun t : ℝ => ‖dampedSpectralResidual ε t‖^2) ∧
      (∫ t : ℝ, ‖dampedSpectralResidual ε t‖^2) =
        2*Real.pi * ∑' n : ℕ, (dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := hpoly (ε/4) (by positivity) (1/8) (by norm_num)
  obtain ⟨Cz, hCz0, hCz⟩ := zeta_line_growth
  have hgi : Integrable (fun t : ℝ => 16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ))) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5/4) (by norm_num)
    simpa [Real.norm_eq_abs] using this.const_mul (16*(1 + 2*C₁*Cz)^2)
  have hb : ∀ N t, ‖FN ε N t‖^2 ≤ 16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ)) :=
    fun N t => FN_bound ε hε C₁ Cz hC₁0 hCz0 hC₁ hCz N t
  have hlimF : ∀ t, Tendsto (fun N => FN ε N t) atTop (𝓝 (dampedSpectralResidual ε t)) :=
    FN_tendsto hpoly ε hε hε2
  have hbF : ∀ t, ‖dampedSpectralResidual ε t‖^2 ≤
      16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ)) := fun t =>
    le_of_tendsto' (((hlimF t).norm).pow 2) (fun N => hb N t)
  have hmF := F_meas ε hε2 hε
  have hmN : ∀ N, Measurable (fun t => FN ε N t) := fun N => (FN_continuous ε N).measurable
  have hFi : Integrable (fun t => ‖dampedSpectralResidual ε t‖^2) :=
    Integrable.mono' hgi ((hmF.norm.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hbF t)
  have hNi : ∀ N, Integrable (fun t => ‖FN ε N t‖^2) := fun N =>
    Integrable.mono' hgi (((hmN N).norm.pow_const 2).aestronglyMeasurable)
      (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb N t)
  have hDi : ∀ N, Integrable (fun t => ‖FN ε N t - dampedSpectralResidual ε t‖^2) := fun N =>
    Integrable.mono' (hgi.const_mul 4)
      ((((hmN N).sub hmF).norm.pow_const 2).aestronglyMeasurable) (ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have := sq_norm_sub_le (FN ε N t) (dampedSpectralResidual ε t)
        linarith [hb N t, hbF t])
  -- (i) L² convergence of the finite residuals
  have hT1 : Tendsto (fun N => ∫ t, ‖FN ε N t - dampedSpectralResidual ε t‖^2) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (f := fun _ : ℝ => (0:ℝ))
      (fun t => 4 * (16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ))))
      (Eventually.of_forall fun N =>
        (((hmN N).sub hmF).norm.pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun N => ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        show ‖FN ε N t - dampedSpectralResidual ε t‖^2 ≤ _
        have := sq_norm_sub_le (FN ε N t) (dampedSpectralResidual ε t)
        linarith [hb N t, hbF t])
      (hgi.const_mul 4)
      (ae_of_all _ fun t => by
        have h := (((hlimF t).sub (tendsto_const_nhds (x := dampedSpectralResidual ε t))).norm).pow 2
        simpa using h)
    simpa using this
  -- (ii) convergence of the energies
  have hT2 : Tendsto (fun N => ∫ t, ‖FN ε N t‖^2) atTop
      (𝓝 (∫ t, ‖dampedSpectralResidual ε t‖^2)) :=
    tendsto_integral_filter_of_dominated_convergence
      (fun t => 16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ)))
      (Eventually.of_forall fun N => ((hmN N).norm.pow_const 2).aestronglyMeasurable)
      (Eventually.of_forall fun N => ae_of_all _ fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hb N t)
      hgi (ae_of_all _ fun t => ((hlimF t).norm).pow 2)
  -- the finite identity for each truncation
  have hFNiso : ∀ N, (∫ t, ‖FN ε N t‖^2) = 2*Real.pi * ∑' n : ℕ,
      (dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) := by
    intro N
    have h := (frmp (Finset.range N) (cc ε)).2
    have hfun : (fun n : ℕ => ‖1 - gf (Finset.range N) (cc ε) n‖^2 / ((n+1:ℝ)*(n+2:ℝ))) =
        fun n => (dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) := by
      funext n
      rw [gf_link, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hfun] at h
    exact h
  -- the isometry for differences of truncations
  have hisoNM : ∀ N M : ℕ,
      Summable (fun n : ℕ => (dampedResidualFinite N ε (n+1) - dampedResidualFinite M ε (n+1))^2 /
        ((n+1:ℝ)*(n+2:ℝ))) ∧
      Integrable (fun t => ‖FN ε N t - FN ε M t‖^2) ∧
      2*Real.pi * ∑' n : ℕ, (dampedResidualFinite N ε (n+1) - dampedResidualFinite M ε (n+1))^2 /
        ((n+1:ℝ)*(n+2:ℝ)) = ∫ t, ‖FN ε N t - FN ε M t‖^2 := by
    intro N M
    obtain ⟨hi, hs, he⟩ := iso (Finset.range (N+M))
      (fun k => (if k < N then cc ε k else 0) - (if k < M then cc ε k else 0))
    simp only [Xf_trunc_sub, gf_trunc_sub] at hi hs he
    have hf1 : (fun t : ℝ => ‖(Xf (Finset.range N) (cc ε) t - Xf (Finset.range M) (cc ε) t) *
        riemannZeta (sl t) / sl t‖^2) = fun t => ‖FN ε N t - FN ε M t‖^2 := by
      funext t
      have e : FN ε N t - FN ε M t = -((Xf (Finset.range N) (cc ε) t -
          Xf (Finset.range M) (cc ε) t) * riemannZeta (sl t) / sl t) := by
        simp only [FN]; ring
      rw [e, norm_neg]
    have hf2 : (fun n : ℕ => ‖gf (Finset.range N) (cc ε) n - gf (Finset.range M) (cc ε) n‖^2 /
        ((n+1:ℝ)*(n+2:ℝ))) = fun n => (dampedResidualFinite N ε (n+1) -
          dampedResidualFinite M ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) := by
      funext n
      have e1 := gf_link ε N n
      have e2 := gf_link ε M n
      have e : gf (Finset.range N) (cc ε) n - gf (Finset.range M) (cc ε) n =
          ((dampedResidualFinite M ε (n+1) - dampedResidualFinite N ε (n+1) : ℝ) : ℂ) := by
        push_cast
        linear_combination e2 - e1
      rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    rw [hf1] at hi he
    rw [hf2] at hs he
    exact ⟨hs, hi, he.symm⟩
  have hR0 : ∀ m, dampedResidualFinite 0 ε m = 1 := by
    intro m; simp [dampedResidualFinite]
  have hRsq : ∀ N, Summable (fun n : ℕ => (dampedResidualFinite N ε (n+1))^2 /
      ((n+1:ℝ)*(n+2:ℝ))) := by
    intro N
    have hs := (hisoNM N 0).1
    simp only [hR0] at hs
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hs.mul_left 2).add (summable_w.mul_left 2))
    have h := real_sq_sub_le (dampedResidualFinite N ε (n+1) - 1) (-1)
    have hW : (0:ℝ) < (n+1:ℝ)*(n+2:ℝ) := by positivity
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    apply div_le_div_of_nonneg_right _ hW.le
    nlinarith [h]
  -- Cauchy estimate in the weighted sequence space
  have hcauchy : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      ∑' n : ℕ, (dampedResidualFinite N ε (n+1) - dampedResidualFinite M ε (n+1))^2 /
        ((n+1:ℝ)*(n+2:ℝ)) ≤ δ := by
    intro δ hδ
    have hδ' : 0 < δ * Real.pi / 2 := by positivity
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hT1.eventually (gt_mem_nhds hδ'))
    refine ⟨N₀, fun N M hN hM => ?_⟩
    obtain ⟨_, hi, he⟩ := hisoNM N M
    have hle : (∫ t, ‖FN ε N t - FN ε M t‖^2) ≤
        ∫ t, (2*‖FN ε N t - dampedSpectralResidual ε t‖^2 +
          2*‖FN ε M t - dampedSpectralResidual ε t‖^2) := by
      refine integral_mono hi (((hDi N).const_mul 2).add ((hDi M).const_mul 2)) (fun t => ?_)
      have := sq_norm_sub_le (FN ε N t - dampedSpectralResidual ε t)
        (FN ε M t - dampedSpectralResidual ε t)
      simp only [sub_sub_sub_cancel_right] at this
      exact this
    rw [integral_add ((hDi N).const_mul 2) ((hDi M).const_mul 2), integral_const_mul,
      integral_const_mul] at hle
    have h1 := hN₀ N hN
    have h2 := hN₀ M hM
    have hpi : 0 < 2*Real.pi := by positivity
    have : 2*Real.pi * ∑' n : ℕ, (dampedResidualFinite N ε (n+1) -
        dampedResidualFinite M ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) ≤ 2*Real.pi * δ := by
      rw [he]; linarith
    exact le_of_mul_le_mul_left this hpi
  have hpart : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
      (∑ n ∈ Finset.range H,
        (dampedResidualFinite N ε (n+1) - dampedResidualProfile ε (n+1))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) ≤ δ := by
    intro δ hδ
    obtain ⟨N₀, hN₀⟩ := hcauchy δ hδ
    refine ⟨N₀, fun N hN H => ?_⟩
    have hlim : Tendsto (fun M => ∑ n ∈ Finset.range H,
        (dampedResidualFinite N ε (n+1) - dampedResidualFinite M ε (n+1))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) atTop
        (𝓝 (∑ n ∈ Finset.range H,
          (dampedResidualFinite N ε (n+1) - dampedResidualProfile ε (n+1))^2 /
            ((n+1 : ℝ)*(n+2 : ℝ)))) := by
      refine tendsto_finsetSum _ (fun n _ => ?_)
      exact ((tendsto_const_nhds.sub (residual_tendsto_profile ε hε (n+1))).pow 2).div_const _
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨N₀, fun M hM => ?_⟩)
    exact ((hisoNM N M).1.sum_le_tsum _ (fun n _ => by positivity)).trans (hN₀ N M hN hM)
  -- conclusion (1)
  refine ⟨fun δ hδ => ?_, ?_⟩
  · obtain ⟨N₀, hN₀⟩ := hpart (δ/2) (by positivity)
    exact ⟨N₀, fun N hN H => lt_of_le_of_lt (hN₀ N hN H) (by linarith)⟩
  -- summability of the profile
  obtain ⟨N₁, hN₁⟩ := hpart 1 one_pos
  have hPs : Summable (fun n : ℕ => (dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ))) := by
    refine summable_of_sum_range_le (c := 2*1 + 2*∑' n : ℕ,
      (dampedResidualFinite N₁ ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) (fun n => by positivity)
      (fun H => ?_)
    have hpt : ∀ n ∈ Finset.range H, (dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ)) ≤
        2*((dampedResidualFinite N₁ ε (n+1) - dampedResidualProfile ε (n+1))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) +
        2*((dampedResidualFinite N₁ ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) := by
      intro n _
      have h := real_sq_sub_le (dampedResidualFinite N₁ ε (n+1) - dampedResidualProfile ε (n+1))
        (dampedResidualFinite N₁ ε (n+1))
      have hW : (0:ℝ) < (n+1:ℝ)*(n+2:ℝ) := by positivity
      rw [mul_div_assoc', mul_div_assoc', ← add_div]
      apply div_le_div_of_nonneg_right _ hW.le
      nlinarith [h]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := hN₁ N₁ le_rfl H
    have h2 := (hRsq N₁).sum_le_tsum (Finset.range H) (fun n _ => by positivity)
    linarith
  refine ⟨hPs, hFi, ?_⟩
  -- convergence of the discrete energies
  have hRle : ∀ N, ∑' n : ℕ, (dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) ≤
      (∫ t, 16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ))) / (2*Real.pi) := by
    intro N
    have h := integral_mono (hNi N) hgi (fun t => hb N t)
    rw [hFNiso N] at h
    rw [le_div_iff₀ (by positivity)]
    linarith
  set G₀ : ℝ := (∫ t, 16*(1 + 2*C₁*Cz)^2 * (1+|t|)^(-(5/4:ℝ))) / (2*Real.pi) with hG₀
  set Pi0 : ℝ := ∑' n : ℕ, (dampedResidualProfile ε (n+1))^2 / ((n+1 : ℝ)*(n+2 : ℝ)) with hPi0def
  have hPi0nn : 0 ≤ Pi0 := tsum_nonneg (fun n => by positivity)
  have hG0 : 0 ≤ G₀ := le_trans (tsum_nonneg (fun n => by positivity)) (hRle 0)
  have hconvR : Tendsto (fun N => ∑' n : ℕ, (dampedResidualFinite N ε (n+1))^2 /
      ((n+1:ℝ)*(n+2:ℝ))) atTop (𝓝 Pi0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    set lam : ℝ := (2*G₀ + 2*Pi0 + 1) / δ with hlam
    have hlam0 : 0 < lam := by positivity
    obtain ⟨N₀, hN₀⟩ := hpart (δ/lam) (by positivity)
    refine ⟨N₀, fun N hN => ?_⟩
    rw [Real.dist_eq]
    -- summabilities
    have hW : ∀ n : ℕ, (0:ℝ) < (n+1:ℝ)*(n+2:ℝ) := fun n => by positivity
    have sa : Summable (fun n : ℕ => (dampedResidualFinite N ε (n+1) -
        dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (((hRsq N).mul_left 2).add (hPs.mul_left 2))
      have h := real_sq_sub_le (dampedResidualFinite N ε (n+1)) (dampedResidualProfile ε (n+1))
      rw [mul_div_assoc', mul_div_assoc', ← add_div]
      exact div_le_div_of_nonneg_right h (hW n).le
    have sb : Summable (fun n : ℕ => (dampedResidualFinite N ε (n+1) +
        dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) := by
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (((hRsq N).mul_left 2).add (hPs.mul_left 2))
      have h := real_sq_sub_le (dampedResidualFinite N ε (n+1)) (-dampedResidualProfile ε (n+1))
      simp only [sub_neg_eq_add, neg_sq] at h ⊢
      rw [mul_div_assoc', mul_div_assoc', ← add_div]
      exact div_le_div_of_nonneg_right h (hW n).le
    have hA : ∑' n : ℕ, (dampedResidualFinite N ε (n+1) -
        dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) ≤ δ / lam :=
      Real.tsum_le_of_sum_range_le (fun n => by positivity) (hN₀ N hN)
    have hB : ∑' n : ℕ, (dampedResidualFinite N ε (n+1) +
        dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) ≤ 2*G₀ + 2*Pi0 := by
      have h := Summable.tsum_le_tsum (fun n => ?_) sb (((hRsq N).mul_left 2).add (hPs.mul_left 2))
      · rw [Summable.tsum_add ((hRsq N).mul_left 2) (hPs.mul_left 2), tsum_mul_left,
          tsum_mul_left] at h
        linarith [hRle N]
      · have h := real_sq_sub_le (dampedResidualFinite N ε (n+1)) (-dampedResidualProfile ε (n+1))
        simp only [sub_neg_eq_add, neg_sq] at h ⊢
        rw [mul_div_assoc', mul_div_assoc', ← add_div]
        exact div_le_div_of_nonneg_right h (hW n).le
    -- the dominating series
    have sy : Summable (fun n : ℕ => (lam * ((dampedResidualFinite N ε (n+1) -
        dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) +
        ((dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
          ((n+1:ℝ)*(n+2:ℝ))) / lam) / 2) :=
      ((sa.mul_left lam).add (sb.div_const lam)).div_const 2
    have hxy : ∀ n : ℕ, |(dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) -
        (dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))| ≤
        (lam * ((dampedResidualFinite N ε (n+1) -
          dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) +
          ((dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
            ((n+1:ℝ)*(n+2:ℝ))) / lam) / 2 := by
      intro n
      have h := abs_sq_sub_sq_le (dampedResidualFinite N ε (n+1))
        (dampedResidualProfile ε (n+1)) lam hlam0
      rw [← sub_div, abs_div, abs_of_pos (hW n)]
      have e : (lam * ((dampedResidualFinite N ε (n+1) -
          dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) +
          ((dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
            ((n+1:ℝ)*(n+2:ℝ))) / lam) / 2 =
          ((lam * (dampedResidualFinite N ε (n+1) - dampedResidualProfile ε (n+1))^2 +
            (dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 / lam) / 2) /
              ((n+1:ℝ)*(n+2:ℝ)) := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right h (hW n).le
    have hdiff : ∑' n : ℕ, (dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) - Pi0 =
        ∑' n : ℕ, ((dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) -
          (dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) :=
      ((hRsq N).tsum_sub hPs).symm
    have hsx : Summable (fun n : ℕ => (dampedResidualFinite N ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) -
        (dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) := (hRsq N).sub hPs
    have hup := Summable.tsum_le_tsum (fun n => (abs_le.1 (hxy n)).2) hsx sy
    have hlo := Summable.tsum_le_tsum (fun n => (abs_le.1 (hxy n)).1) sy.neg hsx
    rw [tsum_neg] at hlo
    have hsyv : ∑' n : ℕ, (lam * ((dampedResidualFinite N ε (n+1) -
        dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ))) +
        ((dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
          ((n+1:ℝ)*(n+2:ℝ))) / lam) / 2 =
        (lam * ∑' n : ℕ, (dampedResidualFinite N ε (n+1) -
          dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) +
          (∑' n : ℕ, (dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
            ((n+1:ℝ)*(n+2:ℝ))) / lam) / 2 := by
      rw [tsum_div_const, Summable.tsum_add (sa.mul_left lam) (sb.div_const lam), tsum_mul_left,
        tsum_div_const]
    have hbound : (lam * ∑' n : ℕ, (dampedResidualFinite N ε (n+1) -
          dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) +
          (∑' n : ℕ, (dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
            ((n+1:ℝ)*(n+2:ℝ))) / lam) / 2 < δ := by
      have e1 : lam * ∑' n : ℕ, (dampedResidualFinite N ε (n+1) -
          dampedResidualProfile ε (n+1))^2 / ((n+1:ℝ)*(n+2:ℝ)) ≤ δ := by
        calc _ ≤ lam * (δ / lam) := by gcongr
          _ = δ := by field_simp
      have e2 : (∑' n : ℕ, (dampedResidualFinite N ε (n+1) + dampedResidualProfile ε (n+1))^2 /
            ((n+1:ℝ)*(n+2:ℝ))) / lam < δ := by
        rw [div_lt_iff₀ hlam0, hlam]
        have : δ * ((2*G₀ + 2*Pi0 + 1) / δ) = 2*G₀ + 2*Pi0 + 1 := by field_simp
        rw [this]
        linarith
      linarith
    rw [hdiff, abs_lt]
    constructor <;> linarith
  have hlim2 : Tendsto (fun N => ∫ t, ‖FN ε N t‖^2) atTop (𝓝 (2*Real.pi * Pi0)) := by
    have := hconvR.const_mul (2*Real.pi)
    refine this.congr (fun N => ?_)
    rw [hFNiso N]
  exact tendsto_nhds_unique hT2 hlim2

end DampedMellinAux

theorem solution
    (hpoly : NymanBeurling.MoebiusPolynomialBoundaryBound) :
    (∀ ε : ℝ, 0 < ε → ε < 1/2 → ∀ δ : ℝ, 0 < δ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ H : ℕ,
        (∑ n ∈ Finset.range H,
          (NymanBeurling.dampedResidualFinite N ε (n+1) -
            NymanBeurling.dampedResidualProfile ε (n+1))^2 /
              ((n+1 : ℝ)*(n+2 : ℝ))) < δ) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1/2 →
      Summable (fun n : ℕ => (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) ∧
      Integrable (fun t : ℝ => ‖NymanBeurling.dampedSpectralResidual ε t‖^2) ∧
      (∫ t : ℝ, ‖NymanBeurling.dampedSpectralResidual ε t‖^2) =
        2*Real.pi * ∑' n : ℕ, (NymanBeurling.dampedResidualProfile ε (n+1))^2 /
          ((n+1 : ℝ)*(n+2 : ℝ))) :=
  ⟨fun ε hε hε2 => (DampedMellinAux.main_package hpoly ε hε hε2).1,
   fun ε hε hε2 => (DampedMellinAux.main_package hpoly ε hε hε2).2⟩
