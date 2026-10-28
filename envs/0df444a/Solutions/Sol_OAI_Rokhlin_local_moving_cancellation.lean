-- Prove2me | solution 1 for OAI.Rokhlin.local_moving_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T07:09:58.157769+00:00
-- url     : https://prove2.me/submissions/67794da0-f95a-4dad-ba34-e7504154411c

import Mathlib
import Definitions.Def_OAIQ3Ro002
import Theorems.Thm_OAI_Rokhlin_polynomial_cancellation

section
-- module Solutions.OAIQ3_Rok.Compat
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Foundations
attribute [-instance] _root_.OAI.Rokhlin.StrongUnitary.measurableSpace _root_.OAI.Rokhlin.StrongUnitary.topology _root_.OAI.Rokhlin.submodule_completeSpace_inf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

section

namespace ProjectiveCharacters
variable {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
  {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
  (hχ : ProjectiveCharacters η χ)
include hχ

theorem integrable (l : L) : Integrable (χ l) η :=
  (integrable_const (1 : ℝ)).mono' (hχ.measurable l) ((hχ.modulus l).mono (fun _ h => h.le))

omit [IsProbabilityMeasure η] in

theorem conjugate (l : L) : ∃ c : ℂ, ‖c‖ = 1 ∧
    (fun y => conj (χ l y)) =ᵐ[η] (fun y => c * χ (-l) y) := by
  obtain ⟨c, hc, hm⟩ := hχ.mul (-l) l
  refine ⟨c⁻¹, by simp [hc], ?_⟩
  filter_upwards [hm, hχ.zero, hχ.modulus l] with y hy h0 hn
  simp only [neg_add_cancel, h0, mul_one] at hy
  have hcn : c ≠ 0 := by intro hz; simp [hz] at hc
  have hln : χ l y ≠ 0 := by intro hz; simp [hz] at hn
  rw [← Complex.inv_eq_conj hn]
  apply (mul_right_cancel₀ hln)
  rw [inv_mul_cancel₀ hln, mul_assoc, hy, inv_mul_cancel₀ hcn]

omit [IsProbabilityMeasure η] in

theorem finset_prod {ι : Type*} (s : Finset ι) (l : ι → L) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      (fun y => ∏ i ∈ s, χ (l i) y) =ᵐ[η] (fun y => c * χ (∑ i ∈ s, l i) y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, norm_one, ?_⟩
    filter_upwards [hχ.zero] with y hy
    simp [hy]
  | @insert i s hi ih =>
    obtain ⟨c, hc, hsp⟩ := ih
    obtain ⟨d, hd, hmul⟩ := hχ.mul (l i) (∑ j ∈ s, l j)
    refine ⟨c * d, by simp [hc, hd], ?_⟩
    filter_upwards [hsp, hmul] with y hy hm
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, hy]
    calc
      χ (l i) y * (c * χ (∑ j ∈ s, l j) y) =
        c * (χ (l i) y * χ (∑ j ∈ s, l j) y) := by ring
      _ = c * (d * χ (l i + ∑ j ∈ s, l j) y) := by rw [hm]
      _ = c * d * χ (l i + ∑ j ∈ s, l j) y := by ring

omit [IsProbabilityMeasure η] in
omit [IsProbabilityMeasure η] in

theorem integral_finset_prod_eq_zero {ι : Type*} (s : Finset ι) (l : ι → L)
    (hl : ∑ i ∈ s, l i ≠ 0) :
    ∫ y, ∏ i ∈ s, χ (l i) y ∂η = 0 := by
  obtain ⟨c, _, hp⟩ := hχ.finset_prod s l
  rw [integral_congr_ae hp, integral_const_mul, hχ.mean _ hl, mul_zero]

theorem integrable_finset_prod {ι : Type*} (s : Finset ι) (l : ι → L) :
    Integrable (fun y => ∏ i ∈ s, χ (l i) y) η := by
  obtain ⟨c, _, hp⟩ := hχ.finset_prod s l
  exact ((hχ.integrable _).const_mul c).congr hp.symm

theorem weighted_finset_prod {ι : Type*} (s : Finset ι) (l : ι → L) (a : ι → ℂ) :
    Integrable (fun y => ∏ i ∈ s, a i * χ (l i) y) η ∧
    (∫ y, ∏ i ∈ s, a i * χ (l i) y ∂η) =
      (∏ i ∈ s, a i) * ∫ y, ∏ i ∈ s, χ (l i) y ∂η := by
  simp_rw [Finset.prod_mul_distrib]
  exact ⟨(hχ.integrable_finset_prod s l).const_mul _, integral_const_mul _ _⟩

end ProjectiveCharacters

namespace ProjectiveCharacters
variable {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
  {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
  (hχ : ProjectiveCharacters η χ)
include hχ

theorem integral_signed_linear_prod_eq_zero (l : ℕ → L) (hd : Dissociated l)
    (s : Finset ℕ) (hs : s.Nonempty) (a b : ℕ → ℂ) :
    Integrable (fun y => ∏ i ∈ s, (a i * χ (l i) y + b i * χ (-l i) y)) η ∧
    (∫ y, ∏ i ∈ s, (a i * χ (l i) y + b i * χ (-l i) y) ∂η) = 0 := by
  classical
  let term (t : Finset ℕ) (y : Y) :=
    (∏ i ∈ t, a i * χ (l i) y) * ∏ i ∈ s \ t, b i * χ (-l i) y
  have ht (t : Finset ℕ) (hts : t ⊆ s) : term t = fun y => ∏ i ∈ s,
      (if i ∈ t then a i else b i) * χ (if i ∈ t then l i else -l i) y := by
    funext y
    let f (i : ℕ) := (if i ∈ t then a i else b i) *
      χ (if i ∈ t then l i else -l i) y
    change _ = ∏ i ∈ s, f i
    rw [← Finset.prod_sdiff hts, mul_comm]
    apply congrArg₂ (· * ·)
    · exact Finset.prod_congr rfl (fun i hi => by simp [f, hi])
    · exact Finset.prod_congr rfl (fun i hi => by simp [f, (Finset.mem_sdiff.mp hi).2])
  have hterm (t : Finset ℕ) (hts : t ∈ s.powerset) :
      Integrable (term t) η ∧ (∫ y, term t y ∂η) = 0 := by
    rw [ht t (Finset.mem_powerset.mp hts)]
    have hh := hχ.weighted_finset_prod s
      (fun i => if i ∈ t then l i else -l i) (fun i => if i ∈ t then a i else b i)
    refine ⟨hh.1, hh.2.trans ?_⟩
    rw [hχ.integral_finset_prod_eq_zero s _ (by
      simpa using hd s hs (fun i => decide (i ∈ t))), mul_zero]
  have heq : (fun y => ∏ i ∈ s, (a i * χ (l i) y + b i * χ (-l i) y)) =
      fun y => ∑ t ∈ s.powerset, term t y := by
    funext y
    exact Finset.prod_add _ _ s
  rw [heq]
  exact ⟨integrable_finsetSum _ (fun t ht => (hterm t ht).1), by
    rw [integral_finsetSum _ (fun t ht => (hterm t ht).1)]
    exact Finset.sum_eq_zero (fun t ht => (hterm t ht).2)⟩

theorem integral_real_prod_eq_zero (l : ℕ → L) (hd : Dissociated l)
    (s : Finset ℕ) (hs : s.Nonempty) (w : ℕ → ℂ) :
    Integrable (fun y => ∏ i ∈ s, (w i * conj (χ (l i) y)).re) η ∧
    (∫ y, ∏ i ∈ s, (w i * conj (χ (l i) y)).re ∂η) = 0 := by
  choose c hc heq using fun i => hχ.conjugate (l i)
  have hlin := hχ.integral_signed_linear_prod_eq_zero l hd s hs
    (fun i => conj (w i) / 2) (fun i => w i * c i / 2)
  have heq' : (fun y => ((∏ i ∈ s, (w i * conj (χ (l i) y)).re : ℝ) : ℂ)) =ᵐ[η]
      (fun y => ∏ i ∈ s, (conj (w i) / 2 * χ (l i) y +
        (w i * c i / 2) * χ (-l i) y)) := by
    filter_upwards [ae_all_iff.mpr heq] with y hy
    push_cast
    apply Finset.prod_congr rfl
    intro i _
    rw [Complex.re_eq_add_conj, map_mul, starRingEnd_self_apply, hy i]
    ring
  have hint : Integrable (fun y => ((∏ i ∈ s, (w i * conj (χ (l i) y)).re : ℝ) : ℂ)) η :=
    hlin.1.congr heq'.symm
  have hintR := hint.re
  change Integrable (fun y => (((∏ i ∈ s, (w i * conj (χ (l i) y)).re : ℝ) : ℂ)).re) η at hintR
  refine ⟨by simpa only [Complex.ofReal_re] using hintR, ?_⟩
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, integral_congr_ae heq', hlin.2]
  rfl

theorem integral_affine_real_prod (l : ℕ → L) (hd : Dissociated l)
    (s : Finset ℕ) (w : ℕ → ℂ) (b : ℕ → ℝ) :
    Integrable (fun y => ∏ i ∈ s, (b i + (w i * conj (χ (l i) y)).re)) η ∧
    (∫ y, ∏ i ∈ s, (b i + (w i * conj (χ (l i) y)).re) ∂η) = ∏ i ∈ s, b i := by
  classical
  have ht (t : Finset ℕ) :
      Integrable (fun y => (∏ i ∈ t, (w i * conj (χ (l i) y)).re) *
        ∏ i ∈ s \ t, b i) η ∧
      (∫ y, (∏ i ∈ t, (w i * conj (χ (l i) y)).re) *
        ∏ i ∈ s \ t, b i ∂η) = if t = ∅ then ∏ i ∈ s, b i else 0 := by
    by_cases he : t = ∅
    · subst t
      simp
    · obtain ⟨hit, hzt⟩ := hχ.integral_real_prod_eq_zero l hd t
        (Finset.nonempty_iff_ne_empty.mpr he) w
      exact ⟨hit.mul_const _, by rw [integral_mul_const, hzt]; simp [he]⟩
  have hex (y : Y) :
      (∏ i ∈ s, (b i + (w i * conj (χ (l i) y)).re)) =
      ∑ t ∈ s.powerset, (∏ i ∈ t, (w i * conj (χ (l i) y)).re) *
        ∏ i ∈ s \ t, b i := by
    simp_rw [add_comm (b _)]
    exact Finset.prod_add _ _ _
  simp_rw [hex]
  refine ⟨integrable_finsetSum _ (fun t _ => (ht t).1), ?_⟩
  rw [integral_finsetSum _ (fun t _ => (ht t).1)]
  simp_rw [(ht _).2]
  simp

theorem dissociated_exponential_bound (l : ℕ → L) (hd : Dissociated l)
    (s : Finset ℕ) (w : ℕ → ℂ) (hw : ∀ i ∈ s, ‖w i‖ ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    Integrable (fun y => Real.exp (θ * ∑ i ∈ s, (w i * conj (χ (l i) y)).re)) η ∧
    (∫ y, Real.exp (θ * ∑ i ∈ s, (w i * conj (χ (l i) y)).re) ∂η) ≤
      Real.exp (2 * θ ^ 2 * s.card) := by
  have hg := hχ.integral_affine_real_prod l hd s (fun i => (θ : ℂ) * w i)
    (fun _ => 1 + 2 * θ ^ 2)
  have hscale (i : ℕ) (y : Y) :
      ((θ : ℂ) * w i * conj (χ (l i) y)).re =
        θ * (w i * conj (χ (l i) y)).re := by
    simp only [mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [hscale] at hg
  have hpoint : ∀ᵐ y ∂η, ∀ i ∈ s,
      Real.exp (θ * (w i * conj (χ (l i) y)).re) ≤
        1 + 2 * θ ^ 2 + θ * (w i * conj (χ (l i) y)).re := by
    filter_upwards [ae_all_iff.mpr (fun i => hχ.modulus (l i))] with y hy i hi
    have hr : |(w i * conj (χ (l i) y)).re| ≤ 1 := by
      calc
        _ ≤ ‖w i * conj (χ (l i) y)‖ := Complex.abs_re_le_norm _
        _ = ‖w i‖ := by rw [norm_mul, Complex.norm_conj, hy i, mul_one]
        _ ≤ 1 := hw i hi
    have ht : |θ * (w i * conj (χ (l i) y)).re| ≤ θ := by
      rw [abs_mul, abs_of_nonneg hθ]
      simpa using mul_le_mul_of_nonneg_left hr hθ
    have hq := Real.abs_exp_sub_one_sub_id_le (ht.trans hθ1)
    have hqq : (θ * (w i * conj (χ (l i) y)).re) ^ 2 ≤ θ ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hθ).mpr ht
    have hupper := (le_abs_self _).trans hq
    nlinarith [sq_nonneg θ]
  have hprod : (fun y => Real.exp (θ * ∑ i ∈ s, (w i * conj (χ (l i) y)).re)) ≤ᵐ[η]
      (fun y => ∏ i ∈ s, (1 + 2 * θ ^ 2 + θ * (w i * conj (χ (l i) y)).re)) := by
    filter_upwards [hpoint] with y hy
    rw [Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) hy
  have hm : AEStronglyMeasurable
      (fun y => Real.exp (θ * ∑ i ∈ s, (w i * conj (χ (l i) y)).re)) η := by
    apply Real.continuous_exp.comp_aestronglyMeasurable
    apply AEStronglyMeasurable.const_mul
    have hi (i : ℕ) : AEStronglyMeasurable
        (fun y => (w i * conj (χ (l i) y)).re) η :=
      Complex.continuous_re.comp_aestronglyMeasurable
        ((hχ.measurable (l i)).star.const_mul (w i))
    convert Finset.aestronglyMeasurable_sum s (fun i _ => hi i) using 1
    all_goals try with_reducible_and_instances rfl
    funext y
    simp only [Finset.sum_apply]
  have hint := hg.1.mono' hm (hprod.mono (fun y hy => by
    simpa only [Real.norm_of_nonneg (Real.exp_pos _).le] using hy))
  refine ⟨hint, (integral_mono_ae hint hg.1 hprod).trans ?_⟩
  rw [hg.2, Finset.prod_const]
  calc
    (1 + 2 * θ ^ 2) ^ s.card ≤ (Real.exp (2 * θ ^ 2)) ^ s.card := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (2 * θ ^ 2)
    _ = Real.exp (2 * θ ^ 2 * s.card) := by rw [← Real.exp_nat_mul, mul_comm]

end ProjectiveCharacters
end

open MeasureTheory Filter
open scoped BigOperators Topology

section

section FiniteDistribution
variable {A : Type*} [Fintype A] (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
include hp hsum

theorem probability_le_one (a : A) : p a ≤ 1 := by
  rw [← hsum]
  exact Finset.single_le_sum (fun a _ => hp a) (Finset.mem_univ a)

theorem entropy_term_nonneg (a : A) : 0 ≤ -p a * Real.log (p a) := by
  rw [neg_mul, neg_nonneg]
  exact mul_nonpos_of_nonneg_of_nonpos (hp a)
    (Real.log_nonpos (hp a) (probability_le_one p hp hsum a))

theorem shannonEntropy_nonneg : 0 ≤ shannonEntropy p :=
  Finset.sum_nonneg (fun a _ => entropy_term_nonneg p hp hsum a)

theorem unlikely_mass_bound {a : ℝ} (ha : 0 < a) :
    ∑ i ∈ Finset.univ.filter (fun i => p i < Real.exp (-a)), p i ≤
      shannonEntropy p / a := by
  classical
  rw [le_div_iff₀ ha, Finset.sum_mul]
  calc
    ∑ i ∈ Finset.univ.filter (fun i => p i < Real.exp (-a)), p i * a ≤
        ∑ i ∈ Finset.univ.filter (fun i => p i < Real.exp (-a)), -p i * Real.log (p i) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hz : p i = 0
      · simp [hz]
      · have hpi : 0 < p i := (hp i).lt_of_ne' hz
        have hlog := (Real.log_lt_iff_lt_exp hpi).mpr (Finset.mem_filter.mp hi).2
        nlinarith [mul_nonneg (hp i) (le_of_lt (show 0 < -a - Real.log (p i) by linarith))]
    _ ≤ shannonEntropy p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro i _ _
      exact entropy_term_nonneg p hp hsum i

theorem likely_card_bound (a : ℝ) :
    ((Finset.univ.filter (fun i => Real.exp (-a) ≤ p i)).card : ℝ) ≤ Real.exp a := by
  classical
  have h : ((Finset.univ.filter (fun i => Real.exp (-a) ≤ p i)).card : ℝ) *
      Real.exp (-a) ≤ 1 := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => Real.exp (-a) ≤ p i), Real.exp (-a) := by simp
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => Real.exp (-a) ≤ p i), p i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
      _ ≤ ∑ i, p i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
      _ = 1 := hsum
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos a).le
  simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] using hm

end FiniteDistribution
variable {Y : Type*} [MeasurableSpace Y] {η : Measure Y} [IsProbabilityMeasure η]

theorem exponential_tail_bound (S : Y → ℝ) {θ b t : ℝ} (hθ : 0 < θ)
    (hint : Integrable (fun y => Real.exp (θ * S y)) η)
    (hbound : (∫ y, Real.exp (θ * S y) ∂η) ≤ Real.exp b) :
    η.real {y | t < S y} ≤ Real.exp (b - θ * t) := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall (fun y => (Real.exp_pos (θ * S y)).le)) hint (Real.exp (θ * t))
  have hsub : {y | t < S y} ⊆ {y | Real.exp (θ * t) ≤ Real.exp (θ * S y)} := by
    intro y hy
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.le hθ.le)
  have hm' := (mul_le_mul_of_nonneg_left (measureReal_mono hsub) (Real.exp_pos _).le).trans
    (hm.trans hbound)
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hm')

theorem randomized_tail_bound {A : Type*} [Fintype A] (F : Y → A)
    (hF : ∀ a, MeasurableSet (F ⁻¹' {a})) (S : A → Y → ℝ)
    {a ε δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (ht : ∀ w, η.real {y | ε < S w y} ≤ δ) :
    η.real {y | ε < S (F y) y} ≤
      shannonEntropy (fun w => η.real (F ⁻¹' {w})) / a + Real.exp a * δ := by
  classical
  let p (w : A) := η.real (F ⁻¹' {w})
  have hp : ∀ w, 0 ≤ p w := fun _ => measureReal_nonneg
  have hsum : ∑ w, p w = 1 := by
    have hh := sum_measureReal_preimage_singleton (μ := η) Finset.univ (fun w _ => hF w)
    simpa [p] using hh
  let good := Finset.univ.filter (fun w => Real.exp (-a) ≤ p w)
  let bad := Finset.univ.filter (fun w => p w < Real.exp (-a))
  have hsub : {y | ε < S (F y) y} ⊆
      (F ⁻¹' (bad : Set A)) ∪ ⋃ w ∈ good, {y | ε < S w y} := by
    intro y hy
    by_cases hg : Real.exp (-a) ≤ p (F y)
    · right
      exact Set.mem_iUnion.mpr ⟨F y, Set.mem_iUnion.mpr ⟨by simp [good, hg], hy⟩⟩
    · left
      simpa [bad] using lt_of_not_ge hg
  have hbad : η.real (F ⁻¹' (bad : Set A)) ≤ shannonEntropy p / a := by
    rw [← sum_measureReal_preimage_singleton bad (fun w _ => hF w)]
    exact unlikely_mass_bound p hp hsum ha
  calc
    η.real {y | ε < S (F y) y} ≤
        η.real (F ⁻¹' (bad : Set A)) + η.real (⋃ w ∈ good, {y | ε < S w y}) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ shannonEntropy p / a + ∑ w ∈ good, η.real {y | ε < S w y} :=
      add_le_add hbad (measureReal_biUnion_finset_le _ _)
    _ ≤ shannonEntropy p / a + Real.exp a * δ := by
      apply add_le_add_right
      calc
        _ ≤ ∑ _ ∈ good, δ := Finset.sum_le_sum (fun w _ => ht w)
        _ = (good.card : ℝ) * δ := by simp
        _ ≤ Real.exp a * δ := mul_le_mul_of_nonneg_right (likely_card_bound p hp hsum a) hδ

end

section
open MeasureTheory Filter
open scoped BigOperators Topology

theorem integral_le_threshold_add_tail {Y : Type*} [MeasurableSpace Y]
    {η : Measure Y} [IsProbabilityMeasure η] {S : Y → ℝ}
    (hint : Integrable S η) (hS : ∀ᵐ y ∂η, S y ≤ 1) {ε : ℝ} (hε : 0 ≤ ε) :
    (∫ y, S y ∂η) ≤ ε + η.real {y | ε < S y} := by
  let s := {y | ε < S y}
  have hs : NullMeasurableSet s η :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hint.aestronglyMeasurable
  have he : ∫ y in s, S y ∂η ≤ η.real s := by
    have hh := integral_mono_ae hint.restrict (integrable_const (1 : ℝ))
      (ae_restrict_of_ae hS : ∀ᵐ y ∂η.restrict s, S y ≤ 1)
    simpa using hh
  have hc : ∫ y in sᶜ, S y ∂η ≤ ε := by
    have hh : ∫ y in sᶜ, S y ∂η ≤ η.real sᶜ * ε := by
      have hh := integral_mono_ae hint.restrict (integrable_const ε)
        ((ae_restrict_mem₀ hs.compl).mono (fun y hy => le_of_not_gt hy))
      simpa using hh
    exact hh.trans (by simpa using mul_le_mul_of_nonneg_right (measureReal_le_one (s := sᶜ)) hε)
  rw [← integral_add_compl₀ hs hint]
  linarith

end

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

variable {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
    {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}

theorem dissociated_tail_bound (hχ : ProjectiveCharacters η χ)
    (l : ℕ → L) (hd : Dissociated l) (n : ℕ) (hn : 0 < n)
    (w : ℕ → ℂ) (hw : ∀ i < n, ‖w i‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    η.real {y | ε < (∑ i ∈ Finset.range n, (w i * conj (χ (l i) y)).re) / n} ≤
      Real.exp (-ε ^ 2 * n / 8) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hh := hχ.dissociated_exponential_bound l hd (Finset.range n) w
    (fun i hi => hw i (Finset.mem_range.mp hi)) (θ := ε / 4) (by positivity) (by linarith)
  have ht := exponential_tail_bound
    (fun y => ∑ i ∈ Finset.range n, (w i * conj (χ (l i) y)).re)
    (θ := ε / 4) (b := 2 * (ε / 4) ^ 2 * n) (t := ε * n) (by positivity)
    hh.1 (by simpa using hh.2)
  have he : (-ε ^ 2 * (n : ℝ) / 8) = 2 * (ε / 4) ^ 2 * n - ε / 4 * (ε * n) := by ring
  rw [he]
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext y
  exact lt_div_iff₀ hn'

end

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate
variable {Y L A : Type*} [MeasurableSpace Y] [AddCommGroup L]
    {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem randomized_dissociated_tail (hχ : ProjectiveCharacters η χ)
    (l : ℕ → L) (hd : Dissociated l)
    (F : ℕ → Y → A) (hF : ∀ i, Measurable (F i))
    (v : A → ℂ) (hv : ∀ a, ‖v a‖ ≤ 1)
    (ω : ℕ → ℂ) (hω : ∀ i, ‖ω i‖ ≤ 1)
    (n : ℕ) (hn : 0 < n) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    η.real {y | ε < (∑ i ∈ Finset.range n,
      (ω i * v (F i y) * conj (χ (l i) y)).re) / n} ≤
      wordEntropy (η := η) F n / a + Real.exp (a - ε ^ 2 * n / 8) := by
  classical
  let w (t : Fin n → A) (i : ℕ) := if h : i < n then ω i * v (t ⟨i, h⟩) else 0
  let S (t : Fin n → A) (y : Y) :=
    (∑ i ∈ Finset.range n, (w t i * conj (χ (l i) y)).re) / n
  have ht (t : Fin n → A) : η.real {y | ε < S t y} ≤ Real.exp (-ε ^ 2 * n / 8) := by
    apply dissociated_tail_bound hχ l hd n hn (w t) _ hε hε1
    intro i hi
    simp only [w, dite_eq_left hi, norm_mul]
    exact (mul_le_mul (hω i) (hv _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hf : Measurable (entropyWord F n) := Measurable.of_eval (fun i => hF i.val)
  have hh := randomized_tail_bound (entropyWord F n)
    (fun t => hf (measurableSet_singleton t)) S ha (Real.exp_pos _).le ht
  have he (y : Y) : S (entropyWord F n y) y =
      (∑ i ∈ Finset.range n, (ω i * v (F i y) * conj (χ (l i) y)).re) / n := by
    dsimp only [S]
    apply congrArg (fun r : ℝ => r / (n : ℝ))
    apply Finset.sum_congr rfl
    intro i hi
    simp only [w, dite_eq_left (Finset.mem_range.mp hi), entropyWord]
  simp_rw [he] at hh
  simpa only [wordEntropy, ← Real.exp_add, sub_eq_add_neg, neg_mul, neg_div] using hh

end

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

theorem exists_aligning_phase (z : ℂ) : ∃ ω : ℂ, ‖ω‖ = 1 ∧ (ω * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, by simp, by simp [hz]⟩
  · refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · simp [hz]
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.div_ofReal_re,
        Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      field_simp

variable {Y L A : Type*} [MeasurableSpace Y] [AddCommGroup L]
    {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem dissociated_correlation_mean_bound (hχ : ProjectiveCharacters η χ)
    (l : ℕ → L) (hd : Dissociated l)
    (F : ℕ → Y → A) (hF : ∀ i, Measurable (F i))
    (v : A → ℂ) (hv : ∀ a, ‖v a‖ ≤ 1)
    (n : ℕ) (hn : 0 < n) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∑ i ∈ Finset.range n, ‖∫ y, v (F i y) * conj (χ (l i) y) ∂η‖) / n ≤
      ε + wordEntropy (η := η) F n / a + Real.exp (a - ε ^ 2 * n / 8) := by
  choose ω hω hw using fun i =>
    exists_aligning_phase (∫ y, v (F i y) * conj (χ (l i) y) ∂η)
  let q (i : ℕ) (y : Y) := ω i * v (F i y) * conj (χ (l i) y)
  have hqm (i : ℕ) : AEStronglyMeasurable (q i) η :=
    ((((measurable_of_finite v).comp (hF i)).aestronglyMeasurable.const_mul (ω i)).mul
      (hχ.measurable (l i)).star)
  have hqb (i : ℕ) : ∀ᵐ y ∂η, ‖q i y‖ ≤ 1 := by
    filter_upwards [hχ.modulus (l i)] with y hy
    simpa only [q, norm_mul, Complex.norm_conj, hy, hω i, one_mul, mul_one] using hv (F i y)
  have hqi (i : ℕ) : Integrable (q i) η :=
    (integrable_const (1 : ℝ)).mono' (hqm i) (hqb i)
  have hqR (i : ℕ) : Integrable (fun y => (q i y).re) η := (hqi i).re
  let S (y : Y) := (∑ i ∈ Finset.range n, (q i y).re) / n
  have hSi : Integrable S η :=
    (integrable_finsetSum _ (fun i _ => hqR i)).div_const _
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hSb : ∀ᵐ y ∂η, S y ≤ 1 := by
    filter_upwards [ae_all_iff.mpr hqb] with y hy
    apply (div_le_iff₀ hn').mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, (1 : ℝ) := Finset.sum_le_sum
        (fun i _ => (Complex.re_le_norm _).trans (hy i))
      _ = 1 * n := by simp
  have hmean : (∫ y, S y ∂η) =
      (∑ i ∈ Finset.range n, ‖∫ y, v (F i y) * conj (χ (l i) y) ∂η‖) / n := by
    rw [integral_div, integral_finsetSum _ (fun i _ => hqR i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change (∫ y, Complex.reCLM (q i y) ∂η) = _
    rw [Complex.reCLM.integral_comp_comm (hqi i)]
    change (∫ y, ω i * v (F i y) * conj (χ (l i) y) ∂η).re = _
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    exact hw i
  rw [← hmean]
  have htail := randomized_dissociated_tail hχ l hd F hF v hv ω (fun i => (hω i).le)
    n hn ha hε hε1
  have hh := integral_le_threshold_add_tail hSi hSb hε.le
  exact hh.trans (by simpa only [add_assoc] using add_le_add_right htail ε)

end

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate
variable {Y L A : Type*} [MeasurableSpace Y] [AddCommGroup L]
    {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem entropy_cancellation (hχ : ProjectiveCharacters η χ)
    (l : ℕ → L) (hd : Dissociated l)
    (F : ℕ → Y → A) (hF : ∀ i, Measurable (F i))
    (v : A → ℂ) (hv : ∀ a, ‖v a‖ ≤ 1)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := η) F n / n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range n, ‖∫ y, v (F i y) * conj (χ (l i) y) ∂η‖) / n)
      atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le (by positivity))
  · intro b hb
    let ε : ℝ := min (b / 2) 1
    have hε : 0 < ε := lt_min (by positivity) zero_lt_one
    have hε1 : ε ≤ 1 := min_le_right _ _
    have hεb : ε ≤ b / 2 := min_le_left _ _
    let c : ℝ := ε ^ 2 / 16
    have hc : 0 < c := by positivity
    have hE : Tendsto (fun n : ℕ => Real.exp (-(c * n))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp ((tendsto_const_mul_atTop_of_pos hc).mpr
          tendsto_natCast_atTop_atTop))
    have hH' : Tendsto (fun n : ℕ => wordEntropy (η := η) F n / (c * n)) atTop (𝓝 0) := by
      simpa only [div_div, mul_comm, zero_div] using hH.div_const c
    have ht := hH'.add hE
    simp only [add_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (show 0 < b / 2 by positivity)),
      eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hh := dissociated_correlation_mean_bound hχ l hd F hF v hv n hn0
      (a := c * n) (mul_pos hc hn') hε hε1
    have he : c * (n : ℝ) - ε ^ 2 * n / 8 = -(c * n) := by dsimp [c]; ring
    rw [he] at hh
    linarith

end

section FactorEntropy
variable {A B : Type*} [Fintype A] [Fintype B]

theorem shannonEntropy_map_le [DecidableEq B] (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (f : A → B) :
    shannonEntropy (fun b => ∑ a, if f a = b then p a else 0) ≤ shannonEntropy p := by
  classical
  let q (b : B) := ∑ a, if f a = b then p a else 0
  have hpq (a : A) : p a ≤ q (f a) := by
    exact (by simpa [q] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun x => if f x = f a then p x else 0)
        (fun x _ => by split_ifs; exact hp x; exact le_rfl) (Finset.mem_univ a)))
  have he (b : B) : -q b * Real.log (q b) =
      ∑ a, if f a = b then -p a * Real.log (q b) else 0 := by
    change -(∑ a, if f a = b then p a else 0) * Real.log (q b) = _
    rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  change (∑ b, -q b * Real.log (q b)) ≤ ∑ a, -p a * Real.log (p a)
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases ha : p a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonpos_left
      (Real.log_le_log ((hp a).lt_of_ne' ha) (hpq a)) (neg_nonpos.mpr (hp a))

end FactorEntropy
section
variable {Y A B : Type*} [MeasurableSpace Y] {η : Measure Y} [IsProbabilityMeasure η]
    [Fintype A] [Fintype B] [MeasurableSpace A] [MeasurableSingletonClass A]

theorem randomEntropy_comp_le (F : Y → A) (hF : Measurable F) (g : A → B) :
    shannonEntropy (fun b => η.real ((g ∘ F) ⁻¹' {b})) ≤
      shannonEntropy (fun a => η.real (F ⁻¹' {a})) := by
  classical
  have he (b : B) : η.real ((g ∘ F) ⁻¹' {b}) =
      ∑ a, if g a = b then η.real (F ⁻¹' {a}) else 0 := by
    rw [← Finset.sum_filter]
    have hh := sum_measureReal_preimage_singleton (μ := η)
      (Finset.univ.filter (fun a => g a = b)) (fun a _ => hF (measurableSet_singleton a))
    rw [hh]
    congr 1
    ext y
    simp
  simp_rw [he]
  exact shannonEntropy_map_le _ (fun _ => measureReal_nonneg) g

theorem wordEntropy_nonneg (F : ℕ → Y → A) (hF : ∀ n, Measurable (F n)) (n : ℕ) :
    0 ≤ wordEntropy (η := η) F n := by
  apply shannonEntropy_nonneg _ (fun _ => measureReal_nonneg)
  have hm : Measurable (entropyWord F n) := Measurable.of_eval (fun _ => hF _)
  have hh := sum_measureReal_preimage_singleton (μ := η) Finset.univ
    (fun w _ => hm (measurableSet_singleton w))
  simpa using hh

theorem wordEntropy_progression_le (F : ℕ → Y → A) (hF : ∀ n, Measurable (F n))
    (p : ℕ) (hp : 0 < p) (j n : ℕ) :
    wordEntropy (η := η) (fun m => F (p * m + j)) n ≤
      wordEntropy (η := η) F (p * n + j) := by
  let select (w : Fin (p * n + j) → A) (i : Fin n) :=
    w ⟨p * i.val + j, Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left i.isLt hp) j⟩
  have hm : Measurable (entropyWord F (p * n + j)) :=
    Measurable.of_eval (fun _ => hF _)
  exact randomEntropy_comp_le (entropyWord F (p * n + j)) hm select

theorem zero_entropy_progression (F : ℕ → Y → A) (hF : ∀ n, Measurable (F n))
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := η) F n / n) atTop (𝓝 0))
    (p : ℕ) (hp : 0 < p) (j : ℕ) :
    Tendsto (fun n : ℕ => wordEntropy (η := η) (fun m => F (p * m + j)) n / n)
      atTop (𝓝 0) := by
  have hM : Tendsto (fun n : ℕ => p * n + j) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ p * n + j
    have hh := Nat.mul_le_mul_right n hp
    omega
  have ht := (hH.comp hM).mul_const ((p + j : ℕ) : ℝ)
  simp only [zero_mul] at ht
  apply squeeze_zero' ?_ ?_ ht
  · exact Eventually.of_forall (fun n => div_nonneg
      (wordEntropy_nonneg _ (fun m => hF (p * m + j)) n) (Nat.cast_nonneg n))
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hM' : (0 : ℝ) < p * n + j := by positivity
    have hMn : (p * n + j : ℝ) ≤ (p + j) * n := by
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ j by positivity)]
    have hpos := wordEntropy_nonneg (η := η) F hF (p * n + j)
    calc
      _ ≤ wordEntropy (η := η) F (p * n + j) / n :=
        div_le_div_of_nonneg_right (wordEntropy_progression_le F hF p hp j n) hn'.le
      _ ≤ wordEntropy (η := η) F (p * n + j) / (p * n + j) * (p + j) := by
        apply (div_le_iff₀ hn').mpr
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
        apply (le_div_iff₀ hM').mpr
        nlinarith [mul_le_mul_of_nonneg_left hMn hpos]
      _ = _ := by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_mul]

end

open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate


open Filter
open scoped BigOperators Topology InnerProductSpace

section

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate

namespace DifferencePolynomial
variable {L : Type*} [AddCommGroup L]

theorem const (l : L) (d : ℕ) : DifferencePolynomial d (fun _ => l) := by
  induction d generalizing l with
  | zero => exact ⟨l, fun _ => rfl⟩
  | succ d ih =>
    intro h _
    simpa only [sub_self] using ih (0 : L)

theorem add {d : ℕ} {P Q : ℕ → L} (hP : DifferencePolynomial d P)
    (hQ : DifferencePolynomial d Q) : DifferencePolynomial d (fun m => P m + Q m) := by
  induction d generalizing P Q with
  | zero =>
    obtain ⟨p, hp⟩ := hP
    obtain ⟨q, hq⟩ := hQ
    exact ⟨p + q, fun m => by simp only [hp, hq]⟩
  | succ d ih =>
    intro h hh
    have hx := ih (hP h hh) (hQ h hh)
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    funext m
    exact add_sub_add_comm _ _ _ _

theorem shift {d : ℕ} {P : ℕ → L} (hP : DifferencePolynomial d P) (s : ℕ) :
    DifferencePolynomial d (fun m => P (m + s)) := by
  induction d generalizing P with
  | zero => obtain ⟨l, hl⟩ := hP; exact ⟨l, fun m => hl (m + s)⟩
  | succ d ih =>
    intro h hh
    have hx := ih (hP h hh)
    convert hx using 1
    all_goals try with_reducible_and_instances rfl
    funext m
    simp only [Nat.add_right_comm]

theorem sum {ι : Type*} (S : Finset ι) {d : ℕ} (P : ι → ℕ → L)
    (hP : ∀ i ∈ S, DifferencePolynomial d (P i)) :
    DifferencePolynomial d (fun m => ∑ i ∈ S, P i m) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using const (0 : L) d
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hP i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)))

theorem of_forward_difference {d : ℕ} {P : ℕ → L}
    (hP : DifferencePolynomial d (fun m => P (m + 1) - P m)) :
    DifferencePolynomial (d + 1) P := by
  intro h hh
  clear hh
  have hs := sum (Finset.range h) (fun i m => P (m + i + 1) - P (m + i))
    (fun i _ => hP.shift i)
  have heq (m : ℕ) : (∑ i ∈ Finset.range h, (P (m + i + 1) - P (m + i))) =
      P (m + h) - P m := by
    clear hs
    induction h with
    | zero => simp
    | succ h ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Nat.add_assoc]
      abel
  simpa only [heq] using hs

end DifferencePolynomial

end

open scoped BigOperators
open Polynomial
section

theorem monic_mahlerMeasure_eq_one (p : ℤ[X]) (hp : p.Monic)
    (hroots : ∀ z ∈ p.aroots ℂ, ‖z‖ ≤ 1) :
    (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  rw [(hp.map _).leadingCoeff, norm_one, one_mul]
  apply Multiset.prod_eq_one
  intro r hr
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hr
  exact max_eq_left (hroots z hz)

theorem integer_polynomial_dvd_cyclotomic_power (p : ℤ[X]) (hp : p.Monic)
    (hzero : ∀ z ∈ p.aroots ℂ, z ≠ 0)
    (hroots : ∀ z ∈ p.aroots ℂ, ‖z‖ ≤ 1) :
    ∃ N d : ℕ, 0 < N ∧ 0 < d ∧ p ∣ (X ^ N - 1) ^ d := by
  classical
  let f := p.map (Int.castRingHom ℂ)
  let s := f.roots.toFinset
  have hmahler := monic_mahlerMeasure_eq_one p hp hroots
  have horders (z : s) : ∃ n : ℕ, 0 < n ∧ (z.val : ℂ) ^ n = 1 := by
    have hz : z.val ∈ p.aroots ℂ := Multiset.mem_toFinset.mp z.property
    exact Polynomial.pow_eq_one_of_mahlerMeasure_eq_one hmahler (hzero _ hz) hz
  choose n hnpos hn using horders
  let N := ∏ z : s, n z
  have hN : 0 < N := Finset.prod_pos (fun _ _ => hnpos _)
  have hpow : ∀ z ∈ f.roots, z ^ N = 1 := by
    intro z hz
    let w : s := ⟨z, Multiset.mem_toFinset.mpr hz⟩
    have hd : n w ∣ N := Finset.dvd_prod_of_mem n (Finset.mem_univ w)
    obtain ⟨a, ha⟩ := hd
    rw [ha, pow_mul, hn w, one_pow]
  let Q : ℂ[X] := X ^ N - 1
  have hQ : Q ≠ 0 := by
    intro hh
    have he := congrArg (eval (0 : ℂ)) hh
    simp [Q, hN.ne'] at he
  have hQroots : ∀ z ∈ f.roots, z ∈ Q.roots := by
    intro z hz
    apply (mem_roots hQ).mpr
    simp [IsRoot.def, Q, hpow z hz]
  let d := f.roots.card + 1
  have hd : 0 < d := Nat.succ_pos _
  have hmult : f.roots ≤ (Q ^ d).roots := by
    rw [roots_pow]
    apply Multiset.le_iff_count.mpr
    intro z
    rw [Multiset.count_nsmul]
    by_cases hz : z ∈ f.roots
    · have hc : 0 < Q.roots.count z := Multiset.count_pos.mpr (hQroots z hz)
      calc
        f.roots.count z ≤ f.roots.card := Multiset.count_le_card _ _
        _ ≤ d := Nat.le_succ _
        _ ≤ d * Q.roots.count z := Nat.le_mul_of_pos_right d hc
    · simp [Multiset.count_eq_zero.mpr hz]
  have hf0 : f ≠ 0 := (hp.map _).ne_zero
  have hdivC : f ∣ Q ^ d :=
    ((IsAlgClosed.splits f).dvd_iff_roots_le_roots hf0 (pow_ne_zero d hQ)).mpr hmult
  refine ⟨N, d, hN, hd, ?_⟩
  apply (Polynomial.map_dvd_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int hp).mp
  simpa [f, Q] using hdivC

theorem quasiUnipotent_of_integer_annihilator {A : Type*} [Ring A] [Algebra ℤ A]
    (a : A) (p : ℤ[X]) (hp : p.Monic) (hann : aeval a p = 0)
    (hzero : ∀ z ∈ p.aroots ℂ, z ≠ 0)
    (hroots : ∀ z ∈ p.aroots ℂ, ‖z‖ ≤ 1) :
    ∃ N d : ℕ, 0 < N ∧ 0 < d ∧ (a ^ N - 1) ^ d = 0 := by
  obtain ⟨N, d, hN, hd, hdiv⟩ := integer_polynomial_dvd_cyclotomic_power p hp hzero hroots
  refine ⟨N, d, hN, hd, ?_⟩
  have hh := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hann
  simpa using hh

section Lattice
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

lemma charpoly_dual (f : M →ₗ[R] M) : f.dualMap.charpoly = f.charpoly := by
  classical
  let b := Module.Free.chooseBasis R M
  have hm : LinearMap.toMatrix b.dualBasis b.dualBasis f.dualMap =
      (LinearMap.toMatrix b b f).transpose := by
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr,
      Matrix.transpose_apply]
  rw [← f.dualMap.charpoly_toMatrix b.dualBasis, hm, Matrix.charpoly_transpose,
    f.charpoly_toMatrix b]

end Lattice

section Torsion
variable {M : Type*} [AddCommGroup M] (G : M ≃ₗ[ℤ] M)

lemma torsionRestrictEquiv_pow (n : ℕ) (x : Submodule.torsion ℤ M) :
    ((torsionRestrictEquiv G ^ n) x : M) = (G ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pow_succ', LinearEquiv.mul_apply]
    change G ((torsionRestrictEquiv G ^ n) x : M) = _
    rw [ih]

lemma torsion_period [Module.Finite ℤ M] :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ Submodule.torsion ℤ M, (G ^ n) x = x := by
  classical
  have : Finite (Submodule.torsion ℤ M) :=
    Module.finite_of_fg_torsion _ (Submodule.torsion_isTorsion)
  have : Finite ((Submodule.torsion ℤ M) ≃ₗ[ℤ] (Submodule.torsion ℤ M)) :=
    Finite.of_injective (fun f => (f : (Submodule.torsion ℤ M) → (Submodule.torsion ℤ M)))
      DFunLike.coe_injective
  let H := torsionRestrictEquiv G
  refine ⟨orderOf H, orderOf_pos H, ?_⟩
  intro x hx
  have hh := congrArg (fun f : (Submodule.torsion ℤ M) ≃ₗ[ℤ]
      (Submodule.torsion ℤ M) => ((f ⟨x, hx⟩ : Submodule.torsion ℤ M) : M))
      (pow_orderOf_eq_one H)
  change ((torsionRestrictEquiv G ^ orderOf H) ⟨x, hx⟩ : M) = x at hh
  rw [torsionRestrictEquiv_pow] at hh
  exact hh

end Torsion

section CyclicLattice
open scoped TensorProduct
variable {M : Type*} [AddCommGroup M] (G : M ≃ₗ[ℤ] M) (l : M)

lemma eigenfunctional_generator_ne_zero
    (hspan : Submodule.span ℤ (Set.range fun n : ℤ => (G ^ n) l) = ⊤)
    (φ : M →+ ℂ) (hφ : φ ≠ 0) (ζ : ℂ) (hζ : ζ ≠ 0)
    (heigen : ∀ x, φ (G x) = ζ * φ x) : φ l ≠ 0 := by
  intro hl
  have horbit (n : ℤ) : φ ((G ^ n) l) = 0 := by
    induction n using Int.induction_on with
    | zero => simpa using hl
    | succ n ih =>
      rw [add_comm (n : ℤ), zpow_add, zpow_one, LinearEquiv.mul_apply, heigen, ih, mul_zero]
    | pred n ih =>
      have heq : G * G ^ (-(n : ℤ) - 1) = G ^ (-(n : ℤ)) := by
        calc
          G * G ^ (-(n : ℤ) - 1) = G ^ (1 : ℤ) * G ^ (-(n : ℤ) - 1) := by rw [zpow_one]
          _ = G ^ (1 + (-(n : ℤ) - 1)) := by rw [zpow_add]
          _ = G ^ (-(n : ℤ)) := by congr 1; omega
      have hh := heigen ((G ^ (-(n : ℤ) - 1)) l)
      rw [← LinearEquiv.mul_apply, heq, ih] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left hζ
  have hker : Submodule.span ℤ (Set.range fun n : ℤ => (G ^ n) l) ≤
      φ.toIntLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact horbit n
  rw [hspan] at hker
  exact hφ (by ext x; exact hker (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ M)))

variable [Module.Free ℤ M] [Module.Finite ℤ M]

theorem lattice_orbit_alternative
    (hspan : Submodule.span ℤ (Set.range fun n : ℤ => (G ^ n) l) = ⊤) :
    (∃ (φ : M →+ ℂ) (ζ : ℂ), φ l ≠ 0 ∧ 1 < ‖ζ‖ ∧
      ∀ x, φ (G x) = ζ * φ x) ∨
    (∃ N d : ℕ, 0 < N ∧ 0 < d ∧ (G.toLinearMap ^ N - 1) ^ d = 0) := by
  classical
  let V := ℂ ⊗[ℤ] M
  let H : V ≃ₗ[ℂ] V := G.baseChange ℤ ℂ M M
  let p := G.toLinearMap.charpoly
  have hp : p.Monic := G.toLinearMap.charpoly_monic
  have hchar : H.toLinearMap.charpoly = p.map (Int.castRingHom ℂ) := by
    exact G.toLinearMap.charpoly_baseChange ℂ
  have hzero : ∀ ζ ∈ p.aroots ℂ, ζ ≠ 0 := by
    intro ζ hζ hz
    have hr : H.toLinearMap.charpoly.IsRoot ζ := by
      rw [hchar]
      exact (Polynomial.mem_roots (hp.map _).ne_zero).mp hζ
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly H.toLinearMap ζ).mpr hr
    obtain ⟨v, hv, hv0⟩ := he.exists_hasEigenvector
    have hh : H v = 0 := by simpa [hz] using Module.End.mem_eigenspace_iff.mp hv
    exact hv0 (H.injective (hh.trans (map_zero H).symm))
  by_cases hex : ∃ ζ ∈ p.aroots ℂ, 1 < ‖ζ‖
  · obtain ⟨ζ, hroot, hζ⟩ := hex
    have hr : H.toLinearMap.dualMap.charpoly.IsRoot ζ := by
      rw [charpoly_dual, hchar]
      exact (Polynomial.mem_roots (hp.map _).ne_zero).mp hroot
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly H.toLinearMap.dualMap ζ).mpr hr
    obtain ⟨F, hF⟩ := he.exists_hasEigenvector
    let φ : M →+ ℂ := F.toAddMonoidHom.comp
      (TensorProduct.mk ℤ ℂ M (1 : ℂ)).toAddMonoidHom
    have hφapply (x : M) : φ x = F ((1 : ℂ) ⊗ₜ[ℤ] x) := rfl
    have hφ0 : φ ≠ 0 := by
      intro hh
      apply hF.2
      apply LinearMap.ext
      intro v
      change F v = 0
      induction v using OAI.tensorInductionOn with
      | tmul a x =>
        have hFx : F ((1 : ℂ) ⊗ₜ[ℤ] x) = 0 := by
          change φ x = 0
          simp only [hh, AddMonoidHom.zero_apply]
        rw [show a ⊗ₜ[ℤ] x = a • ((1 : ℂ) ⊗ₜ[ℤ] x) by
          rw [TensorProduct.smul_tmul']; simp, map_smul, hFx, smul_zero]
      | add v w hv hw => rw [map_add, hv, hw, add_zero]
    have heigen (x : M) : φ (G x) = ζ * φ x := by
      have hh := congrArg (fun f : Module.Dual ℂ V => f ((1 : ℂ) ⊗ₜ[ℤ] x))
        hF.apply_eq_smul
      change F (H ((1 : ℂ) ⊗ₜ[ℤ] x)) = ζ * F ((1 : ℂ) ⊗ₜ[ℤ] x) at hh
      exact hh
    exact Or.inl ⟨φ, ζ, eigenfunctional_generator_ne_zero G l hspan φ hφ0 ζ
      (hzero ζ hroot) heigen, hζ, heigen⟩
  · right
    apply quasiUnipotent_of_integer_annihilator G.toLinearMap p hp
      G.toLinearMap.aeval_self_charpoly hzero
    intro ζ hζ
    exact le_of_not_gt (fun hh => hex ⟨ζ, hζ, hh⟩)

end CyclicLattice

lemma nilpotent_pow_sub_one {A : Type*} [Ring A] [Algebra ℤ A]
    (a : A) (d q : ℕ) (h : (a - 1) ^ d = 0) : (a ^ q - 1) ^ d = 0 := by
  have hdiv : ((X : ℤ[X]) - 1) ^ d ∣ (X ^ q - 1) ^ d :=
    pow_dvd_pow_of_dvd (sub_one_dvd_pow_sub_one X q) d
  have hh := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv
    (show aeval a (((X : ℤ[X]) - 1) ^ d) = 0 by simpa using h)
  simpa using hh

lemma linear_semiconj_pow {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (q : M →ₗ[R] N) (a : Module.End R M) (b : Module.End R N)
    (h : ∀ x, q (a x) = b (q x)) (n : ℕ) (x : M) :
    q ((a ^ n) x) = (b ^ n) (q x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, h, ih]

variable {M : Type*} [AddCommGroup M] (G : M ≃ₗ[ℤ] M)

lemma torsionQuotEquiv_zpow_mk (n : ℤ) (x : M) :
    (torsionQuotEquiv G ^ n) ((Submodule.torsion ℤ M).mkQ x) =
      (Submodule.torsion ℤ M).mkQ ((G ^ n) x) := by
  induction n using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [zpow_add, zpow_one, LinearEquiv.mul_apply]
    exact ih (x := G x)
  | pred n ih =>
    simp only [zpow_sub, zpow_one, LinearEquiv.mul_apply]
    exact ih (x := G.symm x)

lemma torsionQuot_cyclic (l : M)
    (hspan : Submodule.span ℤ (Set.range fun n : ℤ => (G ^ n) l) = ⊤) :
    Submodule.span ℤ (Set.range fun n : ℤ =>
      (torsionQuotEquiv G ^ n) ((Submodule.torsion ℤ M).mkQ l)) = ⊤ := by
  let q := (Submodule.torsion ℤ M).mkQ
  have hrange : (Set.range fun n : ℤ => (torsionQuotEquiv G ^ n) (q l)) =
      q '' (Set.range fun n : ℤ => (G ^ n) l) := by
    rw [← Set.range_comp]
    congr 1
    funext n
    exact torsionQuotEquiv_zpow_mk G n l
  rw [hrange, ← Submodule.map_span, hspan, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

theorem quasiUnipotent_of_torsionQuot [Module.Finite ℤ M] (N d : ℕ)
    (hN : 0 < N) (_hd : 0 < d)
    (hquot : ((torsionQuotEquiv G).toLinearMap ^ N - 1) ^ d = 0) :
    ∃ p e : ℕ, 0 < p ∧ 0 < e ∧ (G.toLinearMap ^ p - 1) ^ e = 0 := by
  obtain ⟨q, hq, hper⟩ := torsion_period G
  let p := N * q
  have hp : 0 < p := Nat.mul_pos hN hq
  have hquot' : ((torsionQuotEquiv G).toLinearMap ^ p - 1) ^ d = 0 := by
    simpa [p, ← pow_mul] using
      nilpotent_pow_sub_one ((torsionQuotEquiv G).toLinearMap ^ N) d q hquot
  have hper' (x : M) (hx : x ∈ Submodule.torsion ℤ M) : (G ^ p) x = x := by
    change (G ^ (N * q)) x = x
    rw [Nat.mul_comm N q, pow_mul]
    have hfix : ∀ n : ℕ, ((G ^ q) ^ n) x = x := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [pow_succ', LinearEquiv.mul_apply, ih, hper x hx]
    exact hfix N
  let π := (Submodule.torsion ℤ M).mkQ
  have hpow (n : ℕ) (x : M) : π ((G.toLinearMap ^ n) x) =
      ((torsionQuotEquiv G).toLinearMap ^ n) (π x) :=
    linear_semiconj_pow π G.toLinearMap (torsionQuotEquiv G).toLinearMap
      (fun _ => rfl) n x
  have hdiff (x : M) : π ((G.toLinearMap ^ p - 1) x) =
      ((torsionQuotEquiv G).toLinearMap ^ p - 1) (π x) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hpow]
  have himage (x : M) : ((G.toLinearMap ^ p - 1) ^ d) x ∈ Submodule.torsion ℤ M := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change π (((G.toLinearMap ^ p - 1) ^ d) x) = 0
    rw [linear_semiconj_pow π _ _ hdiff, hquot', LinearMap.zero_apply]
  refine ⟨p, d + 1, hp, Nat.succ_pos _, ?_⟩
  apply LinearMap.ext
  intro x
  rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply, sub_eq_zero]
  simpa only [Module.End.pow_apply, LinearEquiv.pow_apply, LinearEquiv.coe_coe] using
    hper' (((G.toLinearMap ^ p - 1) ^ d) x) (himage x)

theorem fg_cyclic_orbit_alternative [Module.Finite ℤ M] (l : M)
    (hspan : Submodule.span ℤ (Set.range fun n : ℤ => (G ^ n) l) = ⊤) :
    (∃ (φ : M →+ ℂ) (ζ : ℂ), φ l ≠ 0 ∧ 1 < ‖ζ‖ ∧
      ∀ x, φ (G x) = ζ * φ x) ∨
    (∃ N d : ℕ, 0 < N ∧ 0 < d ∧ (G.toLinearMap ^ N - 1) ^ d = 0) := by
  let π := (Submodule.torsion ℤ M).mkQ
  rcases lattice_orbit_alternative (torsionQuotEquiv G) (π l)
      (torsionQuot_cyclic G l hspan) with h | h
  · obtain ⟨φ, ζ, hφ, hζ, heigen⟩ := h
    exact Or.inl ⟨φ.comp π.toAddMonoidHom, ζ, hφ, hζ, fun x => heigen (π x)⟩
  · obtain ⟨N, d, hN, hd, hnil⟩ := h
    exact Or.inr (quasiUnipotent_of_torsionQuot G N d hN hd hnil)

end

open scoped BigOperators
section
variable {L : Type*} [AddCommGroup L] (G : L ≃ₗ[ℤ] L) (l : L)

lemma mem_initialOrbit {q i : ℕ} (hi : i < q) :
    (G ^ i) l ∈ initialOrbit G l q :=
  Submodule.subset_span ⟨i, hi, rfl⟩

theorem cyclicOrbit_fg_of_boundary (q : ℕ) (hq : 0 < q)
    (hupper : (G ^ q) l ∈ initialOrbit G l q)
    (hlower : G.symm l ∈ initialOrbit G l q) :
    (cyclicOrbit G l).FG := by
  let M := initialOrbit G l q
  have hforward : M ≤ M.comap G.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change G ((G ^ i) l) ∈ M
    rw [← LinearEquiv.mul_apply, ← pow_succ']
    have hle : i + 1 ≤ q := hi
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact mem_initialOrbit G l hlt
    · simpa [heq] using hupper
  have hbackward : M ≤ M.comap G.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change G.symm ((G ^ i) l) ∈ M
    cases i with
    | zero => simpa using hlower
    | succ i =>
      rw [pow_succ', LinearEquiv.mul_apply, G.symm_apply_apply]
      exact mem_initialOrbit G l (Nat.lt_trans (Nat.lt_succ_self i) hi)
  have hzero : l ∈ M := by simpa using mem_initialOrbit G l hq
  have horbit (n : ℤ) : (G ^ n) l ∈ M := by
    induction n using Int.induction_on with
    | zero => simpa using hzero
    | succ n ih =>
      have hh := hforward ih
      change G ((G ^ (n : ℤ)) l) ∈ M at hh
      simpa only [← LinearEquiv.mul_apply, ← zpow_one_add, add_comm] using hh
    | pred n ih =>
      have hh := hbackward ih
      change G.symm ((G ^ (-(n : ℤ))) l) ∈ M at hh
      have heq : G.symm * G ^ (-(n : ℤ)) = G ^ (-(n : ℤ) - 1) := by
        change G⁻¹ * G ^ (-(n : ℤ)) = _
        rw [← zpow_neg_one, ← zpow_add]
        congr 1
        omega
      rw [← LinearEquiv.mul_apply, heq] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
  have hEq : cyclicOrbit G l = M := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact horbit n)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, _, rfl⟩
      exact Submodule.subset_span ⟨(i : ℤ), by simp⟩
  rw [hEq]
  exact Submodule.fg_span ((Set.finite_Iio q).image _)

theorem cyclicOrbit_fg_of_relation (q : ℕ) (hq : 0 < q) (b : ℕ → ℤ)
    (hb0 : b 0 = 1 ∨ b 0 = -1) (hbq : b q = 1 ∨ b q = -1)
    (hrel : ∑ i ∈ Finset.range (q + 1), b i • (G ^ i) l = 0) :
    (cyclicOrbit G l).FG := by
  apply cyclicOrbit_fg_of_boundary G l q hq
  · have hs : (∑ i ∈ Finset.range q, b i • (G ^ i) l) ∈ initialOrbit G l q := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (mem_initialOrbit G l (Finset.mem_range.mp hi))
    rw [Finset.sum_range_succ] at hrel
    have hh : b q • (G ^ q) l ∈ initialOrbit G l q := by
      rw [eq_neg_of_add_eq_zero_right hrel]
      exact Submodule.neg_mem _ hs
    rcases hbq with h | h <;> simpa [h] using hh
  · have hs : (∑ i ∈ Finset.range q, b (i + 1) • (G ^ i) l) ∈
        initialOrbit G l q := by
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (mem_initialOrbit G l (Finset.mem_range.mp hi))
    rw [Finset.sum_range_succ'] at hrel
    have hh := congrArg G.symm hrel
    simp only [map_add, map_sum, map_zsmul, pow_zero,
      pow_succ', LinearEquiv.mul_apply, G.symm_apply_apply, map_zero] at hh
    change (∑ x ∈ Finset.range q, b (x + 1) • (G ^ x) l) + b 0 • G.symm l = 0 at hh
    have hb : b 0 • G.symm l ∈ initialOrbit G l q := by
      rw [eq_neg_of_add_eq_zero_right hh]
      exact Submodule.neg_mem _ hs
    rcases hb0 with h | h <;> simpa [h] using hb

lemma cyclicOrbit_shift (m : ℕ) : cyclicOrbit G ((G ^ m) l) = cyclicOrbit G l := by
  unfold cyclicOrbit
  congr 1
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n + (m : ℤ), ?_⟩
    change (G ^ (n + (m : ℤ))) l = (G ^ n) ((G ^ m) l)
    rw [zpow_add, LinearEquiv.mul_apply, zpow_natCast]
  · rintro ⟨n, rfl⟩
    refine ⟨n - (m : ℤ), ?_⟩
    change (G ^ (n - (m : ℤ))) ((G ^ m) l) = (G ^ n) l
    rw [← zpow_natCast G m, ← LinearEquiv.mul_apply, ← zpow_add, sub_add_cancel]

theorem cyclicOrbit_fg_of_signed_relation (s : Finset ℕ) (hs : s.Nonempty)
    (ε : ℕ → Bool) (hrel : (∑ i ∈ s, if ε i then (G ^ i) l else -((G ^ i) l)) = 0) :
    (cyclicOrbit G l).FG := by
  classical
  let m := s.min' hs
  let M := s.max' hs
  let q := M - m
  let v := (G ^ m) l
  let b : ℕ → ℤ := fun i => if m + i ∈ s then (if ε (m + i) then 1 else -1) else 0
  let f : ℕ → L := fun i => if i ∈ s then (if ε i then (G ^ i) l else -((G ^ i) l)) else 0
  have hm : m ∈ s := Finset.min'_mem s hs
  have hM : M ∈ s := Finset.max'_mem s hs
  have hmM : m ≤ M := Finset.min'_le s M hM
  have hmq : m + q = M := by dsimp [q]; omega
  have hsub : s ⊆ Finset.Ico m (M + 1) := by
    intro i hi
    exact Finset.mem_Ico.mpr ⟨Finset.min'_le s i hi,
      Nat.lt_succ_of_le (Finset.le_max' s i hi)⟩
  have hsum : (∑ i ∈ Finset.Ico m (M + 1), f i) = 0 := by
    rw [← Finset.sum_subset hsub (by intro i _ hi; simp [f, hi])]
    simpa only [f, Finset.sum_congr rfl (fun i hi => ite_eq_left hi)] using hrel
  have hb0 : b 0 = 1 ∨ b 0 = -1 := by simp only [b, Nat.add_zero, ite_eq_left hm]; split <;> simp
  have hbq : b q = 1 ∨ b q = -1 := by simp only [b, hmq, ite_eq_left hM]; split <;> simp
  have hnormalized : (∑ i ∈ Finset.range (q + 1), b i • (G ^ i) v) = 0 := by
    have hcount : M + 1 - m = q + 1 := by dsimp [q]; omega
    rw [Finset.sum_Ico_eq_sum_range, hcount] at hsum
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    dsimp [b, f, v]
    split_ifs with hi hε
    · simp only [one_smul, ← LinearEquiv.mul_apply, ← pow_add, Nat.add_comm]
    · simp only [neg_one_smul, ← LinearEquiv.mul_apply, ← pow_add, Nat.add_comm]
    · simp only [zero_smul]
  have hv : (cyclicOrbit G v).FG := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · have hb : b 0 • v = 0 := by simpa [hq] using hnormalized
      have hv0 : v = 0 := by rcases hb0 with h | h <;> simpa [h] using hb
      simp only [hv0, cyclicOrbit, map_zero, Set.range_const, Submodule.span_singleton_eq_bot.mpr rfl]
      exact Submodule.fg_bot
    · exact cyclicOrbit_fg_of_relation G v q hq b hb0 hbq hnormalized
  simpa only [v, cyclicOrbit_shift] using hv

end

section OrbitGrowth
variable {L : Type*} [AddCommGroup L]

theorem dissociated_of_geometric_functional (l : ℕ → L) (φ : L →+ ℂ)
    (a ζ : ℂ) (ha : a ≠ 0) (hζ : 2 < ‖ζ‖)
    (hφ : ∀ m, φ (l m) = a * ζ ^ m) : Dissociated l := by
  classical
  intro s hs ε heq
  let m := s.max' hs
  have hm : m ∈ s := Finset.max'_mem s hs
  have hrel : (∑ i ∈ s, if ε i then a * ζ ^ i else -(a * ζ ^ i)) = 0 := by
    have hh := congrArg φ heq
    simpa only [map_sum, apply_ite, map_neg, map_zero, hφ] using hh
  have heq' : (if ε m then a * ζ ^ m else -(a * ζ ^ m)) =
      -(∑ i ∈ s.erase m, if ε i then a * ζ ^ i else -(a * ζ ^ i)) := by
    rw [← Finset.sum_erase_add _ _ hm] at hrel
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hrel)
  have hsmall : s.erase m ⊆ Finset.range m := by
    intro i hi
    have his := Finset.mem_of_mem_erase hi
    have hne := (Finset.mem_erase.mp hi).1
    exact Finset.mem_range.mpr (lt_of_le_of_ne (Finset.le_max' s i his) hne)
  have hbound : ‖a‖ * ‖ζ‖ ^ m ≤ ‖a‖ * ∑ i ∈ Finset.range m, ‖ζ‖ ^ i := by
    calc
      _ = ‖if ε m then a * ζ ^ m else -(a * ζ ^ m)‖ := by
        split <;> simp [norm_pow]
      _ = ‖∑ i ∈ s.erase m, if ε i then a * ζ ^ i else -(a * ζ ^ i)‖ := by
        rw [heq', norm_neg]
      _ ≤ ∑ i ∈ s.erase m, ‖if ε i then a * ζ ^ i else -(a * ζ ^ i)‖ := norm_sum_le _ _
      _ = ∑ i ∈ s.erase m, ‖a‖ * ‖ζ‖ ^ i := by
        apply Finset.sum_congr rfl
        intro i _
        split <;> simp [norm_pow]
      _ ≤ ∑ i ∈ Finset.range m, ‖a‖ * ‖ζ‖ ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsmall (fun _ _ _ => by positivity)
      _ = _ := by rw [Finset.mul_sum]
  have hsum : (∑ i ∈ Finset.range m, ‖ζ‖ ^ i) < ‖ζ‖ ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hp : 0 < ‖ζ‖ ^ m := pow_pos (lt_trans (by norm_num) hζ) m
      nlinarith
  have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
  exact (not_lt_of_ge hbound) (mul_lt_mul_of_pos_left hsum ha')

theorem dissociated_progressions_of_eigenfunctional (G : L → L) (l : L)
    (φ : L →+ ℂ) (ζ : ℂ) (hl : φ l ≠ 0) (hζ : 1 < ‖ζ‖)
    (heigen : ∀ v, φ (G v) = ζ * φ v) :
    ∃ p : ℕ, 0 < p ∧ ∀ j : ℕ,
      Dissociated (fun m => G^[p * m + j] l) := by
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt (2 : ℝ) hζ
  have hp0 : 0 < p := by
    by_contra hh
    have : p = 0 := Nat.eq_zero_of_not_pos hh
    simp [this] at hp
  have hφ (n : ℕ) : φ (G^[n] l) = φ l * ζ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', heigen, ih, pow_succ]
      ring
  refine ⟨p, hp0, fun j => ?_⟩
  apply dissociated_of_geometric_functional _ φ (φ l * ζ ^ j) (ζ ^ p)
  · exact mul_ne_zero hl (pow_ne_zero _ (by intro hh; norm_num [hh] at hζ))
  · simpa only [norm_pow] using hp
  · intro m
    rw [hφ, pow_add, pow_mul]
    ring


theorem differencePolynomial_of_nilpotent_difference (G : Module.End ℤ L)
    (d : ℕ) (l : L) (h : ((G - 1) ^ (d + 1)) l = 0) :
    DifferencePolynomial d (fun m => (G ^ m) l) := by
  induction d generalizing l with
  | zero =>
    have hl : G l = l := by
      simpa only [zero_add, pow_one, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] using h
    refine ⟨l, ?_⟩
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simpa only [pow_succ, Module.End.mul_apply, hl] using ih
  | succ d ih =>
    apply DifferencePolynomial.of_forward_difference
    have hn : ((G - 1) ^ (d + 1)) ((G - 1) l) = 0 := by
      simpa only [pow_succ, Module.End.mul_apply] using h
    have hp := ih ((G - 1) l) hn
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext m
    simp only [pow_succ, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub]

theorem polynomial_progressions_of_nilpotent (G : Module.End ℤ L)
    (p d : ℕ) (h : (G ^ p - 1) ^ (d + 1) = 0) (l : L) (j : ℕ) :
    DifferencePolynomial d (fun m => (G ^ (p * m + j)) l) := by
  have hn : ((G ^ p - 1) ^ (d + 1)) ((G ^ j) l) = 0 := by rw [h]; rfl
  have hp := differencePolynomial_of_nilpotent_difference (G ^ p) d ((G ^ j) l) hn
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  funext m
  rw [pow_add, pow_mul, Module.End.mul_apply]

end OrbitGrowth

section
variable {L : Type*} [AddCommGroup L] (G : L ≃ₗ[ℤ] L) (l : L)

lemma cyclicOrbitEquiv_zpow_coe (n : ℤ) (x : cyclicOrbit G l) :
    ((cyclicOrbitEquiv G l ^ n) x : L) = (G ^ n) x := by
  induction n using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [zpow_add, zpow_one, LinearEquiv.mul_apply]
    exact ih (cyclicOrbitEquiv G l x)
  | pred n ih =>
    simp only [zpow_sub, zpow_one, LinearEquiv.mul_apply]
    exact ih ((cyclicOrbitEquiv G l).symm x)

lemma cyclicOrbitEquiv_pow_coe (n : ℕ) (x : cyclicOrbit G l) :
    ((cyclicOrbitEquiv G l ^ n) x : L) = (G ^ n) x := by
  simpa only [zpow_natCast] using cyclicOrbitEquiv_zpow_coe G l (n : ℤ) x

lemma cyclicGenerator_spans : Submodule.span ℤ (Set.range fun n : ℤ =>
    (cyclicOrbitEquiv G l ^ n) (cyclicGenerator G l)) = ⊤ := by
  apply (Submodule.span_val_image_eq_iff (cyclicOrbit G l) _).mp
  rw [← Set.range_comp]
  have heq : (Subtype.val ∘ fun n : ℤ =>
      (cyclicOrbitEquiv G l ^ n) (cyclicGenerator G l)) = fun n : ℤ => (G ^ n) l := by
    funext n
    exact cyclicOrbitEquiv_zpow_coe G l n (cyclicGenerator G l)
  rw [heq]
  rfl

lemma Dissociated.of_injective_map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (hf : Function.Injective f) (a : ℕ → A)
    (h : Dissociated a) : Dissociated (fun n => f (a n)) := by
  intro s hs ε hzero
  apply h s hs ε
  apply hf
  rw [map_zero, map_sum]
  convert hzero using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp only [map_neg]

theorem orbit_alternatives :
    Dissociated (fun r : ℕ => (G ^ r) l) ∨
    (∃ p : ℕ, 0 < p ∧ ∀ j : ℕ, Dissociated (fun m => (G ^ (p * m + j)) l)) ∨
    (∃ p d : ℕ, 0 < p ∧ 0 < d ∧
      ((cyclicOrbitEquiv G l).toLinearMap ^ p - 1) ^ d = 0) := by
  classical
  by_cases hdiss : Dissociated (fun r : ℕ => (G ^ r) l)
  · exact Or.inl hdiss
  · right
    simp only [Dissociated, not_forall, exists_prop, not_ne_iff] at hdiss
    obtain ⟨s, hs, ε, hrel⟩ := hdiss
    have hfg := cyclicOrbit_fg_of_signed_relation G l s hs ε hrel
    have : Module.Finite ℤ (cyclicOrbit G l) := Module.Finite.of_fg hfg
    rcases fg_cyclic_orbit_alternative (cyclicOrbitEquiv G l) (cyclicGenerator G l)
        (cyclicGenerator_spans G l) with h | h
    · obtain ⟨φ, ζ, hφ, hζ, heigen⟩ := h
      obtain ⟨p, hp, hd⟩ := dissociated_progressions_of_eigenfunctional
        (cyclicOrbitEquiv G l) (cyclicGenerator G l) φ ζ hφ hζ heigen
      refine Or.inl ⟨p, hp, fun j => ?_⟩
      have hh := Dissociated.of_injective_map (cyclicOrbit G l).subtype.toAddMonoidHom
        (cyclicOrbit G l).injective_subtype _ (hd j)
      have heq (n : ℕ) : (((cyclicOrbitEquiv G l)^[n]) (cyclicGenerator G l) : L) =
          (G ^ n) l := by
        rw [← LinearEquiv.pow_apply]
        exact cyclicOrbitEquiv_pow_coe G l n (cyclicGenerator G l)
      change Dissociated (fun n => (((cyclicOrbitEquiv G l)^[p * n + j])
        (cyclicGenerator G l) : L)) at hh
      simpa only [heq] using hh
    · exact Or.inr h

end

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

theorem cesaro_zero_of_progressions (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (p : ℕ) (hp : 0 < p)
    (h : ∀ j < p, Tendsto (fun N : ℕ =>
      (∑ m ∈ Finset.range N, a (p * m + j)) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N, a m) / N) atTop (𝓝 0) := by
  have hblock (N : ℕ) : (∑ m ∈ Finset.range (p * N), a m) =
      ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range p, a (p * m + j) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
  have hsum := tendsto_finsetSum (Finset.range p) (fun j hj => h j (Finset.mem_range.mp hj))
  simp only [Finset.sum_const_zero] at hsum
  apply squeeze_zero (fun N => div_nonneg
    (Finset.sum_nonneg (fun m _ => ha m)) (Nat.cast_nonneg N)) (fun N => ?_) hsum
  rw [← Finset.sum_div, Finset.sum_comm, ← hblock]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by simpa using Nat.mul_le_mul_right N hp))
    (fun m _ _ => ha m)

namespace DifferencePolynomial

theorem map {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) {d : ℕ} {P : ℕ → A} (h : DifferencePolynomial d P) :
    DifferencePolynomial d (fun m => f (P m)) := by
  induction d generalizing P with
  | zero => obtain ⟨l, hl⟩ := h; exact ⟨f l, fun m => congrArg f (hl m)⟩
  | succ d ih =>
    intro s hs
    simpa only [map_sub] using ih (h s hs)
end DifferencePolynomial

theorem wordEntropy_comp {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {μ : Measure X} [IsProbabilityMeasure μ] {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (F : ℕ → X → A) (hF : ∀ m, Measurable (F m)) (n : ℕ) :
    wordEntropy (η := η) (fun m y => F m (x y)) n = wordEntropy (η := μ) F n := by
  unfold wordEntropy shannonEntropy
  apply Finset.sum_congr rfl
  intro w _
  have he : η.real (entropyWord (fun m y => F m (x y)) n ⁻¹' {w}) =
      μ.real (entropyWord F n ⁻¹' {w}) := hx.measureReal_preimage
    ((Measurable.of_eval (fun _ => hF _)) (measurableSet_singleton w)).nullMeasurableSet
  dsimp only
  rw [he]


theorem orbit_cancellation_unit
    {X Y L A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ a b z, t (a + b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (a : X → A) (ha : Measurable a) (v : A → ℂ) (hv : ∀ b, ‖v b‖ ≤ 1)
    (hcenter : ∫ z, v (a z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => a (t m z)) n / n)
      atTop (𝓝 0))
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)
    (G : L ≃ₗ[ℤ] L) (l : L) :
    Tendsto (fun N : ℕ => (∑ m ∈ Finset.range N,
      ‖∫ y, v (a (t m (x y))) * conj (χ ((G ^ m) l) y) ∂η‖) / N)
      atTop (𝓝 0) := by
  have haw (m : ℕ) : Measurable (fun y => a (t m (x y))) :=
    ha.comp ((ht m).measurable.comp hx.measurable)
  have hHy : Tendsto (fun n : ℕ =>
      wordEntropy (η := η) (fun m y => a (t m (x y))) n / n) atTop (𝓝 0) := by
    have he (n : ℕ) := wordEntropy_comp x hx (fun m z => a (t m z))
      (fun m => ha.comp (ht m).measurable) n
    simpa only [he] using hH
  rcases orbit_alternatives G l with hd | ⟨p, hp, hd⟩ | ⟨p, d, hp, hd, hn⟩
  · exact entropy_cancellation hχ _ hd _ haw v hv hHy
  · apply cesaro_zero_of_progressions _ (fun _ => norm_nonneg _) p hp
    intro j _
    exact entropy_cancellation hχ _ (hd j) _ (fun m => haw (p * m + j)) v hv
      (zero_entropy_progression _ haw hHy p hp j)
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    have hpm : Tendsto (fun m : ℕ => p * m) atTop atTop :=
      tendsto_atTop_mono (fun m => by simpa using Nat.mul_le_mul_right m hp) tendsto_id
    apply cesaro_zero_of_progressions _ (fun _ => norm_nonneg _) p hp
    intro j _
    have hpoly := polynomial_progressions_of_nilpotent
      (cyclicOrbitEquiv G l).toLinearMap p d hn (cyclicGenerator G l) j
    have hmap := hpoly.map (cyclicOrbit G l).subtype.toAddMonoidHom
    have heq (m : ℕ) : ((cyclicOrbitEquiv G l).toLinearMap ^ m) (cyclicGenerator G l) =
        (cyclicOrbitEquiv G l ^ m) (cyclicGenerator G l) := by
      rw [Module.End.pow_apply, LinearEquiv.coe_coe, ← LinearEquiv.pow_apply]
    have hpolyl : DifferencePolynomial d (fun m => (G ^ (p * m + j)) l) := by
      convert hmap using 1
      all_goals try with_reducible_and_instances rfl
      funext m
      change (G ^ (p * m + j)) l =
        (((cyclicOrbitEquiv G l).toLinearMap ^ (p * m + j)) (cyclicGenerator G l) : L)
      rw [heq, cyclicOrbitEquiv_pow_coe]
      rfl
    have hfm : AEStronglyMeasurable (fun z => v (a z)) μ :=
      ((measurable_of_finite v).comp ha).aestronglyMeasurable
    have hfmj := hfm.comp_measurePreserving (ht j)
    have hfj0 : ∫ z, v (a (t j z)) ∂μ = 0 := by
      have hh := integral_map (μ := μ) (f := fun z => v (a z))
        (ht j).measurable.aemeasurable (by rw [(ht j).map_eq]; exact hfm)
      simpa only [(ht j).map_eq, hcenter] using hh.symm
    have hc := polynomial_cancellation x hx (fun m => t (p * m)) (fun m => ht (p * m)) hχ
      (fun b c z => by rw [Nat.mul_add, htadd])
      (fun A B hA hB => (hmix A B hA hB).comp hpm) d _ hpolyl hfmj zero_le_one
      (Eventually.of_forall (fun z => hv (a (t j z)))) hfj0
    simpa only [Function.comp_apply, htadd, div_eq_mul_inv, mul_comm] using hc

end

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

theorem orbit_cancellation
    {X Y L A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ a b z, t (a + b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (a : X → A) (ha : Measurable a) (v : A → ℂ)
    (hcenter : ∫ z, v (a z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => a (t m z)) n / n)
      atTop (𝓝 0))
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)
    (G : L ≃ₗ[ℤ] L) (l : L) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
      ‖∫ y, v (a (t m (x y))) * conj (χ ((G ^ m) l) y) ∂η‖)
      atTop (𝓝 0) := by
  let C : ℝ := (∑ b, ‖v b‖) + 1
  have hC : 0 < C := by
    have : 0 ≤ ∑ b, ‖v b‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp only [C]
    linarith
  have hCn : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  let w (b : A) : ℂ := (C : ℂ)⁻¹ * v b
  have hw (b : A) : ‖w b‖ ≤ 1 := by
    have hb := Finset.single_le_sum (fun b _ => norm_nonneg (v b)) (Finset.mem_univ b)
    change ‖(C : ℂ)⁻¹ * v b‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hC.le, mul_comm,
      ← div_eq_mul_inv, div_le_one hC]
    dsimp only [C]
    linarith
  have hw0 : ∫ z, w (a z) ∂μ = 0 := by
    simp only [w, integral_const_mul, hcenter, mul_zero]
  have hlim := orbit_cancellation_unit x hx t ht htadd hmix a ha w hw hw0 hH hχ G l
  have he (b : A) : v b = (C : ℂ) * w b := by simp [w, hCn]
  have hecor (m : ℕ) : ‖∫ y, v (a (t m (x y))) * conj (χ ((G ^ m) l) y) ∂η‖ =
      C * ‖∫ y, w (a (t m (x y))) * conj (χ ((G ^ m) l) y) ∂η‖ := by
    simp_rw [he, mul_assoc, integral_const_mul]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC.le]
  have hh := hlim.const_mul C
  simp only [mul_zero] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  simp only [hecor, ← Finset.mul_sum, div_eq_mul_inv]
  ring


end Rokhlin

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_OrbitCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {U Y C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]
    (S : Set (U × HilbertCode κ))

lemma localGroupCode_equiv (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (q : {q // (a,q) ∈ S}) : localGroupCode κ S a (e q) = q.val := by
  have h : ∃ r, (a,r) ∈ S ∧ HilbertCode.projective a r = (e q).val := ⟨q.val,q.property,(he q).symm⟩
  rw [localGroupCode,dite_eq_left h]
  have hh := h.choose_spec
  have heq : e ⟨h.choose,hh.1⟩ = e q := Subtype.ext ((he _).trans hh.2)
  exact congrArg Subtype.val (e.injective heq)

lemma localGroupBlock_equiv (ψ : U × HilbertCode κ → C) (a : U)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (q : {q // (a,q) ∈ S}) : localGroupBlock κ S ψ a (e q) = ψ (a,q.val) := by
  unfold localGroupBlock
  rw [localGroupCode_equiv κ S a e he q]

end

section
open MeasureTheory Set
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
attribute [local instance] Classical.propDecidable
variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)

lemma projectiveRep_class (g : ProjectiveCircle μ) :
    projectiveCircle μ (projectiveRep μ g) (measurableCircle_measurable Y _) = g := by
  by_cases hg : g = 1
  · subst g
    simp only [projectiveRep]
    exact projectiveCircle_one μ
  · rw [projectiveRep,ite_eq_right hg]
    exact Quotient.out_eq g

end

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] (κ : Kernel U Y) [IsMarkovKernel κ]

omit [MeasurableSpace.CountablyGenerated Y] in
lemma norm_integral_mul_conj_of_phase {μ : Measure Y} (f g h : Y → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (he : g =ᵐ[μ] fun y => c * h y) :
    ‖∫ y, f y * conj (g y) ∂μ‖ = ‖∫ y, f y * conj (h y) ∂μ‖ := by
  have ht : (fun y => f y * conj (g y)) =ᵐ[μ]
      fun y => conj c * (f y * conj (h y)) := he.mono fun y hy => by
    dsimp only at hy ⊢
    rw [hy,map_mul]; ring
  rw [integral_congr_ae ht,integral_const_mul,norm_mul,Complex.norm_conj,hc,one_mul]

lemma absoluteCoefficient_projective (f : Y → ℂ) (a : U) (q : HilbertCode κ) :
    absoluteCoefficient κ f (a,q) =
      ‖∫ y, f y * conj (projectiveCharacter (κ a) (HilbertCode.projective a q) y) ∂κ a‖ := by
  have he : projectiveCircle (κ a) (HilbertCode.circleRep q)
      (HilbertCode.measurable_circleRep_fixed q) =
      projectiveCircle (κ a) (projectiveRep (κ a) (HilbertCode.projective a q))
        (measurableCircle_measurable Y _) := by
    rw [projectiveRep_class]
    rfl
  obtain ⟨c,hc⟩ := (projectiveCircle_eq_iff _ _ _ _ _).mp he
  apply norm_integral_mul_conj_of_phase _ _ _ (c : ℂ) (Circle.norm_coe c)
  filter_upwards [hc] with y hy
  exact congrArg (fun z : Circle => (z : ℂ)) hy
end

namespace BorelFibreEnumeration
open MeasureTheory Set
open scoped BigOperators

section
attribute [local instance] Classical.propDecidable
variable {U Z W : Type*} [MeasurableSpace U] [MeasurableSpace Z] [MeasurableSpace W]
variable {S : Set (U × Z)} (E : BorelFibreEnumeration S)

lemma fibreSum_eq_tsum (F : U × Z → ℝ) (a : U) :
    E.fibreSum F a = ∑' z : {z : Z // (a,z) ∈ S}, F (a,z.val) := by
  rw [fibreSum,←(E.sumFibreEquiv a).tsum_eq]
  exact (tsum_subtype {n | a ∈ E.domain n} (fun n => F (a,E.section_ n a))).symm

lemma fibreSum_eq_sum_equiv {K : Type*} [Fintype K] (a : U)
    (e : K ≃ {z : Z // (a,z) ∈ S}) (F : U × Z → ℝ) :
    E.fibreSum F a = ∑ k, F (a,(e k).val) := by
  rw [E.fibreSum_eq_tsum,←e.tsum_eq,tsum_fintype]

end

end BorelFibreEnumeration

section
open MeasureTheory Set
variable {U Z C H : Type*} [MeasurableSpace U] [MeasurableSpace Z]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    {S : Set (U × Z)} (E : BorelFibreEnumeration S)
    (ψ : U × Z → C) (hψ : Measurable ψ) (D : C ≃ C)
    (τ : H → C) (G : H ≃ H)
    (hG : ∀ h, τ (G h) = D.symm (τ h))

include hG in
lemma movingBlock_sum (a : U) (e : H ≃ {z // (a,z) ∈ S})
    (he : ∀ l, ψ (a,(e l).val) = τ l) (b : C)
    (hb : {l | τ l = b}.Finite) (n : ℕ) (F : U × Z → ℝ) :
    (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum F a =
      ∑ l ∈ hb.toFinset, F (a,(e ((G^[n]) l)).val) := by
  classical
  let : Fintype {l : H // τ l = b} := hb.fintype
  rw [(E.restrictLevel ψ hψ _).fibreSum_eq_sum_equiv a
    (movingBlockCodeEquiv ψ D τ G hG a e he b n) F]
  change (∑ k : {l : H // τ l = b}, F (a,(e ((G^[n]) k.val)).val)) = _
  exact (Finset.sum_subtype hb.toFinset (fun l => hb.mem_toFinset (a := l))
    (fun l => F (a,(e ((G^[n]) l)).val))).symm
end

namespace ProjectiveCharacters
open MeasureTheory
variable {Y L K : Type*} [MeasurableSpace Y] [AddCommGroup L] [AddCommGroup K]
    {η : Measure Y} {χ : L → Y → ℂ}
lemma reindex (hχ : ProjectiveCharacters η χ) (e : K ≃+ L) :
    ProjectiveCharacters η (fun k => χ (e k)) where
  measurable k := hχ.measurable _
  modulus k := hχ.modulus _
  zero := by simpa only [map_zero] using hχ.zero
  mul k l := by simpa only [map_add] using hχ.mul (e k) (e l)
  mean k hk := hχ.mean (e k) (by intro h; exact hk (e.injective (h.trans (map_zero e).symm)))
end ProjectiveCharacters

section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ComplexConjugate
variable {X Y L A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [AddCommGroup L]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {μ : Measure X} [IsProbabilityMeasure μ]
    {η : Measure Y} [IsProbabilityMeasure η]
    (x : Y → X) (hx : MeasurePreserving x η μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ a b z, t (a+b) z = t b (t a z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (a : X → A) (ha : Measurable a) (v : A → ℂ)
    (hcenter : ∫ z, v (a z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => a (t m z)) n / n)
      atTop (𝓝 0))
    {χ : L → Y → ℂ} (hχ : ProjectiveCharacters η χ)
    (G : L ≃ₗ[ℤ] L)

include hx ht htadd hmix ha hcenter hH hχ in
lemma finite_block_cancellation (B : Finset L) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ m ∈ Finset.range N,
      ∑ l ∈ B, ‖∫ y, v (a (t m (x y))) * conj (χ ((G ^ m) l) y) ∂η‖)
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum B (fun l _ =>
    orbit_cancellation x hx t ht htadd hmix a ha v hcenter hH hχ G l)
  simp only [Finset.sum_const_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext N
  rw [←Finset.mul_sum,Finset.sum_comm]

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ComplexConjugate
variable {U Y X A C : Type*} [MeasurableSpace U] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y] [MeasurableSpace X]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace C] [MeasurableSingletonClass C]
    (κ : Kernel U Y) [IsMarkovKernel κ] (S : Set (U × HilbertCode κ))
    (E : BorelFibreEnumeration S) (ψ : U × HilbertCode κ → C) (hψ : Measurable ψ)
    (D : C ≃ C) (a₀ a : U) (b : C)
    (hb : {g : localProjectiveGroup κ S a₀ | localGroupBlock κ S ψ a₀ g = b}.Finite)
    (G : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a₀)
    (hG : ∀ g, localGroupBlock κ S ψ a₀ (G g) = D.symm (localGroupBlock κ S ψ a₀ g))
    (J : localProjectiveGroup κ S a₀ ≃* localProjectiveGroup κ S a)
    (hJ : ∀ g, localGroupBlock κ S ψ a (J g) = localGroupBlock κ S ψ a₀ g)
    (e : {q // (a,q) ∈ S} ≃ localProjectiveGroup κ S a)
    (he : ∀ q, (e q).val = HilbertCode.projective a q.val)
    (hχ : ProjectiveCharacters (κ a)
      (fun g : Additive (localProjectiveGroup κ S a) => projectiveCharacter (κ a) g.toMul.val))
    {μ : Measure X} [IsProbabilityMeasure μ]
    (x : Y → X) (hx : MeasurePreserving x (κ a) μ)
    (t : ℕ → X → X) (ht : ∀ m, MeasurePreserving (t m) μ μ)
    (htadd : ∀ c d z, t (c+d) z = t d (t c z))
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun m => μ (A ∩ t m ⁻¹' B)) atTop (𝓝 (μ A * μ B)))
    (α : X → A) (hα : Measurable α) (v : A → ℂ)
    (hcenter : ∫ z, v (α z) ∂μ = 0)
    (hH : Tendsto (fun n : ℕ => wordEntropy (η := μ) (fun m z => α (t m z)) n / n)
      atTop (𝓝 0))
    (R : Y → Y) (f : Y → ℂ) (hf : ∀ n y, f ((R^[n]) y) = v (α (t n (x y))))
include hb hG hJ he hχ hx ht htadd hmix hα hcenter hH hf in
lemma local_moving_cancellation_oai :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum
        (absoluteCoefficient κ (f ∘ R^[n])) a) atTop (𝓝 0) := by
  classical
  let H := Additive (localProjectiveGroup κ S a₀)
  let G' : H ≃ₗ[ℤ] H := G.toAdditive.toIntLinearEquiv
  let τ : H → C := fun g => localGroupBlock κ S ψ a₀ g.toMul
  have hb' : {g : H | τ g = b}.Finite := hb
  let e' : H ≃ {q // (a,q) ∈ S} :=
    { toFun := fun g => e.symm (J g.toMul)
      invFun := fun q => Additive.ofMul (J.symm (e q))
      left_inv := by intro g; simp
      right_inv := by intro q; simp }
  have he' (g : H) : ψ (a,(e' g).val) = τ g := by
    dsimp only [e',Equiv.coe_fn_mk]
    rw [←localGroupBlock_equiv κ S ψ a e he,e.apply_symm_apply,hJ]
  have hG' (g : H) : τ (G'.toEquiv g) = D.symm (τ g) := hG _
  have hs (n : ℕ) :
      (E.restrictLevel ψ hψ ((D.symm^[n]) b)).fibreSum
        (absoluteCoefficient κ (f ∘ R^[n])) a =
      ∑ l ∈ hb'.toFinset, ‖∫ y, v (α (t n (x y))) *
        conj (projectiveCharacter (κ a) (J ((G'^n) l).toMul).val y) ∂κ a‖ := by
    rw [movingBlock_sum E ψ hψ D τ G'.toEquiv hG' a e' he' b hb' n]
    apply Finset.sum_congr rfl
    intro l hl
    rw [absoluteCoefficient_projective]
    have hq : HilbertCode.projective a (e' ((G'.toEquiv^[n]) l)).val =
        (J ((G'^n) l).toMul).val := by
      rw [←he]
      dsimp only [e',Equiv.coe_fn_mk]
      rw [e.apply_symm_apply]
      rw [LinearEquiv.coe_pow]
      rfl
    rw [hq]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      dsimp only [Function.comp_apply]
      rw [hf]
  have hc := finite_block_cancellation x hx t ht htadd hmix α hα v hcenter hH
    (hχ.reindex J.toAdditive) G' hb'.toFinset
  simp only [hs]
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  rfl
end

end Rokhlin

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Rokhlin.local_moving_cancellation_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Rokhlin.local_moving_cancellation_oai.{u_1, u_2, u_3, u_4, u_5}
