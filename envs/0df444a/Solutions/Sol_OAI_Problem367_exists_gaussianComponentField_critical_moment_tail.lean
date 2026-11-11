-- Prove2me | solution 1 for OAI.Problem367.exists_gaussianComponentField_critical_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:44:56.373914+00:00
-- url     : https://prove2.me/submissions/3776ebfb-2593-4674-8f91-72607ebcbbe0

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_gaussianComponentField_critical_base_moments
import Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_gaussian_component_field_recursion

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_IndependentMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem integrable_prod_comp_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i))
    (f : ι → ℝ → ℝ) (hmf : ∀ i, Measurable (f i))
    (hf : ∀ i, Integrable (fun ω => f i (X i ω)) μ) :
    Integrable (fun ω => ∏ i, f i (X i ω)) μ := by
  have hfi : ∀ i, Integrable (f i) (μ.map (X i)) := by
    intro i
    exact (integrable_map_measure (hmf i).aestronglyMeasurable (hmX i).aemeasurable).mpr (hf i)
  have hi := Integrable.fintype_prod hfi
  have hmap := hX.map_fun_eq_pi_map (fun i => (hmX i).aemeasurable)
  have hm : Measurable (fun x : ι → ℝ => ∏ i, f i (x i)) := by
    exact Finset.measurable_prod _ (fun i _ => (hmf i).comp (measurable_pi_apply i))
  have hmarray : Measurable (fun ω i => X i ω) := Measurable.of_eval hmX
  have hi' : Integrable (fun x : ι → ℝ => ∏ i, f i (x i))
      (μ.map (fun ω i => X i ω)) := by rw [hmap]; exact hi
  exact (integrable_map_measure hm.aestronglyMeasurable hmarray.aemeasurable).mp hi'

theorem integrable_sum_pow_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i)) (p : ℕ)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => X i ω ^ k) μ) :
    Integrable (fun ω => (∑ i, X i ω) ^ p) μ := by
  classical
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  apply integrable_finsetSum
  intro r hr
  apply Integrable.const_mul
  apply integrable_prod_comp_of_iIndepFun hX hmX (fun i x => x ^ r i)
    (fun i => measurable_id.pow_const (r i))
  intro i
  apply hMom
  have hrsum := (Finset.mem_piAntidiag.mp hr).1
  have hri := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (r j))
    (Finset.mem_univ i)
  simpa [hrsum] using hri

theorem integral_sum_pow_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i)) (p : ℕ)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => X i ω ^ k) μ) :
    (∫ ω, (∑ i, X i ω) ^ p ∂μ) =
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
        (Nat.multinomial Finset.univ r : ℝ) * ∏ i, ∫ ω, X i ω ^ r i ∂μ := by
  classical
  have hprod : ∀ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
      Integrable (fun ω => ∏ i, X i ω ^ r i) μ := by
    intro r hr
    apply integrable_prod_comp_of_iIndepFun hX hmX (fun i x => x ^ r i)
      (fun i => measurable_id.pow_const (r i))
    intro i
    apply hMom
    have hrsum := (Finset.mem_piAntidiag.mp hr).1
    have hri := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (r j))
      (Finset.mem_univ i)
    simpa [hrsum] using hri
  simp_rw [Finset.sum_pow_eq_sum_piAntidiag]
  rw [integral_finsetSum _ (fun r hr => (hprod r hr).const_mul _)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_const_mul]
  congr 1
  exact hX.integral_fun_prod_comp (fun i => (hmX i).aemeasurable)
    (fun i => (measurable_id.pow_const (r i)).aestronglyMeasurable)

theorem integral_abs_sum_pow_le_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i)) (p : ℕ)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => |X i ω| ^ k) μ) :
    (∫ ω, |∑ i, X i ω| ^ p ∂μ) ≤
      ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
        (Nat.multinomial Finset.univ r : ℝ) * ∏ i, ∫ ω, |X i ω| ^ r i ∂μ := by
  have hAbs : iIndepFun (fun i ω => |X i ω|) μ :=
    hX.comp (fun _ x => |x|) (fun _ => measurable_abs)
  have hi := integrable_sum_pow_of_iIndepFun hAbs (fun i => (hmX i).abs) p hMom
  calc
    (∫ ω, |∑ i, X i ω| ^ p ∂μ) ≤ (∫ ω, (∑ i, |X i ω|) ^ p ∂μ) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg _) _)) hi
      exact Filter.Eventually.of_forall fun ω =>
        pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) p
    _ = _ := integral_sum_pow_of_iIndepFun hAbs (fun i => (hmX i).abs) p hMom

theorem piAntidiag_pure_filter_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} :
    (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
        (fun r => ∃ i, r i = p) =
      Finset.univ.image (fun i : ι => Pi.single i p) := by
  classical
  ext r
  constructor
  · intro hr
    obtain ⟨hr, i, hi⟩ := Finset.mem_filter.mp hr
    have hsum := (Finset.mem_piAntidiag.mp hr).1
    have hrest : ∑ j ∈ Finset.univ.erase i, r j = 0 := by
      have hh := Finset.sum_erase_add Finset.univ r (Finset.mem_univ i)
      rw [hi, hsum] at hh
      omega
    have heq : r = Pi.single i p := by
      funext j
      by_cases hji : j = i
      · subst j; simpa only [Pi.single_eq_same] using hi
      · have hj := Finset.sum_eq_zero_iff.mp hrest j
          (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
        simpa [Pi.single_apply, hji] using hj
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩
  · intro hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_piAntidiag.mpr
      constructor
      · simp [Finset.sum_pi_single']
      · intro j _; exact Finset.mem_univ j
    · exact ⟨i, by simp⟩

theorem multinomial_sum_eq_pure_add_mixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ℕ → ℝ) (hzero : ∀ i, M i 0 = 1)
    {p : ℕ} (hp : 0 < p) :
    (∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
      (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i)) =
      (∑ i, M i p) +
        ∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
          (fun r => ¬ ∃ i, r i = p),
          (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun r : ι → ℕ => ∃ i, r i = p)]
  congr 1
  rw [piAntidiag_pure_filter_eq]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Nat.multinomial_single]
    simp only [Nat.cast_one, one_mul]
    rw [Finset.prod_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hji
      simpa [Pi.single_apply, hji] using hzero j
    · simp
  · intro i _ j _ hij
    by_contra hne
    have hh := congrFun hij i
    simp only [Pi.single_eq_same, Pi.single_apply, ite_eq_right hne] at hh
    omega

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_MomentCombinatorics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace Problem367

theorem sum_sq_le_of_two_positive {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℕ) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hri : 0 < r i) (hrj : 0 < r j) :
    (∑ k ∈ s, r k ^ 2) ≤ (∑ k ∈ s, r k - 1) ^ 2 + 1 := by
  have hsum : r i + ∑ k ∈ s.erase i, r k = ∑ k ∈ s, r k :=
    Finset.add_sum_erase s r hi
  have hsumSq : r i ^ 2 + ∑ k ∈ s.erase i, r k ^ 2 = ∑ k ∈ s, r k ^ 2 :=
    Finset.add_sum_erase s (fun k => r k ^ 2) hi
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hrest : 1 ≤ ∑ k ∈ s.erase i, r k :=
    le_trans hrj (Finset.single_le_sum (fun k _ => Nat.zero_le (r k)) hj')
  have hsq : (∑ k ∈ s.erase i, r k ^ 2) ≤ (∑ k ∈ s.erase i, r k) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => Nat.zero_le (r k))
  have htotal : 1 ≤ ∑ k ∈ s, r k := by omega
  have htotalSub := Nat.sub_add_cancel htotal
  have hiSub := Nat.sub_add_cancel hri
  have hrestSub := Nat.sub_add_cancel hrest
  nlinarith [Nat.zero_le ((r i - 1) * ((∑ k ∈ s.erase i, r k) - 1))]

theorem critical_moment_absorption {b theta : ℝ}
    (hb : 0 ≤ b) (htheta : 0 ≤ theta) (hthetaOne : theta < 1)
    (hcritical : b * theta ^ 2 = 1) {p : ℕ} (hp : 3 ≤ p) :
    0 < 1 - theta ∧ 1 - theta ≤ 1 - b * theta ^ p := by
  constructor
  · linarith
  · have hpow : theta ^ p ≤ theta ^ 3 :=
      pow_le_pow_of_le_one htheta hthetaOne.le hp
    have hmul := mul_le_mul_of_nonneg_left hpow hb
    have hcube : b * theta ^ 3 = theta := by nlinarith [hcritical]
    linarith

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_MomentInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem pow_mul_exp_le_of_log_le
    {m a c : ℝ} (hm : 0 < m) (hlog : Real.log m ≤ a)
    {q p : ℕ} (hqp : q ≤ p) :
    m ^ p * Real.exp (-a * ((p : ℝ) - c)) ≤
      m ^ q * Real.exp (-a * ((q : ℝ) - c)) := by
  have hp : m ^ p = Real.exp ((p : ℝ) * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  have hq : m ^ q = Real.exp ((q : ℝ) * Real.log m) := by
    rw [Real.exp_nat_mul, Real.exp_log hm]
  rw [hp, hq, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hqp' : (q : ℝ) ≤ p := by exact_mod_cast hqp
  nlinarith [mul_nonneg (sub_nonneg.mpr hqp') (sub_nonneg.mpr hlog)]

theorem critical_moment_error_le_order_three
    {m K : ℝ} (hm : 0 < m) (hK : 0 ≤ K) (hlog : Real.log m ≤ 2 * K)
    {p : ℕ} (hp : 3 ≤ p) :
    Real.exp (-K * (p : ℝ) ^ 2 / 2) +
        m ^ p * Real.exp (-2 * K * ((p : ℝ) - 1)) ≤
      Real.exp (-9 * K / 2) + m ^ 3 * Real.exp (-4 * K) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hfirst : Real.exp (-K * (p : ℝ) ^ 2 / 2) ≤ Real.exp (-9 * K / 2) := by
    apply Real.exp_le_exp.mpr
    have hsquare : (9 : ℝ) ≤ (p : ℝ)^2 := by nlinarith
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hsquare)]
  have hsecond := pow_mul_exp_le_of_log_le (c := (1 : ℝ)) hm hlog hp
  norm_num at hsecond
  have he1 : -2 * K * ((p : ℝ) - 1) = -(2 * K * ((p : ℝ) - 1)) := by ring
  have he2 : -4 * K = -(2 * K * 2) := by ring
  rw [he1, he2]
  exact add_le_add hfirst hsecond

theorem exists_critical_moment_constant
    {m kappa : ℝ} (hm : 0 < m) (hkappa : 0 < kappa) (K0 : ℝ) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 ≤ K ∧ Real.log m ≤ 2 * K ∧
      Real.exp (-9 * K / 2) + m ^ 3 * Real.exp (-4 * K) ≤ kappa := by
  let K := |K0| + |Real.log m| + |Real.log (kappa / 2)| +
    |Real.log (kappa / (2 * m ^ 3))| + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hK0 : K0 ≤ K := by
    dsimp [K]
    linarith [le_abs_self K0, abs_nonneg (Real.log m),
      abs_nonneg (Real.log (kappa / 2)), abs_nonneg (Real.log (kappa / (2 * m ^ 3)))]
  have hlog : Real.log m ≤ 2 * K := by
    dsimp [K]
    linarith [le_abs_self (Real.log m), abs_nonneg K0,
      abs_nonneg (Real.log m), abs_nonneg (Real.log (kappa / 2)),
      abs_nonneg (Real.log (kappa / (2 * m ^ 3)))]
  have hfirst_exp : -9 * K / 2 ≤ Real.log (kappa / 2) := by
    have hh : -Real.log (kappa / 2) ≤ K := by
      dsimp [K]
      linarith [neg_le_abs (Real.log (kappa / 2)), abs_nonneg K0,
        abs_nonneg (Real.log m), abs_nonneg (Real.log (kappa / (2 * m ^ 3)))]
    linarith
  have hsecond_exp : -4 * K ≤ Real.log (kappa / (2 * m ^ 3)) := by
    have hh : -Real.log (kappa / (2 * m ^ 3)) ≤ K := by
      dsimp [K]
      linarith [neg_le_abs (Real.log (kappa / (2 * m ^ 3))), abs_nonneg K0,
        abs_nonneg (Real.log m), abs_nonneg (Real.log (kappa / 2))]
    linarith
  have hfirst : Real.exp (-9 * K / 2) ≤ kappa / 2 := by
    calc
      Real.exp (-9 * K / 2) ≤ Real.exp (Real.log (kappa / 2)) :=
        Real.exp_le_exp.mpr hfirst_exp
      _ = kappa / 2 := Real.exp_log (by positivity)
  have hsecond : m ^ 3 * Real.exp (-4 * K) ≤ kappa / 2 := by
    calc
      m ^ 3 * Real.exp (-4 * K) ≤
          m ^ 3 * Real.exp (Real.log (kappa / (2 * m ^ 3))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsecond_exp) (by positivity)
      _ = kappa / 2 := by rw [Real.exp_log (by positivity)]; field_simp
  exact ⟨K, hK0, hK, hlog, by linarith⟩

theorem critical_moment_absorb
    {b theta A B e : ℝ} (hb : 0 ≤ b) (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : b * theta ^ 2 = 1) {p : ℕ} (hp : 3 ≤ p)
    (hB : 0 ≤ B) (he : e ≤ 1 - theta)
    (hrec : (1 - b * theta ^ p) * A ≤ B * e) : A ≤ B := by
  have hgap := (critical_moment_absorption hb htheta htheta1 hcritical hp).2
  have hpos : 0 < 1 - b * theta ^ p := by linarith
  apply (mul_le_mul_iff_right₀ hpos).mp
  calc
    (1 - b * theta ^ p) * A ≤ B * e := hrec
    _ ≤ B * (1 - theta) := mul_le_mul_of_nonneg_left he hB
    _ ≤ (1 - b * theta ^ p) * B := by
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left hgap hB

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_MixedMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem exists_two_positive_of_mixed
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ} {p : ℕ}
    (hsum : ∑ i, r i = p) (hp : 0 < p) (hmixed : ¬ ∃ i, r i = p) :
    ∃ i j, i ≠ j ∧ 0 < r i ∧ 0 < r j := by
  classical
  have hpos : 0 < ∑ i, r i := by simpa only [hsum] using hp
  obtain ⟨i, hi, hri⟩ := Finset.sum_pos_iff.mp hpos
  have hrest : 0 < ∑ j ∈ Finset.univ.erase i, r j := by
    have hh := Finset.sum_erase_add Finset.univ r hi
    rw [hsum] at hh
    have hine : r i ≠ p := fun heq => hmixed ⟨i, heq⟩
    omega
  obtain ⟨j, hj, hrj⟩ := Finset.sum_pos_iff.mp hrest
  exact ⟨i, j, Ne.symm (Finset.mem_erase.mp hj).1, hri, hrj⟩

theorem mixed_sum_sq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ} {p : ℕ}
    (hsum : ∑ i, r i = p) (hp : 0 < p) (hmixed : ¬ ∃ i, r i = p) :
    ∑ i, (r i : ℝ)^2 ≤ (p : ℝ)^2 - 2 * ((p : ℝ) - 1) := by
  obtain ⟨i, j, hij, hri, hrj⟩ := exists_two_positive_of_mixed hsum hp hmixed
  have hs := sum_sq_le_of_two_positive Finset.univ r
    (Finset.mem_univ i) (Finset.mem_univ j) hij hri hrj
  rw [hsum] at hs
  have hs' : ∑ i, (r i : ℝ)^2 ≤ ((p - 1 : ℕ) : ℝ)^2 + 1 := by exact_mod_cast hs
  rw [Nat.cast_sub hp, Nat.cast_one] at hs'
  nlinarith

theorem mixed_moment_product_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ} {p : ℕ}
    (hsum : ∑ i, r i = p) (hp : 0 < p) (hmixed : ¬ ∃ i, r i = p)
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (M : ι → ℕ → ℝ) (hM : ∀ i k, 0 ≤ M i k)
    (hbound : ∀ i k, k < p → M i k ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    ∏ i, M i (r i) ≤
      Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4) := by
  have hri : ∀ i, r i < p := by
    intro i
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => Nat.zero_le (r j))
      (Finset.mem_univ i)
    rw [hsum] at hh
    have hn : r i ≠ p := fun heq => hmixed ⟨i, heq⟩
    omega
  have hsum' : ∑ i, (r i : ℝ) = p := by exact_mod_cast hsum
  calc
    ∏ i, M i (r i) ≤
        ∏ i, (Real.exp (K * (r i : ℝ)^2) * t ^ ((r i : ℝ) / 4)) :=
      Finset.prod_le_prod (fun i _ => hM i (r i)) (fun i _ => hbound i (r i) (hri i))
    _ = Real.exp (K * ∑ i, (r i : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Real.rpow_sum_of_pos ht,
        ← Finset.mul_sum, ← Finset.sum_div, hsum']
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (mixed_sum_sq_le hsum hp hmixed) hK))
      (Real.rpow_nonneg ht.le _)

theorem mixed_multinomial_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} (hp : 0 < p)
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (M : ι → ℕ → ℝ) (hM : ∀ i k, 0 ≤ M i k)
    (hbound : ∀ i k, k < p → M i k ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    (∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
      (fun r => ¬ ∃ i, r i = p),
      (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i)) ≤
        (Fintype.card ι : ℝ)^p *
          (Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4)) := by
  classical
  let A := Finset.piAntidiag (Finset.univ : Finset ι) p
  let C := Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4)
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  have hsum : (∑ r ∈ A, (Nat.multinomial Finset.univ r : ℝ)) = (Fintype.card ι : ℝ)^p := by
    have hh := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset ι) (fun _ => (1 : ℝ)) p
    simpa [A] using hh.symm
  calc
    _ ≤ ∑ r ∈ A.filter (fun r => ¬ ∃ i, r i = p),
        (Nat.multinomial Finset.univ r : ℝ) * C := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hrA, hrMix⟩ := Finset.mem_filter.mp hr
      have hrSum := (Finset.mem_piAntidiag.mp hrA).1
      exact mul_le_mul_of_nonneg_left
        (mixed_moment_product_le hrSum hp hrMix hK ht M hM hbound) (Nat.cast_nonneg _)
    _ = (∑ r ∈ A.filter (fun r => ¬ ∃ i, r i = p),
        (Nat.multinomial Finset.univ r : ℝ)) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ r ∈ A, (Nat.multinomial Finset.univ r : ℝ)) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun r _ _ => Nat.cast_nonneg _)
    _ = _ := by rw [hsum]

open MeasureTheory ProbabilityTheory in

theorem independent_abs_moment_le_pure_add_remainder
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    {p : ℕ} (hp : 0 < p)
    (hMom : ∀ i k, k ≤ p → Integrable (fun ω => |X i ω| ^ k) μ)
    {K t : ℝ} (hK : 0 ≤ K) (ht : 0 < t)
    (hbound : ∀ i k, k < p → (∫ ω, |X i ω| ^ k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    (∫ ω, |∑ i, X i ω| ^ p ∂μ) ≤ (∑ i, ∫ ω, |X i ω| ^ p ∂μ) +
      (Fintype.card ι : ℝ)^p *
        (Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) * t ^ ((p : ℝ) / 4)) := by
  classical
  let M : ι → ℕ → ℝ := fun i k => ∫ ω, |X i ω| ^ k ∂μ
  have hzero : ∀ i, M i 0 = 1 := by intro i; simp [M]
  have hM : ∀ i k, 0 ≤ M i k := by
    intro i k
    exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) _)
  calc
    _ ≤ ∑ r ∈ Finset.piAntidiag (Finset.univ : Finset ι) p,
        (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i) :=
      integral_abs_sum_pow_le_of_iIndepFun hX hmX p hMom
    _ = (∑ i, M i p) +
        ∑ r ∈ (Finset.piAntidiag (Finset.univ : Finset ι) p).filter
          (fun r => ¬ ∃ i, r i = p),
          (Nat.multinomial Finset.univ r : ℝ) * ∏ i, M i (r i) :=
      multinomial_sum_eq_pure_add_mixed M hzero hp
    _ ≤ _ := add_le_add (le_refl _) (mixed_multinomial_sum_le hp hK ht M hM hbound)

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_MomentTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem exists_moment_order {K L : ℝ} (hK : 0 < K) (hL : 32 * K ≤ L) :
    ∃ p : ℕ, 1 ≤ p ∧
      K * (p : ℝ) ^ 2 - (p : ℝ) * L / 8 ≤ -(L ^ 2) / (512 * K) := by
  let p : ℕ := ⌊L / (16 * K)⌋₊
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hden : 0 < 16 * K := by positivity
  have hratio : 2 ≤ L / (16 * K) := by
    apply (le_div_iff₀ hden).mpr
    linarith
  have hp1 : 1 ≤ p := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hpu : (p : ℝ) ≤ L / (16 * K) :=
    Nat.floor_le (by positivity)
  have hpl' : L / (16 * K) < (p : ℝ) + 1 := Nat.lt_floor_add_one _
  have hpl : L / (32 * K) ≤ (p : ℝ) := by
    have hratio' : L / (32 * K) = (L / (16 * K)) / 2 := by ring
    rw [hratio']
    linarith
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hpu' : 16 * K * (p : ℝ) ≤ L := by
    nlinarith [(le_div_iff₀ hden).mp hpu]
  have hstep : K * (p : ℝ) ^ 2 - (p : ℝ) * L / 8 ≤ -(p : ℝ) * L / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right hpu' hp0]
  have hpl'': L ≤ (p : ℝ) * (32 * K) :=
    (div_le_iff₀ (by positivity)).mp hpl
  refine ⟨p, hp1, hstep.trans ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < 512 * K)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hpl'' hL0.le]

theorem measureReal_abs_gt_le_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {a : ℝ} {p : ℕ}
    (ha : 0 < a) (hY : Integrable (fun ω => |Y ω| ^ p) μ) :
    μ.real {ω | a < |Y ω|} ≤ (∫ ω, |Y ω| ^ p ∂μ) / a ^ p := by
  have hsubset : {ω | a < |Y ω|} ⊆ {ω | a ^ p ≤ |Y ω| ^ p} := by
    intro ω hω
    exact pow_le_pow_left₀ ha.le hω.le p
  apply (le_div_iff₀ (pow_pos ha p)).mpr
  calc
    μ.real {ω | a < |Y ω|} * a ^ p ≤
        μ.real {ω | a ^ p ≤ |Y ω| ^ p} * a ^ p :=
      mul_le_mul_of_nonneg_right (measureReal_mono hsubset) (pow_nonneg ha.le p)
    _ ≤ ∫ ω, |Y ω| ^ p ∂μ := by
      simpa only [mul_comm] using
        mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall (fun ω => pow_nonneg (abs_nonneg (Y ω)) p)) hY (a ^ p)

theorem measureReal_abs_gt_exp_le_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {K L : ℝ}
    (hK : 0 < K) (hL : 32 * K ≤ L)
    (hint : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |Y ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∫ ω, |Y ω| ^ p ∂μ) ≤ Real.exp (K * (p : ℝ) ^ 2 - (p : ℝ) * L / 4)) :
    μ.real {ω | Real.exp (-L / 8) < |Y ω|} ≤
      Real.exp (-(L ^ 2) / (512 * K)) := by
  obtain ⟨p, hp, hexponent⟩ := exists_moment_order hK hL
  calc
    μ.real {ω | Real.exp (-L / 8) < |Y ω|} ≤
        (∫ ω, |Y ω| ^ p ∂μ) / Real.exp (-L / 8) ^ p :=
      measureReal_abs_gt_le_moment (Real.exp_pos _) (hint p hp)
    _ ≤ Real.exp (K * (p : ℝ) ^ 2 - (p : ℝ) * L / 4) /
        Real.exp (-L / 8) ^ p :=
      div_le_div_of_nonneg_right (hmom p hp) (pow_nonneg (Real.exp_nonneg _) p)
    _ = Real.exp (K * (p : ℝ) ^ 2 - (p : ℝ) * L / 8) := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ Real.exp (-(L ^ 2) / (512 * K)) := Real.exp_le_exp.mpr hexponent

theorem measureReal_abs_gt_rpow_le_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {K t : ℝ}
    (hK : 0 < K) (ht : 0 < t) (hsmall : 32 * K ≤ Real.log (1 / t))
    (hint : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |Y ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∫ ω, |Y ω| ^ p ∂μ) ≤ Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) :
    μ.real {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
      Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K)) := by
  have hthreshold : Real.exp (-Real.log (1 / t) / 8) = t ^ (1 / 8 : ℝ) := by
    rw [Real.rpow_def_of_pos ht, one_div, Real.log_inv]
    congr 1
    ring
  rw [← hthreshold]
  apply measureReal_abs_gt_exp_le_of_moments hK hsmall hint
  intro p hp
  convert hmom p hp using 1
  all_goals try with_reducible_and_instances rfl
  rw [Real.rpow_def_of_pos ht, ← Real.exp_add, one_div, Real.log_inv]
  congr 1
  ring

theorem measure_abs_gt_rpow_le_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} {K t : ℝ}
    (hK : 0 < K) (ht : 0 < t) (hsmall : 32 * K ≤ Real.log (1 / t))
    (hint : ∀ p : ℕ, 1 ≤ p → Integrable (fun ω => |Y ω| ^ p) μ)
    (hmom : ∀ p : ℕ, 1 ≤ p →
      (∫ ω, |Y ω| ^ p ∂μ) ≤ Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) :
    μ {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
      ENNReal.ofReal (Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K))) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal
    (measureReal_abs_gt_rpow_le_of_moments hK ht hsmall hint hmom)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_MomentRecurrence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem critical_cavity_moment_step
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : ℕ} {theta K t : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK : 0 ≤ K) (ht : 0 < t)
    (hlog : Real.log ((b : ℝ) + 1) ≤ 2 * K)
    (hsmall : Real.exp (-9 * K / 2) + ((b : ℝ) + 1)^3 * Real.exp (-4 * K) ≤ 1 - theta)
    (A : ℕ → ℝ) {p : ℕ} (hp : 3 ≤ p)
    {X : Fin (b + 1) → Ω → ℝ} (hX : iIndepFun X μ)
    (hmX : ∀ i, Measurable (X i))
    (hMom : ∀ i (k : ℕ), k ≤ p → Integrable (fun ω => |X i ω|^k) μ)
    (hRec : A p ≤ ∫ ω, |∑ i, X i ω|^p ∂μ)
    (hOwn : ∀ k : ℕ, k ≤ p → (∫ ω, |X 0 ω|^k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2 / 2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ (i : Fin b) k, k ≤ p → (∫ ω, |X i.succ ω|^k ∂μ) ≤ theta^k * A k)
    (hLower : ∀ k, k < p → A k ≤ Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :
    A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  have hbound : ∀ (i : Fin (b + 1)) k, k < p → (∫ ω, |X i ω|^k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4) := by
    intro i k hk
    refine Fin.cases ?_ (fun j => ?_) i
    · calc
        _ ≤ Real.exp (K * (k : ℝ)^2 / 2) * t ^ ((k : ℝ) / 4) := hOwn k hk.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hK (sq_nonneg (k : ℝ))]))
          (Real.rpow_nonneg ht.le _)
    · calc
        _ ≤ theta^k * A k := hChild j k hk.le
        _ ≤ theta^k * (Real.exp (K * (k : ℝ)^2) * t ^ ((k : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left (hLower k hk) (pow_nonneg htheta _)
        _ ≤ _ := mul_le_of_le_one_left (by positivity) (pow_le_one₀ htheta htheta1.le)
  have hest := independent_abs_moment_le_pure_add_remainder hX hmX
    (show 0 < p by omega) hMom hK ht hbound
  have hpure : (∑ i : Fin (b + 1), ∫ ω, |X i ω|^p ∂μ) ≤
      Real.exp (K * (p : ℝ)^2 / 2) * t ^ ((p : ℝ) / 4) +
        (b : ℝ) * theta^p * A p := by
    rw [Fin.sum_univ_succ]
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin b))) => hChild i p (le_refl _))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    have := add_le_add (hOwn p (le_refl _)) hh
    simpa only [mul_assoc] using this
  have hrec' : (1 - (b : ℝ) * theta^p) * A p ≤
      (Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) *
      (Real.exp (-K * (p : ℝ)^2 / 2) +
        ((b : ℝ) + 1)^p * Real.exp (-2 * K * ((p : ℝ) - 1))) := by
    have hh := hRec.trans (hest.trans (add_le_add hpure (le_refl _)))
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hh
    have he1 : Real.exp (K * (p : ℝ)^2 / 2) =
        Real.exp (K * (p : ℝ)^2) * Real.exp (-K * (p : ℝ)^2 / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (K * ((p : ℝ)^2 - 2 * ((p : ℝ) - 1))) =
        Real.exp (K * (p : ℝ)^2) * Real.exp (-2 * K * ((p : ℝ) - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he1, he2] at hh
    nlinarith
  apply critical_moment_absorb (Nat.cast_nonneg b) htheta htheta1 hcritical hp
    (by positivity) (e := Real.exp (-K * (p : ℝ)^2 / 2) +
      ((b : ℝ) + 1)^p * Real.exp (-2 * K * ((p : ℝ) - 1))) _ hrec'
  exact (critical_moment_error_le_order_three (by positivity) hK hlog hp).trans hsmall

theorem critical_all_moments_of_independent_recursion
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {b : ℕ} {theta K t : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta^2 = 1) (hK : 0 ≤ K) (ht : 0 < t)
    (hlog : Real.log ((b : ℝ) + 1) ≤ 2 * K)
    (hsmall : Real.exp (-9 * K / 2) + ((b : ℝ) + 1)^3 * Real.exp (-4 * K) ≤ 1 - theta)
    (A : ℕ → ℝ) {X : Fin (b + 1) → Ω → ℝ}
    (hX : iIndepFun X μ) (hmX : ∀ i, Measurable (X i))
    (hMom : ∀ i (k : ℕ), Integrable (fun ω => |X i ω|^k) μ)
    (hRec : ∀ p, A p ≤ ∫ ω, |∑ i, X i ω|^p ∂μ)
    (hOwn : ∀ k : ℕ, (∫ ω, |X 0 ω|^k ∂μ) ≤
      Real.exp (K * (k : ℝ)^2 / 2) * t ^ ((k : ℝ) / 4))
    (hChild : ∀ (i : Fin b) k, (∫ ω, |X i.succ ω|^k ∂μ) ≤ theta^k * A k)
    (hbase : ∀ p, p < 3 → A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4)) :
    ∀ p, A p ≤ Real.exp (K * (p : ℝ)^2) * t ^ ((p : ℝ) / 4) := by
  intro p
  induction p using Nat.strong_induction_on with
  | h p ih =>
    by_cases hp : p < 3
    · exact hbase p hp
    · exact critical_cavity_moment_step htheta htheta1 hcritical hK ht hlog hsmall A
        (by omega) hX hmX (fun i k _ => hMom i k) (hRec p)
        (fun k _ => hOwn k) (fun i k _ => hChild i k) ih

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Cavity_MomentTransport
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem abs_moment_of_identDistrib_abs
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {Y : Ω → ℝ} {Z : Ξ → ℝ}
    (h : IdentDistrib (fun ω => |Z ω|) (fun ω => |Y ω|) ν μ) (p : ℕ) :
    (Integrable (fun ω => |Z ω|^p) ν ↔ Integrable (fun ω => |Y ω|^p) μ) ∧
      (∫ ω, |Z ω|^p ∂ν) = ∫ ω, |Y ω|^p ∂μ := by
  have hp := h.comp (measurable_id.pow_const p)
  exact ⟨hp.integrable_iff, hp.integral_eq⟩

theorem response_abs_moment_of_identDistrib_abs
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {μ : Measure Ω} {ν : Measure Ξ} {Y : Ω → ℝ} {Z : Ξ → ℝ}
    (h : IdentDistrib (fun ω => |Z ω|) (fun ω => |Y ω|) ν μ)
    {theta : ℝ} {psi : ℝ → ℝ}
    (hpsi : Measurable psi) (hZ : Measurable Z)
    (hcontract : ∀ z, |psi z| ≤ theta * |z|) (p : ℕ)
    (hint : Integrable (fun ω => |Y ω|^p) μ) :
    Integrable (fun ω => |psi (Z ω)|^p) ν ∧
      (∫ ω, |psi (Z ω)|^p ∂ν) ≤ theta^p * ∫ ω, |Y ω|^p ∂μ := by
  obtain ⟨hi, heq⟩ := abs_moment_of_identDistrib_abs h p
  have hZi := hi.mpr hint
  have hbound : ∀ ω, |psi (Z ω)|^p ≤ theta^p * |Z ω|^p := by
    intro ω
    simpa only [mul_pow] using
      pow_le_pow_left₀ (abs_nonneg _) (hcontract (Z ω)) p
  have hpi : Integrable (fun ω => |psi (Z ω)|^p) ν := by
    apply (hZi.const_mul (theta^p)).mono' ((hpsi.comp hZ).abs.pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => by
      change ‖|psi (Z ω)|^p‖ ≤ theta^p * |Z ω|^p
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg (psi (Z ω))) p)]
      exact hbound ω
  refine ⟨hpi, ?_⟩
  calc
    _ ≤ ∫ ω, theta^p * |Z ω|^p ∂ν := integral_mono hpi (hZi.const_mul _) hbound
    _ = theta^p * ∫ ω, |Y ω|^p ∂μ := by rw [integral_const_mul, heq]

theorem iIndepFun_cavity_response
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} {b : ℕ}
    {Z : Fin (b + 1) → Ξ → ℝ} (hZ : iIndepFun Z ν)
    {psi : ℝ → ℝ} (hpsi : Measurable psi) :
    iIndepFun (fun (i : Fin (b + 1)) (ω : Ξ) => Fin.cases (motive := fun _ => ℝ) (Z 0 ω) (fun j => psi (Z j.succ ω)) i) ν := by
  have hm : ∀ i : Fin (b + 1), Measurable (fun x : ℝ =>
      Fin.cases (motive := fun _ => ℝ) x (fun _ => psi x) i) := by
    intro i
    exact Fin.cases measurable_id (fun _ => hpsi) i
  have hh := hZ.comp (fun (i : Fin (b + 1)) (x : ℝ) =>
    Fin.cases (motive := fun _ => ℝ) x (fun _ => psi x) i) hm
  have hfun : (fun i => (fun x : ℝ => Fin.cases (motive := fun _ => ℝ) x (fun _ => psi x) i) ∘ Z i) =
      (fun (i : Fin (b + 1)) (ω : Ξ) => Fin.cases (motive := fun _ => ℝ)
        (Z 0 ω) (fun j => psi (Z j.succ ω)) i) := by
    funext i ω
    refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  rw [hfun] at hh
  exact hh

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_DiscreteConditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped MeasureTheory

namespace Problem367

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  [MeasurableSingletonClass A] {μ : Measure Ω} [IsFiniteMeasure μ]

theorem condExp_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {f : Ω → ℝ} (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap S inferInstance] =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => ∫ ω, f ω ∂μ[|S ⁻¹' {a}] := by
  let s := S ⁻¹' {a}
  have hs : MeasurableSet s := hS (measurableSet_singleton a)
  have hs' : MeasurableSet[MeasurableSpace.comap S inferInstance] s :=
    ⟨{a}, measurableSet_singleton a, rfl⟩
  by_cases hμs : μ s = 0
  · rw [show S ⁻¹' {a} = s from rfl, Measure.restrict_eq_zero.2 hμs]
    rfl
  have havg : (∫ ω, (∫ x, f x ∂μ[|s]) ∂μ.restrict s) =
      ∫ ω, f ω ∂μ.restrict s := by
    rw [integral_const, ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    rw [← mul_assoc, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr
      ⟨hμs, measure_ne_top _ _⟩), one_mul]
  refine (condExp_restrict_ae_eq_restrict hS.comap_le hs' hf).symm.trans ?_
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hS.comap_le hf.restrict
  · intro t _ _
    exact (integrable_const _).integrableOn
  · rintro t ⟨u, hu, rfl⟩ _
    rw [Measure.restrict_restrict (hS hu)]
    by_cases ha : a ∈ u
    · have heq : S ⁻¹' u ∩ s = s := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff]
        exact ⟨And.right, fun h => ⟨h ▸ ha, h⟩⟩
      rw [heq]
      exact havg
    · have heq : S ⁻¹' u ∩ s = ∅ := by
        ext ω
        simp only [s, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
          iff_false, not_and]
        intro h hEq
        exact ha (hEq ▸ h)
      simp [heq]
  · exact stronglyMeasurable_const.aestronglyMeasurable

theorem condExp_indicator_comap_eq_cond_on_fiber {S : Ω → A} (hS : Measurable S)
    (a : A) {t : Set Ω} (ht : MeasurableSet t) :
    μ⟦t | MeasurableSpace.comap S inferInstance⟧ =ᵐ[μ.restrict (S ⁻¹' {a})]
      fun _ => μ[|S ⁻¹' {a}].real t := by
  rw [← integral_indicator_one ht]
  exact condExp_comap_eq_cond_on_fiber hS a ((integrable_const (1 : ℝ)).indicator ht)

theorem indepFun_cond_fiber_of_condIndepFun [StandardBorelSpace Ω]
    {B C : Type*} [MeasurableSpace B] [MeasurableSpace C]
    {S : Ω → A} {X : Ω → B} {Y : Ω → C}
    (hS : Measurable S) (hX : Measurable X) (hY : Measurable Y)
    (hXY : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X Y μ)
    (a : A) : IndepFun X Y μ[|S ⁻¹' {a}] := by
  by_cases hμa : μ (S ⁻¹' {a}) = 0
  · rw [cond_eq_zero_of_meas_eq_zero hμa]
    simp [indepFun_iff_measure_inter_preimage_eq_mul]
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hcond := (condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY).mp hXY s t hs ht
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a ((hX hs).inter (hY ht))
  have hfirst := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hX hs)
  have hsecond := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a (hY ht)
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (X ⁻¹' s ∩ Y ⁻¹' t) =
        μ[|S ⁻¹' {a}].real (X ⁻¹' s) * μ[|S ⁻¹' {a}].real (Y ⁻¹' t) := by
    filter_upwards [hcond', hleft, hfirst, hsecond] with ω h h₁ h₂ h₃
    simpa only [h₁, h₂, h₃] using h
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by finiteness)).mp
  simpa only [measureReal_def, ENNReal.toReal_mul] using hω

theorem iIndepFun_cond_fiber_of_iCondIndepFun [StandardBorelSpace Ω]
    {ι : Type*} {B : ι → Type*} [mB : ∀ i, MeasurableSpace (B i)]
    {S : Ω → A} {X : ∀ i, Ω → B i}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hXI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X μ)
    (a : A) (hμa : μ (S ⁻¹' {a}) ≠ 0) : iIndepFun X μ[|S ⁻¹' {a}] := by
  classical
  let : IsProbabilityMeasure μ[|S ⁻¹' {a}] := cond_isProbabilityMeasure hμa
  have : (ae (μ.restrict (S ⁻¹' {a}))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hμa)
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro I sets hsets
  have hcond := (iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB X hX).mp hXI I hsets
  have hcond' := ae_restrict_le (s := S ⁻¹' {a}) hcond
  have hmeas : MeasurableSet (⋂ i ∈ I, X i ⁻¹' sets i) :=
    Finset.measurableSet_biInter I (fun i hi => hX i (hsets i hi))
  have hleft := condExp_indicator_comap_eq_cond_on_fiber (μ := μ) hS a hmeas
  have heach : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}), ∀ i ∈ I,
      (μ⟦X i ⁻¹' sets i | MeasurableSpace.comap S inferInstance⟧) ω =
        μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    apply (Finset.eventually_all I).mpr
    intro i hi
    exact condExp_indicator_comap_eq_cond_on_fiber hS a (hX i (hsets i hi))
  have heq : ∀ᵐ ω ∂μ.restrict (S ⁻¹' {a}),
      μ[|S ⁻¹' {a}].real (⋂ i ∈ I, X i ⁻¹' sets i) =
        ∏ i ∈ I, μ[|S ⁻¹' {a}].real (X i ⁻¹' sets i) := by
    filter_upwards [hcond', hleft, heach] with ω h h₁ h₂
    rw [h₁] at h
    simp only [Finset.prod_apply] at h
    exact h.trans (Finset.prod_congr rfl h₂)
  obtain ⟨ω, hω⟩ := heq.exists
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _)
    (ENNReal.prod_ne_top (fun i hi => measure_ne_top _ _))).mp
  simpa only [measureReal_def, ENNReal.toReal_prod] using hω

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfinitePiPair
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

variable {I A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem infinitePi_map_pair_arrays
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i => (μ i).prod (ν i)) := by
  apply (Measure.isProjectiveLimit_infinitePi (fun i => (μ i).prod (ν i))).unique ?_ |>.symm
  intro s
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      s.restrict ∘ (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) =
      (fun p : (s → A) × (s → B) => fun i => (p.1 i, p.2 i)) ∘
        Prod.map s.restrict s.restrict := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  exact (measurePreserving_arrowProdEquivProdArrow A B s
    (fun i : s => μ i) (fun i : s => ν i)).symm.map_eq

theorem infinitePi_map_split_pairs
    (μ : I → Measure A) (ν : I → Measure B)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i => (μ i).prod (ν i))).map
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) =
      (Measure.infinitePi μ).prod (Measure.infinitePi ν) := by
  rw [← infinitePi_map_pair_arrays μ ν,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp :
      (fun x : I → A × B => (fun i => (x i).1, fun i => (x i).2)) ∘
        (fun p : (I → A) × (I → B) => fun i => (p.1 i, p.2 i)) = id := rfl
  rw [hcomp, Measure.map_id]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Pullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun m hm f g ν) :
    CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := he.quasiMeasurePreserving.ae_eq_comp
    ((condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg).mp hfg U V hU hV)
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.trans (hωmul.trans (congrArg₂ (· * ·) hωE.symm hωH.symm))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_FamilyConditionalPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

alias ⟨_, iCondIndepFun_of_comp_measurePreserving⟩ :=
  iCondIndepFun_iff_comp_measurePreserving

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_InfiniteBlockIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

open MeasureTheory ProbabilityTheory

section Unconditional

variable {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : Measure Ω} {f : ∀ i, Ω → X i}

theorem iIndepFun_disjoint_blocks {κ : Type*} (hf : iIndepFun f μ)
    (hm : ∀ i, Measurable (f i)) (S : κ → Set ι)
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndepFun (fun j ω (i : S j) => f i ω) μ := by
  have := hf.isProbabilityMeasure
  have : ∀ index, IsProbabilityMeasure (μ.map (f index)) :=
    fun i => Measure.isProbabilityMeasure_map (hm i).aemeasurable
  have hinj : Function.Injective (fun p : (j : κ) × S j => (p.2 : ι)) := by
    rintro ⟨i, u⟩ ⟨j, v⟩ huv
    change (u : ι) = (v : ι) at huv
    have hij : i = j := by
      by_contra hne
      exact Set.disjoint_left.1 (hS hne) u.property (huv.symm ▸ v.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext huv)
  have hgroup := hf.precomp hinj
  have hmap := hgroup.map_fun_eq_infinitePi_map (fun p => hm p.2)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  calc
    μ.map (fun ω j (i : S j) => f i ω) =
        (μ.map (fun ω (p : (j : κ) × S j) => f p.2 ω)).map
          (MeasurableEquiv.piCurry (fun j (i : S j) => X i)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.infinitePi (fun j =>
        Measure.infinitePi (fun i : S j => μ.map (f i))) := by
      rw [hmap]
      exact Measure.infinitePi_map_piCurry (fun (j : κ) (i : S j) => μ.map (f i))
    _ = Measure.infinitePi (fun j => μ.map (fun ω (i : S j) => f i ω)) := by
      congr 1
      funext j
      exact (hf.precomp (g := fun i : S j => (i : ι)) Subtype.val_injective
        |>.map_fun_eq_infinitePi_map (fun i : S j => hm (i : ι))).symm

theorem infinitePi_map_disjoint_family {κ : Type*}
    (ν : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    (S : κ → Set ι) (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    (Measure.infinitePi ν).map (fun labels index => (S index).domRestrict labels) =
      Measure.infinitePi (fun j => Measure.infinitePi (fun i : S j => ν i)) := by
  have h := iIndepFun_disjoint_blocks (iIndepFun_infinitePi (fun _ => measurable_id))
    (fun i => measurable_pi_apply i) S hS (μ := Measure.infinitePi ν)
  change iIndepFun (fun index labels => (S index).domRestrict labels)
    (Measure.infinitePi ν) at h
  calc
    _ = Measure.infinitePi (fun index => (Measure.infinitePi ν).map (S index).domRestrict) :=
      h.map_fun_eq_infinitePi_map (by fun_prop)
    _ = _ := by
      congr 1
      funext j
      exact Measure.infinitePi_map_restrict' ν

end Unconditional

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentProductIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem367

theorem setIntegral_prod_preimage_fst
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {f : S × A → ℝ} (hf : Integrable f (ρ.prod μ)) (D : Set S) :
    (∫ z in Prod.fst ⁻¹' D, f z ∂ρ.prod μ) =
      ∫ s in D, ∫ a, f (s, a) ∂μ ∂ρ := by
  have hset : (Prod.fst ⁻¹' D : Set (S × A)) = D ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, ← Measure.restrict_prod_eq_prod_univ]
  apply integral_prod
  rw [Measure.restrict_prod_eq_prod_univ]
  exact hf.restrict

theorem condExp_prod_fst
    {S A : Type*} [mS : MeasurableSpace S] [MeasurableSpace A]
    (ρ : Measure S) (μ : Measure A) [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    {f : S × A → ℝ} (hfm : StronglyMeasurable f) (hf : Integrable f (ρ.prod μ)) :
    (ρ.prod μ)[f | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
      fun z => ∫ a, f (z.1, a) ∂μ := by
  have hg : Integrable (fun z : S × A => ∫ a, f (z.1, a) ∂μ) (ρ.prod μ) :=
    hf.integral_prod_left.comp_fst μ
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun _ _ _ => hg.integrableOn)
  · intro D hD _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hD
    rw [setIntegral_prod_preimage_fst ρ μ hg,
      setIntegral_prod_preimage_fst ρ μ hf]
    simp
  · have hfm' : StronglyMeasurable (Function.uncurry (fun s a => f (s, a))) := by
      simpa only [Function.uncurry_def] using hfm
    exact (hfm'.integral_prod_right.comp_measurable
      (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

theorem condIndepFun_latent_product
    {S A B C D : Type*} [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace S] [StandardBorelSpace A] [StandardBorelSpace B]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap (Prod.fst : S × (A × B) → S)) measurable_fst.comap_le
      (fun z : S × (A × B) => F (z.1, z.2.1))
      (fun z : S × (A × B) => G (z.1, z.2.2)) (ρ.prod (μ.prod ν)) := by
  classical
  have hFm : Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) := by fun_prop
  have hGm : Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) := by fun_prop
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hFm hGm]
  intro U V hU hV
  let E : Set (S × (A × B)) := (fun z => F (z.1, z.2.1)) ⁻¹' U
  let H : Set (S × (A × B)) := (fun z => G (z.1, z.2.2)) ⁻¹' V
  have hE : MeasurableSet E := hU.preimage hFm
  have hH : MeasurableSet H := hV.preimage hGm
  have hcE := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hE).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hE)
  have hcH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator hH).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hH)
  have hcEH := condExp_prod_fst ρ (μ.prod ν)
    (measurable_const.indicator (hE.inter hH)).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  filter_upwards [hcE, hcH, hcEH] with z hzE hzH hzEH
  change ((ρ.prod (μ.prod ν))[(E ∩ H).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzEH, hzE, hzH]
  have hprod : (fun ab : A × B => (E ∩ H).indicator (fun _ => (1 : ℝ)) (z.1, ab)) =
      fun ab => (if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0) *
        (if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0) := by
    funext ab
    by_cases hfa : F (z.1, ab.1) ∈ U <;> by_cases hgb : G (z.1, ab.2) ∈ V <;>
      simp [E, H, hfa, hgb]
  rw [hprod, integral_prod_mul
    (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)
    (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
  have hleft : (∫ ab : A × B, E.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ a, if F (z.1, a) ∈ U then (1 : ℝ) else 0 ∂μ := by
    change (∫ ab : A × B, if F (z.1, ab.1) ∈ U then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_fst (fun a => if F (z.1, a) ∈ U then (1 : ℝ) else 0)]
    simp
  have hright : (∫ ab : A × B, H.indicator (fun _ => (1 : ℝ)) (z.1, ab) ∂μ.prod ν) =
      ∫ b, if G (z.1, b) ∈ V then (1 : ℝ) else 0 ∂ν := by
    change (∫ ab : A × B, if G (z.1, ab.2) ∈ V then (1 : ℝ) else 0 ∂μ.prod ν) = _
    rw [integral_fun_snd (fun b => if G (z.1, b) ∈ V then (1 : ℝ) else 0)]
    simp
  rw [hleft, hright]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LatentFamilyIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iCondIndepFun_latent_of_fiber_indep
    {ι S A : Type*} {B : ι → Type*}
    [mS : MeasurableSpace S] [MeasurableSpace A]
    [mB : ∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [StandardBorelSpace A]
    (ρ : Measure S) (μ : Measure A)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ]
    (F : ∀ i, S × A → B i) (hF : ∀ i, Measurable (F i))
    (hind : ∀ s, iIndepFun (fun i a => F i (s, a)) μ) :
    iCondIndepFun (mS.comap (Prod.fst : S × A → S)) measurable_fst.comap_le
      F (ρ.prod μ) := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mB F hF]
  intro I sets hsets
  let E : ι → Set (S × A) := fun i => F i ⁻¹' sets i
  have hE : ∀ i ∈ I, MeasurableSet (E i) := fun i hi => (hsets i hi).preimage (hF i)
  have hEI : MeasurableSet (⋂ i ∈ I, E i) := by
    exact I.measurableSet_biInter hE
  have hcI := condExp_prod_fst ρ μ
    (measurable_const.indicator hEI).stronglyMeasurable
    ((integrable_const (1 : ℝ)).indicator hEI)
  have hc : ∀ i ∈ I,
      (ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst] =ᵐ[ρ.prod μ]
        fun z => ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ := by
    intro i hi
    exact condExp_prod_fst ρ μ
      (measurable_const.indicator (hE i hi)).stronglyMeasurable
      ((integrable_const (1 : ℝ)).indicator (hE i hi))
  have hcall := (Filter.eventually_all_finset I).2 hc
  filter_upwards [hcI, hcall] with z hzI hz
  change ((ρ.prod μ)[(⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) |
      mS.comap Prod.fst]) z = _
  rw [hzI]
  simp only [Finset.prod_apply]
  have hprod : (∏ i ∈ I,
      ((ρ.prod μ)[(E i).indicator (fun _ => (1 : ℝ)) | mS.comap Prod.fst]) z) =
      ∏ i ∈ I, ∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ :=
    Finset.prod_congr rfl hz
  rw [hprod]
  let T : ι → Set A := fun i => (fun a => F i (z.1, a)) ⁻¹' sets i
  have hT : ∀ i ∈ I, MeasurableSet (T i) := by
    intro i hi
    exact (hsets i hi).preimage ((hF i).comp (measurable_const.prodMk measurable_id))
  have hTI : MeasurableSet (⋂ i ∈ I, T i) := I.measurableSet_biInter hT
  have hleft : (fun a => (⋂ i ∈ I, E i).indicator (fun _ => (1 : ℝ)) (z.1, a)) =
      (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) := by
    funext a
    simp only [Set.indicator, Set.mem_iInter, E, T, Set.mem_preimage]
  rw [hleft]
  have hmass : (∫ a, (⋂ i ∈ I, T i).indicator (fun _ => (1 : ℝ)) a ∂μ) =
      μ.real (⋂ i ∈ I, T i) := by
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) hTI)
  rw [hmass]
  have hright : ∀ i ∈ I,
      (∫ a, (E i).indicator (fun _ => (1 : ℝ)) (z.1, a) ∂μ) = μ.real (T i) := by
    intro i hi
    change (∫ a, (T i).indicator (fun _ => (1 : ℝ)) a ∂μ) = _
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) (hT i hi))
  rw [Finset.prod_congr rfl hright]
  unfold Measure.real
  rw [(hind z.1).measure_inter_preimage_eq_mul I hsets, ENNReal.toReal_prod]

theorem iCondIndepFun_latent_infinitePi
    {ι S : Type*} [Countable ι] {A B : ι → Type*}
    [mS : MeasurableSpace S] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSpace (B i)]
    [StandardBorelSpace S] [∀ i, StandardBorelSpace (A i)]
    (ρ : Measure S) (ν : ∀ i, Measure (A i))
    [IsFiniteMeasure ρ] [∀ i, IsProbabilityMeasure (ν i)]
    (F : ∀ i, S × A i → B i) (hF : ∀ i, Measurable (F i)) :
    iCondIndepFun (mS.comap (Prod.fst : S × (∀ i, A i) → S))
      measurable_fst.comap_le
      (fun i z => F i (z.1, z.2 i)) (ρ.prod (Measure.infinitePi ν)) := by
  apply iCondIndepFun_latent_of_fiber_indep ρ (Measure.infinitePi ν)
    (fun i z => F i (z.1, z.2 i))
  · intro i
    exact (hF i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  · intro s
    exact iIndepFun_infinitePi (fun i =>
      (hF i).comp (measurable_const.prodMk measurable_id))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FairSpin
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

lemma fairSpin_neg_preimage : fairSpin ⁻¹' {IsingSpin.neg} = Set.Iic (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin]

lemma fairSpin_pos_preimage : fairSpin ⁻¹' {IsingSpin.pos} = Set.Ioi (1 / 2 : ℝ) := by
  ext u
  simp [fairSpin, not_le]

lemma fairSpin_neg_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.neg}) = 1 / 2 := by
  rw [fairSpin_neg_preimage, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Icc 0 (1 / 2) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨h0, hu⟩
    · rintro ⟨h0, hu⟩
      exact ⟨hu, h0, by linarith⟩
  rw [h, Real.volume_Icc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_pos_mass : uniform01 (fairSpin ⁻¹' {IsingSpin.pos}) = 1 / 2 := by
  rw [fairSpin_pos_preimage, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi (1 / 2 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc (1 / 2) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hu, h0, h1⟩
      exact ⟨hu, h1⟩
    · rintro ⟨hu, h1⟩
      exact ⟨hu, by linarith, h1⟩
  rw [h, Real.volume_Ioc]
  norm_num [ENNReal.ofReal_div_of_pos]

lemma fairSpin_mass (a : IsingSpin) : uniform01 (fairSpin ⁻¹' {a}) = 1 / 2 := by
  cases a
  · exact fairSpin_neg_mass
  · exact fairSpin_pos_mass

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_LabelDecomposition
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.LabelDecomposition

theorem indepFun_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    IndepFun (fun U : ι → A => U r)
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i)
      (Measure.infinitePi μ) := by
  have hi : iIndepFun (fun i (U : ι → A) => U i) (Measure.infinitePi μ) :=
    iIndepFun_infinitePi (X := fun _ a => a) (fun _ => measurable_id)
  have hle : ∀ i : ι,
      MeasurableSpace.comap (fun U : ι → A => U i) inferInstance ≤
        (inferInstance : MeasurableSpace (ι → A)) :=
    fun i => measurable_iff_comap_le.mp (measurable_pi_apply i)
  have hd : Disjoint ({r} : Set ι) {i | i ≠ r} := by simp
  have h := indep_iSup_of_disjoint hle hi hd
  change Indep (MeasurableSpace.comap (fun U : ι → A => U r) inferInstance)
    (MeasurableSpace.comap
      (fun U : ι → A => fun i : {i : ι // i ≠ r} => U i) inferInstance)
    (Measure.infinitePi μ)
  rw [MeasurableSpace.comap_process_pi, iSup_subtype]
  simpa only [Set.mem_singleton_iff, Set.mem_ofPred_eq, iSup_iSup_eq_left] using h

theorem map_coordinate_rest {ι A : Type*} [MeasurableSpace A]
    (μ : ι → Measure A) [∀ i, IsProbabilityMeasure (μ i)] (r : ι) :
    (Measure.infinitePi μ).map
      (fun U : ι → A => (U r, fun i : {i : ι // i ≠ r} => U i)) =
      (μ r).prod (Measure.infinitePi (fun i : {i : ι // i ≠ r} => μ i)) := by
  rw [(indepFun_coordinate_rest μ r).map_prod_eq_prod_map_map
    (measurable_pi_apply r).aemeasurable
      ((measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1)).aemeasurable)]
  rw [Measure.infinitePi_map_eval,
    Measure.map_infinitePi_infinitePi_of_inj Subtype.val_injective]

theorem map_fairSpin_rest (d : ℕ) (r : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (fairSpin (U r), fun v : {v : TreeVertex d // v ≠ r} => U v)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : {v : TreeVertex d // v ≠ r} => uniform01)) := by
  change (Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map _ = _
  have hrest : Measurable
      (fun U : TreeVertex d → ℝ => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v)) :=
    (measurable_pi_apply r).prodMk
      (measurable_pi_iff.mpr (fun i => measurable_pi_apply i.1))
  calc
    _ = ((Measure.infinitePi (fun _ : TreeVertex d => uniform01)).map
        (fun U => (U r, fun v : {v : TreeVertex d // v ≠ r} => U v))).map
          (Prod.map fairSpin id) := by
      rw [Measure.map_map (measurable_fairSpin.prodMap measurable_id) hrest]
      rfl
    _ = _ := by
      rw [map_coordinate_rest,
        ← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]

end Problem367.LabelDecomposition

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Parents
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

theorem treeAdj_length {d : ℕ} {u v : TreeVertex d} (h : treeAdj u v) :
    v.1.length = u.1.length + 1 ∨ u.1.length = v.1.length + 1 := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · left; simp [hc]
  · right; simp [hc]

theorem treeAdj_parent_of_length_lt {d : ℕ} {u v : TreeVertex d}
    (h : treeAdj u v) (hlt : u.1.length < v.1.length) : parentVertex v = u := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · have hlen : u.1.length = v.1.length + 1 := by simp [hc]
    omega

theorem treeAdj_lower_unique {d : ℕ} {u v w : TreeVertex d}
    (hu : treeAdj u w) (hv : treeAdj v w)
    (huw : u.1.length < w.1.length) (hvw : v.1.length < w.1.length) : u = v := by
  exact (treeAdj_parent_of_length_lt hu huw).symm.trans
    (treeAdj_parent_of_length_lt hv hvw)

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_Cardinality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem367

private lemma mem_inducedEdges_8911 {d : ℕ} (D : Finset (TreeVertex d))
    (u v : TreeVertex d) :
    (u, v) ∈ inducedEdges D ↔
      (u ∈ D ∧ v ∈ D) ∧ treeAdj u v ∧ u.1.length < v.1.length := by
  classical
  rw [inducedEdges, Finset.mem_filter]
  exact and_congr Finset.mem_product Iff.rfl

lemma inducedEdges_snd_injOn {d : ℕ} (D : Finset (TreeVertex d)) :
    Set.InjOn Prod.snd (↑(inducedEdges D) : Set (TreeVertex d × TreeVertex d)) := by
  rintro ⟨a, b⟩ hab ⟨c, e⟩ hce heq
  have hab' : (a ∈ D ∧ b ∈ D) ∧ treeAdj a b ∧ a.1.length < b.1.length := by
    exact (mem_inducedEdges_8911 D a b).mp hab
  have hce' : (c ∈ D ∧ e ∈ D) ∧ treeAdj c e ∧ c.1.length < e.1.length := by
    exact (mem_inducedEdges_8911 D c e).mp hce
  change b = e at heq
  subst e
  exact Prod.ext (treeAdj_lower_unique hab'.2.1 hce'.2.1 hab'.2.2 hce'.2.2) rfl

end Problem367

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcast
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

attribute [local instance] OAI.Problem367.RootedBroadcast.rootedBroadcastMeasurableSingletonSpin
lemma spinMul_comm (a b : IsingSpin) : spinMul a b = spinMul b a := by
  cases a <;> cases b <;> rfl
lemma spinMul_assoc (a b c : IsingSpin) : spinMul (spinMul a b) c = spinMul a (spinMul b c) := by
  cases a <;> cases b <;> cases c <;> rfl
@[simp] lemma spinMul_cancel (a b : IsingSpin) : spinMul a (spinMul a b) = b := by
  rw [← spinMul_assoc, spinMul_self, pos_spinMul]

lemma biasedSpin_pos_mass {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.pos}) = ENNReal.ofReal p := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.pos} = Set.Iic p := by
    ext u
    simp [biasedSpin]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Iic]
  have h : Set.Iic p ∩ Set.Icc 0 1 = Set.Icc 0 p := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun ⟨hu,h0,_⟩ => ⟨h0,hu⟩, fun ⟨h0,hu⟩ => ⟨hu,h0,hu.trans hp1⟩⟩
  rw [h, Real.volume_Icc, sub_zero]

lemma biasedSpin_neg_mass {p : ℝ} (hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    uniform01 ((biasedSpin p) ⁻¹' {IsingSpin.neg}) = ENNReal.ofReal (1-p) := by
  have hpre : (biasedSpin p) ⁻¹' {IsingSpin.neg} = Set.Ioi p := by
    ext u
    simp [biasedSpin, not_le]
  rw [hpre, uniform01, Measure.restrict_apply measurableSet_Ioi]
  have h : Set.Ioi p ∩ Set.Icc 0 1 = Set.Ioc p 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun ⟨hu,_,h1⟩ => ⟨hu,h1⟩, fun ⟨hu,h1⟩ => ⟨hu,hp0.trans hu.le,h1⟩⟩
  rw [h, Real.volume_Ioc]

lemma ofNoise_root {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    ofNoise noise ⟨[], List.isChain_nil⟩ = noise ⟨[], List.isChain_nil⟩ := by
  rw [ofNoise]
  simp

@[simp] lemma noiseFromSpins_ofNoise {d : ℕ} (noise : TreeVertex d → IsingSpin) :
    noiseFromSpins (ofNoise noise) = noise := by
  funext v
  by_cases hv : v.val = []
  · rw [noiseFromSpins, ite_eq_left hv, ofNoise]
    simp [hv]
  · rw [noiseFromSpins, ite_eq_right hv, ofNoise_nonroot noise v hv]
    rw [spinMul_assoc, spinMul_self, spinMul_pos]

@[simp] lemma ofNoise_noiseFromSpins {d : ℕ} (x : TreeVertex d → IsingSpin) :
    ofNoise (noiseFromSpins x) = x := by
  funext v
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise (noiseFromSpins x) v = x v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · rw [ofNoise]
        simp [hnil, noiseFromSpins]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot _ v hnil, ih _ hlt (parent v) rfl,
          noiseFromSpins, ite_eq_right hnil, spinMul_assoc, spinMul_self, spinMul_pos]
  exact h _ v rfl

lemma edgeNoise_mass {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1) (a : IsingSpin) :
    uniform01 ((edgeNoise theta) ⁻¹' {a}) =
      ENNReal.ofReal ((1 + (if a = IsingSpin.pos then theta else -theta)) / 2) := by
  have hp0 : 0 ≤ (1 + theta) / 2 := by linarith
  have hp1 : (1 + theta) / 2 ≤ 1 := by linarith
  cases a
  · rw [edgeNoise, biasedSpin_neg_mass hp0 hp1, ite_eq_right (by decide : IsingSpin.neg ≠ IsingSpin.pos)]
    congr 1
    ring
  · rw [edgeNoise, biasedSpin_pos_mass hp0 hp1]
    rfl

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_SpinEncoding
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma spinAgreementCode_comm (a b : IsingSpin) :
    spinAgreementCode a b = spinAgreementCode b a := by
  cases a <;> cases b <;> rfl

lemma ConnectedFinset.spin_eq_on_iff_root_agreements {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {r : TreeVertex d} (hr : r ∈ D)
    (σ τ : TreeVertex d → IsingSpin) :
    (∀ v ∈ D, σ v = τ v) ↔
      σ r = τ r ∧ ∀ e ∈ inducedEdges D,
        spinAgreementCode (σ e.1) (σ e.2) =
          spinAgreementCode (τ e.1) (τ e.2) := by
  classical
  constructor
  · intro h
    refine ⟨h r hr, ?_⟩
    intro e he
    have heD := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    rw [h e.1 heD.1, h e.2 heD.2]
  · rintro ⟨hroot, hedges⟩
    have step {u v : TreeVertex d} (hu : u ∈ D) (hv : v ∈ D)
        (hadj : treeAdj u v) (heq : σ u = τ u) : σ v = τ v := by
      have hcode : spinAgreementCode (σ u) (σ v) =
          spinAgreementCode (τ u) (τ v) := by
        rcases treeAdj_length hadj with hlen | hlen
        · apply hedges (u, v)
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_product.mpr ⟨hu, hv⟩, hadj, by change u.1.length < v.1.length; omega⟩
        · have his : (v, u) ∈ inducedEdges D := by
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_product.mpr ⟨hv, hu⟩, Or.symm hadj, by change v.1.length < u.1.length; omega⟩
          simpa only [spinAgreementCode_comm (σ v) (σ u),
            spinAgreementCode_comm (τ v) (τ u)] using hedges (v, u) his
      rw [heq] at hcode
      exact spinAgreementCode_injective_right (τ u) hcode
    intro v hv
    have hpath := hD.2 r hr v hv
    induction hpath with
    | refl => exact hroot
    | tail hpath hadj ih => exact step hadj.1 hadj.2.1 hadj.2.2 (ih hadj.1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_RootedBroadcastLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

local instance rootedBroadcastLawMeasurableSingletonSpin : MeasurableSingletonClass IsingSpin :=
  ⟨fun _ => trivial⟩

lemma eq_root_iff {d : ℕ} (v : TreeVertex d) : v = root d ↔ v.val = [] := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply Subtype.ext
    exact h

lemma ofNoise_root_decomposition {d : ℕ} (noise : TreeVertex d → IsingSpin)
    (v : TreeVertex d) :
    ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      ofNoise noise v = spinMul (noise (root d)) (ofNoise (eraseRootNoise noise) v) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hnil : v.val = []
      · have hvroot : v = root d := (eq_root_iff v).mpr hnil
        subst v
        simp [root, ofNoise_root, eraseRootNoise]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise v hnil, ofNoise_nonroot (eraseRootNoise noise) v hnil,
          eraseRootNoise, ite_eq_right hnil, ih _ hlt (parent v) rfl]
        rw [← spinMul_assoc, spinMul_comm (noise v) (noise (root d)), spinMul_assoc]
  exact h _ v rfl

lemma measurable_nonrootNoise (d : ℕ) (theta : ℝ) : Measurable (@nonrootNoise d theta) := by
  apply Measurable.of_eval
  intro v
  by_cases hv : v = root d
  · simpa only [nonrootNoise, dite_eq_left hv] using
      (measurable_const : Measurable (fun _ : NonrootVertex d → ℝ => IsingSpin.pos))
  · simpa only [nonrootNoise, dite_eq_right hv, Function.comp_def] using
      (measurable_edgeNoise theta).comp (measurable_pi_apply (X := fun _ : NonrootVertex d => ℝ) ⟨v, hv⟩)

lemma measurable_rootlessFactor (d : ℕ) (theta : ℝ) : Measurable (@rootlessFactor d theta) :=
  (measurable_ofNoise d).comp (measurable_nonrootNoise d theta)

lemma factor_root_decomposition {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    (v : TreeVertex d) :
    factor theta U v = spinMul (fairSpin (U (root d)))
      (rootlessFactor theta (fun w : NonrootVertex d => U w.val) v) := by
  rw [factor, ofNoise_root_decomposition]
  have heq : eraseRootNoise (inputNoise theta U) =
      nonrootNoise theta (fun w : NonrootVertex d => U w.val) := by
    funext w
    by_cases hw : w = root d
    · subst w
      simp [eraseRootNoise, nonrootNoise]
    · have hnil : w.val ≠ [] := fun h => hw ((eq_root_iff w).mpr h)
      simp [eraseRootNoise, inputNoise, nonrootNoise, hw, hnil]
  rw [heq]
  rfl

lemma factor_edge_agreement {d : ℕ} (theta : ℝ) (U : TreeVertex d → ℝ)
    {u v : TreeVertex d} (huv : treeAdj u v) (hlt : u.val.length < v.val.length) :
    spinAgreementCode (factor theta U u) (factor theta U v) = edgeNoise theta (U v) := by
  have hp : parent v = u := treeAdj_parent_of_length_lt huv hlt
  have hnil : v.val ≠ [] := by
    intro heq
    simp only [heq, List.length_nil] at hlt
    omega
  change spinMul (factor theta U u) (factor theta U v) = _
  change spinMul (ofNoise (inputNoise theta U) u) (ofNoise (inputNoise theta U) v) = _
  rw [ofNoise_nonroot _ v hnil, hp]
  simp only [inputNoise, ite_eq_right hnil]
  rw [spinMul_comm (edgeNoise theta (U v)), spinMul_cancel]

lemma factor_cylinder_event {d : ℕ} (theta : ℝ) (D : Finset (TreeVertex d))
    (hD : ConnectedFinset D) (r : TreeVertex d) (hr : r ∈ D)
    (eta : TreeVertex d → IsingSpin) :
    {U : TreeVertex d → ℝ | ∀ v ∈ D, factor theta U v = eta v} =
      {U | factor theta U r = eta r ∧ ∀ e ∈ inducedEdges D,
        edgeNoise theta (U e.2) = spinAgreementCode (eta e.1) (eta e.2)} := by
  classical
  ext U
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hD.spin_eq_on_iff_root_agreements hr]
  apply and_congr_right
  intro hroot
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  have he' := (Finset.mem_filter.mp he).2
  rw [factor_edge_agreement theta U he'.1 he'.2]

lemma edgeVertex_injective {d : ℕ} (D : Finset (TreeVertex d)) :
    Function.Injective (edgeVertex D) := by
  intro a b hab
  apply Subtype.ext
  apply inducedEdges_snd_injOn D a.property b.property
  exact congrArg Subtype.val hab

lemma nonroot_edge_event_mass {d : ℕ} {theta : ℝ} (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))
      {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
        spinAgreementCode (eta e.val.1) (eta e.val.2)} =
      ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  classical
  let A : Set ((e : inducedEdges D) → ℝ) := Set.pi Set.univ
    (fun e => edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)})
  have hA : MeasurableSet A := MeasurableSet.univ_pi
    (fun e => (measurable_edgeNoise theta) (measurableSet_singleton _))
  have hm : Measurable (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e)) := by
    fun_prop
  calc
    _ = (Measure.map (fun Y : NonrootVertex d → ℝ => fun e : inducedEdges D => Y (edgeVertex D e))
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) A := by
      rw [Measure.map_apply hm hA]
      congr 1
      ext Y
      simp [A, Set.mem_pi]
    _ = (Measure.infinitePi (fun _ : inducedEdges D => uniform01)) A := by
      rw [Measure.map_infinitePi_infinitePi_of_inj (edgeVertex_injective D)]
    _ = ∏ e : inducedEdges D, uniform01
        (edgeNoise theta ⁻¹' {spinAgreementCode (eta e.val.1) (eta e.val.2)}) := by
      simpa only [A, Finset.coe_univ] using
        (Measure.infinitePi_pi (fun _ : inducedEdges D => uniform01)
          (s := Finset.univ) (fun e _ => (measurable_edgeNoise theta)
            (measurableSet_singleton (spinAgreementCode (eta e.val.1) (eta e.val.2)))))
    _ = _ := by
      simp only [edgeNoise_mass h0 h1, spinAgreementCode_eq_pos_iff]
      exact Finset.prod_coe_sort (inducedEdges D) (fun e : TreeVertex d × TreeVertex d =>
        ENNReal.ofReal ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2))

lemma freeCylinderWeight_eq_edge_product {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta D eta =
      (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
  unfold freeCylinderWeight
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  rw [ENNReal.ofReal_prod_of_nonneg]
  · norm_num [ENNReal.ofReal_div_of_pos]
  · intro e he
    split_ifs <;> linarith

lemma hasFreeIsingLaw_of_root_nonroot_joint {d : ℕ} {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (hjoint : ∀ r : TreeVertex d,
      (labelMeasure d).map (fun U => (factor theta U r, fun w : NonrootVertex d => U w.val)) =
        (uniform01.map fairSpin).prod (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) :
    HasFreeIsingLaw theta ((labelMeasure d).map (factor theta)) := by
  classical
  intro D hD eta
  obtain ⟨r, hr⟩ := hD.1
  let A : Set (NonrootVertex d → ℝ) :=
    {Y | ∀ e : inducedEdges D, edgeNoise theta (Y (edgeVertex D e)) =
      spinAgreementCode (eta e.val.1) (eta e.val.2)}
  have hA : MeasurableSet A := by
    simp only [A, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact ((measurable_edgeNoise theta).comp (measurable_pi_apply (edgeVertex D e)))
      (measurableSet_singleton _)
  have hS : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} :=
    MeasurableSet.pi D.countable_toSet (fun v _ => measurableSet_singleton (eta v))
  have hm : Measurable (fun U : TreeVertex d → ℝ =>
      (factor theta U r, fun w : NonrootVertex d => U w.val)) := by
    exact ((measurable_pi_apply r).comp (measurable_factor d theta)).prodMk
      (Measurable.of_eval (fun w => measurable_pi_apply w.val))
  rw [Measure.map_apply (measurable_factor d theta) hS]
  change (labelMeasure d) {U | ∀ v ∈ D, factor theta U v = eta v} = _
  rw [factor_cylinder_event theta D hD r hr eta]
  calc
    _ = ((labelMeasure d).map (fun U =>
        (factor theta U r, fun w : NonrootVertex d => U w.val))) ({eta r} ×ˢ A) := by
      rw [Measure.map_apply hm ((measurableSet_singleton _).prod hA)]
      congr 1
      ext U
      simp [A, Set.mem_prod, edgeVertex]
    _ = ((uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01))) ({eta r} ×ˢ A) := by
      rw [hjoint r]
    _ = (uniform01.map fairSpin) {eta r} *
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A :=
      Measure.prod_prod _ _
    _ = (1 / 2 : ENNReal) * ∏ e ∈ inducedEdges D, ENNReal.ofReal
        ((1 + (if eta e.1 = eta e.2 then theta else -theta)) / 2) := by
      rw [Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass]
      rw [show (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) A = _ from
        nonroot_edge_event_mass h0 h1 D eta]
    _ = freeCylinderWeight theta D eta := (freeCylinderWeight_eq_edge_product h0 h1 D eta).symm

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastLocality
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367
namespace RootedBroadcast

lemma ofNoise_congr_prefix {d : ℕ} (noise₁ noise₂ : TreeVertex d → IsingSpin)
    (v : TreeVertex d)
    (heq : ∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) :
    ofNoise noise₁ v = ofNoise noise₂ v := by
  have h : ∀ n : ℕ, ∀ v : TreeVertex d, v.val.length = n →
      (∀ w : TreeVertex d, w.val <+: v.val → noise₁ w = noise₂ w) →
      ofNoise noise₁ v = ofNoise noise₂ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv heq
      by_cases hnil : v.val = []
      · calc
          ofNoise noise₁ v = noise₁ v := by rw [ofNoise]; simp [hnil]
          _ = noise₂ v := heq v (List.prefix_refl _)
          _ = ofNoise noise₂ v := by rw [ofNoise]; simp [hnil]
      · have hlt : (parent v).val.length < n := by
          simp only [parent, parentVertex, List.length_dropLast, ← hv]
          have : 0 < v.val.length := List.length_pos_iff.mpr hnil
          omega
        rw [ofNoise_nonroot noise₁ v hnil, ofNoise_nonroot noise₂ v hnil]
        apply congrArg₂ spinMul (heq v (List.prefix_refl _))
        apply ih _ hlt (parent v) rfl
        intro w hw
        exact heq w (hw.trans (List.dropLast_prefix v.val))
  exact h _ v rfl heq

lemma prefix_in_branch_or_root {d : ℕ} (c : Fin d)
    {u v : TreeVertex d} (hv : [c] <+: v.val) (huv : u.val <+: v.val) :
    u.val = [] ∨ [c] <+: u.val := by
  by_cases hu : u.val = []
  · exact Or.inl hu
  · right
    apply List.prefix_of_prefix_length_le hv huv
    have : 0 < u.val.length := List.length_pos_iff.mpr hu
    simpa only [List.length_singleton] using Nat.succ_le_of_lt this

lemma measurable_branchNoise {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (fun p : IsingSpin × (BranchVertex c → ℝ) => branchNoise theta c p.1 p.2) := by
  apply Measurable.of_eval
  intro v
  by_cases hnil : v.val = []
  · simpa only [branchNoise, ite_eq_left hnil] using
      (measurable_fst : Measurable (Prod.fst : IsingSpin × (BranchVertex c → ℝ) → IsingSpin))
  · by_cases hv : [c] <+: v.val
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_left hv, Function.comp_def] using
        (measurable_edgeNoise theta).comp
          ((measurable_pi_apply (X := fun _ : BranchVertex c => ℝ) ⟨v,hv⟩).comp measurable_snd)
    · simpa only [branchNoise, ite_eq_right hnil, dite_eq_right hv] using
        (measurable_const : Measurable (fun _ : IsingSpin × (BranchVertex c → ℝ) => IsingSpin.pos))

lemma measurable_branchFactor {d : ℕ} (theta : ℝ) (c : Fin d) :
    Measurable (branchFactor theta c) := by
  apply Measurable.of_eval
  intro v
  exact (measurable_ofNoise_apply v.val).comp (measurable_branchNoise theta c)

lemma factor_branch_representation {d : ℕ} (theta : ℝ) (c : Fin d)
    (U : TreeVertex d → ℝ) :
    (fun v : BranchVertex c => factor theta U v.val) =
      branchFactor theta c (fairSpin (U (root d)), fun v : BranchVertex c => U v.val) := by
  funext v
  apply ofNoise_congr_prefix
  intro w hw
  rcases prefix_in_branch_or_root c v.property hw with hnil | hbranch
  · have heq : w = root d := (eq_root_iff w).mpr hnil
    subst w
    simp [inputNoise, branchNoise]
  · have hnil : w.val ≠ [] := by
      intro heq
      rw [heq] at hbranch
      have hl := hbranch.length_le
      simp at hl
    simp [inputNoise, branchNoise, hnil, hbranch]

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchLabels
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
namespace Problem367

namespace RootedBroadcast

lemma branch_disjoint {d : ℕ} {c e : Fin d} (hce : c ≠ e) :
    Disjoint {v : TreeVertex d | [c] <+: v.val} {v | [e] <+: v.val} := by
  apply Set.disjoint_left.mpr
  intro v hc he
  have hprefix : [c] <+: [e] := List.prefix_of_prefix_length_le hc he (by simp)
  have heq : [c] = [e] := hprefix.eq_of_length (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hce (by simpa only [List.singleton_inj] using heq)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastBranchFamily
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367.RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_UniformTwist
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Twist
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance localInst_ra1e236_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem measurePreserving_fairSpin_mul (b : IsingSpin) :
    MeasurePreserving (fun a => spinMul a b)
      (uniform01.map fairSpin) (uniform01.map fairSpin) := by
  have hm : Measurable (fun a => spinMul a b) := measurable_of_finite _
  refine ⟨hm, ?_⟩
  apply Measure.ext_of_singleton
  intro a
  have hpre : (fun x => spinMul x b) ⁻¹' {a} = {spinMul a b} := by
    ext x
    cases x <;> cases a <;> cases b <;> simp [spinMul]
  rw [Measure.map_apply hm (measurableSet_singleton a), hpre,
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _),
    Measure.map_apply measurable_fairSpin (measurableSet_singleton _), fairSpin_mass,
    fairSpin_mass]

theorem measurePreserving_fairSpin_twist
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    {f : Y → IsingSpin} (hf : Measurable f) :
    MeasurePreserving (fun p : IsingSpin × Y => (spinMul p.1 (f p.2), p.2))
      ((uniform01.map fairSpin).prod ν) ((uniform01.map fairSpin).prod ν) := by
  apply measurePreserving_fiberTwist (uniform01.map fairSpin) ν
    (fun y a => spinMul a (f y))
  · exact measurable_spinMul.comp (measurable_fst.prodMk (hf.comp measurable_snd))
  · intro y
    exact measurePreserving_fairSpin_mul (f y)

end RootedBroadcast
end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_BroadcastJointLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367.RootedBroadcast

theorem map_factor_rest (d : ℕ) (theta : ℝ) (v : TreeVertex d) :
    (labelMeasure d).map
      (fun U => (factor theta U v, fun w : NonrootVertex d => U w.val)) =
      (uniform01.map fairSpin).prod
        (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) := by
  have hf : Measurable (fun Y : NonrootVertex d → ℝ => rootlessFactor theta Y v) :=
    (measurable_pi_apply v).comp (measurable_rootlessFactor d theta)
  have ht := measurePreserving_fairSpin_twist
    (Measure.infinitePi (fun _ : NonrootVertex d => uniform01)) hf
  have hj : Measurable (fun U : TreeVertex d → ℝ =>
      (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val)) :=
    (measurable_fairSpin.comp (measurable_pi_apply (root d))).prodMk
      (measurable_pi_iff.mpr (fun w => measurable_pi_apply w.val))
  calc
    _ = ((labelMeasure d).map
        (fun U => (fairSpin (U (root d)), fun w : NonrootVertex d => U w.val))).map
          (fun p : IsingSpin × (NonrootVertex d → ℝ) =>
            (spinMul p.1 (rootlessFactor theta p.2 v), p.2)) := by
      rw [Measure.map_map ht.measurable hj]
      congr 1
      funext U
      exact Prod.ext (factor_root_decomposition theta U v) rfl
    _ = _ := by
      rw [LabelDecomposition.map_fairSpin_rest]
      exact ht.map_eq

end Problem367.RootedBroadcast

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeIsingMeasure
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Problem367

theorem freeIsingMeasure_hasFreeIsingLaw (d : ℕ) {theta : ℝ}
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) :
    HasFreeIsingLaw theta (freeIsingMeasure d theta) :=
  RootedBroadcast.hasFreeIsingLaw_of_root_nonroot_joint h0 h1
    (RootedBroadcast.map_factor_rest d theta)

theorem HasFreeIsingLaw.eq_freeIsingMeasure {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1) : mu = freeIsingMeasure d theta :=
  hmu.unique (freeIsingMeasure_hasFreeIsingLaw d h0 h1)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

theorem map_root_branch_family_of_sampler {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [MeasurableSpace S]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f) :
    (Measure.infinitePi ν).map (fun U => (f (U (root d)),
      fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
        Measure.infinitePi (fun v : BranchVertex c => ν v.val))) := by
  let F : (NonrootVertex d → A) → (∀ c : Fin d, BranchVertex c → A) :=
    fun Y c v => Y (branchEmbedding c v)
  have hF : Measurable F := by fun_prop
  have hind := (LabelDecomposition.indepFun_coordinate_rest ν (root d)).comp hf hF
  have hB : Measurable (fun U : TreeVertex d → A => f (U (root d))) :=
    hf.comp (measurable_pi_apply (root d))
  have hY : Measurable (fun U : TreeVertex d → A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) := by fun_prop
  have hroot : (Measure.infinitePi ν).map (fun U => f (U (root d))) =
      (ν (root d)).map f := by
    change (Measure.infinitePi ν).map (f ∘ (fun U => U (root d))) = _
    rw [← Measure.map_map hf (measurable_pi_apply (root d)), Measure.infinitePi_map_eval]
  change IndepFun (fun U : TreeVertex d → A => f (U (root d)))
    (fun U => fun c : Fin d => fun v : BranchVertex c => U v.val)
    (Measure.infinitePi ν) at hind
  rw [hind.map_prod_eq_prod_map_map hB.aemeasurable hY.aemeasurable, hroot]
  congr 1
  exact infinitePi_map_disjoint_family ν
    (fun c : Fin d => {v : TreeVertex d | [c] <+: v.val})
    (fun _ _ hce => branch_disjoint hce)

theorem iCondIndepFun_root_branch_observables {d : ℕ} {A S : Type*}
    [MeasurableSpace A] [mS : MeasurableSpace S]
    [StandardBorelSpace A] [StandardBorelSpace S]
    {B : Fin d → Type*} [∀ c, MeasurableSpace (B c)]
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (f : A → S) (hf : Measurable f)
    (F : ∀ c, S × (BranchVertex c → A) → B c) (hF : ∀ c, Measurable (F c)) :
    iCondIndepFun
      (mS.comap (fun U : TreeVertex d → A => f (U (root d))))
      (hf.comp (measurable_pi_apply (root d))).comap_le
      (fun c U => F c (f (U (root d)), fun v => U v.val))
      (Measure.infinitePi ν) := by
  let e : (TreeVertex d → A) → S × (∀ c : Fin d, BranchVertex c → A) :=
    fun U => (f (U (root d)), fun c v => U v.val)
  let ρ := ((ν (root d)).map f).prod (Measure.infinitePi (fun c : Fin d =>
    Measure.infinitePi (fun v : BranchVertex c => ν v.val)))
  have he : MeasurePreserving e (Measure.infinitePi ν) ρ :=
    ⟨(hf.comp (measurable_pi_apply (root d))).prodMk (by fun_prop),
      map_root_branch_family_of_sampler ν f hf⟩
  have hbase := iCondIndepFun_latent_infinitePi ((ν (root d)).map f)
    (fun c : Fin d => Measure.infinitePi (fun v : BranchVertex c => ν v.val)) F hF
  have hpull := iCondIndepFun_comp_measurePreserving (Measure.infinitePi ν) ρ e he
    (mS.comap Prod.fst) measurable_fst.comap_le
    (fun c => show Measurable (fun z : S × (∀ c : Fin d, BranchVertex c → A) =>
      F c (z.1, z.2 c)) from by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e] using hpull

theorem map_noisyBroadcast {d : ℕ} {A : Type*} [MeasurableSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (factor theta (fun v => (U v).1), fun v => (U v).2)) =
      (freeIsingMeasure d theta).prod (Measure.infinitePi ν) := by
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fun v => (U v).1), fun v => (U v).2))).map
        (Prod.map (factor theta) id) := by
      rw [Measure.map_map ((measurable_factor d theta).prodMap measurable_id) (by fun_prop)]
      rfl
    _ = _ := by
      rw [infinitePi_map_split_pairs, ← Measure.map_prod_map _ _
        (measurable_factor d theta) measurable_id, Measure.map_id]
      rfl

local instance instMeasurableSingletonClassIsingSpin_2_ra1e236_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem iCondIndepFun_noisy_factor_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let F : ∀ c : Fin d, IsingSpin × (BranchVertex c → ℝ × A) →
      (BranchVertex c → IsingSpin) × (BranchVertex c → A) :=
    fun c p => (branchFactor theta c (p.1, fun v => (p.2 v).1),
      fun v => (p.2 v).2)
  have hF : ∀ c, Measurable (F c) := by
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := iCondIndepFun_root_branch_observables
    (fun v => uniform01.prod (ν v)) (fun p : ℝ × A => fairSpin p.1)
    (measurable_fairSpin.comp measurable_fst) F hF
  have heq : (fun (c : Fin d) (U : TreeVertex d → ℝ × A) => F c (fairSpin (U (root d)).1, fun v => U v.val)) =
      (fun c U => ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
        fun v : BranchVertex c => (U v.val).2)) := by
    funext c U
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  rw [heq] at h
  exact h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_1_ra1e236_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_iCondIndepFun_noisy_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply iCondIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot : (fun U : TreeVertex d → ℝ × A =>
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d)) =
      (fun U => fairSpin (U (RootedBroadcast.root d)).1) := by
    funext U
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.iCondIndepFun_noisy_factor_branches theta ν

theorem HasFreeIsingLaw.iCondIndepFun_noisy_branches {d : ℕ} {theta : ℝ}
    {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)] :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun c z => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact freeIsingMeasure_iCondIndepFun_noisy_branches theta ν

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_NoisyBranchConditionalLaw
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance noisyBranchConditionalLawMeasurableSingletonIsingSpin_ra1e236_1 :
    MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.planted_spin_event_mass
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (v : TreeVertex d) (s : IsingSpin) :
    (μ.prod (Measure.infinitePi ν))
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} = 1 / 2 := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  have hset :
      {z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | z.1 v = s} =
        {x : TreeVertex d → IsingSpin | x v = s} ×ˢ Set.univ := by
    ext z
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one, hμ.marginal]
  norm_num [ENNReal.ofReal_div_of_pos]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_IndependentOwnFamily
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem iIndepFun_option_of_indep_tuple
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {B : Option ι → Type*} [∀ i, MeasurableSpace (B i)]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ∀ i, Ω → B i} (hX : ∀ i, Measurable (X i))
    (hchildren : iIndepFun (fun i => X (some i)) μ)
    (hown : IndepFun (X none) (fun ω i => X (some i) ω) μ) :
    iIndepFun X μ := by
  have hm : Measurable (fun ω i => X (some i) ω) :=
    Measurable.of_eval fun i => hX (some i)
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).mpr
  calc
    μ.map (fun ω i => X i ω) =
        (μ.map (fun ω => ((fun i => X (some i) ω), X none ω))).map
          (MeasurableEquiv.piOptionEquivProd B).symm := by
      rw [Measure.map_map (MeasurableEquiv.measurable _) (hm.prodMk (hX none))]
      congr 1
      funext ω i
      cases i <;> rfl
    _ = ((Measure.pi fun i => μ.map (X (some i))).prod (μ.map (X none))).map
        (MeasurableEquiv.piOptionEquivProd B).symm := by
      rw [hown.symm.map_prod_eq_prod_map_map hm.aemeasurable (hX none).aemeasurable,
        hchildren.map_fun_eq_pi_map (fun i => (hX (some i)).aemeasurable)]
    _ = _ := Measure.pi_map_piOptionEquivProd (fun i => μ.map (X i))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_Flip
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.ConnectedHull.prefix_length _root_.OAI.Problem367.ConnectedHull.prefix_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.inducedEdges_singleton _root_.OAI.Problem367.isingSpin_neg_ne_pos _root_.OAI.Problem367.isingSpin_pos_ne_neg _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.spinSign_mul_self _root_.OAI.Problem367.spinSign_neg _root_.OAI.Problem367.spinSign_pos _root_.OAI.Problem367.spinSign_sq _root_.OAI.Problem367.sum_spinSign _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.transitionKernel_one _root_.OAI.Problem367.transitionKernel_spinSum _root_.OAI.Problem367.transitionKernel_sum _root_.OAI.Problem367.transitionKernel_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.map_flipConfig {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    HasFreeIsingLaw theta (mu.map flipConfig) := by
  intro D hD eta
  have hmeas : MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
    simp only [Set.ofPred_forall]
    apply D.measurableSet_biInter
    intro v hv
    exact (show MeasurableSet ({eta v} : Set IsingSpin) from trivial).preimage
      (measurable_pi_apply v)
  rw [Measure.map_apply measurable_flipConfig hmeas]
  have hpre : flipConfig ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = flipConfig eta v} := by
    ext x
    simp [flipConfig]
  rw [hpre, hmu D hD (flipConfig eta), freeCylinderWeight_flipConfig]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_FreeLawSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem HasFreeIsingLaw.flip_invariant {d : ℕ} {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu) :
    mu.map flipConfig = mu :=
  hmu.map_flipConfig.unique hmu

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_PlantedInformation
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace Problem367.PlantedInformation

open PlantedSymmetry

variable {ι κ : Type*}

theorem measurable_spinSign : Measurable spinSign := by
  intro s hs
  trivial

end Problem367.PlantedInformation

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurable_selectedPosterior {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (rho : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedPosterior rho F v r) :=
  stronglyMeasurable_condExp.measurable.mono (selectedObservationField_le hF v) le_rfl

theorem selectedObservationField_comap_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) (v : ι → TreeVertex d) (g : TreeAut d) :
    (selectedObservationField F v).comap (Prod.map (relabel g) (relabel g)) =
      selectedObservationField F (fun i => g.toEquiv.symm (v i)) := by
  unfold selectedObservationField
  rw [MeasurableSpace.comap_comp]
  rfl

theorem selectedObservationField_eq_of_range_eq {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    (F : IsingSpin → A → B) {v : ι → TreeVertex d} {w : κ → TreeVertex d}
    (hvw : Set.range v = Set.range w) :
    selectedObservationField F v = selectedObservationField F w :=
  le_antisymm (selectedObservationField_le_of_range_subset F hvw.subset)
    (selectedObservationField_le_of_range_subset F hvw.symm.subset)

theorem selectedPosterior_relabel_ae {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
        Prod.map (relabel g) (relabel g) =ᵐ[mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))]
      selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r) := by
  let := hmu.isProbabilityMeasure
  let rho := mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) rho := by
    apply Integrable.of_bound
      ((hsign.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hCE := condExp_comp_measurePreserving rho rho
    (Prod.map (relabel g) (relabel g))
    (PlantedStationarity.measurePreserving_planted_relabel hmu nu g)
    (selectedObservationField F v) (selectedObservationField_le hF v) hi
  rw [selectedObservationField_comap_relabel] at hCE
  exact hCE.symm

theorem selectedPosterior_identDistrib_relabel {d : ℕ} {A B ι : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (r : TreeVertex d) (g : TreeAut d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (fun i => g.toEquiv.symm (v i)) (g.toEquiv.symm r))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have hm := measurable_selectedPosterior
    (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) hF v r
  refine ⟨hm.aemeasurable, (measurable_selectedPosterior _ hF _ _).aemeasurable, ?_⟩
  have hCE := selectedPosterior_relabel_ae hmu nu hF v r g
  have hmp := PlantedStationarity.measurePreserving_planted_relabel hmu nu g
  calc
    _ = Measure.map
        (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r ∘
          Prod.map (relabel g) (relabel g))
        (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
      rw [← Measure.map_map hm hmp.measurable, hmp.map_eq]
    _ = _ := Measure.map_congr hCE

theorem selectedPosterior_identDistrib_of_range_relabel {d : ℕ} {A B ι κ : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (v : ι → TreeVertex d) (w : κ → TreeVertex d) (r s : TreeVertex d) (g : TreeAut d)
    (hregion : Set.range (fun i => g.toEquiv.symm (v i)) = Set.range w)
    (hroot : g.toEquiv.symm r = s) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F v r)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) F w s)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have h := selectedPosterior_identDistrib_relabel hmu nu hF v r g
  simpa only [selectedPosterior, selectedObservationField_eq_of_range_eq F hregion, hroot] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentPosteriorStationarity
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem mem_range_componentIndexVertex {d : ℕ} {c : Fin d} {v : TreeVertex d} :
    v ∈ Set.range (componentIndexVertex (c := c)) ↔ ∃ w, v.1 = c :: w := by
  constructor
  · rintro ⟨⟨n, w⟩, rfl⟩
    exact ⟨w.1, rfl⟩
  · rintro ⟨w, hw⟩
    have hchain : (c :: w).IsChain (fun a b : Fin d => a ≠ b) := by
      rw [← hw]
      exact v.2
    refine ⟨⟨w.length, ⟨w, rfl, hchain⟩⟩, ?_⟩
    exact Subtype.ext hw.symm

theorem range_componentIndexVertex_colorPerm {d : ℕ} (e : Equiv.Perm (Fin d)) (c : Fin d) :
    Set.range (fun u : ComponentIndex c => (colorPermAut e).toEquiv.symm
      (componentIndexVertex u)) = Set.range (componentIndexVertex (c := e.symm c)) := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    apply mem_range_componentIndexVertex.mpr
    refine ⟨u.2.1.map e.symm, ?_⟩
    rfl
  · intro hv
    obtain ⟨w, hw⟩ := mem_range_componentIndexVertex.mp hv
    have hmem : (colorPermAut e).toEquiv v ∈ Set.range (componentIndexVertex (c := c)) := by
      apply mem_range_componentIndexVertex.mpr
      refine ⟨w.map e, ?_⟩
      simp [hw]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ?_⟩
    change (colorPermAut e).toEquiv.symm (componentIndexVertex u) = v
    rw [hu, Equiv.symm_apply_apply]

theorem componentPosterior_identDistrib {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (componentIndexVertex (c := c)) ⟨[c], List.IsChain.singleton c⟩)
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (componentIndexVertex (c := a)) ⟨[a], List.IsChain.singleton a⟩)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  let e : Equiv.Perm (Fin d) := Equiv.swap c a
  have hmap : e.symm c = a := by simp [e]
  apply selectedPosterior_identDistrib_of_range_relabel hmu nu hF
    (componentIndexVertex (c := c)) (componentIndexVertex (c := a))
    ⟨[c], List.IsChain.singleton c⟩ ⟨[a], List.IsChain.singleton a⟩ (colorPermAut e)
  · rw [← hmap]
    exact range_componentIndexVertex_colorPerm e c
  · apply Subtype.ext
    change [e.symm c] = [a]
    rw [hmap]

theorem childComponentPosterior_identDistrib {d : ℕ} {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] {theta : ℝ}
    {mu : Measure (TreeVertex d → IsingSpin)} (hmu : HasFreeIsingLaw theta mu)
    (nu : Measure A) [IsProbabilityMeasure nu]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    IdentDistrib
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (childComponentIndexVertex c a) (prefixFlip c ⟨[a], List.IsChain.singleton a⟩))
      (selectedPosterior (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
        F (componentIndexVertex (c := c)) ⟨[c], List.IsChain.singleton c⟩)
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu)))
      (mu.prod (Measure.infinitePi (fun _ : TreeVertex d => nu))) := by
  have h := selectedPosterior_identDistrib_relabel hmu nu hF
    (componentIndexVertex (c := a)) ⟨[a], List.IsChain.singleton a⟩ (prefixTreeAut c)
  exact h.symm.trans (componentPosterior_identDistrib hmu nu hF a c)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_Descent
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_comp_measurePreserving
    {Ω Ω' C D : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (e : Ω → Ω') (he : MeasurePreserving e μ ν)
    (m : MeasurableSpace Ω') (hm : m ≤ mΩ')
    {f : Ω' → C} {g : Ω' → D}
    (hf : @Measurable Ω' C mΩ' _ f) (hg : @Measurable Ω' D mΩ' _ g)
    (hfg : CondIndepFun (m.comap e)
      ((MeasurableSpace.comap_mono hm).trans (@Measurable.comap_le Ω Ω' mΩ mΩ' e
        (@MeasurePreserving.measurable Ω Ω' mΩ mΩ' e μ ν he)))
      (f ∘ e) (g ∘ e) μ) : CondIndepFun m hm f g ν := by
  let : MeasurableSpace Ω' := mΩ'
  classical
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro U V hU hV
  have hE := hU.preimage hf
  have hH := hV.preimage hg
  have hCE := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hE)
  have hCH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator hH)
  have hCEH := condExp_comp_measurePreserving μ ν e he m hm
    ((integrable_const (1 : ℝ)).indicator (hE.inter hH))
  have hmul := (condIndepFun_iff_condExp_inter_preimage_eq_mul
    (hf.comp he.measurable) (hg.comp he.measurable)).mp hfg U V hU hV
  have hmeas : MeasurableSet {ω' | (ν⟦f ⁻¹' U ∩ g ⁻¹' V | m⟧) ω' =
      (ν⟦f ⁻¹' U | m⟧) ω' * (ν⟦g ⁻¹' V | m⟧) ω'} :=
    measurableSet_eq_fun (stronglyMeasurable_condExp.mono hm).measurable
      ((stronglyMeasurable_condExp.mono hm).measurable.mul
        (stronglyMeasurable_condExp.mono hm).measurable)
  have hdesc := ae_map_iff (μ := μ) he.measurable.aemeasurable hmeas
  rw [he.map_eq] at hdesc
  apply hdesc.mpr
  filter_upwards [hCE, hCH, hCEH, hmul] with ω hωE hωH hωEH hωmul
  exact hωEH.symm.trans (hωmul.trans (congrArg₂ (· * ·) hωE hωH))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_LatentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_product_jointLaw
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hjoint : Measure.map (fun ω => (Z ω, X ω, Y ω)) P = ρ.prod (μ.prod ν))
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  have he : MeasurePreserving (fun ω => (Z ω, X ω, Y ω)) P (ρ.prod (μ.prod ν)) :=
    ⟨hZ.prodMk (hX.prodMk hY), hjoint⟩
  have hbase := condIndepFun_latent_product ρ μ ν F G hF hG
  have hpull := condIndepFun_comp_measurePreserving P (ρ.prod (μ.prod ν))
    (fun ω => (Z ω, X ω, Y ω)) he (mS.comap Prod.fst) measurable_fst.comap_le
    (show Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) by fun_prop)
    (show Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hpull

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyRootIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367
namespace RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_3_ra1e236_1 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem map_root_ownNoise_branch_family {d : ℕ} {A : Type*}
    [MeasurableSpace A] (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.infinitePi (fun v => uniform01.prod (ν v))).map
      (fun U : TreeVertex d → ℝ × A =>
        (fairSpin (U (root d)).1, (U (root d)).2,
          fun c : Fin d => fun v : BranchVertex c => U v.val)) =
      (uniform01.map fairSpin).prod ((ν (root d)).prod
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))) := by
  have hbase := map_root_branch_family_of_sampler
    (fun v => uniform01.prod (ν v))
    (fun p : ℝ × A => (fairSpin p.1, p.2))
    ((measurable_fairSpin.comp measurable_fst).prodMk measurable_snd)
  have hroot : (uniform01.prod (ν (root d))).map
      (fun p : ℝ × A => (fairSpin p.1, p.2)) =
      (uniform01.map fairSpin).prod (ν (root d)) := by
    change (uniform01.prod (ν (root d))).map (Prod.map fairSpin id) = _
    rw [← Measure.map_prod_map _ _ measurable_fairSpin measurable_id, Measure.map_id]
  rw [hroot] at hbase
  calc
    _ = ((Measure.infinitePi (fun v => uniform01.prod (ν v))).map
        (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val))).map
          MeasurableEquiv.prodAssoc := by
      have hmf : Measurable (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1) :=
        (measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d))
      have hm : Measurable (fun U : TreeVertex d → ℝ × A =>
          ((fairSpin (U (root d)).1, (U (root d)).2),
            fun c : Fin d => fun v : BranchVertex c => U v.val)) :=
        (hmf.prodMk (by fun_prop)).prodMk (by fun_prop)
      rw [Measure.map_map (by fun_prop) hm]
      rfl
    _ = _ := by
      rw [hbase]
      exact (measurePreserving_prodAssoc (uniform01.map fairSpin) (ν (root d))
        (Measure.infinitePi (fun c : Fin d =>
          Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))).map_eq

theorem condIndepFun_noisy_factor_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun U : TreeVertex d → ℝ × A => fairSpin (U (root d)).1))
      ((measurable_fairSpin.comp measurable_fst).comp
        (measurable_pi_apply (root d))).comap_le
      (fun U => (fairSpin (U (root d)).1, (U (root d)).2))
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2))
      (Measure.infinitePi (fun v => uniform01.prod (ν v))) := by
  let G : IsingSpin × (∀ c : Fin d, BranchVertex c → ℝ × A) →
      (∀ c : Fin d, (BranchVertex c → IsingSpin) × (BranchVertex c → A)) :=
    fun p c => (branchFactor theta c (p.1, fun v => (p.2 c v).1),
      fun v => (p.2 c v).2)
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro c
    exact ((measurable_branchFactor theta c).comp
      (measurable_fst.prodMk (by fun_prop))).prodMk (by fun_prop)
  have h := condIndepFun_of_product_jointLaw
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    (uniform01.map fairSpin) (ν (root d))
    (Measure.infinitePi (fun c : Fin d =>
      Measure.infinitePi (fun v : BranchVertex c => uniform01.prod (ν v.val))))
    ((measurable_fairSpin.comp measurable_fst).comp (measurable_pi_apply (root d)))
    (measurable_snd.comp (measurable_pi_apply (root d)))
    (show Measurable (fun U : TreeVertex d → ℝ × A =>
      fun c : Fin d => fun v : BranchVertex c => U v.val) from by fun_prop)
    (map_root_ownNoise_branch_family ν) id G measurable_id hG
  have hfun : (fun U : TreeVertex d → ℝ × A =>
      G (fairSpin (U (root d)).1, fun c v => U v.val)) =
      (fun U => fun c : Fin d =>
        ((fun v : BranchVertex c => factor theta (fun w => (U w).1) v.val),
          fun v : BranchVertex c => (U v.val).2)) := by
    funext U c
    apply Prod.ext
    · exact (factor_branch_representation theta c (fun w => (U w).1)).symm
    · rfl
  simpa only [Function.comp_def, id_eq, hfun] using h

end RootedBroadcast

local instance instMeasurableSingletonClassIsingSpin_2_ra1e236_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem freeIsingMeasure_condIndepFun_noisy_root_branches {d : ℕ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    (theta : ℝ) (ν : TreeVertex d → Measure A)
    [∀ v, IsProbabilityMeasure (ν v)] :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) := by
  let e : (TreeVertex d → ℝ × A) →
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) :=
    fun U => (RootedBroadcast.factor theta (fun v => (U v).1), fun v => (U v).2)
  have he : MeasurePreserving e (Measure.infinitePi (fun v => uniform01.prod (ν v)))
      ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) :=
    ⟨((RootedBroadcast.measurable_factor d theta).comp (by fun_prop)).prodMk
      (by fun_prop), RootedBroadcast.map_noisyBroadcast theta ν⟩
  apply condIndepFun_of_comp_measurePreserving
    (Measure.infinitePi (fun v => uniform01.prod (ν v)))
    ((freeIsingMeasure d theta).prod (Measure.infinitePi ν)) e he
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from by fun_prop)
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
  have hroot (U : TreeVertex d → ℝ × A) :
      RootedBroadcast.factor theta (fun v => (U v).1) (RootedBroadcast.root d) =
      fairSpin (U (RootedBroadcast.root d)).1 := by
    simp [RootedBroadcast.factor, RootedBroadcast.root,
      RootedBroadcast.ofNoise_root, RootedBroadcast.inputNoise]
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, e, hroot] using
    RootedBroadcast.condIndepFun_noisy_factor_root_branches theta ν

theorem HasFreeIsingLaw.condIndepFun_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (RootedBroadcast.root d)))
      ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
      (fun z => F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d)))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
          fun v : RootedBroadcast.BranchVertex c => z.2 v.val)))
      (μ.prod (Measure.infinitePi ν)) := by
  have heq := hμ.eq_freeIsingMeasure h0 h1
  subst μ
  exact (freeIsingMeasure_condIndepFun_noisy_root_branches theta ν).comp hF hG

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Trees_NoisyBranchTransport
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

local instance instMeasurableSingletonClassIsingSpin_3_ra1e236_2 : MeasurableSingletonClass IsingSpin := ⟨fun _ => trivial⟩
theorem HasFreeIsingLaw.measurePreserving_planted_relabel
    {d : ℕ} {theta : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (ν : Measure A) [IsProbabilityMeasure ν]
    (g : TreeAut d) :
    MeasurePreserving (Prod.map (relabel g) (relabel g))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply (hμ.measurePreserving_relabel g).prod
  exact ⟨measurable_relabel g,
    Measure.map_infinitePi_infinitePi_of_inj g.toEquiv.symm.injective⟩

theorem HasFreeIsingLaw.iCondIndepFun_relabel_noisy_branches
    {d : ℕ} {theta : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (fun c z =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 (g.toEquiv.symm v.val)),
          fun v : RootedBroadcast.BranchVertex c => z.2 (g.toEquiv.symm v.val)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := iCondIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (fun c => show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val)) from by fun_prop)
    (hμ.iCondIndepFun_noisy_branches h0 h1 (fun _ => ν))
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

theorem HasFreeIsingLaw.condIndepFun_relabel_root_branch_observables
    {d : ℕ} {theta : ℝ} {A C D : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ]
    (hμ : HasFreeIsingLaw theta μ) (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν] (g : TreeAut d)
    (F : IsingSpin × A → C)
    (G : (∀ c : Fin d, (RootedBroadcast.BranchVertex c → IsingSpin) ×
      (RootedBroadcast.BranchVertex c → A)) → D)
    (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          z.1 (g.toEquiv.symm (RootedBroadcast.root d))))
      ((measurable_pi_apply (g.toEquiv.symm (RootedBroadcast.root d))).comp
        measurable_fst).comap_le
      (fun z => F (z.1 (g.toEquiv.symm (RootedBroadcast.root d)),
        z.2 (g.toEquiv.symm (RootedBroadcast.root d))))
      (fun z => G (fun c : Fin d =>
        ((fun v : RootedBroadcast.BranchVertex c => z.1 (g.toEquiv.symm v.val)),
          fun v : RootedBroadcast.BranchVertex c => z.2 (g.toEquiv.symm v.val))))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  have h := condIndepFun_comp_measurePreserving
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
    (Prod.map (relabel g) (relabel g)) (hμ.measurePreserving_planted_relabel ν g)
    ((inferInstance : MeasurableSpace IsingSpin).comap
      (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        z.1 (RootedBroadcast.root d)))
    ((measurable_pi_apply (RootedBroadcast.root d)).comp measurable_fst).comap_le
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      F (z.1 (RootedBroadcast.root d), z.2 (RootedBroadcast.root d))) from
      hF.comp (by fun_prop))
    (show Measurable (fun z : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      G (fun c : Fin d => ((fun v : RootedBroadcast.BranchVertex c => z.1 v.val),
        fun v : RootedBroadcast.BranchVertex c => z.2 v.val))) from hG.comp (by fun_prop))
    (hμ.condIndepFun_root_branch_observables h0 h1 (fun _ => ν) F G hF hG)
  simpa only [MeasurableSpace.comap_comp, Function.comp_def, Prod.map, relabel] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_ComponentObservationIndependence
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ColoredPathAverage.colors_eq_cons_pathReducedTailEquiv _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.cutPrefix_appendCutContinuation _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_avoidingTreeCut _root_.OAI.Problem367.mem_restrictedTreeCut _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem HasFreeIsingLaw.iCondIndepFun_child_component_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun a : Fin d => fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : ComponentIndex a => F (p.1 (childComponentIndexVertex c a u))
          (p.2 (childComponentIndexVertex c a u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let v (a : Fin d) (u : ComponentIndex a) : RootedBroadcast.BranchVertex a :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G (a : Fin d) : (RootedBroadcast.BranchVertex a → IsingSpin) ×
      (RootedBroadcast.BranchVertex a → A) → (ComponentIndex a → B) :=
    fun p u => F (p.1 (v a u)) (p.2 (v a u))
  have hG (a : Fin d) : Measurable (G a) := by
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (RootedBroadcast.BranchVertex a → IsingSpin) ×
        (RootedBroadcast.BranchVertex a → A) => (p.1 (v a u), p.2 (v a u))) by fun_prop)
  have h := (hμ.iCondIndepFun_relabel_noisy_branches h0 h1 ν (prefixTreeAut c)).comp G hG
  exact h

theorem HasFreeIsingLaw.iCondIndepFun_forward_child_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    iCondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun a : {a : Fin d // c ≠ a} =>
        fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun u : ComponentIndex a.1 => F (p.1 (childComponentIndexVertex c a.1 u))
          (p.2 (childComponentIndexVertex c a.1 u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  exact Kernel.iIndepFun.precomp Subtype.val_injective
    (hμ.iCondIndepFun_child_component_observations h0 h1 ν hF c)

theorem HasFreeIsingLaw.condIndepFun_own_forward_child_observations
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A] [MeasurableSpace B]
    {μ : Measure (TreeVertex d → IsingSpin)} [IsFiniteMeasure μ] (hμ : HasFreeIsingLaw theta μ)
    (h0 : -1 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c : Fin d) :
    CondIndepFun
      ((inferInstance : MeasurableSpace IsingSpin).comap
        (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
          p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      ((measurable_pi_apply ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))).comp measurable_fst).comap_le
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        F (p.1 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))) (p.2 ((⟨[c], List.IsChain.singleton c⟩ : TreeVertex d))))
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
        fun a : {a : Fin d // c ≠ a} => fun u : ComponentIndex a.1 =>
          F (p.1 (childComponentIndexVertex c a.1 u))
            (p.2 (childComponentIndexVertex c a.1 u)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  let v (a : Fin d) (u : ComponentIndex a) : RootedBroadcast.BranchVertex a :=
    ⟨componentIndexVertex u, by simp [componentIndexVertex, componentVertex]⟩
  let G : (∀ a : Fin d, (RootedBroadcast.BranchVertex a → IsingSpin) ×
      (RootedBroadcast.BranchVertex a → A)) →
      (∀ a : {a : Fin d // c ≠ a}, ComponentIndex a.1 → B) :=
    fun p a u => F ((p a.1).1 (v a.1 u)) ((p a.1).2 (v a.1 u))
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro a
    apply Measurable.of_eval
    intro u
    exact hF.comp (show Measurable (fun p :
      (∀ a : Fin d, (RootedBroadcast.BranchVertex a → IsingSpin) ×
        (RootedBroadcast.BranchVertex a → A)) =>
          ((p a.1).1 (v a.1 u), (p a.1).2 (v a.1 u))) by fun_prop)
  have h := hμ.condIndepFun_relabel_root_branch_observables h0 h1 ν (prefixTreeAut c)
    (Function.uncurry F) G hF hG
  exact h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_ComponentConditionalRecursionInputs
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

private theorem measurable_artanh : Measurable Real.artanh := by
  unfold Real.artanh
  fun_prop

theorem measurable_componentOwnChildFields {d : ℕ} {A : Type*} [MeasurableSpace A]
    (ρ : Measure ((TreeVertex d → IsingSpin) × (TreeVertex d → A)))
    {F : IsingSpin → A → ℝ} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (i : Option {a : Fin d // c ≠ a}) :
    Measurable (componentOwnChildFields ρ F c i) := by
  cases i with
  | none =>
    exact hF.comp (show Measurable (fun p :
      (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      (p.1 (RootedBroadcast.branchRoot c), p.2 (RootedBroadcast.branchRoot c))) by fun_prop)
  | some a => exact measurable_artanh.comp (measurable_selectedPosterior ρ hF _ _)

theorem HasFreeIsingLaw.iIndepFun_component_fields_cond_spin
    {d : ℕ} {θ : ℝ} {A : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (h0 : -1 ≤ θ) (h1 : θ ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → ℝ} (hF : Measurable (Function.uncurry F))
    (c : Fin d) (s : IsingSpin) :
    let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
    iIndepFun (componentOwnChildFields ρ F c)
      ρ[|{p | p.1 (RootedBroadcast.branchRoot c) = s}] := by
  let := hμ.isProbabilityMeasure
  let Ω := (TreeVertex d → IsingSpin) × (TreeVertex d → A)
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  let I := {a : Fin d // c ≠ a}
  let S : Ω → IsingSpin := fun p => p.1 (RootedBroadcast.branchRoot c)
  let X (a : I) (p : Ω) : ComponentIndex a.1 → ℝ :=
    fun u => F (p.1 (childComponentIndexVertex c a.1 u))
      (p.2 (childComponentIndexVertex c a.1 u))
  let Y : Ω → ℝ := componentOwnChildFields ρ F c none
  let Z (a : I) : Ω → ℝ := componentOwnChildFields ρ F c (some a)
  have hS : Measurable S := (measurable_pi_apply _).comp measurable_fst
  have hX (a : I) : Measurable (X a) :=
    Measurable.of_eval fun u => hF.comp (show Measurable (fun p : Ω =>
      (p.1 (childComponentIndexVertex c a.1 u),
       p.2 (childComponentIndexVertex c a.1 u))) from
      ((measurable_pi_apply _).comp measurable_fst).prodMk
        ((measurable_pi_apply _).comp measurable_snd))
  have hY : Measurable Y := measurable_componentOwnChildFields ρ hF c none
  have hZ (a : I) : Measurable (Z a) :=
    measurable_componentOwnChildFields ρ hF c (some a)
  have hmass : ρ (S ⁻¹' {s}) ≠ 0 := by
    change ρ {p | p.1 (RootedBroadcast.branchRoot c) = s} ≠ 0
    rw [hμ.planted_spin_event_mass]
    norm_num
  let : IsProbabilityMeasure ρ[|S ⁻¹' {s}] := cond_isProbabilityMeasure hmass
  have hchildren : iIndepFun X ρ[|S ⁻¹' {s}] :=
    iIndepFun_cond_fiber_of_iCondIndepFun hS hX
      (hμ.iCondIndepFun_forward_child_observations h0 h1 ν hF c) s hmass
  have hown : IndepFun Y (fun p a => X a p) ρ[|S ⁻¹' {s}] :=
    indepFun_cond_fiber_of_condIndepFun hS hY (Measurable.of_eval hX)
      (hμ.condIndepFun_own_forward_child_observations h0 h1 ν hF c) s
  have hsmall (a : I) :
      Measurable[MeasurableSpace.comap (X a) inferInstance, inferInstance] (Z a) :=
    measurable_artanh.comp stronglyMeasurable_condExp.measurable
  have hZchildren : iIndepFun Z ρ[|S ⁻¹' {s}] :=
    iIndep_of_iIndep_of_le hchildren (fun a => (hsmall a).comap_le)
  have hZown : IndepFun Y (fun p a => Z a p) ρ[|S ⁻¹' {s}] := by
    apply indep_of_indep_of_le hown le_rfl
    rw [MeasurableSpace.comap_process_pi, MeasurableSpace.comap_process_pi]
    exact iSup_mono fun a => (hsmall a).comap_le
  change iIndepFun (componentOwnChildFields ρ F c) ρ[|S ⁻¹' {s}]
  exact iIndepFun_option_of_indep_tuple (μ := ρ[|S ⁻¹' {s}])
    (measurable_componentOwnChildFields ρ hF c) hZchildren hZown

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_LinearSignalTilt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem integral_eq_zero_of_ae_sign_reversal {Ω : Type*} [MeasurableSpace Ω]
    {mu : Measure Ω} (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T mu mu)
    {f : Ω → ℝ} (hf : ∀ᵐ x ∂mu, f (T x) = -f x) : (∫ x, f x ∂mu) = 0 := by
  have h := hT.integral_comp' f
  rw [integral_congr_ae hf, integral_neg] at h
  linarith

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorSymmetry
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem measurePreserving_plantedMarkFlip {d : ℕ} {A : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν) :
    MeasurePreserving (plantedMarkFlipEquiv d A)
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let := hμ.isProbabilityMeasure
  have hm : (Measure.infinitePi (fun _ : TreeVertex d => ν)).map Neg.neg =
      Measure.infinitePi (fun _ : TreeVertex d => ν) := by
    change (Measure.infinitePi (fun _ : TreeVertex d => ν)).map
      (fun z i => -z i) = _
    rw [Measure.infinitePi_map_pi _ (fun _ => measurable_neg)]
    simp only [hν]
  exact (show MeasurePreserving flipConfig μ μ from
    ⟨measurable_flipConfig, hμ.flip_invariant⟩).prod
    (show MeasurePreserving Neg.neg
      (Measure.infinitePi (fun _ : TreeVertex d => ν))
      (Measure.infinitePi (fun _ : TreeVertex d => ν)) from ⟨measurable_neg, hm⟩)

theorem measurable_plantedMarkFlip_selectedObservationField
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B]
    (F : IsingSpin → A → B)
    (hodd : ∀ s z, F s.flip (-z) = -F s z) (v : ι → TreeVertex d) :
    Measurable[selectedObservationField F v, selectedObservationField F v]
      (plantedMarkFlipEquiv d A) := by
  apply measurable_comap_iff.mpr
  have heq : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      fun i => F (p.1 (v i)) (p.2 (v i))) ∘ plantedMarkFlipEquiv d A =
      fun p i => -F (p.1 (v i)) (p.2 (v i)) := by
    funext p i
    exact hodd (p.1 (v i)) (p.2 (v i))
  rw [heq]
  exact (comap_measurable (fun p : (TreeVertex d → IsingSpin) ×
    (TreeVertex d → A) => fun i => F (p.1 (v i)) (p.2 (v i)))).neg

theorem selectedPosterior_flip_ae {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {θ : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r ∘
      plantedMarkFlipEquiv d A =ᵐ[μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))]
      -selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r := by
  let := hμ.isProbabilityMeasure
  let ρ := μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))
  have hi : Integrable (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ρ := by
    have hs : Measurable spinSign := by intro s hs; trivial
    apply Integrable.of_bound
      ((hs.comp ((measurable_pi_apply r).comp measurable_fst)).aestronglyMeasurable) 1
    apply Filter.Eventually.of_forall
    intro p
    cases hs : p.1 r <;> norm_num [spinSign, hs]
  have hm := measurable_plantedMarkFlip_selectedObservationField F hodd v
  have hn := condExp_comp_measurePreserving_equiv
    (selectedObservationField_le hF v) (plantedMarkFlipEquiv d A)
    (measurePreserving_plantedMarkFlip hμ ν hν) hm hm hi
  have ho : (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) =>
      spinSign (p.1 r)) ∘ plantedMarkFlipEquiv d A =
      -(fun p => spinSign (p.1 r)) := by
    funext p
    cases hs : p.1 r <;>
      simp [plantedMarkFlipEquiv, flipConfig, IsingSpin.flip, spinSign, hs]
  rw [ho] at hn
  exact hn.trans (condExp_neg _ _)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Spins_PosteriorTilt
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingSpin.flip_eq_iff _root_.OAI.Problem367.IsingSpin.flip_flip _root_.OAI.Problem367.IsingSpin.toReal_neg _root_.OAI.Problem367.IsingSpin.toReal_pos _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.extendFiniteSpin_apply _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.flipConfig_apply _root_.OAI.Problem367.flipConfig_flipConfig _root_.OAI.Problem367.flipConfig_preimage_spin _root_.OAI.Problem367.freeCylinderWeight_flipConfig _root_.OAI.Problem367.freeCylinderWeight_singleton _root_.OAI.Problem367.restrict_extendFiniteSpin _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Problem367

theorem setIntegral_spin_posterior_tilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    {F : Ω → ℝ} (hF : StronglyMeasurable[mSmall] F) (hFi : Integrable F mu)
    (a : IsingSpin) :
    ∫ x in {x | S x = a}, F x ∂mu = (1 / 2 : ℝ) *
      ∫ x, F x * (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hSm : AEStronglyMeasurable (fun x => spinSign (S x)) mu :=
    (hsign.comp hS).aestronglyMeasurable
  have hSb : ∀ᵐ x ∂mu, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro x
    cases hs : S x <;> norm_num [spinSign, hs]
  have hSi : Integrable (fun x => spinSign (S x)) mu := Integrable.of_bound hSm 1 hSb
  have hFSi : Integrable (fun x => F x * spinSign (S x)) mu := hFi.mul_bdd hSm hSb
  have hpull := condExp_mul_of_stronglyMeasurable_left hF hFSi hSi
  have hFMi : Integrable
      (fun x => F x * mu[fun y => spinSign (S y) | mSmall] x) mu :=
    integrable_condExp.congr hpull
  have hint : (∫ x, F x * spinSign (S x) ∂mu) =
      ∫ x, F x * mu[fun y => spinSign (S y) | mSmall] x ∂mu := by
    rw [← integral_condExp (m := mSmall) hm]
    exact integral_congr_ae hpull
  have hA : MeasurableSet {x | S x = a} :=
    (show MeasurableSet ({a} : Set IsingSpin) from trivial).preimage hS
  have hindicator : ({x | S x = a} : Set Ω).indicator F =
      fun x => (1 / 2 : ℝ) * (F x + spinSign a * (F x * spinSign (S x))) := by
    funext x
    cases hs : S x <;> cases a <;> simp [Set.indicator, hs, spinSign] <;> ring
  rw [← integral_indicator hA, hindicator, integral_const_mul,
    integral_add hFi (hFSi.const_mul (spinSign a)), integral_const_mul, hint]
  congr 1
  rw [← integral_const_mul, ← integral_add hFi (hFMi.const_mul (spinSign a))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by ring)

theorem integral_cond_spin_posterior_tilt
    {Ω : Type*} {mSmall m : MeasurableSpace Ω} {mu : Measure Ω} [IsFiniteMeasure mu]
    (hm : mSmall ≤ m) {S : Ω → IsingSpin} (hS : Measurable S)
    {F : Ω → ℝ} (hF : StronglyMeasurable[mSmall] F) (hFi : Integrable F mu)
    (a : IsingSpin) (hfair : mu {x | S x = a} = (1 / 2 : ENNReal)) :
    ∫ x, F x ∂ProbabilityTheory.cond mu {x | S x = a} =
      ∫ x, F x * (1 + spinSign a * mu[fun y => spinSign (S y) | mSmall] x) ∂mu := by
  rw [ProbabilityTheory.cond, integral_smul_measure, hfair]
  rw [setIntegral_spin_posterior_tilt hm hS hF hFi a]
  norm_num
  ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_SelectedPosteriorEvenConditioning
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem integral_cond_spin_eq_of_ae_flip
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hflip : ∀ᵐ x ∂μ, S (T x) = (S x).flip)
    {f : Ω → ℝ} (hfm : StronglyMeasurable f) (hfi : Integrable f μ)
    (heven : ∀ᵐ x ∂μ, f (T x) = f x)
    (a : IsingSpin) (hfair : μ {x | S x = a} = (1 / 2 : ENNReal)) :
    (∫ x, f x ∂μ[|{x | S x = a}]) = ∫ x, f x ∂μ := by
  have hsign : Measurable spinSign := by intro s hs; trivial
  have hsm : StronglyMeasurable (fun x => spinSign (S x)) :=
    (hsign.comp hS).stronglyMeasurable
  have hsb : ∀ᵐ x ∂μ, ‖spinSign (S x)‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    cases S x <;> norm_num [spinSign]
  have hsi : Integrable (fun x => spinSign (S x)) μ :=
    Integrable.of_bound hsm.aestronglyMeasurable 1 hsb
  have hfsi : Integrable (fun x => f x * spinSign (S x)) μ :=
    hfi.mul_bdd hsm.aestronglyMeasurable hsb
  have hzero : (∫ x, f x * spinSign (S x) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae_sign_reversal T hT
    filter_upwards [hflip, heven] with x hx hf
    rw [hf, hx]
    cases S x <;> simp [IsingSpin.flip, spinSign]
  have htilt := integral_cond_spin_posterior_tilt (mSmall := inferInstance)
    le_rfl hS hfm hfi a hfair
  have hce : μ[fun x => spinSign (S x) | (inferInstance : MeasurableSpace Ω)] =ᵐ[μ]
      fun x => spinSign (S x) := Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable le_rfl hsm hsi)
  rw [htilt]
  calc
    _ = ∫ x, f x + spinSign a * (f x * spinSign (S x)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hce] with x hx
      rw [hx]
      ring
    _ = _ := by
      rw [integral_add hfi (hfsi.const_mul _), integral_const_mul, hzero]
      ring

theorem identDistrib_cond_spin_of_ae_flip
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (hflip : ∀ᵐ x ∂μ, S (T x) = (S x).flip)
    {F : Ω → ℝ} (hF : Measurable F)
    (heven : ∀ᵐ x ∂μ, F (T x) = F x)
    (a : IsingSpin) (hfair : μ {x | S x = a} = (1 / 2 : ENNReal)) :
    IdentDistrib F F μ[|{x | S x = a}] μ := by
  let : IsProbabilityMeasure μ[|{x | S x = a}] :=
    cond_isProbabilityMeasure (by rw [hfair]; norm_num)
  refine ⟨hF.aemeasurable, hF.aemeasurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hF.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    integral_map hF.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  apply integral_cond_spin_eq_of_ae_flip T hT hS hflip
    (f.continuous.measurable.comp hF).stronglyMeasurable
    (Integrable.of_bound (f.continuous.measurable.comp hF).aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (F x)))
    _ a hfair
  filter_upwards [heven] with x hx
  exact congrArg f hx

theorem selectedPosterior_even_identDistrib_cond_spin
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r w : TreeVertex d)
    {g : ℝ → ℝ} (hg : Measurable g) (hgeven : ∀ x, g (-x) = g x)
    (s : IsingSpin) :
    IdentDistrib
      (fun p => g (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p))
      (fun p => g (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p))
      ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[|{p | p.1 w = s}])
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply identDistrib_cond_spin_of_ae_flip (plantedMarkFlipEquiv d A)
    (measurePreserving_plantedMarkFlip hμ ν hν)
    ((measurable_pi_apply w).comp measurable_fst)
    (Filter.Eventually.of_forall fun _ => rfl)
    (hg.comp (measurable_selectedPosterior _ hF v r))
    _ s (hμ.planted_spin_event_mass (fun _ => ν) w s)
  filter_upwards [selectedPosterior_flip_ae hμ ν hν hF hodd v r] with p hp
  change g (selectedPosterior _ F v r (plantedMarkFlipEquiv d A p)) = _
  change selectedPosterior _ F v r (plantedMarkFlipEquiv d A p) =
    -selectedPosterior _ F v r p at hp
  rw [hp, hgeven]
  rfl

theorem artanh_neg_unrestricted (x : ℝ) : Real.artanh (-x) = -Real.artanh x := by
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · have hn : -x ∈ Set.Ioo (-1 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    apply Real.tanh_injective
    rw [Real.tanh_artanh hn, Real.tanh_neg, Real.tanh_artanh hx]
  · rcases le_or_gt x (-1) with hleft | hleft
    · have hzero := Real.artanh_eq_zero_iff.mpr (Or.inl hleft)
      have hnzero := Real.artanh_eq_zero_iff.mpr
        (Or.inr (Or.inr (show 1 ≤ -x by linarith)))
      rw [hzero, hnzero, neg_zero]
    · have hright : 1 ≤ x := by
        by_contra h
        exact hx ⟨hleft, lt_of_not_ge h⟩
      have hzero := Real.artanh_eq_zero_iff.mpr (Or.inr (Or.inr hright))
      have hnzero := Real.artanh_eq_zero_iff.mpr (Or.inl (show -x ≤ -1 by linarith))
      rw [hzero, hnzero, neg_zero]

private theorem measurable_artanh_evenConditioning : Measurable Real.artanh := by
  unfold Real.artanh
  exact ((measurable_const.add measurable_id).div
    (measurable_const.sub measurable_id)).sqrt.log

theorem selectedField_abs_identDistrib_cond_spin
    {d : ℕ} {A B ι : Type*}
    [AddGroup A] [MeasurableSpace A] [MeasurableNeg A]
    [AddGroup B] [MeasurableSpace B] [MeasurableNeg B] {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (ν : Measure A) [IsProbabilityMeasure ν] (hν : ν.map Neg.neg = ν)
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F))
    (hodd : ∀ s z, F s.flip (-z) = -F s z)
    (v : ι → TreeVertex d) (r w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p)|)
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) F v r p)|)
      ((μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))[|{p | p.1 w = s}])
      (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν))) := by
  apply selectedPosterior_even_identDistrib_cond_spin hμ ν hν hF hodd v r w
    measurable_artanh_evenConditioning.abs _ s
  intro x
  rw [artanh_neg_unrestricted, abs_neg]

theorem HasFreeIsingLaw.selected_gaussian_field_abs_identDistrib_cond_spin
    {d : ℕ} {ι : Type*} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (t : ℝ) (variance : ℝ≥0) (v : ι → TreeVertex d)
    (r w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun a z => t * spinSign a + z) v r p)|)
      (fun p => |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))
        (fun a z => t * spinSign a + z) v r p)|)
      ((μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance))[|{p | p.1 w = s}])
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) variance)) := by
  apply selectedField_abs_identDistrib_cond_spin hμ (gaussianReal 0 variance)
  · simp only [gaussianReal_map_neg, neg_zero]
  · have hs : Measurable spinSign := by intro a ha; trivial
    exact ((hs.comp measurable_fst).const_mul t).add measurable_snd
  · intro a z
    cases a <;> simp [IsingSpin.flip, spinSign] <;> ring

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_Moments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem integral_one_add_abs_pow_gaussian_le {p : ℕ} (hp : 1 ≤ p) :
    (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) ≤ Real.exp (2 * (p : ℝ) ^ 2) := by
  have hpos := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (p : ℝ)
  have hneg := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-(p : ℝ))
  have hmgf (r : ℝ) : (∫ x : ℝ, Real.exp (r * x) ∂gaussianReal 0 1) =
      Real.exp (r ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1)) r
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have htwo : 2 ≤ Real.exp (3 * (p : ℝ) ^ 2 / 2) := by
    nlinarith [Real.add_one_le_exp (3 * (p : ℝ) ^ 2 / 2), sq_nonneg ((p : ℝ) - 1)]
  calc
    (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) ≤
        ∫ x : ℝ, Real.exp ((p : ℝ) * x) + Real.exp (-(p : ℝ) * x)
          ∂gaussianReal 0 1 :=
      integral_mono (integrable_one_add_abs_pow_gaussian p) (hpos.add hneg)
        (fun x => one_add_abs_pow_le_two_exp x p)
    _ = 2 * Real.exp ((p : ℝ) ^ 2 / 2) := by
      rw [integral_add hpos hneg, hmgf, hmgf, neg_sq]
      ring
    _ ≤ Real.exp (3 * (p : ℝ) ^ 2 / 2) * Real.exp ((p : ℝ) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = Real.exp (2 * (p : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem abs_gaussian_observation_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (x : ℝ) :
    |t + Real.sqrt t * x| ≤ Real.sqrt t * (1 + |x|) := by
  calc
    |t + Real.sqrt t * x| ≤ |t| + |Real.sqrt t * x| := abs_add_le _ _
    _ = t + Real.sqrt t * |x| := by rw [abs_of_nonneg ht, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg t)]
    _ ≤ Real.sqrt t + Real.sqrt t * |x| :=
      add_le_add_left (Real.le_sqrt_self_iff.mpr ht1) _
    _ = Real.sqrt t * (1 + |x|) := by ring

theorem integrable_gaussian_observation_abs_pow {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (p : ℕ) :
    Integrable (fun x : ℝ => |t + Real.sqrt t * x| ^ p) (gaussianReal 0 1) := by
  apply ((integrable_one_add_abs_pow_gaussian p).const_mul (Real.sqrt t ^ p)).mono'
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_gaussian_observation_le ht ht1 x) p

theorem integral_gaussian_observation_abs_pow_le {t : ℝ} {p : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hp : 1 ≤ p) :
    (∫ x : ℝ, |t + Real.sqrt t * x| ^ p ∂gaussianReal 0 1) ≤
      Real.exp (2 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
  have hscale : Real.sqrt t ^ p ≤ t ^ ((p : ℝ) / 4) := by
    calc
      Real.sqrt t ^ p = t ^ ((p : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ht.le]
        congr 1
        ring
      _ ≤ t ^ ((p : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (by have : 0 ≤ (p : ℝ) := Nat.cast_nonneg p; linarith)
  calc
    (∫ x : ℝ, |t + Real.sqrt t * x| ^ p ∂gaussianReal 0 1) ≤
        ∫ x : ℝ, Real.sqrt t ^ p * (1 + |x|) ^ p ∂gaussianReal 0 1 := by
      apply integral_mono (integrable_gaussian_observation_abs_pow ht.le ht1 p)
        ((integrable_one_add_abs_pow_gaussian p).const_mul _)
      intro x
      change |t + Real.sqrt t * x| ^ p ≤ Real.sqrt t ^ p * (1 + |x|) ^ p
      rw [← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_gaussian_observation_le ht.le ht1 x) p
    _ = Real.sqrt t ^ p * (∫ x : ℝ, (1 + |x|) ^ p ∂gaussianReal 0 1) :=
      integral_const_mul _ _
    _ ≤ Real.sqrt t ^ p * Real.exp (2 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_one_add_abs_pow_gaussian_le hp) (by positivity)
    _ ≤ t ^ ((p : ℝ) / 4) * Real.exp (2 * (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hscale (Real.exp_nonneg _)
    _ = Real.exp (2 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := mul_comm _ _

theorem integrable_gaussian_observation_abs_pow_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (p : ℕ) :
    Integrable (fun ω => |t + Real.sqrt t * G ω| ^ p) μ := by
  have h := integrable_gaussian_observation_abs_pow ht ht1 p
  rw [← hG.map_eq] at h
  exact h.comp_aemeasurable hG.aemeasurable

theorem integral_gaussian_observation_abs_pow_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {G : Ω → ℝ}
    (hG : HasLaw G (gaussianReal 0 1) μ) {t : ℝ} {p : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hp : 1 ≤ p) :
    (∫ ω, |t + Real.sqrt t * G ω| ^ p ∂μ) ≤
      Real.exp (2 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
  have heq := hG.integral_comp
    (f := fun x : ℝ => |t + Real.sqrt t * x| ^ p) (by fun_prop)
  change (∫ ω, |t + Real.sqrt t * G ω| ^ p ∂μ) = _ at heq
  rw [heq]
  exact integral_gaussian_observation_abs_pow_le ht ht1 hp

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_Attenuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma lipschitzWith_tanh_response : LipschitzWith 1 Real.tanh := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro x
    exact (hasDerivAt_tanh_response x).differentiableAt
  · intro x
    have h : |deriv Real.tanh x| ≤ 1 := by
      rw [(hasDerivAt_tanh_response x).deriv,
        abs_of_nonneg (sub_nonneg.mpr (le_of_lt (Real.tanh_sq_lt_one x)))]
      nlinarith [sq_nonneg (Real.tanh x)]
    exact_mod_cast h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Estimates_MessageFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem367

lemma cavityMessage_abs_le_mul {theta : ℝ} (hθ0 : 0 ≤ theta) (hθ1 : theta ≤ 1) (z : ℝ) :
    |cavityMessage theta z| ≤ theta * |z| := by
  have h := (lipschitzWith_cavityMessage hθ0 hθ1).dist_le_mul z 0
  change dist (cavityMessage theta z) (cavityMessage theta 0) ≤ theta * dist z 0 at h
  simpa only [Real.dist_eq, cavityMessage_zero, sub_zero] using h

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Posterior_SelectedPosteriorField
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem condExp_tanh_bounds_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K)) :
    ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₁]) ω ∧
      (μ[f | m₁]) ω ≤ Real.tanh (X ω + K) := by
  have h₁ : m₁ ≤ m := h₁₂.trans h₂
  have hL : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω - K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.sub stronglyMeasurable_const)
  have hU : StronglyMeasurable[m₁] (fun ω => Real.tanh (X ω + K)) :=
    lipschitzWith_tanh_response.continuous.comp_stronglyMeasurable (hX.add stronglyMeasurable_const)
  have iL : Integrable (fun ω => Real.tanh (X ω - K)) μ := by
    apply Integrable.of_bound (hL.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω - K)).le
  have iU : Integrable (fun ω => Real.tanh (X ω + K)) μ := by
    apply Integrable.of_bound (hU.mono h₁).aestronglyMeasurable 1
    exact ae_of_all μ fun ω => by simpa only [Real.norm_eq_abs] using
      (Real.abs_tanh_lt_one (X ω + K)).le
  have hlo := condExp_mono (m := m₁) iL integrable_condExp
    (hb.mono fun ω hω => hω.1)
  have hhi := condExp_mono (m := m₁) integrable_condExp iU
    (hb.mono fun ω hω => hω.2)
  rw [condExp_of_stronglyMeasurable h₁ hL iL] at hlo
  rw [condExp_of_stronglyMeasurable h₁ hU iU] at hhi
  filter_upwards [hlo, hhi, condExp_condExp_of_le (f := f) h₁₂ h₂] with ω hLω hUω hTω
  rw [hTω] at hLω hUω
  exact ⟨hLω, hUω⟩

theorem condExp_field_bound_of_le
    {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {m₁ m₂ : MeasurableSpace Ω} (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ m)
    {f X : Ω → ℝ} {K : ℝ} (hX : StronglyMeasurable[m₁] X)
    (hb : ∀ᵐ ω ∂μ, (μ[f | m₂]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₂]) ω) - X ω| ≤ K) :
    ∀ᵐ ω ∂μ, (μ[f | m₁]) ω ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh ((μ[f | m₁]) ω) - X ω| ≤ K := by
  have hmono : Monotone Real.tanh := by
    apply monotone_of_deriv_nonneg
    · intro x
      exact (hasDerivAt_tanh_response x).differentiableAt
    · intro x
      rw [(hasDerivAt_tanh_response x).deriv]
      exact (sub_pos.mpr (Real.tanh_sq_lt_one x)).le
  have hs : ∀ᵐ ω ∂μ, Real.tanh (X ω - K) ≤ (μ[f | m₂]) ω ∧
      (μ[f | m₂]) ω ≤ Real.tanh (X ω + K) := by
    filter_upwards [hb] with ω hω
    have hlo := hmono (show X ω - K ≤ Real.artanh ((μ[f | m₂]) ω) by
      linarith [(abs_le.mp hω.2).1])
    have hhi := hmono (show Real.artanh ((μ[f | m₂]) ω) ≤ X ω + K by
      linarith [(abs_le.mp hω.2).2])
    rw [Real.tanh_artanh hω.1] at hlo hhi
    exact ⟨hlo, hhi⟩
  filter_upwards [condExp_tanh_bounds_of_le (m := m) μ h₁₂ h₂ hX hs] with ω hω
  have h := posterior_field_limit_of_tanh_bounds
    (u := fun _ : ℕ => (μ[f | m₁]) ω) tendsto_const_nhds (fun _ => hω)
  exact ⟨h.1, h.2.1⟩

theorem HasFreeIsingLaw.selected_gaussian_posterior_field_bound
    {d : ℕ} {ι : Type*} {β : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw (Real.tanh β) μ)
    (hβ : 0 ≤ β) (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) :
    ∀ᵐ p ∂μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t),
      selectedPosterior (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p ∈ Set.Ioo (-1 : ℝ) 1 ∧
      |Real.artanh (selectedPosterior
        (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))
        (fun s z => (t : ℝ) * spinSign s + z) v r p) -
          PlantedSymmetry.observation t p r| ≤ (d : ℝ) * β := by
  let := hμ.isProbabilityMeasure
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  have hsub : selectedObservationField F v ≤
      PlantedSymmetry.observationSigma (TreeVertex d) t := by
    change selectedObservationField F v ≤ selectedObservationField F id
    apply selectedObservationField_le_of_range_subset F
    intro w hw
    exact ⟨w, rfl⟩
  have hX : StronglyMeasurable[selectedObservationField F v]
      (fun p => PlantedSymmetry.observation t p r) := by
    obtain ⟨i, rfl⟩ := hr
    exact ((measurable_pi_apply i).comp (comap_measurable
      (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
        fun j => F (p.1 (v j)) (p.2 (v j))))).stronglyMeasurable
  exact condExp_field_bound_of_le
    (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)) hsub
    (PlantedSymmetry.observationSigma_le (TreeVertex d) t) hX
    (hμ.gaussian_posterior_field_bound hβ t r)

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_SelectedCriticalFieldMoments
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem measurable_selectedGaussianField {d : ℕ} {ι : Type*}
    (μ : Measure (TreeVertex d → IsingSpin)) (t : ℝ≥0)
    (v : ι → TreeVertex d) (r : TreeVertex d) :
    Measurable (selectedGaussianField μ t v r) := by
  have ha : Measurable Real.artanh := by unfold Real.artanh; fun_prop
  apply ha.comp
  apply measurable_selectedPosterior
  exact ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
    measurable_snd

theorem HasFreeIsingLaw.integrable_selectedGaussianField_abs_pow
    {d : ℕ} {ι : Type*} {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (v : ι → TreeVertex d) (r : TreeVertex d)
    (hr : r ∈ Set.range v) (p : ℕ) :
    Integrable (fun q => |selectedGaussianField μ t v r q| ^ p)
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  apply integrable_abs_pow_of_bounded_perturbation p
    (show 0 ≤ (d : ℝ) * beta + t by positivity)
    (measurable_selectedGaussianField μ t v r).aemeasurable
    (integrable_abs_pow_of_gaussianLaw (gaussianPlanted_noise_hasLaw μ t r) p)
  filter_upwards [hμ.selected_gaussian_posterior_field_bound hb t v r hr] with q hq
  have hs : |(t : ℝ) * spinSign (q.1 r)| = t := by
    cases he : q.1 r <;> simp [spinSign, abs_of_nonneg t.coe_nonneg]
  calc
    |selectedGaussianField μ t v r q - q.2 r| =
        |(selectedGaussianField μ t v r q - observation t q r) +
          (t : ℝ) * spinSign (q.1 r)| := by
      congr 1
      simp only [observation]
      ring
    _ ≤ |selectedGaussianField μ t v r q - observation t q r| +
        |(t : ℝ) * spinSign (q.1 r)| := abs_add_le _ _
    _ ≤ (d : ℝ) * beta + t := by
      rw [hs]
      exact add_le_add hq.2 le_rfl

theorem criticalComponentFieldMomentConstant_pos (d : ℕ) (beta : ℝ) :
    0 < criticalComponentFieldMomentConstant d beta := by
  unfold criticalComponentFieldMomentConstant
  positivity

theorem criticalComponentBaseExponent_ge_two (d : ℕ) (beta : ℝ) :
    2 ≤ criticalComponentBaseExponent d beta := by
  unfold criticalComponentBaseExponent
  linarith [criticalComponentFieldMomentConstant_pos d beta,
    Real.sqrt_nonneg (criticalComponentFieldMomentConstant d beta)]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Conditioning_SelectedFieldConditionedMoments
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.selectedGaussianField_abs_identDistrib_cond_spin
    {d : ℕ} {ι : Type*} {theta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (t : ℝ≥0) (v : ι → TreeVertex d) (r w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib (fun p => |selectedGaussianField μ t v r p|)
      (fun p => |selectedGaussianField μ t v r p|)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 w = s}])
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) :=
  hμ.selected_gaussian_field_abs_identDistrib_cond_spin t t v r w s

theorem HasFreeIsingLaw.childComponentField_cond_abs_identDistrib
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (t : ℝ≥0) (c a : Fin d)
    (w : TreeVertex d) (s : IsingSpin) :
    IdentDistrib
      (fun p => |selectedGaussianField μ t (childComponentIndexVertex c a)
        (prefixFlip c (RootedBroadcast.branchRoot a)) p|)
      (fun p => |selectedGaussianField μ t (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) p|)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 w = s}])
      (μ.prod (gaussianNoiseLaw (TreeVertex d) t)) := by
  have hF : Measurable (Function.uncurry
      (fun (a : IsingSpin) (z : ℝ) => (t : ℝ) * spinSign a + z)) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
      measurable_snd
  have ha : Measurable (fun x : ℝ => |Real.artanh x|) := by
    unfold Real.artanh
    fun_prop
  apply (hμ.selectedGaussianField_abs_identDistrib_cond_spin t
    (childComponentIndexVertex c a) (prefixFlip c (RootedBroadcast.branchRoot a)) w s).trans
  exact (childComponentPosterior_identDistrib hμ (gaussianReal 0 t) hF c a).comp ha

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_OptionResponseReindex
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

variable {Ω ι : Type*} {b : ℕ}

theorem iIndepFun_ownChildFinFamily [MeasurableSpace Ω] (e : Fin b ≃ ι)
    {Z : Option ι → Ω → ℝ} {μ : Measure Ω} (hZ : iIndepFun Z μ) :
    iIndepFun (ownChildFinFamily e Z) μ := by
  exact iIndepFun.precomp (f := Z) (g := (finSuccEquiv b).trans e.optionCongr)
    ((finSuccEquiv b).trans e.optionCongr).injective hZ

theorem measurable_ownChildFinFamily [MeasurableSpace Ω] (e : Fin b ≃ ι)
    {Z : Option ι → Ω → ℝ} (hm : ∀ i, Measurable (Z i)) (i : Fin (b + 1)) :
    Measurable (ownChildFinFamily e Z i) :=
  hm _

theorem sum_response_ownChildFinFamily [Fintype ι] (e : Fin b ≃ ι)
    (Z : Option ι → Ω → ℝ) (psi : ℝ → ℝ) (ω : Ω) :
    (∑ i : Fin (b + 1), Fin.cases (ownChildFinFamily e Z 0 ω)
      (fun j => psi (ownChildFinFamily e Z j.succ ω)) i) =
      Z none ω + ∑ a : ι, psi (Z (some a) ω) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, ownChildFinFamily_zero,
    ownChildFinFamily_succ]
  exact congrArg (fun x : ℝ => Z none ω + x)
    (e.sum_comp (fun a => psi (Z (some a) ω)))

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_UniformResponseMoments
attribute [-instance] _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem exists_measure_uniform_critical_response_moment_and_tail_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {b : ℕ} {theta K0 : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta < 1)
    (hcritical : (b : ℝ) * theta ^ 2 = 1) (hK0 : 0 < K0) :
    ∃ K : ℝ, K0 ≤ K ∧ 0 < K ∧
      ∀ (μ : Measure Ω) (ν : Measure Ξ),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      ∀ (t : ℝ), 0 < t →
      ∀ (Y : Ω → ℝ) (Ycond : Ξ → ℝ) (Z : Fin (b + 1) → Ξ → ℝ)
        (psi : ℝ → ℝ),
      Measurable psi → (∀ z, |psi z| ≤ theta * |z|) →
      (∀ p : ℕ, Integrable (fun ω => |Y ω| ^ p) μ) →
      (∀ p : ℕ, Integrable (fun ω => |Z 0 ω| ^ p) ν) →
      iIndepFun Z ν → (∀ i, Measurable (Z i)) →
      IdentDistrib (fun ω => |Ycond ω|) (fun ω => |Y ω|) ν μ →
      (∀ i : Fin b, IdentDistrib (fun ω => |Z i.succ ω|)
        (fun ω => |Y ω|) ν μ) →
      (∀ᵐ ω ∂ν, Ycond ω =
        ∑ i : Fin (b + 1), Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i) →
      (∀ p : ℕ, (∫ ω, |Z 0 ω| ^ p ∂ν) ≤
        Real.exp (K0 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) →
      (∀ p : ℕ, p < 3 → (∫ ω, |Y ω| ^ p ∂μ) ≤
        Real.exp (K0 * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) →
      (∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
        Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / t) →
        μ {ω | t ^ (1 / 8 : ℝ) < |Y ω|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / t) ^ 2) / (512 * K)))) := by
  obtain ⟨K, hKK0, hK, hlog, hsmall⟩ :=
    exists_critical_moment_constant (m := (b : ℝ) + 1) (by positivity)
      (show 0 < 1 - theta by linarith) (2 * K0)
  have hK0K : K0 ≤ K := by linarith
  have hKpos : 0 < K := hK0.trans_le hK0K
  refine ⟨K, hK0K, hKpos, ?_⟩
  intro μ ν hμ hν t ht Y Ycond Z psi hpsi hcontract hY hOwnInt hZ hmZ
    hCond hChild hEq hOwn hbase
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let X : Fin (b + 1) → Ξ → ℝ :=
    fun i ω => Fin.cases (Z 0 ω) (fun j => psi (Z j.succ ω)) i
  have hXi : iIndepFun X ν := iIndepFun_cavity_response hZ hpsi
  have hmX : ∀ i, Measurable (X i) := by
    intro i
    exact Fin.cases (hmZ 0) (fun j => hpsi.comp (hmZ j.succ)) i
  have hChildMoment (i : Fin b) (p : ℕ) :=
    response_abs_moment_of_identDistrib_abs (hChild i) hpsi (hmZ i.succ)
      hcontract p (hY p)
  have hMom : ∀ i (p : ℕ), Integrable (fun ω => |X i ω| ^ p) ν := by
    intro i p
    exact Fin.cases (hOwnInt p) (fun j => (hChildMoment j p).1) i
  have hRec (p : ℕ) : (∫ ω, |Y ω| ^ p ∂μ) ≤ ∫ ω, |∑ i, X i ω| ^ p ∂ν := by
    apply le_of_eq
    calc
      _ = ∫ ω, |Ycond ω| ^ p ∂ν := (abs_moment_of_identDistrib_abs hCond p).2.symm
      _ = _ := integral_congr_ae (by
        filter_upwards [hEq] with ω hω
        exact congrArg (fun x : ℝ => |x| ^ p) hω)
  have hOwnBound (p : ℕ) : (∫ ω, |X 0 ω| ^ p ∂ν) ≤
      Real.exp (K * (p : ℝ) ^ 2 / 2) * t ^ ((p : ℝ) / 4) := by
    apply (hOwn p).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hKK0) (sq_nonneg (p : ℝ))]
  have hmom : ∀ p : ℕ, (∫ ω, |Y ω| ^ p ∂μ) ≤
      Real.exp (K * (p : ℝ) ^ 2) * t ^ ((p : ℝ) / 4) := by
    apply critical_all_moments_of_independent_recursion htheta htheta1 hcritical hK ht
      hlog hsmall (fun p => ∫ ω, |Y ω| ^ p ∂μ) hXi hmX hMom hRec hOwnBound
      (fun i p => (hChildMoment i p).2)
    intro p hp
    apply (hbase p hp).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hK0K (sq_nonneg _))
  exact ⟨hmom, fun htime => measure_abs_gt_rpow_le_of_moments hKpos ht htime
    (fun p _ => hY p) (fun p _ => hmom p)⟩

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Gaussian_ConditionalNoise
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.freeIsingMeasure_probability
attribute [-simp] _root_.OAI.Problem367.ConnectedHull.pathAssignment_path _root_.OAI.Problem367.ConnectedHull.path_last _root_.OAI.Problem367.ConnectedHull.path_zero _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.RootedBroadcast.flipBranchToComplement_val _root_.OAI.Problem367.RootedBroadcast.noiseFromSpins_ofNoise _root_.OAI.Problem367.RootedBroadcast.ofNoise_noiseFromSpins _root_.OAI.Problem367.RootedBroadcast.pos_spinMul _root_.OAI.Problem367.RootedBroadcast.prefixFlip_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixFlip_root _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_branchRoot _root_.OAI.Problem367.RootedBroadcast.prefixTreeAut_symm_root _root_.OAI.Problem367.RootedBroadcast.spinMul_cancel _root_.OAI.Problem367.RootedBroadcast.spinMul_pos _root_.OAI.Problem367.RootedBroadcast.spinMul_self _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.branchColorAut_length _root_.OAI.Problem367.branchColorAut_singleton _root_.OAI.Problem367.branchColorAut_val _root_.OAI.Problem367.branchColorMap_symm_apply _root_.OAI.Problem367.card_treeBallFinset _root_.OAI.Problem367.card_treeNeighborFinset _root_.OAI.Problem367.colorPermAut_length _root_.OAI.Problem367.colorPermAut_nil _root_.OAI.Problem367.colorPermAut_val _root_.OAI.Problem367.colorPermMap_symm_apply _root_.OAI.Problem367.colorPermMap_val _root_.OAI.Problem367.connectedSpinEncode_apply_root _root_.OAI.Problem367.connectedSpinEquiv_apply _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.finiteFreeIsingPMF_apply _root_.OAI.Problem367.iUnion_treeBallFinset _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.mem_treeBallFinset _root_.OAI.Problem367.mem_treeNeighborFinset _root_.OAI.Problem367.parentVertex_length _root_.OAI.Problem367.parentVertex_val _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.prefixFlip_twice _root_.OAI.Problem367.spinAgreementCode_eq_neg_iff _root_.OAI.Problem367.spinAgreementCode_eq_pos_iff _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.sum_treeShell_zero _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

theorem cond_prod_first_event {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) (ν : Measure A) [SFinite μ] [IsProbabilityMeasure ν]
    (E : Set Ω) :
    (μ.prod ν)[|E ×ˢ Set.univ] = (μ[|E]).prod ν := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, Measure.prod_prod, measure_univ, mul_one,
    ← Measure.restrict_prod_eq_prod_univ, Measure.prod_smul_left]

theorem HasFreeIsingLaw.measurePreserving_noise_cond_spin
    {d : ℕ} {θ : ℝ} {A : Type*} [MeasurableSpace A]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw θ μ)
    (ν : TreeVertex d → Measure A) [∀ v, IsProbabilityMeasure (ν v)]
    (r w : TreeVertex d) (s : IsingSpin) :
    MeasurePreserving (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) => p.2 w)
      (μ.prod (Measure.infinitePi ν))[|{p | p.1 r = s}] (ν w) := by
  let := hμ.isProbabilityMeasure
  have hmass : μ {σ | σ r = s} ≠ 0 := by rw [hμ.marginal]; norm_num
  let : IsProbabilityMeasure μ[|{σ | σ r = s}] := cond_isProbabilityMeasure hmass
  have hset : {p : (TreeVertex d → IsingSpin) × (TreeVertex d → A) | p.1 r = s} =
      {σ : TreeVertex d → IsingSpin | σ r = s} ×ˢ Set.univ := by ext p; simp
  rw [hset, cond_prod_first_event]
  refine ⟨(measurable_pi_apply w).comp measurable_snd, ?_⟩
  change Measure.map ((fun z : TreeVertex d → A => z w) ∘ Prod.snd) _ = _
  rw [← Measure.map_map (measurable_pi_apply w) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul, Measure.infinitePi_map_eval]

theorem HasFreeIsingLaw.gaussian_noise_hasLaw_cond_spin
    {d : ℕ} {θ : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw θ μ) (t : ℝ≥0) (r w : TreeVertex d) (s : IsingSpin) :
    HasLaw (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) => p.2 w)
      (gaussianReal 0 t)
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 r = s}] := by
  exact (hμ.measurePreserving_noise_cond_spin (fun _ => gaussianReal 0 t) r w s).hasLaw

theorem HasFreeIsingLaw.standard_gaussian_hasLaw_cond_spin
    {d : ℕ} {θ : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw θ μ) (t : ℝ≥0) (ht : 0 < t)
    (r w : TreeVertex d) (s : IsingSpin) :
    HasLaw (fun p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) =>
      p.2 w / Real.sqrt t) (gaussianReal 0 1)
      (μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 r = s}] := by
  have h := gaussianReal_div_const (hμ.gaussian_noise_hasLaw_cond_spin t r w s) (Real.sqrt t)
  have hs : t / NNReal.mk ((Real.sqrt t) ^ 2) (sq_nonneg _) = 1 := by
    apply NNReal.eq
    change (t : ℝ) / (Real.sqrt (t : ℝ)) ^ 2 = 1
    rw [Real.sq_sqrt (show (0 : ℝ) ≤ t from t.2),
      div_self (ne_of_gt (show (0 : ℝ) < t from ht))]
  simpa only [zero_div, hs] using h

theorem HasFreeIsingLaw.own_gaussian_observation_cond_pos
    {d : ℕ} {θ : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (_hμ : HasFreeIsingLaw θ μ) (t : ℝ≥0) (ht : 0 < t) (r : TreeVertex d) :
    ∀ᵐ p ∂(μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t))[|{p | p.1 r = .pos}],
      PlantedSymmetry.observation t p r =
        (t : ℝ) + Real.sqrt t * (p.2 r / Real.sqrt t) := by
  have hs : MeasurableSet {p : (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ) |
      p.1 r = .pos} :=
    (show MeasurableSet ({IsingSpin.pos} : Set IsingSpin) from trivial).preimage
      ((measurable_pi_apply r).comp measurable_fst)
  filter_upwards [ae_cond_mem hs] with p hp
  have hroot : p.1 r = .pos := hp
  have hsqrt : Real.sqrt (t : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (show (0 : ℝ) < t from ht)).ne'
  simp only [PlantedSymmetry.observation, hroot, spinSign, mul_one]
  rw [mul_div_cancel₀ _ hsqrt]

end Problem367

end

end OAI
end

section
-- module Solutions.Q243_FreeIsing.FreeIsing_Energy_ActualCriticalFieldMoments
attribute [-instance] _root_.OAI.Problem367.IsingConditionalCopyBounds.graphLaw_isProbabilityMeasure _root_.OAI.Problem367.IsingObservationFactor.copies_probability _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_observationLaw_probability _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
attribute [-simp] _root_.OAI.Problem367.CutContinuationChannels.averageChannel_globalCone _root_.OAI.Problem367.CutContinuationChannels.continuationChannel_globalCone _root_.OAI.Problem367.FactorObservable.centeredSpinLp_coe _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_fst _root_.OAI.Problem367.FiniteIsingSplit.splitEquiv_snd _root_.OAI.Problem367.FinitePathGibbs.tailPartition_zero _root_.OAI.Problem367.GaussianTreeResponseNaturality.fieldEquiv_apply_image _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_apply _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_uniformObservation _root_.OAI.Problem367.IsingObservationInnovation.innovationMap_zero _root_.OAI.Problem367.IsingObservationInnovation.uniformObservation_relabel _root_.OAI.Problem367.IsingOrientedPath.attenuation_outward _root_.OAI.Problem367.IsingOrientedPath.endpoint_extensionAt _root_.OAI.Problem367.LocalSupportGeometry.prefixVertex_length _root_.OAI.Problem367.PathSideBranches.parent_sideVertex _root_.OAI.Problem367.PathSideBranches.restrictNoisyRegion_array _root_.OAI.Problem367.PathSideBranches.sideVertex_length _root_.OAI.Problem367.PathSideBranches.sideVertex_val _root_.OAI.Problem367.PosteriorChain.transition_spinMean _root_.OAI.Problem367.PosteriorChain.transition_sum _root_.OAI.Problem367.TreeConeCoding.length_vertex _root_.OAI.Problem367.TreeConeCoding.vertex_nil _root_.OAI.Problem367.TreeConeCoding.vertex_val _root_.OAI.Problem367.TreeGibbsAut.spinEquiv_apply_image _root_.OAI.Problem367.TreeKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredAverage_pow_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_apply_coe _root_.OAI.Problem367.TreeKoopman.centeredGenerator_sq _root_.OAI.Problem367.TreeKoopman.generatorOperator_sq _root_.OAI.Problem367.TreeKoopman.reverseVertex_twice _root_.OAI.Problem367.TreeKoopman.wordRelabel_cons _root_.OAI.Problem367.TreeKoopman.wordRelabel_nil _root_.OAI.Problem367.TreeLawKoopman.centeredAverage_apply_coe _root_.OAI.Problem367.TreeLawKoopman.generatorOperator_sq _root_.OAI.Problem367.TreePathGibbs.vertexEquiv_val _root_.OAI.Problem367.dropVertex_length _root_.OAI.Problem367.dropVertex_val _root_.OAI.Problem367.mem_rootComplementFinset _root_.OAI.Problem367.mem_rootComponentFinset _root_.OAI.Problem367.mem_rootComponentIndices _root_.OAI.Problem367.prefixColorAut_length _root_.OAI.Problem367.prefixColorAut_val _root_.OAI.Problem367.prefixColorMap_symm_apply _root_.OAI.Problem367.spinSign_flip _root_.OAI.Problem367.tsum_treeShell_radial _root_.OAI.Problem367.vertexSampler_relabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.conditioned_own_gaussian_abs_moments
    {d : ℕ} {theta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw theta μ) (t : ℝ≥0) (ht : 0 < t)
    (ht1 : (t : ℝ) ≤ 1) (r : TreeVertex d) (p : ℕ) :
    Integrable (fun q => |observation t q r| ^ p)
      ((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 r = .pos}]) ∧
    (∫ q, |observation t q r| ^ p
      ∂((μ.prod (gaussianNoiseLaw (TreeVertex d) t))[|{q | q.1 r = .pos}])) ≤
      Real.exp (2 * (p : ℝ) ^ 2) * (t : ℝ) ^ ((p : ℝ) / 4) := by
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let ν := P[|{q | q.1 r = IsingSpin.pos}]
  have hmass : P {q | q.1 r = IsingSpin.pos} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r .pos
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure (by rw [hmass]; norm_num)
  have hG := hμ.standard_gaussian_hasLaw_cond_spin t ht r r .pos
  have hEq : (fun q => |observation t q r| ^ p) =ᵐ[ν]
      fun q => |(t : ℝ) + Real.sqrt t * (q.2 r / Real.sqrt t)| ^ p := by
    filter_upwards [hμ.own_gaussian_observation_cond_pos t ht r] with q hq
    rw [hq]
  have hInt := integrable_gaussian_observation_abs_pow_of_hasLaw hG t.coe_nonneg ht1 p
  refine ⟨hInt.congr hEq.symm, ?_⟩
  change (∫ q, |observation t q r| ^ p ∂ν) ≤ _
  rw [integral_congr_ae hEq]
  rcases p with _ | p
  · simp
  · exact integral_gaussian_observation_abs_pow_le_of_hasLaw hG
      (show (0 : ℝ) < t from ht) ht1 (Nat.succ_pos p)

theorem exists_gaussianComponentField_critical_moment_tail_oai
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ} (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (μ : Measure (TreeVertex d → IsingSpin)),
      HasFreeIsingLaw (Real.tanh beta) μ →
      ∀ (t : ℝ≥0), 0 < t → (t : ℝ) ≤ 1 → ∀ c : Fin d,
      (∀ p : ℕ, Integrable
        (fun q => |selectedGaussianField μ t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p)
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))) ∧
      (∀ p : ℕ, (∫ q,
        |selectedGaussianField μ t (componentIndexVertex (c := c))
          (RootedBroadcast.branchRoot c) q| ^ p
        ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
        Real.exp (K * (p : ℝ) ^ 2) * (t : ℝ) ^ ((p : ℝ) / 4)) ∧
      (32 * K ≤ Real.log (1 / (t : ℝ)) →
        (μ.prod (gaussianNoiseLaw (TreeVertex d) t))
          {q | (t : ℝ) ^ (1 / 8 : ℝ) <
            |selectedGaussianField μ t (componentIndexVertex (c := c))
              (RootedBroadcast.branchRoot c) q|} ≤
          ENNReal.ofReal (Real.exp (-(Real.log (1 / (t : ℝ)) ^ 2) / (512 * K)))) := by
  classical
  have h0 := tanh_nonneg_of_beta_nonneg hb
  have h1 := Real.tanh_lt_one beta
  have hK0 : 0 < criticalComponentBaseExponent d beta :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (criticalComponentBaseExponent_ge_two d beta)
  obtain ⟨K, hKK0, hK, hUniform⟩ :=
    exists_measure_uniform_critical_response_moment_and_tail_bound
      (Ω := (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))
      (Ξ := (TreeVertex d → IsingSpin) × (TreeVertex d → ℝ))
      h0 h1 hcritical hK0
  refine ⟨K, hK, ?_⟩
  intro μ hμ t ht ht1 c
  let : IsProbabilityMeasure μ := hμ.isProbabilityMeasure
  let P := μ.prod (gaussianNoiseLaw (TreeVertex d) t)
  let r := RootedBroadcast.branchRoot c
  let ν := P[|{q | q.1 r = IsingSpin.pos}]
  let Y := selectedGaussianField μ t (componentIndexVertex (c := c)) r
  let F : IsingSpin → ℝ → ℝ := fun s z => (t : ℝ) * spinSign s + z
  let I := {a : Fin d // c ≠ a}
  have hcard : Fintype.card I = d - 1 := by
    dsimp [I]
    simp [Fintype.card_subtype_compl]
  let e : Fin (d - 1) ≃ I :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hcard.symm)
  let Z := ownChildFinFamily e (componentOwnChildFields P F c)
  have hmass : P {q | q.1 r = IsingSpin.pos} = (1 / 2 : ENNReal) :=
    hμ.planted_spin_event_mass (fun _ => gaussianReal 0 t) r .pos
  let : IsProbabilityMeasure ν := cond_isProbabilityMeasure (by rw [hmass]; norm_num)
  have hF : Measurable (Function.uncurry F) :=
    ((PlantedInformation.measurable_spinSign.comp measurable_fst).const_mul _).add
      measurable_snd
  have hr : r ∈ Set.range (componentIndexVertex (c := c)) := by
    apply mem_range_componentIndexVertex.mpr
    exact ⟨[], by simp [r, RootedBroadcast.branchRoot]⟩
  have hInt (p : ℕ) : Integrable (fun q => |Y q| ^ p) P :=
    hμ.integrable_selectedGaussianField_abs_pow hb t _ r hr p
  have hz0 : Z 0 = fun q => observation t q r := by
    rfl
  have hzsucc (i : Fin (d - 1)) : Z i.succ =
      selectedGaussianField μ t (childComponentIndexVertex c (e i).1)
        (prefixFlip c (RootedBroadcast.branchRoot (e i).1)) := by
    dsimp only [Z]
    rw [ownChildFinFamily_succ]
    rfl
  have hZ : iIndepFun Z ν := by
    apply iIndepFun_ownChildFinFamily
    exact hμ.iIndepFun_component_fields_cond_spin (by linarith) h1.le
      (gaussianReal 0 t) hF c .pos
  have hmZ : ∀ i, Measurable (Z i) :=
    measurable_ownChildFinFamily e (measurable_componentOwnChildFields P hF c)
  have hOwn (p : ℕ) := hμ.conditioned_own_gaussian_abs_moments t ht ht1 r p
  have hOwnInt (p : ℕ) : Integrable (fun q => |Z 0 q| ^ p) ν := by
    rw [hz0]
    exact (hOwn p).1
  have hOwnBound (p : ℕ) : (∫ q, |Z 0 q| ^ p ∂ν) ≤
      Real.exp (criticalComponentBaseExponent d beta * (p : ℝ) ^ 2) *
        (t : ℝ) ^ ((p : ℝ) / 4) := by
    rw [hz0]
    apply (hOwn p).2.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg t.coe_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (criticalComponentBaseExponent_ge_two d beta) (sq_nonneg _))
  have hCond : IdentDistrib (fun q => |Y q|) (fun q => |Y q|) ν P :=
    hμ.selectedGaussianField_abs_identDistrib_cond_spin t _ r r .pos
  have hChild (i : Fin (d - 1)) :
      IdentDistrib (fun q => |Z i.succ q|) (fun q => |Y q|) ν P := by
    rw [hzsucc]
    exact hμ.childComponentField_cond_abs_identDistrib t c (e i).1 r .pos
  have hEq : ∀ᵐ q ∂ν, Y q =
      ∑ i : Fin (d - 1 + 1),
        Fin.cases (Z 0 q) (fun j => cavityMessage (Real.tanh beta) (Z j.succ q)) i := by
    have hRec := (cond_absolutelyContinuous (μ := P)
      (s := {q | q.1 r = IsingSpin.pos})).ae_le
      (hμ.gaussian_component_field_recursion (by omega) hb t c)
    filter_upwards [hRec] with q hq
    exact hq.trans (sum_response_ownChildFinFamily e
      (componentOwnChildFields P F c) (cavityMessage (Real.tanh beta)) q).symm
  refine ⟨hInt, ?_⟩
  exact hUniform P ν inferInstance inferInstance (t : ℝ) (show (0 : ℝ) < t from ht)
    Y Y Z (cavityMessage (Real.tanh beta))
    (lipschitzWith_cavityMessage h0 h1.le).continuous.measurable
    (cavityMessage_abs_le_mul h0 h1.le) hInt hOwnInt hZ hmZ hCond hChild hEq
    hOwnBound (hμ.gaussianComponentField_critical_base_moments hd hb hcritical t ht1 c)

end Problem367

end

end OAI
end

theorem solution : type_of% @OAI.Problem367.exists_gaussianComponentField_critical_moment_tail_oai := @OAI.Problem367.exists_gaussianComponentField_critical_moment_tail_oai
