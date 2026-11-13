-- Prove2me | solution 1 for OAI.InvariantIsing.spectralCanonical_identification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:08:44.872784+00:00
-- url     : https://prove2.me/submissions/7164c064-70a5-4ff7-ace7-12c73e12405d

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258005
import Theorems.Thm_OAI_InvariantIsing_spectralCanonicalWard_pair
import Theorems.Thm_OAI_InvariantIsing_spectralCanonical_symbols

section
-- module Solutions.OAIQ258_II.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_TiltedLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tilted Label Law. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction

namespace IsingPerceptron

lemma compact_integrable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {P : Measure X} [IsFiniteMeasure P]
    {F : X → ℝ} (hF : Continuous F) : Integrable F P :=
  (BoundedContinuousFunction.mkOfCompact ⟨F,hF⟩).integrable P

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArraySynchronization
attribute [-instance] _root_.OAI.InvariantIsing.simpleFieldPositive_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Synchronization. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix

namespace IsingPerceptron



lemma polya_no_linear_cap {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb : b < 1)
    {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (h0 : 0 < r 0)
    (hrec : ∀ k, r (k+1) = r k * ((n : ℝ) + k - b) / ((n : ℝ) + k))
    (hcap : ∀ k : ℕ, (k+1 : ℝ) * r k ≤ 1) : False := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let t : ℕ → ℝ := fun k => ((n : ℝ) + k - 1) * r k
  have ht : ∀ k, t (k+1) = t k + (1-b) * r k := by
    intro k
    have hnk : (n : ℝ) + k ≠ 0 := by positivity
    dsimp [t]
    rw [hrec]
    push_cast
    field_simp
    ring
  have hbase : 0 < t 0 := by
    dsimp [t]; simp only [Nat.cast_zero, add_zero]
    exact mul_pos (by linarith) h0
  have hmono : Monotone t := monotone_nat_of_le_succ (fun k => by
    rw [ht]
    nlinarith [hr k])
  have hlower : ∀ k, t 0 / ((n : ℝ) + k - 1) ≤ r k := by
    intro k
    have h := hmono (Nat.zero_le k)
    have hden : 0 < (n : ℝ) + k - 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact (div_le_iff₀ hden).mpr (by simpa only [t, mul_comm] using h)
  have hsum : ∀ k, t 0 + (1-b)*t 0 *
      (∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1)) ≤ t k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ht]
      have he := mul_le_mul_of_nonneg_left (hlower k) (sub_pos.mpr hb).le
      calc
        _ = (t 0 + (1-b)*t 0 * (∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1))) +
              (1-b)*(t 0 / ((n : ℝ) + k - 1)) := by ring
        _ ≤ _ := add_le_add ih he
  have hupper : ∀ k, t k ≤ (n : ℝ) - 1 := by
    intro k
    have h := hcap k
    have he : (n : ℝ) + k - 1 ≤ ((n : ℝ)-1) * (k+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have he' := mul_le_mul_of_nonneg_right he (hr k)
    have h' := mul_le_mul_of_nonneg_left h (by linarith : 0 ≤ (n : ℝ)-1)
    dsimp [t]
    nlinarith
  have hcompare : ∀ k, (∑ j ∈ Finset.range k, 1 / (j+1 : ℝ)) / n ≤
      ∑ j ∈ Finset.range k, 1 / ((n : ℝ) + j - 1) := by
    intro k
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun j _ => ?_
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hden : 0 < (n : ℝ) + j - 1 := by linarith
    rw [div_div]
    apply one_div_le_one_div_of_le hden
    nlinarith
  have hH : Tendsto (fun k => t 0 + (1-b)*t 0 *
      ((∑ j ∈ Finset.range k, 1 / (j+1 : ℝ)) / n)) atTop atTop := by
    apply tendsto_atTop_add_const_left
    apply Filter.Tendsto.const_mul_atTop (by positivity)
    exact Filter.Tendsto.atTop_div_const (by positivity)
      Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨k, hk⟩ := ((tendsto_atTop.1 hH) ((n : ℝ) - 1 + 1)).exists
  have he := (mul_le_mul_of_nonneg_left (hcompare k) (by positivity : 0 ≤ (1-b)*t 0))
  have hs := hsum k
  have hu := hupper k
  linarith

 

lemma equal_probability_aedisjoint_cap {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {k : ℕ} {s : Fin (k+1) → Set Ω}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (fun i j => AEDisjoint μ (s i) (s j)))
    {r : ℝ} (hs : ∀ i, μ.real (s i) = r) : (k+1 : ℝ)*r ≤ 1 := by
  have he := measureReal_biUnion_finset₀ (μ := μ) (s := Finset.univ)
    (fun i _ j _ hij => hd hij) (fun i _ => (hm i).nullMeasurableSet)
    (fun i _ => measure_ne_top μ (s i))
  have hu : (⋃ i ∈ Finset.univ, s i) = ⋃ i, s i := by simp
  rw [hu] at he
  have hh : μ.real (⋃ i, s i) ≤ 1 := measureReal_le_one
  rw [he] at hh
  simpa [hs, Nat.cast_add, Nat.cast_one] using hh

lemma swap_hasFiniteSupport (i j : ℕ) : {a | (Equiv.swap i j) a ≠ a}.Finite := by
  apply ((Set.finite_singleton j).insert i).subset
  intro a ha
  by_contra hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
  exact ha (Equiv.swap_apply_of_ne_of_ne hn.1 hn.2)

lemma measurableSet_starSet {a : ℕ} (J : Finset ℕ) {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    (t : ℝ) (i : ℕ) : MeasurableSet (starSet a J A T t i) := by
  apply MeasurableSet.inter
  · exact hA.preimage (Measurable.of_eval fun x => Measurable.of_eval fun y =>
      (measurable_pi_apply (y : ℕ)).comp (measurable_pi_apply (x : ℕ)))
  apply MeasurableSet.inter
  · exact hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x : ℕ)))
  change MeasurableSet {b : RealArray | ∀ j ∈ J, j ≠ i → b i j < t}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt
      (by fun_prop : Measurable (fun b : RealArray => b i j)) measurable_const

lemma measurableSet_duplicateSet {a : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    (t : ℝ) (i j : ℕ) : MeasurableSet (duplicateSet a A T t i j) := by
  apply MeasurableSet.inter
  · exact hA.preimage (Measurable.of_eval fun x => Measurable.of_eval fun y =>
      (measurable_pi_apply (y : ℕ)).comp (measurable_pi_apply (x : ℕ)))
  apply MeasurableSet.inter
  · exact hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply i).comp (measurable_pi_apply (x : ℕ)))
  exact (hT.preimage (Measurable.of_eval fun x =>
      (measurable_pi_apply j).comp (measurable_pi_apply (x : ℕ)))).inter
    (measurableSet_lt (by fun_prop : Measurable (fun b : RealArray => b i j)) measurable_const)

lemma starSet_permute {a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} {i : ℕ} {e : Equiv.Perm ℕ}
    (hfix : ∀ x < a, e x = x) (hJ : ∀ j, j ∈ J ↔ e j ∈ J) :
    permuteArray e ⁻¹' starSet a J A T t i = starSet a J A T t (e i) := by
  ext b
  have hA : (fun x y : Fin a => permuteArray e b x y) = fun x y : Fin a => b x y := by
    funext x y
    simp only [permuteArray, hfix x x.isLt, hfix y y.isLt]
  have hT : (fun x : Fin a => permuteArray e b x i) = fun x : Fin a => b x (e i) := by
    funext x
    simp only [permuteArray, hfix x x.isLt]
  change (_ ∈ A ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _)
  rw [hA, hT]
  constructor
  · rintro ⟨ha, ht, hs⟩
    refine ⟨ha, ht, ?_⟩
    intro j hj hji
    have hj' : e.symm j ∈ J := (hJ _).mpr (by simpa using hj)
    have hji' : e.symm j ≠ i := by intro he; apply hji; rw [← he]; simp
    simpa only [permuteArray, Equiv.apply_symm_apply] using hs _ hj' hji'
  · rintro ⟨ha, ht, hs⟩
    exact ⟨ha, ht, fun j hj hji => hs (e j) ((hJ j).mp hj) (e.injective.ne hji)⟩

lemma duplicateSet_permute {a : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} {i j : ℕ} {e : Equiv.Perm ℕ}
    (hfix : ∀ x < a, e x = x) :
    permuteArray e ⁻¹' duplicateSet a A T t i j = duplicateSet a A T t (e i) (e j) := by
  ext b
  change (_ ∈ A ∧ _ ∈ T ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _ ∈ T ∧ _)
  have hA : (fun x y : Fin a => permuteArray e b x y) = fun x y : Fin a => b x y := by
    funext x y
    simp only [permuteArray, hfix x x.isLt, hfix y y.isLt]
  have hT : ∀ i, (fun x : Fin a => permuteArray e b x i) = fun x : Fin a => b x (e i) := by
    intro i; funext x
    simp only [permuteArray, hfix x x.isLt]
  rw [hA, hT i, hT j]
  rfl

lemma swap_preserves_ge {a x y z : ℕ} (hx : a ≤ x) (hy : a ≤ y) (hz : a ≤ z) :
    a ≤ (Equiv.swap x y) z := by
  by_cases hzx : z = x
  · subst z; simpa using hy
  by_cases hzy : z = y
  · subst z; simpa using hx
  simpa only [Equiv.swap_apply_of_ne_of_ne hzx hzy] using hz

lemma star_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} (hA : MeasurableSet A) (hT : MeasurableSet T)
    {t : ℝ} {i j : ℕ} (hai : a ≤ i) (haj : a ≤ j) (hi : i ∈ J) (hj : j ∈ J) :
    μ (B ⁻¹' starSet a J A T t i) = μ (B ⁻¹' starSet a J A T t j) := by
  have h := (hwe (Equiv.swap i j) (swap_hasFiniteSupport i j)).measure_mem_eq
    (measurableSet_starSet J hA hT t i)
  change μ (B ⁻¹' starSet a J A T t i) =
    μ (B ⁻¹' (permuteArray (Equiv.swap i j) ⁻¹' starSet a J A T t i)) at h
  have hfix : ∀ x < a, (Equiv.swap i j) x = x := by
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hJ : ∀ x, x ∈ J ↔ (Equiv.swap i j) x ∈ J := by
    intro x
    by_cases hxi : x = i
    · subst x; simp only [Equiv.swap_apply_left]; exact iff_of_true hi hj
    by_cases hxj : x = j
    · subst x; simp only [Equiv.swap_apply_right]; exact iff_of_true hj hi
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj]
  rw [starSet_permute hfix hJ, Equiv.swap_apply_left] at h
  exact h

lemma duplicate_probability_swap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ) (i j : ℕ)
    {x y : ℕ} (hx : a ≤ x) (hy : a ≤ y) :
    μ (B ⁻¹' duplicateSet a A T t i j) =
      μ (B ⁻¹' duplicateSet a A T t ((Equiv.swap x y) i) ((Equiv.swap x y) j)) := by
  have h := (hwe (Equiv.swap x y) (swap_hasFiniteSupport x y)).measure_mem_eq
    (measurableSet_duplicateSet hA hT t i j)
  change μ (B ⁻¹' duplicateSet a A T t i j) =
    μ (B ⁻¹' (permuteArray (Equiv.swap x y) ⁻¹' duplicateSet a A T t i j)) at h
  rwa [duplicateSet_permute (by
    intro z hz
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))] at h

lemma duplicate_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    {i j : ℕ} (hi : a ≤ i) (hj : a ≤ j) (hij : i ≠ j) :
    μ (B ⁻¹' duplicateSet a A T t a (a+1)) = μ (B ⁻¹' duplicateSet a A T t i j) := by
  let k := (Equiv.swap a i) (a+1)
  have hk : a ≤ k := swap_preserves_ge (le_refl a) hi (by omega)
  have hki : k ≠ i := by
    have hh : (Equiv.swap a i) (a+1) ≠ (Equiv.swap a i) a :=
      (Equiv.swap a i).injective.ne (by omega)
    simpa only [Equiv.swap_apply_left] using hh
  have h₁ := duplicate_probability_swap hwe hA hT t a (a+1) (le_refl a) hi
  have h₂ := duplicate_probability_swap hwe hA hT t i k hk hj
  rw [Equiv.swap_apply_of_ne_of_ne hki.symm hij, Equiv.swap_apply_left] at h₂
  rw [Equiv.swap_apply_left] at h₁
  exact h₁.trans h₂

lemma no_duplicate_star_cap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ)
    {a : ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hdup : μ (B ⁻¹' duplicateSet a A T t a (a+1)) = 0) (k : ℕ) :
    (k+1 : ℝ) * μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a) ≤ 1 := by
  let J := Finset.Ico a (a+k+1)
  let s : Fin (k+1) → Set Ω := fun i => B ⁻¹' starSet a J A T t (a+i)
  have hmem : ∀ i : Fin (k+1), a+i ∈ J := by
    intro i
    simp only [J, Finset.mem_Ico]
    constructor <;> omega
  apply equal_probability_aedisjoint_cap (μ := μ) (s := s)
  · intro i
    exact (measurableSet_starSet J hA hT t (a+i)).preimage hm
  · intro i j hij
    have hnull : μ (B ⁻¹' duplicateSet a A T t (a+i) (a+j)) = 0 := by
      rw [← duplicate_probability_equal hwe hA hT t (by omega) (by omega)
        (by intro h; apply hij; apply Fin.ext; omega), hdup]
    change μ (s i ∩ s j) = 0
    apply measure_mono_null (t := B ⁻¹' duplicateSet a A T t (a+i) (a+j)) ?_ hnull
    intro ω hω
    exact ⟨hω.1.1, hω.1.2.1, hω.2.2.1,
      hω.1.2.2 (a+j) (hmem j) (by intro h; apply hij; apply Fin.ext; omega)⟩
  · intro i
    apply congrArg ENNReal.toReal
    exact star_probability_equal hwe hA hT (by omega) (le_refl a) (hmem i)
      (by simp only [J, Finset.mem_Ico]; constructor <;> omega)


lemma measurable_extendArrayBlock (n : ℕ) : Measurable (extendArrayBlock n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  by_cases hi : i < n
  · by_cases hj : j < n
    · simpa only [extendArrayBlock, dite_eq_left hi, dite_eq_left hj, Function.comp_def] using
        ((measurable_pi_apply (⟨j,hj⟩ : Fin n)).comp (measurable_pi_apply (⟨i,hi⟩ : Fin n)))
    · simp only [extendArrayBlock, dite_eq_left hi, dite_eq_right hj]; exact measurable_const
  · simp only [extendArrayBlock, dite_eq_right hi]; exact measurable_const

lemma starSet_dependsOn {Ω : Type*} {B : Ω → RealArray} {ω : Ω}
    {n a : ℕ} {J : Finset ℕ} {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    {t : ℝ} {i : ℕ} (han : a ≤ n) (hin : i < n) (hJ : ∀ j ∈ J, j < n) :
    extendArrayBlock n (arrayBlock B n ω) ∈ starSet a J A T t i ↔
      B ω ∈ starSet a J A T t i := by
  have he : ∀ x y, x < n → y < n →
      extendArrayBlock n (arrayBlock B n ω) x y = B ω x y := by
    intro x y hx hy
    simp only [extendArrayBlock, dite_eq_left hx, dite_eq_left hy, arrayBlock]
  have hA : (fun x y : Fin a => extendArrayBlock n (arrayBlock B n ω) x y) =
      fun x y : Fin a => B ω x y := by
    funext x y
    exact he x y (x.isLt.trans_le han) (y.isLt.trans_le han)
  have hT : (fun x : Fin a => extendArrayBlock n (arrayBlock B n ω) x i) =
      fun x : Fin a => B ω x i := by
    funext x
    exact he x i (x.isLt.trans_le han) hin
  change (_ ∈ A ∧ _ ∈ T ∧ _) ↔ (_ ∈ A ∧ _ ∈ T ∧ _)
  rw [hA, hT]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro j
  apply forall_congr'; intro hj
  rw [he i j hin (hJ j hj)]

lemma starSet_chain_succ {a k : ℕ} {A : Set (Fin a → Fin a → ℝ)}
    {T : Set (Fin a → ℝ)} {t : ℝ} :
    starSet a (Finset.Ico a (a+(k+1)+1)) A T t a =
      starSet a (Finset.Ico a (a+k+1)) A T t a ∩ {b | b a (a+k+1) < t} := by
  ext b
  constructor
  · rintro ⟨ha, ht, hs⟩
    refine ⟨⟨ha, ht, fun j hj hja => hs j ?_ hja⟩, hs (a+k+1) ?_ (by omega)⟩
    · simp only [Finset.mem_Ico] at hj ⊢; omega
    · simp only [Finset.mem_Ico]; omega
  · rintro ⟨⟨ha, ht, hs⟩, hn⟩
    refine ⟨ha, ht, ?_⟩
    intro j hj hja
    by_cases hjn : j = a+k+1
    · change b a (a+k+1) < t at hn
      simpa only [hjn] using hn
    · apply hs j _ hja
      simp only [Finset.mem_Ico] at hj ⊢; omega

lemma gg_star_chain_recurrence {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hsym : ∀ ω i j, B ω i j = B ω j i) (hGG : HasGhirlandaGuerra B μ)
    {a : ℕ} (ha : 0 < a) {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hTlow : ∀ v ∈ T, ∀ i, v i < t) (k : ℕ) :
    μ.real (B ⁻¹' starSet a (Finset.Ico a (a+(k+1)+1)) A T t a) =
      μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a) *
        ((a+1 : ℕ) + (k : ℝ) - (1 - μ.real {ω | B ω 0 1 < t})) /
        ((a+1 : ℕ) + (k : ℝ)) := by
  classical
  let n := a+k+1
  let J := Finset.Ico a n
  let C : Set Ω := B ⁻¹' starSet a J A T t a
  let F : Set (Fin n → Fin n → ℝ) := extendArrayBlock n ⁻¹' starSet a J A T t a
  let i : Fin n := ⟨a, by dsimp [n]; omega⟩
  have hF : MeasurableSet F :=
    (measurableSet_starSet J hA hT t a).preimage (measurable_extendArrayBlock n)
  have hC : arrayBlock B n ⁻¹' F = C := by
    ext ω
    exact starSet_dependsOn (by dsimp [n]; omega) (by dsimp [n]; omega)
      (by intro j hj; exact (Finset.mem_Ico.mp hj).2)
  have h := hGG n (by dsimp [n]; omega) i F hF (Set.Iio t) measurableSet_Iio
  rw [hC] at h
  have hevent : ∀ j ∈ Finset.univ.erase i,
      C ∩ {ω | B ω i j ∈ Set.Iio t} = C := by
    intro j hj
    apply Set.inter_eq_left.mpr
    intro ω hω
    have hji : j.val ≠ a := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext he)
    change B ω a j.val < t
    by_cases hja : j.val < a
    · rw [hsym ω a j.val]
      exact hTlow _ hω.2.1 ⟨j.val,hja⟩
    · exact hω.2.2 j.val (Finset.mem_Ico.mpr ⟨by omega, j.isLt⟩) hji
  have hsum : (∑ j ∈ Finset.univ.erase i, μ.real (C ∩ {ω | B ω i j ∈ Set.Iio t})) =
      (n-1 : ℝ) * μ.real C := by
    calc
      _ = ∑ _j ∈ Finset.univ.erase i, μ.real C :=
        Finset.sum_congr rfl (fun j hj => congrArg μ.real (hevent j hj))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Nat.cast_sub (by dsimp [n]; omega : 1 ≤ n), Nat.cast_one]
  rw [hsum] at h
  rw [starSet_chain_succ, Set.preimage_inter]
  change μ.real (C ∩ {ω | B ω a n < t}) = _
  change μ.real (C ∩ {ω | B ω a n < t}) = _ at h
  rw [h]
  dsimp [C, J, n]
  simp only [Set.mem_Iio]
  push_cast
  ring

lemma low_pair_probability_equal {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hwe : WeaklyExchangeable B μ)
    {a : ℕ} (ha : 0 < a) (t : ℝ) :
    μ {ω | B ω 0 1 < t} = μ {ω | B ω 0 a < t} := by
  have h := (hwe (Equiv.swap 1 a) (swap_hasFiniteSupport 1 a)).measure_mem_eq
    (measurableSet_lt (by fun_prop : Measurable (fun b : RealArray => b 0 1))
      (measurable_const (a := t)))
  have hz : (Equiv.swap 1 a) 0 = 0 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  simpa only [Set.preimage_ofPred_eq, permuteArray, hz, Equiv.swap_apply_left] using h

lemma starSet_base (a : ℕ) (A : Set (Fin a → Fin a → ℝ)) (T : Set (Fin a → ℝ)) (t : ℝ) :
    starSet a (Finset.Ico a (a+1)) A T t a =
      {b | (fun x y : Fin a => b x y) ∈ A ∧ (fun x : Fin a => b x a) ∈ T} := by
  ext b
  constructor
  · intro h; exact ⟨h.1, h.2.1⟩
  · rintro ⟨hA, hT⟩
    refine ⟨hA, hT, ?_⟩
    intro j hj hjne
    simp only [Finset.mem_Ico] at hj
    omega

 

theorem gg_duplication_positive {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {a : ℕ} (ha : 0 < a) {A : Set (Fin a → Fin a → ℝ)} {T : Set (Fin a → ℝ)}
    (hA : MeasurableSet A) (hT : MeasurableSet T) (t : ℝ)
    (hTlow : ∀ v ∈ T, ∀ i, v i < t)
    (hpos : 0 < μ.real (B ⁻¹' starSet a (Finset.Ico a (a+1)) A T t a)) :
    0 < μ.real (B ⁻¹' duplicateSet a A T t a (a+1)) := by
  by_contra hn
  have hzero : μ (B ⁻¹' duplicateSet a A T t a (a+1)) = 0 := by
    apply (measureReal_eq_zero_iff (μ := μ)).mp
    exact le_antisymm (not_lt.mp hn) measureReal_nonneg
  have hp : 0 < μ.real {ω | B ω 0 1 < t} := by
    have he := congrArg ENNReal.toReal (low_pair_probability_equal hwe ha t)
    change μ.real {ω | B ω 0 1 < t} = μ.real {ω | B ω 0 a < t} at he
    rw [he]
    exact hpos.trans_le (measureReal_mono (μ := μ) (fun ω hω => hTlow _ hω.2.1 ⟨0,ha⟩))
  apply polya_no_linear_cap (n := a+1) (b := 1 - μ.real {ω | B ω 0 1 < t})
    (r := fun k => μ.real (B ⁻¹' starSet a (Finset.Ico a (a+k+1)) A T t a))
    (by omega) (by linarith) (fun _ => measureReal_nonneg)
    (by simpa only [Nat.add_zero] using hpos)
  · exact gg_star_chain_recurrence hsym hGG ha hA hT t hTlow
  · exact no_duplicate_star_cap hm hwe hA hT t hzero


lemma measurable_arrayBlock {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} (hm : Measurable B) (n : ℕ) :
    Measurable (arrayBlock B n) := by
  unfold arrayBlock
  fun_prop

lemma blockLaw_support_compact {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hb : ∀ ω i j, |B ω i j| ≤ D) (n : ℕ) :
    IsCompact (blockLaw B μ n).support := by
  apply (isCompact_Icc (a := fun _ _ : Fin n => -D)
    (b := fun _ _ : Fin n => D)).of_isClosed_subset Measure.isClosed_support
  apply Measure.support_subset_of_isClosed isClosed_Icc
  rw [mem_ae_iff]
  rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm n) isClosed_Icc.isOpen_compl.measurableSet]
  have he : arrayBlock B n ⁻¹' (Set.Icc (fun _ _ : Fin n => -D) (fun _ _ : Fin n => D))ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    apply hω
    constructor
    · intro i j; exact (abs_le.mp (hb ω i j)).1
    · intro i j; exact (abs_le.mp (hb ω i j)).2
  rw [he, measure_empty]

 

theorem gg_duplicate_supported_last {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    {a : ℕ} (ha : 0 < a) {A : Fin (a+1) → Fin (a+1) → ℝ}
    (hA : A ∈ (blockLaw B μ (a+1)).support) {t : ℝ}
    (ht : ∀ i : Fin a, A i.castSucc (Fin.last a) ≤ t) :
    ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin a, C i.castSucc.castSucc j.castSucc.castSucc = A i.castSucc j.castSucc) ∧
      (∀ i : Fin a, C i.castSucc.castSucc (Fin.last a).castSucc = A i.castSucc (Fin.last a)) ∧
      (∀ i : Fin a, C i.castSucc.castSucc (Fin.last (a+1)) = A i.castSucc (Fin.last a)) ∧
      C (Fin.last a).castSucc (Fin.last (a+1)) ≤ t := by
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin a, |C i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε) ∧
      (∀ i : Fin a, |C i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε) ∧
      (∀ i : Fin a, |C i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε) ∧
      C (Fin.last a).castSucc (Fin.last (a+1)) < t+ε := by
    intro ε hε
    let F : Set (Fin a → Fin a → ℝ) :=
      {c | ∀ i j, |c i j - A i.castSucc j.castSucc| < ε}
    let T : Set (Fin a → ℝ) :=
      {c | ∀ i, |c i - A i.castSucc (Fin.last a)| < ε}
    have hF : MeasurableSet F := by
      dsimp [F]; simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt (by fun_prop) measurable_const
    have hT : MeasurableSet T := by
      dsimp [T]; simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
    have hball := (Measure.mem_support_iff_forall A).mp hA
      (Metric.ball A ε) (Metric.ball_mem_nhds A hε)
    rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm (a+1)) Metric.isOpen_ball.measurableSet] at hball
    have hpos : 0 < μ.real (B ⁻¹' starSet a (Finset.Ico a (a+1)) F T (t+ε) a) := by
      have hsub : arrayBlock B (a+1) ⁻¹' Metric.ball A ε ⊆
          B ⁻¹' starSet a (Finset.Ico a (a+1)) F T (t+ε) a := by
        intro ω hω
        rw [starSet_base]
        have hc := (dist_pi_lt_iff hε).mp hω
        constructor
        · intro i j
          exact (dist_pi_lt_iff hε).mp (hc i.castSucc) j.castSucc
        · intro i
          exact (dist_pi_lt_iff hε).mp (hc i.castSucc) (Fin.last a)
      exact ENNReal.toReal_pos (ne_of_gt (hball.trans_le (measure_mono hsub))) (measure_ne_top _ _)
    have hd := gg_duplication_positive hm hsym hwe hGG ha hF hT (t+ε)
      (by intro v hv i; have hi := (abs_lt.mp (hv i)).2; have := ht i; linarith) hpos
    let E : Set (Fin (a+2) → Fin (a+2) → ℝ) := {c |
      (∀ i j : Fin a, |c i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε) ∧
      (∀ i : Fin a, |c i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε) ∧
      (∀ i : Fin a, |c i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε) ∧
      c (Fin.last a).castSucc (Fin.last (a+1)) < t+ε}
    have hE : MeasurableSet E := by
      change MeasurableSet ({c : Fin (a+2) → Fin (a+2) → ℝ | ∀ i j : Fin a, |c i.castSucc.castSucc j.castSucc.castSucc - A i.castSucc j.castSucc| < ε} ∩
        ({c | ∀ i : Fin a, |c i.castSucc.castSucc (Fin.last a).castSucc - A i.castSucc (Fin.last a)| < ε} ∩
        ({c | ∀ i : Fin a, |c i.castSucc.castSucc (Fin.last (a+1)) - A i.castSucc (Fin.last a)| < ε} ∩
        {c | c (Fin.last a).castSucc (Fin.last (a+1)) < t+ε})))
      refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_lt (by fun_prop) measurable_const
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
      · simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt (by fun_prop) measurable_const
      · exact measurableSet_lt (by fun_prop) measurable_const
    have hEp : 0 < (blockLaw B μ (a+2)) E := by
      rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm (a+2)) hE]
      exact ENNReal.toReal_pos_iff.mp hd |>.1
    obtain ⟨C, hCE, hCs⟩ := Measure.nonempty_inter_support_of_pos hEp
    exact ⟨C, hCs, hCE⟩
  choose C hCs hC using fun k : ℕ => happrox (1 / (k+1)) (by positivity)
  obtain ⟨L, hLs, φ, hφ, hlim⟩ := (blockLaw_support_compact hm hb (a+2)).tendsto_subseq hCs
  have hzero : Tendsto (fun k => 1 / ((φ k : ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hentry : ∀ i j, Tendsto (fun k => C (φ k) i j) atTop (𝓝 (L i j)) := by
    intro i j
    exact ((continuous_apply j).comp (continuous_apply i)).continuousAt.tendsto.comp hlim
  have heq : ∀ (i j : Fin (a+2)) (v : ℝ),
      (∀ k, |C k i j-v| < 1/((k:ℝ)+1)) → L i j = v := by
    intro i j v hv
    have hl := ((hentry i j).sub (tendsto_const_nhds (x := v))).abs
    have hg : |L i j-v| ≤ 0 := le_of_tendsto_of_tendsto hl hzero
      (Filter.Eventually.of_forall fun k => (hv (φ k)).le)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hg (abs_nonneg _)))
  refine ⟨L, hLs, ?_, ?_, ?_, ?_⟩
  · intro i j; exact heq _ _ _ (fun k => (hC k).1 i j)
  · intro i; exact heq _ _ _ (fun k => (hC k).2.1 i)
  · intro i; exact heq _ _ _ (fun k => (hC k).2.2.1 i)
  · have htlim := tendsto_const_nhds.add hzero (a := t)
    simp only [add_zero] at htlim
    exact le_of_tendsto_of_tendsto (hentry _ _) htlim
      (Filter.Eventually.of_forall fun k => (hC (φ k)).2.2.2.le)

lemma support_mem_of_continuous_invariant {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : Continuous f) (hi : ∀ s, MeasurableSet s → μ (f ⁻¹' s) = μ s)
    {x : X} (hx : x ∈ μ.support) : f x ∈ μ.support := by
  apply (Measure.mem_support_iff_forall _).mpr
  intro U hU
  obtain ⟨V, hVU, hVo, hxV⟩ := mem_nhds_iff.mp hU
  have hp := (Measure.mem_support_iff_forall x).mp hx _
    (hf.continuousAt.preimage_mem_nhds (hVo.mem_nhds hxV))
  rw [hi V hVo.measurableSet] at hp
  exact hp.trans_le (measure_mono hVU)

lemma blockLaw_support_swap {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω}
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ)
    {n : ℕ} {A : Fin n → Fin n → ℝ} (hA : A ∈ (blockLaw B μ n).support)
    (i j : Fin n) :
    (fun x y => A ((Equiv.swap i j) x) ((Equiv.swap i j) y)) ∈
      (blockLaw B μ n).support := by
  have hcoe : ∀ x : Fin n, ((Equiv.swap i j) x).val = (Equiv.swap i.val j.val) x.val := by
    intro x
    by_cases hxi : x = i
    · subst x; simp
    by_cases hxj : x = j
    · subst x; simp
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxj,
      Equiv.swap_apply_of_ne_of_ne (fun h => hxi (Fin.ext h)) (fun h => hxj (Fin.ext h))]
  let f : (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) :=
    fun A x y => A ((Equiv.swap i j) x) ((Equiv.swap i j) y)
  have hf : Continuous f := by unfold f; fun_prop
  apply support_mem_of_continuous_invariant hf _ hA
  intro S hS
  rw [blockLaw, Measure.map_apply (measurable_arrayBlock hm n) (hS.preimage hf.measurable),
    Measure.map_apply (measurable_arrayBlock hm n) hS]
  have h := (hwe (Equiv.swap i.val j.val) (swap_hasFiniteSupport i.val j.val)).measure_mem_eq
    (s := (fun b : RealArray => arrayBlock (fun _ : Unit => b) n ()) ⁻¹' S)
    (hS.preimage (by unfold arrayBlock; fun_prop))
  convert h.symm using 2 <;> first | (with_reducible_and_instances rfl) | (ext ω <;> simp only [Set.mem_preimage, arrayBlock, f, hcoe] <;> rfl)

lemma isClosed_setOf_posSemidef (n : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} := by
  have he : {A : Matrix (Fin n) (Fin n) ℝ | A.PosSemidef} =
      {A : Matrix (Fin n) (Fin n) ℝ | ∀ i j, A i j = A j i} ∩ {A | ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (A *ᵥ v)} := by
    ext A
    constructor
    · intro h
      refine ⟨?_, fun v => by simpa using h.dotProduct_mulVec_nonneg v⟩
      intro i j
      have he := congrFun (congrFun h.1 i) j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he.symm
    · rintro ⟨hs, hq⟩
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · ext i j; exact hs j i
      · intro v; simpa using hq v
  rw [he]
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun v => isClosed_le continuous_const (by unfold dotProduct Matrix.mulVec; fun_prop)

lemma blockLaw_support_gram {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} (hm : Measurable B) {D : ℝ}
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) {n : ℕ}
    {A : Fin n → Fin n → ℝ} (hA : A ∈ (blockLaw B μ n).support) :
    Matrix.PosSemidef A ∧ ∀ i, A i i = D := by
  have hdclosed : IsClosed {A : Fin n → Fin n → ℝ | ∀ i, A i i = D} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  have hc : IsClosed {A : Fin n → Fin n → ℝ | Matrix.PosSemidef A ∧ ∀ i, A i i = D} :=
    (isClosed_setOf_posSemidef n).inter hdclosed
  apply Measure.support_subset_of_isClosed hc _ hA
  rw [mem_ae_iff, blockLaw, Measure.map_apply (measurable_arrayBlock hm n) hc.isOpen_compl.measurableSet]
  have he : arrayBlock B n ⁻¹' {A : Fin n → Fin n → ℝ | Matrix.PosSemidef A ∧ ∀ i, A i i = D}ᶜ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact hω ⟨hpsd ω n, fun i => hdiag ω i⟩
  rw [he, measure_empty]

lemma real_posSemidef_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) : ∀ i j, A i j = A j i := by
  intro i j
  have h := congrFun (congrFun hA.1 i) j
  simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm

 
theorem gg_duplicate_supported {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {a : ℕ} (ha : 0 < a) {A : Fin (a+1) → Fin (a+1) → ℝ}
    (hA : A ∈ (blockLaw B μ (a+1)).support) (p : Fin (a+1)) {t : ℝ}
    (ht : ∀ i, i ≠ p → A i p ≤ t) :
    ∃ C ∈ (blockLaw B μ (a+2)).support,
      (∀ i j : Fin (a+1), C i.castSucc j.castSucc = A i j) ∧
      (∀ i : Fin (a+1), i ≠ p → C i.castSucc (Fin.last (a+1)) = A i p) ∧
      C p.castSucc (Fin.last (a+1)) ≤ t := by
  let e := Equiv.swap p (Fin.last a)
  let A' : Fin (a+1) → Fin (a+1) → ℝ := fun i j => A (e i) (e j)
  have hA' : A' ∈ (blockLaw B μ (a+1)).support := blockLaw_support_swap hm hwe hA p (Fin.last a)
  have ht' : ∀ i : Fin a, A' i.castSucc (Fin.last a) ≤ t := by
    intro i
    simp only [A', e, Equiv.swap_apply_right]
    apply ht
    intro he
    have hh := congrArg e he
    simp only [e, Equiv.swap_apply_self, Equiv.swap_apply_left] at hh
    exact Fin.castSucc_ne_last i hh
  obtain ⟨C, hCs, hC0, hC1, hC2, hC3⟩ :=
    gg_duplicate_supported_last hm hsym hwe hGG hb ha hA' ht'
  have hgramA := blockLaw_support_gram hm hpsd hdiag hA
  have hgramC := blockLaw_support_gram hm hpsd hdiag hCs
  have hfull : ∀ i j : Fin (a+1), C i.castSucc j.castSucc = A' i j := by
    intro i j
    refine Fin.lastCases ?_ (fun ii => ?_) i
    · refine Fin.lastCases ?_ (fun jj => ?_) j
      · exact (hgramC.2 _).trans (hgramA.2 _).symm
      · rw [real_posSemidef_symm hgramC.1, hC1]
        exact real_posSemidef_symm hgramA.1 _ _
    · refine Fin.lastCases ?_ (fun jj => ?_) j
      · exact hC1 ii
      · exact hC0 ii jj
  let e' := Equiv.swap p.castSucc (Fin.last a).castSucc
  have hecast : ∀ i : Fin (a+1), e' i.castSucc = (e i).castSucc := by
    intro i
    by_cases hi : i = p
    · subst i; simp [e', e]
    by_cases hil : i = Fin.last a
    · subst i; simp [e', e]
    rw [show e i = i from Equiv.swap_apply_of_ne_of_ne hi hil]
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (Fin.castSucc_injective _ h))
      (fun h => hil (Fin.castSucc_injective _ h))
  have helast : e' (Fin.last (a+1)) = Fin.last (a+1) := by
    apply Equiv.swap_apply_of_ne_of_ne <;> exact (Fin.castSucc_ne_last _).symm
  refine ⟨fun i j => C (e' i) (e' j), blockLaw_support_swap hm hwe hCs _ _, ?_, ?_, ?_⟩
  · intro i j
    change C (e' i.castSucc) (e' j.castSucc) = _
    rw [hecast, hecast, hfull]
    simp only [A', e, Equiv.swap_apply_self]
  · intro i hip
    change C (e' i.castSucc) (e' (Fin.last (a+1))) = _
    rw [hecast, helast]
    have heil : e i ≠ Fin.last a := by
      intro he
      have he' := congrArg e he
      simp only [e, Equiv.swap_apply_self, Equiv.swap_apply_right] at he'
      exact hip he'
    obtain ⟨ii, hii⟩ := Fin.eq_castSucc_of_ne_last heil
    rw [← hii, hC2]
    dsimp [A']
    have heii : e ii.castSucc = i := by rw [hii]; exact Equiv.swap_apply_self _ _ _
    rw [heii]
    simp [e]
  · change C (e' p.castSucc) (e' (Fin.last (a+1))) ≤ _
    rw [hecast, helast]
    simpa only [e, Equiv.swap_apply_left] using hC3

lemma psd_bilinear_symm {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (x y : ι → ℝ) :
    x ⬝ᵥ (B *ᵥ y) = y ⬝ᵥ (B *ᵥ x) := by
  have hs : ∀ i j, B i j = B j i := by
    intro i j
    have h := congrFun (congrFun hB.1 i) j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h.symm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hs j i]
  ring

lemma psd_cauchy_schwarz {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) (x y : ι → ℝ) :
    (x ⬝ᵥ (B *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (B *ᵥ x)) * (y ⬝ᵥ (B *ᵥ y)) := by
  have hq : ∀ t : ℝ, 0 ≤ (x ⬝ᵥ (B *ᵥ x)) * (t * t) +
      (2 * (x ⬝ᵥ (B *ᵥ y))) * t + (y ⬝ᵥ (B *ᵥ y)) := by
    intro t
    have h := hB.dotProduct_mulVec_nonneg (t • x + y)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      dotProduct_add, add_dotProduct, smul_dotProduct, dotProduct_smul,
      smul_eq_mul] at h
    rw [psd_bilinear_symm hB y x] at h
    nlinarith
  have h := discrim_le_zero hq
  dsimp [discrim] at h
  nlinarith

lemma psd_three_gap {B : Matrix (Fin 3) (Fin 3) ℝ} (hB : B.PosSemidef) :
    (B 0 2 - B 0 1) ^ 2 ≤ B 0 0 * (B 1 1 + B 2 2 - 2 * B 1 2) := by
  have hs : B 2 1 = B 1 2 := by
    have h := congrFun (congrFun hB.1 1) 2
    simpa only [Matrix.conjTranspose_apply, star_trivial] using h
  have h := psd_cauchy_schwarz hB ![1, 0, 0] ![0, -1, 1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hs] at h
  nlinarith


lemma groupAverageMatrix_posSemidef {m : ℕ}
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} (hB : B.PosSemidef) :
    (groupAverageMatrix B).PosSemidef := by
  classical
  let C : Matrix (Fin 3 × Fin m) (Fin 3) ℝ := fun a i => if a.1 = i then (m : ℝ)⁻¹ else 0
  have h := hB.conjTranspose_mul_mul_same C
  have heq : C.conjTranspose * B * C = groupAverageMatrix B := by
    ext i j
    change (∑ a : Fin 3 × Fin m, (∑ b : Fin 3 × Fin m, C b i * B b a) * C a j) = _
    simp only [C, Fintype.sum_prod_type, ite_mul, zero_mul, mul_ite, mul_zero]
    simp only [Finset.sum_mul]
    dsimp [groupAverageMatrix]
    rw [Finset.sum_comm]
    simp [div_eq_mul_inv, pow_two, mul_assoc, mul_comm]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rwa [heq] at h

lemma groupAverageMatrix_cross {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {i j : Fin 3} {q : ℝ}
    (h : ∀ a b, B (i,a) (j,b) = q) : groupAverageMatrix B i j = q := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [groupAverageMatrix, h, pow_two]
  field_simp

lemma groupAverageMatrix_diag_le {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {i : Fin 3} {D q : ℝ}
    (hd : ∀ a, B (i,a) (i,a) = D)
    (ho : ∀ a b, a ≠ b → B (i,a) (i,b) ≤ q) :
    groupAverageMatrix B i i ≤ D / m + (1 - 1 / (m : ℝ)) * q := by
  classical
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hr : ∀ a, ∑ b : Fin m, B (i,a) (i,b) ≤ D + (m - 1 : ℝ) * q := by
    intro a
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a), hd a]
    have h := Finset.sum_le_sum (s := Finset.univ.erase a)
      (f := fun b => B (i,a) (i,b)) (g := fun _ => q)
      (fun b hb => ho a b (Ne.symm (Finset.mem_erase.mp hb).1))
    simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at h
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hr a)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  dsimp [groupAverageMatrix]
  apply (div_le_iff₀ (sq_pos_of_pos hm')).mpr
  calc
    _ ≤ m * (D + (m - 1 : ℝ) * q) := h
    _ = _ := by field_simp

lemma psd_entry_le_diagonal {ι : Type*} [Fintype ι] {B : Matrix ι ι ℝ}
    (hB : B.PosSemidef) {D : ℝ} (hd : ∀ i, B i i = D) (i j : ι) : B i j ≤ D := by
  classical
  have hD : 0 ≤ D := hd i ▸ hB.diag_nonneg
  have h := psd_cauchy_schwarz hB (Pi.single i 1) (Pi.single j 1)
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, mul_ite, hd] at h
  nlinarith [sq_nonneg (B i j - D)]

lemma groupAverageMatrix_diag_le_common {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {D : ℝ}
    (hB : B.PosSemidef) (hd : ∀ a, B a a = D) (i : Fin 3) :
    groupAverageMatrix B i i ≤ D := by
  have h := groupAverageMatrix_diag_le hm (fun a => hd (i,a))
    (fun a b _ => psd_entry_le_diagonal hB hd (i,a) (i,b))
  have hD : D / (m : ℝ) + (1 - 1 / (m : ℝ)) * D = D := by ring
  rwa [hD] at h

 
lemma duplicated_triple_gap_bound {m : ℕ} (hm : 0 < m)
    {B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ} {D a b c : ℝ}
    (hB : B.PosSemidef) (hd : ∀ i, B i i = D)
    (hab : ∀ i j, B (0,i) (1,j) = a)
    (hac : ∀ i j, B (0,i) (2,j) = b)
    (hbc : ∀ i j, B (1,i) (2,j) = c)
    (h22 : ∀ i j, i ≠ j → B (1,i) (1,j) ≤ c)
    (h33 : ∀ i j, i ≠ j → B (2,i) (2,j) ≤ c) :
    (b - a)^2 ≤ 2 * D * (D - c) / m := by
  have hG := groupAverageMatrix_posSemidef hB
  have h := psd_three_gap hG
  have h00 := groupAverageMatrix_diag_le_common hm hB hd 0
  have h11 := groupAverageMatrix_diag_le hm (fun i => hd (1,i)) h22
  have h22' := groupAverageMatrix_diag_le hm (fun i => hd (2,i)) h33
  have h01 := groupAverageMatrix_cross hm hab
  have h02 := groupAverageMatrix_cross hm hac
  have h12 := groupAverageMatrix_cross hm hbc
  rw [h01, h02, h12] at h
  have hD : 0 ≤ D := (hG.diag_nonneg (i := 0)).trans h00
  have hq : 0 ≤ groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2 * c := by
    have h0 := hG.dotProduct_mulVec_nonneg ![0, -1, 1]
    have hs : groupAverageMatrix B 2 1 = groupAverageMatrix B 1 2 := by
      have he := congrFun (congrFun hG.1 1) 2
      simpa only [Matrix.conjTranspose_apply, star_trivial] using he
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, hs, h12] at h0
    linarith
  calc
    (b - a)^2 ≤ groupAverageMatrix B 0 0 *
        (groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2*c) := h
    _ ≤ D * (groupAverageMatrix B 1 1 + groupAverageMatrix B 2 2 - 2*c) :=
      mul_le_mul_of_nonneg_right h00 hq
    _ ≤ D * (2 * (D / m + (1 - 1 / (m : ℝ)) * c) - 2*c) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    _ = 2 * D * (D - c) / m := by ring

 

lemma no_arbitrary_nonultrametric_duplicates {D a b c : ℝ} (hab : a < b)
    (hex : ∀ m : ℕ, 0 < m → ∃ B : Matrix (Fin 3 × Fin m) (Fin 3 × Fin m) ℝ,
      B.PosSemidef ∧ (∀ i, B i i = D) ∧
      (∀ i j, B (0,i) (1,j) = a) ∧ (∀ i j, B (0,i) (2,j) = b) ∧
      (∀ i j, B (1,i) (2,j) = c) ∧
      (∀ i j, i ≠ j → B (1,i) (1,j) ≤ c) ∧
      (∀ i j, i ≠ j → B (2,i) (2,j) ≤ c)) : False := by
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * D * (D - c) / (b-a)^2)
  obtain ⟨B, hB, hd, h01, h02, h12, h11, h22⟩ := hex (m+1) (by omega)
  have h := duplicated_triple_gap_bound (by omega : 0 < m+1) hB hd h01 h02 h12 h11 h22
  have hp : 0 < (b-a)^2 := sq_pos_of_pos (sub_pos.mpr hab)
  have hm' : (0 : ℝ) < (m+1 : ℕ) := by positivity
  have hbound := (div_lt_iff₀ hp).mp hm
  have hbig := (le_div_iff₀ hm').mp h
  simp only [Nat.cast_add, Nat.cast_one] at hbig
  nlinarith

lemma gg_duplicate_supported_of_two_le {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {n : ℕ} (hn : 2 ≤ n) {A : Fin n → Fin n → ℝ}
    (hA : A ∈ (blockLaw B μ n).support) (p : Fin n) {t : ℝ}
    (ht : ∀ i, i ≠ p → A i p ≤ t) :
    ∃ C ∈ (blockLaw B μ (n+1)).support,
      (∀ i j : Fin n, C i.castSucc j.castSucc = A i j) ∧
      (∀ i : Fin n, i ≠ p → C i.castSucc (Fin.last n) = A i p) ∧
      C p.castSucc (Fin.last n) ≤ t := by
  cases n with
  | zero => omega
  | succ a => exact gg_duplicate_supported hm hsym hwe hGG hb hpsd hdiag (by omega) hA p ht



lemma gg_supported_populations {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support)
    {t : ℝ} (ht : ∀ i j, i ≠ j → Q i j ≤ t) :
    ∀ n, 3 ≤ n → ∃ A ∈ (blockLaw B μ n).support,
      (∀ i j, i ≠ j → A i j ≤ t) ∧
      (∀ i j, tripleLabel i ≠ tripleLabel j → A i j = Q (tripleLabel i) (tripleLabel j)) := by
  have hQsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨Q, hQ, ht, ?_⟩
    intro i j _
    have hh : ∀ i : Fin 3, tripleLabel i = i := fun i => Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [hh, hh]
  | succ n hn ih =>
    obtain ⟨A, hAs, hAo, hAc⟩ := ih
    let p : Fin n := ⟨n % 3, (Nat.mod_lt n (by decide : 0 < 3)).trans_le hn⟩
    have hp : tripleLabel p = tripleLabel (Fin.last n) := by
      apply Fin.ext; exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))
    obtain ⟨C, hCs, hC0, hC1, hCp⟩ := gg_duplicate_supported_of_two_le
      hm hsym hwe hGG hb hpsd hdiag (by omega) hAs p (fun i hi => hAo i p hi)
    have hCsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hCs).1
    refine ⟨C, hCs, ?_, ?_⟩
    · intro i j
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro _
          rw [hCsym]
          by_cases hj : jj = p
          · subst jj; exact hCp
          · rw [hC1 jj hj]; exact hAo jj p hj
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro _
          by_cases hi : ii = p
          · subst ii; exact hCp
          · rw [hC1 ii hi]; exact hAo ii p hi
        · intro hij
          rw [hC0]; exact hAo ii jj (fun he => hij (congrArg Fin.castSucc he))
    · intro i j
      refine Fin.lastCases ?_ (fun ii => ?_) i
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij; exact (hij rfl).elim
        · intro hij
          have hjp : tripleLabel jj ≠ tripleLabel p := by
            intro he; apply hij; exact hp.symm.trans he.symm
          have hjne : jj ≠ p := fun he => hjp (congrArg tripleLabel he)
          rw [hCsym, hC1 jj hjne, hAc jj p hjp, hp, hQsym]
          rfl
      · refine Fin.lastCases ?_ (fun jj => ?_) j
        · intro hij
          have hip : tripleLabel ii ≠ tripleLabel p := by
            intro he; apply hij; exact he.trans hp
          have hine : ii ≠ p := fun he => hip (congrArg tripleLabel he)
          rw [hC1 ii hine, hAc ii p hip, hp]
          rfl
        · intro hij
          rw [hC0]; exact hAc ii jj hij

lemma gg_supported_triple_ordered {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hb : ∀ ω i j, |B ω i j| ≤ D)
    (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support)
    (horder : Q 0 2 ≤ Q 1 2) : Q 0 2 ≤ Q 0 1 := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hQsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
  have hQo : ∀ i j : Fin 3, i ≠ j → Q i j ≤ Q 1 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hlt.le.trans horder
    · exact horder
    · exact (hQsym 1 0).le.trans (hlt.le.trans horder)
    · exact (hij rfl).elim
    · exact le_rfl
    · exact (hQsym 2 0).le.trans horder
    · exact (hQsym 2 1).le
    · exact (hij rfl).elim
  apply no_arbitrary_nonultrametric_duplicates hlt
  intro m hmpos
  obtain ⟨A, hAs, hAo, hAc⟩ := gg_supported_populations hm hsym hwe hGG hb hpsd hdiag
    hQ hQo (3*m) (by omega)
  let e : Fin 3 × Fin m → Fin (3*m) := fun x => ⟨3*x.2.val+x.1.val, by omega⟩
  have he : ∀ i a, tripleLabel (e (i,a)) = i := by
    intro i a
    apply Fin.ext
    dsimp [tripleLabel, e]
    omega
  have hei : Function.Injective e := by
    intro x y hxy
    have hv := congrArg Fin.val hxy
    dsimp [e] at hv
    apply Prod.ext <;> apply Fin.ext <;> omega
  have hgram := blockLaw_support_gram hm hpsd hdiag hAs
  refine ⟨Matrix.submatrix A e e, Matrix.PosSemidef.submatrix hgram.1 e,
    fun _ => hgram.2 _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    change A (e (0,i)) (e (1,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j
    change A (e (0,i)) (e (2,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j
    change A (e (1,i)) (e (2,j)) = _
    rw [hAc _ _ (by rw [he, he]; decide), he, he]
  · intro i j hij
    exact hAo _ _ (fun hh => hij (congrArg Prod.snd (hei hh)))
  · intro i j hij
    exact hAo _ _ (fun hh => hij (congrArg Prod.snd (hei hh)))

lemma array_entry_abs_le_diagonal {B : RealArray} {D : ℝ}
    (hp : ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j))
    (hd : ∀ i, B i i = D) (i j : ℕ) : |B i j| ≤ D := by
  let n := max i j + 1
  let ii : Fin n := ⟨i, by dsimp [n]; omega⟩
  let jj : Fin n := ⟨j, by dsimp [n]; omega⟩
  have hD : 0 ≤ D := (hp n).diag_nonneg (i := ii) |>.trans (hd i).le
  have hs := psd_cauchy_schwarz (hp n) (Pi.single ii 1) (Pi.single jj 1)
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, ite_mul, mul_ite, hd] at hs
  change B i j ^ 2 ≤ D * D at hs
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (B i j - D), sq_nonneg (B i j + D)]

lemma gg_supported_triple_ultrametric {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D)
    {Q : Fin 3 → Fin 3 → ℝ} (hQ : Q ∈ (blockLaw B μ 3).support) :
    min (Q 0 2) (Q 1 2) ≤ Q 0 1 := by
  have hb : ∀ ω i j, |B ω i j| ≤ D :=
    fun ω => array_entry_abs_le_diagonal (hpsd ω) (hdiag ω)
  by_cases ho : Q 0 2 ≤ Q 1 2
  · rw [min_eq_left ho]
    exact gg_supported_triple_ordered hm hsym hwe hGG hb hpsd hdiag hQ ho
  · have ho' : Q 1 2 ≤ Q 0 2 := le_of_not_ge ho
    rw [min_eq_right ho']
    have hQs := blockLaw_support_swap hm hwe hQ 0 1
    have hqsym := real_posSemidef_symm (blockLaw_support_gram hm hpsd hdiag hQ).1
    have hh : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    have h := gg_supported_triple_ordered hm hsym hwe hGG hb hpsd hdiag hQs
      (by simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right, hh] using ho')
    simpa only [Equiv.swap_apply_left, Equiv.swap_apply_right, hh, hqsym 1 0] using h

 

theorem gg_ultrametric_triple {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, min (B ω 0 2) (B ω 1 2) ≤ B ω 0 1 := by
  have hs : ∀ᵐ A ∂blockLaw B μ 3, A ∈ (blockLaw B μ 3).support :=
    Measure.support_mem_ae
  have ht : ∀ᵐ A ∂blockLaw B μ 3, min (A 0 2) (A 1 2) ≤ A 0 1 :=
    hs.mono (fun _ h => gg_supported_triple_ultrametric hm hsym hwe hGG hpsd hdiag h)
  exact (ae_map_iff (measurable_arrayBlock hm 3).aemeasurable
    (measurableSet_le (by fun_prop) (by fun_prop))).mp ht


lemma finite_permutation_extending {ι β : Type*} [Fintype ι]
    (f g : ι → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ e : Equiv.Perm β, {b | e b ≠ b}.Finite ∧ ∀ i, e (f i) = g i := by
  classical
  let U : Finset β := Finset.univ.image f ∪ Finset.univ.image g
  let f' : ι → U := fun i => ⟨f i, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
  let g' : ι → U := fun i => ⟨g i, Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))⟩
  have hf' : Function.Injective f' := fun i j h => hf (congrArg Subtype.val h)
  have hg' : Function.Injective g' := fun i j h => hg (congrArg Subtype.val h)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f' g' hf' hg'
  let emb : U ↪ β := Function.Embedding.subtype _
  refine ⟨σ.viaFintypeEmbedding emb, ?_, ?_⟩
  · apply U.finite_toSet.subset
    intro b hb
    by_contra h
    apply hb
    apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
    rintro ⟨a, rfl⟩
    exact h a.2
  · intro i
    change σ.viaFintypeEmbedding emb (emb (f' i)) = emb (g' i)
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image, hσ]

lemma gg_ultrametric {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hsym : ∀ ω i j, B ω i j = B ω j i)
    (hwe : WeaklyExchangeable B μ) (hGG : HasGhirlandaGuerra B μ)
    {D : ℝ} (hpsd : ∀ ω n, Matrix.PosSemidef (arrayBlock B n ω))
    (hdiag : ∀ ω i, B ω i i = D) :
    ∀ᵐ ω ∂μ, IsUltrametricArray (B ω) := by
  have ht := gg_ultrametric_triple hm hsym hwe hGG hpsd hdiag
  have hall : ∀ i j k, ∀ᵐ ω ∂μ, min (B ω i k) (B ω j k) ≤ B ω i j := by
    intro i j k
    by_cases hij : i = j
    · subst j
      apply ae_of_all
      intro ω
      have hb := array_entry_abs_le_diagonal (hpsd ω) (hdiag ω) i k
      simpa only [min_self, hdiag] using (le_abs_self (B ω i k)).trans hb
    by_cases hik : i = k
    · subst k
      exact ae_of_all _ (fun ω => by rw [hsym ω j i]; exact min_le_right _ _)
    by_cases hjk : j = k
    · subst k
      exact ae_of_all _ (fun ω => min_le_left _ _)
    let f : Fin 3 → ℕ := fun a => a.val
    let g : Fin 3 → ℕ := ![i,j,k]
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [g]
    obtain ⟨e, he, hef⟩ := finite_permutation_extending f g Fin.val_injective hg
    have hh := (hwe e he).ae_mem_snd
      (t := {b : RealArray | min (b 0 2) (b 1 2) ≤ b 0 1})
      (measurableSet_le (by fun_prop) (by fun_prop)) ht
    have he0 : e 0 = i := hef 0
    have he1 : e 1 = j := hef 1
    have he2 : e 2 = k := hef 2
    simpa only [Set.mem_ofPred_eq, permuteArray, he0, he1, he2] using hh
  exact ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => ae_all_iff.mpr (hall i j)))


lemma HasEntryGhirlandaGuerra.map {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → F} (hf : Measurable f) :
    HasEntryGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := by
  intro n hn i A hA t ht
  exact h n hn i ((fun b j k => f (b j k)) ⁻¹' A)
    (hA.preimage (by fun_prop)) (f ⁻¹' t) (ht.preimage hf)

lemma HasEntryGhirlandaGuerra.real_map {Ω E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] {B : Ω → ℕ → ℕ → E} {μ : Measure Ω}
    (h : HasEntryGhirlandaGuerra B μ) {f : E → ℝ} (hf : Measurable f) :
    HasGhirlandaGuerra (fun ω i j => f (B ω i j)) μ := h.map hf

lemma gg_two_links_positive {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {B : Ω → ℕ → ℕ → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hGG : HasEntryGhirlandaGuerra B μ) {A C : Set E}
    (hA : MeasurableSet A) (hC : MeasurableSet C)
    (hpA : 0 < μ.real {ω | B ω 0 1 ∈ A}) (hpC : 0 < μ.real {ω | B ω 0 1 ∈ C}) :
    0 < μ.real ({ω | B ω 0 1 ∈ A} ∩ {ω | B ω 0 2 ∈ C}) := by
  have h := hGG 2 (by omega) 0 {b : Fin 2 → Fin 2 → E | b 0 1 ∈ A}
    (hA.preimage (by fun_prop)) C hC
  change μ.real ({ω | B ω 0 1 ∈ A} ∩ {ω | B ω 0 2 ∈ C}) = _ at h
  rw [h]
  exact add_pos_of_pos_of_nonneg (div_pos (mul_pos hpA hpC) (by norm_num))
    (div_nonneg (Finset.sum_nonneg (fun _ _ => measureReal_nonneg)) (by norm_num))

lemma ultrametric_no_crossing {r t : RealArray}
    (hr : IsUltrametricArray r) (ht : IsUltrametricArray t)
    (hs : IsUltrametricArray (fun i j => r i j + t i j))
    (hrsym : ∀ i j, r i j = r j i) (htsym : ∀ i j, t i j = t j i) :
    ¬ (r 0 1 < r 0 2 ∧ t 0 2 < t 0 1) := by
  rintro ⟨hR, hT⟩
  have hr23 : r 1 2 = r 0 1 := by
    have h1 := hr 0 1 2
    have h2 := hr 1 2 0
    rw [hrsym 1 0, hrsym 2 0, min_eq_left hR.le] at h2
    have : r 1 2 ≤ r 0 1 := by
      by_contra! hn
      exact (lt_min hR hn).not_ge h1
    exact le_antisymm this h2
  have ht23 : t 1 2 = t 0 2 := by
    have h1 := ht 0 2 1
    have h2 := ht 1 2 0
    rw [htsym 2 1] at h1
    rw [htsym 1 0, htsym 2 0, min_eq_right hT.le] at h2
    have : t 1 2 ≤ t 0 2 := by
      by_contra! hn
      exact (lt_min hT hn).not_ge h1
    exact le_antisymm this h2
  have hh := hs 1 2 0
  simp only [hrsym 1 0, hrsym 2 0, htsym 1 0, htsym 2 0, hr23, ht23] at hh
  exact (lt_min (by linarith) (by linarith)).not_ge hh

 

theorem jointGG_support_ordered {Ω : Type*} [MeasurableSpace Ω]
    {R T : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hR : Measurable R) (hT : Measurable T)
    (hGG : HasEntryGhirlandaGuerra (fun ω i j => (R ω i j, T ω i j)) μ)
    (huR : ∀ᵐ ω ∂μ, IsUltrametricArray (R ω))
    (huT : ∀ᵐ ω ∂μ, IsUltrametricArray (T ω))
    (huS : ∀ᵐ ω ∂μ, IsUltrametricArray (fun i j => R ω i j + T ω i j))
    (hsR : ∀ᵐ ω ∂μ, ∀ i j, R ω i j = R ω j i)
    (hsT : ∀ᵐ ω ∂μ, ∀ i j, T ω i j = T ω j i) :
    let ν := μ.map (fun ω => (R ω 0 1, T ω 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  dsimp only
  intro x hx y hy hxy
  by_contra! hc
  let a := (x.1+y.1)/2
  let b := (x.2+y.2)/2
  let A : Set (ℝ × ℝ) := {z | z.1 < a ∧ b < z.2}
  let C : Set (ℝ × ℝ) := {z | a < z.1 ∧ z.2 < b}
  have hAo : IsOpen A := (isOpen_lt continuous_fst continuous_const).inter
    (isOpen_lt continuous_const continuous_snd)
  have hCo : IsOpen C := (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_snd continuous_const)
  have hm : Measurable (fun ω => (R ω 0 1, T ω 0 1)) := by fun_prop
  have hyp : 0 < (μ.map (fun ω => (R ω 0 1,T ω 0 1))) A :=
    (Measure.mem_support_iff_forall x).mp hx A (hAo.mem_nhds (by dsimp [A,a,b]; constructor <;> linarith))
  have hxp : 0 < (μ.map (fun ω => (R ω 0 1,T ω 0 1))) C :=
    (Measure.mem_support_iff_forall y).mp hy C (hCo.mem_nhds (by dsimp [C,a,b]; constructor <;> linarith))
  rw [Measure.map_apply hm hAo.measurableSet] at hyp
  rw [Measure.map_apply hm hCo.measurableSet] at hxp
  have hp := gg_two_links_positive hGG hAo.measurableSet hCo.measurableSet
    (ENNReal.toReal_pos hyp.ne' (measure_ne_top _ _))
    (ENNReal.toReal_pos hxp.ne' (measure_ne_top _ _))
  have hz : μ ({ω | (R ω 0 1,T ω 0 1) ∈ A} ∩
      {ω | (R ω 0 2,T ω 0 2) ∈ C}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [huR,huT,huS,hsR,hsT] with ω hr ht hs hsr hst
    rintro ⟨ha,hc⟩
    exact ultrametric_no_crossing hr ht hs hsr hst
      ⟨ha.1.trans hc.1, hc.2.trans ha.2⟩
  rw [measureReal_def, hz, ENNReal.toReal_zero] at hp
  exact lt_irrefl 0 hp

end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_ArrayGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Array Geometry. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal Matrix
namespace IsingPerceptron

lemma HasGhirlandaGuerra.congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {B C : Ω → RealArray} {μ : Measure Ω} (h : HasGhirlandaGuerra B μ) (he : B =ᵐ[μ] C) :
    HasGhirlandaGuerra C μ := by
  have hm (P : RealArray → Prop) : μ.real {ω | P (C ω)} = μ.real {ω | P (B ω)} := by
    apply measureReal_congr
    filter_upwards [he] with ω hω
    change P (C ω) = P (B ω)
    rw [hω]
  intro n hn i A hA t ht
  change μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i n ∈ t} =
    (μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A} * μ.real {ω | C ω 0 1 ∈ t}) / n +
    (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) / n
  rw [hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i n ∈ t),
    hm (fun b => (fun j k : Fin n => b j k) ∈ A), hm (fun b => b 0 1 ∈ t)]
  have hs : (∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => C ω j k) ∈ A ∧ C ω i j ∈ t}) =
      ∑ j ∈ Finset.univ.erase i, μ.real {ω | (fun j k : Fin n => B ω j k) ∈ A ∧ B ω i j ∈ t} := by
    apply Finset.sum_congr rfl
    intro j _
    exact hm (fun b => (fun j k : Fin n => b j k) ∈ A ∧ b i j ∈ t)
  rw [hs]
  exact h n hn i A hA t ht

lemma isClosed_gramDiagonal (D : ℝ) : IsClosed {B | GramDiagonal D B} := by
  change IsClosed ({B : RealArray | ∀ n, Matrix.PosSemidef (fun i j : Fin n => B i j)} ∩
    {B | ∀ i, B i i = D})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro n
    exact (isClosed_setOf_posSemidef n).preimage (by fun_prop)
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_eq (by fun_prop) continuous_const)

lemma GramDiagonal.symm {D : ℝ} {B : RealArray} (h : GramDiagonal D B) (i j : ℕ) : B i j = B j i := by
  let n := max i j+1
  let ii : Fin n := ⟨i,by omega⟩
  let jj : Fin n := ⟨j,by omega⟩
  exact real_posSemidef_symm (h.1 n) ii jj

lemma GramDiagonal.default {D : ℝ} (hD : 0 ≤ D) :
    GramDiagonal D (fun i j => if i=j then D else 0) := by
  constructor
  · intro n
    have he : (fun i j : Fin n => if (i:ℕ)=(j:ℕ) then D else 0) =
        Matrix.diagonal (fun _ : Fin n => D) := by
      ext i j
      simp only [Matrix.diagonal_apply,Fin.val_inj]
    rw [he]
    exact Matrix.PosSemidef.diagonal (fun _ => hD)
  · intro i
    simp

 

lemma gg_ultrametric_ae {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hm : Measurable B) (hwe : WeaklyExchangeable B μ) (hgg : HasGhirlandaGuerra B μ)
    {D : ℝ} (hD : 0 ≤ D) (hG : ∀ᵐ ω ∂μ, GramDiagonal D (B ω)) :
    ∀ᵐ ω ∂μ, IsUltrametricArray (B ω) := by
  classical
  let C : Ω → RealArray := fun ω => if GramDiagonal D (B ω) then B ω else fun i j => if i=j then D else 0
  have hc : Measurable C := hm.ite ((isClosed_gramDiagonal D).measurableSet.preimage hm) measurable_const
  have he : B =ᵐ[μ] C := hG.mono (fun ω hω => by simp only [C,ite_eq_left hω])
  have hCG : ∀ ω, GramDiagonal D (C ω) := by
    intro ω
    by_cases h : GramDiagonal D (B ω)
    · simpa only [C,ite_eq_left h] using h
    · simpa only [C,ite_eq_right h] using GramDiagonal.default hD
  have hcwe : WeaklyExchangeable C μ := by
    intro e hefin
    have ht := (IdentDistrib.of_ae_eq hm.aemeasurable he).comp
      (u := permuteArray e) (by unfold permuteArray; fun_prop)
    exact (IdentDistrib.of_ae_eq hm.aemeasurable he).symm.trans ((hwe e hefin).trans ht)
  have ht := gg_ultrametric hc (fun ω => (hCG ω).symm) hcwe (hgg.congr_ae he)
    (fun ω => (hCG ω).1) (fun ω => (hCG ω).2)
  filter_upwards [ht,he] with ω ht he
  simpa only [he] using ht


end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma le_cdf_overlapQuantile {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u : ℝ} (hu : u ≤ 1) :
    u ≤ cdf μ (overlapQuantile μ u) := by
  rw [← (cdf μ).iInf_Ioi_eq]
  apply le_ciInf
  intro y
  obtain ⟨x,hx,hxy⟩ := exists_lt_of_csInf_lt (quantileSet_nonempty hs hu) y.2
  exact hx.2.trans ((monotone_cdf μ) hxy.le)

lemma overlapQuantile_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1)
    (hx : x ∈ Icc (0:ℝ) 1) : overlapQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  constructor
  · intro h
    exact (le_cdf_overlapQuantile hs hu.2.le).trans ((monotone_cdf μ) h)
  · intro h
    exact csInf_le (quantileSet_bddBelow μ u) ⟨hx,h⟩

lemma cdf_of_lt_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {x : ℝ} (hx : x < 0) : cdf μ x = 0 := by
  rw [cdf_eq_real,Measure.real]
  have he : μ (Iic x) = 0 := by
    apply measure_mono_null (t := {y : ℝ | ¬y ∈ Icc (0:ℝ) 1}) _ (ae_iff.mp hs)
    intro y hy hy'
    exact (not_le.mpr (hx.trans_le hy'.1)) hy
  rw [he,ENNReal.toReal_zero]

lemma quantileFunction_le_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    quantileFunction μ u ≤ x ↔ u ≤ cdf μ x := by
  by_cases hx : x < 0
  · rw [cdf_of_lt_zero hs hx]
    exact iff_of_false (not_le.mpr (hx.trans_le (quantileFunction_mem hs u).1))
      (not_le.mpr hu.1)
  · by_cases hx' : x ≤ 1
    · simpa only [quantileFunction,min_eq_left hu.2.le] using overlapQuantile_le_iff hs hu ⟨le_of_not_gt hx,hx'⟩
    · have hc : cdf μ x = 1 := le_antisymm (cdf_le_one μ x)
        (by simpa only [cdf_one_of_unit_support hs] using (monotone_cdf μ) (le_of_not_ge hx'))
      rw [hc]
      exact iff_of_true ((quantileFunction_mem hs u).2.trans (le_of_not_ge hx')) hu.2.le

lemma unitUniform_Iic {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) :
    unitUniform (Iic a) = ENNReal.ofReal a := by
  rw [unitUniform,Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := volume)),
    Measure.restrict_apply measurableSet_Iic,inter_comm,Set.Ioc_inter_Iic]
  simp only [inf_eq_right.mpr ha.2,Real.volume_Ioc,sub_zero]

lemma quantile_preimage_Iic {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hs : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (x : ℝ) :
    quantileFunction μ ⁻¹' Iic x =ᵐ[unitUniform] Iic (cdf μ x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact propext (quantileFunction_le_iff hs hu)


end IsingPerceptron

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralArrayGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram structure and replica symmetry for spectral arrays retaining common disorder. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_permuteSpectralArray {m : ℕ} (e : ℕ → ℕ) :
    Continuous (permuteSpectralArray (m := m) e) := by
  unfold permuteSpectralArray
  fun_prop

lemma scalar_of_spectral_exchangeable {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (f : SpectralEntry m → ℝ) (hf : Measurable f) :
    WeaklyExchangeable (fun x i j => f (x (i,j))) (Q : Measure (SpectralArray m)) := by
  intro e _
  have hm : Measurable (fun x : SpectralArray m => fun i j => f (x (i,j))) := by fun_prop
  refine ⟨hm.aemeasurable, (hm.comp (continuous_permuteSpectralArray e).measurable).aemeasurable, ?_⟩
  calc
    _ = ((Q : Measure (SpectralArray m)).map (permuteSpectralArray e)).map
        (fun x i j => f (x (i,j))) :=
      congrArg (Measure.map (fun x i j => f (x (i,j)))) (hE e).symm
    _ = _ := Measure.map_map hm (continuous_permuteSpectralArray e).measurable

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGGGeometry
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology _root_.OAI.InvariantIsing.spectralLinearLaw_probability
attribute [-simp] _root_.OAI.InvariantIsing.cavityGroupBlockOfBlock_view
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Published ultrametricity and synchronization applied to spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology Matrix

namespace InvariantIsing

lemma continuous_spectralLinearEntry {m : ℕ} (w : Fin m → ℝ) :
    Continuous (spectralLinearEntry w) := by
  unfold spectralLinearEntry
  fun_prop

lemma continuous_spectralLinearArray {m : ℕ} (w : Fin m → ℝ) :
    Continuous (spectralLinearArray w) := by
  unfold spectralLinearArray spectralLinearEntry
  fun_prop

lemma spectralGram_linear {m : ℕ} {x : SpectralArray m} (hG : SpectralGram x)
    (q w : Fin m → ℝ) (hd : ∀ i a, (x (i,i) a : ℝ) = q a)
    (hw : ∀ a, 0 ≤ w a) :
    GramDiagonal (∑ a, w a * q a) (spectralLinearArray w x) := by
  constructor
  · intro n
    have hp := Matrix.posSemidef_sum Finset.univ (fun a _ => (hG a n).smul (hw a))
    have he : (fun i j : Fin n => spectralLinearArray w x i j) =
        ∑ a : Fin m, w a • (fun i j : Fin n => spectralCoordinateArray a x i j) := by
      ext i j
      simp [spectralLinearArray, spectralLinearEntry, spectralCoordinateArray]
    rw [he]
    exact hp
  · intro i
    simp only [spectralLinearArray, spectralLinearEntry, hd]

lemma spectralGG_linear_ultrametric {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray m)), IsUltrametricArray (spectralLinearArray w x) := by
  exact gg_ultrametric_ae (continuous_spectralLinearArray w).measurable
    (scalar_of_spectral_exchangeable hE (spectralLinearEntry w)
      (continuous_spectralLinearEntry w).measurable)
    (hgg.real_map (continuous_spectralLinearEntry w).measurable)
    (Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (hq a))
    (by filter_upwards [hG, hd] with x hx hdx; exact spectralGram_linear hx q w hdx hw)

/-- Nonnegative combinations of the actual spectral and tree coordinates have
ordered joint support. This is the finite-vector consequence used for the
manuscript's simultaneous overlap paths. -/
theorem spectralGG_support_ordered {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w z : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a) :
    let ν := (Q : Measure (SpectralArray m)).map
      (fun x => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1))
    ∀ x ∈ ν.support, ∀ y ∈ ν.support, x.1 < y.1 → x.2 ≤ y.2 := by
  have hsum := spectralGG_linear_ultrametric hgg hG q hq hd hE
    (w + z) (fun a => add_nonneg (hw a) (hz a))
  have he (x : SpectralArray m) : spectralLinearArray (w + z) x =
      fun i j => spectralLinearArray w x i j + spectralLinearArray z x i j := by
    funext i j
    simp only [spectralLinearArray, spectralLinearEntry, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  simp_rw [he] at hsum
  exact jointGG_support_ordered (continuous_spectralLinearArray w).measurable
    (continuous_spectralLinearArray z).measurable
    (hgg.map (f := fun x => (spectralLinearEntry w x, spectralLinearEntry z x))
      ((continuous_spectralLinearEntry w).prodMk (continuous_spectralLinearEntry z)).measurable)
    (spectralGG_linear_ultrametric hgg hG q hq hd hE w hw)
    (spectralGG_linear_ultrametric hgg hG q hq hd hE z hz) hsum
    (by filter_upwards [hG, hd] with x hx hdx
        exact (spectralGram_linear hx q w hdx hw).symm)
    (by filter_upwards [hG, hd] with x hx hdx
        exact (spectralGram_linear hx q z hdx hz).symm)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.IsingPerceptron_OrderedQuantile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordered Quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal
namespace IsingPerceptron

lemma map_restrict_fst_rectangle (μ : Measure (ℝ × ℝ)) {S T : Set ℝ} (hS : MeasurableSet S) :
    ((μ.restrict (univ ×ˢ T)).map Prod.fst) S = μ (S ×ˢ T) := by
  rw [Measure.map_apply measurable_fst hS,Measure.restrict_apply (hS.preimage measurable_fst)]
  congr 1
  ext x
  simp

lemma map_restrict_snd_rectangle (μ : Measure (ℝ × ℝ)) {S T : Set ℝ} (hT : MeasurableSet T) :
    ((μ.restrict (S ×ˢ univ)).map Prod.snd) T = μ (S ×ˢ T) := by
  rw [Measure.map_apply measurable_snd hT,Measure.restrict_apply (hT.preimage measurable_snd)]
  congr 1
  ext x
  simp [and_comm]

lemma measure_pair_eq_of_lower_rectangles {μ ν : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (h : ∀ a b : ℝ, μ (Iic a ×ˢ Iic b) = ν (Iic a ×ˢ Iic b))
    (hU : μ univ = ν univ) : μ = ν := by
  have hfirst (a : ℝ) : (μ.restrict (Iic a ×ˢ univ)).map Prod.snd =
      (ν.restrict (Iic a ×ˢ univ)).map Prod.snd := by
    apply Measure.ext_of_Iic
    intro b
    rw [map_restrict_snd_rectangle μ measurableSet_Iic,map_restrict_snd_rectangle ν measurableSet_Iic]
    exact h a b
  have hsecond (T : Set ℝ) (hT : MeasurableSet T) :
      (μ.restrict (univ ×ˢ T)).map Prod.fst = (ν.restrict (univ ×ˢ T)).map Prod.fst := by
    apply Measure.ext_of_Iic
    intro a
    rw [map_restrict_fst_rectangle μ measurableSet_Iic,map_restrict_fst_rectangle ν measurableSet_Iic]
    have he := congrArg (fun ρ : Measure ℝ => ρ T) (hfirst a)
    simpa only [map_restrict_snd_rectangle μ hT,map_restrict_snd_rectangle ν hT] using he
  apply ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod _ hU
  rintro _ ⟨S,hS,T,hT,rfl⟩
  have he := congrArg (fun ρ : Measure ℝ => ρ S) (hsecond T hT)
  simpa only [map_restrict_fst_rectangle μ hS,map_restrict_fst_rectangle ν hS] using he

lemma ordered_pair_cdf (μ : Measure (ℝ × ℝ))
    (ho : ∀ x ∈ μ.support, ∀ y ∈ μ.support, x.1 < y.1 → x.2 ≤ y.2) (a b : ℝ) :
    μ (Iic a ×ˢ Iic b) = min (μ (Prod.fst ⁻¹' Iic a)) (μ (Prod.snd ⁻¹' Iic b)) := by
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iic a
  let T : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iic b
  have hrect : Iic a ×ˢ Iic b = S ∩ T := rfl
  rw [hrect]
  change μ (S ∩ T) = min (μ S) (μ T)
  have hsupport : ∀ᵐ x ∂μ, x ∈ μ.support := μ.support_mem_ae
  by_cases h : ∀ x ∈ μ.support, x ∈ S → x ∈ T
  · have hst : S ≤ᵐ[μ] T := hsupport.mono (fun x hx => h x hx)
    rw [min_eq_left (measure_mono_ae hst)]
    apply measure_congr
    filter_upwards [hst] with x hx
    exact propext ⟨fun hh => hh.1,fun hh => ⟨hh,hx hh⟩⟩
  · push Not at h
    obtain ⟨x,hx,hxs,hxt⟩ := h
    have hts : T ≤ᵐ[μ] S := by
      filter_upwards [hsupport] with y hy
      intro hyt
      change y.1 ≤ a
      by_contra! hy'
      have hxy := ho x hx y hy (lt_of_le_of_lt hxs hy')
      exact hxt (hxy.trans hyt)
    rw [min_eq_right (measure_mono_ae hts)]
    apply measure_congr
    filter_upwards [hts] with y hy
    exact propext ⟨fun hh => hh.2,fun hh => ⟨hy hh,hh⟩⟩

lemma pair_quantile_cdf {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0:ℝ) 1) (hν : ∀ᵐ x ∂ν, x ∈ Icc (0:ℝ) 1) (a b : ℝ) :
    (unitUniform.map (fun u => (quantileFunction μ u,quantileFunction ν u))) (Iic a ×ˢ Iic b) =
      min (μ (Iic a)) (ν (Iic b)) := by
  rw [Measure.map_apply ((monotone_quantileFunction hμ).measurable.prodMk
      (monotone_quantileFunction hν).measurable) (measurableSet_Iic.prod measurableSet_Iic)]
  have he : (fun u => (quantileFunction μ u,quantileFunction ν u)) ⁻¹' (Iic a ×ˢ Iic b) =ᵐ[unitUniform]
      Iic (min (cdf μ a) (cdf ν b)) := by
    filter_upwards [quantile_preimage_Iic hμ a,quantile_preimage_Iic hν b] with u hu hv
    change (quantileFunction μ u ≤ a ∧ quantileFunction ν u ≤ b) = (u ≤ min (cdf μ a) (cdf ν b))
    rw [le_min_iff]
    exact congrArg₂ And hu hv
  rw [measure_congr he,unitUniform_Iic ⟨le_min (cdf_nonneg μ a) (cdf_nonneg ν b),
    (min_le_left _ _).trans (cdf_le_one μ a)⟩,ENNReal.ofReal_min,ofReal_cdf,ofReal_cdf]

 

theorem ordered_pair_quantile_law {ρ : Measure (ℝ × ℝ)} [IsProbabilityMeasure ρ]
    (ho : ∀ x ∈ ρ.support, ∀ y ∈ ρ.support, x.1 < y.1 → x.2 ≤ y.2)
    (hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0:ℝ) 1 ∧ x.2 ∈ Icc (0:ℝ) 1) :
    unitUniform.map (fun u => (quantileFunction (ρ.map Prod.fst) u,quantileFunction (ρ.map Prod.snd) u)) = ρ := by
  let : IsProbabilityMeasure (ρ.map Prod.fst) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (ρ.map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance
  have hμ : ∀ᵐ x ∂ρ.map Prod.fst, x ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_fst.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.1))
  have hν : ∀ᵐ x ∂ρ.map Prod.snd, x ∈ Icc (0:ℝ) 1 :=
    (ae_map_iff measurable_snd.aemeasurable measurableSet_Icc).mpr (hs.mono (fun _ h => h.2))
  let : IsProbabilityMeasure (unitUniform.map (fun u =>
      (quantileFunction (ρ.map Prod.fst) u,quantileFunction (ρ.map Prod.snd) u))) :=
    (Measure.isProbabilityMeasure_map_iff ((monotone_quantileFunction hμ).measurable.prodMk
      (monotone_quantileFunction hν).measurable).aemeasurable).mpr inferInstance
  apply measure_pair_eq_of_lower_rectangles _ (by simp)
  intro a b
  rw [pair_quantile_cdf hμ hν,ordered_pair_cdf ρ ho,
    Measure.map_apply measurable_fst measurableSet_Iic,Measure.map_apply measurable_snd measurableSet_Iic]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal







open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal





open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal





open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Core_Variational
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral overlap deficit

The deficit `D` is equation (1.4) of the manuscript. Global bounded monotone
representatives are used for paths on `(0,1)`; endpoint values never enter the
integrals.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace InvariantIsing

lemma OverlapPath.integrable (p : OverlapPath) : Integrable p.val pathMeasure := by
  apply (integrable_const (1 : ℝ)).mono' p.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (p.nonneg s)] using p.le_one s

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_QuantileProductKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantile form of the ultrametric product kernel, including plateaus. -/

noncomputable section

open MeasureTheory IsingPerceptron Set

namespace InvariantIsing

lemma intervalIntegrable_of_measurable_abs_le {f : ℝ → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ u, |f u| ≤ B) (s t : ℝ) : IntervalIntegrable f volume s t := by
  rw [intervalIntegrable_iff]
  let : IsFiniteMeasure (volume.restrict (uIoc s t)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min s t) (max s t)))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact integrable_of_measurable_abs_le hf hb

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite spectral-group functions from manuscript `rot:f`. -/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolventDerivative_le_one (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) (x : ℝ) :
    projectedResolventDerivative ρ eig hρ hρsum a x ≤ 1 := by
  rw [← sum_projectedResolventDerivative ρ eig hρ hρsum x]
  exact Finset.single_le_sum
    (fun b _ => (projectedResolventDerivative_pos ρ eig hρ hρsum b x).le)
    (Finset.mem_univ a)

theorem hasStrictDerivAt_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 < x) :
    HasStrictDerivAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hm := finiteSecondResolvent_pos (fun a => (hρ a).le) hρsum hs.1
  have hd := hasStrictDerivAt_finiteInverse ρ eig hρ hρsum hx
  have hden : HasStrictDerivAt
      (fun y => finiteInverse ρ eig hρ hρsum y - eig a)
      (-1 / finiteSecondResolvent ρ eig (finiteInverse ρ eig hρ hρsum x)) x := by
    convert! hd.sub_const (eig a) using 1
    all_goals try with_reducible_and_instances rfl
  have hquot := (hasStrictDerivAt_const x (ρ a)).fun_div hden
    (ne_of_gt (sub_pos.mpr (hs.1 a)))
  have heq : (fun y => ρ a / (finiteInverse ρ eig hρ hρsum y - eig a)) =ᶠ[𝓝 x]
      projectedResolvent ρ eig hρ hρsum a := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    simp only [projectedResolvent, ite_eq_left (show 0 < y from hy)]
  convert hquot.congr_of_eventuallyEq heq using 1
  all_goals try with_reducible_and_instances rfl
  simp only [projectedResolventDerivative, ite_eq_left hx]
  field_simp
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint regularity for the finite spectral-group functions. -/

noncomputable section

open scoped BigOperators Topology
open Filter Set

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem projectedResolvent_eq_regular (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) {x : ℝ} (hx : 0 ≤ x) :
    projectedResolvent ρ eig hρ hρsum a x =
      ρ a * x / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)) := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, mul_zero, zero_mul,
      add_zero, zero_div]
  · have hs := finiteInverse_spec ρ eig hρ hρsum h
    have hden : 1 + x * (finiteR ρ eig hρ hρsum x - eig a) =
        x * (finiteInverse ρ eig hρ hρsum x - eig a) := by
      simp only [finiteR, ite_eq_left h]
      field_simp
      ring
    simp only [projectedResolvent, ite_eq_left h, hden]
    field_simp [h.ne', (sub_pos.mpr (hs.1 a)).ne']

/-- The right derivative at the origin is the spectral mass, as asserted
in manuscript `rot:f-derivative`. -/
theorem hasDerivWithinAt_projectedResolvent_zero (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (a : ι) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a) (ρ a) (Ioi 0) 0 := by
  have hcR := continuousAt_finiteR_zero ρ eig hρ hρsum
  have hden : ContinuousAt
      (fun x : ℝ => 1 + x * (finiteR ρ eig hρ hρsum x - eig a)) 0 :=
    continuousAt_const.add (continuousAt_id.mul (hcR.sub continuousAt_const))
  have hquot : Tendsto
      (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a)))
      (𝓝 0) (𝓝 (ρ a)) := by
    have hc : ContinuousAt
        (fun x : ℝ => ρ a / (1 + x * (finiteR ρ eig hρ hρsum x - eig a))) 0 :=
      continuousAt_const.div hden (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [zero_mul, add_zero, div_one] using
      hc.tendsto
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mpr
  apply Tendsto.congr' _ (hquot.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [slope_def_field, projectedResolvent_eq_regular ρ eig hρ hρsum a hx.le]
  simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, sub_zero]
  field_simp [hx'.ne']

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralOverlapPaths
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reconstructed finite-alphabet overlap paths in manuscript `rot:full-paths`.
The formulas and their positivity and sum constraints are proved here;
identification with limiting Gibbs overlaps is separate. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem spectralGroupPath_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (s : ℝ) :
    0 ≤ spectralGroupPath ρ eig hρ hρsum p a s :=
  intervalIntegral.integral_nonneg_of_forall (p.nonneg s)
    (spectralPathDensity_nonneg ρ eig hρ hρsum p a)

theorem spectralGroupPath_monotone (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Monotone (spectralGroupPath ρ eig hρ hρsum p a) := by
  intro s t hst
  exact intervalIntegral.integral_mono_interval le_rfl (p.nonneg s) (p.monotone hst)
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨p.nonneg t, p.le_one t⟩)

theorem spectralGroupPath_le_diagonal (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) (s : ℝ) :
    spectralGroupPath ρ eig hρ hρsum p a s ≤ spectralGroupDiagonal ρ eig hρ hρsum p a :=
  intervalIntegral.integral_mono_interval le_rfl (p.nonneg s) (p.le_one s)
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨zero_le_one, le_rfl⟩)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaProductPrimitives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integral primitive identities for bounded measurable replica paths.
No continuity of the overlap paths is required. -/

noncomputable section

open MeasureTheory Set Filter

namespace InvariantIsing

lemma continuous_tail_integral {f : ℝ → ℝ}
    (hf : ∀ s t, IntervalIntegrable f volume s t) (t : ℝ) :
    Continuous (fun u => ∫ v in u..t, f v) := by
  have he := (intervalIntegral.continuous_primitive hf t).neg
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  rw [intervalIntegral.integral_symm t u]
  rfl

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_PathSymbolAEUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Almost-everywhere symbols determine the almost-everywhere path up to
one constant. This is the form needed after weak limiting Ward equations. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

theorem ae_equal_pathSymbols_constant_difference (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db : ℝ)
    (heq : ∀ᵐ s ∂pathMeasure, pathSymbol da a s = pathSymbol db b s) :
    ∃ c : ℝ, ∀ᵐ s ∂pathMeasure, a s - b s = c := by
  let h : ℝ → ℝ := fun u => a u - b u
  let D := da - db
  let H : ℝ → ℝ := fun u => ∫ v in u..1, h v
  let G : ℝ → ℝ := fun u => (D - H u) / u
  have hhi (v w : ℝ) : IntervalIntegrable h volume v w :=
    intervalIntegrable_of_measurable_abs_le (ha.sub hb)
      (fun u => (abs_sub _ _).trans (add_le_add (haB u) (hbB u))) v w
  have hai (v w : ℝ) : IntervalIntegrable a volume v w :=
    intervalIntegrable_of_measurable_abs_le ha haB v w
  have hbi (v w : ℝ) : IntervalIntegrable b volume v w :=
    intervalIntegrable_of_measurable_abs_le hb hbB v w
  have hH : Continuous H := continuous_tail_integral hhi 1
  have hid : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → h u = G u := by
    have he : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 →
        pathSymbol da a u = pathSymbol db b u :=
      (ae_restrict_iff' measurableSet_Ioo).mp heq
    filter_upwards [he] with u hu humem
    have heq := hu humem
    unfold pathSymbol at heq
    apply (eq_div_iff humem.1.ne').mpr
    change (a u - b u) * u = D - H u
    dsimp only [D, H, h]
    rw [intervalIntegral.integral_sub (hai u 1) (hbi u 1)]
    linarith
  have hGd (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt G 0 u := by
    have hGc : ContinuousAt G u := (continuousAt_const.sub hH.continuousAt).div
      continuousAt_id hu.1.ne'
    have hlocal : h =ᶠ[𝓝 u ⊓ ae volume] G := by
      filter_upwards [hid.filter_mono inf_le_right,
        Filter.Eventually.filter_mono inf_le_left (isOpen_Ioo.mem_nhds hu)] with v hv hvmem
      exact hv hvmem
    have hlim : Tendsto h (𝓝 u ⊓ ae volume) (𝓝 (G u)) :=
      (hGc.tendsto.mono_left inf_le_left).congr' hlocal.symm
    have hHd : HasDerivAt H (-G u) u := intervalIntegral.integral_hasDerivAt_of_tendsto_ae_left
      (hhi u 1) (ha.sub hb).stronglyMeasurable.stronglyMeasurableAtFilter hlim
    have hd := ((hasDerivAt_const u D).sub hHd).div (hasDerivAt_id u) hu.1.ne'
    change HasDerivAt G (((0 - -G u) * u - (D - H u) * 1) / u ^ 2) u at hd
    have hval : G u * u = D - H u := div_mul_cancel₀ _ hu.1.ne'
    have hz : ((0 - -G u) * u - (D - H u) * 1) / u ^ 2 = 0 := by
      apply div_eq_zero_iff.mpr
      left
      nlinarith
    rw [hz] at hd
    exact hd
  refine ⟨G (1 / 2), ?_⟩
  apply (ae_restrict_iff' measurableSet_Ioo).mpr
  filter_upwards [hid] with s hs hsmem
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu => (hGd u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hGd u hu).deriv) hsmem (show (1 / 2 : ℝ) ∈ Ioo 0 1 by norm_num)
  exact (hs hsmem).trans hc

lemma ae_constant_right_root {h : ℝ → ℝ} {c r : ℝ}
    (he : ∀ᵐ s ∂pathMeasure, h s = c) (hr : Tendsto h (𝓝[>] 0) (𝓝 r)) : c = r := by
  by_contra hc
  have hp : 0 < |c - r| := abs_pos.mpr (sub_ne_zero.mpr hc)
  have hsmall : {s : ℝ | |h s - r| < |c - r|} ∈ 𝓝[>] (0 : ℝ) := by
    have ht := (hr.sub_const r).abs
    have hs := (tendsto_order.mp ht).2 _ (by simpa only [sub_self, abs_zero] using hp)
    exact hs
  obtain ⟨δ, hδ, hsub⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset (show (0 : ℝ) < 1 by norm_num)).mp hsmall
  have hmono : Ioo (0 : ℝ) δ ⊆ Ioo (0 : ℝ) 1 := Ioo_subset_Ioo le_rfl hδ.2
  have heδ : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) δ), h s = c :=
    ae_mono (Measure.restrict_mono hmono le_rfl) he
  have hmass : volume (Ioo (0 : ℝ) δ) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr hδ.1).ne'
  obtain ⟨s, hs, hsc⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hmass heδ
  have hh := hsub hs
  change |h s - r| < |c - r| at hh
  rw [hsc] at hh
  exact (lt_irrefl _) hh

theorem ae_equal_pathSymbols_equal_roots (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (haB : ∀ u, |a u| ≤ A) (hbB : ∀ u, |b u| ≤ B) (da db r : ℝ)
    (heq : ∀ᵐ s ∂pathMeasure, pathSymbol da a s = pathSymbol db b s)
    (hra : Tendsto a (𝓝[>] 0) (𝓝 r)) (hrb : Tendsto b (𝓝[>] 0) (𝓝 r)) :
    da = db ∧ a =ᵐ[pathMeasure] b := by
  obtain ⟨c, hc⟩ := ae_equal_pathSymbols_constant_difference a b ha hb haB hbB da db heq
  have hlim : Tendsto (fun s => a s - b s) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hra.sub hrb
  have hc0 : c = 0 := ae_constant_right_root hc hlim
  have hab : a =ᵐ[pathMeasure] b := by
    filter_upwards [hc] with s hs
    exact sub_eq_zero.mp (hs.trans hc0)
  refine ⟨?_, hab⟩
  have hunit : ∀ᵐ s ∂pathMeasure, s ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  obtain ⟨s, hs, hsym, hsame⟩ := (hunit.and (heq.and hab)).exists
  have habv : ∀ᵐ u ∂volume, u ∈ Ioo (0 : ℝ) 1 → a u = b u :=
    (ae_restrict_iff' measurableSet_Ioo).mp hab
  have hi : (∫ u in s..1, a u) = ∫ u in s..1, b u := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [habv, volume.ae_ne (1 : ℝ)] with u hu hune humem
    rw [uIoc_of_le hs.2.le] at humem
    exact hu ⟨hs.1.trans humem.1, lt_of_le_of_ne humem.2 hune⟩
  unfold pathSymbol at hsym
  rw [hsame, hi] at hsym
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Arrays_ReplicaProductRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The root of the replica-product path. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

lemma pathSymbol_root_tendsto (d : ℝ) (a : ℝ → ℝ) (ha : Measurable a)
    {A : ℝ} (haB : ∀ u, |a u| ≤ A) {r : ℝ}
    (hr : Tendsto a (𝓝[>] 0) (𝓝 r)) :
    Tendsto (pathSymbol d a) (𝓝[>] 0) (𝓝 (d - ∫ u in 0..1, a u)) := by
  have hi (s t : ℝ) : IntervalIntegrable a volume s t :=
    intervalIntegrable_of_measurable_abs_le ha haB s t
  have ht := ((continuous_tail_integral hi 1).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hz : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  change Tendsto (fun s => d - s * a s - ∫ u in s..1, a u) _ _
  simpa only [zero_mul, sub_zero] using
    ((tendsto_const_nhds.sub (hz.mul hr)).sub ht :
      Tendsto (fun s => d - s * a s - ∫ u in s..1, a u) (𝓝[>] 0)
        (𝓝 (d - 0 * r - ∫ u in 0..1, a u)))

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDensityContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A continuous bounded extension of the spectral path density. -/

noncomputable section

open Set Filter
open scoped Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem continuous_spectralPathDensity
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) :
    Continuous (spectralPathDensity ρ eig hρ hρsum p a) :=
  (continuous_projectedResolventDerivative ρ eig hρ hρsum a).comp (continuous_deficit p)

theorem spectralPathDensity_le_one
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (a : ι) (r : ℝ) :
    spectralPathDensity ρ eig hρ hρsum p a r ≤ 1 :=
  projectedResolventDerivative_le_one ρ eig hρ hρsum a (deficit p r)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralDeficitDerivative
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating the overlap deficit away from atoms of the overlap law. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace InvariantIsing

/-- At every non-atom of the path law, the derivative of `D_p` is minus
the distribution function. This is the analytic step in `rot:function-path`. -/
theorem hasDerivAt_deficit_of_nonatom (p : OverlapPath) (r : ℝ)
    (hnonatom : pathMeasure {s | p s = r} = 0) :
    HasDerivAt (deficit p) (-pathMeasure.real {s | p s ≤ r}) r := by
  let A : Set ℝ := {s | p s ≤ r}
  have hA : MeasurableSet A := measurableSet_le p.measurable measurable_const
  let F : ℝ → ℝ → ℝ := fun t s => max (p s - t) 0
  let F' : ℝ → ℝ := fun s => A.indicator (fun _ => (1 : ℝ)) s - 1
  have hiA : Integrable (A.indicator (fun _ => (1 : ℝ))) pathMeasure :=
    (integrable_const (1 : ℝ)).indicator hA
  have hi' : Integrable F' pathMeasure := hiA.sub (integrable_const 1)
  have hmean : (∫ s, F' s ∂pathMeasure) = pathMeasure.real A - 1 := by
    dsimp [F']
    rw [integral_sub hiA (integrable_const 1), integral_indicator_const 1 hA]
    simp only [smul_eq_mul, mul_one, integral_const, measureReal_def,
      pathMeasure_univ, ENNReal.toReal_one]
  have hne : ∀ᵐ s ∂pathMeasure, p s ≠ r := by
    rw [ae_iff]
    simpa only [not_not] using hnonatom
  have hdiff : ∀ᵐ s ∂pathMeasure, HasDerivAt (F · s) (F' s) r := by
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with h | h
    · have heq : (F · s) =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        exact max_eq_right (sub_nonpos.mpr (show p s ≤ t from ht.le))
      have hd : HasDerivAt (F · s) 0 r :=
        (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq heq
      simpa only [F', indicator_of_mem (show s ∈ A from h.le), sub_self] using hd
    · have heq : (F · s) =ᶠ[𝓝 r] (fun t => p s - t) := by
        filter_upwards [Iio_mem_nhds h] with t ht
        exact max_eq_left (sub_nonneg.mpr (show t ≤ p s from ht.le))
      have hd : HasDerivAt (fun t : ℝ => p s - t) (-1) r := by
        convert! (hasDerivAt_const r (p s)).sub (hasDerivAt_id r) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      have hd' := hd.congr_of_eventuallyEq heq
      simpa only [F', indicator_of_notMem (show s ∉ A from not_le.mpr h),
        zero_sub] using hd'
  have hlip : ∀ s, LipschitzWith 1 (F · s) := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := abs_max_sub_max_le_abs (p s - x) (p s - y) 0
    have he : (p s - x) - (p s - y) = -(x - y) := by ring
    simpa only [F, Real.dist_eq, NNReal.coe_one, one_mul, he, abs_neg] using h
  have hmeas : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable (F t) pathMeasure :=
    Eventually.of_forall fun _t =>
      ((p.measurable.sub measurable_const).max measurable_const).aestronglyMeasurable
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := pathMeasure) (F := F) (F' := F') (bound := fun _ => (1 : ℝ))
    (s := univ) univ_mem hmeas (p.integrable_posPart r) hi'.aestronglyMeasurable
    (ae_of_all _ fun s => by simpa using hlip s)
    (integrable_const 1) hdiff
  have hdD : HasDerivAt (deficit p) ((0 - 1) - ∫ s, F' s ∂pathMeasure) r := by
    convert! ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).sub hd using 1
    all_goals try with_reducible_and_instances rfl
  rw [hmean] at hdD
  convert hdD using 1
  all_goals try with_reducible_and_instances rfl
  ring

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPrimitive
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar primitive identity in the reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem pathCDF_monotone (p : OverlapPath) :
    Monotone (fun r => pathMeasure.real {s | p s ≤ r}) := by
  intro r u hru
  exact measureReal_mono (fun s hs => hs.trans hru)

theorem hasDerivWithinAt_projectedResolvent_nonneg
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (projectedResolvent ρ eig hρ hρsum a)
      (projectedResolventDerivative ρ eig hρ hρsum a x) (Ici 0) x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false] using
      (hasDerivWithinAt_projectedResolvent_zero ρ eig hρ hρsum a).Ici_of_Ioi
  · exact (hasStrictDerivAt_projectedResolvent ρ eig hρ hρsum a h).hasDerivAt.hasDerivWithinAt

theorem continuousOn_projectedResolvent
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (a : ι) {c : ℝ} :
    ContinuousOn (projectedResolvent ρ eig hρ hρsum a) (Icc 0 c) := by
  intro x hx
  exact (hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a hx.1).continuousWithinAt.mono
    (fun _ hy => hy.1)

/-- The FTC step in `rot:function-path`, valid even when the overlap law has atoms. -/
theorem integral_spectralDensity_mul_CDF (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ r in q..1, spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {s | p s ≤ r}) =
      projectedResolvent ρ eig hρ hρsum a (deficit p q) := by
  let E : Set ℝ := {r | 0 < pathMeasure {s | p s = r}}
  have hE : E.Countable := Measure.countable_meas_level_set_pos p.measurable
  have hcf : ContinuousOn (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
      (Icc 0 1) :=
    (continuousOn_projectedResolvent ρ eig hρ hρsum a).comp
      (continuous_deficit p).continuousOn (fun _ hr => deficit_mem_unit p hr)
  have hcd := (spectralPathDensity_continuousOn ρ eig hρ hρsum p a).mono
    (Icc_subset_Icc hq.1 le_rfl)
  have hint : IntervalIntegrable (fun r => spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {s | p s ≤ r}) volume q 1 :=
    (pathCDF_monotone p).intervalIntegrable.continuousOn_mul
      ((uIcc_of_le hq.2).symm ▸ hcd)
  have hderiv : ∀ r ∈ Ioo q 1 \ E,
      HasDerivAt (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
        (-(spectralPathDensity ρ eig hρ hρsum p a r *
          pathMeasure.real {s | p s ≤ r})) r := by
    intro r hr
    have hzero : pathMeasure {s | p s = r} = 0 := le_antisymm (le_of_not_gt hr.2) bot_le
    have hdD := hasDerivAt_deficit_of_nonatom p r hzero
    have hdf := hasDerivWithinAt_projectedResolvent_nonneg ρ eig hρ hρsum a
      (deficit_nonneg p hr.1.2.le)
    have ht : ∀ᶠ u in 𝓝 r, deficit p u ∈ Ici 0 := by
      filter_upwards [Iio_mem_nhds hr.1.2] with u hu
      exact deficit_nonneg p hu.le
    refine (hdf.comp_hasDerivAt r hdD ht).congr_deriv (Eq.symm ?_)
    · dsimp [spectralPathDensity]
      ring
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le
    (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
    (fun r => -(spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {s | p s ≤ r})) hq.2 hE
    (hcf.mono (Icc_subset_Icc hq.1 le_rfl)) hderiv hint.neg
  rw [intervalIntegral.integral_neg, deficit_one] at hFTC
  have hz : projectedResolvent ρ eig hρ hρsum a 0 = 0 := by
    simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false]
  rw [hz] at hFTC
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralFubini
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
attribute [-simp] _root_.OAI.InvariantIsing.fieldPairing_zero _root_.OAI.InvariantIsing.finiteTemperatureFunctional_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fubini identification of reconstructed spectral-group symbols. -/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The layer-cake calculation in manuscript `rot:function-path`. -/
theorem integral_spectralDensity_CDF_fubini (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    (∫ r in q..1, spectralPathDensity ρ eig hρ hρsum p a r *
      pathMeasure.real {u | p u ≤ r}) =
      ∫ u, (∫ r in max q (p u)..1, spectralPathDensity ρ eig hρ hρsum p a r) ∂pathMeasure := by
  let h := spectralPathDensity ρ eig hρ hρsum p a
  let K : ℝ → ℝ → ℝ := fun r u => if p u ≤ r then h r else 0
  let : IsFiniteMeasure (volume.restrict (uIoc q 1)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min q 1) (max q 1)))
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hm : Measurable (Function.uncurry K) := by
    exact Measurable.ite
      (measurableSet_le (p.measurable.comp measurable_snd) measurable_fst)
      ((continuous_spectralPathDensity ρ eig hρ hρsum p a).measurable.comp measurable_fst)
      measurable_const
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (uIoc q 1)).prod pathMeasure) := by
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      dsimp [Function.uncurry, K]
      split_ifs
      · rw [abs_of_nonneg (spectralPathDensity_nonneg ρ eig hρ hρsum p a z.1)]
        exact spectralPathDensity_le_one ρ eig hρ hρsum p a z.1
      · simp
  have hinner_u : ∀ r, (∫ u, K r u ∂pathMeasure) = h r * pathMeasure.real {u | p u ≤ r} := by
    intro r
    change (∫ u, ({u | p u ≤ r}).indicator (fun _ => h r) u ∂pathMeasure) = _
    rw [integral_indicator_const (h r) (measurableSet_le p.measurable measurable_const)]
    simp only [smul_eq_mul, mul_comm]
  have hinner_r : ∀ u, (∫ r in q..1, K r u) = ∫ r in max q (p u)..1, h r := by
    intro u
    rw [intervalIntegral.integral_of_le hq.2,
      intervalIntegral.integral_of_le (max_le hq.2 (p.le_one u))]
    change (∫ r, (Ici (p u)).indicator h r ∂volume.restrict (Ioc q 1)) = _
    rw [integral_indicator measurableSet_Ici,
      ← restrict_Ioi_eq_restrict_Ici,
      Measure.restrict_restrict measurableSet_Ioi, inter_comm, Ioc_inter_Ioi]
  have hswap := intervalIntegral_integral_swap hK
  simp_rw [hinner_u, hinner_r] at hswap
  exact hswap

theorem spectralGroupSymbol_eq_CDF_integral (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
      (spectralGroupPath ρ eig hρ hρsum p a) s =
      ∫ r in p s..1, spectralPathDensity ρ eig hρ hρsum p a r *
        pathMeasure.real {u | p u ≤ r} := by
  let h := spectralPathDensity ρ eig hρ hρsum p a
  let G : ℝ → ℝ := fun q => ∫ r in 0..q, h r
  have hc : Continuous h := continuous_spectralPathDensity ρ eig hρ hρsum p a
  have hG : Monotone G := by
    intro q r hqr
    have hi := intervalIntegral.integral_nonneg_of_forall (μ := volume) hqr
      (spectralPathDensity_nonneg ρ eig hρ hρsum p a)
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 q) (hc.intervalIntegrable (μ := volume) q r)
    dsimp [G]
    linarith
  let H : ℝ → ℝ := fun u => G (max (p s) (p u))
  have hH : Monotone H := by
    intro u v huv
    exact hG (max_le_max le_rfl (p.monotone huv))
  have hHbounds : ∀ u, 0 ≤ H u ∧ H u ≤ spectralGroupDiagonal ρ eig hρ hρsum p a := by
    intro u
    have h0 : G 0 = 0 := by simp [G]
    constructor
    · rw [← h0]
      exact hG (le_max_of_le_left (p.nonneg s))
    · exact hG (max_le (p.le_one s) (p.le_one u))
  have hHi : Integrable H pathMeasure := by
    apply (integrable_const (spectralGroupDiagonal ρ eig hρ hρsum p a)).mono'
      hH.measurable.aestronglyMeasurable
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hHbounds u).1]
      exact (hHbounds u).2
  have htail : ∀ u, (∫ r in max (p s) (p u)..1, h r) =
      spectralGroupDiagonal ρ eig hρ hρsum p a - H u := by
    intro u
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 (max (p s) (p u)))
      (hc.intervalIntegrable (μ := volume) (max (p s) (p u)) 1)
    change _ = (∫ r in 0..1, h r) - (∫ r in 0..max (p s) (p u), h r)
    linarith
  have hlow : (∫ u in 0..s, H u) = s * spectralGroupPath ρ eig hρ hρsum p a s := by
    calc
      _ = ∫ _ in 0..s, spectralGroupPath ρ eig hρ hρsum p a s := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.1
        intro u hu
        dsimp [H]
        rw [max_eq_left (p.monotone hu.2.le)]
        rfl
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hhigh : (∫ u in s..1, H u) = ∫ u in s..1, spectralGroupPath ρ eig hρ hρsum p a u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hs.2
    intro u hu
    dsimp [H]
    rw [max_eq_right (p.monotone hu.1.le)]
    rfl
  have hHmean : (∫ u, H u ∂pathMeasure) =
      s * spectralGroupPath ρ eig hρ hρsum p a s +
        ∫ u in s..1, spectralGroupPath ρ eig hρ hρsum p a u := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hH.intervalIntegrable (μ := volume) (a := 0) (b := s))
      (hH.intervalIntegrable (μ := volume) (a := s) (b := 1))
    rw [hlow, hhigh] at hadd
    change (∫ u in Ioo 0 1, H u) = _
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact hadd.symm
  rw [integral_spectralDensity_CDF_fubini ρ eig hρ hρsum p a ⟨p.nonneg s, p.le_one s⟩]
  change _ = ∫ u, (∫ r in max (p s) (p u)..1, h r) ∂pathMeasure
  simp_rw [htail]
  rw [integral_sub (integrable_const _) hHi]
  simp only [integral_const, measureReal_def, pathMeasure_univ, ENNReal.toReal_one, one_smul]
  rw [hHmean]
  unfold pathSymbol
  ring

/-- The full reconstructed-symbol identity in manuscript `rot:function-path`. -/
theorem spectralGroupSymbol_eq_projectedResolvent (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
      (spectralGroupPath ρ eig hρ hρsum p a) s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)) := by
  rw [spectralGroupSymbol_eq_CDF_integral ρ eig hρ hρsum p a hs]
  exact integral_spectralDensity_mul_CDF ρ eig hρ hρsum p a ⟨p.nonneg s, p.le_one s⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGroupRoots
attribute [-instance] _root_.OAI.IsingPerceptron.labeledLeafMeasurableSpace _root_.OAI.IsingPerceptron.labeledTreeMeasurableSpace _root_.OAI.IsingPerceptron.markForestMeasurableSpace _root_.OAI.IsingPerceptron.noiseLeafMeasurableSpace _root_.OAI.IsingPerceptron.noiseTreeMeasurableSpace _root_.OAI.IsingPerceptron.rawLeafMeasurableSpace _root_.OAI.IsingPerceptron.rawTreeMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Right roots of the reconstructed finite spectral-group paths. The
deficit is constant below the total path's right root, including root zero. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators Topology

namespace InvariantIsing

lemma OverlapPath.rightLim_mem_unit (p : OverlapPath) :
    Function.rightLim p.val 0 ∈ Icc (0 : ℝ) 1 :=
  ⟨(p.nonneg 0).trans (p.monotone.le_rightLim le_rfl),
    (p.monotone.rightLim_le zero_lt_one).trans (p.le_one 1)⟩

lemma OverlapPath.rightLim_le_of_pos (p : OverlapPath) {u : ℝ} (hu : 0 < u) :
    Function.rightLim p.val 0 ≤ p u := p.monotone.rightLim_le hu

lemma deficit_eq_one_sub_mean_of_le_rightLim (p : OverlapPath) {r : ℝ}
    (hr : r ≤ Function.rightLim p.val 0) :
    deficit p r = 1 - ∫ s, p s ∂pathMeasure := by
  have he : (fun s => max (p s - r) 0) =ᵐ[pathMeasure] fun s => p s - r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact max_eq_left (sub_nonneg.mpr (hr.trans (p.rightLim_le_of_pos hs.1)))
  unfold deficit
  rw [integral_congr_ae he, integral_sub p.integrable (integrable_const r)]
  simp only [integral_const, probReal_univ, one_smul]
  ring

lemma deficit_eq_at_rightLim_of_le (p : OverlapPath) {r : ℝ}
    (hr : r ≤ Function.rightLim p.val 0) :
    deficit p r = deficit p (Function.rightLim p.val 0) := by
  rw [deficit_eq_one_sub_mean_of_le_rightLim p hr,
    deficit_eq_one_sub_mean_of_le_rightLim p le_rfl]

variable {ι : Type*} [Fintype ι]

lemma spectralPathDensity_eq_at_rightLim (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {r : ℝ}
    (hr : r ≤ Function.rightLim p.val 0) :
    spectralPathDensity ρ eig hρ hρsum p a r =
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)) := by
  unfold spectralPathDensity
  rw [deficit_eq_at_rightLim_of_le p hr]

lemma integral_spectralDensity_rightLim (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    (∫ r in 0..Function.rightLim p.val 0, spectralPathDensity ρ eig hρ hρsum p a r) =
      Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)) := by
  calc
    _ = ∫ _r in 0..Function.rightLim p.val 0, projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)) := by
      apply intervalIntegral.integral_congr_Ioo_of_le p.rightLim_mem_unit.1
      intro r hr
      exact spectralPathDensity_eq_at_rightLim ρ eig hρ hρsum p a hr.2.le
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- The reconstructed group path has the exact root prescribed by the
root Ward equations, with no assumption that the total path is continuous. -/
theorem spectralGroupPath_root_tendsto (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Tendsto (spectralGroupPath ρ eig hρ hρsum p a) (𝓝[>] (0 : ℝ))
      (𝓝 (Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)))) := by
  have hc := continuous_spectralPathDensity ρ eig hρ hρsum p a
  have hG : Continuous (fun q => ∫ r in 0..q, spectralPathDensity ρ eig hρ hρsum p a r) :=
    intervalIntegral.continuous_primitive (fun s t => hc.intervalIntegrable s t) 0
  have ht := hG.continuousAt.tendsto.comp (p.monotone.tendsto_rightLim 0)
  rw [integral_spectralDensity_rightLim ρ eig hρ hρsum p a] at ht
  exact ht

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralGroupIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A canonical group quantile and its diagonal are identified by the
spectral symbols and roots derived from the actual Ward equations. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- Equality with the reconstructed spectral group follows from its
proved symbol and root formulas and the AE path uniqueness theorem. -/
theorem spectralGroup_identification_of_symbol_root (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p q : OverlapPath) (d : ℝ) (a : ι)
    (hsymbol : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hroot : Function.rightLim q.val 0 = Function.rightLim p.val 0 *
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0))) :
    d = spectralGroupDiagonal ρ eig hρ hρsum p a ∧
      q.val =ᵐ[pathMeasure] spectralGroupPath ρ eig hρ hρsum p a := by
  have hqB (s : ℝ) : |q s| ≤ 1 := by
    rw [abs_of_nonneg (q.nonneg s)]
    exact q.le_one s
  have hGB (s : ℝ) : |spectralGroupPath ρ eig hρ hρsum p a s| ≤ 1 := by
    rw [abs_of_nonneg (spectralGroupPath_nonneg ρ eig hρ hρsum p a s)]
    exact (spectralGroupPath_le_diagonal ρ eig hρ hρsum p a s).trans
      (spectralGroupDiagonal_le_one ρ eig hρ hρsum p a)
  have heq : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s =
      pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
        (spectralGroupPath ρ eig hρ hρsum p a) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hsymbol] with s hs hsym
    exact hsym.trans (spectralGroupSymbol_eq_projectedResolvent ρ eig hρ hρsum p a
      ⟨hs.1.le, hs.2.le⟩).symm
  have hqr : Tendsto q.val (𝓝[>] (0 : ℝ))
      (𝓝 (Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)))) := by
    rw [← hroot]
    exact q.monotone.tendsto_rightLim 0
  exact ae_equal_pathSymbols_equal_roots q.val (spectralGroupPath ρ eig hρ hρsum p a)
    q.measurable (spectralGroupPath_monotone ρ eig hρ hρsum p a).measurable hqB hGB
    d (spectralGroupDiagonal ρ eig hρ hρsum p a) _ heq hqr
    (spectralGroupPath_root_tendsto ρ eig hρ hρsum p a)

/-- The finite family form keeps all group quantiles on one common full
measure set, as needed for the actual limiting spectral-array law. -/
theorem spectralGroups_identification_of_symbols_roots (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath)
    (q : ι → OverlapPath) (d : ι → ℝ)
    (hsymbol : ∀ a, ∀ᵐ s ∂pathMeasure, pathSymbol (d a) (q a).val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hroot : ∀ a, Function.rightLim (q a).val 0 = Function.rightLim p.val 0 *
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0))) :
    (∀ a, d a = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ s ∂pathMeasure, ∀ a, q a s = spectralGroupPath ρ eig hρ hρsum p a s := by
  have he (a : ι) := spectralGroup_identification_of_symbol_root ρ eig hρ hρsum p (q a) (d a) a
    (hsymbol a) (hroot a)
  exact ⟨fun a => (he a).1, ae_all_iff.mpr fun a => (he a).2⟩

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic reconstruction of spectral-group symbols and roots, as used
in manuscript Proposition `rot:paths`, from the Ward equations. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

 /-- The root Ward equations determine the normalized derivative weights.
 This also includes the zero-symbol endpoint and tied eigenvalues. -/
 theorem spectral_root_reconstruction (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
     (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) (r : ι → ℝ)
     (hward : ∀ a b, ρ b * r a - ρ a * r b =
       (eig a - eig b) *
         (projectedResolvent ρ eig hρ hρsum a x * r b +
          r a * projectedResolvent ρ eig hρ hρsum b x)) (a : ι) :
     r a = (∑ b, r b) * projectedResolventDerivative ρ eig hρ hρsum a x := by
   by_cases hxpos : 0 < x
   · let B := finiteInverse ρ eig hρ hρsum x
     have hs := finiteInverse_spec ρ eig hρ hρsum hxpos
     have hgap : ∀ b, B - eig b ≠ 0 := fun b => (sub_pos.mpr (hs.1 b)).ne'
     have hM := finiteSecondResolvent_pos (fun b => (hρ b).le) hρsum hs.1
     have hpair : ∀ b, r a * (B - eig a) ^ 2 * (ρ b / (B - eig b) ^ 2) =
         ρ a * r b := by
       intro b
       have hw := hward a b
       simp only [projectedResolvent, ite_eq_left hxpos] at hw
       change ρ b * r a - ρ a * r b =
         (eig a - eig b) * (ρ a / (B - eig a) * r b +
           r a * (ρ b / (B - eig b))) at hw
       field_simp [hgap a, hgap b] at hw ⊢
       nlinarith [hw]
     have hsum := congrArg (fun f : ι → ℝ => ∑ b, f b) (funext hpair)
     simp only [← Finset.mul_sum] at hsum
     change r a * (B - eig a) ^ 2 * finiteSecondResolvent ρ eig B =
       ρ a * ∑ b, r b at hsum
     simp only [projectedResolventDerivative, ite_eq_left hxpos]
     change r a = (∑ b, r b) * (ρ a /
       (finiteSecondResolvent ρ eig B * (B - eig a) ^ 2))
     rw [← mul_div_assoc]
     apply (eq_div_iff (mul_ne_zero hM.ne' (pow_ne_zero 2 (hgap a)))).mpr
     nlinarith [hsum]
   · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxpos) hx
     subst x
     have hpair : ∀ b, ρ b * r a = ρ a * r b := by
       intro b
       have hw := hward a b
       simp only [projectedResolvent, lt_self_iff_false, ite_false, if_false, zero_mul,
         mul_zero, add_zero] at hw
       linarith
     have hsum := congrArg (fun f : ι → ℝ => ∑ b, f b) (funext hpair)
     simp only [← Finset.sum_mul, ← Finset.mul_sum, hρsum, one_mul] at hsum
     simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, if_false, mul_comm] using hsum

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Fields_CanonicalRootReconstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Root reconstruction for a finite family of canonical overlap paths.
The Ward equations and reconstructed symbols determine the roots, whose
sum follows from the almost-everywhere path sum. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

lemma projectedResolvent_deficit_path_root_tendsto (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) :
    Tendsto (fun s => projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (projectedResolvent ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)))) := by
  have hc : ContinuousOn (fun r => projectedResolvent ρ eig hρ hρsum a (deficit p r))
      (Icc (0 : ℝ) 1) :=
    (continuousOn_projectedResolvent ρ eig hρ hρsum a).comp
      (continuous_deficit p).continuousOn (fun _ hr => deficit_mem_unit p hr)
  have hp : Tendsto p.val (𝓝[>] (0 : ℝ)) (𝓝[Icc (0 : ℝ) 1] (Function.rightLim p.val 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨p.monotone.tendsto_rightLim 0,
      Filter.Eventually.of_forall fun s => ⟨p.nonneg s, p.le_one s⟩⟩
  exact (hc _ p.rightLim_mem_unit).tendsto.comp hp

lemma canonical_symbol_root_eq (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p q : OverlapPath) (d : ℝ) (a : ι)
    (hsymbol : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s))) :
    d - (∫ u in 0..1, q u) =
      projectedResolvent ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)) := by
  have hqB (u : ℝ) : |q u| ≤ 1 := by
    rw [abs_of_nonneg (q.nonneg u)]
    exact q.le_one u
  have he : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s -
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)) = 0 := by
    filter_upwards [hsymbol] with s hs
    exact sub_eq_zero.mpr hs
  have ht := (pathSymbol_root_tendsto d q.val q.measurable hqB
    (q.monotone.tendsto_rightLim 0)).sub
      (projectedResolvent_deficit_path_root_tendsto ρ eig hρ hρsum p a)
  have hz := ae_constant_right_root he ht
  linarith

lemma canonical_group_roots_sum (p : OverlapPath) (q : ι → OverlapPath)
    (hsum : ∀ᵐ s ∂pathMeasure, ∑ a, q a s = p s) :
    (∑ a, Function.rightLim (q a).val 0) = Function.rightLim p.val 0 := by
  classical
  have hs : Tendsto (fun s => ∑ a, q a s) (𝓝[>] (0 : ℝ))
      (𝓝 (∑ a, Function.rightLim (q a).val 0)) := by
    exact tendsto_finsetSum Finset.univ (fun a _ => (q a).monotone.tendsto_rightLim 0)
  have he : ∀ᵐ s ∂pathMeasure, (∑ a, q a s) - p s = 0 := by
    filter_upwards [hsum] with s hs
    exact sub_eq_zero.mpr hs
  have hz := ae_constant_right_root he (hs.sub (p.monotone.tendsto_rightLim 0))
  linarith

/-- The actual root Ward equations fix every canonical group root once
the symbols and the total path have been identified. -/
theorem canonical_group_root_reconstruction (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath)
    (q : ι → OverlapPath) (d : ι → ℝ)
    (hsymbol : ∀ a, ∀ᵐ s ∂pathMeasure, pathSymbol (d a) (q a).val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hsum : ∀ᵐ s ∂pathMeasure, ∑ a, q a s = p s)
    (hward : ∀ a b, ρ b * Function.rightLim (q a).val 0 -
      ρ a * Function.rightLim (q b).val 0 = (eig a - eig b) *
        ((d a - ∫ u in 0..1, q a u) * Function.rightLim (q b).val 0 +
          Function.rightLim (q a).val 0 * (d b - ∫ u in 0..1, q b u))) (a : ι) :
    Function.rightLim (q a).val 0 = Function.rightLim p.val 0 *
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0)) := by
  have hsym (b : ι) := canonical_symbol_root_eq ρ eig hρ hρsum p (q b) (d b) b (hsymbol b)
  have hw (b c : ι) : ρ c * Function.rightLim (q b).val 0 -
      ρ b * Function.rightLim (q c).val 0 = (eig b - eig c) *
        (projectedResolvent ρ eig hρ hρsum b (deficit p (Function.rightLim p.val 0)) *
            Function.rightLim (q c).val 0 +
          Function.rightLim (q b).val 0 *
            projectedResolvent ρ eig hρ hρsum c (deficit p (Function.rightLim p.val 0))) := by
    simpa only [hsym b, hsym c] using hward b c
  have he := spectral_root_reconstruction ρ eig hρ hρsum
    (deficit_mem_unit p p.rightLim_mem_unit).1 (fun b => Function.rightLim (q b).val 0) hw a
  rwa [canonical_group_roots_sum p q hsum] at he

/-- The symbols, path sum and root Ward equations determine the complete
canonical spectral family, including its diagonal. -/
theorem canonical_groups_identification_of_symbols_rootWard (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath)
    (q : ι → OverlapPath) (d : ι → ℝ)
    (hsymbol : ∀ a, ∀ᵐ s ∂pathMeasure, pathSymbol (d a) (q a).val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hsum : ∀ᵐ s ∂pathMeasure, ∑ a, q a s = p s)
    (hward : ∀ a b, ρ b * Function.rightLim (q a).val 0 -
      ρ a * Function.rightLim (q b).val 0 = (eig a - eig b) *
        ((d a - ∫ u in 0..1, q a u) * Function.rightLim (q b).val 0 +
          Function.rightLim (q a).val 0 * (d b - ∫ u in 0..1, q b u))) :
    (∀ a, d a = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ s ∂pathMeasure, ∀ a, q a s = spectralGroupPath ρ eig hρ hρsum p a s :=
  spectralGroups_identification_of_symbols_roots ρ eig hρ hρsum p q d hsymbol
    (canonical_group_root_reconstruction ρ eig hρ hρsum p q d hsymbol hsum hward)

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Total spin overlap and self normalization for a genuine spectral partition. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped BigOperators Topology

namespace InvariantIsing

lemma spectralSpinWeight_nonneg (m : ℕ) (a : Fin (m + 1)) : 0 ≤ spectralSpinWeight m a := by
  refine Fin.lastCases ?_ (fun _ => ?_) a <;> simp [spectralSpinWeight]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralQuantilePaths
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous pair quantile laws of the actual spectral GG limits. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators Topology

namespace InvariantIsing

/-- All pairs of required nonnegative linear overlap combinations have
simultaneous quantile laws. The total spin combination is included once its
unit bound is derived from the genuine spectral partition. -/
theorem spectralQuantilePath_pair_law {m : ℕ} {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w z : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a) (hz : ∀ a, 0 ≤ z a)
    (hws : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray w x 0 1 ∈ Icc (0 : ℝ) 1)
    (hzs : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), spectralLinearArray z x 0 1 ∈ Icc (0 : ℝ) 1) :
    InvariantIsing.pathMeasure.map
      (fun s => (spectralQuantilePath Q w hws s, spectralQuantilePath Q z hzs s)) =
      (Q : Measure (SpectralArray m)).map
        (fun x => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1)) := by
  let F := fun x : SpectralArray m => (spectralLinearArray w x 0 1, spectralLinearArray z x 0 1)
  have hm : Measurable F := by unfold F spectralLinearArray spectralLinearEntry; fun_prop
  let ρ := (Q : Measure (SpectralArray m)).map F
  let : IsProbabilityMeasure ρ := (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  have hs : ∀ᵐ x ∂ρ, x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.prod measurableSet_Icc)).mpr
    filter_upwards [hws, hzs] with x hx hy
    exact ⟨hx, hy⟩
  have hfirst : ρ.map Prod.fst = spectralLinearLaw Q w := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_fst hm]
    rfl
  have hsecond : ρ.map Prod.snd = spectralLinearLaw Q z := by
    dsimp only [ρ]
    rw [Measure.map_map measurable_snd hm]
    rfl
  have he := ordered_pair_quantile_law (spectralGG_support_ordered hgg hG q hq hd hE w z hw hz) hs
  rw [hfirst, hsecond] at he
  exact he

lemma integral_of_pair_law {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) (ν : Measure T) (f g : Ω → ℝ) (F G : T → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) (hG : Measurable G)
    (hl : μ.map (fun x => (f x, g x)) = ν.map (fun x => (F x, G x))) :
    (∫ x, f x * g x ∂μ) = ∫ x, F x * G x ∂ν := by
  have hm : StronglyMeasurable (fun p : ℝ × ℝ => p.1 * p.2) := by fun_prop
  calc
    _ = ∫ p : ℝ × ℝ, p.1 * p.2 ∂μ.map (fun x => (f x, g x)) :=
      (integral_map_of_stronglyMeasurable (hf.prodMk hg) hm).symm
    _ = ∫ p : ℝ × ℝ, p.1 * p.2 ∂ν.map (fun x => (F x, G x)) := by rw [hl]
    _ = _ := integral_map_of_stronglyMeasurable (hF.prodMk hG) hm

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralQuantileMoments
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linear relations pass to simultaneous overlap quantiles. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma finite_sum_square_eq {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 = ∑ i, ∑ j, f i * f j := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma integrable_finite_sum_square {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : ι → Ω → ℝ}
    (hi : ∀ i j, Integrable (fun x => f i x * f j x) μ) :
    Integrable (fun x => (∑ i, f i x) ^ 2) μ := by
  simp_rw [finite_sum_square_eq]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))

lemma integral_finite_sum_square {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : ι → Ω → ℝ}
    (hi : ∀ i j, Integrable (fun x => f i x * f j x) μ) :
    (∫ x, (∑ i, f i x) ^ 2 ∂μ) = ∑ i, ∑ j, ∫ x, f i x * f j x ∂μ := by
  simp_rw [finite_sum_square_eq]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  exact Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hi i j))

/-- Pair moments alone preserve every finite linear relation. This avoids
assuming a simultaneous vector law before it has been constructed. -/
lemma ae_sum_zero_of_pair_moments {Ω T ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace T] [Fintype ι]
    {μ : Measure Ω} {ν : Measure T} {f : ι → Ω → ℝ} {g : ι → T → ℝ}
    (hf : ∀ i j, Integrable (fun x => f i x * f j x) μ)
    (hg : ∀ i j, Integrable (fun x => g i x * g j x) ν)
    (he : ∀ i j, (∫ x, f i x * f j x ∂μ) = ∫ x, g i x * g j x ∂ν)
    (hz : ∀ᵐ x ∂ν, (∑ i, g i x) = 0) :
    ∀ᵐ x ∂μ, (∑ i, f i x) = 0 := by
  have hzero : (∫ x, (∑ i, f i x) ^ 2 ∂μ) = 0 := by
    calc
      _ = ∑ i, ∑ j, ∫ x, f i x * f j x ∂μ := integral_finite_sum_square hf
      _ = ∑ i, ∑ j, ∫ x, g i x * g j x ∂ν := by simp_rw [he]
      _ = ∫ x, (∑ i, g i x) ^ 2 ∂ν := (integral_finite_sum_square hg).symm
      _ = 0 := by
        rw [integral_congr_ae (hz.mono (fun x hx => by rw [hx, zero_pow (by decide)]))]
        exact integral_zero _ _
  have ha := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (∑ i, f i x))
    (integrable_finite_sum_square hf)).mp hzero
  filter_upwards [ha] with x hx
  exact (sq_eq_zero_iff).mp hx

lemma integral_scaled_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (c d : ℝ) :
    (∫ x, (c * f x) * (d * g x) ∂μ) = c * d * ∫ x, f x * g x ∂μ := by
  have he (x : Ω) : (c * f x) * (d * g x) = (c * d) * (f x * g x) := by ring
  simp_rw [he]
  exact integral_const_mul _ _

/-- Every linear relation among nonnegative spectral combinations holds
almost everywhere for their common quantile parameter. -/
theorem spectralQuantilePath_linear_relation {m k : ℕ}
    {Q : ProbabilityMeasure (SpectralArray m)}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray m)))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), SpectralGram x)
    (q : Fin m → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray m)), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray m)).map (permuteSpectralArray e) = Q)
    (w : Fin k → Fin m → ℝ) (hw : ∀ i a, 0 ≤ w i a)
    (hs : ∀ i, ∀ᵐ x ∂(Q : Measure (SpectralArray m)),
      spectralLinearArray (w i) x 0 1 ∈ Icc (0 : ℝ) 1)
    (c : Fin k → ℝ) (hc : ∀ a, (∑ i, c i * w i a) = 0) :
    ∀ᵐ s ∂pathMeasure, (∑ i, c i * spectralQuantilePath Q (w i) (hs i) s) = 0 := by
  let f := fun i s => c i * spectralQuantilePath Q (w i) (hs i) s
  let g := fun i x => c i * spectralLinearArray (w i) x 0 1
  have hfi (i j : Fin k) : Integrable (fun s => f i s * f j s) pathMeasure := by
    refine integrable_of_measurable_abs_le (F := fun s => f i s * f j s)
      (c := |c i| * |c j|) ?_ ?_
    · exact (measurable_const.mul (spectralQuantilePath Q (w i) (hs i)).measurable).mul
        (measurable_const.mul (spectralQuantilePath Q (w j) (hs j)).measurable)
    intro s
    simp only [f, abs_mul, abs_of_nonneg ((spectralQuantilePath Q (w i) (hs i)).nonneg s),
      abs_of_nonneg ((spectralQuantilePath Q (w j) (hs j)).nonneg s)]
    exact mul_le_mul (mul_le_of_le_one_right (abs_nonneg _) ((spectralQuantilePath Q (w i) (hs i)).le_one s))
      (mul_le_of_le_one_right (abs_nonneg _) ((spectralQuantilePath Q (w j) (hs j)).le_one s))
      (mul_nonneg (abs_nonneg _) ((spectralQuantilePath Q (w j) (hs j)).nonneg s)) (abs_nonneg _)
  have hgi (i j : Fin k) : Integrable (fun x => g i x * g j x)
      (Q : Measure (SpectralArray m)) := by
    apply compact_integrable
    unfold g spectralLinearArray spectralLinearEntry
    fun_prop
  apply ae_sum_zero_of_pair_moments hfi hgi
  · intro i j
    dsimp only [f, g]
    rw [integral_scaled_product, integral_scaled_product]
    congr 1
    exact integral_of_pair_law pathMeasure (Q : Measure (SpectralArray m)) _ _ _ _
      (spectralQuantilePath Q (w i) (hs i)).measurable
      (spectralQuantilePath Q (w j) (hs j)).measurable
      (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
      (by unfold spectralLinearArray spectralLinearEntry; fun_prop)
      (spectralQuantilePath_pair_law hgg hG q hq hd hE (w i) (w j) (hw i) (hw j) (hs i) (hs j))
  · exact ae_of_all _ fun x => by
      simp only [g, spectralLinearArray, spectralLinearEntry, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [← mul_assoc, ← Finset.sum_mul, hc, zero_mul, Finset.sum_const_zero]

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralPartitionPaths
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual spectral-group quantiles sum to the total spin quantile. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma spectralPartitionQuantileWeights_nonneg (m : ℕ) (i a : Fin (m + 1)) :
    0 ≤ spectralPartitionQuantileWeights m i a := by
  classical
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [spectralPartitionQuantileWeights, Fin.lastCases_last] using
      spectralSpinWeight_nonneg m a
  · simp only [spectralPartitionQuantileWeights, Fin.lastCases_castSucc, Pi.single_apply]
    split_ifs <;> norm_num

lemma spectralPartitionRelation_eq_zero (m : ℕ) (a : Fin (m + 1)) :
    (∑ i, spectralPartitionRelation m i * spectralPartitionQuantileWeights m i a) = 0 := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [spectralPartitionRelation, spectralPartitionQuantileWeights,
    Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, neg_mul, one_mul]
  refine Fin.lastCases ?_ (fun j => ?_) a
  · simp [spectralSpinWeight]
  · simp [Pi.single_apply, spectralSpinWeight, Fin.castSucc_inj]

theorem spectralPartitionQuantileWeights_unit {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (i : Fin (m + 1)) :
    ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      spectralLinearArray (spectralPartitionQuantileWeights m i) x 0 1 ∈ Icc (0 : ℝ) 1 := by
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simpa only [spectralPartitionQuantileWeights, Fin.lastCases_last,
      spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn
  · simpa only [spectralPartitionQuantileWeights, Fin.lastCases_castSucc] using
      spectralCoordinate_unit hn a.castSucc

/-- The spectral partition and vector Ghirlanda–Guerra synchronization
yield the sum identity. -/
theorem spectralPartition_quantile_sum {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : Equiv.Perm ℕ,
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ)) :
    ∀ᵐ s ∂pathMeasure,
      (∑ a : Fin m, spectralQuantilePath Q (Pi.single a.castSucc 1) (spectralCoordinate_unit hn a.castSucc) s) =
        spectralQuantilePath Q (spectralSpinWeight m)
          (by simpa only [spectralLinearArray_spinWeight] using spectralPartition_spin_unit hP hn) s := by
  have hr := spectralQuantilePath_linear_relation hgg hG q hq hd hE
    (spectralPartitionQuantileWeights m) (spectralPartitionQuantileWeights_nonneg m)
    (spectralPartitionQuantileWeights_unit hP hn) (spectralPartitionRelation m)
    (spectralPartitionRelation_eq_zero m)
  filter_upwards [hr] with s hs
  rw [Fin.sum_univ_castSucc] at hs
  simp only [spectralPartitionRelation, spectralPartitionQuantileWeights,
    Fin.lastCases_castSucc, Fin.lastCases_last, one_mul, neg_mul, one_mul] at hs
  linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Spectral_SpectralCanonicalIdentification
attribute [-instance] _root_.OAI.InvariantIsing.cavityMarkedProbabilityTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual off-diagonal and diagonal limiting Ward equations identify
the canonical spectral-group paths and their deterministic diagonals. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

 theorem spectralCanonical_identification_oai {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (hoff : ∀ a b, ∀ Φ : ℝ → ℝ, Continuous Φ → ∀ C : ℝ, 0 ≤ C → (∀ r, |Φ r| ≤ C) →
      spectralOffWardResidual Q ρ eig a b Φ = 0)
    (hdiag : ∀ a b, spectralDiagonalWardResidual Q ρ eig a b = 0) :
    let p := spectralSpinQuantilePath Q hP hn
    (∀ a, q a.castSucc = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ s ∂pathMeasure, ∀ a, spectralGroupQuantilePath Q hn a s =
        spectralGroupPath ρ eig hρ hρsum p a s := by
  intro p
  have hs := spectralCanonical_symbols hgg hG q hq hd hE hP hn ρ eig hρ hρsum hoff hdiag
  apply canonical_groups_identification_of_symbols_rootWard ρ eig hρ hρsum p
    (spectralGroupQuantilePath Q hn) (fun a => q a.castSucc)
  · intro a
    filter_upwards [hs] with s hs
    exact hs a
  · exact spectralPartition_quantile_sum hgg hG q hq hd (fun e => hE e e.injective) hP hn
  · intro a b
    exact (spectralCanonicalWard_pair hgg hG q hq hd hE hP hn ρ eig a b (hoff a b) (hdiag a b)).2

end InvariantIsing

end

end OAI
end

theorem solution : type_of% @OAI.InvariantIsing.spectralCanonical_identification_oai := @OAI.InvariantIsing.spectralCanonical_identification_oai
