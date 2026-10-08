-- Prove2me | solution 1 for OAI.TwoPointCorrelations.ProhibitedPrimeFamily.positive_divisor_degree_cost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:41:39.773139+00:00
-- url     : https://prove2.me/submissions/9f060fe1-1902-407c-9bc3-97b777a4b606

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]



lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))


lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]

lemma average_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.average (fun x => f x * c) = μ.average f * c := by
  simp only [average, mul_assoc, sum_mul]








lemma independent_average_product [DecidableEq ι] (μ : ι → FiniteLaw α) (f : ι → α → ℝ) :
    (independent μ).average (fun x => ∏ i, f i (x i)) = ∏ i, (μ i).average (f i) := by
  simp only [average, independent, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x => (μ i).weight x * f i x)).symm

lemma probability_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.probability E := by
  classical
  apply μ.average_nonneg
  intro x
  split_ifs <;> norm_num

lemma probability_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.probability E ≤ 1 := by
  classical
  apply (μ.average_mono (g := fun _ => 1) ?_).trans_eq (μ.average_const 1)
  intro x
  split_ifs <;> norm_num


end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledForest
namespace OAI

/-!
# Labeled ordered forests

Binary trees use the first-child / next-sibling convention. The labels
are auxiliary: erasing them keeps the finite shape used by the code.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree

variable {V : Type*}











@[simp] lemma attachForestLeaf_roots [DecidableEq V] (parent leaf : V) (t : BinaryTree V) :
    forestRoots (attachForestLeaf parent leaf t) = forestRoots t := by
  induction t with
  | nil => rfl
  | node v l r hl hr =>
      by_cases hv : v = parent <;> simp [attachForestLeaf, hv, forestRoots, hr]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling
namespace OAI

/-! Product sampling and the atom bound for independent linear equations. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
@[simp] lemma joinCoordinates_mem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : S) : joinCoordinates S x y i = x i := by simp [joinCoordinates, i.property]

omit [Fintype ι] in
@[simp] lemma joinCoordinates_notMem (S : Finset ι) (x : S → A) (y : {i // i ∉ S} → A)
    (i : {i // i ∉ S}) : joinCoordinates S x y i = y i := by simp [joinCoordinates, i.property]

namespace FiniteLaw

variable [Fintype A]

lemma independent_probability_all (μ : ι → FiniteLaw A) (E : ι → A → Prop) :
    (independent μ).probability (fun x => ∀ i, E i (x i)) =
      ∏ i, (μ i).probability (E i) := by
  classical
  unfold probability
  calc
    _ = (independent μ).average (fun x => ∏ i, if E i (x i) then (1 : ℝ) else 0) := by
      apply congrArg (independent μ).average
      funext x
      by_cases hx : ∀ i, E i (x i) <;> simp [Fintype.prod_boole, hx]
    _ = _ := independent_average_product μ (fun i x => if E i x then 1 else 0)

lemma independent_weight_join (μ : ι → FiniteLaw A) (S : Finset ι)
    (x : S → A) (y : {i // i ∉ S} → A) :
    (independent μ).weight (joinCoordinates S x y) =
      (independent (fun i : S => μ i)).weight x *
      (independent (fun i : {i // i ∉ S} => μ i)).weight y := by
  change (∏ i, (μ i).weight (joinCoordinates S x y i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem, independent]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]

/-- Conditioning on coordinates outside `S` leaves the original product
law on `S`. -/
lemma independent_average_split (μ : ι → FiniteLaw A) (S : Finset ι) (f : (ι → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i : {i // i ∉ S} => μ i)).average (fun y =>
        (independent (fun i : S => μ i)).average (fun x => f (joinCoordinates S x y))) := by
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ S) (fun _ => A)
  calc
    _ = ∑ z : (S → A) × ({i // i ∉ S} → A),
        (independent μ).weight (joinCoordinates S z.1 z.2) *
          f (joinCoordinates S z.1 z.2) := by
      exact (e.symm.sum_comp (fun z => (independent μ).weight z * f z)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [independent_weight_join, average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro x _
      ring



end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteLawMapping
namespace OAI

/-! Finite pushforward identities, used to identify the actual two-selection
padding experiment with its three-point difference law. -/

namespace TwoPointCorrelations.FiniteLaw

open _root_.Finset
open scoped _root_.Classical

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

lemma average_fibers (μ : FiniteLaw α) (g : α → β) (F : β → ℝ) :
    μ.average (fun x => F (g x)) = ∑ y, μ.probability (fun x => g x = y) * F y := by
  calc
    _ = μ.average (fun x => ∑ y, if g x = y then F y else 0) := by
      congr 1
      funext x
      simp
    _ = _ := by
      rw [average_sum]
      apply sum_congr rfl
      intro y _
      simp [average, probability, sum_mul, mul_ite, ite_mul]

lemma independent_average_map [DecidableEq ι] (μ : ι → FiniteLaw α)
    (ν : ι → FiniteLaw β) (g : ι → α → β)
    (hg : ∀ i y, (μ i).probability (fun x => g i x = y) = (ν i).weight y)
    (F : (ι → β) → ℝ) :
    (independent μ).average (fun x => F (fun i => g i (x i))) =
      (independent ν).average F := by
  rw [average_fibers]
  unfold average
  apply sum_congr rfl
  intro y _
  congr 1
  have he : (fun x : ι → α => (fun i => g i (x i)) = y) =
      (fun x => ∀ i, g i (x i) = y i) := by
    funext x
    exact propext funext_iff
  rw [he, independent_probability_all μ (fun i x => g i x = y i)]
  simp only [hg, independent]



end TwoPointCorrelations.FiniteLaw

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixAction
namespace OAI

/-! Concrete continuous operators associated with finite matrices. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] lemma matrixOperator_apply (A : ι → ι → ℂ) (v : EuclideanSpace ℂ ι) (i : ι) :
    matrixOperator A v i = ∑ j, A i j * v j := rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MixedDifference
namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl


namespace FiniteLaw











end FiniteLaw



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddedListCode
namespace OAI

/-! Fixed-length code slots for finite lists with a bounded length. -/

namespace TwoPointCorrelations

variable {α : Type*} {N : ℕ}


@[simp] theorem paddedListCode_ofFn (l : List α) (h : l.length ≤ N) (default : α) :
    List.ofFn (paddedListCode l h default) = l ++ List.replicate (N - l.length) default := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i hi hj
    simp only [List.getElem_ofFn, paddedListCode]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CommonResidueLift
namespace OAI

/-! One integer realizes all coordinates of a common residue configuration. -/

namespace TwoPointCorrelations

open _root_.Finset


/-- Prime divisibility at any offset is read from that same lifted origin. -/
lemma residue_offset_divisibility {p : ℕ} (r : ZMod p) (n offset : ℤ)
    (hn : (n : ZMod p) = r) :
    (p : ℤ) ∣ n + offset ↔ r = -(offset : ZMod p) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, hn, add_eq_zero_iff_eq_neg]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveModel
namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder, using only finite probability identities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw




lemma probability_complement {α : Type*} [Fintype α] (μ : FiniteLaw α) (E : α → Prop) :
    μ.probability (fun x => ¬E x) = 1 - μ.probability E := by
  have hsum : μ.probability E + μ.probability (fun x => ¬E x) = 1 := by
    unfold probability average
    rw [← sum_add_distrib]
    calc
      _ = ∑ x, μ.weight x := by
        apply sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      _ = 1 := μ.total
  linarith



end FiniteLaw







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BernoulliTail
namespace OAI

/-! Exact exponential moments and elementary upper tails for the finite
independent Boolean laws used by the two prime-degree deletions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.probability_lt_exp_bound {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (Z : A → ℝ) (a t : ℝ) (ht : 0 ≤ t) :
    μ.probability (fun x => a < Z x) ≤
      Real.exp (-t * a) * μ.average (fun x => Real.exp (t * Z x)) := by
  calc
    _ ≤ μ.average (fun x => Real.exp (t * Z x) * Real.exp (-t * a)) := by
      apply μ.average_mono
      intro x
      by_cases hx : a < Z x
      · rw [if_pos hx, ← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        nlinarith
      · rw [if_neg hx]
        positivity
    _ = _ := by rw [μ.average_mul_const]; ring


lemma booleanCount_eq_card {ι : Type*} [Fintype ι] (a : ι → Bool) :
    booleanCount a = ((univ.filter (fun i => a i = true)).card : ℝ) := by
  exact sum_boole (fun i => a i = true) univ

lemma booleanLaw_exp_average (q t : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (booleanLaw q hq0 hq1).average (fun b => Real.exp (t * (if b then 1 else 0))) =
      1 + q * (Real.exp t - 1) := by
  simp [FiniteLaw.average, booleanLaw]
  ring

lemma independent_boolean_exp_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (t : ℝ) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => Real.exp (t * booleanCount a)) =
        ∏ i, (1 + q i * (Real.exp t - 1)) := by
  have he (a : ι → Bool) : Real.exp (t * booleanCount a) =
      ∏ i, Real.exp (t * (if a i then 1 else 0)) := by
    rw [booleanCount, mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [FiniteLaw.independent_average_product
    (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
    (fun _ b => Real.exp (t * (if b then 1 else 0)))]
  simp only [booleanLaw_exp_average]

lemma independent_boolean_exp_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t M : ℝ) (ht : 0 ≤ t) (hM : (∑ i, q i) ≤ M) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => Real.exp (t * booleanCount a)) ≤ Real.exp ((Real.exp t - 1) * M) := by
  rw [independent_boolean_exp_average]
  have hu : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht)
  calc
    _ ≤ ∏ i, Real.exp (q i * (Real.exp t - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        exact add_nonneg zero_le_one (mul_nonneg (hq0 i) hu)
      · intro i _
        simpa only [add_comm] using Real.add_one_le_exp (q i * (Real.exp t - 1))
    _ = Real.exp ((∑ i, q i) * (Real.exp t - 1)) := by
      rw [sum_mul, Real.exp_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

/-- The entire bound is a finite product identity followed by exponential
Markov; no probability theorem is assumed. -/
theorem independent_boolean_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (t M a : ℝ) (ht : 0 ≤ t) (hM : (∑ i, q i) ≤ M) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => a < booleanCount b) ≤
        Real.exp ((Real.exp t - 1) * M - t * a) := by
  apply (FiniteLaw.probability_lt_exp_bound _ _ a t ht).trans
  calc
    _ ≤ Real.exp (-t * a) * Real.exp ((Real.exp t - 1) * M) :=
      mul_le_mul_of_nonneg_left (independent_boolean_exp_bound q hq0 hq1 t M ht hM)
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositivePrimeTilt
namespace OAI

/-! Tilting the prime divisibility law by the positive majorant of one
tuple of centered prime factors.  Selected primes have parameter
`(1 + q)/2`; every other prime keeps its original parameter. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]







lemma positiveCenterWeight_eq (q : ι → ℝ) (S : Finset ι) (a : ι → Bool) :
    positiveCenterWeight q S a = ∏ i ∈ S, ((if a i then 1 else 0) + q i) := by
  simp only [positiveCenterWeight, ← prod_filter, filter_mem_eq_inter, univ_inter]

lemma positiveCenterNormalizer_eq (q : ι → ℝ) (S : Finset ι) :
    positiveCenterNormalizer q S = ∏ i ∈ S, 2 * q i := by
  simp only [positiveCenterNormalizer, ← prod_filter, filter_mem_eq_inter, univ_inter]

lemma positiveCenterNormalizer_nonneg (q : ι → ℝ) (S : Finset ι)
    (hq : ∀ i, 0 ≤ q i) : 0 ≤ positiveCenterNormalizer q S := by
  unfold positiveCenterNormalizer
  apply prod_nonneg
  intro i _
  split_ifs
  · exact mul_nonneg (by norm_num) (hq i)
  · exact zero_le_one

lemma positive_center_tilt_weight (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (a : ι → Bool) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).weight a *
        positiveCenterWeight q S a =
      (positiveCenterLaw q S hq0 hq1).weight a * positiveCenterNormalizer q S := by
  simp only [FiniteLaw.independent, positiveCenterLaw, positiveCenterWeight,
    positiveCenterNormalizer, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> cases a i <;>
    simp [positiveCenterParameter, hi, booleanLaw] <;> ring

lemma positive_center_tilt_average (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (F : (ι → Bool) → ℝ) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
        (fun a => positiveCenterWeight q S a * F a) =
      positiveCenterNormalizer q S * (positiveCenterLaw q S hq0 hq1).average F := by
  simp only [FiniteLaw.average, mul_sum]
  apply sum_congr rfl
  intro a _
  rw [← mul_assoc, positive_center_tilt_weight]
  ring


lemma positiveCenterParameter_sum_le (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) :
    (∑ i, positiveCenterParameter q S i) ≤ (S.card : ℝ) + ∑ i, q i := by
  calc
    _ ≤ ∑ i, ((if i ∈ S then (1 : ℝ) else 0) + q i) := by
      apply sum_le_sum
      intro i _
      unfold positiveCenterParameter
      by_cases hi : i ∈ S
      · simp only [hi, ite_true]
        linarith [hq0 i]
      · simp only [hi, ite_false, zero_add, le_refl]
    _ = _ := by simp only [sum_add_distrib, sum_boole, filter_mem_eq_inter,
      univ_inter]

/-- The selected primes may be bounded simply by their number.  The
remaining Bernoulli mean is at most the original total reciprocal mass. -/
theorem positive_center_degree_tail (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (W : ℝ) (hW : 10 ≤ W) (hmass : (∑ i, q i) ≤ 2 * W * S.card) :
    (positiveCenterLaw q S hq0 hq1).probability
      (fun a => 6 * W * S.card < booleanCount a) ≤ Real.exp (-2 * W * S.card) := by
  have hJ : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hM : (∑ i, positiveCenterParameter q S i) ≤
      (S.card : ℝ) + 2 * W * S.card :=
    (positiveCenterParameter_sum_le q S hq0).trans (add_le_add le_rfl hmass)
  have hb := independent_boolean_tail (positiveCenterParameter q S)
    (positiveCenterParameter_nonneg q S hq0) (positiveCenterParameter_le_one q S hq1)
    1 ((S.card : ℝ) + 2 * W * S.card) (6 * W * S.card) (by norm_num) hM
  apply hb.trans
  apply Real.exp_le_exp.mpr
  have he : Real.exp 1 - 1 ≤ (7 / 4 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hW0 : 0 ≤ W := by linarith
  have hM0 : 0 ≤ (S.card : ℝ) + 2 * W * S.card :=
    add_nonneg hJ (mul_nonneg (mul_nonneg (by norm_num) hW0) hJ)
  have heM := mul_le_mul_of_nonneg_right he hM0
  nlinarith [mul_nonneg (sub_nonneg.mpr hW) hJ]

theorem positive_center_weighted_degree_tail (q : ι → ℝ) (S : Finset ι)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (W : ℝ) (hW : 10 ≤ W) (hmass : (∑ i, q i) ≤ 2 * W * S.card) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => positiveCenterWeight q S a *
        if 6 * W * S.card < booleanCount a then 1 else 0) ≤
      positiveCenterNormalizer q S * Real.exp (-2 * W * S.card) := by
  rw [positive_center_tilt_average]
  exact mul_le_mul_of_nonneg_left (positive_center_degree_tail q S hq0 hq1 W hW hmass)
    (positiveCenterNormalizer_nonneg q S hq0)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TriangularElimination
namespace OAI

/-! Successive elimination for finite product laws and triangular events. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A]


omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_same (i : ι) (a : A) (y : {j : ι // j ≠ i} → A) :
    restoreCoordinate i a y i = a := by simp [restoreCoordinate]

omit [Fintype ι] [Fintype A] in
@[simp] lemma restoreCoordinate_other (i : ι) (a : A) (y : {j : ι // j ≠ i} → A)
    (j : {j : ι // j ≠ i}) : restoreCoordinate i a y j = y j := by
  simp [restoreCoordinate, j.property]


namespace FiniteLaw





end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.UniformResidues
namespace OAI

/-! Uniform residue coordinates realized on one common finite carrier. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma uniformResidueLaw_weight (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) (hx : x.val < p) :
    (uniformResidueLaw B p hp hpB).weight x = (p : ℝ)⁻¹ := by
  simp [uniformResidueLaw, hx]


@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection
namespace OAI

/-!
# Correcting an almost independent Boolean density

This is the finite Fourier correction used in the proof of the manuscript's
finite-residue comparison (`q:finite-law`, `q:fourier-correction-tv`). The
construction removes the chosen nonconstant Walsh coefficients and adds the
constant `a` before normalization, retaining pointwise nonnegativity.
-/

namespace TwoPointCorrelations

open _root_.Finset










@[simp] lemma booleanSign_not (b : Bool) : booleanSign (!b) = -booleanSign b := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma booleanSign_sq (b : Bool) : booleanSign b * booleanSign b = 1 := by
  cases b <;> norm_num [booleanSign]

@[simp] lemma abs_booleanSign (b : Bool) : |booleanSign b| = 1 := by
  cases b <;> norm_num [booleanSign]



@[simp] lemma abs_walsh {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    |walsh S x| = 1 := by
  simp [walsh, Finset.abs_prod]

@[simp] lemma walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh S x = 1 := by
  unfold walsh
  rw [← Finset.prod_mul_distrib]
  simp
























end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
namespace OAI

/-!
# Exact finite jitter encoding

For `Q = 2^B`, the integer code `⌊(r Q + j)/s⌋`, with `j` uniform in
`{0,…,Q-1}`, has exactly the distribution of the first `B` binary digits
of `(r + U)/s` for uniform `U` in `[0,1)`. This finite construction avoids
continuous auxiliary probability spaces. Jointly uniform residue and
jitter give a uniform code. Decoding can fail for at most `s` jitter values
at each fixed residue, giving the stronger bound `s/Q`.
-/

open _root_.Finset

namespace TwoPointCorrelations












@[simp] lemma decode_jitterBits {s B : ℕ} (hs : 0 < s) (r : Fin s) (j : Fin (2 ^ B)) :
    decodeBits hs (jitterBits r j) = jitterDecode hs (by positivity) (jitterCode r j) := by
  simp [decodeBits, jitterBits]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
namespace OAI

/-!
# Low-order coefficients of the actual encoded interval law

A Walsh coefficient only uses the residue coordinates touched by its bits.
All other independent jitters integrate out. The remaining observable is
bounded by one, so CRT gives the product of its selected moduli divided by
the interval length as an explicit coefficient bound.
-/

namespace TwoPointCorrelations

open _root_.Finset





@[simp] lemma flattenBitBlocks_apply {m B : ℕ} (z : Fin m → BooleanCube B)
    (k : Fin (m * B)) : flattenBitBlocks m B z k = z k.divNat k.modNat := rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.CanonicalForest
namespace OAI

/-! Equal ordered-forest shapes identify their graphs by preorder indices. -/

namespace TwoPointCorrelations

open _root_.SimpleGraph _root_.BinaryTree

variable {V W : Type*}


@[simp] lemma forestIndexEquiv_val [DecidableEq V] (t : BinaryTree V)
    (ht : (forestNodes t).Nodup) (hc : ∀ v, v ∈ forestNodes t) (v : V) :
    (forestIndexEquiv t ht hc v).val = (forestNodes t).idxOf v := rfl






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoder
namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations











@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]


@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRunEncoding
namespace OAI

/-! Reconstructing perfect runs and imperfect attachments from their bits. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]




@[simp] theorem columnFlags_length (entries : List (Option α)) (previous : Option α) :
    (columnFlags entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [columnFlags, ih]










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnBoundaryEncoding
namespace OAI

/-! Run bits may force a split at a perfect-block boundary without changing its label. -/

namespace TwoPointCorrelations

variable {α : Type*} [DecidableEq α]



@[simp] theorem columnFlagsWithCuts_length (entries : List (Option α × Bool)) (previous : Option α) :
    (columnFlagsWithCuts entries previous).length = entries.length := by
  induction entries generalizing previous with
  | nil => rfl
  | cons entry rest ih => rcases entry with ⟨a, cut⟩; cases a <;> simp [columnFlagsWithCuts, ih]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWords
namespace OAI

/-!
# Positive words, reversal, and descent to a minimal prohibited word

A step keeps its whole tuple and padding divisor. Positivity is the exact
integer divisibility `q*d ∣ x` at its departure. Since the displacement is
`±h*q*d`, this divisibility also holds at its arrival. Restriction and
reversal therefore preserve positivity, as required in the witness descent.
-/

namespace TwoPointCorrelations


namespace SignedStep


@[simp] lemma flip_flip (a : SignedStep) : a.flip.flip = a := by
  cases a
  simp [flip]



@[simp] lemma displacement_flip (h : ℕ) (a : SignedStep) :
    a.flip.displacement h = -a.displacement h := by
  rcases a with ⟨b, d, q⟩
  cases b <;> simp [flip, displacement]


@[simp] lemma divisor_flip (a : SignedStep) : a.flip.divisor = a.divisor := rfl



end SignedStep


@[simp] lemma wordDisplacement_nil (h : ℕ) : wordDisplacement h [] = 0 := rfl

@[simp] lemma wordDisplacement_cons (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordDisplacement h (a :: w) = a.displacement h + wordDisplacement h w := rfl

@[simp] lemma wordDisplacement_append (h : ℕ) (u v : List SignedStep) :
    wordDisplacement h (u ++ v) = wordDisplacement h u + wordDisplacement h v := by
  simp [wordDisplacement]


@[simp] lemma reverseWord_nil : reverseWord [] = [] := rfl

@[simp] lemma reverseWord_cons (a : SignedStep) (w : List SignedStep) :
    reverseWord (a :: w) = reverseWord w ++ [a.flip] := by simp [reverseWord]

@[simp] lemma reverseWord_append (u v : List SignedStep) :
    reverseWord (u ++ v) = reverseWord v ++ reverseWord u := by simp [reverseWord]

@[simp] lemma reverseWord_length (w : List SignedStep) : (reverseWord w).length = w.length := by
  simp [reverseWord]

@[simp] lemma reverseWord_reverseWord (w : List SignedStep) : reverseWord (reverseWord w) = w := by
  simp [reverseWord, List.map_map, Function.comp_def]

@[simp] lemma wordDisplacement_reverseWord (h : ℕ) (w : List SignedStep) :
    wordDisplacement h (reverseWord w) = -wordDisplacement h w := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]


@[simp] lemma positiveWord_nil (h : ℕ) (x : ℤ) : PositiveWord h x [] := trivial

@[simp] lemma positiveWord_cons (h : ℕ) (x : ℤ) (a : SignedStep) (w : List SignedStep) :
    PositiveWord h x (a :: w) ↔ a.divisor ∣ x ∧ PositiveWord h (x + a.displacement h) w := Iff.rfl






















end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.BlockGeometry
namespace OAI

/-!
# The shortest-gap argument for perfect blocks

The finite combinatorial lemma isolates a shortest gap across all prime
coordinates. Every label has interval-shaped uses inside the intervening
substring. The arithmetic lemmas below use exact integer displacement sums.
-/

namespace TwoPointCorrelations

open _root_.Finset








@[simp] lemma intervalDisplacement_singleton (D : ℕ → ℤ) (a : ℕ) :
    intervalDisplacement D a (a + 1) = D a := by simp [intervalDisplacement]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnChunkBudgets
namespace OAI

/-! Exact decoder budgets for lists of actual perfect blocks. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
@[simp] theorem regularPieceCount_append (a b : List (List α ⊕ α)) :
    regularPieceCount (a ++ b) = regularPieceCount a + regularPieceCount b := by
  simp [regularPieceCount, List.filterMap_append]

omit [DecidableEq α] in
@[simp] theorem omittedPieceCount_append (a b : List (List α ⊕ α)) :
    omittedPieceCount (a ++ b) = omittedPieceCount a + omittedPieceCount b := by
  simp [omittedPieceCount, List.filterMap_append]






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShortBlockPartition
namespace OAI

/-! The actual subdivision of perfect intervals into short blocks. -/

namespace TwoPointCorrelations

variable {α : Type*}





@[simp] theorem shortBlocks_length (s : ℕ) (l : List α) :
    (shortBlocks s l).length = l.length / s + 1 := by
  simp [shortBlocks, shortBlockLengths]











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingDivisorEncoding
namespace OAI

/-! Squarefree padding divisors encode prime selections without multiplicity.
This identifies the bin law with the paper's numerical divisor sum. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical






lemma paddingAvailablePrimes_card (Q : Finset ℕ) (a : Q → Bool) :
    (paddingAvailablePrimes Q a).card = (selectedCoordinates Q a).card := by
  exact card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)

lemma padding_supported_iff_primeFactors_subset (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime) (a b : Q → Bool) :
    PaddingSelectionSupported Q a b ↔
      (paddingSelectedDivisor Q b).primeFactors ⊆ paddingAvailablePrimes Q a := by
  rw [paddingSelectedDivisor_primeFactors Q hQ b]
  constructor
  · intro h p hp
    have hpQ := paddingAvailablePrimes_subset Q b hp
    exact (mem_paddingAvailablePrimes Q a ⟨p, hpQ⟩).mpr
      (h ⟨p, hpQ⟩ ((mem_paddingAvailablePrimes Q b ⟨p, hpQ⟩).mp hp))
  · intro h p hp
    exact (mem_paddingAvailablePrimes Q a p).mp
      (h ((mem_paddingAvailablePrimes Q b p).mpr hp))









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingIntegerBins
namespace OAI

/-! The squarefree divisor formula uses literal divisibility by the site,
including the site zero. Bin membership is exactly the half-open interval
condition in the manuscript. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma paddingSelectedDivisor_dvd_iff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) (n : ℤ) :
    (paddingSelectedDivisor Q b : ℤ) ∣ n ↔
      ∀ p : Q, b p = true → (p.val : ℤ) ∣ n := by
  rw [paddingSelectedDivisor, Nat.cast_prod]
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun q : Q => (q.val : ℤ))
      (mem_filter.mpr ⟨mem_univ p, hp⟩)).trans h
  · intro h
    apply prod_dvd_of_coprime
    · intro p _ q _ hpq
      apply Nat.Coprime.cast
      apply (Nat.coprime_primes (hQ p p.property) (hQ q q.property)).mpr
      exact fun he => hpq (Subtype.ext he)
    · intro p hp
      exact h p (mem_filter.mp hp).2

lemma padding_literal_support_iff_dvd (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (n : ℤ) (q : ℕ) (hq : q ∈ retainedPrimeDivisors Q) :
    q.primeFactors ⊆ paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) ↔
      (q : ℤ) ∣ n := by
  obtain ⟨b, rfl⟩ := exists_paddingSelection Q q hq
  rw [← padding_supported_iff_primeFactors_subset Q hQ,
    paddingSelectedDivisor_dvd_iff Q hQ b n]
  simp only [PaddingSelectionSupported, decide_eq_true_eq]


lemma paddingAvailablePrimes_integer (Q : Finset ℕ) (n : ℤ) :
    paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n)) =
      Q.filter (fun (p : ℕ) => (p : ℤ) ∣ n) := by
  ext p
  constructor
  · intro hp
    have hpQ := paddingAvailablePrimes_subset Q _ hp
    exact mem_filter.mpr ⟨hpQ, by
      simpa using (mem_paddingAvailablePrimes Q _ ⟨p, hpQ⟩).mp hp⟩
  · intro hp
    exact (mem_paddingAvailablePrimes Q _ ⟨p, (mem_filter.mp hp).1⟩).mpr
      (by simpa using (mem_filter.mp hp).2)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordSegments
namespace OAI

/-! Exact identification of list segments with integer displacement intervals. -/

namespace TwoPointCorrelations

open _root_.Finset


@[simp] lemma wordStepDisplacement_nil (h i : ℕ) : wordStepDisplacement h [] i = 0 := by
  simp [wordStepDisplacement]

@[simp] lemma wordStepDisplacement_cons_zero (h : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) 0 = a.displacement h := rfl

@[simp] lemma wordStepDisplacement_cons_succ (h i : ℕ) (a : SignedStep) (w : List SignedStep) :
    wordStepDisplacement h (a :: w) (i + 1) = wordStepDisplacement h w i := rfl












end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
namespace OAI

/-! The actual resampling model after every other column and padding are fixed. -/

namespace TwoPointCorrelations


namespace ColumnWordPattern

variable {α : Type*}




@[simp] lemma word_length (w : ColumnWordPattern α) (value : α → ℕ) :
    (w.word value).length = w.length := by simp [word]





end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuit
namespace OAI

/-! The actual deleted event is a finite depth-two DNF of prime tests. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit





end AC0Circuit














lemma squarefree_divisor_iff (d : ℕ) (hd : Squarefree d) (n : ℤ) :
    (d : ℤ) ∣ n ↔ ∀ p ∈ d.primeFactors, (p : ℤ) ∣ n := by
  constructor
  · intro hn p hp
    have hp' : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast Nat.dvd_of_mem_primeFactors hp
    exact hp'.trans hn
  · intro hn
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.cast_prod]
    apply prod_dvd_of_coprime
    · intro p hp q hq hpq
      exact ((Nat.coprime_primes (Nat.mem_primeFactors.mp hp).1
        (Nat.mem_primeFactors.mp hq).1).mpr hpq).cast (R := ℤ)
    · exact hn








end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PositiveWordProbability
namespace OAI

/-!
# Probability of one positive numerical word

The same residue coordinate is reused at every occurrence of a prime.
Selecting one occurrence per distinct prime therefore bounds the probability
by one reciprocal per distinct prime, including all padding factors. There
is no independence assumption between different sites of the word.
-/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.probability_mono_of_imp {A : Type*} [Fintype A]
    (μ : FiniteLaw A) {E F : A → Prop} (h : ∀ x, E x → F x) :
    μ.probability E ≤ μ.probability F := by
  apply μ.average_mono
  intro x
  by_cases he : E x
  · simp only [if_pos he, if_pos (h x he), le_refl]
  · simp only [if_neg he]
    split_ifs <;> norm_num

/-- Every residue modulo the true modulus has precisely its uniform mass,
even though the common carrier `Fin B` also contains zero-weight points. -/
theorem uniformResidueLaw_mod_eq (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (r : ZMod p) :
    (uniformResidueLaw B p hp hpB).probability
      (fun x => (x.val : ZMod p) = r) = (p : ℝ)⁻¹ := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  let : DecidableEq (ZMod p) := fun _ _ => Classical.propDecidable _
  let a : Fin B := ⟨r.val, r.val_lt.trans_le hpB⟩
  have ha : a.val < p := r.val_lt
  have har : (a.val : ZMod p) = r := ZMod.natCast_zmod_val r
  have hterm (x : Fin B) :
      (uniformResidueLaw B p hp hpB).weight x *
        (if (x.val : ZMod p) = r then (1 : ℝ) else 0) =
      if x = a then (p : ℝ)⁻¹ else 0 := by
    by_cases hx : x = a
    · subst x
      simp only [uniformResidueLaw_weight B p hp hpB a ha, har, ite_true, mul_one]
    · by_cases hxp : x.val < p
      · have hxr : (x.val : ZMod p) ≠ r := by
          intro he
          have hv := congrArg ZMod.val he
          rw [ZMod.val_natCast_of_lt hxp] at hv
          exact hx (Fin.ext hv)
        simp only [uniformResidueLaw_weight B p hp hpB x hxp, if_neg hxr,
          mul_zero, if_neg hx]
      · simp only [uniformResidueLaw, if_neg hxp, zero_mul, if_neg hx]
  unfold FiniteLaw.probability FiniteLaw.average
  dsimp only
  calc
    _ = ∑ x : Fin B, if x = a then (p : ℝ)⁻¹ else 0 :=
      Finset.sum_congr rfl (fun x _ => hterm x)
    _ = _ := by simp









end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueEvent
namespace OAI

/-! Padding divisibility in one common residue sample, with arbitrary departures. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



/-- Repeated padding primes impose compatibility conditions on a single
coordinate. The probability pays only one reciprocal per distinct prime. -/
theorem paddingResidueEvent_probability_le {R : ℕ} (Q : Finset ℕ)
    (q : Fin R → ℕ) (offset : Fin R → ℤ) (B : ℕ)
    (hp : ∀ p ∈ Q, 0 < p) (hpB : ∀ p ∈ Q, p ≤ B)
    (hQ : paddingPrimeSupport q ⊆ Q) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (hp _ p.property) (hpB _ p.property))).probability
        (PaddingResidueEvent Q q offset) ≤
      ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹ := by
  classical
  let E (p : Q) (y : Fin B) : Prop := ∀ i : Fin R, p.val ∈ (q i).primeFactors →
    (y.val : ZMod p.val) = -((offset i : ℤ) : ZMod p.val)
  have he : PaddingResidueEvent (B := B) Q q offset = (fun y => ∀ p, E p (y p)) := by
    funext y
    exact propext forall_comm
  rw [he, FiniteLaw.independent_probability_all]
  have hprod : (∏ p : Q, if p.val ∈ paddingPrimeSupport q then (p.val : ℝ)⁻¹ else 1) =
      ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹ := by
    rw [← prod_filter]
    apply prod_bij (fun p _ => p.val)
    · intro p hp'
      exact (mem_filter.mp hp').2
    · intro p _ r _ hpr
      exact Subtype.ext hpr
    · intro p hp'
      exact ⟨⟨p, hQ hp'⟩, mem_filter.mpr ⟨mem_univ _, hp'⟩, rfl⟩
    · intro p _
      rfl
  rw [← hprod]
  apply Finset.prod_le_prod
  · intro p _
    exact FiniteLaw.probability_nonneg _ _
  · intro p _
    by_cases hp' : p.val ∈ paddingPrimeSupport q
    · rw [if_pos hp']
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp'
      exact ((uniformResidueLaw B p.val (hp _ p.property) (hpB _ p.property)).probability_mono_of_imp
        (fun y hy => hy i hi)).trans_eq
          (uniformResidueLaw_mod_eq B p.val (hp _ p.property) (hpB _ p.property)
            (-((offset i : ℤ) : ZMod p.val)))
    · rw [if_neg hp']
      exact FiniteLaw.probability_le_one _ _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingResidueTilt
namespace OAI

/-! At every translated site of the uniform residue model, divisibility
indicators give independent Bernoulli(1/p) variables. Thus the exact weighted
residue expectation is the tilted padding law used in the bin-square bound. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma padding_residue_single_law (B p : ℕ) (hp : 2 ≤ p) (hpB : p ≤ B)
    (n : ℤ) (b : Bool) :
    (uniformResidueLaw B p (by omega) hpB).probability
      (fun z => decide ((p : ℤ) ∣ (z.val : ℤ) + n) = b) =
        (paddingOriginalPrimeLaw p hp).weight b := by
  have he (z : Fin B) : (p : ℤ) ∣ (z.val : ℤ) + n ↔
      (z.val : ZMod p) = -(n : ZMod p) :=
    residue_offset_divisibility (z.val : ZMod p) z.val n (by simp)
  have hh : (uniformResidueLaw B p (by omega) hpB).probability
      (fun z => (p : ℤ) ∣ (z.val : ℤ) + n) = (p : ℝ)⁻¹ := by
    simpa only [he] using uniformResidueLaw_mod_eq B p (by omega) hpB (-(n : ZMod p))
  cases b
  · have hc := FiniteLaw.probability_complement (uniformResidueLaw B p (by omega) hpB)
      (fun z => (p : ℤ) ∣ (z.val : ℤ) + n)
    rw [hh] at hc
    simpa [paddingOriginalPrimeLaw, booleanLaw, one_div] using hc
  · simpa [paddingOriginalPrimeLaw, booleanLaw, one_div] using hh

lemma padding_residue_average (Q : Finset ℕ) (B : ℕ)
    (hQ : ∀ p ∈ Q, 2 ≤ p) (hQB : ∀ p ∈ Q, p ≤ B) (n : ℤ)
    (F : (Q → Bool) → ℝ) :
    (FiniteLaw.independent (fun p : Q =>
      uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))).average
        (fun z => F (paddingResidueAvailable Q B n z)) =
          (paddingOriginalLaw Q hQ).average F := by
  exact FiniteLaw.independent_average_map
    (fun p : Q => uniformResidueLaw B p.val (by have := hQ p p.property; omega) (hQB p p.property))
    (fun p : Q => paddingOriginalPrimeLaw p (hQ p p.property))
    (fun p (z : Fin B) => decide ((p.val : ℤ) ∣ (z.val : ℤ) + n))
    (fun p b => padding_residue_single_law B p (hQ p p.property) (hQB p p.property) n b) F




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemDecoding
namespace OAI

/-! Decode bounded witness metadata into the actual interval or comparison relations. -/

namespace TwoPointCorrelations


attribute [instance] PackedPrimeRelation.termFintype

namespace WitnessSystemData

variable {n N : ℕ} {ι : Type*} [DecidableEq ι]







@[simp] lemma toSystem_size (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) :
    (d.toSystem main word h ht).size = d.chosen.card := by
  exact Fintype.card_coe d.chosen

@[simp] lemma toSystem_holds (d : WitnessSystemData n N ι) (main : LabeledPrimeWord ι)
    (word : Fin n → LabeledPrimeWord ι) (h : ℕ) (ht : d.Triangular main word h) (x : ι → ℤ) :
    (d.toSystem main word h ht).Holds x ↔ d.Holds main word h x := Iff.rfl

end WitnessSystemData

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
namespace OAI

/-! Splitting a coded word into the main path and its attached witness paths. -/

namespace TwoPointCorrelations
namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]


omit [DecidableEq ι] in
@[simp] lemma segment_length (w : LabeledPrimeWord ι) (a n : ℕ) :
    (w.segment a n).word.length = min n (w.word.length - a) := by
  simp only [segment, List.length_take, List.length_drop]



end LabeledPrimeWord
end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeResidueLift
namespace OAI

/-! Evaluate the actual padding-periodic weights at one common integer lift of the product-law sample. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open _root_.Finset
open scoped _root_.Classical



lemma residueOrigin_spec {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) :
    (data.residueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_residue_origin x).choose_spec p

lemma residueOrigin_divisibility {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)
    (x : ↥(data.P ∪ data.Q) → Fin B) (p : ↥(data.P ∪ data.Q)) (offset : ℤ) :
    (p.val : ℤ) ∣ data.residueOrigin x + offset ↔
      (p.val : ℤ) ∣ (x p).val + offset := by
  exact (residue_offset_divisibility _ _ _ (data.residueOrigin_spec x p)).trans
    (residue_offset_divisibility ((x p).val : ZMod p.val) ((x p).val : ℤ) offset
      (by simp)).symm




end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueLawUniform
namespace OAI

/-! The common padded carrier law pushes forward to the genuine uniform
product of prime residue fields. Padding points contribute zero mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


local instance residuePrime_neZero {h J M : ℕ} (data : ProhibitedPrimeFamily h J M)
    (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
namespace OAI

/-! Restriction of a product law to selected prime coordinates.  The
coordinate laws may depend on the prime; no common-modulus uniformity is
assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma independent_average_reindex {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : ι ≃ κ) (μ : κ → FiniteLaw A) (f : (κ → A) → ℝ) :
    (independent μ).average f =
      (independent (fun i => μ (e i))).average (fun x => f (fun k => x (e.symm k))) := by
  let E : (ι → A) ≃ (κ → A) := Equiv.arrowCongr e (Equiv.refl A)
  calc
    _ = ∑ x : ι → A, (independent μ).weight (E x) * f (E x) :=
      (E.sum_comp (fun x => (independent μ).weight x * f x)).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      change (∏ k, (μ k).weight (x (e.symm k))) * f (fun k => x (e.symm k)) =
        (∏ i, (μ (e i)).weight (x i)) * f (fun k => x (e.symm k))
      congr 1
      simpa only [e.apply_symm_apply] using
        e.symm.prod_comp (fun i => (μ (e i)).weight (x i))

lemma independent_average_restrict {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι) (f : (S → A) → ℝ) :
    (independent μ).average (fun x => f (fun i : S => x i)) =
      (independent (fun i : S => μ i)).average f := by
  rw [independent_average_split μ S]
  simp only [joinCoordinates_mem, average_const]

/-- Independent coordinates retain their individual laws under an
injective change of the index set. -/
lemma independent_average_embedding {ι κ A : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Fintype A]
    (e : κ → ι) (he : Function.Injective e) (μ : ι → FiniteLaw A)
    (f : (κ → A) → ℝ) :
    (independent μ).average (fun x => f (fun k => x (e k))) =
      (independent (fun k => μ (e k))).average f := by
  let S : Finset ι := univ.image e
  let E : κ ≃ S := Equiv.ofBijective
    (fun k => ⟨e k, mem_image.mpr ⟨k, mem_univ _, rfl⟩⟩) (by
      constructor
      · intro x y hxy
        exact he (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨k, _, hk⟩ := mem_image.mp y.property
        exact ⟨k, Subtype.ext hk⟩)
  calc
    _ = (independent (fun i : S => μ i)).average
        (fun x => f (fun k => x (E k))) :=
      independent_average_restrict μ S (fun x => f (fun k => x (E k)))
    _ = _ := by
      rw [independent_average_reindex E]
      simp only [E.symm_apply_apply]
      rfl

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)







lemma paddingResidueOrigin_spec (x : data.Q → Fin B) (p : data.Q) :
    (data.paddingResidueOrigin x : ZMod p.val) = ((x p).val : ZMod p.val) :=
  (data.exists_padding_residue_origin x).choose_spec p


end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightIndependence
namespace OAI

/-! The retained departure weight is independent of tuple-prime residue draws.
Only the padding-prime residues enter its divisibility, density and cutoff data. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma squarefree_divisor_congr (Qp : Finset ℕ) (q : ℕ) (hq : Squarefree q)
    (hpool : q.primeFactors ⊆ Qp) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    (q : ℤ) ∣ n ↔ (q : ℤ) ∣ m := by
  rw [squarefree_divisor_iff q hq n, squarefree_divisor_iff q hq m]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    hnm p (hpool hp)]





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingWeights
namespace OAI

/-! The graph's literal padding weight and vertex normalization.
The normalization is the square root of `5^omega_Q(n)` and depends
only on the padding-prime residues, including at the integer zero. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma actualPaddingCoefficient_nonneg (q : ℕ) : 0 ≤ actualPaddingCoefficient q := by
  unfold actualPaddingCoefficient
  positivity











lemma actualPaddingDegree_eq_available (Q : Finset ℕ) (n : ℤ) :
    actualPaddingDegree Q n =
      (paddingAvailablePrimes Q (fun p => decide ((p.val : ℤ) ∣ n))).card := by
  rw [paddingAvailablePrimes_integer]
  rfl










end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeDegreeTail
namespace OAI

/-! The prime-degree deletion under the literal full residue law.  The
positive tuple majorant has mean `2^omega(d)/d`, and its tilted degree
tail is exponentially small in `W * omega(d)`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma primeSelection_card (P S : Finset ℕ) (hSP : S ⊆ P) :
    (primeSelection P S hSP).card = S.card := by
  have hi : Function.Injective (fun p : S => (⟨p.val, hSP p.property⟩ : P)) := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)
  simp only [primeSelection, card_image_of_injective _ hi, card_attach]





lemma positivePrimeWeight_eq_selection (P S : Finset ℕ) (hSP : S ⊆ P) (n : ℤ) :
    positivePrimeWeight S n =
      positiveCenterWeight (fun p : P => 1 / (p.val : ℝ)) (primeSelection P S hSP)
        (fun p => decide ((p.val : ℤ) ∣ n)) := by
  rw [positiveCenterWeight_eq]
  unfold primeSelection
  rw [prod_image]
  · simp only [positivePrimeWeight, decide_eq_true_eq]
    exact (prod_attach S (fun p : ℕ =>
      (if (p : ℤ) ∣ n then (1 : ℝ) else 0) + 1 / (p : ℝ))).symm
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)

lemma positivePrimeNormalizer_eq_selection (P S : Finset ℕ) (hSP : S ⊆ P) :
    positivePrimeNormalizer S =
      positiveCenterNormalizer (fun p : P => 1 / (p.val : ℝ)) (primeSelection P S hSP) := by
  rw [positiveCenterNormalizer_eq]
  unfold primeSelection
  rw [prod_image]
  · simp only [positivePrimeNormalizer, mul_one_div]
    exact (prod_attach S (fun p : ℕ => (2 : ℝ) / p)).symm
  · intro p _ q _ hpq
    exact Subtype.ext (congrArg (fun r : P => r.val) hpq)


lemma actualPrimeDegree_eq_count (P : Finset ℕ) (n : ℤ) :
    (actualPaddingDegree P n : ℝ) =
      booleanCount (fun p : P => decide ((p.val : ℤ) ∣ n)) := by
  rw [actualPaddingDegree_eq_available, paddingAvailablePrimes_card, booleanCount_eq_card]
  rfl

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

/-- Every prime coordinate retains its Bernoulli divisibility law under
the full tuple-and-padding law, also at a translated CRT origin. -/
lemma residue_average_prime_availability
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
    (F : (data.P → Bool) → ℝ) :
    (data.residueLaw B hB).average (fun x =>
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site))) =
      (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F := by
  let e : data.P → ↥(data.P ∪ data.Q) := fun p => ⟨p.val, mem_union_left _ p.property⟩
  have he : Function.Injective e := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun r : ↥(data.P ∪ data.Q) => r.val) hpq)
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        F (paddingResidueAvailable data.P B site (fun p => x (e p)))) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply congrArg F
      funext p
      change decide ((p.val : ℤ) ∣ data.residueOrigin x + site) =
        decide ((p.val : ℤ) ∣ (x (e p)).val + site)
      have hdiv : (p.val : ℤ) ∣ data.residueOrigin x + site ↔
          (p.val : ℤ) ∣ (x (e p)).val + site := data.residueOrigin_divisibility x (e p) site
      simp only [hdiv]
    _ = (FiniteLaw.independent (fun p : data.P => uniformResidueLaw B p.val
        (data.primeP p p.property).pos (hB p (mem_union_left _ p.property)))).average
          (fun z => F (paddingResidueAvailable data.P B site z)) :=
      FiniteLaw.independent_average_embedding e he
        (fun p => uniformResidueLaw B p.val (data.prime p).pos (hB p p.property))
        (fun z => F (paddingResidueAvailable data.P B site z))
    _ = _ := padding_residue_average data.P B (fun p hp => (data.primeP p hp).two_le)
      (fun p hp => hB p (mem_union_left _ hp)) site F


/-- The positive centered-prime majorant, with a prime-degree failure,
is bounded by its exact mean times `exp(-2W * #S)`. -/
theorem positive_prime_degree_tail (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) ≤
      positivePrimeNormalizer S * Real.exp (-2 * W * S.card) := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  have hq0 (p : data.P) : 0 ≤ q p := by dsimp [q]; positivity
  have hq1 (p : data.P) : q p ≤ 1 := by
    apply (div_le_one (by exact_mod_cast (data.primeP p p.property).pos)).mpr
    exact_mod_cast (data.primeP p p.property).one_lt.le
  have hm : (∑ p : data.P, q p) ≤ 2 * W * T.card := by
    rw [primeSelection_card]
    change (∑ p : data.P, 1 / (p.val : ℝ)) ≤ 2 * W * S.card
    rw [sum_coe_sort data.P (fun p : ℕ => 1 / (p : ℝ))]
    exact hmass
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      positivePrimeWeight S (data.residueOrigin x + site) *
        (if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then (1 : ℝ) else 0) =
      positiveCenterWeight q T (fun p : data.P =>
        decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
        (if 6 * W * T.card < booleanCount (fun p : data.P =>
          decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) then 1 else 0) := by
    rw [positivePrimeWeight_eq_selection data.P S hSP,
      actualPrimeDegree_eq_count, primeSelection_card]
  simp_rw [he]
  rw [data.residue_average_prime_availability hB site (fun a =>
    positiveCenterWeight q T a * if 6 * W * T.card < booleanCount a then 1 else 0)]
  have ht := positive_center_weighted_degree_tail q T hq0 hq1 W hW hm
  rw [primeSelection_card, ← positivePrimeNormalizer_eq_selection] at ht
  simpa only [paddingOriginalLaw, paddingOriginalPrimeLaw, T, q, primeSelection_card] using ht


end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimePaddingFactorization
namespace OAI

/-! Exact independence of tuple-prime and padding-prime observables under
the actual union residue law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma independent_average_sum_product {ι κ A : Type*}
    [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq ι] [DecidableEq κ]
    (μ : ι → FiniteLaw A) (ν : κ → FiniteLaw A)
    (f : (ι → A) → ℝ) (g : (κ → A) → ℝ) :
    (independent (Sum.elim μ ν)).average
      (fun x => f (fun i => x (Sum.inl i)) * g (fun k => x (Sum.inr k))) =
      (independent μ).average f * (independent ν).average g := by
  let e := Equiv.sumArrowEquivProdArrow ι κ A
  calc
    _ = ∑ xy : (ι → A) × (κ → A),
        (independent (Sum.elim μ ν)).weight (Sum.elim xy.1 xy.2) * (f xy.1 * g xy.2) :=
      (e.symm.sum_comp (fun x => (independent (Sum.elim μ ν)).weight x *
        (f (fun i => x (Sum.inl i)) * g (fun k => x (Sum.inr k))))).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, independent, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, average]
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro y _
      ring

end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)



lemma residue_average_tuple_padding
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (f : (data.P → Fin B) → ℝ) (g : (data.Q → Fin B) → ℝ) :
    (data.residueLaw B hB).average (fun x =>
      f (data.tupleRestriction x) * g (data.paddingRestriction x)) =
      (data.tupleResidueLaw B hB).average f *
        (data.paddingResidueLaw B hB).average g := by
  let e : data.P ⊕ data.Q → ↥(data.P ∪ data.Q) := Sum.elim
    (fun p => ⟨p.val, mem_union_left _ p.property⟩)
    (fun p => ⟨p.val, mem_union_right _ p.property⟩)
  have he : Function.Injective e := by
    intro x y hxy
    have hv := congrArg (fun p : ↥(data.P ∪ data.Q) => p.val) hxy
    cases x with
    | inl p =>
      cases y with
      | inl q => exact congrArg Sum.inl (Subtype.ext hv)
      | inr q =>
        exact False.elim (disjoint_left.mp data.disjoint p.property (hv.symm ▸ q.property))
    | inr p =>
      cases y with
      | inl q =>
        exact False.elim (disjoint_left.mp data.disjoint q.property (hv ▸ p.property))
      | inr q => exact congrArg Sum.inr (Subtype.ext hv)
  let μ := fun p : ↥(data.P ∪ data.Q) =>
    uniformResidueLaw B p.val (data.prime p).pos (hB _ p.property)
  have hμ : (fun i => μ (e i)) = Sum.elim
      (fun p : data.P => uniformResidueLaw B p.val (data.primeP _ p.property).pos
        (hB _ (mem_union_left _ p.property)))
      (fun p : data.Q => uniformResidueLaw B p.val (data.primeQ _ p.property).pos
        (hB _ (mem_union_right _ p.property))) := by
    funext i
    cases i <;> rfl
  have ht := FiniteLaw.independent_average_embedding e he μ
    (fun x => f (fun p => x (Sum.inl p)) * g (fun p => x (Sum.inr p)))
  rw [hμ, FiniteLaw.independent_average_sum_product] at ht
  exact ht

/-- Prime divisibility observables and an arbitrary padding-periodic
integer weight are independent at the same translated CRT origin. -/
lemma residue_average_prime_boolean_padding
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (site : ℤ)
    (F : (data.P → Bool) → ℝ) (g : ℤ → ℝ)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) *
        g (data.residueOrigin x + site)) =
      (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F *
        (data.paddingResidueLaw B hB).average (fun z =>
          g (data.paddingResidueOrigin z + site)) := by
  calc
    _ = (data.residueLaw B hB).average (fun x =>
        F (paddingResidueAvailable data.P B site (data.tupleRestriction x)) *
          g (data.paddingResidueOrigin (data.paddingRestriction x) + site)) := by
      apply congrArg (data.residueLaw B hB).average
      funext x
      apply congrArg₂ (fun a b : ℝ => a * b)
      · apply congrArg F
        funext p
        change decide ((p.val : ℤ) ∣ data.residueOrigin x + site) =
          decide ((p.val : ℤ) ∣ (x ⟨p.val, mem_union_left _ p.property⟩).val + site)
        have hdiv : (p.val : ℤ) ∣ data.residueOrigin x + site ↔
            (p.val : ℤ) ∣ (x ⟨p.val, mem_union_left _ p.property⟩).val + site :=
          data.residueOrigin_divisibility x ⟨p.val, mem_union_left _ p.property⟩ site
        simp only [hdiv]
      · apply hg
        intro q hq
        let p : data.Q := ⟨q, hq⟩
        rw [Int.cast_add, Int.cast_add]
        exact congrArg (fun a : ZMod q => a + (site : ZMod q))
          ((data.residueOrigin_spec x (data.paddingCoordinate p)).trans
            (data.paddingResidueOrigin_spec (data.paddingRestriction x) p).symm)
    _ = (data.tupleResidueLaw B hB).average
        (fun z => F (paddingResidueAvailable data.P B site z)) *
          (data.paddingResidueLaw B hB).average
            (fun z => g (data.paddingResidueOrigin z + site)) :=
      data.residue_average_tuple_padding hB
        (fun z : data.P → Fin B => F (paddingResidueAvailable data.P B site z))
        (fun z : data.Q → Fin B => g (data.paddingResidueOrigin z + site))
    _ = _ := by
      congr 1
      exact padding_residue_average data.P B (fun p hp => (data.primeP p hp).two_le)
        (fun p hp => hB p (mem_union_left _ hp)) site F


theorem positive_prime_padding_degree_tail
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card)
    (site : ℤ) (g : ℤ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → g n = g m) :
    (data.residueLaw B hB).average (fun x =>
      (positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) * g (data.residueOrigin x + site)) ≤
      (positivePrimeNormalizer S * Real.exp (-2 * W * S.card)) *
        (data.paddingResidueLaw B hB).average (fun z =>
          g (data.paddingResidueOrigin z + site)) := by
  let q := fun p : data.P => 1 / (p.val : ℝ)
  let T := primeSelection data.P S hSP
  let F := fun a : data.P → Bool => positiveCenterWeight q T a *
    if 6 * W * T.card < booleanCount a then (1 : ℝ) else 0
  have he (x : ↥(data.P ∪ data.Q) → Fin B) :
      (positivePrimeWeight S (data.residueOrigin x + site) *
        if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then (1 : ℝ) else 0) =
      F (fun p : data.P => decide ((p.val : ℤ) ∣ data.residueOrigin x + site)) := by
    dsimp [F]
    rw [positivePrimeWeight_eq_selection data.P S hSP,
      actualPrimeDegree_eq_count, primeSelection_card]
  have htail : (paddingOriginalLaw data.P (fun p hp => (data.primeP p hp).two_le)).average F ≤
      positivePrimeNormalizer S * Real.exp (-2 * W * S.card) := by
    rw [← data.residue_average_prime_availability hB site F]
    simp_rw [← he]
    exact data.positive_prime_degree_tail hB S hSP W hW hmass site
  simp_rw [he]
  rw [data.residue_average_prime_boolean_padding hB site F g hg]
  exact mul_le_mul_of_nonneg_right htail
    ((data.paddingResidueLaw B hB).average_nonneg (fun z => hg0 _))

end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DegreeCostResidue
namespace OAI

/-! The model degree cost preserves one reciprocal for the fixed
padding divisor. This is the estimate transferred to integer intervals. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)

lemma padding_divisor_probability_le (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q) (site : ℤ) :
    (data.paddingResidueLaw B hB).average (fun z =>
      if (q : ℤ) ∣ data.paddingResidueOrigin z + site then (1 : ℝ) else 0) ≤
        1 / (q : ℝ) := by
  have hsupport := retainedPrimeDivisor_factors data.Q data.primeQ hq
  have hsq := retainedPrimeDivisor_squarefree data.Q data.primeQ hq
  have he (z : data.Q → Fin B) :
      (q : ℤ) ∣ data.paddingResidueOrigin z + site ↔
        PaddingResidueEvent data.Q (fun _ : Fin 1 => q) (fun _ => site) z := by
    rw [← padding_literal_support_iff_dvd data.Q data.primeQ
      (data.paddingResidueOrigin z + site) q hq, paddingAvailablePrimes_integer]
    constructor
    · intro hz i p hp
      have hdiv := (mem_filter.mp (hz hp)).2
      exact (residue_offset_divisibility
        ((z p).val : ZMod p.val) (data.paddingResidueOrigin z) site
        (data.paddingResidueOrigin_spec z p)).mp hdiv
    · intro hz p hp
      refine mem_filter.mpr ⟨hsupport hp, ?_⟩
      let p' : data.Q := ⟨p, hsupport hp⟩
      exact (residue_offset_divisibility ((z p').val : ZMod p)
        (data.paddingResidueOrigin z) site (data.paddingResidueOrigin_spec z p')).mpr
          (hz 0 p' hp)
  have hs : paddingPrimeSupport (fun _ : Fin 1 => q) = q.primeFactors := by
    ext p
    simp only [paddingPrimeSupport, mem_biUnion, mem_univ, true_and]
    exact ⟨fun ⟨_, hp⟩ => hp, fun hp => ⟨0, hp⟩⟩
  have hsup : paddingPrimeSupport (fun _ : Fin 1 => q) ⊆ data.Q := by
    simpa only [hs] using hsupport
  have hh := paddingResidueEvent_probability_le data.Q (fun _ : Fin 1 => q)
    (fun _ => site) B (fun p hp => (data.primeQ p hp).pos)
    (fun p hp => hB p (mem_union_right _ hp)) hsup
  have hprod : (∏ p ∈ paddingPrimeSupport (fun _ : Fin 1 => q), (p : ℝ)⁻¹) =
      1 / (q : ℝ) := by
    rw [hs]
    rw [prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq, one_div]
  rw [hprod] at hh
  simpa [FiniteLaw.probability, he, ProhibitedPrimeFamily.paddingResidueLaw] using hh

theorem positive_divisor_degree_cost_oai (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (S : Finset ℕ) (hSP : S ⊆ data.P) (q : ℕ) (hq : q ∈ retainedPrimeDivisors data.Q)
    (W : ℝ) (hW : 10 ≤ W)
    (hmass : (∑ p ∈ data.P, 1 / (p : ℝ)) ≤ 2 * W * S.card) (site : ℤ) :
    (data.residueLaw B hB).average (fun x =>
      actualPaddingCoefficient q * positivePrimeWeight S (data.residueOrigin x + site) *
        if (q : ℤ) ∣ data.residueOrigin x + site ∧
          6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
          then 1 else 0) ≤
      actualPaddingCoefficient q / q * positivePrimeNormalizer S *
        Real.exp (-2 * W * S.card) := by
  let g := fun n : ℤ => if (q : ℤ) ∣ n then (1 : ℝ) else 0
  have hg0 (n) : 0 ≤ g n := by dsimp [g]; split_ifs <;> norm_num
  have hg (n m : ℤ) (he : ∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) : g n = g m := by
    have hd := squarefree_divisor_congr data.Q q
      (retainedPrimeDivisor_squarefree data.Q data.primeQ hq)
      (retainedPrimeDivisor_factors data.Q data.primeQ hq) n m he
    simp only [g, hd]
  have hh := data.positive_prime_padding_degree_tail hB S hSP W hW hmass site g hg0 hg
  have hprob := data.padding_divisor_probability_le hB q hq site
  have hconstant : 0 ≤ positivePrimeNormalizer S * Real.exp (-2 * W * S.card) := by
    unfold positivePrimeNormalizer
    positivity
  have hbound := hh.trans (mul_le_mul_of_nonneg_left hprob hconstant)
  have hm := mul_le_mul_of_nonneg_left hbound (actualPaddingCoefficient_nonneg q)
  calc
    _ = actualPaddingCoefficient q * (data.residueLaw B hB).average (fun x =>
        (positivePrimeWeight S (data.residueOrigin x + site) *
          if 6 * W * S.card < (actualPaddingDegree data.P (data.residueOrigin x + site) : ℝ)
            then 1 else 0) * g (data.residueOrigin x + site)) := by
      rw [mul_comm (actualPaddingCoefficient q) _, ← FiniteLaw.average_mul_const]
      apply congrArg (data.residueLaw B hB).average
      funext x
      dsimp [g]
      split_ifs <;> simp_all
      all_goals ring
    _ ≤ _ := by convert (preTransparency := .instances) hm using 1; ring

end ProhibitedPrimeFamily


end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.ProhibitedPrimeFamily.positive_divisor_degree_cost_oai := @OAI.TwoPointCorrelations.ProhibitedPrimeFamily.positive_divisor_degree_cost_oai
