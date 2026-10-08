-- Prove2me | solution 1 for OAI.TwoPointCorrelations.eventually_prohibited_good_trace_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:51:22.25579+00:00
-- url     : https://prove2.me/submissions/48dd8509-0681-43b9-b418-ab5fccd2ef85

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_tuple_column_array_cover

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






end FiniteLaw

end TwoPointCorrelations

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

omit [Fintype A] [DecidableEq A] in
theorem abs_mixedDifference_le (a : ι → A) (F : (ι → A) → ℝ)
    (hF : ∀ x, |F x| ≤ 1) (x : ι → A) :
    |mixedDifference a F x| ≤ 2 ^ Fintype.card ι := by
  unfold mixedDifference
  calc
    _ ≤ ∑ S : Finset ι, |(-1 : ℝ) ^ Sᶜ.card * F (forceCoordinates S a x)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S : Finset ι, (1 : ℝ) := by
      apply sum_le_sum
      intro S _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        hF (forceCoordinates S a x)
    _ = _ := by simp

omit [Fintype A] [DecidableEq A] in
/-- A nonzero alternating difference has a nonzero hybrid term. -/
theorem exists_forced_value_ne_zero (a : ι → A) (F : (ι → A) → ℝ) (x : ι → A)
    (h : mixedDifference a F x ≠ 0) :
    ∃ S : Finset ι, F (forceCoordinates S a x) ≠ 0 := by
  by_contra! hc
  apply h
  unfold mixedDifference
  apply sum_eq_zero
  intro S _
  rw [hc S, mul_zero]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingSum
namespace OAI

/-!
# Summing padding choices in one fixed residue environment

This is the backwards induction of manuscript Lemma `q:padding-sum`.
A state is the current integer site. The transitions may depend on the current
padding choice and all earlier choices through that site. No independence of
translated residue coordinates is assumed.
-/

open scoped _root_.BigOperators

namespace TwoPointCorrelations


/-- A row bound at every site controls the full path sum, despite the dependence
of later sites on earlier padding choices. -/
theorem paddingMass_le (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hweight : ∀ i n q, q ∈ Q → 0 ≤ weight i n q)
    (hrow : ∀ i n, ∑ q ∈ Q, weight i n q ≤ K)
    (m i : ℕ) (n : ℤ) : paddingMass Q weight next m i n ≤ K ^ m := by
  induction m generalizing i n with
  | zero => simp [paddingMass]
  | succ m ih =>
    calc
      paddingMass Q weight next (m + 1) i n =
          ∑ q ∈ Q, weight i n q * paddingMass Q weight next m (i + 1) (next i n q) := rfl
      _ ≤ ∑ q ∈ Q, weight i n q * K ^ m := by
        apply Finset.sum_le_sum
        intro q hq
        exact mul_le_mul_of_nonneg_left (ih _ _) (hweight i n q hq)
      _ = (∑ q ∈ Q, weight i n q) * K ^ m := by rw [Finset.sum_mul]
      _ ≤ K * K ^ m := mul_le_mul_of_nonneg_right (hrow i n) (pow_nonneg hK _)
      _ = K ^ (m + 1) := by ring





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PartialCentering
namespace OAI

/-! Exact singleton centering on selected coordinates of the complete residue sample. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]



omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma selectedMixedDifference_bound (S : Finset ι) (a : ι → A) (F : (ι → A) → ℝ)
    (hF : ∀ x, |F x| ≤ 1) (x : ι → A) :
    |selectedMixedDifference S a F x| ≤ 2 ^ S.card := by
  simpa only [selectedMixedDifference, Fintype.card_coe] using
    abs_mixedDifference_le (fun i : S => a i)
      (fun z : S → A => F (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
      (fun z => hF _) (fun i : S => x i)

namespace FiniteLaw




end FiniteLaw

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitOccurrenceWeights
namespace OAI

/-! The exact reciprocal exponent of each nonsingleton lit designation. -/

namespace TwoPointCorrelations

open _root_.Finset



lemma litReciprocalExponent_pos (lit unlit : ℕ) (hm : 2 ≤ lit + unlit) :
    1 ≤ litReciprocalExponent lit unlit := by
  unfold litReciprocalExponent
  split_ifs <;> omega





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.OccurrenceCounts
namespace OAI

/-! Counts of the actual slots belonging to each prime label. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]




omit [Fintype ι] in
lemma lit_unlit_count (label : τ → ι) (lit : τ → Bool) (i : ι) :
    (litOccurrences label lit i).card + (unlitOccurrences label lit i).card =
      (labelOccurrences label i).card := by
  have he : unlitOccurrences label lit i =
      (labelOccurrences label i).filter (fun t => ¬lit t = true) := by
    ext t
    simp [unlitOccurrences]
  rw [litOccurrences, he]
  exact card_filter_add_card_filter_not (s := labelOccurrences label i) (fun t => lit t = true)

lemma total_label_occurrences (label : τ → ι) :
    ∑ i, (labelOccurrences label i).card = Fintype.card τ := by
  simpa only [labelOccurrences, mem_univ, filter_true, card_univ] using
    sum_card_fiberwise_eq_card_filter (univ : Finset τ) (univ : Finset ι) label





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitConsistency
namespace OAI

/-! Compress all lit tests for one prime into one forced residue, or zero. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ A : Type*} [DecidableEq ι] [DecidableEq A]



omit [DecidableEq A] in
lemma litForcedTarget_at (L : Finset τ) (label : τ → ι) (target : τ → A)
    (base : ι → A) (hL : LitConsistent L label target) (t : τ) (ht : t ∈ L) :
    litForcedTarget L label target base (label t) = target t := by
  classical
  have hex : ∃ u ∈ L, label u = label t := ⟨t, ht, rfl⟩
  simp only [litForcedTarget, dif_pos hex]
  exact hL _ (Classical.choose_spec hex).1 t ht (Classical.choose_spec hex).2



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PerfectRows
namespace OAI

/-! The imperfect-row budget comes from actual singleton and unlit slots. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

lemma singleton_slot_count (label : τ → ι) :
    (univ.filter (fun t : τ => label t ∈ singletonLabels label)).card =
      (singletonLabels label).card := by
  have hf := sum_card_fiberwise_eq_card_filter (univ : Finset τ) (singletonLabels label) label
  have hs : (∑ i ∈ singletonLabels label, (labelOccurrences label i).card) =
      (singletonLabels label).card := by
    calc
      _ = ∑ _i ∈ singletonLabels label, 1 := by
        apply sum_congr rfl
        intro i hi
        exact (mem_filter.mp hi).2
      _ = _ := by simp
  exact hf.symm.trans hs


variable {n J : ℕ}



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixClosedWords
namespace OAI

/-! Signed closed-word expansion of the actual matrix power moment. -/

namespace TwoPointCorrelations

open _root_.Finset

section Paths

variable {V : Type*} [Fintype V] [DecidableEq V]








omit [DecidableEq V] in
lemma sum_fin_cons {k : ℕ} (f : (Fin (k + 1) → V) → ℝ) :
    ∑ v, f v = ∑ a, ∑ v : Fin k → V, f (Fin.cons a v) := by
  have he := (Fin.consEquiv (fun _ : Fin (k + 1) => V)).sum_comp f
  change (∑ p : V × (Fin k → V), f (Fin.cons p.1 p.2)) = ∑ v, f v at he
  simpa only [Fintype.sum_prod_type] using he.symm







end Paths

section Nonbacktracking

variable {D V : Type*} [DecidableEq D]



variable [DecidableEq V]



end Nonbacktracking

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DesignationWeights
namespace OAI

/-! Group literal unlit factors and forced lit atoms into exact prime exponents. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]

lemma product_grouped_by_label (S : Finset τ) (label : τ → ι) (θ : ι → ℝ) :
    (∏ t ∈ S, θ (label t)) = ∏ i, θ i ^ (S.filter (fun t => label t = i)).card := by
  rw [← prod_fiberwise' S label θ]
  simp only [prod_const]

omit [Fintype ι] in
lemma mem_label_image_iff_count_pos (S : Finset τ) (label : τ → ι) (i : ι) :
    i ∈ S.image label ↔ 0 < (S.filter (fun t => label t = i)).card := by
  rw [card_pos, filter_nonempty_iff]
  exact mem_image

lemma label_image_product (S : Finset τ) (label : τ → ι) (θ : ι → ℝ) :
    (∏ i ∈ S.image label, θ i) =
      ∏ i, θ i ^ (if (S.filter (fun t => label t = i)).card = 0 then 0 else 1) := by
  have he : (∏ i ∈ S.image label, θ i) =
      ∏ i, if i ∈ S.image label then θ i else 1 := by
    rw [← prod_filter]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
  rw [he]
  apply prod_congr rfl
  intro i _
  have hi := mem_label_image_iff_count_pos S label i
  by_cases hc : (S.filter (fun t => label t = i)).card = 0
  · have hn : i ∉ S.image label := by simpa [hc] using hi
    simp [hc, hn]
  · have hm : i ∈ S.image label := hi.mpr (Nat.pos_of_ne_zero hc)
    simp [hc, hm]

/-- The modulus atom appears once if there is any lit occurrence; unlit
occurrences retain their individual scalar reciprocals. -/
lemma designated_weight_exponents (L U : Finset τ) (label : τ → ι) (θ : ι → ℝ) :
    (∏ t ∈ U, θ (label t)) * (∏ i ∈ L.image label, θ i) =
      ∏ i, θ i ^ litReciprocalExponent
        (L.filter (fun t => label t = i)).card (U.filter (fun t => label t = i)).card := by
  rw [product_grouped_by_label, label_image_product, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← pow_add]
  rfl




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualDesignations
namespace OAI

/-! Literal lit/unlit slot sets and the reciprocal coefficient of an actual word. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]



lemma nonsingleton_lit_fiber (label : τ → ι) (lit : τ → Bool) (i : ι) :
    (nonsingletonLitSlots label lit).filter (fun t => label t = i) =
      if i ∈ nonsingletonLabels label then litOccurrences label lit i else ∅ := by
  classical
  ext t
  by_cases ht : label t = i <;> by_cases hi : i ∈ nonsingletonLabels label <;>
    simp [nonsingletonLitSlots, litOccurrences, labelOccurrences, ht, hi]

lemma nonsingleton_unlit_fiber (label : τ → ι) (lit : τ → Bool) (i : ι) :
    (nonsingletonUnlitSlots label lit).filter (fun t => label t = i) =
      if i ∈ nonsingletonLabels label then unlitOccurrences label lit i else ∅ := by
  classical
  ext t
  by_cases ht : label t = i <;> by_cases hi : i ∈ nonsingletonLabels label <;>
    simp [nonsingletonUnlitSlots, unlitOccurrences, labelOccurrences, ht, hi]





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ObservedDesignationWeights
namespace OAI

/-! Exact designation weights when the ambient prime pool contains unused primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

lemma filtered_power_product (S : Finset ι) (θ : ι → ℝ) (e : ι → ℕ) :
    (∏ i ∈ S, θ i ^ e i) = ∏ i, θ i ^ (if i ∈ S then e i else 0) := by
  calc
    _ = ∏ i, if i ∈ S then θ i ^ e i else 1 := by
      rw [← prod_filter]
      simp
    _ = _ := by
      apply prod_congr rfl
      intro i _
      split_ifs <;> simp

/-- Each observed prime contributes one baseline reciprocal, including
singletons. Only repeated labels contribute additional exponents. -/
theorem observed_designation_reciprocal_factor (label : τ → ι) (lit : τ → Bool)
    (p : ι → ℝ) :
    (∏ t ∈ nonsingletonUnlitSlots label lit, (p (label t))⁻¹) *
      (∏ i ∈ (nonsingletonLitSlots label lit).image label, (p i)⁻¹) *
      (∏ i ∈ singletonLabels label, (p i)⁻¹) =
        (∏ i ∈ univ.image label, (p i)⁻¹) *
          ∏ i ∈ nonsingletonLabels label, (p i)⁻¹ ^
            extraReciprocalExponent (litOccurrences label lit i).card
              (unlitOccurrences label lit i).card := by
  rw [designated_weight_exponents (nonsingletonLitSlots label lit)
    (nonsingletonUnlitSlots label lit) label (fun i => (p i)⁻¹)]
  have hs : (∏ i ∈ singletonLabels label, (p i)⁻¹) =
      ∏ i, (p i)⁻¹ ^ (if i ∈ singletonLabels label then 1 else 0) := by
    simpa only [pow_one] using
      filtered_power_product (singletonLabels label) (fun i => (p i)⁻¹) (fun _ => 1)
  rw [hs, label_image_product univ label (fun i => (p i)⁻¹),
    filtered_power_product (nonsingletonLabels label) (fun i => (p i)⁻¹)
      (fun i => extraReciprocalExponent (litOccurrences label lit i).card
        (unlitOccurrences label lit i).card), ← prod_mul_distrib, ← prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [← pow_add, ← pow_add]
  congr 1
  rw [nonsingleton_lit_fiber, nonsingleton_unlit_fiber]
  by_cases hn : i ∈ nonsingletonLabels label
  · have hc := (mem_filter.mp hn).2
    have hm := lit_unlit_count label lit i
    have hp := litReciprocalExponent_pos (litOccurrences label lit i).card
      (unlitOccurrences label lit i).card (by omega)
    have hns : i ∉ singletonLabels label := by
      simp only [singletonLabels, mem_filter, mem_univ, true_and]
      omega
    simp only [if_pos hn, if_neg hns, add_zero,
      extraReciprocalExponent]
    have hz : (univ.filter (fun t => label t = i)).card ≠ 0 := by
      change (labelOccurrences label i).card ≠ 0
      omega
    simp only [if_neg hz]
    omega
  · have hc : (labelOccurrences label i).card < 2 := by
      simpa only [nonsingletonLabels, mem_filter, mem_univ, true_and, not_le] using hn
    simp only [if_neg hn, card_empty, litReciprocalExponent, ↓reduceIte,
      add_zero, zero_add]
    by_cases hzero : (labelOccurrences label i).card = 0
    · have hns : i ∉ singletonLabels label := by
        simp [singletonLabels, hzero]
      simp only [if_neg hns]
      change 0 = if (labelOccurrences label i).card = 0 then 0 else 1
      rw [if_pos hzero]
    · have hone : (labelOccurrences label i).card = 1 := by omega
      have hss : i ∈ singletonLabels label := by simp [singletonLabels, hone]
      simp only [if_pos hss]
      change 1 = if (labelOccurrences label i).card = 0 then 0 else 1
      rw [if_neg hzero]

theorem observed_designation_reciprocal_bound (label : τ → ι) (lit : τ → Bool)
    (p : ι → ℝ) (H : ℝ) (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    (∏ t ∈ nonsingletonUnlitSlots label lit, (p (label t))⁻¹) *
      (∏ i ∈ (nonsingletonLitSlots label lit).image label, (p i)⁻¹) *
      (∏ i ∈ singletonLabels label, (p i)⁻¹) ≤
        (∏ i ∈ univ.image label, (p i)⁻¹) * H⁻¹ ^
          (∑ i ∈ nonsingletonLabels label,
            extraReciprocalExponent (litOccurrences label lit i).card
              (unlitOccurrences label lit i).card) := by
  rw [observed_designation_reciprocal_factor, ← prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod
    · intro i _
      exact pow_nonneg (inv_nonneg.mpr (hH.trans_le (hp i)).le) _
    · intro i _
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hH.trans_le (hp i)).le)
        (inv_anti₀ hH (hp i)) _
  · exact prod_nonneg (fun i _ => inv_nonneg.mpr (hH.trans_le (hp i)).le)


lemma designationLit_unlit (label : τ → ι) (U : Finset τ)
    (hU : U ⊆ nonsingletonSlots label) :
    nonsingletonUnlitSlots label (designationLit U) = U := by
  ext t
  simp only [nonsingletonUnlitSlots, mem_filter, mem_univ, true_and, designationLit,
    decide_eq_false_iff_not, not_not]
  constructor
  · exact And.right
  · intro ht
    exact ⟨(mem_filter.mp (hU ht)).2, ht⟩

lemma designationLit_lit (label : τ → ι) (U : Finset τ) :
    nonsingletonLitSlots label (designationLit U) = nonsingletonSlots label \ U := by
  ext t
  simp [nonsingletonLitSlots, nonsingletonSlots, designationLit, and_comm]

/-- The coefficient in the full signed expansion retains the actual
extra-exponent saving even when unused primes occur in the ambient pool. -/
theorem full_word_designated_reciprocal_bound (label : τ → ι) (U : Finset τ)
    (hU : U ⊆ nonsingletonSlots label) (p : ι → ℕ) (H : ℝ)
    (hH : 0 < H) (hp : ∀ i, H ≤ p i) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label ≤
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^
        (∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card) := by
  simpa only [designationLit_unlit label U hU, designationLit_lit, designatedReciprocal]
    using observed_designation_reciprocal_bound label (designationLit U)
      (fun i => (p i : ℝ)) H hH hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ObservedReciprocalBound
namespace OAI

/-! Extra-reciprocal estimates require the lower prime bound only on used tuple coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma designation_sdiff_decidable {τ : Type*} (d₁ d₂ : DecidableEq τ) (S U : Finset τ) :
    @SDiff.sdiff (Finset τ) (@Finset.instSDiff τ d₁) S U =
      @SDiff.sdiff (Finset τ) (@Finset.instSDiff τ d₂) S U := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  rfl


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.IntegerEdges
namespace OAI

/-! Concrete centered integer edges and the padding-density cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset












lemma retainedPaddingAtom_nonneg (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (q : ℕ) (hL : 0 ≤ L) (hu : 0 ≤ u q) :
    0 ≤ retainedPaddingAtom Q u eligible g L K extra n q := by
  unfold retainedPaddingAtom
  split_ifs
  · exact div_nonneg (mul_nonneg hL hu) (sq_nonneg _)
  · exact le_rfl

lemma retainedPaddingAtom_sum_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (hL : 0 < L) (hK : 0 ≤ K) :
    ∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q ≤ K := by
  classical
  by_cases hk : integerEdgeKeep Q u eligible g L K extra n
  · have heq : (∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q) =
        L * paddingDensity Q u eligible g n := by
      simp only [retainedPaddingAtom, paddingDensity]
      rw [← mul_div_assoc, mul_sum, sum_div]
      apply sum_congr rfl
      intro q _
      by_cases hq : eligible q ∧ (q : ℤ) ∣ n
      · simp [hq.1, hq.2, hk]
      · simp only [show ¬(eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n) from
          fun hh => hq ⟨hh.1, hh.2.1⟩, hq, ite_false, mul_zero, zero_div]
    rw [heq]
    calc
      _ ≤ L * (K / L) := mul_le_mul_of_nonneg_left hk.1 hL.le
      _ = K := by field_simp
  · simpa [retainedPaddingAtom, hk] using hK



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestCode
namespace OAI

/-!
# A finite code for rooted ordered forests

First-child / next-sibling representation turns a rooted ordered forest
into a binary tree. One bit records a leaf; a nonleaf uses a marker and a
vertex-type bit. The resulting code has exactly `3*n+1` bits.
-/

namespace TwoPointCorrelations

open _root_.BinaryTree










/-- Exponential, coefficient-independent count for typed plane-forest shapes. -/
theorem card_bounded_forests (N : ℕ) :
    Nat.card {t : BinaryTree Bool // t.numNodes ≤ N} ≤ 2 ^ (3 * N + 1) := by
  have h := Nat.card_le_card_of_injective (boundedForestCode N) (boundedForestCode_injective N)
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool] using h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestCodeAsymptotics
namespace OAI

/-! Absorbing the sublinear endpoint and exceptional-position costs. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_sublinear_log_cost (d C : ℝ) (hd : d < 1) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ d * Real.log L ≤ L := by
  by_cases hzero : C = 0
  · filter_upwards [eventually_ge_atTop 0] with L hL
    simpa only [hzero, zero_mul] using hL
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  have hb := (isLittleO_log_rpow_atTop (show 0 < 1 - d by linarith)).bound
    (show 0 < 1 / C by positivity)
  filter_upwards [eventually_ge_atTop 1, hb] with L hL hb
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL), Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hb
  calc
    C * L ^ d * Real.log L ≤ C * L ^ d * ((1 / C) * L ^ (1 - d)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C * (1 / C)) * (L ^ d * L ^ (1 - d)) := by ring
    _ = L := by
      rw [mul_one_div_cancel hzero, one_mul, ← Real.rpow_add hLp,
        show d + (1 - d) = 1 by ring, Real.rpow_one]

lemma eventually_forest_endpoint_cost (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L ^ (0.92 : ℝ) * Real.log (4 * L) ≤ L := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_sublinear_log_cost 0.92 (2 * C) (by norm_num) (by positivity)] with L hL hc
  have hLp : 0 < L := by linarith
  have hlog : Real.log (4 * L) ≤ 2 * Real.log L := by
    rw [Real.log_mul (by norm_num) hLp.ne']
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hL
    linarith
  calc
    _ ≤ C * L ^ (0.92 : ℝ) * (2 * Real.log L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = (2 * C) * L ^ (0.92 : ℝ) * Real.log L := by ring
    _ ≤ L := hc


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ForestPathCounting
namespace OAI

/-!
# Counting all realizable numbered path families

The union is over every finite acyclic graph, not a single graph with fixed
numerical coefficients. A typed forest shape and two endpoints per segment
determine the entire family of numbered paths.
-/

namespace TwoPointCorrelations

open _root_.SimpleGraph


namespace ForestPathData

variable {N segments : ℕ}







theorem card_code_le (N segments : ℕ) :
    Fintype.card (Code N segments) ≤ 2 ^ (3 * N + 1) * N ^ (2 * segments) := by
  have ht : Fintype.card {t : BinaryTree Bool // t.numNodes ≤ N} ≤ 2 ^ (3 * N + 1) := by
    simpa only [Nat.card_eq_fintype_card] using card_bounded_forests N
  simp only [Code, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  calc
    _ ≤ 2 ^ (3 * N + 1) * (N * N) ^ segments := Nat.mul_le_mul_right _ ht
    _ = _ := by rw [← pow_two, ← pow_mul]

end ForestPathData





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





theorem card_columnDecoderCode_le (N segments omitted imperfect : ℕ) :
    Fintype.card (ColumnDecoderCode N segments omitted imperfect) ≤
      2 ^ (6 * N + 1) * N ^ (2 * segments + omitted + imperfect) := by
  have h := ForestPathData.card_code_le N segments
  calc
    _ = Fintype.card (ForestPathData.Code N segments) *
        (2 ^ N * ((2 * 2) ^ N * (N ^ omitted * N ^ imperfect))) := by
      simp only [ColumnDecoderCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool]
    _ ≤ (2 ^ (3 * N + 1) * N ^ (2 * segments)) *
        (2 ^ N * ((2 * 2) ^ N * (N ^ omitted * N ^ imperfect))) :=
      Nat.mul_le_mul_right _ h
    _ = _ := by
      rw [mul_pow]
      calc
        _ = (2 ^ (3 * N + 1) * 2 ^ N * 2 ^ N * 2 ^ N) *
            (N ^ (2 * segments) * N ^ omitted * N ^ imperfect) := by ring
        _ = _ := by
          have hb : 2 ^ (3 * N + 1) * 2 ^ N * 2 ^ N * 2 ^ N =
              2 ^ (6 * N + 1) := by
            rw [← pow_add, ← pow_add, ← pow_add]
            congr 1
            omega
          rw [hb, ← pow_add, ← pow_add]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnDecoderAsymptotics
namespace OAI

/-! Exponential bound for the universal full-column decoder. -/

namespace TwoPointCorrelations

open _root_.Filter

/-- The exponent constant is absolute. Fixed coefficients in the
sublinear segment budget only change the lower threshold for `L`. -/
theorem eventually_column_decoder_exponential (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k N segments omitted imperfect : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      ((2 * segments + omitted + imperfect : ℕ) : ℝ) ≤ C * L ^ (0.92 : ℝ) →
      (Fintype.card (ColumnDecoderCode N segments omitted imperfect) : ℝ) ≤
        Real.exp (52 * k) := by
  filter_upwards [eventually_ge_atTop 4, eventually_forest_endpoint_cost C hC] with L hL hcost
  intro k N segments omitted imperfect hklo hkhi hN hNk hM
  let M := 2 * segments + omitted + imperfect
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNreal : (N : ℝ) ≤ 4 * L := by
    have h := (show (N : ℝ) ≤ 4 * k by exact_mod_cast hNk)
    linarith
  have hlogN : Real.log N ≤ Real.log (4 * L) := Real.log_le_log hNpos hNreal
  have hlogpos : 0 ≤ Real.log (4 * L) := Real.log_nonneg (by linarith)
  have hMcost : (M : ℝ) * Real.log N ≤ L := by
    calc
      _ ≤ (M : ℝ) * Real.log (4 * L) := mul_le_mul_of_nonneg_left hlogN (by positivity)
      _ ≤ (C * L ^ (0.92 : ℝ)) * Real.log (4 * L) :=
        mul_le_mul_of_nonneg_right hM hlogpos
      _ ≤ L := hcost
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbits : (2 : ℝ) ^ (6 * N + 1) ≤ Real.exp (6 * N + 1) := by
    calc
      _ ≤ (Real.exp 1) ^ (6 * N + 1) := pow_le_pow_left₀ (by norm_num) htwo _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hcard : (Fintype.card (ColumnDecoderCode N segments omitted imperfect) : ℝ) ≤
      (2 : ℝ) ^ (6 * N + 1) * (N : ℝ) ^ M := by
    exact_mod_cast card_columnDecoderCode_le N segments omitted imperfect
  calc
    _ ≤ (2 : ℝ) ^ (6 * N + 1) * (N : ℝ) ^ M := hcard
    _ ≤ Real.exp (6 * N + 1) * Real.exp ((M : ℝ) * Real.log N) := by
      rw [Real.exp_nat_mul, Real.exp_log hNpos]
      exact mul_le_mul_of_nonneg_right hbits (by positivity)
    _ = Real.exp ((6 * N + 1) + (M : ℝ) * Real.log N) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (52 * k) := by
      apply Real.exp_le_exp.mpr
      have hNbound : (N : ℝ) ≤ 4 * k := by exact_mod_cast hNk
      linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BoundedColumnCodes
namespace OAI

/-! One code universe when segment, omitted-run and imperfect counts vary. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter





/-- The union over all bounded counts still has an absolute exponential
cost. Fixed constants in the sublinear budget affect only the threshold. -/
theorem eventually_bounded_column_code_exponential (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k N segments omitted imperfect : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      segments ≤ N → omitted ≤ N → imperfect ≤ N →
      ((2 * segments + omitted + imperfect : ℕ) : ℝ) ≤ C * L ^ (0.92 : ℝ) →
      (Fintype.card (BoundedColumnDecoderCode N segments omitted imperfect) : ℝ) ≤
        Real.exp (64 * k) := by
  filter_upwards [eventually_column_decoder_exponential C hC] with L hcode
  intro k N segments omitted imperfect hklo hkhi hN hNk hS hO hI hbudget
  have heach (s : Fin (segments + 1)) (o : Fin (omitted + 1)) (i : Fin (imperfect + 1)) :
      (Fintype.card (ColumnDecoderCode N s.val o.val i.val) : ℝ) ≤ Real.exp (52 * k) := by
    apply hcode k N s.val o.val i.val hklo hkhi hN hNk
    apply le_trans _ hbudget
    exact_mod_cast (show 2 * s.val + o.val + i.val ≤ 2 * segments + omitted + imperfect by omega)
  have hfactor (a : ℕ) (ha : a ≤ N) : (a : ℝ) + 1 ≤ Real.exp N := by
    have h : (a : ℝ) ≤ N := by exact_mod_cast ha
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hcounts : ((segments : ℝ) + 1) * (omitted + 1) * (imperfect + 1) ≤
      Real.exp (3 * N) := by
    calc
      _ ≤ Real.exp N * Real.exp N * Real.exp N := by
        gcongr
        · exact hfactor segments hS
        · exact hfactor omitted hO
        · exact hfactor imperfect hI
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc
    _ = ∑ s : Fin (segments + 1), ∑ o : Fin (omitted + 1), ∑ i : Fin (imperfect + 1),
        (Fintype.card (ColumnDecoderCode N s.val o.val i.val) : ℝ) := by
      simp only [BoundedColumnDecoderCode, Fintype.card_sigma, Nat.cast_sum]
    _ ≤ ∑ _s : Fin (segments + 1), ∑ _o : Fin (omitted + 1), ∑ _i : Fin (imperfect + 1),
        Real.exp (52 * k) := by
      exact sum_le_sum (fun s _ => sum_le_sum (fun o _ => sum_le_sum (fun i _ => heach s o i)))
    _ = (((segments : ℝ) + 1) * (omitted + 1) * (imperfect + 1)) * Real.exp (52 * k) := by
      simp [mul_assoc]
    _ ≤ Real.exp (3 * N) * Real.exp (52 * k) :=
      mul_le_mul_of_nonneg_right hcounts (Real.exp_pos _).le
    _ = Real.exp (3 * N + 52 * k) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (64 * k) := by
      apply Real.exp_le_exp.mpr
      have h : (N : ℝ) ≤ 4 * k := by exact_mod_cast hNk
      linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnCodeUniverse
namespace OAI

/-! A fixed finite universe for every column with the proved numerical budget. -/

namespace TwoPointCorrelations

open _root_.Filter





/-- All permitted counts are included simultaneously. The factor 264 is
absorbed only into the large-scale threshold; the exponential constant 64
is the same for every column and every choice of numerical coefficients. -/
theorem eventually_budget_column_code_card :
    ∀ᶠ L : ℝ in atTop, ∀ k N : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      (Fintype.card (BudgetColumnCode N L) : ℝ) ≤ Real.exp (64 * k) := by
  filter_upwards [eventually_bounded_column_code_exponential 264 (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L h hL
  intro k N hklo hkhi hN hNk
  have hc : columnBudgetCap N L ≤ N := Nat.min_le_left _ _
  have hfloor : (columnBudgetCap N L : ℝ) ≤ 66 * L ^ (0.92 : ℝ) := by
    have hf := Nat.floor_le (show 0 ≤ 66 * L ^ (0.92 : ℝ) by positivity)
    have hm : (columnBudgetCap N L : ℝ) ≤ ⌊66 * L ^ (0.92 : ℝ)⌋₊ := by
      exact_mod_cast (Nat.min_le_right N ⌊66 * L ^ (0.92 : ℝ)⌋₊)
    exact hm.trans hf
  apply h k N _ _ _ hklo hkhi hN hNk hc hc hc
  push_cast
  nlinarith






/-- The full column pattern array has cost exponential in `J*k`, with
one universal finite set for all numerical assignments. -/
theorem eventually_budget_column_array_card :
    ∀ᶠ L : ℝ in atTop, ∀ k J N : ℕ,
      L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → 1 ≤ N → N ≤ 4 * k →
      (Fintype.card (BudgetColumnArrayCode J N L) : ℝ) ≤ Real.exp (64 * k * J) := by
  filter_upwards [eventually_budget_column_code_card] with L h
  intro k J N hklo hkhi hN hNk
  let : Fintype (BudgetColumnCode N L) := inferInstance
  have hc := h k N hklo hkhi hN hNk
  calc
    _ = (Fintype.card (BudgetColumnCode N L) : ℝ) ^ J := by
      simp only [BudgetColumnArrayCode, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    _ ≤ (Real.exp (64 * k)) ^ J := pow_le_pow_left₀ (by positivity) hc J
    _ = Real.exp (64 * k * J) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingWordSum
namespace OAI

/-! The recursive padding bound is the full sum over actual padding words. -/

namespace TwoPointCorrelations

open _root_.Finset


theorem paddingMass_eq_sum_words (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (m i : ℕ) (n : ℤ) :
    paddingMass Q weight next m i n = ∑ q : Fin m → Q, paddingWordWeight Q weight next i n q := by
  classical
  induction m generalizing i n with
  | zero => simp [paddingMass, paddingWordWeight]
  | succ m ih =>
      rw [paddingMass, sum_fin_cons, ← sum_coe_sort Q]
      apply sum_congr rfl
      intro q _
      rw [ih, mul_sum]
      apply sum_congr rfl
      intro tail _
      simp only [paddingWordWeight, Fin.cons_zero, Fin.tail_cons]

/-- Literal finite path sum, retaining the departure density cutoff at
every visited site, uniformly in all earlier padding choices. -/
theorem retained_padding_word_sum_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (next : ℕ → ℤ → ℕ → ℤ)
    (hL : 0 < L) (hK : 0 ≤ K) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (m i : ℕ) (n : ℤ) :
    (∑ q : Fin m → Q, paddingWordWeight Q
      (fun i n q => retainedPaddingAtom Q u (eligible i) g L K (extra i) n q)
      next i n q) ≤ K ^ m := by
  rw [← paddingMass_eq_sum_words]
  apply paddingMass_le Q _ next K hK
  · intro i n q hq
    exact retainedPaddingAtom_nonneg Q u (eligible i) g L K (extra i) n q hL.le (hu q hq)
  · intro i n
    exact retainedPaddingAtom_sum_le Q u (eligible i) g L K (extra i) n hL hK

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitBlockGeometry
namespace OAI

/-! Perfect blocks use only the lit divisibilities at their actual positions. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem positiveWord_iff_departures (h : ℕ) (x : ℤ) (w : List SignedStep) :
    PositiveWord h x w ↔ ∀ i : Fin w.length,
      (w.get i).divisor ∣ x + wordDisplacement h (w.take i.val) := by
  induction w generalizing x with
  | nil => simp
  | cons a w ih =>
      rw [positiveWord_cons, ih]
      constructor
      · rintro ⟨ha, hw⟩ i
        rcases i with ⟨i, hi⟩
        cases i with
        | zero => simpa using ha
        | succ i =>
            simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
              wordDisplacement_cons, add_assoc] using hw ⟨i, by simpa using hi⟩
      · intro hw
        refine ⟨?_, ?_⟩
        · simpa using hw ⟨0, by simp⟩
        · intro i
          simpa only [List.get_eq_getElem, List.getElem_cons_succ, List.take_succ_cons,
            wordDisplacement_cons, add_assoc] using hw ⟨i.val + 1, by simp⟩



namespace ColumnWordPattern

variable {α : Type*} [Fintype α] [DecidableEq α]


end ColumnWordPattern

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MidpointCut
namespace OAI

/-! Force the trace midpoint boundary by charging one extra imperfect position. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem imperfectColumnCount_eq_card_compl {n : ℕ} (perfect : Finset (Fin n)) :
    imperfectColumnCount perfect = perfectᶜ.card := by
  classical
  let entries := (List.finRange n).filter (fun i => !decide (i ∈ perfect))
  have he : columnPositionEntries perfect =
      (List.finRange n).map (fun i => (i, decide (i ∈ perfect))) := by
    simp [columnPositionEntries, List.finRange, List.map_ofFn, Function.comp_def]
  have hn : entries.Nodup := (List.nodup_finRange n).filter _
  have hs : entries.toFinset = perfectᶜ := by
    ext i
    simp [entries]
  rw [imperfectColumnCount, he, List.filter_map, List.length_map]
  change entries.length = perfectᶜ.card
  rw [← List.toFinset_card_of_nodup hn, hs]

theorem imperfectColumnCount_erase_le {n : ℕ} (perfect : Finset (Fin n)) (cut : Fin n) :
    imperfectColumnCount (perfect.erase cut) ≤ imperfectColumnCount perfect + 1 := by
  classical
  rw [imperfectColumnCount_eq_card_compl, imperfectColumnCount_eq_card_compl]
  have hs : (perfect.erase cut)ᶜ ⊆ insert cut perfectᶜ := by
    intro i hi
    by_cases he : i = cut
    · simp [he]
    · have hp : i ∉ perfect := by
        intro hip
        exact (mem_compl.mp hi) (mem_erase.mpr ⟨he, hip⟩)
      exact mem_insert_of_mem (mem_compl.mpr hp)
  exact (card_le_card hs).trans (card_insert_le _ _)




/-- The one additional midpoint reference fits inside the same imperfect
budget once the singleton and unlit exceptional classes have been removed. -/
theorem eventually_imperfect_with_cut_bound :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ singletons unlit imperfect : ℕ,
      imperfect ≤ singletons + unlit + 1 →
      (singletons : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (unlit : ℝ) ≤ L ^ (1 / 50 : ℝ) →
      (imperfect : ℝ) ≤ 2 * L ^ (1 / 4 : ℝ) := by
  have hp := (tendsto_rpow_atTop (show 0 < (23 / 100 : ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop 2)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hp] with L hL hp
  intro S U I hI hS hU
  have hone : 1 ≤ L ^ (1 / 50 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have he : L ^ (1 / 50 : ℝ) * L ^ (23 / 100 : ℝ) = L ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add (by linarith : 0 < L)]
    norm_num
  have hprod := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by linarith) (1 / 50 : ℝ))
  have hi : (I : ℝ) ≤ (S : ℝ) + U + 1 := by exact_mod_cast hI
  nlinarith

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






lemma stepWord_covered (pairs : Finset (ℕ × ℕ)) (s : ℕ) (w : List SignedStep)
    (hlen : w.length ≤ s) (hpairs : ∀ a ∈ w, (a.tuple, a.padding) ∈ pairs) :
    ∃ c : BoundedStepWords pairs s, decodeStepWord c = w := by
  let f : Fin w.length → StepAlphabet pairs := fun i =>
    ⟨(w.get i).forward, ⟨((w.get i).tuple, (w.get i).padding), hpairs _ (List.get_mem _ _)⟩⟩
  refine ⟨⟨⟨w.length, by omega⟩, f⟩, ?_⟩
  change List.ofFn (fun i : Fin w.length => decodeStep (f i)) = w
  have he : (fun i : Fin w.length => decodeStep (f i)) = w.get := by
    funext i
    cases hw : w.get i
    simp only [f, decodeStep, hw]
  rw [he, List.ofFn_get]








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

lemma positiveWord_iff_prime_tests (h : ℕ) (n : ℤ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple)) :
    PositiveWord h n w ↔ ∀ i : Fin w.length,
      ∀ p ∈ ((w.get i).padding * (w.get i).tuple).primeFactors,
        (p : ℤ) ∣ n + wordDisplacement h (w.take i.val) := by
  rw [positiveWord_iff_departures]
  apply forall_congr'
  intro i
  simpa only [SignedStep.divisor, Nat.cast_mul] using
    squarefree_divisor_iff _ (hsq _ (List.get_mem _ _)) (n + wordDisplacement h (w.take i.val))







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




lemma mem_wordDivisorPrimeSupport (w : List SignedStep) (p : ℕ) :
    p ∈ wordDivisorPrimeSupport w ↔
      ∃ k : Fin w.length, p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors := by
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset]
  exact List.exists_mem_iff_get


/-- A residue test is exact arithmetic positivity at any common integer lift. -/
theorem residuePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h : ℕ)
    (w : List SignedStep) (r : ∀ i, ZMod (p i)) (n : ℤ)
    (hn : ∀ i, (n : ZMod (p i)) = r i)
    (hsq : ∀ a ∈ w, Squarefree (a.padding * a.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    ResiduePositiveWord p h w r ↔ PositiveWord h n w := by
  rw [positiveWord_iff_prime_tests h n w hsq]
  constructor
  · intro hr k q hq
    have hmem : q ∈ wordDivisorPrimeSupport w :=
      (mem_wordDivisorPrimeSupport w q).mpr ⟨k, hq⟩
    obtain ⟨i, rfl⟩ := hcover q hmem
    exact (residue_offset_divisibility (r i) n _ (hn i)).mpr (hr k i hq)
  · intro hn' k i hi
    exact (residue_offset_divisibility (r i) n _ (hn i)).mp (hn' k (p i) hi)





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SplitBadWordSum
namespace OAI

/-!
# Summing tuple and padding classes in the required order

The padding assignment is frozen before applying the nondegenerate tuple
relation. It is then averaged with one reciprocal per padding class. The
statement permits different symbolic words for different padding choices,
since every bound is uniform in those choices.
-/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma sum_reciprocal_assignments {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ) :
    (∑ x : ι → P, ∏ i, ((x i).val : ℝ)⁻¹) = primeHarmonicMass P ^ Fintype.card ι := by
  simpa only [prod_const, card_univ, primeHarmonicMass] using
    (Fintype.prod_sum (fun (_ : ι) (p : P) => (p.val : ℝ)⁻¹)).symm





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum
namespace OAI

/-! Sum each column in its own prime pool after fixing the common pattern code. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma columnReciprocalWeight_nonneg {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : 0 ≤ columnReciprocalWeight w := by
  unfold columnReciprocalWeight
  positivity

theorem same_column_patterns_reciprocal_sum {J R : ℕ} (P : Fin J → Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P)) (template : ColumnPrimeAssignment J R P)
    (hpattern : ∀ w ∈ F, ∀ j i k, w j i = w j k ↔ template j i = template j k) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤
      ∏ j, primeHarmonicMass (P j) ^ (univ.image (template j)).card := by
  let C (j : Fin J) := univ.image (template j)
  let rep (j : Fin J) (c : C j) : Fin R := Classical.choose (mem_image.mp c.property)
  have hrep (j : Fin J) (c : C j) : template j (rep j c) = c.val :=
    (Classical.choose_spec (mem_image.mp c.property)).2
  let classify (j : Fin J) (i : Fin R) : C j :=
    ⟨template j i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hconstant (w : ColumnPrimeAssignment J R P) (hw : w ∈ F) (j : Fin J) (i : Fin R) :
      w j i = w j (rep j (classify j i)) :=
    (hpattern w hw j i _).mpr (hrep j (classify j i)).symm
  let encode (w : ColumnPrimeAssignment J R P) : (j : Fin J) → C j → P j :=
    fun j c => w j (rep j c)
  have hinj : Set.InjOn encode F := by
    intro w hw v hv he
    funext j i
    exact (hconstant w hw j i).trans
      ((congrFun (congrFun he j) (classify j i)).trans (hconstant v hv j i).symm)
  have hweight (w : ColumnPrimeAssignment J R P) (hw : w ∈ F) :
      columnReciprocalWeight w = ∏ j, ∏ c : C j, ((encode w j c).val : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro j _
    have himage : univ.image (fun c : C j => w j (rep j c)) = univ.image (w j) := by
      ext p
      constructor
      · rintro hp
        obtain ⟨c, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨rep j c, mem_univ _, rfl⟩
      · rintro hp
        obtain ⟨i, _, rfl⟩ := mem_image.mp hp
        exact mem_image.mpr ⟨classify j i, mem_univ _, (hconstant w hw j i).symm⟩
    rw [← himage, prod_image]
    intro c _ d _ hcd
    apply Subtype.ext
    exact (hrep j c).symm.trans (((hpattern w hw j _ _).mp hcd).trans (hrep j d))
  calc
    _ = ∑ z ∈ F.image encode, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      rw [sum_image hinj]
      exact sum_congr rfl hweight
    _ ≤ ∑ z : (j : Fin J) → C j → P j, ∏ j, ∏ c : C j, ((z j c).val : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro z _ _
      positivity
    _ = ∏ j, ∑ z : C j → P j, ∏ c, ((z c).val : ℝ)⁻¹ := by rw [Fintype.prod_sum]
    _ = _ := by
      apply prod_congr rfl
      intro j _
      simpa only [Fintype.card_coe, C] using sum_reciprocal_assignments (ι := C j) (P j)

/-- A code covers the joint pattern, but the numerical prime sums retain
the separate harmonic mass of each column. There is no factor from the
number of columns in the base of the power. -/
theorem covered_column_patterns_reciprocal_sum {J R : ℕ} {Code : Type*} [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J R P))
    (decode : Code → Fin J → Fin R → Fin R → Bool) (A : ℝ) (M : ℕ)
    (hA : 1 ≤ A) (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hlabels : ∀ w ∈ F, (∑ j, (univ.image (w j)).card) ≤ M)
    (hcover : ∀ w ∈ F, ∃ c, ∀ j i k, decode c j i k = decide (w j i = w j k)) :
    (∑ w ∈ F, columnReciprocalWeight w) ≤ (Fintype.card Code : ℝ) * A ^ M := by
  let fiber (c : Code) := F.filter (fun w => ∀ j i k, decode c j i k = decide (w j i = w j k))
  have hsum : (∑ w ∈ F, columnReciprocalWeight w) ≤
      ∑ c, ∑ w ∈ fiber c, columnReciprocalWeight w := by
    calc
      _ ≤ ∑ w ∈ F, ∑ c, if ∀ j i k, decode c j i k = decide (w j i = w j k)
          then columnReciprocalWeight w else 0 := by
        apply sum_le_sum
        intro w hw
        obtain ⟨c, hc⟩ := hcover w hw
        exact le_trans (by simp only [if_pos hc]; exact le_rfl)
          (single_le_sum (s := (univ : Finset Code))
            (f := fun d => if ∀ j i k, decode d j i k = decide (w j i = w j k)
              then columnReciprocalWeight w else 0)
            (fun d _ => ite_nonneg (columnReciprocalWeight_nonneg w) le_rfl) (mem_univ c))
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : Code) : (∑ w ∈ fiber c, columnReciprocalWeight w) ≤ A ^ M := by
    by_cases he : (fiber c).Nonempty
    · obtain ⟨v, hv⟩ := he
      have hp : ∀ w ∈ fiber c, ∀ j i k, w j i = w j k ↔ v j i = v j k := by
        intro w hw j i k
        exact decide_eq_decide.mp (((mem_filter.mp hw).2 j i k).symm.trans
          ((mem_filter.mp hv).2 j i k))
      apply (same_column_patterns_reciprocal_sum P (fiber c) v hp).trans
      calc
        _ ≤ ∏ j, A ^ (univ.image (v j)).card := by
          apply Finset.prod_le_prod
          · intro j _
            exact pow_nonneg (by unfold primeHarmonicMass; positivity) _
          · intro j _
            exact pow_le_pow_left₀ (by unfold primeHarmonicMass; positivity) (hmass j) _
        _ = A ^ (∑ j, (univ.image (v j)).card) := prod_pow_eq_pow_sum _ _ _
        _ ≤ A ^ M := pow_le_pow_right₀ hA (hlabels v (mem_filter.mp hv).1)
    · simp only [not_nonempty_iff_eq_empty.mp he, sum_empty]
      positivity
  exact hsum.trans (by
    calc
      _ ≤ ∑ _c : Code, A ^ M := sum_le_sum (fun c _ => hfiber c)
      _ = _ := by simp)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodColumnSum
namespace OAI

/-! Sum the good column patterns with one reciprocal per observed prime. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

/-- Unused elements of the ambient label type make no contribution. -/
lemma twice_observed_labels_le_slots_add_singletons
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι] (label : τ → ι) :
    2 * (univ.image label).card ≤ Fintype.card τ + (singletonLabels label).card := by
  have hlocal (i : ι) :
      2 * (if 0 < (labelOccurrences label i).card then 1 else 0) ≤
        (labelOccurrences label i).card +
          (if (labelOccurrences label i).card = 1 then 1 else 0) := by
    split_ifs <;> omega
  have hs := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hlocal i)
  rw [← mul_sum, sum_add_distrib, total_label_occurrences] at hs
  have hused : (∑ i : ι, if 0 < (labelOccurrences label i).card then (1 : ℕ) else 0) =
      (univ.image label).card := by
    have hi (i : ι) : 0 < (labelOccurrences label i).card ↔ i ∈ univ.image label := by
      rw [card_pos]
      simp [labelOccurrences, filter_nonempty_iff, mem_image]
    simp only [hi]
    simp
  have hsingle : (∑ i : ι, if (labelOccurrences label i).card = 1 then (1 : ℕ) else 0) =
      (singletonLabels label).card := by simp [singletonLabels, sum_boole]
  rwa [hused, hsingle] at hs


lemma column_observed_count {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    2 * (∑ j, (univ.image (w j)).card) ≤ J * R + columnSingletonCount w := by
  have hs := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin J))) =>
    twice_observed_labels_le_slots_add_singletons (w j))
  simpa only [← mul_sum, sum_add_distrib, Fintype.card_fin, sum_const,
    card_univ, smul_eq_mul, columnSingletonCount] using hs

/-- At most `2*S` singleton labels leave at most `J*k+S` distinct primes
in a word with `2*k` occurrences per column. -/
lemma good_column_observed_count {J k S : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J (2 * k) P) (hs : columnSingletonCount w ≤ 2 * S) :
    (∑ j, (univ.image (w j)).card) ≤ J * k + S := by
  have h := column_observed_count w
  nlinarith



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.GoodWordWeightedSum
namespace OAI

/-! Sum padding only after fixing each complete column pattern. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma weighted_pair_sum_le {I Q : Type*} [DecidableEq I] [Fintype Q]
    (F : Finset (I × Q)) (b : I → ℝ) (weight : I → Q → ℝ) (K : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hw : ∀ i q, 0 ≤ weight i q)
    (hK : ∀ i, (∑ q, weight i q) ≤ K) :
    (∑ a ∈ F, b a.1 * weight a.1 a.2) ≤ K * ∑ i ∈ F.image Prod.fst, b i := by
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem Prod.fst ha)
    (fun a : I × Q => b a.1 * weight a.1 a.2), mul_sum]
  apply sum_le_sum
  intro i _
  let S := F.filter (fun a => a.1 = i)
  have hinj : Set.InjOn (Prod.snd : I × Q → Q) S := by
    intro a ha c hc he
    exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hc).2.symm) he
  calc
    _ = ∑ q ∈ S.image Prod.snd, b i * weight i q := by
      rw [sum_image hinj]
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ ≤ ∑ q : Q, b i * weight i q := by
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro q _ _
      exact mul_nonneg (hb i) (hw i q)
    _ = b i * ∑ q, weight i q := (mul_sum _ _ _).symm
    _ ≤ b i * K := mul_le_mul_of_nonneg_left (hK i) (hb i)
    _ = K * b i := mul_comm _ _

/-- The code may depend on the padding word. After fixing a code, sum
all padding choices for each prime assignment and use the uniform bound.
This avoids exchanging a prime-dependent cutoff with a supremum. -/
theorem covered_column_padding_sum {J R M : ℕ} {Q Code : Type*}
    [Fintype Q] [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J R P × Q))
    (decode : Code → Fin J → Fin R → Fin R → Bool)
    (weight : ColumnPrimeAssignment J R P → Q → ℝ) (A K : ℝ)
    (hA : 1 ≤ A) (hK : 0 ≤ K)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hw : ∀ w q, 0 ≤ weight w q) (hpad : ∀ w, (∑ q, weight w q) ≤ K)
    (hlabels : ∀ a ∈ F, (∑ j, (univ.image (a.1 j)).card) ≤ M)
    (hcover : ∀ a ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 * weight a.1 a.2) ≤
      (Fintype.card Code : ℝ) * K * A ^ M := by
  let fiber (c : Code) := F.filter (fun a =>
    ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l))
  have hsum : (∑ a ∈ F, columnReciprocalWeight a.1 * weight a.1 a.2) ≤
      ∑ c, ∑ a ∈ fiber c, columnReciprocalWeight a.1 * weight a.1 a.2 := by
    calc
      _ ≤ ∑ a ∈ F, ∑ c, if ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)
          then columnReciprocalWeight a.1 * weight a.1 a.2 else 0 := by
        apply sum_le_sum
        intro a ha
        obtain ⟨c, hc⟩ := hcover a ha
        have hs := single_le_sum (s := (univ : Finset Code))
          (f := fun d => if ∀ j i l, decode d j i l = decide (a.1 j i = a.1 j l)
            then columnReciprocalWeight a.1 * weight a.1 a.2 else 0)
          (fun d _ => ite_nonneg (mul_nonneg (columnReciprocalWeight_nonneg _) (hw _ _)) le_rfl)
          (mem_univ c)
        simpa only [if_pos hc] using hs
      _ = _ := by rw [sum_comm]; simp only [fiber, sum_filter]
  have hfiber (c : Code) :
      (∑ a ∈ fiber c, columnReciprocalWeight a.1 * weight a.1 a.2) ≤ K * A ^ M := by
    apply (weighted_pair_sum_le (fiber c) columnReciprocalWeight weight K
      columnReciprocalWeight_nonneg hw hpad).trans
    apply mul_le_mul_of_nonneg_left _ hK
    have hm : ∀ w ∈ (fiber c).image Prod.fst, (∑ j, (univ.image (w j)).card) ≤ M := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
      exact hlabels a (mem_filter.mp ha).1
    have hc : ∀ w ∈ (fiber c).image Prod.fst, ∃ _d : Unit,
        ∀ j i l, decode c j i l = decide (w j i = w j l) := by
      intro w hw
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hw
      exact ⟨(), (mem_filter.mp ha).2⟩
    simpa only [Fintype.card_unit, Nat.cast_one, one_mul] using
      covered_column_patterns_reciprocal_sum P ((fiber c).image Prod.fst)
        (fun (_ : Unit) => decode c) A M hA hmass hm hc
  exact hsum.trans (by
    calc
      _ ≤ ∑ _c : Code, K * A ^ M := sum_le_sum (fun c _ => hfiber c)
      _ = _ := by simp [mul_assoc])

/-- The good-word column count, with padding summed uniformly before the
remaining prime assignments. All actual admissibility restrictions can
remain in the finite set `F`. -/
theorem covered_good_column_padding_sum {J k S : ℕ} {Q Code : Type*}
    [Fintype Q] [Fintype Code]
    (P : Fin J → Finset ℕ) (F : Finset (ColumnPrimeAssignment J (2 * k) P × Q))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (weight : ColumnPrimeAssignment J (2 * k) P → Q → ℝ) (A K : ℝ)
    (hA : 1 ≤ A) (hK : 0 ≤ K) (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hw : ∀ w q, 0 ≤ weight w q) (hpad : ∀ w, (∑ q, weight w q) ≤ K)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hcover : ∀ a ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 * weight a.1 a.2) ≤
      (Fintype.card Code : ℝ) * K * A ^ (J * k + S) :=
  covered_column_padding_sum P F decode weight A K hA hK hmass hw hpad
    (fun a ha => good_column_observed_count a.1 (hsingle a ha)) hcover

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodRetainedWordSum
namespace OAI

/-! The good-word bound with the actual, normalized, retained padding weights. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma paddingWordWeight_nonneg (Q : Finset ℕ) (weight : ℕ → ℤ → ℕ → ℝ)
    (next : ℕ → ℤ → ℕ → ℤ) (hweight : ∀ i n q, 0 ≤ weight i n q)
    {m : ℕ} (i : ℕ) (n : ℤ) (q : Fin m → Q) :
    0 ≤ paddingWordWeight Q weight next i n q := by
  induction m generalizing i n with
  | zero => exact zero_le_one
  | succ m ih =>
      exact mul_nonneg (hweight _ _ _) (ih _ _ (Fin.tail q))


/-- The bound holds uniformly for prime-dependent eligibility, walk shifts,
and cutoffs, retaining the exact departure normalization at each step. -/
theorem good_retained_word_sum {J k S : ℕ} {Code : Type*} [Fintype Code]
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K A : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ) (n : ℤ)
    (hL : 0 < L) (hK : 0 ≤ K) (hA : 1 ≤ A) (hu : ∀ q, 0 ≤ u q)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hcover : ∀ a ∈ F, ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 *
      retainedColumnPaddingWeight Q u eligible g L K extra next n a.1 a.2) ≤
        (Fintype.card Code : ℝ) * K ^ (2 * k) * A ^ (J * k + S) := by
  apply covered_good_column_padding_sum P F decode
    (retainedColumnPaddingWeight Q u eligible g L K extra next n) A (K ^ (2 * k))
    hA (pow_nonneg hK _) hmass ?_ ?_ hsingle hcover
  · intro w q
    apply paddingWordWeight_nonneg
    intro i n q
    exact retainedPaddingAtom_nonneg Q u (eligible w i) g L K (extra w i) n q hL.le (hu q)
  · intro w
    exact retained_padding_word_sum_le Q u (eligible w) g L K (extra w) (next w)
      hL hK (fun q _ => hu q) (2 * k) 0 n


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodMomentConstant
namespace OAI

/-! Absorb the proved good-word costs into one absolute square-root mass constant. -/

namespace TwoPointCorrelations

open _root_.Filter

private lemma positive_nat_power_exp (x : ℝ) (hx : 0 < x) (n : ℕ) :
    x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- The threshold may depend on the fixed harmonic mass. The base
constant is absolute; the mass keeps its square-root exponent. -/
theorem eventually_good_moment_constant (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ J k S : ℕ,
      1 ≤ J → L / 2 ≤ (k : ℝ) → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * (2 * W) ^ (J * k + S) ≤
          (Real.exp 150 * Real.sqrt W) ^ (2 * k * J) := by
  let C := 2 * Real.log 2 + Real.log (2 * W)
  have hWp : 0 < W := by linarith
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
      (Real.log_nonneg (by linarith))
  have hgrow := (tendsto_rpow_atTop (show 0 < (3 / 4 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop (2 * C))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hgrow] with L hL hgrow
  intro J k S hJ hk hS
  have hJreal : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hkj : (k : ℝ) ≤ k * J := by nlinarith
  have hL2 : L ≤ 2 * (k : ℝ) := by linarith
  have hprod : L ^ (1 / 4 : ℝ) * L ^ (3 / 4 : ℝ) = L := by
    rw [← Real.rpow_add hL]
    norm_num
  have hCS : C * (S : ℝ) ≤ (k : ℝ) * J := by
    have hh := mul_le_mul_of_nonneg_left hgrow
      (Real.rpow_nonneg hL.le (1 / 4 : ℝ))
    rw [hprod] at hh
    have hs := mul_le_mul_of_nonneg_left hS hC
    nlinarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : Real.log (2 * W) = Real.log 2 + Real.log W :=
    Real.log_mul (by norm_num) hWp.ne'
  have hE : 108 * L + ((4 * k * J + 2 * S : ℕ) : ℝ) * Real.log 2 +
      64 * k * J + ((J * k + S : ℕ) : ℝ) * Real.log (2 * W) ≤
      ((J * k : ℕ) : ℝ) * (300 + Real.log W) := by
    push_cast
    dsimp [C] at hCS
    rw [hlog] at hCS ⊢
    have h2 := mul_le_mul_of_nonneg_right hlog2
      (show 0 ≤ 5 * (k : ℝ) * J by positivity)
    nlinarith
  have hsq : (Real.exp 150 * Real.sqrt W) ^ 2 = Real.exp 300 * W := by
    rw [mul_pow, Real.sq_sqrt hWp.le, ← Real.exp_nat_mul]
    norm_num
  calc
    _ = Real.exp (108 * L + ((4 * k * J + 2 * S : ℕ) : ℝ) * Real.log 2 +
        64 * k * J + ((J * k + S : ℕ) : ℝ) * Real.log (2 * W)) := by
      rw [positive_nat_power_exp 2 (by norm_num),
        positive_nat_power_exp (2 * W) (by positivity), ← Real.exp_add,
        ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (((J * k : ℕ) : ℝ) * (300 + Real.log W)) := Real.exp_le_exp.mpr hE
    _ = (Real.exp 300 * W) ^ (J * k) := by
      have he : Real.exp 300 * W = Real.exp (300 + Real.log W) := by
        rw [Real.exp_add, Real.exp_log hWp]
      rw [he, ← Real.exp_nat_mul]
    _ = (Real.exp 150 * Real.sqrt W) ^ (2 * (J * k)) := by
      exact ((pow_mul (Real.exp 150 * Real.sqrt W) 2 (J * k)).trans
        (congrArg (fun a : ℝ => a ^ (J * k)) hsq)).symm
    _ = _ := by congr 1; ring

/-- Restore the normalization factor from the padding sum. -/
theorem eventually_good_moment_with_padding (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ J k S : ℕ, ∀ K : ℝ,
      1 ≤ J → L / 2 ≤ (k : ℝ) → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) → 0 ≤ K →
      Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S) ≤
          (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_good_moment_constant W hW] with L hc
  intro J k S K hJ hk hS hK
  have hh := mul_le_mul_of_nonneg_right (hc J k S hJ hk hS) (pow_nonneg hK (2 * k))
  calc
    _ = (Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * (2 * W) ^ (J * k + S)) * K ^ (2 * k) := by ring
    _ ≤ (Real.exp 150 * Real.sqrt W) ^ (2 * k * J) * K ^ (2 * k) := hh
    _ = _ := by
      symm
      rw [mul_pow, ← pow_mul, show J * (2 * k) = 2 * k * J by ring, mul_comm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodTraceCost
namespace OAI

/-! Absorb the exact good designated-word cost, including all designations, into the moment base. -/

namespace TwoPointCorrelations

open _root_.Filter

theorem eventually_good_trace_cost (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J k S : ℕ) (K M : ℝ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L →
      (S : ℝ) ≤ L ^ (1 / 4 : ℝ) → 0 ≤ K →
      M ≤ (2 : ℝ) ^ (2 * S) *
        ((Fintype.card (BudgetColumnArrayCode J (4 * k) L) : ℝ) *
          K ^ (2 * k) * (2 * W) ^ (J * k + S)) →
      Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J) * M ≤
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_budget_column_array_card,
    eventually_good_moment_with_padding W hW] with L hL hcard hmoment
  intro J k S K M hJ hklo hkhi hS hK hM
  have hk : 1 ≤ k := by
    by_contra hn
    have hz : k = 0 := by omega
    subst k
    norm_num at hklo
    linarith
  have hc := hcard k J (4 * k) hklo hkhi (by omega) le_rfl
  have hb : M ≤ (2 : ℝ) ^ (2 * S) *
      (Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S)) := by
    apply hM.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hc (pow_nonneg hK _)
  calc
    _ ≤ Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J) *
        ((2 : ℝ) ^ (2 * S) *
          (Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S))) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.exp (108 * L) * (2 : ℝ) ^ (4 * k * J + 2 * S) *
        Real.exp (64 * k * J) * K ^ (2 * k) * (2 * W) ^ (J * k + S) := by
      rw [pow_add]
      ring
    _ ≤ _ := hmoment J k S K hJ hklo hS hK

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodWeightedDifferenceSum
namespace OAI

/-! Average the good-word forest estimate while retaining the exact padding normalization. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem good_weighted_difference_sum {α : Type*} [Fintype α]
    {J k S : ℕ} {Code : Type*} [Fintype Code]
    (μ : FiniteLaw α) (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
    (decode : Code → Fin J → Fin (2 * k) → Fin (2 * k) → Bool)
    (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K A T : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ) (origin : α → ℤ)
    (weight delta : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → α → ℝ)
    (hL : 0 < L) (hK : 0 ≤ K) (hA : 1 ≤ A) (hT : 0 ≤ T) (hu : ∀ q, 0 ≤ u q)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hpad : ∀ a ∈ F, ∀ x, weight a x ≤
      retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2)
    (hdelta : ∀ a ∈ F, ∀ x, |delta a x| ≤ T)
    (hcover : ∀ a ∈ F, ∀ x, weight a x ≠ 0 → delta a x ≠ 0 →
      ∃ c, ∀ j i l, decode c j i l = decide (a.1 j i = a.1 j l)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 *
      μ.average (fun x => weight a x * |delta a x|)) ≤
      T * ((Fintype.card Code : ℝ) * K ^ (2 * k) * A ^ (J * k + S)) := by
  have hpoint (x : α) :
      (∑ a ∈ F, columnReciprocalWeight a.1 * (weight a x * |delta a x|)) ≤
      T * ((Fintype.card Code : ℝ) * K ^ (2 * k) * A ^ (J * k + S)) := by
    let Fx := F.filter (fun a => weight a x ≠ 0 ∧ delta a x ≠ 0)
    have heq : (∑ a ∈ F, columnReciprocalWeight a.1 * (weight a x * |delta a x|)) =
        ∑ a ∈ Fx, columnReciprocalWeight a.1 * (weight a x * |delta a x|) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a _
      split_ifs with ha
      · rfl
      · rcases not_and_or.mp ha with hw | hd
        · simp only [not_not] at hw
          rw [hw, zero_mul, mul_zero]
        · simp only [not_not] at hd
          rw [hd, abs_zero, mul_zero, mul_zero]
    rw [heq]
    calc
      _ ≤ ∑ a ∈ Fx, T * (columnReciprocalWeight a.1 *
          retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) := by
        apply sum_le_sum
        intro a ha
        have haF := (mem_filter.mp ha).1
        have hb := mul_le_mul (hpad a haF x) (hdelta a haF x)
          (abs_nonneg _) (le_trans (hw a haF x) (hpad a haF x))
        calc
          _ ≤ columnReciprocalWeight a.1 *
              (retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2 * T) :=
            mul_le_mul_of_nonneg_left hb (columnReciprocalWeight_nonneg _)
          _ = _ := by ring
      _ = T * ∑ a ∈ Fx, columnReciprocalWeight a.1 *
          retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2 :=
        (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (good_retained_word_sum P Q Fx decode u eligible g L K A extra next (origin x)
          hL hK hA hu hmass (fun a ha => hsingle a (mem_filter.mp ha).1)
          (fun a ha => hcover a (mem_filter.mp ha).1 x
            (mem_filter.mp ha).2.1 (mem_filter.mp ha).2.2)) hT
  calc
    _ = μ.average (fun x => ∑ a ∈ F,
        columnReciprocalWeight a.1 * (weight a x * |delta a x|)) := by
      simp only [FiniteLaw.average, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ _ := (μ.average_mono hpoint).trans_eq (μ.average_const _)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedDensity
namespace OAI

/-! Density of the actual deleted event, with all finite catalog costs included. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace ProhibitedPrimeFamily

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)


lemma whole_squarefree (dq : ℕ × ℕ) (hdq : dq ∈ F.pairs) : Squarefree (dq.2 * dq.1) := by
  apply (Nat.squarefree_mul ?_).mpr
  · exact ⟨F.padding_squarefree _ hdq, F.tuple_squarefree _ hdq⟩
  · apply (Nat.disjoint_primeFactors (F.padding_squarefree _ hdq).ne_zero
      (F.tuple_squarefree _ hdq).ne_zero).mp
    exact F.disjoint.symm.mono (F.padding_pool _ hdq) (F.tuple_pool _ hdq)






end ProhibitedPrimeFamily

open _root_.Filter


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleOccurrences
namespace OAI

/-! Identify the singleton count and reciprocal weight of actual tuple slots. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma tupleSlotLabel_occurrences {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (j : Fin J) (p : P j) :
    (labelOccurrences (tupleSlotLabel w) ⟨j, p⟩).card = (labelOccurrences (w j) p).card := by
  have he : labelOccurrences (tupleSlotLabel w) ⟨j, p⟩ =
      (labelOccurrences (w j) p).image (fun i => (i, j)) := by
    ext t
    rcases t with ⟨i, l⟩
    by_cases hl : l = j
    · subst l
      simp [labelOccurrences, tupleSlotLabel]
    · have hn : tupleSlotLabel w (i, l) ≠ ⟨j, p⟩ := by
        intro h
        exact hl (congrArg Sigma.fst h)
      simp [labelOccurrences, hn, Ne.symm hl]
  rw [he, card_image_of_injective]
  exact fun a b h => congrArg Prod.fst h

lemma tupleSlotLabel_singletons {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) :
    (singletonLabels (tupleSlotLabel w)).card = columnSingletonCount w := by
  simp only [singletonLabels, card_filter, Fintype.sum_sigma,
    tupleSlotLabel_occurrences, columnSingletonCount]



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePerfectRows
namespace OAI

/-! The actual singleton and unlit slots determine the forest's perfect rows. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem perfectRows_lit {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (label : Fin R × Fin J → ι) (U : Finset (Fin R × Fin J))
    (i : Fin R) (hi : i ∈ perfectRows label U) (j : Fin J) :
    (i, j) ∈ nonsingletonSlots label \ U := by
  have hnot : (i, j) ∉ singletonSlots label ∪ U := by
    intro h
    exact (mem_compl.mp hi) (mem_image.mpr ⟨(i, j), h, rfl⟩)
  have hs : label (i, j) ∉ singletonLabels label := by
    intro h
    exact hnot (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hp : 0 < (labelOccurrences label (label (i, j))).card :=
    card_pos.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  refine mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
  · simp only [singletonLabels, nonsingletonLabels, mem_filter, mem_univ, true_and] at hs ⊢
    omega
  · exact fun hu => hnot (mem_union_right _ hu)

theorem perfectRows_imperfect_le {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (label : Fin R × Fin J → ι) (U : Finset (Fin R × Fin J)) (cut : Fin R) :
    imperfectColumnCount ((perfectRows label U).erase cut) ≤
      (singletonLabels label).card + U.card + 1 := by
  apply (imperfectColumnCount_erase_le _ _).trans
  apply Nat.add_le_add_right
  rw [imperfectColumnCount_eq_card_compl, perfectRows, compl_compl]
  exact (card_image_le.trans (card_union_le _ _)).trans_eq
    (congrArg (· + U.card) (singleton_slot_count label))

theorem tuple_perfectRows_imperfect_le {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (U : Finset (Fin R × Fin J)) (cut : Fin R) :
    imperfectColumnCount ((perfectRows (tupleSlotLabel w) U).erase cut) ≤
      columnSingletonCount w + U.card + 1 := by
  simpa only [tupleSlotLabel_singletons] using
    perfectRows_imperfect_le (tupleSlotLabel w) U cut

theorem eventually_tuple_perfectRows_budget :
    ∀ᶠ L : ℝ in Filter.atTop, ∀ (J R : ℕ) (P : Fin J → Finset ℕ)
      (w : ColumnPrimeAssignment J R P) (U : Finset (Fin R × Fin J)) (cut : Fin R),
      (columnSingletonCount w : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (U.card : ℝ) ≤ L ^ (1 / 50 : ℝ) →
      (imperfectColumnCount ((perfectRows (tupleSlotLabel w) U).erase cut) : ℝ) ≤
        2 * L ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_imperfect_with_cut_bound] with L hL
  intro J R P w U cut hS hU
  exact hL _ _ _ (tuple_perfectRows_imperfect_le w U cut) hS hU

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma columnTuple_primeFactors {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (columnTuple w i).primeFactors = univ.image (fun j => (w j i).val) := by
  exact familyTuple_primeFactors (fun _ p => p.val)
    (fun j p => hprime j _ p.property) (fun j => w j i)
    (selectedPrimeValues_injective (fun j => w j i) hdisjoint)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleWordPrimeSupport
namespace OAI

/-! Match the tuple/padding reciprocal factors to the full numerical word support. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mem_tuplePrimeSupport {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (p : ℕ) :
    p ∈ tuplePrimeSupport w ↔ ∃ j i, (w j i).val = p := by
  simp only [tuplePrimeSupport, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨j, q, ⟨i, rfl⟩, rfl⟩
    exact ⟨j, i, rfl⟩
  · rintro ⟨j, i, rfl⟩
    exact ⟨j, w j i, ⟨i, rfl⟩, rfl⟩

lemma tuplePrimeSupport_reciprocal {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    (∏ p ∈ tuplePrimeSupport w, (p : ℝ)⁻¹) = columnReciprocalWeight w := by
  unfold tuplePrimeSupport columnReciprocalWeight
  rw [prod_biUnion]
  · apply prod_congr rfl
    intro j _
    rw [prod_image]
    exact fun _ _ _ _ h => Subtype.ext h
  · intro j _ l _ hjl
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := mem_image.mp hp
    obtain ⟨b, _, hab⟩ := mem_image.mp hq
    exact disjoint_left.mp (hdisjoint j l (Ne.symm hjl)) a.property (hab ▸ b.property)




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference
namespace OAI

/-! Forcing lit nonsingletons commutes with singleton differences; padding stays outside them. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma witnessAvoidance_abs_le_one {ι A W : Type*} [Fintype W]
    (I : W → (ι → A) → Bool) (x : ι → A) : |witnessAvoidance I x| ≤ 1 := by
  unfold witnessAvoidance
  rw [abs_prod]
  calc
    _ ≤ ∏ _w : W, (1 : ℝ) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro w _
      cases hi : I w x <;> norm_num [hi]
    _ = _ := prod_const_one

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.SelectedGoodHybrid
namespace OAI

/-! A nonzero selected difference has one surviving hybrid, preserving all exterior weights. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma selected_difference_nonzero_hybrid {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (S : Finset ι) (a x : ι → A) (G : (ι → A) → ℝ)
    (hG : selectedMixedDifference S a G x ≠ 0) :
    ∃ y : ι → A, (∀ i, i ∉ S → y i = x i) ∧ G y ≠ 0 := by
  obtain ⟨T, hT⟩ := exists_forced_value_ne_zero (fun i : S => a i)
    (fun z : S → A => G (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
    (fun i : S => x i) hG
  refine ⟨joinCoordinates S (forceCoordinates T (fun i : S => a i) (fun i : S => x i))
    (fun i : {i // i ∉ S} => x i), ?_, hT⟩
  intro i hi
  simp only [joinCoordinates, hi, dite_false]

theorem selected_forced_nonzero_hybrid {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (S T M : Finset ι) (hS : S ⊆ M) (hT : T ⊆ M)
    (a b x : ι → A) (G weight : (ι → A) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ M → y i = z i) → weight y = weight z)
    (hG : selectedMixedDifference S a (fun y => G (forceCoordinates T b y)) x ≠ 0) :
    ∃ y : ι → A, (∀ i, i ∉ M → y i = x i) ∧
      (∀ i ∈ T, y i = b i) ∧ weight y = weight x ∧ G y ≠ 0 := by
  obtain ⟨z, hz, hGz⟩ := selected_difference_nonzero_hybrid S a x
    (fun y => G (forceCoordinates T b y)) hG
  have he : ∀ i, i ∉ M → forceCoordinates T b z i = x i := by
    intro i hi
    have hiT : i ∉ T := fun hit => hi (hT hit)
    have hiS : i ∉ S := fun his => hi (hS his)
    simpa only [forceCoordinates_apply, hiT, ite_false] using hz i hiS
  exact ⟨forceCoordinates T b z, he, (fun i hi => by simp only [forceCoordinates_apply, hi, ite_true]),
    hweight _ _ he, hGz⟩

theorem centered_word_nonzero_hybrid {ι τ A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (U : Finset τ)
    (G weight : (ι → A) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ univ.image label → y i = z i) → weight y = weight z)
    (hL : LitConsistent (nonsingletonSlots label \ U) label target)
    (hG : selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
      (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
        (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x ≠ 0) :
    ∃ y : ι → A, (∀ i, i ∉ univ.image label → y i = x i) ∧
      (∀ t ∈ nonsingletonSlots label \ U, y (label t) = target t) ∧
      weight y = weight x ∧ G y ≠ 0 := by
  have hS : singletonLabels label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, ht⟩ := singleton_occurrence_exists label ⟨i, hi⟩
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  have hT : (nonsingletonSlots label \ U).image label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, _, ht⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  obtain ⟨y, hy, hylit, hyw, hyG⟩ := selected_forced_nonzero_hybrid (singletonLabels label)
    ((nonsingletonSlots label \ U).image label) (univ.image label) hS hT
    (singletonTarget label target base) (litForcedTarget (nonsingletonSlots label \ U) label target base)
    x G weight hweight hG
  refine ⟨y, hy, ?_, hyw, hyG⟩
  intro t ht
  rw [hylit _ (mem_image.mpr ⟨t, ht, rfl⟩), litForcedTarget_at _ _ _ _ hL t ht]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.AmbientTupleLabels
namespace OAI

/-! Actual tuple slots have the same equality pattern in the ambient prime pool and column coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma columnPrimeValue_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun c : (j : Fin J) × P j => c.2.val) := by
  rintro ⟨j, p⟩ ⟨l, q⟩ hpq
  change p.val = q.val at hpq
  have hjl : j = l := by
    by_contra hne
    exact disjoint_left.mp (hdisjoint j l (Ne.symm hne)) p.property (hpq.symm ▸ q.property)
  subst l
  exact congrArg (Sigma.mk j) (Subtype.ext hpq)

lemma tuple_label_eq_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) (t u : Fin R × Fin J) :
    label t = label u ↔ tupleSlotLabel w t = tupleSlotLabel w u := by
  rw [← hinj.eq_iff, ← (columnPrimeValue_injective hdisjoint).eq_iff]
  change p (label t) = p (label u) ↔ (w t.2 t.1).val = (w u.2 u.1).val
  rw [show p (label t) = (w t.2 t.1).val from hlabel t.1 t.2,
    show p (label u) = (w u.2 u.1).val from hlabel u.1 u.2]

lemma tuple_label_singletonSlots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) :
    singletonSlots label = singletonSlots (tupleSlotLabel w) := by
  have he (t : Fin R × Fin J) : labelOccurrences label (label t) =
      labelOccurrences (tupleSlotLabel w) (tupleSlotLabel w t) := by
    ext u
    simp only [labelOccurrences, mem_filter, mem_univ, true_and]
    exact tuple_label_eq_iff w hdisjoint p hinj label hlabel u t
  ext t
  simp only [singletonSlots, singletonLabels, mem_filter, mem_univ, true_and, he]

lemma tuple_label_singleton_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) :
    (singletonLabels label).card = columnSingletonCount w := by
  calc
    _ = (singletonSlots label).card := (singleton_slot_count label).symm
    _ = (singletonSlots (tupleSlotLabel w)).card :=
      congrArg Finset.card (tuple_label_singletonSlots w hdisjoint p hinj label hlabel)
    _ = _ := (singleton_slot_count (tupleSlotLabel w)).trans (tupleSlotLabel_singletons w)

lemma tuple_label_perfectRows {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) (U : Finset (Fin R × Fin J)) :
    perfectRows label U = perfectRows (tupleSlotLabel w) U := by
  simp only [perfectRows, tuple_label_singletonSlots w hdisjoint p hinj label hlabel]

lemma tuple_label_reciprocal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) :
    (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) = columnReciprocalWeight w := by
  have he : (univ.image label).image p = tuplePrimeSupport w := by
    ext q
    simp only [mem_image, mem_univ, true_and, mem_tuplePrimeSupport]
    constructor
    · rintro ⟨i, ⟨t, rfl⟩, rfl⟩
      exact ⟨t.2, t.1, (hlabel t.1 t.2).symm⟩
    · rintro ⟨j, i, rfl⟩
      exact ⟨label (i, j), ⟨(i, j), rfl⟩, hlabel i j⟩
  rw [← tuplePrimeSupport_reciprocal w hdisjoint, ← he]
  exact (prod_image (g := p) (f := fun q : ℕ => (q : ℝ)⁻¹)
    (fun _ _ _ _ h => hinj h)).symm

theorem designatedReciprocal_le_tuple {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (p : ι → ℕ) (hinj : Function.Injective p) (hp : ∀ i, 0 < p i)
    (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val)
    (U : Finset (Fin R × Fin J)) (hU : U ⊆ nonsingletonSlots label) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label ≤
      columnReciprocalWeight w := by
  have hb := full_word_designated_reciprocal_bound label U hU p 1
    (by norm_num) (fun i => by exact_mod_cast hp i)
  rw [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Fin R × Fin J)) _ _] at hb
  simpa only [inv_one, one_pow, mul_one, tuple_label_reciprocal w hdisjoint p hinj label hlabel]
    using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedFamilyWitnesses
namespace OAI

/-! The literal minimal-word catalog discharges the numerical witness-family hypotheses. -/

namespace TwoPointCorrelations.ProhibitedPrimeFamily

open _root_.Finset
open scoped _root_.Classical

variable {h J M : ℕ} (F : ProhibitedPrimeFamily h J M)

lemma catalog_pairs (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : (t.tuple, t.padding) ∈ F.pairs :=
  c.property.1.2.2.1 t ht


lemma catalog_whole_squarefree (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : Squarefree (t.padding * t.tuple) :=
  F.whole_squarefree _ (F.catalog_pairs s c t ht)




end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.AttachedCatalogAvoidance
namespace OAI

/-! The attached minimal-word catalog is the actual vertex-deletion indicator. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma attachedResiduePositiveWord_iff {ι : Type*} (p : ι → ℕ) (h B : ℕ)
    (w : List SignedStep) (a n : ℤ) (x : ι → Fin B)
    (hn : ∀ i, (n : ZMod (p i)) = ((x i).val : ZMod (p i)))
    (hsq : ∀ t ∈ w, Squarefree (t.padding * t.tuple))
    (hcover : ∀ q ∈ wordDivisorPrimeSupport w, ∃ i, p i = q) :
    AttachedResiduePositiveWord p h w a B x ↔ PositiveWord h (n + a) w := by
  let r (i : ι) : ZMod (p i) := ((x i).val : ZMod (p i)) + (a : ZMod (p i))
  have hr : ∀ i, ((n + a : ℤ) : ZMod (p i)) = r i := by
    intro i
    simp only [Int.cast_add, hn, r]
  rw [← residuePositiveWord_iff p h w r (n + a) hr hsq hcover]
  constructor
  · intro ht k i hi
    change ((x i).val : ZMod (p i)) + (a : ZMod (p i)) = _
    rw [ht k i hi, Int.cast_add]
    ring
  · intro ht k i hi
    have he := ht k i hi
    change ((x i).val : ZMod (p i)) + (a : ZMod (p i)) = _ at he
    change ((x i).val : ZMod (p i)) = _
    rw [Int.cast_add]
    calc
      _ = (((x i).val : ZMod (p i)) + (a : ZMod (p i))) - a := by ring
      _ = _ := by rw [he]; ring


theorem attachedCatalogAvoidance_ne_zero_iff {h J M : ℕ}
    (F : ProhibitedPrimeFamily h J M) (s B D : ℕ) (main : List SignedStep)
    (hD : main.length ≤ D) (x : ↥(F.P ∪ F.Q) → Fin B) (n : ℤ)
    (hn : ∀ p : ↥(F.P ∪ F.Q), (n : ZMod p.val) = ((x p).val : ZMod p.val)) :
    attachedCatalogAvoidance F s B D main x ≠ 0 ↔
      ∀ v ≤ main.length, ¬ProhibitedSite h s (fun d q => (d, q) ∈ F.pairs)
        (n + wordDisplacement h (main.take v)) := by
  have htest (a : Fin (D + 1) × ProhibitedCatalog F.pairs h s) :
      AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
        (decodeStepWord a.2.val) (wordDisplacement h (main.take (min a.1.val main.length))) B x ↔
      PositiveWord h (n + wordDisplacement h (main.take (min a.1.val main.length)))
        (decodeStepWord a.2.val) := by
    apply attachedResiduePositiveWord_iff _ h B _ _ n x hn
    · exact F.catalog_whole_squarefree s a.2
    · intro q hq
      exact ⟨⟨q, F.support_subset s a.2 hq⟩, rfl⟩
  have hne : attachedCatalogAvoidance F s B D main x ≠ 0 ↔
      ∀ a : Fin (D + 1) × ProhibitedCatalog F.pairs h s,
        ¬PositiveWord h (n + wordDisplacement h (main.take (min a.1.val main.length)))
          (decodeStepWord a.2.val) := by
    unfold attachedCatalogAvoidance witnessAvoidance
    rw [prod_ne_zero_iff]
    constructor
    · intro hx a ha
      have hz := hx a (mem_univ a)
      have ht := (htest a).mpr ha
      simp [ht] at hz
    · intro hx a _
      have ht : ¬AttachedResiduePositiveWord (fun p : ↥(F.P ∪ F.Q) => p.val) h
          (decodeStepWord a.2.val)
          (wordDisplacement h (main.take (min a.1.val main.length))) B x :=
        fun hp => hx a ((htest a).mp hp)
      simp [ht]
  rw [hne]
  constructor
  · intro ha v hv ⟨w, hw, hm⟩
    obtain ⟨c, hc⟩ := stepWord_covered F.pairs s w hm.1.2.1 hm.1.2.2.1
    have hcm : MinimalWord (ForwardProhibited h s (fun d q => (d, q) ∈ F.pairs))
        (decodeStepWord c) := by rw [hc]; exact hm
    have hh := ha (⟨v, by omega⟩, ⟨c, hcm⟩)
    rw [min_eq_left hv, hc] at hh
    exact hh hw
  · intro ha a hw
    exact ha (min a.1.val main.length) (Nat.min_le_right _ _)
      ⟨decodeStepWord a.2.val, hw, a.2.property⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.GoodWordHybrid
namespace OAI

/-! A surviving weighted mixed difference supplies the exact integer word needed by the forest cover. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem good_word_integer_hybrid {h J M B s D m : ℕ}
    (data : ProhibitedPrimeFamily h J M) (step : Fin m → SignedStep)
    (hstep : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (hmD : m ≤ D)
    (label : Fin m × Fin J → ↥(data.P ∪ data.Q))
    (hlabels : ∀ i (p : ↥(data.P ∪ data.Q)), p.val ∈ (step i).tuple.primeFactors →
      ∃ j, label (i, j) = p)
    (U : Finset (Fin m × Fin J)) (base x : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ univ.image label → y i = z i) → weight y = weight z)
    (hpadding : ∀ y, weight y ≠ 0 → MainPaddingTests
      (fun p : ↥(data.P ∪ data.Q) => p.val) h B (List.ofFn step) y)
    (hx : weight x ≠ 0)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
        (wordDisplacement h ((List.ofFn step).take t.1.val))))
    (hnz : selectedMixedDifference (singletonLabels label)
      (singletonTarget label
        (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
          (wordDisplacement h ((List.ofFn step).take t.1.val))) base)
      (fun z => attachedCatalogAvoidance data s B D (List.ofFn step)
        (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label
            (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
              (wordDisplacement h ((List.ofFn step).take t.1.val))) base) z)) x ≠ 0) :
    ∃ n : ℤ,
      (∀ i ∈ perfectRows label U, (step i).divisor ∣
        n + wordDisplacement h ((List.ofFn step).take i.val)) ∧
      (∀ v ≤ m, ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
        (n + wordDisplacement h ((List.ofFn step).take v))) := by
  let main := List.ofFn step
  let target (t : Fin m × Fin J) := forcedResidue B (label t).val (data.prime _).pos
    (hB _ (label t).property) (wordDisplacement h (main.take t.1.val))
  obtain ⟨y, _hy, hylit, hyw, hyG⟩ := centered_word_nonzero_hybrid label target base x U
    (attachedCatalogAvoidance data s B D main) weight hweight hL hnz
  have hypad := hpadding y (fun hzero => hx (hyw.symm.trans hzero))
  let (p : ↥(data.P ∪ data.Q)) : NeZero p.val := ⟨(data.prime p).ne_zero⟩
  have hcop : Pairwise (fun p q : ↥(data.P ∪ data.Q) => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (data.prime p) (data.prime q)).mpr
      (fun he => hpq (Subtype.ext he))
  obtain ⟨n, hn⟩ := exists_common_integer_residue (fun p : ↥(data.P ∪ data.Q) => p.val)
    hcop (fun p => ((y p).val : ZMod p.val))
  refine ⟨n, ?_, ?_⟩
  · intro i hi
    have hsquare := data.whole_squarefree _ (hstep i)
    have htests : ∀ q ∈ ((step i).padding * (step i).tuple).primeFactors,
        (q : ℤ) ∣ n + wordDisplacement h (main.take i.val) := by
      intro q hq
      have hq' := hq
      rw [Nat.primeFactors_mul (data.padding_squarefree _ (hstep i)).ne_zero
        (data.tuple_squarefree _ (hstep i)).ne_zero, mem_union] at hq'
      have hqpool : q ∈ data.P ∪ data.Q := by
        rcases hq' with hpad | htup
        · exact mem_union_right _ (data.padding_pool _ (hstep i) hpad)
        · exact mem_union_left _ (data.tuple_pool _ (hstep i) htup)
      let c : ↥(data.P ∪ data.Q) := ⟨q, hqpool⟩
      apply (residue_offset_divisibility (((y c).val : ZMod c.val)) n
        (wordDisplacement h (main.take i.val)) (hn c)).mpr
      rcases hq' with hpad | htup
      · have hk : i.val < main.length := by simpa only [main, List.length_ofFn] using i.isLt
        have ht := hypad (⟨i.val, hk⟩ : Fin main.length) c
        have he : main.get ⟨i.val, hk⟩ = step i := by simp [main, List.get_eq_getElem]
        have hpad' : c.val ∈ (main.get ⟨i.val, hk⟩).padding.primeFactors := by
          simpa only [he] using hpad
        exact ht hpad'
      · obtain ⟨j, hj⟩ := hlabels i c htup
        have hyl := hylit (i, j) (perfectRows_lit label U i hi j)
        rw [hj] at hyl
        rw [hyl]
        dsimp [target]
        rw [hj]
        exact ZMod.natCast_zmod_val
          (-(wordDisplacement h (main.take i.val) : ZMod c.val))
    have hd := (squarefree_divisor_iff ((step i).padding * (step i).tuple) hsquare
      (n + wordDisplacement h (main.take i.val))).mpr htests
    simpa only [SignedStep.divisor, Nat.cast_mul] using hd
  · have hmainD : main.length ≤ D := by simpa only [main, List.length_ofFn] using hmD
    have havoid := (attachedCatalogAvoidance_ne_zero_iff data s B D main hmainD y n hn).mp hyG
    simpa only [main, List.length_ofFn] using havoid

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.GoodWordForest
namespace OAI

/-! The surviving actual mixed difference supplies the forest cover, including its arithmetic hypotheses. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma ProhibitedPrimeFamily.supplied_word_support {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (word : List SignedStep)
    (hpairs : ∀ a ∈ word, (a.tuple, a.padding) ∈ data.pairs)
    (p v : ℕ) (hp : TuplePrimeAt word p v) :
    ¬p ∣ h ∧ ∀ a ∈ word, ¬p ∣ a.padding := by
  obtain ⟨hpprime, t, ht, hpt⟩ := hp
  have htword := List.mem_of_getElem? ht
  have htpair := hpairs t htword
  have hpP : p ∈ data.P := data.tuple_pool _ htpair
    (hpprime.mem_primeFactors hpt (data.tuple_squarefree _ htpair).ne_zero)
  refine ⟨data.excluded p hpP, ?_⟩
  intro a ha hpa
  have hapair := hpairs a ha
  have hpQ : p ∈ data.Q := data.padding_pool _ hapair
    (hpprime.mem_primeFactors hpa (data.padding_squarefree _ hapair).ne_zero)
  exact disjoint_left.mp data.disjoint hpP hpQ

theorem good_word_column_cover {h J M B s D R r : ℕ}
    (data : ProhibitedPrimeFamily h J M) (P : Fin J → Finset ℕ)
    (w : ColumnPrimeAssignment J R P) (hR : 0 < R)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B) (hRD : R ≤ D)
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (U : Finset (Fin R × Fin J)) (base x : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ univ.image label → y i = z i) → weight y = weight z)
    (hpadding : ∀ y, weight y ≠ 0 → MainPaddingTests
      (fun p : ↥(data.P ∪ data.Q) => p.val) h B (columnTupleWord w forward padding) y)
    (hx : weight x ≠ 0)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
        (wordDisplacement h ((columnTupleWord w forward padding).take t.1.val))))
    (hnz : selectedMixedDifference (singletonLabels label)
      (singletonTarget label
        (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
          (wordDisplacement h ((columnTupleWord w forward padding).take t.1.val))) base)
      (fun z => attachedCatalogAvoidance data s B D (columnTupleWord w forward padding)
        (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label
            (fun t => forcedResidue B (label t).val (data.prime _).pos (hB _ (label t).property)
              (wordDisplacement h ((columnTupleWord w forward padding).take t.1.val))) base) z)) x ≠ 0)
    (hh : 0 < h) (hs : 0 < s) (cut : Fin R)
    (hleft : ((columnTupleWord w forward padding).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ((columnTupleWord w forward padding).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (L : ℝ) (hLone : 1 ≤ L) (hRL : (R : ℝ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : (imperfectColumnCount ((perfectRows label U).erase cut) : ℝ) ≤
      2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ j, ColumnLowRank (tupleColumnPattern w hR forward padding j)
      hR h (perfectRows label U) cut r) :
    ∃ code : BudgetColumnArrayCode J (2 * R) L,
      ∀ j i l, decodeBudgetColumnArray (show R ≤ 2 * R by omega) code j i l =
        decide (w j i = w j l) := by
  let step : Fin R → SignedStep := fun i => ⟨forward i, columnTuple w i, padding i⟩
  have hlabels : ∀ i (p : ↥(data.P ∪ data.Q)), p.val ∈ (step i).tuple.primeFactors →
      ∃ j, label (i, j) = p := by
    intro i p hp
    change p.val ∈ (columnTuple w i).primeFactors at hp
    rw [columnTuple_primeFactors w i hprime hdisjoint] at hp
    obtain ⟨j, _, hj⟩ := mem_image.mp hp
    exact ⟨j, Subtype.ext ((hlabel i j).trans hj)⟩
  obtain ⟨n, hn, havoid⟩ := good_word_integer_hybrid data step hpairs hB hRD label
    hlabels U base x weight hweight hpadding hx hL hnz
  have hpairword : ∀ a ∈ columnTupleWord w forward padding,
      (a.tuple, a.padding) ∈ data.pairs := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hpairs i
  apply tuple_column_array_cover P w hR forward padding hprime hdisjoint
    (supply := fun d q => (d, q) ∈ data.pairs) (x := n) hh hs
    (perfectRows label U) cut ?_ hpairword ?_ ?_ ?_ hleft hright
    (data.supplied_word_support _ hpairword) ?_ L hLone hRL hsL hrL hI hno
  · intro i hi
    simpa only [step, SignedStep.divisor, columnTupleWord] using hn i hi
  · intro a ha
    exact Nat.pos_of_ne_zero (data.padding_squarefree _ (hpairword a ha)).ne_zero
  · intro a ha
    exact data.tuple_squarefree _ (hpairword a ha)
  · intro a ha
    exact data.tuple_card _ (hpairword a ha)
  · intro y hy
    obtain ⟨a, b, hab, rfl⟩ := hy
    have ha : a.length ≤ R := by
      have hlen := congrArg List.length hab
      simp only [columnTupleWord, List.length_ofFn, List.length_append] at hlen
      omega
    have htake : (columnTupleWord w forward padding).take a.length = a := by
      rw [hab, List.take_left]
    have hv := havoid a.length ha
    change ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs)
      (n + wordDisplacement h ((columnTupleWord w forward padding).take a.length)) at hv
    rw [htake] at hv
    exact hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodDesignatedWordSum
namespace OAI

/-! The actual good designated-word sum: forced residues, literal deletions and retained padding weights. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma budgetColumnArray_cover_congr {n J N M : ℕ} {L : ℝ}
    (hn : n ≤ N) (hm : n ≤ M) (he : N = M)
    (pattern : Fin J → Fin n → Fin n → Bool)
    (hc : ∃ code : BudgetColumnArrayCode J N L,
      ∀ j i l, decodeBudgetColumnArray hn code j i l = pattern j i l) :
    ∃ code : BudgetColumnArrayCode J M L,
      ∀ j i l, decodeBudgetColumnArray hm code j i l = pattern j i l := by
  subst M
  exact hc



lemma prohibitedWordDifference_abs_le {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B) (U : Finset (Fin R × Fin J))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    |prohibitedWordDifference data hB s D word label base U x| ≤
      2 ^ (singletonLabels label).card := by
  apply selectedMixedDifference_bound
  intro y
  exact witnessAvoidance_abs_le_one _ _

theorem good_designated_word_sum {h J M B s D k S r : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (P : Fin J → Finset ℕ) (Q : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
    (hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hpairs : ∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs)
    (hRD : 2 * k ≤ D)
    (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
      Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val)
    (base : ↥(data.P ∪ data.Q) → Fin B) (U : Finset (Fin (2 * k) × Fin J))
    (hU : ∀ a ∈ F, U ⊆ nonsingletonSlots (label a))
    (hLit : ∀ a ∈ F, LitConsistent (nonsingletonSlots (label a) \ U) (label a)
      (tupleForcedTarget data hB (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a)))
    (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
      (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hweight : ∀ a ∈ F, ∀ y z, (∀ i, i ∉ univ.image (label a) → y i = z i) →
      weight a y = weight a z)
    (hpadding : ∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests
      (fun p : ↥(data.P ∪ data.Q) => p.val) h B
      (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x)
    (hh : 0 < h) (hs : 0 < s) (cut : Fin (2 * k))
    (hleft : ∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (hright : ∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
      (fun a b => a.tuple ≠ b.tuple))
    (L K A : ℝ) (hL : 1 ≤ L) (hRL : (2 * k : ℕ) ≤ 2 * L)
    (hsL : L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ))
    (hrL : (r : ℝ) ≤ L ^ (1 / 50 : ℝ))
    (hI : ∀ a ∈ F, (imperfectColumnCount ((perfectRows (label a) U).erase cut) : ℝ) ≤
      2 * L ^ (1 / 4 : ℝ))
    (hno : ∀ a ∈ F, ∀ j, ColumnLowRank
      (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
      hR h (perfectRows (label a) U) cut r)
    (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
    (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ)
    (hK : 0 ≤ K) (hA : 1 ≤ A) (hu : ∀ q, 0 ≤ u q)
    (hmass : ∀ j, primeHarmonicMass (P j) ≤ A)
    (hsingle : ∀ a ∈ F, columnSingletonCount a.1 ≤ 2 * S)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hpad : ∀ a ∈ F, ∀ x, weight a x ≤
      retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) :
    (∑ a ∈ F, designatedReciprocal (fun p : ↥(data.P ∪ data.Q) => p.val)
      (singletonLabels (label a)) (nonsingletonSlots (label a) \ U) U (label a) *
      (data.residueLaw B hB).average (fun x => weight a x *
        |prohibitedWordDifference data hB s D
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base U x|)) ≤
      (2 : ℝ) ^ (2 * S) * ((Fintype.card (BudgetColumnArrayCode J (4 * k) L) : ℝ) *
        K ^ (2 * k) * A ^ (J * k + S)) := by
  let delta a := prohibitedWordDifference data hB s D
    (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base U
  apply le_trans _ (good_weighted_difference_sum (data.residueLaw B hB) P Q F
    (decodeBudgetColumnArray (show 2 * k ≤ 4 * k by omega)) u eligible g L K A
    (2 ^ (2 * S)) extra next origin weight delta (by linarith) hK hA (by positivity)
    hu hmass hsingle hw hpad ?_ ?_)
  · apply sum_le_sum
    intro a ha
    exact mul_le_mul_of_nonneg_right
      (designatedReciprocal_le_tuple a.1 hdisjoint _ Subtype.val_injective
        (fun p => (data.prime p).pos) (label a) (hlabel a ha) U (hU a ha))
      ((data.residueLaw B hB).average_nonneg
        (fun x => mul_nonneg (hw a ha x) (abs_nonneg _)))
  · intro a ha x
    apply (prohibitedWordDifference_abs_le data hB s D _ _ base U x).trans
    apply pow_le_pow_right₀ (by norm_num)
    rw [tuple_label_singleton_count a.1 hdisjoint _ Subtype.val_injective _ (hlabel a ha)]
    exact hsingle a ha
  · intro a ha x hx hd
    apply budgetColumnArray_cover_congr (show 2 * k ≤ 2 * (2 * k) by omega)
      (show 2 * k ≤ 4 * k by omega) (show 2 * (2 * k) = 4 * k by omega)
      (fun j i l => decide (a.1 j i = a.1 j l))
    exact good_word_column_cover data P a.1 hR forward (fun i => (a.2 i).val)
      hprime hdisjoint (hpairs a ha) hB hRD (label a) (hlabel a ha) U base x
      (weight a) (hweight a ha) (hpadding a ha) hx (hLit a ha) hd hh hs cut
      (hleft a ha) (hright a ha) L hL hRL hsL hrL (hI a ha) (hno a ha)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceDesignationSlices
namespace OAI

/-! Exact finite reindexing of designated trace terms by their lit/unlit choice. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem prohibited_designation_sum_eq_slices {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (keep : α → Finset (Fin R × Fin J) → Prop) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (keep a),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) =
    ∑ U : Finset (Fin R × Fin J),
      ∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
        prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U := by
  symm
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  have hset : (univ : Finset (Finset (Fin R × Fin J))).filter
      (fun U => U ⊆ nonsingletonSlots (label a) ∧ keep a U) =
      (nonsingletonSlots (label a)).powerset.filter (keep a) := by
    ext U
    simp only [mem_filter, mem_univ, true_and, mem_powerset]
  rw [← sum_filter, hset, sum_filter]

theorem prohibited_designated_sum_eq_lit_filter {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ) (U : Finset (Fin R × Fin J)) :
    (∑ a ∈ F, prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) =
      ∑ a ∈ F.filter (fun a => LitConsistent (nonsingletonSlots (label a) \ U) (label a)
        (tupleForcedTarget data hB (word a) (label a))),
        designatedReciprocal (fun p : ↥(data.P ∪ data.Q) => p.val)
          (singletonLabels (label a)) (nonsingletonSlots (label a) \ U) U (label a) *
          (data.residueLaw B hB).average
            (fun x => weight a x * |prohibitedWordDifference data hB s D (word a) (label a) base U x|) := by
  simp only [prohibitedDesignatedTerm, sum_filter]

theorem prohibited_designation_sum_le {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (keep : α → Finset (Fin R × Fin J) → Prop) (A : ℝ)
    (hA : ∀ U : Finset (Fin R × Fin J),
      (∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
        prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ A) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (keep a),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤
        (2 : ℝ) ^ (R * J) * A := by
  calc
    _ = ∑ U : Finset (Fin R × Fin J),
        ∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U :=
      prohibited_designation_sum_eq_slices data hB s D F word label base weight keep
    _ ≤ ∑ _U : Finset (Fin R × Fin J), A := sum_le_sum (fun U _ => hA U)
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.GoodTraceTotal
namespace OAI

/-! All good designated terms, including the finite choice of designation, fit
inside the absolute square-root harmonic-mass moment bound. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_good_trace_total_oai (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M B s D k S : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
      (hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
      (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cut : Fin (2 * k))
      (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
      (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L → (S : ℝ) ≤ L ^ (1 / 4 : ℝ) →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      2 * k ≤ D → (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      (∀ a ∈ F, ∀ y z, (∀ i, i ∉ univ.image (label a) → y i = z i) → weight a y = weight a z) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      0 < h → 0 < s → L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      0 ≤ K → (∀ q, 0 ≤ u q) → (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ a ∈ F, columnSingletonCount a.1 ≤ S) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤
        retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) →
      Real.exp (108 * L) *
        (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ∀ j, ColumnLowRank
            (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
            hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
          prohibitedDesignatedTerm data hB s D
            (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) base (weight a) U) ≤
      (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_tuple_perfectRows_budget,
    eventually_good_trace_cost W hW] with L hL hbudget hcost
  intro h J M B s D k S data hB P Q F hR forward label base weight cut u eligible g K extra next origin
    hJ hklo hkhi hS hprime hdisjoint hpairs hRD hlabel hweight hpadding hh hs hsL
    hleft hright hK hu hmass hsingle hw hpad
  let word (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    columnTupleWord a.1 forward (fun i => (a.2 i).val)
  let keep (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
      (U : Finset (Fin (2 * k) × Fin J)) := U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ∀ j, ColumnLowRank
    (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
    hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊
  let A := (2 : ℝ) ^ (2 * S) * ((Fintype.card (BudgetColumnArrayCode J (4 * k) L) : ℝ) *
    K ^ (2 * k) * (2 * W) ^ (J * k + S))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hslice (U : Finset (Fin (2 * k) × Fin J)) :
      (∑ a ∈ F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U),
        prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ A := by
    let E := (F.filter (fun a => U ⊆ nonsingletonSlots (label a) ∧ keep a U)).filter
      (fun a => LitConsistent (nonsingletonSlots (label a) \ U) (label a)
        (tupleForcedTarget data hB (word a) (label a)))
    have hEF : E ⊆ F := (filter_subset _ _).trans (filter_subset _ _)
    rw [prohibited_designated_sum_eq_lit_filter]
    apply good_designated_word_sum data hB P Q E hR forward hprime hdisjoint
      (fun a ha => hpairs a (hEF ha)) hRD label (fun a ha => hlabel a (hEF ha)) base U
      (fun _ ha => (mem_filter.mp (mem_filter.mp ha).1).2.1)
      (fun _ ha => (mem_filter.mp ha).2) weight
      (fun a ha => hweight a (hEF ha)) (fun a ha => hpadding a (hEF ha)) hh hs cut
      (fun a ha => hleft a (hEF ha)) (fun a ha => hright a (hEF ha))
      L K (2 * W) hL (by exact_mod_cast (mul_le_mul_of_nonneg_left hkhi (by norm_num : (0 : ℝ) ≤ 2)))
      hsL (Nat.floor_le (Real.rpow_nonneg (by linarith) _)) ?_ ?_
      u eligible g extra next origin hK (by linarith) hu hmass
      (fun a ha => (hsingle a (hEF ha)).trans (by omega))
      (fun a ha => hw a (hEF ha)) (fun a ha => hpad a (hEF ha))
    · intro a ha
      rw [tuple_label_perfectRows a.1 hdisjoint _ Subtype.val_injective _ (hlabel a (hEF ha))]
      apply hbudget J (2 * k) P a.1 U cut
      · exact (show (columnSingletonCount a.1 : ℝ) ≤ S by exact_mod_cast hsingle a (hEF ha)).trans hS
      · exact (show (U.card : ℝ) ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ by
          exact_mod_cast (mem_filter.mp (mem_filter.mp ha).1).2.2.1).trans
          (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    · intro a ha
      exact (mem_filter.mp (mem_filter.mp ha).1).2.2.2
  have htotal := prohibited_designation_sum_le data hB s D F word label base weight keep A
    (by
      intro U
      convert (preTransparency := .instances) hslice U using 1
      apply sum_congr
      · ext a
        simp only [mem_filter]
      · intro a _
        rfl)
  have hexp : 2 * k * J ≤ 4 * k * J :=
    Nat.mul_le_mul_right J (Nat.mul_le_mul_right k (by decide : 2 ≤ 4))
  have htotal' := htotal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp) hA)
  convert (preTransparency := .instances) (mul_le_mul_of_nonneg_left htotal' (Real.exp_pos (108 * L)).le).trans
    (by simpa only [mul_assoc] using hcost J k S K A hJ hklo hkhi hS hK le_rfl) using 1
  congr 1
  apply sum_congr rfl
  intro a _
  apply sum_congr
  · ext U
    simp only [mem_filter, keep]
  · intro U _
    rfl

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.eventually_prohibited_good_trace_total_oai := @OAI.TwoPointCorrelations.eventually_prohibited_good_trace_total_oai
