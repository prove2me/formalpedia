-- Prove2me | solution 1 for OAI.TwoPointCorrelations.eventually_weighted_high_rank_words
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:06:28.069824+00:00
-- url     : https://prove2.me/submissions/96884c95-e888-4a27-932b-c3d8ea55efd4

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_high_rank_fixed_padding_sum

section
-- module Solutions.OAIChowla.Compat
/-!
Backports of a few Mathlib lemmas from Mathlib d13f23b (the openai/math pin) to
Mathlib 0df444a, with the same names and statements and Mathlib's own proofs.
-/

open _root_.Polynomial




namespace Finset


/-- Backport (Mathlib d13f23b), additive form of `prod_le_prod_of_injOn`. -/
theorem sum_le_sum_of_injOn {ι α N : Type*} [AddCommMonoid N] [PartialOrder N]
    [IsOrderedAddMonoid N] [DecidableEq α]
    {f : ι → N} {g : α → N} {s : Finset ι} {t : Finset α} (e : ι → α) (he : Set.InjOn e s)
    (ht : image e s ⊆ t) (h : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ a ∈ t, a ∉ image e s → 0 ≤ g a) :
    ∑ i ∈ s, f i ≤ ∑ a ∈ t, g a := by
  refine le_trans ?_ <| sum_le_sum_of_subset_of_nonneg ht hg
  rw [sum_image he]
  exact sum_le_sum h

end Finset

section LogSubst
open _root_.Real _root_.Set _root_.MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





end LogSubst

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteProbability
namespace OAI

/-!
# Finite weighted sampling for the random-prime rank argument

The prime labels in the rank argument have a nonuniform reciprocal law.
The corresponding finite-sum probability identities account for that law.
-/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn


namespace FiniteLaw

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]



lemma average_nonneg (μ : FiniteLaw α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ μ.average f := sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (hf x))

lemma average_mono (μ : FiniteLaw α) {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.average f ≤ μ.average g := sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))



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

open _root_.Finset hiding sum_le_sum_of_injOn

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





end FiniteLaw

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

open _root_.Finset hiding sum_le_sum_of_injOn

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PartialCentering
namespace OAI

/-! Exact singleton centering on selected coordinates of the complete residue sample. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn



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

open _root_.Finset hiding sum_le_sum_of_injOn

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






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.DesignationWeights
namespace OAI

/-! Group literal unlit factors and forced lit atoms into exact prime exponents. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn


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

open _root_.Finset hiding sum_le_sum_of_injOn
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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ObservedReciprocalBound
namespace OAI

/-! Extra-reciprocal estimates require the lower prime bound only on used tuple coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma designation_sdiff_decidable {τ : Type*} (d₁ d₂ : DecidableEq τ) (S U : Finset τ) :
    @SDiff.sdiff (Finset τ) (@Finset.instSDiff τ d₁) S U =
      @SDiff.sdiff (Finset τ) (@Finset.instSDiff τ d₂) S U := by
  have hd : d₁ = d₂ := Subsingleton.elim _ _
  cases hd
  rfl

theorem full_word_designated_reciprocal_bound_on_support {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (label : τ → ι) (U : Finset τ) (hU : U ⊆ nonsingletonSlots label)
    (p : ι → ℕ) (H : ℝ) (hH : 0 < H)
    (hp : ∀ i ∈ nonsingletonLabels label, H ≤ p i) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label ≤
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^
        (∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card) := by
  have he : designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label =
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) *
        ∏ i ∈ nonsingletonLabels label, (p i : ℝ)⁻¹ ^
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card := by
    simpa only [designationLit_unlit label U hU, designationLit_lit, designatedReciprocal] using
      observed_designation_reciprocal_factor label (designationLit U) (fun i => (p i : ℝ))
  rw [he, ← prod_pow_eq_pow_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.prod_le_prod
  · intro i _
    positivity
  · intro i hi
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hH (hp i hi)) _

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

open _root_.Finset hiding sum_le_sum_of_injOn










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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
namespace OAI

/-! Canonical occurrence representatives for the imperfect-position code. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn

variable {α : Type*} [DecidableEq α] {N : ℕ}




lemma columnRepresentative_mem (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    columnRepresentative label perfect i ∈ columnRepresentativeCandidates label perfect i :=
  min'_mem _ _

/-- A reference always carries the intended label. -/
theorem columnRepresentative_label (label : Fin N → α) (perfect : Finset (Fin N)) (i : Fin N) :
    label (columnRepresentative label perfect i) = label i := by
  have hm := columnRepresentative_mem label perfect i
  dsimp only [columnRepresentativeCandidates] at hm
  split_ifs at hm <;> exact (mem_filter.mp hm).2



theorem columnRepresentative_eq_iff (label : Fin N → α) (perfect : Finset (Fin N))
    (i j : Fin N) : columnRepresentative label perfect i = columnRepresentative label perfect j ↔
      label i = label j := by
  constructor
  · intro h
    exact (columnRepresentative_label label perfect i).symm.trans
      ((congrArg label h).trans (columnRepresentative_label label perfect j))
  · intro h
    have hc : columnRepresentativeCandidates label perfect i =
        columnRepresentativeCandidates label perfect j := by
      simp only [columnRepresentativeCandidates, h]
    unfold columnRepresentative
    simp only [hc]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting
namespace OAI

/-! Finite descriptions used by the reciprocal crude count. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical






theorem card_crudeWordCode (R N D : ℕ) :
    Fintype.card (CrudeWordCode R N D) = 2 ^ R * (N ^ N * (D ^ N * 2 ^ N)) := by
  simp only [CrudeWordCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]





lemma card_crudeWordCode_exp (R N D : ℕ) :
    (Fintype.card (CrudeWordCode R N D) : ℝ) ≤
      Real.exp (R * Real.log 2 + N * Real.log (N + 1) +
        N * Real.log (D + 1) + N * Real.log 2) := by
  have hp (n k : ℕ) : (n : ℝ) ^ k ≤ Real.exp ((k : ℝ) * Real.log (n + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < n + 1)]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) k
  have htwo (k : ℕ) : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [card_crudeWordCode]
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ R * (Real.exp ((N : ℝ) * Real.log (N + 1)) *
        (Real.exp ((N : ℝ) * Real.log (D + 1)) * 2 ^ N)) := by
      gcongr
      · exact hp N N
      · exact hp D N
    _ = _ := by rw [htwo, htwo, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotCode
namespace OAI

/-! A complete equality-pattern code for tuple and padding prime occurrences. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


namespace PrimeSlotData

variable {R N : ℕ}





lemma code_class_eq_iff (a : PrimeSlotData R N) (i j : Fin N) :
    a.code.2.1 i = a.code.2.1 j ↔ a.prime i = a.prime j :=
  columnRepresentative_eq_iff a.prime ∅ i j

lemma code_class_prime (a : PrimeSlotData R N) (i : Fin N) :
    a.prime (a.code.2.1 i) = a.prime i :=
  columnRepresentative_label a.prime ∅ i

end PrimeSlotData

namespace CrudeWordCode

variable {R N : ℕ}





lemma primeData_encode (a : PrimeSlotData R N) :
    a.code.primeData (fun c => a.prime c.val) = a := by
  cases a with
  | mk forward row isPadding prime =>
      unfold primeData PrimeSlotData.code
      congr 1
      funext i
      exact columnRepresentative_label prime ∅ i

lemma numericalWord_encode (a : PrimeSlotData R N) :
    a.code.numericalWord (fun c => a.prime c.val) = a.word := by
  exact congrArg PrimeSlotData.word (primeData_encode a)



end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeSlots
namespace OAI

/-! Actual prime factors give a complete bounded-slot code for a numerical word. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

variable {R : ℕ}






theorem actualPrimeSlot_card_le (w : Fin R → SignedStep) (J M : ℕ)
    (hJ : ∀ i, (w i).tuple.primeFactors.card ≤ J)
    (hM : ∀ i, (w i).padding.primeFactors.card ≤ M) :
    Fintype.card (ActualPrimeSlot w) ≤ R * (J + M) := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ i : Fin R, ((w i).tuple.primeFactors.card + (w i).padding.primeFactors.card) := by
      simp only [Fintype.card_sum, Fintype.card_coe]
    _ ≤ ∑ _i : Fin R, (J + M) := sum_le_sum (fun i _ => Nat.add_le_add (hJ i) (hM i))
    _ = _ := by simp



lemma actualSlot_factor (w : Fin R → SignedStep) (i : Fin R) (b : Bool)
    (ht : Squarefree (w i).tuple) (hq : Squarefree (w i).padding) :
    (∏ s : ActualPrimeSlot w,
      if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1) =
        if b then (w i).padding else (w i).tuple := by
  rw [Fintype.prod_sigma]
  rw [prod_eq_single i]
  · rw [Fintype.prod_sum_type]
    cases b
    · have hp := (Finset.prod_coe_sort (s := (w i).tuple.primeFactors)
        (f := fun p : ℕ => p)).trans (Nat.prod_primeFactors_of_squarefree ht)
      simpa [actualSlotKind, actualSlotPrime] using hp
    · have hp := (Finset.prod_coe_sort (s := (w i).padding.primeFactors)
        (f := fun p : ℕ => p)).trans (Nat.prod_primeFactors_of_squarefree hq)
      simpa [actualSlotKind, actualSlotPrime] using hp
  · intro j _ hji
    simp only [hji, false_and, ite_false, prod_const_one]
  · simp

lemma actualPrimeSlotData_factor (w : Fin R → SignedStep) (i : Fin R) (b : Bool)
    (ht : Squarefree (w i).tuple) (hq : Squarefree (w i).padding) :
    (actualPrimeSlotData w).factor i b = if b then (w i).padding else (w i).tuple := by
  have he := (actualPrimeSlotEquiv w).symm.prod_comp
    (fun s : ActualPrimeSlot w =>
      if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1)
  calc
    _ = ∏ s : ActualPrimeSlot w,
        if s.1 = i ∧ actualSlotKind w s = b then actualSlotPrime w s else 1 := by
      unfold PrimeSlotData.factor PrimeSlotData.slots
      rw [prod_filter]
      refine Eq.trans ?_ he
      apply prod_congr rfl
      intro j _
      dsimp only [actualPrimeSlotData]
      congr 1
    _ = _ := actualSlot_factor w i b ht hq

theorem actualPrimeSlotData_word (w : Fin R → SignedStep)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding) :
    (actualPrimeSlotData w).word = List.ofFn w := by
  unfold PrimeSlotData.word
  congr 1
  funext i
  rw [actualPrimeSlotData_factor w i false (ht i) (hq i),
    actualPrimeSlotData_factor w i true (ht i) (hq i)]
  cases he : w i
  simp [actualPrimeSlotData, he]


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

open _root_.Finset hiding sum_le_sum_of_injOn








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

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn


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

open _root_.Finset hiding sum_le_sum_of_injOn
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


lemma mem_wordDivisorPrimeSupport (w : List SignedStep) (p : ℕ) :
    p ∈ wordDivisorPrimeSupport w ↔
      ∃ k : Fin w.length, p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors := by
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset]
  exact List.exists_mem_iff_get







end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteSupportAverage
namespace OAI

/-! A bounded function pays the probability of its actual nonzero support. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

theorem FiniteLaw.average_abs_le_support {A : Type*} [Fintype A]
    (μ : FiniteLaw A) (f : A → ℝ) (E : A → Prop) (C : ℝ)
    (hf : ∀ x, |f x| ≤ C) (hsupport : ∀ x, f x ≠ 0 → E x) :
    μ.average (fun x => |f x|) ≤ C * μ.probability E := by
  calc
    _ ≤ μ.average (fun x => (if E x then 1 else 0) * C) := by
      apply μ.average_mono
      intro x
      by_cases hx : E x
      · simpa only [if_pos hx, one_mul] using hf x
      · have hz : f x = 0 := by by_contra hn; exact hx (hsupport x hn)
        simp only [hz, abs_zero, if_neg hx, zero_mul, le_refl]
    _ = C * μ.probability E := by rw [μ.average_mul_const]; exact mul_comm _ _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RankDecay
namespace OAI

/-! The high-rank square-root saving dominates the full crude counting cost. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma sqrt_pow_le_exp (β u : ℝ) (r : ℕ) (hβ : 0 ≤ β) (hbound : β ≤ Real.exp u) :
    Real.sqrt (β ^ r) ≤ Real.exp (u * r / 2) := by
  calc
    _ ≤ Real.sqrt ((Real.exp u) ^ r) :=
      Real.sqrt_le_sqrt (pow_le_pow_left₀ hβ hbound r)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_half]; congr 1; ring

/-- The logarithmic prime-divisor count contributes only its logarithm to
the exponent; the prime lower cutoff contributes the full negative term. -/
lemma reciprocal_rank_base_le (V H T D : ℝ) (M : ℕ)
    (hV : 1 ≤ V) (hH : Real.exp T ≤ H)
    (hM : 1 + (Nat.log 2 M : ℝ) ≤ Real.exp D) :
    (V * H)⁻¹ * (1 + (Nat.log 2 M : ℝ)) ≤ Real.exp (D - T) := by
  have hHp : 0 < H := (Real.exp_pos T).trans_le hH
  have hVH : Real.exp T ≤ V * H := by
    exact hH.trans (by nlinarith)
  have hi : (V * H)⁻¹ ≤ Real.exp (-T) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos T) hVH
  calc
    _ ≤ Real.exp (-T) * Real.exp D :=
      mul_le_mul hi hM (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Exponentially bounded integer coefficients have only linearly many
possible logarithmic prime-divisor slots. -/
lemma natLog_le_linear (M : ℕ) (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hM : (M : ℝ) ≤ Real.exp (A * L)) :
    (Nat.log 2 M : ℝ) ≤ A * L / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hzero : M = 0
  · simp only [hzero, Nat.log_zero_right, Nat.cast_zero]
    positivity
  have hMp : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hzero
  have hlog := Real.log_le_log hMp hM
  rw [Real.log_exp] at hlog
  apply (Real.natLog_le_logb M 2).trans
  exact div_le_div_of_nonneg_right hlog hlog2.le

lemma eventually_rank_log_budget (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ M : ℕ, (M : ℝ) ≤ Real.exp (A * L) →
      1 + (Nat.log 2 M : ℝ) ≤ Real.exp (2 * Real.log L) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_ge_atTop (1 + A / Real.log 2)] with L hL hlarge
  intro M hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := natLog_le_linear M A L hA (by linarith) hM
  have heq : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring, Real.exp_add,
      Real.exp_log (by linarith : 0 < L)]
    ring
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ L by linarith)
  have hA' : 0 ≤ A / Real.log 2 := div_nonneg hA hlog2.le
  have hlog' : (Nat.log 2 M : ℝ) ≤ (A / Real.log 2) * L := by
    convert (preTransparency := .instances) hlog using 1; ring
  nlinarith

/-- The actual coefficient bound `2 R h Q D B` is at most `exp (105 L)`
for the manuscript padding and other-column ranges. -/
lemma eventually_column_minor_size_exp (h : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ R Q D B : ℕ,
      (R : ℝ) ≤ 2 * L → (Q : ℝ) ≤ Real.exp (100 * L + 1) →
      (D : ℝ) ≤ Real.exp (2 * L) → (B : ℝ) ≤ Real.exp L →
      ((2 * R * (h * Q * D) * B : ℕ) : ℝ) ≤ Real.exp (105 * L) := by
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop (4 * h * Real.exp 1)] with L hL hlarge
  intro R Q D B hR hQ hD hB
  have hconst : 4 * h * Real.exp 1 ≤ Real.exp L := by
    linarith [Real.add_one_le_exp L]
  have hlinear : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc
    _ ≤ 2 * (2 * L) * ((h : ℝ) * Real.exp (100 * L + 1) * Real.exp (2 * L)) * Real.exp L := by
      push_cast
      gcongr
    _ = (4 * h * Real.exp 1) * L *
        (Real.exp (100 * L) * Real.exp (2 * L) * Real.exp L) := by
      rw [Real.exp_add]
      ring
    _ = (4 * h * Real.exp 1) * L * Real.exp (103 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp L * Real.exp L * Real.exp (103 * L) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

/-- Quantitative form of `log² L = o(L^(3/200))`, multiplied by `L`. -/
lemma eventually_crude_cost_small (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, C * L * (Real.log L) ^ 2 ≤ (1 / 8 : ℝ) * L ^ (203 / 200 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (s := (3 / 200 : ℝ)) (by norm_num)).bound
      (show 0 < (1 / 8 : ℝ) / (C + 1) by positivity)
  filter_upwards [eventually_ge_atTop 1, h] with L hL hh
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  rw [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hh
  have hscaled : C * (Real.log L) ^ 2 ≤ (1 / 8 : ℝ) * L ^ (3 / 200 : ℝ) := by
    calc
      _ ≤ (C + 1) * (Real.log L) ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
      _ ≤ (C + 1) * (((1 / 8 : ℝ) / (C + 1)) * L ^ (3 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [(show C + 1 ≠ 0 by linarith)]
  have hm := mul_le_mul_of_nonneg_right hscaled hLp.le
  have hp : L ^ (203 / 200 : ℝ) = L ^ (3 / 200 : ℝ) * L := by
    calc
      _ = L ^ ((3 / 200 : ℝ) + 1) := by norm_num
      _ = _ := by rw [Real.rpow_add hLp, Real.rpow_one]
  rw [hp]
  nlinarith

/-- The floor in `r = floor(L^(1/50))` loses at most half the rank once
`L` is large; its upper bound is only `L`, sufficient for every overhead. -/
lemma eventually_rank_floor_bounds :
    ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 50 : ℝ) / 2 ≤ (⌊L ^ (1 / 50 : ℝ)⌋₊ : ℝ) ∧
        (⌊L ^ (1 / 50 : ℝ)⌋₊ : ℝ) ≤ L := by
  have hr := (tendsto_rpow_atTop (show 0 < (1 / 50 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 1, hr] with L hL hr
  have hpos : 0 ≤ L ^ (1 / 50 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hfloor := Nat.lt_floor_add_one (L ^ (1 / 50 : ℝ))
  constructor
  · linarith
  · exact (Nat.floor_le hpos).trans (by
      simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 50 : ℝ) ≤ 1 by norm_num))

/-- The exact exponent `203/200 = 199/200 + 1/50` is retained. Fixed
coefficients in the crude enumeration only affect the threshold. -/
theorem eventually_high_rank_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℕ,
      L ^ (1 / 50 : ℝ) / 2 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      Real.exp (C * L * (Real.log L) ^ 2) *
        Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) ≤
          Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_crude_cost_small (2 * C) (by positivity)] with L hL hlog hsmall
  intro r hrlo hrhi
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hp : L ^ (1 / 50 : ℝ) * L ^ (199 / 200 : ℝ) = L ^ (203 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hnegative := mul_le_mul_of_nonneg_right hrlo
    (show 0 ≤ L ^ (199 / 200 : ℝ) by positivity)
  have hpositive := mul_le_mul_of_nonneg_left hrhi (show 0 ≤ C * Real.log L by positivity)
  have hlog : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hover := mul_le_mul_of_nonneg_left hlog (show 0 ≤ C * L by positivity)
  have hpositive' : C * Real.log L * r ≤ C * L * (Real.log L) ^ 2 := by
    calc
      _ ≤ C * Real.log L * L := hpositive
      _ = C * L * Real.log L := by ring
      _ ≤ _ := hover
  calc
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        Real.exp ((C * Real.log L - L ^ (199 / 200 : ℝ)) * r / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_pow_le_exp _ _ r (by positivity) le_rfl) (by positivity)
    _ = Real.exp (C * L * (Real.log L) ^ 2 +
        (C * Real.log L - L ^ (199 / 200 : ℝ)) * r / 2) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [div_mul_eq_mul_div, hp] at hnegative
      nlinarith [Real.rpow_nonneg hLp.le (203 / 200 : ℝ)]

/-- Numerical conclusion after summing the actual word records. The
coefficient of the counting exponent is fixed; it does not affect the
absolute decay exponent or constant. -/
theorem eventually_high_rank_total (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (r M : ℕ) (V H cost total : ℝ),
      L ^ (1 / 50 : ℝ) / 2 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      1 ≤ V → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      1 + (Nat.log 2 M : ℝ) ≤ Real.exp (C * Real.log L) →
      0 ≤ cost → cost ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      total ≤ cost * Real.sqrt (((V * H)⁻¹ * (1 + (Nat.log 2 M : ℝ))) ^ r) →
      total ≤ Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_high_rank_decay C hC] with L hL
  intro r M V H cost total hrlo hrhi hV hH hM hcost hcost' htotal
  have hbase := reciprocal_rank_base_le V H (L ^ (199 / 200 : ℝ))
    (C * Real.log L) M hV hH hM
  have hVp : 0 < V := lt_of_lt_of_le zero_lt_one hV
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hs : Real.sqrt (((V * H)⁻¹ * (1 + (Nat.log 2 M : ℝ))) ^ r) ≤
      Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) :=
    Real.sqrt_le_sqrt (pow_le_pow_left₀ (by positivity) hbase r)
  apply htotal.trans
  calc
    _ ≤ cost * Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) :=
      mul_le_mul_of_nonneg_left hs hcost
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        Real.sqrt ((Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r) :=
      mul_le_mul_of_nonneg_right hcost' (Real.sqrt_nonneg _)
    _ ≤ _ := hL r hrlo hrhi

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedWitnessProbability
namespace OAI

/-! A common hybrid pays one reciprocal for each new witness prime, without counting hybrids. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



theorem retained_witness_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n B h : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (word : Fin n → List SignedStep) (attachment : Fin n → ℤ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
      (RetainedWitnessTests p S h B word attachment) ≤
      ∏ i ∈ freshWitnessCoordinates p S word, (p i : ℝ)⁻¹ := by
  let E (i : ι) (v : Fin B) : Prop := i ∉ S →
    ∀ (j : Fin n) (k : Fin (word j).length),
      p i ∈ (((word j).get k).padding * ((word j).get k).tuple).primeFactors →
        (v.val : ZMod (p i)) =
          -((attachment j + wordDisplacement h ((word j).take k.val) : ℤ) : ZMod (p i))
  change (FiniteLaw.independent _).probability (fun x => ∀ i, E i (x i)) ≤ _
  rw [FiniteLaw.independent_probability_all]
  unfold freshWitnessCoordinates
  rw [prod_filter]
  apply Finset.prod_le_prod
  · intro i _
    exact FiniteLaw.probability_nonneg _ _
  · intro i _
    by_cases hi : i ∉ S ∧ ∃ j, p i ∈ wordDivisorPrimeSupport (word j)
    · rw [if_pos hi]
      obtain ⟨j, hj⟩ := hi.2
      obtain ⟨k, hk⟩ := (mem_wordDivisorPrimeSupport (word j) (p i)).mp hj
      exact ((uniformResidueLaw B (p i) (hp i) (hpB i)).probability_mono_of_imp
        (fun v hv => hv hi.1 j k hk)).trans_eq (uniformResidueLaw_mod_eq B (p i) (hp i) (hpB i) _)
    · rw [if_neg hi]
      exact FiniteLaw.probability_le_one _ _


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessReciprocalUnion
namespace OAI

/-! Main-word reciprocal factors and the retained new witness factors combine exactly. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma reciprocal_union_split {ι : Type*} [DecidableEq ι] (M W : Finset ι) (weight : ι → ℝ) :
    (∏ i ∈ M, weight i) * (∏ i ∈ W \ M, weight i) = ∏ i ∈ M ∪ W, weight i := by
  have hd : Disjoint M (W \ M) := by
    apply disjoint_left.mpr
    intro i hi hwi
    exact (mem_sdiff.mp hwi).2 hi
  rw [← prod_union hd]
  congr 1
  ext i
  simp only [mem_union, mem_sdiff]
  tauto

lemma freshWitnessCoordinates_eq_diff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (p : ι → ℕ) (S : Finset ι) (word : Fin n → List SignedStep) :
    freshWitnessCoordinates p S word =
      (univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (word j))) \ S := by
  ext i
  simp only [freshWitnessCoordinates, mem_filter, mem_univ, true_and, mem_sdiff]
  tauto

theorem main_witness_reciprocal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n : ℕ} (p : ι → ℕ) (S : Finset ι) (word : Fin n → List SignedStep) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
        (∏ i ∈ freshWitnessCoordinates p S word, (p i : ℝ)⁻¹) =
      ∏ i ∈ S ∪ univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (word j)),
        (p i : ℝ)⁻¹ := by
  rw [freshWitnessCoordinates_eq_diff]
  exact reciprocal_union_split _ _ _

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualSlotClasses
namespace OAI

/-! Actual squarefree prime occurrences satisfy the code's class conditions. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace PrimeSlotData

variable {R N : ℕ}

lemma code_value_injective (a : PrimeSlotData R N) :
    Function.Injective (fun z : a.code.usedClasses => a.prime z.val) := by
  intro z t h
  obtain ⟨i, _, hi⟩ := mem_image.mp z.property
  obtain ⟨j, _, hj⟩ := mem_image.mp t.property
  apply Subtype.ext
  rw [← hi, ← hj]
  apply (a.code_class_eq_iff i j).mpr
  have he : a.prime (a.code.2.1 i) = a.prime (a.code.2.1 j) := by
    simpa only [hi, hj] using h
  exact (a.code_class_prime i).symm.trans (he.trans
    (a.code_class_prime j))

lemma code_value_image (a : PrimeSlotData R N) :
    (univ.image (fun z : a.code.usedClasses => a.prime z.val)) = univ.image a.prime := by
  ext p
  constructor
  · rintro hp
    obtain ⟨z, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨z.val, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨a.code.classAt i, mem_univ _, a.code_class_prime i⟩

lemma code_kindConsistent (a : PrimeSlotData R N)
    (hk : ∀ i j, a.prime i = a.prime j → a.isPadding i = a.isPadding j) :
    a.code.KindConsistent := by
  intro j
  exact hk _ _ (a.code_class_prime j)

lemma code_rowInjective (a : PrimeSlotData R N)
    (hi : ∀ i j, a.row i = a.row j → a.isPadding i = a.isPadding j →
      a.prime i = a.prime j → i = j) : a.code.RowInjective := by
  intro r b i hi' j hj' he
  have hir := (mem_filter.mp hi').2
  have hjr := (mem_filter.mp hj').2
  exact hi i j (hir.1.trans hjr.1.symm) (hir.2.trans hjr.2.symm)
    ((a.code_class_eq_iff i j).mp he)

end PrimeSlotData

variable {R : ℕ}

lemma actualSlot_eq_of_data (w : Fin R → SignedStep) (s t : ActualPrimeSlot w)
    (hr : s.1 = t.1) (hk : actualSlotKind w s = actualSlotKind w t)
    (hp : actualSlotPrime w s = actualSlotPrime w t) : s = t := by
  rcases s with ⟨i, p | p⟩ <;> rcases t with ⟨j, q | q⟩ <;> cases hr
  · congr 2
    exact Subtype.ext hp
  · cases hk
  · cases hk
  · congr 2
    exact Subtype.ext hp

lemma actualSlot_kind_of_prime (w : Fin R → SignedStep)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (s t : ActualPrimeSlot w) (hp : actualSlotPrime w s = actualSlotPrime w t) :
    actualSlotKind w s = actualSlotKind w t := by
  rcases s with ⟨i, p | p⟩ <;> rcases t with ⟨j, q | q⟩
  · rfl
  · change p.val = q.val at hp
    exact False.elim ((disjoint_left.mp (hd i j)) p.property
      (by simpa only [hp] using q.property))
  · change p.val = q.val at hp
    exact False.elim ((disjoint_left.mp (hd j i)) q.property
      (by simpa only [← hp] using p.property))
  · rfl

theorem actualPrimeSlotData_code_kindConsistent (w : Fin R → SignedStep)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    (actualPrimeSlotData w).code.KindConsistent := by
  apply PrimeSlotData.code_kindConsistent
  intro i j hp
  exact actualSlot_kind_of_prime w hd _ _ hp

theorem actualPrimeSlotData_code_rowInjective (w : Fin R → SignedStep) :
    (actualPrimeSlotData w).code.RowInjective := by
  apply PrimeSlotData.code_rowInjective
  intro i j hr hk hp
  apply (actualPrimeSlotEquiv w).symm.injective
  exact actualSlot_eq_of_data w _ _ hr hk hp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualCodeAssignments
namespace OAI

/-! Actual code assignments preserve prime pools and the distinct-prime weight. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

variable {R : ℕ}

lemma actualSlotPrime_mem_tuplePool (w : Fin R → SignedStep) (P : Finset ℕ)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P) (s : ActualPrimeSlot w)
    (hs : actualSlotKind w s = false) : actualSlotPrime w s ∈ P := by
  rcases s with ⟨i, p | p⟩
  · exact hP i p.property
  · cases hs

lemma actualSlotPrime_mem_paddingPool (w : Fin R → SignedStep) (Q : Finset ℕ)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q) (s : ActualPrimeSlot w)
    (hs : actualSlotKind w s = true) : actualSlotPrime w s ∈ Q := by
  rcases s with ⟨i, p | p⟩
  · cases hs
  · exact hQ i p.property

lemma actualPrimeSlotData_prime_image (w : Fin R → SignedStep) :
    univ.image (actualPrimeSlotData w).prime = univ.image (actualSlotPrime w) := by
  ext p
  constructor
  · rintro hp
    obtain ⟨i, _, rfl⟩ := mem_image.mp hp
    exact mem_image.mpr ⟨(actualPrimeSlotEquiv w).symm i, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨s, _, rfl⟩ := mem_image.mp hp
    refine mem_image.mpr ⟨actualPrimeSlotEquiv w s, mem_univ _, ?_⟩
    change actualSlotPrime w ((actualPrimeSlotEquiv w).symm (actualPrimeSlotEquiv w s)) = _
    rw [Equiv.symm_apply_apply]

lemma actualPrimeSlot_support (w : Fin R → SignedStep)
    (ht : ∀ i, (w i).tuple ≠ 0) (hq : ∀ i, (w i).padding ≠ 0) :
    wordDivisorPrimeSupport (List.ofFn w) = univ.image (actualSlotPrime w) := by
  ext p
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    rw [Nat.primeFactors_mul (hq i) (ht i), mem_union] at hp
    rcases hp with hp | hp
    · exact mem_image.mpr ⟨⟨i, Sum.inr ⟨p, hp⟩⟩, mem_univ _, rfl⟩
    · exact mem_image.mpr ⟨⟨i, Sum.inl ⟨p, hp⟩⟩, mem_univ _, rfl⟩
  · rintro hp
    obtain ⟨⟨i, p | p⟩, _, rfl⟩ := mem_image.mp hp
    · refine ⟨w i, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inr p.property
    · refine ⟨w i, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inl p.property

/-- The encoded assignment pays exactly one reciprocal per distinct prime. -/
theorem actual_code_reciprocal_weight (w : Fin R → SignedStep)
    (ht : ∀ i, (w i).tuple ≠ 0) (hq : ∀ i, (w i).padding ≠ 0) :
    (∏ z : (actualPrimeSlotData w).code.usedClasses,
      ((actualPrimeSlotData w).prime z.val : ℝ)⁻¹) =
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  rw [actualPrimeSlot_support w ht hq, ← actualPrimeSlotData_prime_image]
  rw [← PrimeSlotData.code_value_image, prod_image]
  exact fun z _ t _ h => (actualPrimeSlotData w).code_value_injective h

/-- Actual tuple and padding classes inhabit their separate numerical pools. -/
theorem actual_code_pool_assignments (w : Fin R → SignedStep) (P Q : Finset ℕ)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q) :
    ∃ a : (actualPrimeSlotData w).code.tupleClasses → P,
      ∃ b : {z : (actualPrimeSlotData w).code.usedClasses //
        z ∉ (actualPrimeSlotData w).code.tupleClasses} → Q,
      joinCoordinates (actualPrimeSlotData w).code.tupleClasses
        (fun z => (a z).val) (fun z => (b z).val) =
          fun z => (actualPrimeSlotData w).prime z.val := by
  let c := (actualPrimeSlotData w).code
  have htuple (z : c.tupleClasses) : (actualPrimeSlotData w).prime z.val.val ∈ P := by
    apply actualSlotPrime_mem_tuplePool w P hP
      ((actualPrimeSlotEquiv w).symm z.val.val)
    exact (mem_filter.mp z.property).2
  have hpadding (z : {z : c.usedClasses // z ∉ c.tupleClasses}) :
      (actualPrimeSlotData w).prime z.val.val ∈ Q := by
    apply actualSlotPrime_mem_paddingPool w Q hQ
      ((actualPrimeSlotEquiv w).symm z.val.val)
    have hn : ¬c.2.2.2 z.val.val = false := by
      intro hz
      exact z.property (mem_filter.mpr ⟨mem_univ _, hz⟩)
    change c.2.2.2 z.val.val = true
    cases he : c.2.2.2 z.val.val <;> simp_all
  refine ⟨(fun z => ⟨_, htuple z⟩), (fun z => ⟨_, hpadding z⟩), ?_⟩
  funext z
  dsimp only [joinCoordinates]
  split_ifs <;> rfl

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

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma sum_reciprocal_assignments {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Finset ℕ) :
    (∑ x : ι → P, ∏ i, ((x i).val : ℝ)⁻¹) = primeHarmonicMass P ^ Fintype.card ι := by
  simpa only [prod_const, card_univ, primeHarmonicMass] using
    (Fintype.prod_sum (fun (_ : ι) (p : P) => (p.val : ℝ)⁻¹)).symm

/-- Splitting the class set preserves the original reciprocal product. -/
lemma reciprocal_product_join {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (a : S → ℕ) (b : {i // i ∉ S} → ℕ) :
    (∏ i, ((joinCoordinates S a b i : ℕ) : ℝ)⁻¹) =
      (∏ i : S, (a i : ℝ)⁻¹) * ∏ i : {i // i ∉ S}, (b i : ℝ)⁻¹ := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ S)]
  simp only [joinCoordinates_mem, joinCoordinates_notMem]
  have hinst : Subtype.fintype (fun i : ι => i ∈ S) = (inferInstance : Fintype S) :=
    Subsingleton.elim _ _
  rw [hinst]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BadCatalogCost
namespace OAI

/-!
# The cost of the complete short-word catalog

Numerical primes are summed by reciprocal weight, rather than counted as
additional symbols.  This leaves only signs, equality classes, row records,
and tuple/padding flags.  The bound includes every length and every slot
count up to the stated budgets, including invalid codes.
-/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace CrudeWordCode

variable {R N : ℕ}



lemma tuple_padding_class_count (c : CrudeWordCode R N R) :
    Fintype.card c.tupleClasses +
      Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} =
        Fintype.card c.usedClasses := by
  rw [Fintype.card_subtype_compl]
  exact Nat.add_sub_of_le (Fintype.card_subtype_le (fun z => z ∈ c.tupleClasses))

lemma class_count_le_slots (c : CrudeWordCode R N R) :
    Fintype.card c.tupleClasses +
      Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤ N := by
  rw [c.tuple_padding_class_count]
  simpa only [Fintype.card_fin] using
    (Fintype.card_subtype_le (fun z : Fin N => z ∈ c.usedClasses))

/-- Tuple and padding classes together use at most one reciprocal mass per slot. -/
lemma class_mass_le (c : CrudeWordCode R N R) {VP VQ A : ℝ}
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) (hPA : VP ≤ A) (hQA : VQ ≤ A)
    (hA : 1 ≤ A) :
    VP ^ Fintype.card c.tupleClasses *
      VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} ≤ A ^ N := by
  calc
    _ ≤ A ^ Fintype.card c.tupleClasses *
        A ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} :=
      mul_le_mul (pow_le_pow_left₀ hP hPA _) (pow_le_pow_left₀ hQ hQA _)
        (pow_nonneg hQ _) (pow_nonneg (zero_le_one.trans hA) _)
    _ = A ^ (Fintype.card c.tupleClasses +
        Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := (pow_add _ _ _).symm
    _ ≤ A ^ N := pow_le_pow_right₀ hA c.class_count_le_slots

end CrudeWordCode


lemma short_log_le_square (s : ℕ) (L : ℝ) (hs : 1 ≤ s)
    (hlog : 1 ≤ Real.log L) : Real.log L ≤ s * (Real.log L) ^ 2 := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hsr) (sq_nonneg (Real.log L))]

lemma short_polynomial_exp_bound (s k : ℕ) (L : ℝ) (hs : 1 ≤ s)
    (hL : 0 < L) (hlog : 1 ≤ Real.log L) :
    L ^ k ≤ Real.exp ((k : ℝ) * s * (Real.log L) ^ 2) := by
  calc
    _ = Real.exp ((k : ℝ) * Real.log L) := by
      rw [Real.exp_nat_mul, Real.exp_log hL]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (short_log_le_square s L hs hlog)
        (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      nlinarith

/-- Unlike the coarser pattern estimate, this bound does not need `R ≤ N`;
empty or invalid codes may therefore be retained in the catalog. -/
lemma short_crudeWordCode_bound (R N s : ℕ) (L C : ℝ)
    (hlog : 1 ≤ Real.log L) (hR : R ≤ s)
    (hslots : (N : ℝ) ≤ C * s * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hspoly : (s : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (CrudeWordCode R N R) : ℝ) ≤
      Real.exp ((1 + 5 * C) * s * (Real.log L) ^ 2) := by
  have hlog2 : Real.log 2 ≤ Real.log L := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have hr : (R : ℝ) ≤ s := by exact_mod_cast hR
    linarith
  have hlogR : Real.log ((R : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < R + 1) hRpoly
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have h1 : (R : ℝ) * Real.log 2 ≤ s * Real.log L :=
    mul_le_mul (by exact_mod_cast hR) hlog2
      (Real.log_nonneg (by norm_num)) (Nat.cast_nonneg _)
  have h2 := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h3 := mul_le_mul_of_nonneg_left hlogR (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h4 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have h5 := mul_le_mul_of_nonneg_right hslots (show 0 ≤ Real.log L by linarith)
  have h6 : (s : ℝ) * Real.log L ≤ s * (Real.log L) ^ 2 := by
    have hh : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
  apply (card_crudeWordCode_exp R N R).trans
  apply Real.exp_le_exp.mpr
  nlinarith




open _root_.Filter



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnHarmonicSum
namespace OAI

/-! Sum each column in its own prime pool after fixing the common pattern code. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



lemma columnReciprocalWeight_nonneg {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) : 0 ≤ columnReciprocalWeight w := by
  unfold columnReciprocalWeight
  positivity



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeColumnPatterns
namespace OAI

/-! Complete column equality patterns have only one representative index per slot. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical




lemma card_crudeColumnPatternCode (J R : ℕ) :
    Fintype.card (CrudeColumnPatternCode J R) = R ^ (R * J) := by
  simp only [CrudeColumnPatternCode, Fintype.card_fun, Fintype.card_fin, pow_mul]

theorem crude_column_pattern_count_bound (J R : ℕ) (L C : ℝ)
    (hL : 0 < L) (hJ : (J : ℝ) ≤ C * Real.log L)
    (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (CrudeColumnPatternCode J R) : ℝ) ≤
      Real.exp (2 * C * R * (Real.log L) ^ 2) := by
  have hlog : Real.log ((R : ℝ) + 1) ≤ 2 * Real.log L := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < R + 1) hR
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogL : 0 ≤ Real.log L := by
    have hp : (1 : ℝ) ≤ L ^ (2 : ℕ) := (by linarith : (1 : ℝ) ≤ R + 1).trans hR
    have hone : 1 ≤ L := by nlinarith
    exact Real.log_nonneg hone
  rw [card_crudeColumnPatternCode]
  push_cast
  calc
    _ ≤ ((R : ℝ) + 1) ^ (R * J) := pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = Real.exp (((R * J : ℕ) : ℝ) * Real.log ((R : ℝ) + 1)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < R + 1)]
    _ ≤ Real.exp (((R * J : ℕ) : ℝ) * (2 * Real.log L)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (by positivity))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 2 * R * Real.log L by positivity)
      push_cast
      nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeWordEncoding
namespace OAI

/-! A single finite universe covers all numerical words with bounded prime slots. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace PrimeWordEncoding

variable {R T : ℕ} {P Q : Finset ℕ}



lemma weight_nonneg (e : PrimeWordEncoding R T P Q) : 0 ≤ e.weight := by
  unfold weight
  exact prod_nonneg (fun _ _ => by positivity)

/-- No loss in the reciprocal weight occurs on encoding an actual word. -/
theorem covers (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    ∃ e : PrimeWordEncoding R T P Q, e.decode = List.ofFn w ∧
      e.2.1.KindConsistent ∧ e.2.1.RowInjective ∧
      Function.Injective (fun z => (e.2.2.1 z).val) ∧
      e.weight = ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹ := by
  obtain ⟨a, b, hab⟩ := actual_code_pool_assignments w P Q hP hQ
  let c := (actualPrimeSlotData w).code
  let e : PrimeWordEncoding R T P Q :=
    ⟨⟨Fintype.card (ActualPrimeSlot w), by omega⟩, c, a, b⟩
  refine ⟨e, ?_, actualPrimeSlotData_code_kindConsistent w hd,
    actualPrimeSlotData_code_rowInjective w, ?_, ?_⟩
  · change c.numericalWord (joinCoordinates c.tupleClasses
      (fun z => (a z).val) (fun z => (b z).val)) = _
    rw [hab, CrudeWordCode.numericalWord_encode]
    exact actualPrimeSlotData_word w ht hq
  · have ha (z : c.tupleClasses) : (a z).val = (actualPrimeSlotData w).prime z.val.val := by
      have hz := congrFun hab z.val
      simpa only [joinCoordinates_mem] using hz
    intro u v huv
    apply Subtype.ext
    apply (actualPrimeSlotData w).code_value_injective
    change (actualPrimeSlotData w).prime u.val.val = (actualPrimeSlotData w).prime v.val.val
    exact (ha u).symm.trans (huv.trans (ha v))
  · change (∏ z : c.usedClasses, ((joinCoordinates c.tupleClasses
      (fun z => (a z).val) (fun z => (b z).val) z : ℕ) : ℝ)⁻¹) = _
    rw [hab]
    exact actual_code_reciprocal_weight w (fun i => (ht i).ne_zero) (fun i => (hq i).ne_zero)

end PrimeWordEncoding

/-- A finite decoding cover also covers every nonnegative weighted sum.
The chosen representatives are injective because decoding recovers the word. -/
theorem finite_decoding_weight_bound {W C : Type*} [DecidableEq W] [Fintype C]
    (F : Finset W) (decode : C → W) (weight : W → ℝ) (cost : C → ℝ)
    (hcost : ∀ c, 0 ≤ cost c)
    (hcover : ∀ w ∈ F, ∃ c, decode c = w ∧ weight w ≤ cost c) :
    (∑ w ∈ F, weight w) ≤ ∑ c, cost c := by
  let choose (w : F) : C := Classical.choose (hcover w.val w.property)
  have hchoose (w : F) : decode (choose w) = w.val ∧ weight w.val ≤ cost (choose w) :=
    Classical.choose_spec (hcover w.val w.property)
  have hinj : Function.Injective choose := by
    intro u v h
    apply Subtype.ext
    exact (hchoose u).1.symm.trans ((congrArg decode h).trans (hchoose v).1)
  calc
    _ = ∑ w : F, weight w.val := (Finset.sum_coe_sort F weight).symm
    _ ≤ ∑ c, cost c := sum_le_sum_of_injOn choose
      (fun u _ v _ h => hinj h) (subset_univ _)
      (fun w _ => (hchoose w).2) (fun c _ _ => hcost c)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeNumericalWordSum
namespace OAI

/-! Complete reciprocal counting for actual numerical tuple and padding words. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma split_assignment_reciprocal_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (P Q : Finset ℕ) :
    (∑ a : S → P, ∑ b : {i // i ∉ S} → Q,
      ∏ i, ((joinCoordinates S (fun z => (a z).val) (fun z => (b z).val) i : ℕ) : ℝ)⁻¹) =
      primeHarmonicMass P ^ Fintype.card S *
        primeHarmonicMass Q ^ Fintype.card {i // i ∉ S} := by
  simp only [reciprocal_product_join]
  calc
    _ = (∑ a : S → P, ∏ i, ((a i).val : ℝ)⁻¹) *
        (∑ b : {i // i ∉ S} → Q, ∏ i, ((b i).val : ℝ)⁻¹) := by
      exact (sum_mul_sum _ _ _ _).symm
    _ = _ := by rw [sum_reciprocal_assignments, sum_reciprocal_assignments]

lemma primeWordEncoding_weight_sum (R T : ℕ) (P Q : Finset ℕ) :
    (∑ e : PrimeWordEncoding R T P Q, e.weight) =
      ∑ n : Fin (T + 1), ∑ c : CrudeWordCode R n.val R,
        primeHarmonicMass P ^ Fintype.card c.tupleClasses *
          primeHarmonicMass Q ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses} := by
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro n _
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type]
  change (∑ a : c.tupleClasses → P, ∑ b : {z : c.usedClasses // z ∉ c.tupleClasses} → Q,
    ∏ z : c.usedClasses,
      ((joinCoordinates c.tupleClasses (fun z => (a z).val) (fun z => (b z).val) z : ℕ) : ℝ)⁻¹) = _
  exact split_assignment_reciprocal_sum c.tupleClasses P Q

/-- Both prime supplies may be enlarged, but distinct abstract classes
continue to pay distinct reciprocal factors, including after collisions. -/
theorem primeWordEncoding_weight_le (R T : ℕ) (P Q : Finset ℕ) (U : ℝ)
    (hU : 1 ≤ U) (hP : primeHarmonicMass P ≤ U) (hQ : primeHarmonicMass Q ≤ U) :
    (∑ e : PrimeWordEncoding R T P Q, e.weight) ≤
      (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T := by
  rw [primeWordEncoding_weight_sum, sum_mul]
  apply sum_le_sum
  intro n _
  calc
    _ ≤ ∑ _c : CrudeWordCode R n.val R, U ^ T := by
      apply sum_le_sum
      intro c _
      exact (c.class_mass_le (by unfold primeHarmonicMass; positivity)
        (by unfold primeHarmonicMass; positivity) hP hQ hU).trans
        (pow_le_pow_right₀ hU (by omega))
    _ = _ := by simp

/-- A bound for the original numerical words, before any equality-pattern
or prime assignment is enlarged. This is the crude catalog estimate used
by the many-unlit and witness cases. -/
theorem numerical_word_reciprocal_sum_le (R T : ℕ) (P Q : Finset ℕ)
    (F : Finset (Fin R → SignedStep)) (weight : List SignedStep → ℝ) (W U : ℝ)
    (hW : 0 ≤ W) (hU : 1 ≤ U)
    (hP : primeHarmonicMass P ≤ U) (hQ : primeHarmonicMass Q ≤ U)
    (hweight : ∀ w ∈ F, weight (List.ofFn w) ≤ W)
    (hT : ∀ w ∈ F, Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ w ∈ F, ∀ i, Squarefree (w i).tuple)
    (hq : ∀ w ∈ F, ∀ i, Squarefree (w i).padding)
    (htP : ∀ w ∈ F, ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hqQ : ∀ w ∈ F, ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ w ∈ F, ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors) :
    (∑ w ∈ F, weight (List.ofFn w) *
      ∏ p ∈ wordDivisorPrimeSupport (List.ofFn w), (p : ℝ)⁻¹) ≤
      W * (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T := by
  let mass (w : List SignedStep) := ∏ p ∈ wordDivisorPrimeSupport w, (p : ℝ)⁻¹
  have hcover : ∀ w ∈ F.image List.ofFn, ∃ e : PrimeWordEncoding R T P Q,
      e.decode = w ∧ weight w * mass w ≤ W * e.weight := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hv
    obtain ⟨e, he, _, _, _, hmass⟩ := PrimeWordEncoding.covers w (hT w hw)
      (ht w hw) (hq w hw) (htP w hw) (hqQ w hw) (hd w hw)
    refine ⟨e, he, ?_⟩
    rw [hmass]
    exact mul_le_mul_of_nonneg_right (hweight w hw) (by dsimp [mass]; positivity)
  calc
    _ = ∑ w ∈ F.image List.ofFn, weight w * mass w := by
      rw [sum_image (fun _ _ _ _ he => List.ofFn_injective he)]
    _ ≤ ∑ e : PrimeWordEncoding R T P Q, W * e.weight :=
      finite_decoding_weight_bound (F.image List.ofFn) PrimeWordEncoding.decode
        (fun w => weight w * mass w) (fun e => W * e.weight)
        (fun e => mul_nonneg hW e.weight_nonneg) hcover
    _ = W * ∑ e : PrimeWordEncoding R T P Q, e.weight := (mul_sum _ _ _).symm
    _ ≤ W * ((∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T) :=
      mul_le_mul_of_nonneg_left (primeWordEncoding_weight_le R T P Q U hU hP hQ) hW
    _ = _ := by ring

/-- Explicit exponential form of the complete code and reciprocal cost. -/
theorem crude_numerical_cost_exp_bound (R T b : ℕ)
    (L C U : ℝ) (hR : 1 ≤ R) (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * R * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hU : 1 ≤ U) (hUP : U ≤ L ^ b) :
    (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ T ≤
      Real.exp ((3 + 5 * C + b * C) * R * (Real.log L) ^ 2) := by
  have hcode (n : Fin (T + 1)) :
      (Fintype.card (CrudeWordCode R n.val R) : ℝ) ≤
        Real.exp ((1 + 5 * C) * R * (Real.log L) ^ 2) := by
    have hn : n.val ≤ T := by omega
    have hnr : (n.val : ℝ) ≤ T := by exact_mod_cast hn
    exact short_crudeWordCode_bound R n.val R L C hlog le_rfl
      (hnr.trans hslots) (by linarith) hRpoly
  have hcount : (∑ n : Fin (T + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) ≤
      Real.exp ((3 + 5 * C) * R * (Real.log L) ^ 2) := by
    calc
      _ ≤ ((T : ℝ) + 1) * Real.exp ((1 + 5 * C) * R * (Real.log L) ^ 2) := by
        simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using
          (sum_le_sum (s := (univ : Finset (Fin (T + 1)))) (fun n _ => hcode n))
      _ ≤ Real.exp (2 * R * (Real.log L) ^ 2) *
          Real.exp ((1 + 5 * C) * R * (Real.log L) ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact hT.trans (by
          simpa using short_polynomial_exp_bound R 2 L hR hL hlog)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmass : U ^ T ≤ Real.exp ((b : ℝ) * C * R * (Real.log L) ^ 2) := by
    calc
      _ ≤ (L ^ b) ^ T := pow_le_pow_left₀ (by linarith) hUP _
      _ = Real.exp ((T : ℝ) * b * Real.log L) := by
        rw [← pow_mul, ← Real.exp_log hL, ← Real.exp_nat_mul, Real.log_exp]
        congr 1
        push_cast
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have ht := mul_le_mul_of_nonneg_right hslots
          (show 0 ≤ (b : ℝ) * Real.log L by positivity)
        nlinarith
  calc
    _ ≤ Real.exp ((3 + 5 * C) * R * (Real.log L) ^ 2) *
        Real.exp ((b : ℝ) * C * R * (Real.log L) ^ 2) :=
      mul_le_mul hcount hmass (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingCatalog
namespace OAI

/-! The padding catalog also pays only one reciprocal per distinct prime. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma paddingOnlyWord_injective (R : ℕ) :
    Function.Injective (paddingOnlyWord (R := R)) := by
  intro q r h
  funext i
  exact congrArg SignedStep.padding (congrFun h i)

lemma paddingOnlyWord_support {R : ℕ} (q : Fin R → ℕ) :
    wordDivisorPrimeSupport (List.ofFn (paddingOnlyWord q)) = paddingPrimeSupport q := by
  ext p
  simp only [wordDivisorPrimeSupport, List.mem_toFinset, List.mem_ofFn, mem_biUnion,
    paddingPrimeSupport, mem_univ, true_and, paddingOnlyWord]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    refine ⟨i, ?_⟩
    change p ∈ (q i * 1).primeFactors at hp
    simpa only [mul_one] using hp
  · rintro ⟨i, hp⟩
    refine ⟨⟨false, 1, q i⟩, ⟨i, rfl⟩, ?_⟩
    change p ∈ (q i * 1).primeFactors
    simpa only [mul_one] using hp

theorem padding_catalog_reciprocal_sum (R M : ℕ) (Q : Finset ℕ)
    (F : Finset (Fin R → ℕ)) (U : ℝ) (hU : 1 ≤ U)
    (hQ : primeHarmonicMass Q ≤ U)
    (hsq : ∀ q ∈ F, ∀ i, Squarefree (q i))
    (hpool : ∀ q ∈ F, ∀ i, (q i).primeFactors ⊆ Q)
    (hcount : ∀ q ∈ F, ∀ i, (q i).primeFactors.card ≤ M) :
    (∑ q ∈ F, ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹) ≤
      (∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ (R * M) := by
  have hc : ∀ v ∈ F.image paddingOnlyWord,
      Fintype.card (ActualPrimeSlot v) ≤ R * M := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
    simpa only [zero_add] using actualPrimeSlot_card_le (paddingOnlyWord q) 0 M
      (by intro i; simp [paddingOnlyWord]) (hcount q hq)
  have hb := numerical_word_reciprocal_sum_le R (R * M) ∅ Q
    (F.image paddingOnlyWord) (fun _ => 1) 1 U (by norm_num) hU
    (by simpa [primeHarmonicMass] using zero_le_one.trans hU) hQ
    (by intros; exact le_rfl) hc
    (by intro v hv i; obtain ⟨q, _, rfl⟩ := mem_image.mp hv; simp [paddingOnlyWord])
    (by intro v hv i; obtain ⟨q, hq, rfl⟩ := mem_image.mp hv; exact hsq q hq i)
    (by intro v hv i; obtain ⟨q, _, rfl⟩ := mem_image.mp hv; simp [paddingOnlyWord])
    (by intro v hv i; obtain ⟨q, hq, rfl⟩ := mem_image.mp hv; exact hpool q hq i)
    (by intro v hv i j; obtain ⟨q, _, rfl⟩ := mem_image.mp hv; simp [paddingOnlyWord])
  rw [sum_image (fun q _ r _ he => paddingOnlyWord_injective R he)] at hb
  simpa only [one_mul, paddingOnlyWord_support] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TuplePrimeArithmetic
namespace OAI

/-! Disjoint prime pools give the actual tuple factorization and unique tuple labels. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankPaddingSum
namespace OAI

/-! Sum actual squarefree padding after the full high-rank column estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma weighted_pair_second_fiber_sum_le {I Q : Type*} [DecidableEq I] [DecidableEq Q]
    (F : Finset (I × Q)) (b : Q → ℝ) (c : I → ℝ) (K : ℝ)
    (hb : ∀ q, 0 ≤ b q)
    (hfiber : ∀ q ∈ F.image Prod.snd,
      (∑ i ∈ (F.filter (fun a => a.2 = q)).image Prod.fst, c i) ≤ K) :
    (∑ a ∈ F, c a.1 * b a.2) ≤ K * ∑ q ∈ F.image Prod.snd, b q := by
  rw [← sum_fiberwise_of_maps_to (fun a ha => mem_image_of_mem Prod.snd ha)
    (fun a : I × Q => c a.1 * b a.2), mul_sum]
  apply sum_le_sum
  intro q hq
  let S := F.filter (fun a => a.2 = q)
  have hinj : Set.InjOn (Prod.fst : I × Q → I) S := by
    intro a ha d hd he
    exact Prod.ext he ((mem_filter.mp ha).2.trans (mem_filter.mp hd).2.symm)
  calc
    _ = (∑ i ∈ S.image Prod.fst, c i) * b q := by
      rw [sum_mul, sum_image hinj]
      apply sum_congr rfl
      intro a ha
      rw [(mem_filter.mp ha).2]
    _ ≤ K * b q := mul_le_mul_of_nonneg_right (hfiber q hq) (hb q)

/-- A complete reciprocal sum over numerical columns and numerical
padding values. All pattern and padding catalogs are supplied by proved
encodings, and the lit conditions are those of the original words. -/
theorem high_rank_column_padding_sum {J R : ℕ} (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
    (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (hR : 0 < R) (forward : Fin R → Bool) (j : Fin J)
    (h Q D B H r M : ℕ) (U : ℝ) (hU : 1 ≤ U)
    (hP : ∀ p ∈ P j, p.Prime) (hV : 0 < primeHarmonicMass (P j))
    (hmass : ∀ l, primeHarmonicMass (P l) ≤ U) (hQmass : primeHarmonicMass Qp ≤ U)
    (hH : 0 < H) (hlo : ∀ p ∈ P j, H ≤ p) (hbound : ∀ p ∈ P j, p ≤ B)
    (hq : ∀ a ∈ F, ∀ i, a.2 i ≤ Q)
    (hd : ∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D)
    (hsq : ∀ a ∈ F, ∀ i, Squarefree (a.2 i))
    (hpool : ∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp)
    (hcount : ∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M)
    (perfect : Finset (Fin R)) (cut : Fin R)
    (hrank : ∀ a ∈ F,
      ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j) hR h perfect cut r)
    (base : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
    (hlit : ∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ base a.1 a.2 +
      wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) :
    (∑ a ∈ F, columnReciprocalWeight a.1 *
      ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) ≤
      ((Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
        Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
          (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)) *
      ((∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) * U ^ (R * M)) := by
  let K := (Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J) *
    Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
      (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfiber (q : Fin R → ℕ) (hqF : q ∈ F.image Prod.snd) :
      (∑ w ∈ (F.filter (fun a => a.2 = q)).image Prod.fst, columnReciprocalWeight w) ≤ K := by
    let G := (F.filter (fun a => a.2 = q)).image Prod.fst
    have hmem (w : ColumnPrimeAssignment J R P) (hw : w ∈ G) : (w, q) ∈ F := by
      obtain ⟨a, ha, haw⟩ := mem_image.mp hw
      have he : a = (w, q) := Prod.ext haw (mem_filter.mp ha).2
      exact he ▸ (mem_filter.mp ha).1
    obtain ⟨a, ha, haq⟩ := mem_image.mp hqF
    have hq' : ∀ i, q i ≤ Q := by simpa only [haq] using hq a ha
    exact high_rank_fixed_padding_sum P G hR forward q j h Q D B H r U hU
      hP hV hmass hH hlo hbound hq'
      (fun w hw => hd (w, q) (hmem w hw)) perfect cut
      (fun w hw => hrank (w, q) (hmem w hw)) (fun w => base w q)
      (fun w hw => hlit (w, q) (hmem w hw))
  have hpad := padding_catalog_reciprocal_sum R M Qp (F.image Prod.snd) U hU hQmass
    (by intro q hqF; obtain ⟨a, ha, rfl⟩ := mem_image.mp hqF; exact hsq a ha)
    (by intro q hqF; obtain ⟨a, ha, rfl⟩ := mem_image.mp hqF; exact hpool a ha)
    (by intro q hqF; obtain ⟨a, ha, rfl⟩ := mem_image.mp hqF; exact hcount a ha)
  have hb := weighted_pair_second_fiber_sum_le F
    (fun q => ∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹)
    columnReciprocalWeight K (fun _ => by positivity) hfiber
  exact hb.trans (mul_le_mul_of_nonneg_left hpad hK)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankCatalogCost
namespace OAI

/-! Explicit cost of every column pattern and every squarefree padding word. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem column_padding_catalog_cost_exp_bound (J R M : ℕ) (L Cj Cm U : ℝ)
    (hR : 1 ≤ R) (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hJ : (J : ℝ) ≤ Cj * Real.log L) (hM : (M : ℝ) ≤ Cm * Real.log L)
    (hT : ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hRpoly : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hU : 1 ≤ U) (hUP : U ≤ L ^ (2 : ℕ)) :
    ((Fintype.card (CrudeColumnPatternCode J R) : ℝ) * U ^ (R * J)) *
      ((∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) *
        U ^ (R * M)) ≤
      Real.exp ((3 + 7 * Cm + 4 * Cj) * R * (Real.log L) ^ 2) := by
  have hc := crude_column_pattern_count_bound J R L Cj hL hJ hRpoly
  have hp : U ^ (R * J) ≤ Real.exp (2 * Cj * R * (Real.log L) ^ 2) := by
    calc
      _ ≤ (L ^ (2 : ℕ)) ^ (R * J) := pow_le_pow_left₀ (by linarith) hUP _
      _ = Real.exp (((R * J : ℕ) : ℝ) * (2 * Real.log L)) := by
        rw [Real.exp_nat_mul]
        congr 1
        rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
          Real.exp_add, Real.exp_log hL]
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_left hJ
          (show 0 ≤ 2 * R * Real.log L by positivity)
        push_cast
        nlinarith
  have hslots : ((R * M : ℕ) : ℝ) ≤ Cm * R * Real.log L := by
    have hm := mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    push_cast
    nlinarith
  have hpad := crude_numerical_cost_exp_bound R (R * M) 2 L Cm U hR hL hlog
    hslots hT hRpoly hU hUP
  calc
    _ ≤ (Real.exp (2 * Cj * R * (Real.log L) ^ 2) *
        Real.exp (2 * Cj * R * (Real.log L) ^ 2)) *
        Real.exp ((3 + 5 * Cm + 2 * Cm) * R * (Real.log L) ^ 2) := by
      exact mul_le_mul (mul_le_mul hc hp (by positivity) (Real.exp_pos _).le)
        hpad (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankActualDecay
namespace OAI

/-! The actual column/padding catalog is exponentially negligible at the manuscript scales. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_actual_high_rank_decay (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Q D B H : ℕ) (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (base : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
      (weight : ColumnPrimeAssignment J R P × (Fin R → ℕ) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass Qp ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ p ∈ P j, p.Prime) → (∀ p ∈ P j, H ≤ p) → (∀ p ∈ P j, p ≤ B) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (B : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i, Squarefree (a.2 i)) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ base a.1 a.2 +
        wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, weight a ≤ W) →
      (∑ a ∈ F, weight a * columnReciprocalWeight a.1 *
        ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) ≤
          Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  let K := Cw + 2 * (3 + 7 * Cm + 4 * Cj) + 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hK2 : 2 ≤ K := by dsimp [K]; linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_rank_floor_bounds, eventually_column_minor_size_exp h,
    eventually_rank_log_budget 105 (by norm_num),
    eventually_high_rank_total K hK] with L hL hlog hr hminor hlogminor hdecay
  intro J R M Q D B H P Qp F forward j perfect cut base weight W
    hR hRL hJ hM hT hRp hmass hQmass hV hprime hlo hB hQ hD hBexp hH
    hq hd hsq hpool hcount hrank hlit hW hWexp hweight
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hU : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL
  have hHp : (0 : ℝ) < H := (Real.exp_pos _).trans_le hH
  have hHN : 0 < H := by exact_mod_cast hHp
  let r := ⌊L ^ (1 / 50 : ℝ)⌋₊
  let saving := Real.sqrt (((primeHarmonicMass (P j) * H)⁻¹ *
    (1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ))) ^ r)
  let cost := W * (((Fintype.card (CrudeColumnPatternCode J R) : ℝ) * (L ^ (2 : ℕ)) ^ (R * J)) *
    ((∑ n : Fin (R * M + 1), (Fintype.card (CrudeWordCode R n.val R) : ℝ)) *
      (L ^ (2 : ℕ)) ^ (R * M)))
  have hc : cost ≤ Real.exp (K * L * (Real.log L) ^ 2) := by
    have hb := column_padding_catalog_cost_exp_bound J R M L Cj Cm (L ^ (2 : ℕ))
      hR hLp hlog hJ hM hT hRp hU le_rfl
    have hb' : (3 + 7 * Cm + 4 * Cj) * R * (Real.log L) ^ 2 ≤
        2 * (3 + 7 * Cm + 4 * Cj) * L * (Real.log L) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_right hRL
        (show 0 ≤ (3 + 7 * Cm + 4 * Cj) * (Real.log L) ^ 2 by positivity)
      nlinarith
    calc
      cost ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (2 * (3 + 7 * Cm + 4 * Cj) * L * (Real.log L) ^ 2) := by
        exact mul_le_mul hWexp (hb.trans (Real.exp_le_exp.mpr hb')) (by positivity) (by positivity)
      _ = Real.exp ((K - 2) * L * (Real.log L) ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [K]
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (Real.log L)])
  have hraw := high_rank_column_padding_sum P Qp F (by omega) forward j h Q D B H r M
    (L ^ (2 : ℕ)) hU hprime (zero_lt_one.trans_le hV) hmass hQmass hHN hlo hB
    hq hd hsq hpool hcount perfect cut hrank base hlit
  have htotal : (∑ a ∈ F, weight a * columnReciprocalWeight a.1 *
      ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) ≤ cost * saving := by
    calc
      _ ≤ W * (∑ a ∈ F, columnReciprocalWeight a.1 *
          ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹) := by
        rw [mul_sum]
        apply sum_le_sum
        intro a ha
        have ha' := mul_le_mul_of_nonneg_right (hweight a ha)
          (mul_nonneg (columnReciprocalWeight_nonneg a.1) (by positivity :
            0 ≤ ∏ p ∈ paddingPrimeSupport a.2, (p : ℝ)⁻¹))
        simpa only [mul_assoc] using ha'
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left hraw hW
        convert (preTransparency := .instances) hb using 1; dsimp [cost, saving]; ring
  have hm := hlogminor _ (hminor R Q D B hRL hQ hD hBexp)
  have hm' : 1 + (Nat.log 2 (2 * R * (h * Q * D) * B) : ℝ) ≤
      Real.exp (K * Real.log L) := hm.trans (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hK2 (by linarith)))
  exact hdecay r (2 * R * (h * Q * D) * B) (primeHarmonicMass (P j)) H cost _
    hr.1 hr.2 hV hH hm' (by dsimp [cost]; positivity) hc htotal

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleWordPrimeSupport
namespace OAI

/-! Match the tuple/padding reciprocal factors to the full numerical word support. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
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

lemma tupleWord_primeSupport {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (q : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (hq : ∀ i, q i ≠ 0) :
    wordDivisorPrimeSupport (columnTupleWord w forward q) =
      tuplePrimeSupport w ∪ paddingPrimeSupport q := by
  ext p
  have ht (i : Fin R) : columnTuple w i ≠ 0 :=
    (columnTuple_squarefree w i hprime hdisjoint).ne_zero
  simp only [wordDivisorPrimeSupport, columnTupleWord, mem_biUnion, List.mem_toFinset,
    List.mem_ofFn, mem_union, mem_tuplePrimeSupport, paddingPrimeSupport, mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨i, rfl⟩, hp⟩
    rw [Nat.primeFactors_mul (hq i) (ht i), mem_union] at hp
    rcases hp with hp | hp
    · exact Or.inr ⟨i, hp⟩
    · rw [columnTuple_primeFactors w i hprime hdisjoint] at hp
      obtain ⟨j, _, hj⟩ := mem_image.mp hp
      exact Or.inl ⟨j, i, hj⟩
  · rintro (⟨j, i, rfl⟩ | ⟨i, hp⟩)
    · refine ⟨⟨forward i, columnTuple w i, q i⟩, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      apply Or.inr
      rw [columnTuple_primeFactors w i hprime hdisjoint]
      exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
    · refine ⟨⟨forward i, columnTuple w i, q i⟩, ⟨i, rfl⟩, ?_⟩
      rw [Nat.primeFactors_mul (hq i) (ht i), mem_union]
      exact Or.inl hp

lemma tupleWord_reciprocal {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (q : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (hq : ∀ i, q i ≠ 0)
    (hsep : Disjoint (tuplePrimeSupport w) (paddingPrimeSupport q)) :
    columnReciprocalWeight w * (∏ p ∈ paddingPrimeSupport q, (p : ℝ)⁻¹) =
      ∏ p ∈ wordDivisorPrimeSupport (columnTupleWord w forward q), (p : ℝ)⁻¹ := by
  rw [tupleWord_primeSupport w forward q hprime hdisjoint hq, prod_union hsep,
    tuplePrimeSupport_reciprocal w hdisjoint]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessProbabilityWeight
namespace OAI

/-! The retained-witness probability pays exactly the full numerical prime weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma wordDivisorPrimeSupport_append (v w : List SignedStep) :
    wordDivisorPrimeSupport (v ++ w) =
      wordDivisorPrimeSupport v ∪ wordDivisorPrimeSupport w := by
  simp only [wordDivisorPrimeSupport, List.toFinset_append, union_biUnion]

lemma recordedWitnessWord_support {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) :
    wordDivisorPrimeSupport (recordedWitnessWord main word) =
      wordDivisorPrimeSupport main ∪ univ.biUnion (fun j => wordDivisorPrimeSupport (word j)) := by
  rw [recordedWitnessWord, wordDivisorPrimeSupport_append]
  congr 1
  ext p
  simp only [wordDivisorPrimeSupport, mem_biUnion, List.mem_toFinset,
    List.mem_flatten, List.mem_ofFn, mem_univ, true_and]
  constructor
  · rintro ⟨a, ⟨_, ⟨i, rfl⟩, ha⟩, hp⟩
    exact ⟨i, a, ha, hp⟩
  · rintro ⟨i, a, ha, hp⟩
    exact ⟨a, ⟨word i, ⟨i, rfl⟩, ha⟩, hp⟩

lemma coordinate_reciprocal_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (hinj : Function.Injective p) (Q : Finset ℕ)
    (hcover : ∀ q ∈ Q, ∃ i, p i = q) :
    (∏ i ∈ univ.filter (fun i => p i ∈ Q), (p i : ℝ)⁻¹) =
      ∏ q ∈ Q, (q : ℝ)⁻¹ := by
  have he : (univ.filter (fun i => p i ∈ Q)).image p = Q := by
    ext q
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hq
      obtain ⟨i, rfl⟩ := hcover q hq
      exact ⟨i, hq, rfl⟩
  conv_rhs => rw [← he, prod_image (fun i _ j _ hij => hinj hij)]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PaddingWitnessProbability
namespace OAI

/-! Padding tests and the retained witness tests pay the missing reciprocal factors together. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



theorem tuple_weight_mul_padding_hybrid_probability_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (n B h : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (main : List SignedStep) (word : Fin n → List SignedStep)
    (attachment : Fin n → ℤ)
    (hS : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word), ∃ i, p i = q) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => RetainedMainTests p S h B main x ∧
          ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
            ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) ≤
      ∏ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word), (q : ℝ)⁻¹ := by
  let words : Fin (n + 1) → List SignedStep := Fin.cases main word
  let atts : Fin (n + 1) → ℤ := Fin.cases 0 attachment
  have hmono :
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => RetainedMainTests p S h B main x ∧
          ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
            ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B y) ≤
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (RetainedWitnessTests p S h B words atts) := by
    apply FiniteLaw.probability_mono_of_imp
    rintro x ⟨hm, y, hy, hw⟩ i hi j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa only [words, atts, Fin.cases_zero, zero_add] using hm i hi
    · intro k hk
      rw [← hy i hi]
      exact hw j k i hk
  have hb := hmono.trans (retained_witness_probability_le (n + 1) B h p hp hpB S words atts)
  apply (mul_le_mul_of_nonneg_left hb (prod_nonneg (fun _ _ => by positivity))).trans_eq
  rw [main_witness_reciprocal_product]
  have hw (q : ℕ) : (∃ j, q ∈ wordDivisorPrimeSupport (words j)) ↔
      q ∈ wordDivisorPrimeSupport (recordedWitnessWord main word) := by
    rw [recordedWitnessWord_support, mem_union, mem_biUnion]
    constructor
    · rintro ⟨j, hj⟩
      refine Fin.cases ?_ (fun i => ?_) j hj
      · exact fun hj => Or.inl hj
      · exact fun hj => Or.inr ⟨i, mem_univ _, hj⟩
    · rintro (hm | ⟨j, _, hj⟩)
      · exact ⟨0, hm⟩
      · exact ⟨j.succ, hj⟩
  have he : S ∪ univ.filter (fun i => ∃ j, p i ∈ wordDivisorPrimeSupport (words j)) =
      univ.filter (fun i => p i ∈ wordDivisorPrimeSupport (recordedWitnessWord main word)) := by
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and, hw]
    constructor
    · rintro (hi | hi)
      · rw [recordedWitnessWord_support]
        exact mem_union_left _ (hS i hi)
      · exact hi
    · intro hi
      exact Or.inr hi
  rw [he]
  exact coordinate_reciprocal_product p hinj _ hcover

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedMainProbability
namespace OAI

/-! Baseline tuple reciprocals and the retained padding event pay every main prime exactly once. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem tuple_weight_mul_retained_main_probability_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (B h : ℕ) (p : ι → ℕ)
    (hinj : Function.Injective p) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (main : List SignedStep)
    (hS : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport main, ∃ i, p i = q) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (RetainedMainTests p S h B main) ≤
      ∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹ := by
  have hrecord : recordedWitnessWord main (fun i : Fin 0 => i.elim0) = main := by
    simp [recordedWitnessWord]
  have hc : ∀ q ∈ wordDivisorPrimeSupport
      (recordedWitnessWord main (fun i : Fin 0 => i.elim0)), ∃ i, p i = q := by
    simpa only [hrecord] using hcover
  have hb := tuple_weight_mul_padding_hybrid_probability_le 0 B h p hinj hp hpB S main
    (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0) hS hc
  have he (x : ι → Fin B) :
      (RetainedMainTests p S h B main x ∧
        ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
          ∀ j : Fin 0, AttachedResiduePositiveWord p h j.elim0 j.elim0 B y) ↔
      RetainedMainTests p S h B main x := by
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, x, (fun _ _ => rfl), (fun j => j.elim0)⟩
  simpa only [he, hrecord] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedDesignationBound
namespace OAI

/-! A designated trace term retains its extra-reciprocal saving and pays actual padding tests. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem weighted_designation_bound {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B h : ℕ) (p : ι → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (main : List SignedStep) (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (U : Finset τ) (hU : U ⊆ nonsingletonSlots label) (H C : ℝ)
    (hH : 0 < H) (hC : 0 ≤ C) (hpH : ∀ i ∈ nonsingletonLabels label, H ≤ p i)
    (hS : ∀ i ∈ univ.image label, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport main, ∃ i, p i = q)
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x) (hRC : ∀ x, R x ≤ C)
    (hG : ∀ x, |G x| ≤ 1)
    (hretain : ∀ x, R x ≠ 0 → RetainedMainTests p (univ.image label) h B main x) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => R x * |selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|) ≤
      (C * 2 ^ (singletonLabels label).card) *
        H⁻¹ ^ (∑ i ∈ nonsingletonLabels label,
          extraReciprocalExponent (litOccurrences label (designationLit U) i).card
            (unlitOccurrences label (designationLit U) i).card) *
        ∏ q ∈ wordDivisorPrimeSupport main, (q : ℝ)⁻¹ := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let delta := selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
    (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
      (litForcedTarget (nonsingletonSlots label \ U) label target base) y))
  let E := ∑ i ∈ nonsingletonLabels label,
    extraReciprocalExponent (litOccurrences label (designationLit U) i).card
      (unlitOccurrences label (designationLit U) i).card
  have hdelta (x : ι → Fin B) : |delta x| ≤ 2 ^ (singletonLabels label).card :=
    selectedMixedDifference_bound _ _ _ (fun _ => hG _) x
  have habs (x : ι → Fin B) : |R x * delta x| = R x * |delta x| := by
    rw [abs_mul, abs_of_nonneg (hR x)]
  have hav : μ.average (fun x => R x * |delta x|) ≤
      (C * 2 ^ (singletonLabels label).card) *
        μ.probability (RetainedMainTests p (univ.image label) h B main) := by
    have hf := μ.average_abs_le_support (fun x => R x * delta x)
      (RetainedMainTests p (univ.image label) h B main) (C * 2 ^ (singletonLabels label).card)
      (fun x => by rw [habs]; exact mul_le_mul (hRC x) (hdelta x) (abs_nonneg _) hC)
      (fun x hx => hretain x (fun hr => hx (by rw [hr, zero_mul])))
    simpa only [habs] using hf
  have hc := full_word_designated_reciprocal_bound_on_support label U hU p H hH hpH
  have hprob := tuple_weight_mul_retained_main_probability_le B h p hinj hp hpB
    (univ.image label) main hS hcover
  calc
    _ ≤ ((∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * H⁻¹ ^ E) *
        ((C * 2 ^ (singletonLabels label).card) *
          μ.probability (RetainedMainTests p (univ.image label) h B main)) := by
      apply mul_le_mul hc hav
      · exact μ.average_nonneg (fun x => mul_nonneg (hR x) (abs_nonneg _))
      · positivity
    _ = ((C * 2 ^ (singletonLabels label).card) * H⁻¹ ^ E) *
        ((∏ i ∈ univ.image label, (p i : ℝ)⁻¹) *
          μ.probability (RetainedMainTests p (univ.image label) h B main)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprob (by positivity)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedTupleDesignation
namespace OAI

/-! The actual designated tuple-word majorant has precisely the weight used by column rank. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem weighted_designation_le_tuple_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (forward : Fin R → Bool) (q : Fin R → ℕ)
    (hprime : ∀ j, ∀ r ∈ P j, r.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (hq : ∀ i, q i ≠ 0) (hsep : Disjoint (tuplePrimeSupport w) (paddingPrimeSupport q))
    (B h : ℕ) (p : ι → ℕ) (hinj : Function.Injective p)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : Fin R × Fin J → ι) (target : Fin R × Fin J → Fin B) (base : ι → Fin B)
    (U : Finset (Fin R × Fin J)) (hU : U ⊆ nonsingletonSlots label) (H C : ℝ)
    (hH : 1 ≤ H) (hC : 0 ≤ C) (hpH : ∀ i ∈ nonsingletonLabels label, H ≤ p i)
    (hS : ∀ i ∈ univ.image label, p i ∈ wordDivisorPrimeSupport (columnTupleWord w forward q))
    (hcover : ∀ r ∈ wordDivisorPrimeSupport (columnTupleWord w forward q), ∃ i, p i = r)
    (weight G : (ι → Fin B) → ℝ) (hw : ∀ x, 0 ≤ weight x) (hwC : ∀ x, weight x ≤ C)
    (hG : ∀ x, |G x| ≤ 1)
    (hretain : ∀ x, weight x ≠ 0 →
      RetainedMainTests p (univ.image label) h B (columnTupleWord w forward q) x) :
    designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => weight x * |selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|) ≤
      (C * 2 ^ (singletonLabels label).card) * columnReciprocalWeight w *
        ∏ r ∈ paddingPrimeSupport q, (r : ℝ)⁻¹ := by
  have hHp : 0 < H := zero_lt_one.trans_le hH
  have hb := weighted_designation_bound B h p hinj hp hpB (columnTupleWord w forward q)
    label target base U hU H C hHp hC hpH hS hcover weight G hw hwC hG hretain
  have he : H⁻¹ ^ (∑ i ∈ nonsingletonLabels label,
      extraReciprocalExponent (litOccurrences label (designationLit U) i).card
        (unlitOccurrences label (designationLit U) i).card) ≤ 1 :=
    pow_le_one₀ (by positivity) ((inv_le_one₀ hHp).mpr hH)
  rw [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Fin R × Fin J)) _ _] at hb
  apply hb.trans
  calc
    _ ≤ (C * 2 ^ (singletonLabels label).card) * 1 *
        ∏ r ∈ wordDivisorPrimeSupport (columnTupleWord w forward q), (r : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
    _ = _ := by
      rw [mul_one, ← tupleWord_reciprocal w forward q hprime hdisjoint hq hsep]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankWeightedWords
namespace OAI

/-! Column-rank decay applied to the actual weighted mixed-difference majorants. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_weighted_high_rank_words_oai
    (h : ℕ) (Cj Cm Cw : ℝ) (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (J R M Q D B H Z : ℕ)
      (P : Fin J → Finset ℕ) (Qp : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (origin : ColumnPrimeAssignment J R P → (Fin R → ℕ) → ℤ)
      (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpZ : ∀ i, p i ≤ Z)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → ι)
      (target : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → Fin R × Fin J → Fin Z)
      (base : ι → Fin Z) (U : Finset (Fin R × Fin J))
      (weight G : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → (ι → Fin Z) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass Qp ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ l, ∀ r ∈ P l, r.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ r ∈ P j, H ≤ r) → (∀ r ∈ P j, r ≤ B) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (B : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i, Squarefree (a.2 i)) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors ⊆ Qp) →
      (∀ a ∈ F, ∀ i, (a.2 i).primeFactors.card ≤ M) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i ∈ perfect, ((a.1 j i).val : ℤ) ∣ origin a.1 a.2 +
        wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val)) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      Function.Injective p →
      (∀ a ∈ F, U ⊆ nonsingletonSlots (label a)) →
      (∀ a ∈ F, ∀ i ∈ nonsingletonLabels (label a), (H : ℝ) ≤ p i) →
      (∀ a ∈ F, Disjoint (tuplePrimeSupport a.1) (paddingPrimeSupport a.2)) →
      (∀ a ∈ F, ∀ i ∈ univ.image (label a),
        p i ∈ wordDivisorPrimeSupport (columnTupleWord a.1 forward a.2)) →
      (∀ a ∈ F, ∀ r ∈ wordDivisorPrimeSupport (columnTupleWord a.1 forward a.2), ∃ i, p i = r) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, |G a x| ≤ 1) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        RetainedMainTests p (univ.image (label a)) h Z (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, designatedReciprocal p (singletonLabels (label a))
        (nonsingletonSlots (label a) \ U) U (label a) *
        (FiniteLaw.independent (fun i => uniformResidueLaw Z (p i) (hp i) (hpZ i))).average
          (fun x => weight a x * |selectedMixedDifference (singletonLabels (label a))
            (singletonTarget (label a) (target a) base)
            (fun y => G a (forceCoordinates ((nonsingletonSlots (label a) \ U).image (label a))
              (litForcedTarget (nonsingletonSlots (label a) \ U) (label a) (target a) base) y)) x|)) ≤
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    eventually_actual_high_rank_decay h Cj Cm Cw hCj hCm hCw] with L hL hdecay
  intro ι _ _ J R M Q D B H Z P Qp F forward j perfect cut origin p hp hpZ label target base U
    weight G cap W hR hRL hJ hM hT hRp hmass hQmass hV hprime hdisjoint hlo hB hQ hD
    hBexp hH hq hd hsq hpool hcount hrank hlit hW hWexp hinj hU hpH hsep hseen hcover
    hcap hw hwcap hG hretain hcost
  have hHone : (1 : ℝ) ≤ H :=
    (Real.one_le_exp (Real.rpow_nonneg (by linarith) _)).trans hH
  apply le_trans _ (hdecay J R M Q D B H P Qp F forward j perfect cut origin
    (fun a => cap a * 2 ^ (singletonLabels (label a)).card) W
    hR hRL hJ hM hT hRp hmass hQmass hV (hprime j) hlo hB hQ hD hBexp hH
    hq hd hsq hpool hcount hrank hlit hW hWexp hcost)
  apply sum_le_sum
  intro a ha
  have hb := weighted_designation_le_tuple_weight a.1 forward a.2 hprime hdisjoint
    (fun i => (hsq a ha i).ne_zero) (hsep a ha) Z h p hinj hp hpZ
    (label a) (target a) base U (hU a ha) H (cap a) hHone (hcap a ha) (hpH a ha)
    (hseen a ha) (hcover a ha) (weight a) (G a) (hw a ha) (hwcap a ha) (hG a ha) (hretain a ha)
  exact hb

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.eventually_weighted_high_rank_words_oai := @OAI.TwoPointCorrelations.eventually_weighted_high_rank_words_oai
