-- Prove2me | solution 1 for OAI.TwoPointCorrelations.prohibited_singleton_words_le_catalog
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:42:40.082724+00:00
-- url     : https://prove2.me/submissions/f8f27dab-4397-4810-a146-052da5379775

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

omit [DecidableEq A] in
lemma average_const_mul (μ : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    μ.average (fun x => c * f x) = c * μ.average f := by
  simp only [average, Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  ring

omit [DecidableEq A] in
lemma abs_average_le (μ : FiniteLaw A) (f : A → ℝ) :
    |μ.average f| ≤ μ.average (fun x => |f x|) := by
  unfold average
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply sum_congr rfl
  intro x _
  rw [abs_mul, abs_of_nonneg (μ.nonneg x)]

lemma average_singleton_pin (μ : FiniteLaw A) (a : A) (F : A → ℝ) :
    μ.average (fun x => (if x = a then (1 : ℝ) else 0) * F x) = μ.weight a * F a := by
  simp [average]


lemma independent_average_pin (μ : ι → FiniteLaw A) (a : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x => (∏ i, if x i = a i then (1 : ℝ) else 0) * F x) =
      (∏ i, (μ i).weight (a i)) * F a := by
  have hpin (x : ι → A) : (∏ i, if x i = a i then (1 : ℝ) else 0) =
      if x = a then (1 : ℝ) else 0 := by
    by_cases hx : x = a
    · simp [hx]
    · have hn : ¬∀ i, x i = a i := fun h => hx (funext h)
      simp [Fintype.prod_boole, hx, hn]
  simp only [hpin]
  exact average_singleton_pin (independent μ) a F

omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma force_join (S : Finset ι) (a : ι → A)
    (x : S → A) (y : {i // i ∉ S} → A) :
    forceCoordinates S a (joinCoordinates S x y) =
      joinCoordinates S (fun i : S => a i) y := by
  funext i
  by_cases hi : i ∈ S <;> simp [forceCoordinates, piecewise, joinCoordinates, hi]

/-- Forcing a selected set has precisely the product mass of its forced
atoms, even when the observable depends on every other coordinate. -/
theorem independent_forcing (μ : ι → FiniteLaw A) (S : Finset ι)
    (a : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i ∈ S, if x i = a i then (1 : ℝ) else 0) * F x) =
      (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average (fun x => F (forceCoordinates S a x)) := by
  rw [independent_average_split μ S]
  have hin (y : {i // i ∉ S} → A) :
      (independent (fun i : S => μ i)).average (fun x =>
        (∏ i ∈ S, if joinCoordinates S x y i = a i then (1 : ℝ) else 0) *
          F (joinCoordinates S x y)) =
        (∏ i ∈ S, (μ i).weight (a i)) * F (joinCoordinates S (fun i : S => a i) y) := by
    have hpin := independent_average_pin (fun i : S => μ i) (fun i : S => a i)
      (fun x => F (joinCoordinates S x y))
    have hp (x : S → A) :
        (∏ i ∈ S, if joinCoordinates S x y i = a i then (1 : ℝ) else 0) =
          ∏ i : S, if x i = a i then (1 : ℝ) else 0 := by
      rw [← Finset.prod_coe_sort S]
      simp only [joinCoordinates_mem]
    simp_rw [hp]
    rw [← Finset.prod_coe_sort S]
    exact hpin
  simp_rw [hin]
  rw [average_const_mul, independent_average_split μ S (fun x => F (forceCoordinates S a x))]
  congr 1
  apply congrArg (independent (fun i : {i // i ∉ S} => μ i)).average
  funext y
  simp only [force_join, average_const]

/-- Centering every singleton is exactly the alternating sum over forcing
subsets, before any absolute value is taken. -/
theorem exact_mixed_centering (μ : ι → FiniteLaw A) (a : ι → A)
    (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x) =
      (∏ i, (μ i).weight (a i)) * (independent μ).average (mixedDifference a F) := by
  have hexp (x : ι → A) :
      (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) =
      ∑ S : Finset ι, (-1 : ℝ) ^ Sᶜ.card * (∏ i ∈ Sᶜ, (μ i).weight (a i)) *
        ∏ i ∈ S, if x i = a i then (1 : ℝ) else 0 := by
    simp only [sub_eq_add_neg, Fintype.prod_add, prod_neg]
    apply sum_congr rfl
    intro S _
    ring
  have hm : (independent μ).average (mixedDifference a F) =
      ∑ S : Finset ι, (-1 : ℝ) ^ Sᶜ.card *
        (independent μ).average (fun x => F (forceCoordinates S a x)) := by
    unfold mixedDifference
    rw [average_sum]
    simp_rw [average_const_mul]
  simp_rw [hexp, sum_mul]
  rw [average_sum, hm, mul_sum]
  apply sum_congr rfl
  intro S _
  have hc : (∏ i ∈ Sᶜ, (μ i).weight (a i)) *
      (∏ i ∈ S, (μ i).weight (a i)) = ∏ i, (μ i).weight (a i) := by
    rw [mul_comm, prod_mul_prod_compl]
  calc
    _ = ((-1 : ℝ) ^ Sᶜ.card * (∏ i ∈ Sᶜ, (μ i).weight (a i))) *
        (independent μ).average (fun x =>
          (∏ i ∈ S, if x i = a i then (1 : ℝ) else 0) * F x) := by
      rw [← average_const_mul]
      congr 1
      funext x
      ring
    _ = ((-1 : ℝ) ^ Sᶜ.card * (∏ i ∈ Sᶜ, (μ i).weight (a i))) *
        ((∏ i ∈ S, (μ i).weight (a i)) *
          (independent μ).average (fun x => F (forceCoordinates S a x))) := by
      rw [independent_forcing]
    _ = (-1 : ℝ) ^ Sᶜ.card *
        ((∏ i ∈ Sᶜ, (μ i).weight (a i)) * (∏ i ∈ S, (μ i).weight (a i))) *
          (independent μ).average (fun x => F (forceCoordinates S a x)) := by ring
    _ = _ := by rw [hc]; ring



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PartialCentering
namespace OAI

/-! Exact singleton centering on selected coordinates of the complete residue sample. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]


omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma selectedMixedDifference_join (S : Finset ι) (a : ι → A) (F : (ι → A) → ℝ)
    (x : S → A) (y : {i // i ∉ S} → A) :
    selectedMixedDifference S a F (joinCoordinates S x y) =
      mixedDifference (fun i : S => a i) (fun z => F (joinCoordinates S z y)) x := by
  simp only [selectedMixedDifference, joinCoordinates_mem, joinCoordinates_notMem]

omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma selectedMixedDifference_bound (S : Finset ι) (a : ι → A) (F : (ι → A) → ℝ)
    (hF : ∀ x, |F x| ≤ 1) (x : ι → A) :
    |selectedMixedDifference S a F x| ≤ 2 ^ S.card := by
  simpa only [selectedMixedDifference, Fintype.card_coe] using
    abs_mixedDifference_le (fun i : S => a i)
      (fun z : S → A => F (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
      (fun z => hF _) (fun i : S => x i)

namespace FiniteLaw

/-- The unselected coordinates remain part of the original sample, and
are simply held fixed while applying the exact centering identity. -/
theorem exact_selected_centering (μ : ι → FiniteLaw A) (S : Finset ι)
    (a : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x) =
      (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average (selectedMixedDifference S a F) := by
  rw [independent_average_split μ S]
  have hinner (y : {i // i ∉ S} → A) :
      (independent (fun i : S => μ i)).average (fun x : S → A =>
        (∏ i ∈ S, ((if joinCoordinates S x y i = a i then (1 : ℝ) else 0) -
          (μ i).weight (a i))) * F (joinCoordinates S x y)) =
      (∏ i ∈ S, (μ i).weight (a i)) *
        (independent (fun i : S => μ i)).average
          (mixedDifference (fun i : S => a i) (fun x => F (joinCoordinates S x y))) := by
    have hh := exact_mixed_centering (fun i : S => μ i) (fun i : S => a i)
      (fun x => F (joinCoordinates S x y))
    have hp (x : S → A) :
        (∏ i ∈ S, ((if joinCoordinates S x y i = a i then (1 : ℝ) else 0) -
          (μ i).weight (a i))) =
        ∏ i : S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i)) := by
      rw [← prod_coe_sort S]
      simp only [joinCoordinates_mem]
    simp_rw [hp]
    rw [← prod_coe_sort S]
    exact hh
  simp_rw [hinner]
  rw [average_const_mul, independent_average_split μ S (selectedMixedDifference S a F)]
  simp only [selectedMixedDifference_join]

/-- Nonsingletons with at least one lit occurrence are forced once. The
singleton coordinates are then centered on the same sample. -/
theorem exact_selected_designation (μ : ι → FiniteLaw A) (S T : Finset ι)
    (hST : Disjoint S T) (a b : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i ∈ T, if x i = b i then (1 : ℝ) else 0) *
      ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x)) =
      (∏ i ∈ T, (μ i).weight (b i)) * (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average
          (selectedMixedDifference S a (fun x => F (forceCoordinates T b x))) := by
  rw [independent_forcing μ T b]
  have hp (x : ι → A) :
      (∏ i ∈ S, ((if forceCoordinates T b x i = a i then (1 : ℝ) else 0) -
        (μ i).weight (a i))) =
      ∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i)) := by
    apply prod_congr rfl
    intro i hi
    have hiT : i ∉ T := fun hiT => (disjoint_left.mp hST hi hiT)
    simp only [forceCoordinates_apply, hiT, ite_false]
  simp_rw [hp]
  rw [exact_selected_centering μ S a]
  ring

/-- The absolute value is taken only after singleton integration, retaining
the full cancellation caused by the mixed difference. -/
theorem selected_designation_bound (μ : ι → FiniteLaw A) (S T : Finset ι)
    (hST : Disjoint S T) (a b : ι → A) (F : (ι → A) → ℝ) :
    |(independent μ).average (fun x =>
      (∏ i ∈ T, if x i = b i then (1 : ℝ) else 0) *
      ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x))| ≤
      (∏ i ∈ T, (μ i).weight (b i)) * (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average (fun x =>
          |selectedMixedDifference S a (fun x => F (forceCoordinates T b x)) x|) := by
  rw [exact_selected_designation μ S T hST a b F, abs_mul,
    abs_of_nonneg (mul_nonneg (prod_nonneg (fun i _ => (μ i).nonneg _))
      (prod_nonneg (fun i _ => (μ i).nonneg _)))]
  exact mul_le_mul_of_nonneg_left (abs_average_le _ _)
    (mul_nonneg (prod_nonneg (fun i _ => (μ i).nonneg _))
      (prod_nonneg (fun i _ => (μ i).nonneg _)))

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

/-- Repetitions of the same lit residue test contribute just one indicator. -/
lemma lit_indicator_product (L : Finset τ) (label : τ → ι) (target : τ → A)
    (base : ι → A) (hL : LitConsistent L label target) (x : ι → A) :
    (∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) =
      ∏ i ∈ L.image label, if x i = litForcedTarget L label target base i then (1 : ℝ) else 0 := by
  classical
  have hall : (∀ t ∈ L, x (label t) = target t) ↔
      ∀ i ∈ L.image label, x i = litForcedTarget L label target base i := by
    constructor
    · intro hx i hi
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hi
      rw [litForcedTarget_at L label target base hL t ht]
      exact hx t ht
    · intro hx t ht
      have hi := hx (label t) (mem_image.mpr ⟨t, ht, rfl⟩)
      rwa [litForcedTarget_at L label target base hL t ht] at hi
  simp only [Finset.prod_boole, hall]

omit [DecidableEq ι] in
/-- Incompatible lit offsets give exactly zero before any estimate. -/
lemma lit_indicator_product_eq_zero (L : Finset τ) (label : τ → ι) (target : τ → A)
    (hL : ¬LitConsistent L label target) (x : ι → A) :
    (∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) = 0 := by
  classical
  have hno : ¬∀ t ∈ L, x (label t) = target t := by
    intro hx
    apply hL
    intro t ht u hu htu
    exact (hx t ht).symm.trans (htu ▸ hx u hu)
  rw [Finset.prod_boole, if_neg hno]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceDesignations
namespace OAI

/-! Exact lit-consistency reduction and centering for a designated trace word. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

omit [Fintype ι] [DecidableEq ι] [Fintype A] in
/-- Expand only the designated nonsingleton occurrences, retaining all signs. -/
lemma centered_occurrence_expansion [DecidableEq τ] (S : Finset τ)
    (label : τ → ι) (target : τ → A) (θ : ι → ℝ) (x : ι → A) :
    (∏ t ∈ S, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) =
      ∑ U ∈ S.powerset, ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t)) *
        ∏ t ∈ S \ U, if x (label t) = target t then (1 : ℝ) else 0 := by
  rw [Finset.prod_sub]
  apply sum_congr rfl
  intro U _
  ring


/-- A contradictory pair of lit offsets annihilates the term exactly. -/
lemma designated_residue_zero (μ : ι → FiniteLaw A) (S : Finset ι) (L : Finset τ)
    (label : τ → ι) (target : τ → A) (a : ι → A) (c : ℝ) (F : (ι → A) → ℝ)
    (hL : ¬LitConsistent L label target) :
    (FiniteLaw.independent μ).average (fun x => c *
      ((∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) *
        ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x))) = 0 := by
  simp only [lit_indicator_product_eq_zero L label target hL, zero_mul, mul_zero]
  exact FiniteLaw.average_const _ 0

/-- This is the designated-term mixed-difference bound with literal lit
occurrences, including the scalar sign and every residue-independent factor. -/
theorem designated_residue_bound (μ : ι → FiniteLaw A) (S : Finset ι) (L : Finset τ)
    (label : τ → ι) (target : τ → A) (a base : ι → A) (c : ℝ) (F : (ι → A) → ℝ)
    (hL : LitConsistent L label target) (hSL : Disjoint S (L.image label)) :
    |(FiniteLaw.independent μ).average (fun x => c *
      ((∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) *
        ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x)))| ≤
      |c| * (∏ i ∈ L.image label, (μ i).weight (litForcedTarget L label target base i)) *
        (∏ i ∈ S, (μ i).weight (a i)) *
          (FiniteLaw.independent μ).average (fun x =>
            |selectedMixedDifference S a
              (fun x => F (forceCoordinates (L.image label) (litForcedTarget L label target base) x)) x|) := by
  simp_rw [lit_indicator_product L label target base hL]
  rw [FiniteLaw.average_const_mul, abs_mul]
  calc
    _ ≤ |c| * ((∏ i ∈ L.image label, (μ i).weight (litForcedTarget L label target base i)) *
        (∏ i ∈ S, (μ i).weight (a i)) *
          (FiniteLaw.independent μ).average (fun x =>
            |selectedMixedDifference S a
              (fun x => F (forceCoordinates (L.image label) (litForcedTarget L label target base) x)) x|)) :=
      mul_le_mul_of_nonneg_left (FiniteLaw.selected_designation_bound μ S (L.image label) hSL a
        (litForcedTarget L label target base) F) (abs_nonneg c)
    _ = _ := by ring

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

omit [Fintype ι] [DecidableEq ι] in
lemma absolute_unlit_coefficient (U : Finset τ) (label : τ → ι) (θ : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) :
    |(-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t)| = ∏ t ∈ U, θ (label t) := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_nonneg (prod_nonneg (fun t _ => hθ (label t)))



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

lemma singleton_not_nonsingleton (label : τ → ι) (i : ι)
    (hi : i ∈ singletonLabels label) : i ∉ nonsingletonLabels label := by
  have hc := (mem_filter.mp hi).2
  simp only [nonsingletonLabels, mem_filter, mem_univ, true_and, hc]
  omega




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueTraceBound
namespace OAI

/-! The manuscript's designated-term majorant for actual uniform residues. -/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι]


/-- Singleton integration and lit forcing are carried out on one common
residue sample. The unlit slots impose no further residue condition. -/
theorem uniform_designated_trace_bound (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (S : Finset ι) (L U : Finset τ) (label : τ → ι) (target : τ → Fin B)
    (a base : ι → Fin B) (R : ℝ) (G : (ι → Fin B) → ℝ)
    (hR : 0 ≤ R) (hL : LitConsistent L label target)
    (hSL : Disjoint S (L.image label))
    (ha : ∀ i ∈ S, (a i).val < p i)
    (htarget : ∀ t ∈ L, (target t).val < p (label t)) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) *
        ((∏ t ∈ L, if x (label t) = target t then (1 : ℝ) else 0) *
          ((∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (p i : ℝ)⁻¹)) * G x)))| ≤
      R * designatedReciprocal p S L U label *
        (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
          (fun x => |selectedMixedDifference S a
            (fun x => G (forceCoordinates (L.image label)
              (litForcedTarget L label target base) x)) x|) := by
  let μ := fun i => uniformResidueLaw B (p i) (hp i) (hpB i)
  have hs : ∀ x : ι → Fin B,
      (∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) =
        ∏ i ∈ S, ((if x i = a i then (1 : ℝ) else 0) - (p i : ℝ)⁻¹) := by
    intro x
    apply prod_congr rfl
    intro i hi
    rw [uniformResidueLaw_weight B (p i) (hp i) (hpB i) (a i) (ha i hi)]
  have hsp : (∏ i ∈ S, (μ i).weight (a i)) = ∏ i ∈ S, (p i : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro i hi
    exact uniformResidueLaw_weight B (p i) (hp i) (hpB i) (a i) (ha i hi)
  have hlp : (∏ i ∈ L.image label, (μ i).weight (litForcedTarget L label target base i)) =
      ∏ i ∈ L.image label, (p i : ℝ)⁻¹ := by
    apply prod_congr rfl
    intro i hi
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hi
    rw [litForcedTarget_at L label target base hL t ht]
    exact uniformResidueLaw_weight B (p (label t)) (hp _) (hpB _) _ (htarget t ht)
  have hc : |R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)| =
      R * ∏ t ∈ U, (p (label t) : ℝ)⁻¹ := by
    rw [abs_mul, abs_of_nonneg hR,
      absolute_unlit_coefficient U label (fun i => (p i : ℝ)⁻¹)
        (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  have hb := designated_residue_bound μ S L label target a base
    (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) G hL hSL
  simp only [hs, hc, hsp, hlp] at hb
  simpa only [designatedReciprocal, mul_assoc] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenteredWordExpansion
namespace OAI

/-! Split an actual centered word into its singleton factors and lit designations. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι τ A : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]





lemma singletonRepresentative_label (label : τ → ι) (i : singletonLabels label) :
    label (singletonRepresentative label i) = i.val :=
  Classical.choose_spec (singleton_occurrence_exists label i)

lemma singleton_occurrence_unique (label : τ → ι) (i : singletonLabels label)
    (t : τ) (ht : label t = i.val) : t = singletonRepresentative label i := by
  obtain ⟨a, ha⟩ := card_eq_one.mp (mem_filter.mp i.property).2
  have htmem : t ∈ labelOccurrences label i.val := mem_filter.mpr ⟨mem_univ _, ht⟩
  have hrmem : singletonRepresentative label i ∈ labelOccurrences label i.val :=
    mem_filter.mpr ⟨mem_univ _, singletonRepresentative_label label i⟩
  rw [ha, mem_singleton] at htmem hrmem
  exact htmem.trans hrmem.symm



lemma singletonSlots_product (label : τ → ι) (f : τ → ℝ) :
    (∏ t ∈ singletonSlots label, f t) =
      ∏ i : singletonLabels label, f (singletonRepresentative label i) := by
  apply prod_bij (fun t ht => (⟨label t, (mem_filter.mp ht).2⟩ : singletonLabels label))
  · intro t ht
    exact mem_univ _
  · intro t ht u hu he
    have htu : label t = label u := congrArg Subtype.val he
    exact (singleton_occurrence_unique label ⟨label t, (mem_filter.mp ht).2⟩ t rfl).trans
      (singleton_occurrence_unique label ⟨label t, (mem_filter.mp ht).2⟩ u htu.symm).symm
  · intro i _
    refine ⟨singletonRepresentative label i, ?_, ?_⟩
    · exact mem_filter.mpr ⟨mem_univ _, (singletonRepresentative_label label i).symm ▸ i.property⟩
    · exact Subtype.ext (singletonRepresentative_label label i)
  · intro t ht
    rw [← singleton_occurrence_unique label ⟨label t, (mem_filter.mp ht).2⟩ t rfl]

lemma centered_singleton_product [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (θ : ι → ℝ) :
    (∏ t ∈ singletonSlots label,
      ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) =
      ∏ i ∈ singletonLabels label,
        ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i) := by
  rw [singletonSlots_product]
  rw [← Finset.prod_coe_sort (s := singletonLabels label) (f := fun i : ι =>
    ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i))]
  apply prod_congr rfl
  intro i _
  simp only [singletonRepresentative_label, singletonTarget, dif_pos i.property]

lemma centered_word_split [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (θ : ι → ℝ) :
    (∏ t, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) =
      (∏ t ∈ nonsingletonSlots label,
        ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) *
      ∏ i ∈ singletonLabels label,
        ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i) := by
  rw [← centered_singleton_product label target base x θ]
  have he : singletonSlots label = univ.filter (fun t => t ∉ nonsingletonSlots label) := by
    ext t
    have hp : 0 < (labelOccurrences label (label t)).card :=
      card_pos.mpr ⟨t, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    simp only [singletonSlots, nonsingletonSlots, singletonLabels, nonsingletonLabels,
      mem_filter, mem_univ, true_and]
    omega
  rw [he]
  have hcomp : univ.filter (fun t => t ∉ nonsingletonSlots label) =
      (nonsingletonSlots label)ᶜ := by ext t; simp
  rw [hcomp]
  exact (prod_mul_prod_compl (nonsingletonSlots label) (fun t : τ =>
    ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t)))).symm

/-- Every singleton remains centered while only nonsingleton occurrences
are expanded. This is an identity of signed word contributions. -/
lemma centered_word_designation_expansion [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (θ : ι → ℝ)
    (R : ℝ) (G : (ι → A) → ℝ) :
    R * (∏ t, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) * G x =
      ∑ U ∈ (nonsingletonSlots label).powerset,
        (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t))) *
          ((∏ t ∈ nonsingletonSlots label \ U,
            if x (label t) = target t then (1 : ℝ) else 0) *
            ((∏ i ∈ singletonLabels label,
              ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i)) * G x)) := by
  rw [centered_word_split label target base x θ,
    centered_occurrence_expansion (nonsingletonSlots label) label target θ x]
  simp only [sum_mul, mul_sum]
  apply sum_congr rfl
  intro U _
  ring

/-- Averaging precedes the triangle inequality; no absolute value is
introduced while expanding the signed nonsingleton terms. -/
theorem centered_word_expectation [Fintype A] [DecidableEq A]
    (μ : FiniteLaw (ι → A)) (label : τ → ι) (target : τ → A)
    (base : ι → A) (θ : ι → ℝ) (R : ℝ) (G : (ι → A) → ℝ) :
    μ.average (fun x => R *
      (∏ t, ((if x (label t) = target t then (1 : ℝ) else 0) - θ (label t))) * G x) =
      ∑ U ∈ (nonsingletonSlots label).powerset, μ.average (fun x =>
        (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, θ (label t))) *
          ((∏ t ∈ nonsingletonSlots label \ U,
            if x (label t) = target t then (1 : ℝ) else 0) *
            ((∏ i ∈ singletonLabels label,
              ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - θ i)) * G x))) := by
  simp_rw [centered_word_designation_expansion label target base _ θ R G]
  simp only [FiniteLaw.average, mul_sum]
  rw [sum_comm]

lemma singleton_disjoint_designated (label : τ → ι) (U : Finset τ) :
    Disjoint (singletonLabels label) ((nonsingletonSlots label \ U).image label) := by
  apply disjoint_left.mpr
  intro i hi hiL
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hiL
  exact singleton_not_nonsingleton label _ hi ((mem_filter.mp (mem_sdiff.mp ht).1).2)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenteredWordMajorant
namespace OAI

/-! Apply exact uniform singleton centering to the complete signed word. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]

lemma uniform_singleton_target_lt (B : ℕ) (p : ι → ℕ) (label : τ → ι)
    (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t)) (i : ι)
    (hi : i ∈ singletonLabels label) :
    (singletonTarget label target base i).val < p i := by
  simp only [singletonTarget, dif_pos hi]
  simpa only [singletonRepresentative_label] using
    htarget (singletonRepresentative label ⟨i, hi⟩)

/-- Contradictory lit tests vanish even with all singleton factors retained. -/
lemma uniform_word_designation_zero (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t)) (U : Finset τ)
    (R : ℝ) (G : (ι → Fin B) → ℝ)
    (hL : ¬LitConsistent (nonsingletonSlots label \ U) label target) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) *
        ((∏ t ∈ nonsingletonSlots label \ U,
          if x (label t) = target t then (1 : ℝ) else 0) *
          ((∏ i ∈ singletonLabels label,
            ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) -
              (p i : ℝ)⁻¹)) * G x))) = 0 := by
  have hprod (x : ι → Fin B) :
      (∏ i ∈ singletonLabels label,
        ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) -
          (uniformResidueLaw B (p i) (hp i) (hpB i)).weight
            (singletonTarget label target base i))) =
        ∏ i ∈ singletonLabels label,
          ((if x i = singletonTarget label target base i then (1 : ℝ) else 0) - (p i : ℝ)⁻¹) := by
    apply prod_congr rfl
    intro i hi
    rw [uniformResidueLaw_weight B (p i) (hp i) (hpB i) _
      (uniform_singleton_target_lt B p label target base htarget i hi)]
  have hz := designated_residue_zero
    (fun i => uniformResidueLaw B (p i) (hp i) (hpB i)) (singletonLabels label)
    (nonsingletonSlots label \ U) label target (singletonTarget label target base)
    (R * ((-1 : ℝ) ^ U.card * ∏ t ∈ U, (p (label t) : ℝ)⁻¹)) G hL
  simpa only [hprod] using hz

/-- Full-word majorant. Absolute values are introduced only after the
signed expansion and exact singleton integrations have been performed. -/
theorem uniform_centered_word_majorant (B : ℕ) (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R : ℝ) (hR : 0 ≤ R) (G : (ι → Fin B) → ℝ) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        if LitConsistent (nonsingletonSlots label \ U) label target then
          R * designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
            (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
              (fun x => |selectedMixedDifference (singletonLabels label)
                (singletonTarget label target base)
                (fun x => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
                  (litForcedTarget (nonsingletonSlots label \ U) label target base) x)) x|)
        else 0 := by
  rw [centered_word_expectation _ label target base (fun i => (p i : ℝ)⁻¹) R G]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro U _
  by_cases hL : LitConsistent (nonsingletonSlots label \ U) label target
  · rw [if_pos hL]
    exact uniform_designated_trace_bound B p hp hpB (singletonLabels label)
      (nonsingletonSlots label \ U) U label target (singletonTarget label target base) base
      R G hR hL (singleton_disjoint_designated label U)
      (uniform_singleton_target_lt B p label target base htarget)
      (fun t _ => htarget t)
  · rw [if_neg hL,
      uniform_word_designation_zero B p hp hpB label target base htarget U R G hL, abs_zero]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnRepresentatives
namespace OAI

/-! Canonical occurrence representatives for the imperfect-position code. -/

namespace TwoPointCorrelations

open _root_.Finset

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

open _root_.Finset
open scoped _root_.Classical









/-- A finite union bound for arbitrary events under the concrete finite law. -/
theorem FiniteLaw.probability_exists_le {A I : Type*} [Fintype A] [Fintype I]
    (μ : FiniteLaw A) (E : I → A → Prop) :
    μ.probability (fun x => ∃ i, E i x) ≤ ∑ i, μ.probability (E i) := by
  classical
  unfold FiniteLaw.probability
  rw [← μ.average_sum]
  apply μ.average_mono
  intro x
  by_cases hx : ∃ i, E i x
  · obtain ⟨i, hi⟩ := hx
    simp only [if_pos (show ∃ j, E j x from ⟨i, hi⟩)]
    apply (le_trans ?_ (single_le_sum (f := fun i => if E i x then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)))
    simp [hi]
  · simp only [if_neg hx]
    exact sum_nonneg (fun i _ => by split_ifs <;> norm_num)




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

open _root_.Finset
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


/-- Padding is reconstructed from the same prime classes as tuple factors,
so repetitions across steps never introduce new independent numerical choices. -/
lemma numericalWord_get (c : CrudeWordCode R N R) (value : c.usedClasses → ℕ) (i : Fin R) :
    (c.numericalWord value)[i.val]'(by rw [numericalWord_length]; exact i.isLt) =
      ⟨c.1 i,
        ∏ j ∈ univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = false), value (c.classAt j),
        ∏ j ∈ univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = true), value (c.classAt j)⟩ := by
  simp [numericalWord, PrimeSlotData.word, PrimeSlotData.factor, PrimeSlotData.slots, primeData]
  constructor <;> congr 1

end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeSlots
namespace OAI

/-! Actual prime factors give a complete bounded-slot code for a numerical word. -/

namespace TwoPointCorrelations

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessCover
namespace OAI

/-!
# A common hybrid containing a private-prime witness family

The product over all witness tests is expanded only to prove existence.
No cardinality of that powerset is charged in an estimate. An omitted
coordinate annihilates the full mixed difference; a surviving term must
therefore cover every singleton coordinate in one common hybrid.
-/

namespace TwoPointCorrelations

open _root_.Finset

variable {ι W A : Type*} [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]





omit [DecidableEq W] in
lemma mixedDifference_sum (a : ι → A) (F : W → (ι → A) → ℝ) (x : ι → A) :
    mixedDifference a (fun y => ∑ w : W, F w y) x = ∑ w : W, mixedDifference a (F w) x := by
  unfold mixedDifference
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma mixedDifference_const_mul (a : ι → A) (c : ℝ) (F : (ι → A) → ℝ) (x : ι → A) :
    mixedDifference a (fun y => c * F y) x = c * mixedDifference a F x := by
  unfold mixedDifference
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- If one coordinate is irrelevant, its forced-minus-original difference
cancels exactly, regardless of the values of the other coordinates. -/
lemma mixedDifference_eq_zero_of_ignores (a : ι → A) (F : (ι → A) → ℝ) (x : ι → A)
    (i : ι) (hF : ∀ u v, (∀ j, j ≠ i → u j = v j) → F u = F v) :
    mixedDifference a F x = 0 := by
  have hterm (S : Finset ι) (hiS : i ∉ S) :
      (-1 : ℝ) ^ Sᶜ.card * F (forceCoordinates S a x) +
        (-1 : ℝ) ^ (insert i S)ᶜ.card * F (forceCoordinates (insert i S) a x) = 0 := by
    have hvalues : F (forceCoordinates S a x) = F (forceCoordinates (insert i S) a x) := by
      apply hF
      intro j hji
      simp [forceCoordinates_apply, hji]
    have hcard : Sᶜ.card = (insert i S)ᶜ.card + 1 := by
      rw [← insert_compl_insert hiS, card_insert_of_notMem (by simp)]
    rw [hcard, pow_succ, hvalues]
    ring
  unfold mixedDifference
  have hpowerset : (Finset.univ : Finset ι).powerset = (Finset.univ : Finset (Finset ι)) := by ext; simp
  rw [← hpowerset, ← insert_erase (Finset.mem_univ i),
    Finset.sum_powerset_insert (Finset.notMem_erase i Finset.univ), ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro S hS
  exact hterm S (fun hi => (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hi)).1 rfl)

omit [Fintype ι] [DecidableEq ι] in
lemma witnessAvoidance_expansion (I : W → (ι → A) → Bool) (x : ι → A) :
    witnessAvoidance I x =
      ∑ S : Finset W, (-1 : ℝ) ^ S.card * witnessIntersection I S x := by
  unfold witnessAvoidance witnessIntersection
  have h := Finset.prod_sub (fun _ : W => (1 : ℝ)) (fun w => if I w x then 1 else 0) Finset.univ
  simpa using h

omit [Fintype ι] [Fintype W] [DecidableEq W] in
lemma witnessIntersection_ignores (support : W → Finset ι) (I : W → (ι → A) → Bool)
    (hdepends : ∀ w, DependsOn (support w) (I w)) (S : Finset W) (i : ι)
    (hi : i ∉ witnessSupport support S) (x y : ι → A)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    witnessIntersection I S x = witnessIntersection I S y := by
  unfold witnessIntersection
  apply Finset.prod_congr rfl
  intro w hw
  have hIw : I w x = I w y := hdepends w x y (by
    intro j hj
    apply hxy j
    intro hji
    exact hi (Finset.mem_biUnion.mpr ⟨w, hw, hji ▸ hj⟩))
  rw [hIw]

/-- A nonzero full mixed difference of the avoidance event forces a family
covering all singleton coordinates, positive in one common hybrid. -/
theorem mixedDifference_common_cover (support : W → Finset ι) (I : W → (ι → A) → Bool)
    (hdepends : ∀ w, DependsOn (support w) (I w)) (a x : ι → A)
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0) :
    ∃ S : Finset W, witnessSupport support S = Finset.univ ∧
      ∃ H : Finset ι, ∀ w ∈ S, I w (forceCoordinates H a x) = true := by
  have hexp : mixedDifference a (witnessAvoidance I) x =
      ∑ S : Finset W, (-1 : ℝ) ^ S.card * mixedDifference a (witnessIntersection I S) x := by
    have hf : witnessAvoidance I =
        (fun y => ∑ S : Finset W, (-1 : ℝ) ^ S.card * witnessIntersection I S y) :=
      funext (witnessAvoidance_expansion I)
    rw [hf, mixedDifference_sum]
    simp_rw [mixedDifference_const_mul]
  have hterm : ∃ S : Finset W, mixedDifference a (witnessIntersection I S) x ≠ 0 := by
    by_contra! hall
    apply hnonzero
    rw [hexp]
    simp only [hall, mul_zero, Finset.sum_const_zero]
  obtain ⟨S, hS⟩ := hterm
  have hcover : witnessSupport support S = Finset.univ := by
    by_contra hc
    have hex : ∃ i, i ∉ witnessSupport support S := by
      by_contra! hn
      exact hc (Finset.eq_univ_of_forall hn)
    obtain ⟨i, hi⟩ := hex
    exact hS (mixedDifference_eq_zero_of_ignores a (witnessIntersection I S) x i
      (witnessIntersection_ignores support I hdepends S i hi))
  obtain ⟨H, hH⟩ := exists_forced_value_ne_zero a (witnessIntersection I S) x hS
  refine ⟨S, hcover, H, ?_⟩
  intro w hw
  by_contra hIw
  have hz : witnessIntersection I S (forceCoordinates H a x) = 0 := by
    unfold witnessIntersection
    apply Finset.prod_eq_zero hw
    simp [Bool.eq_false_iff.mpr hIw]
  exact hH hz

/-- An inclusion-minimal finite cover has a private coordinate in every
member, and bounded support sizes bound its cardinality from below. -/
theorem exists_private_subcover (support : W → Finset ι) (S : Finset W)
    (hS : witnessSupport support S = Finset.univ) (B : ℕ)
    (hB : ∀ w ∈ S, (support w).card ≤ B) :
    ∃ R ⊆ S, witnessSupport support R = Finset.univ ∧
      Fintype.card ι ≤ R.card * B ∧
      ∀ w ∈ R, ∃ i ∈ support w, ∀ v ∈ R, v ≠ w → i ∉ support v := by
  classical
  have hex : ∃ n : ℕ, ∃ R ⊆ S, witnessSupport support R = Finset.univ ∧ R.card = n :=
    ⟨S.card, S, Finset.Subset.refl S, hS, rfl⟩
  obtain ⟨R, hRS, hcover, hcard⟩ := Nat.find_spec hex
  have hminimal (R' : Finset W) (hR' : R' ⊆ S) (hc : witnessSupport support R' = Finset.univ) :
      R.card ≤ R'.card := by
    have h := Nat.find_min' hex ⟨R', hR', hc, rfl⟩
    omega
  refine ⟨R, hRS, hcover, ?_, ?_⟩
  · calc
      Fintype.card ι = (witnessSupport support R).card := by rw [hcover, Finset.card_univ]
      _ ≤ ∑ w ∈ R, (support w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ R, B := Finset.sum_le_sum (fun w hw => hB w (hRS hw))
      _ = R.card * B := by simp
  · intro w hw
    by_contra hn
    push Not at hn
    have hdeleted : witnessSupport support (R.erase w) = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      have hi : i ∈ witnessSupport support R := by rw [hcover]; exact Finset.mem_univ _
      obtain ⟨v, hv, hiv⟩ := Finset.mem_biUnion.mp hi
      by_cases hvw : v = w
      · subst v
        obtain ⟨v, hvR, hvw, hiv⟩ := hn i hiv
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw, hvR⟩, hiv⟩
      · exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw, hv⟩, hiv⟩
    have hmin := hminimal (R.erase w) (Finset.erase_subset _ _ |>.trans hRS) hdeleted
    have hlt := Finset.card_erase_lt_of_mem hw
    omega

/-- Finite-parameter witness cover: enough singleton coordinates compared
with the maximum witness support yields `T` simultaneous witnesses with
pairwise distinct private marked coordinates. -/
theorem mixedDifference_private_witnesses (support : W → Finset ι) (I : W → (ι → A) → Bool)
    (hdepends : ∀ w, DependsOn (support w) (I w)) (a x : ι → A)
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0)
    (B T : ℕ) (hB : ∀ w, (support w).card ≤ B) (hT : T * B < Fintype.card ι) :
    ∃ R : Finset W, R.card = T ∧ ∃ H : Finset ι,
      (∀ w ∈ R, I w (forceCoordinates H a x) = true) ∧
      ∃ mark : R → ι, Function.Injective mark ∧
        ∀ w : R, mark w ∈ support w ∧ ∀ v ∈ R, v ≠ w → mark w ∉ support v := by
  classical
  obtain ⟨S, hS, H, hH⟩ := mixedDifference_common_cover support I hdepends a x hnonzero
  obtain ⟨Q, hQS, hcover, hcount, hprivate⟩ := exists_private_subcover support S hS B
    (fun w _ => hB w)
  have hTQ : T ≤ Q.card := by nlinarith
  obtain ⟨R, hRQ, hRcard⟩ := Finset.exists_subset_card_eq hTQ
  have hp (w : R) : ∃ i ∈ support w, ∀ v ∈ R, v ≠ w → i ∉ support v := by
    obtain ⟨i, hi, hnot⟩ := hprivate w (hRQ w.property)
    exact ⟨i, hi, fun v hv hne => hnot v (hRQ hv) hne⟩
  choose mark hmark using hp
  refine ⟨R, hRcard, H, (fun w hw => hH w (hQS (hRQ hw))), mark, ?_, hmark⟩
  intro u v huv
  by_contra hne
  have hmem : mark u ∈ support v := by rw [huv]; exact (hmark v).1
  exact (hmark u).2 v v.property (fun heq => hne (Subtype.ext heq.symm)) hmem

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSupport
namespace OAI

/-! Concrete prime supports of numerical witness words. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma mem_wordPrimeSupport (p : ℕ) (w : List SignedStep) :
    p ∈ wordPrimeSupport w ↔ ∃ a ∈ w, p ∈ a.tuple.primeFactors := by
  induction w with
  | nil => simp [wordPrimeSupport]
  | cons a w ih => simp only [wordPrimeSupport, mem_union, ih, List.mem_cons]; aesop

lemma mem_wordPrimeSupport_iff (p : ℕ) (w : List SignedStep)
    (hsq : ∀ a ∈ w, Squarefree a.tuple) :
    p ∈ wordPrimeSupport w ↔ ∃ i, TuplePrimeAt w p i := by
  rw [mem_wordPrimeSupport]
  constructor
  · rintro ⟨a, ha, hp⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hprime := Nat.mem_primeFactors.mp hp
    exact ⟨i, hprime.1, a, hi, hprime.2.1⟩
  · rintro ⟨i, hp, a, hi, hpa⟩
    have ha : a ∈ w := List.mem_iff_getElem?.mpr ⟨i, hi⟩
    exact ⟨a, ha, Nat.mem_primeFactors.mpr ⟨hp, hpa, (hsq a ha).ne_zero⟩⟩

lemma wordPrimeSupport_card_le (w : List SignedStep) (J : ℕ)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card ≤ J) :
    (wordPrimeSupport w).card ≤ w.length * J := by
  induction w with
  | nil => simp [wordPrimeSupport]
  | cons a w ih =>
      have hw := ih (fun b hb => hcard b (List.mem_cons_of_mem a hb))
      have ha := hcard a (List.mem_cons_self)
      calc
        (wordPrimeSupport (a :: w)).card ≤ a.tuple.primeFactors.card + (wordPrimeSupport w).card :=
          Finset.card_union_le _ _
        _ ≤ J + w.length * J := Nat.add_le_add ha hw
        _ = (a :: w).length * J := by simp [Nat.add_mul, Nat.add_comm]


lemma wordCoordinateSupport_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι → ℕ) (hinj : Function.Injective prime) (w : List SignedStep) (J : ℕ)
    (hcard : ∀ a ∈ w, a.tuple.primeFactors.card ≤ J) :
    (wordCoordinateSupport prime w).card ≤ w.length * J := by
  apply (Finset.card_le_card_of_injOn prime ?_ (fun _ _ _ _ heq => hinj heq)).trans
    (wordPrimeSupport_card_le w J hcard)
  intro i hi
  exact (Finset.mem_filter.mp hi).2

/-- Numerical witness words of length at most `s` have at most `s*J`
singleton coordinates in their support. -/
lemma bounded_wordCoordinateSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (prime : ι → ℕ) (hinj : Function.Injective prime) (w : List SignedStep) (s J : ℕ)
    (hlen : w.length ≤ s) (hcard : ∀ a ∈ w, a.tuple.primeFactors.card ≤ J) :
    (wordCoordinateSupport prime w).card ≤ s * J :=
  (wordCoordinateSupport_card_le prime hinj w J hcard).trans (Nat.mul_le_mul_right J hlen)

/-- The witness-cover conclusion with actual numerical words and actual
prime occurrences. Every selected word is positive in the same hybrid,
and its marked prime occurs in no other selected word. -/
theorem numerical_witness_cover {ι W A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype W] [DecidableEq W] (prime : ι → ℕ) (hinj : Function.Injective prime)
    (word : W → List SignedStep) (I : W → (ι → A) → Bool) (a x : ι → A)
    (hdepends : ∀ w, DependsOn (wordCoordinateSupport prime (word w)) (I w))
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0)
    (s J T : ℕ) (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card ≤ J)
    (hT : T * (s * J) < Fintype.card ι) :
    ∃ R : Finset W, R.card = T ∧ ∃ H : Finset ι,
      (∀ w ∈ R, I w (forceCoordinates H a x) = true) ∧
      ∃ mark : R → ι, Function.Injective mark ∧
        ∀ w : R, (∃ i, TuplePrimeAt (word w) (prime (mark w)) i) ∧
          ∀ v ∈ R, v ≠ w → ¬∃ i, TuplePrimeAt (word v) (prime (mark w)) i := by
  obtain ⟨R, hR, H, hI, mark, hinjmark, hmark⟩ :=
    mixedDifference_private_witnesses (fun w => wordCoordinateSupport prime (word w))
      I hdepends a x hnonzero (s * J) T
      (fun w => bounded_wordCoordinateSupport prime hinj (word w) s J (hlen w) (hcard w)) hT
  refine ⟨R, hR, H, hI, mark, hinjmark, ?_⟩
  intro w
  constructor
  · apply (mem_wordPrimeSupport_iff _ _ (hsq w)).mp
    exact (Finset.mem_filter.mp (hmark w).1).2
  · intro v hv hne hocc
    apply (hmark w).2 v hv hne
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (mem_wordPrimeSupport_iff _ _ (hsq v)).mpr hocc⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessOrdering
namespace OAI

/-! Private witnesses can be indexed by increasing attachment, including ties. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma exists_monotone_enumeration {W : Type*} [Fintype W]
    (attachment : W → ℕ) (n : ℕ) (hcard : Fintype.card W = n) :
    ∃ e : Fin n ≃ W, Monotone (fun i => attachment (e i)) := by
  classical
  let e₀ : Fin n ≃ W := (Fintype.equivFinOfCardEq hcard).symm
  let f : Fin n → ℕ := fun i => attachment (e₀ i)
  exact ⟨(Tuple.sort f).trans e₀, Tuple.monotone_sort f⟩

/-- The cover is enumerated after selection, so sorting introduces no
factor counting all covering subfamilies or possible hybrid choices. -/
theorem ordered_numerical_witness_cover {ι W A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (prime : ι → ℕ) (hinj : Function.Injective prime)
    (word : W → List SignedStep) (attachment : W → ℕ)
    (I : W → (ι → A) → Bool) (a x : ι → A)
    (hdepends : ∀ w, DependsOn (wordCoordinateSupport prime (word w)) (I w))
    (hnonzero : mixedDifference a (witnessAvoidance I) x ≠ 0)
    (s J T : ℕ) (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card ≤ J)
    (hT : T * (s * J) < Fintype.card ι) :
    ∃ index : Fin T → W, Function.Injective index ∧
      Monotone (fun i => attachment (index i)) ∧ ∃ H : Finset ι,
      (∀ i, I (index i) (forceCoordinates H a x) = true) ∧
      ∃ mark : Fin T → ι, Function.Injective mark ∧
        ∀ i, (∃ r, TuplePrimeAt (word (index i)) (prime (mark i)) r) ∧
          ∀ j, j ≠ i → ¬∃ r, TuplePrimeAt (word (index j)) (prime (mark i)) r := by
  classical
  obtain ⟨R, hR, H, hI, mark, hmark, hprivate⟩ := numerical_witness_cover
    prime hinj word I a x hdepends hnonzero s J T hlen hsq hcard hT
  obtain ⟨e, he⟩ := exists_monotone_enumeration (fun i : R => attachment i.val) T
    (by simpa only [Fintype.card_coe] using hR)
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, he, H,
    fun i => hI (e i) (e i).property, fun i => mark (e i), hmark.comp e.injective, ?_⟩
  intro i
  refine ⟨(hprivate (e i)).1, ?_⟩
  intro j hji
  apply (hprivate (e i)).2 (e j) (e j).property
  exact fun hij => hji (e.injective (Subtype.ext hij))

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteSupportAverage
namespace OAI

/-! A bounded function pays the probability of its actual nonzero support. -/

namespace TwoPointCorrelations

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueWordDependence
namespace OAI

/-! The actual attached-word residue tests depend only on their tuple singleton primes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma divisor_prime_in_word_support (w : List SignedStep) (p : ℕ) (hp : p.Prime)
    (hsq : ∀ t ∈ w, Squarefree t.tuple) (hpad : ∀ t ∈ w, ¬p ∣ t.padding)
    (k : Fin w.length) (hk : p ∈ ((w.get k).padding * (w.get k).tuple).primeFactors) :
    p ∈ wordPrimeSupport w := by
  have ht : w.get k ∈ w := List.get_mem w k
  have hd := (Nat.mem_primeFactors.mp hk).2.1
  have hdt : p ∣ (w.get k).tuple := (hp.dvd_mul.mp hd).resolve_left (hpad _ ht)
  exact (mem_wordPrimeSupport p w).mpr
    ⟨w.get k, ht, Nat.mem_primeFactors.mpr ⟨hp, hdt, (hsq _ ht).ne_zero⟩⟩

/-- Freeze all other coordinates, including every padding prime. -/
lemma attached_residue_test_depends {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (p : ι → ℕ) (h B : ℕ) (w : List SignedStep) (attachment : ℤ)
    (hsq : ∀ t ∈ w, Squarefree t.tuple)
    (hprime : ∀ i ∈ S, (p i).Prime) (hpad : ∀ i ∈ S, ∀ t ∈ w, ¬p i ∣ t.padding)
    (outside : {i // i ∉ S} → Fin B) :
    DependsOn (wordCoordinateSupport (fun i : S => p i) w)
      (fun z : S → Fin B => decide (AttachedResiduePositiveWord p h w attachment B
        (joinCoordinates S z outside))) := by
  intro z z' hzz
  apply decide_eq_decide.mpr
  have he (k : Fin w.length) (i : ι)
      (hi : p i ∈ ((w.get k).padding * (w.get k).tuple).primeFactors) :
      joinCoordinates S z outside i = joinCoordinates S z' outside i := by
    by_cases his : i ∈ S
    · have hpw := divisor_prime_in_word_support w (p i) (hprime i his) hsq (hpad i his) k hi
      have hz := hzz ⟨i, his⟩ (mem_filter.mpr ⟨mem_univ _, hpw⟩)
      simpa only [joinCoordinates, his, dite_true] using hz
    · simp only [joinCoordinates, his, dite_false]
  constructor
  · intro hz k i hi
    rw [← he k i hi]
    exact hz k i hi
  · intro hz k i hi
    rw [he k i hi]
    exact hz k i hi

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.AttachedResidueLift
namespace OAI

/-! One common integer realizes every attached numerical witness in a hybrid sample. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

theorem attached_residue_words_common_origin {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n B h : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (x : ι → Fin B) (word : Fin n → List SignedStep) (attachment : Fin n → ℤ)
    (hsq : ∀ j t, t ∈ word j → Squarefree (t.padding * t.tuple))
    (hcover : ∀ j q, q ∈ wordDivisorPrimeSupport (word j) → ∃ i, p i = q)
    (htest : ∀ j, AttachedResiduePositiveWord p h (word j) (attachment j) B x) :
    ∃ origin : ℤ, ∀ j, PositiveWord h (origin + attachment j) (word j) := by
  let (i : ι) : NeZero (p i) := ⟨(hprime i).ne_zero⟩
  have hcop : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun he => hij (hinj he))
  let r (i : ι) : ZMod (p i) := ((x i).val : ZMod (p i))
  obtain ⟨origin, horigin⟩ := exists_common_integer_residue p hcop r
  refine ⟨origin, ?_⟩
  intro j
  let rj (i : ι) : ZMod (p i) := r i + (attachment j : ZMod (p i))
  have hj : ∀ i, ((origin + attachment j : ℤ) : ZMod (p i)) = rj i := by
    intro i
    simp only [Int.cast_add, horigin, rj]
  apply (residuePositiveWord_iff p h (word j) rj (origin + attachment j)
    hj (hsq j) (hcover j)).mp
  intro k i hi
  have ht := htest j k i hi
  change r i = -((attachment j + wordDisplacement h ((word j).take k.val) : ℤ) : ZMod (p i)) at ht
  rw [Int.cast_add] at ht
  change r i + (attachment j : ZMod (p i)) = _
  rw [ht]
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RetainedWitnessProbability
namespace OAI

/-! A common hybrid pays one reciprocal for each new witness prime, without counting hybrids. -/

namespace TwoPointCorrelations

open _root_.Finset
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

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordResampling
namespace OAI

/-! Numerical resampling preserves the symbolic witness relations. -/

namespace TwoPointCorrelations

open _root_.Finset

namespace LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]





omit [DecidableEq ι] in
lemma resample_realizes (w : LabeledPrimeWord ι) (value : ι → ℕ) :
    (w.resample value).Realizes value := by
  intro i
  simp [resample, List.getElem_ofFn]


end LabeledPrimeWord

variable {ι : Type*} [DecidableEq ι]



namespace WitnessSystemData

variable {n N : ℕ}




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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotClasses
namespace OAI

/-! Tuple classes can be resampled while all padding classes remain fixed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace CrudeWordCode

variable {R N : ℕ}






lemma classAt_mem_tupleClasses (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (j : Fin N) (hj : c.2.2.2 j = false) : c.classAt j ∈ c.tupleClasses := by
  simp only [tupleClasses, mem_filter, mem_univ, true_and, classAt]
  exact (hc j).trans hj

lemma classAt_notMem_tupleClasses (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (j : Fin N) (hj : c.2.2.2 j = true) : c.classAt j ∉ c.tupleClasses := by
  simp only [tupleClasses, mem_filter, mem_univ, true_and, classAt]
  rw [hc j, hj]
  decide

/-- Rowwise squarefreeness makes the tuple product a product over its classes. -/
lemma tuple_product (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (hi : c.RowInjective) (i : Fin R) (a : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (∏ j ∈ c.recordedSlots i false,
      joinCoordinates c.tupleClasses a b (c.classAt j)) =
        ∏ z ∈ c.tupleLabels i, a z := by
  let f (j : Fin N) (hj : j ∈ c.recordedSlots i false) : c.tupleClasses :=
    ⟨c.classAt j, c.classAt_mem_tupleClasses hc j (mem_filter.mp hj).2.2⟩
  apply prod_bij f
  · intro j hj
    exact mem_subtype.mpr (mem_image.mpr ⟨j, hj, rfl⟩)
  · intro j hj k hk he
    exact hi i false hj hk (congrArg (fun z : c.tupleClasses => z.val.val) he)
  · intro z hz
    obtain ⟨j, hj, he⟩ := mem_image.mp (mem_subtype.mp hz)
    exact ⟨j, hj, Subtype.ext he⟩
  · intro j hj
    exact joinCoordinates_mem c.tupleClasses a b (f j hj)

lemma padding_product (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (i : Fin R) (a a' : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (∏ j ∈ c.recordedSlots i true, joinCoordinates c.tupleClasses a b (c.classAt j)) =
      ∏ j ∈ c.recordedSlots i true, joinCoordinates c.tupleClasses a' b (c.classAt j) := by
  apply prod_congr rfl
  intro j hj
  have hn := c.classAt_notMem_tupleClasses hc j (mem_filter.mp hj).2.2
  simp only [joinCoordinates, hn, dite_false]


lemma labeledWord_length (c : CrudeWordCode R N R)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (c.labeledWord b).word.length = R := c.numericalWord_length _

/-- Resampling changes exactly the tuple primes, with no additional padding choices. -/
theorem labeledWord_resample (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (hi : c.RowInjective) (a : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    ((c.labeledWord b).resample a).word =
      c.numericalWord (joinCoordinates c.tupleClasses a b) := by
  apply List.ext_getElem
  · rw [LabeledPrimeWord.resample_length, labeledWord_length, numericalWord_length]
  · intro i hi₁ hi₂
    have hiR : i < R := by simpa only [numericalWord_length] using hi₂
    let j : Fin R := ⟨i, hiR⟩
    have hp := c.padding_product hc j (fun _ => 1) a b
    have ht := c.tuple_product hc hi j a b
    have hf := c.numericalWord_get (joinCoordinates c.tupleClasses (fun _ => 1) b) j
    simp only [LabeledPrimeWord.resample, List.getElem_ofFn, labeledWord]
    rw [c.numericalWord_get _ j]
    congr 1
    · exact congrArg SignedStep.forward hf
    · exact ht.symm
    · exact (congrArg SignedStep.padding hf).trans hp

end CrudeWordCode

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualSlotClasses
namespace OAI

/-! Actual squarefree prime occurrences satisfy the code's class conditions. -/

namespace TwoPointCorrelations

open _root_.Finset
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

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueWitnessHybrid
namespace OAI

/-! Keep the same common hybrid that supplies the numerical witnesses. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem selected_residue_witnesses_and_hybrid {ι W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (S : Finset ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J T : ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (a x : ι → Fin B)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hsq : ∀ w t, t ∈ word w → Squarefree t.tuple)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ S, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : S → ℕ)
    (hmain : ∀ i : S, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (hnonzero : selectedMixedDifference S a
      (witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B z))) x ≠ 0)
    (hT : T * (s * J) < S.card) :
    ∃ index : Fin T → W, Function.Injective index ∧
      NumericalWitnessEvent main (fun i => word (index i)) p h s J supply ∧
      ∃ y : ι → Fin B, (∀ i, i ∉ S → y i = x i) ∧
        ∀ i, AttachedResiduePositiveWord p h (word (index i))
          (wordDisplacement h (main.take (attachment (index i)))) B y := by
  let I : W → (S → Fin B) → Bool := fun w z => decide
    (AttachedResiduePositiveWord p h (word w)
      (wordDisplacement h (main.take (attachment w))) B
      (joinCoordinates S z (fun i => x i)))
  have hdepends (w) : DependsOn (wordCoordinateSupport (fun i : S => p i) (word w)) (I w) :=
    attached_residue_test_depends S p h B (word w) _ (hsq w)
      (fun i _ => hprime i) (fun i hi => hpad i hi w) _
  have hn : mixedDifference (fun i : S => a i) (witnessAvoidance I) (fun i : S => x i) ≠ 0 :=
    hnonzero
  obtain ⟨index, hindex, horder, H, hI, mark, _hmark, hprivate⟩ :=
    ordered_numerical_witness_cover (fun i : S => p i) (hinj.comp Subtype.val_injective)
      word attachment I (fun i : S => a i) (fun i : S => x i) hdepends hn s J T hlen hsq
      (fun w t ht => (hcard w t ht).le) (by simpa only [Fintype.card_coe] using hT)
  let hybrid := joinCoordinates S (forceCoordinates H (fun i : S => a i) (fun i : S => x i))
    (fun i => x i)
  have htests (i : Fin T) : AttachedResiduePositiveWord p h (word (index i))
      (wordDisplacement h (main.take (attachment (index i)))) B hybrid := by
    have hi := hI i
    exact of_decide_eq_true hi
  obtain ⟨origin, horigin⟩ := attached_residue_words_common_origin T B h p hprime hinj hybrid
    (fun i => word (index i)) (fun i => wordDisplacement h (main.take (attachment (index i))))
    (fun i => hdivsq (index i)) (fun i => hcover (index i)) htests
  refine ⟨index, hindex, ?_, hybrid, ?_, htests⟩
  · refine ⟨(fun i => (mark i).val), (fun i => attachment (index i)),
      (fun i => position (mark i)), horder, (fun i => hatt (index i)), hinj, hprime,
      (fun i => hminimal (index i)), (fun i => hsq (index i)), (fun i => hcard (index i)),
      (fun i => hsupport (index i)), ?_, ?_, ?_, origin, horigin⟩
    · intro i
      exact (mem_wordPrimeSupport_iff _ _ (hsq (index i))).mpr (hprivate i).1
    · intro i j hji hmem
      exact (hprivate i).2 j hji ((mem_wordPrimeSupport_iff _ _ (hsq (index j))).mp hmem)
    · intro i v hv
      exact hmain (mark i) v hv
  · intro i hi
    simp only [hybrid, joinCoordinates, hi, dite_false]

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


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedPrimeSupport
namespace OAI

/-! Every prime used by a numerical encoding lies in its declared finite pools. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem PrimeWordEncoding.divisor_support_subset {R T : ℕ} {P Q : Finset ℕ}
    (e : PrimeWordEncoding R T P Q)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) :
    wordDivisorPrimeSupport e.decode ⊆ P ∪ Q := by
  let c := e.2.1
  let value := joinCoordinates c.tupleClasses
    (fun z => (e.2.2.1 z).val) (fun z => (e.2.2.2 z).val)
  have hv (z : c.usedClasses) : value z ∈ P ∪ Q := by
    by_cases hz : z ∈ c.tupleClasses
    · exact mem_union_left _ (by simpa only [value, joinCoordinates, hz, dite_true]
        using (e.2.2.1 ⟨z, hz⟩).property)
    · exact mem_union_right _ (by simpa only [value, joinCoordinates, hz, dite_false]
        using (e.2.2.2 ⟨z, hz⟩).property)
  have hpv (z : c.usedClasses) : (value z).Prime := by
    rcases mem_union.mp (hv z) with hz | hz
    · exact hP _ hz
    · exact hQ _ hz
  intro q hq
  have hm : ∃ i : Fin R, q ∈
      ((c.primeData value).factor i true * (c.primeData value).factor i false).primeFactors := by
    change q ∈ wordDivisorPrimeSupport (c.primeData value).word at hq
    simpa only [wordDivisorPrimeSupport, PrimeSlotData.word, mem_biUnion,
      List.mem_toFinset, List.mem_ofFn, exists_exists_eq_and] using hq
  obtain ⟨i, hi⟩ := hm
  have hprime := (Nat.mem_primeFactors.mp hi).1
  have hdvd := (Nat.mem_primeFactors.mp hi).2.1
  have hf (b : Bool) (hd : q ∣ (c.primeData value).factor i b) : q ∈ P ∪ Q := by
    obtain ⟨j, _, hj⟩ := (hprime.prime.dvd_finsetProd_iff
      (c.primeData value).prime).mp hd
    have he : q = value (c.classAt j) :=
      (Nat.prime_dvd_prime_iff_eq hprime (hpv (c.classAt j))).mp hj
    rw [he]
    exact hv _
  rcases hprime.dvd_mul.mp hdvd with hd | hd
  · exact hf true hd
  · exact hf false hd

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessRelabel
namespace OAI

/-! Restrict the numerical witness event to the observed tuple-prime labels. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

theorem NumericalWitnessEvent.relabel {n : ℕ} {ι κ : Type*}
    {main : List SignedStep} {word : Fin n → List SignedStep}
    {p : ι → ℕ} {h s J : ℕ} {supply : ℕ → ℕ → Prop}
    (he : NumericalWitnessEvent main word p h s J supply)
    (q : κ → ℕ) (hq : Function.Injective q) (hprime : ∀ j, (q j).Prime)
    (hcover : ∀ i r, r ∈ wordPrimeSupport (word i) → ∃ j, q j = r) :
    NumericalWitnessEvent main word q h s J supply := by
  obtain ⟨mark, attachment, position, horder, hbound, _hp, _hprime,
    hminimal, hsq, hcard, hsupport, hmark, hprivate, hmain, origin, hpositive⟩ := he
  have hex (i : Fin n) : ∃ j, q j = p (mark i) := hcover i _ (hmark i)
  choose mark' hmark' using hex
  refine ⟨mark', attachment, position, horder, hbound, hq, hprime,
    hminimal, hsq, hcard, hsupport, ?_, ?_, ?_, origin, hpositive⟩
  · intro i
    rw [hmark' i]
    exact hmark i
  · intro i j hji
    rw [hmark' i]
    exact hprivate i j hji
  · intro i v hv
    rw [hmark' i] at hv
    exact hmain i v hv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NumericalWitnessEncoding
namespace OAI

/-! Actual numerical witness families are covered by the prime-slot catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma LabeledPrimeWord.realizes_support_covered {ι : Type*} [DecidableEq ι]
    (w : LabeledPrimeWord ι) (value : ι → ℕ) (hw : w.Realizes value)
    (hprime : ∀ i, (value i).Prime) (r : ℕ) (hr : r ∈ wordPrimeSupport w.word) :
    ∃ i, value i = r := by
  obtain ⟨t, ht, hr⟩ := (mem_wordPrimeSupport r w.word).mp hr
  obtain ⟨k, hk⟩ := List.get_of_mem ht
  have hpr := (Nat.mem_primeFactors.mp hr).1
  have hdvd := (Nat.mem_primeFactors.mp hr).2.1
  have htup : (∏ i ∈ w.labels k, value i) = t.tuple := (hw k).trans (congrArg SignedStep.tuple hk)
  rw [← htup] at hdvd
  obtain ⟨i, _, hi⟩ := (hpr.prime.dvd_finsetProd_iff value).mp hdvd
  exact ⟨i, ((Nat.prime_dvd_prime_iff_eq hpr (hprime i)).mp hi).symm⟩

lemma wordPrimeSupport_mono {v w : List SignedStep}
    (hvw : ∀ t ∈ v, t ∈ w) : wordPrimeSupport v ⊆ wordPrimeSupport w := by
  intro p hp
  obtain ⟨t, ht, hpt⟩ := (mem_wordPrimeSupport p v).mp hp
  exact (mem_wordPrimeSupport p w).mpr ⟨t, hvw t ht, hpt⟩

lemma PrimeWordEncoding.tuple_support_covered {R T : ℕ} {P Q : Finset ℕ}
    (e : PrimeWordEncoding R T P Q) (hc : e.2.1.KindConsistent)
    (hi : e.2.1.RowInjective) (hP : ∀ p ∈ P, p.Prime)
    (r : ℕ) (hr : r ∈ wordPrimeSupport e.decode) :
    ∃ z, (e.2.2.1 z).val = r := by
  let a := fun z => (e.2.2.1 z).val
  let b := fun z => (e.2.2.2 z).val
  have he := e.2.1.labeledWord_resample hc hi a b
  apply ((e.2.1.labeledWord b).resample a).realizes_support_covered a
    ((e.2.1.labeledWord b).resample_realizes a) (fun z => hP _ (e.2.2.1 z).property) r
  rw [he]
  exact hr

theorem PrimeWordEncoding.covers_witnesses {R T n : ℕ} {P Q : Finset ℕ}
    (w : Fin R → SignedStep)
    (hT : Fintype.card (ActualPrimeSlot w) ≤ T)
    (ht : ∀ i, Squarefree (w i).tuple) (hq : ∀ i, Squarefree (w i).padding)
    (hP : ∀ i, (w i).tuple.primeFactors ⊆ P)
    (hQ : ∀ i, (w i).padding.primeFactors ⊆ Q)
    (hd : ∀ i j, Disjoint (w i).tuple.primeFactors (w j).padding.primeFactors)
    (hprime : ∀ p ∈ P, p.Prime)
    (mainLength : ℕ) (start len : Fin n → ℕ) (h s J : ℕ) (supply : ℕ → ℕ → Prop)
    {ι : Type*} (p : ι → ℕ)
    (hnum : NumericalWitnessEvent ((List.ofFn w).take mainLength)
      (fun i => ((List.ofFn w).drop (start i)).take (len i)) p h s J supply) :
    ∃ e : PrimeWordEncoding R T P Q, e.Witnesses n mainLength start len h s J supply ∧
      e.decode = List.ofFn w ∧
      e.weight = ∏ q ∈ wordDivisorPrimeSupport (List.ofFn w), (q : ℝ)⁻¹ := by
  obtain ⟨e, he, hc, hi, hinj, hweight⟩ := covers w hT ht hq hP hQ hd
  have hnum' : NumericalWitnessEvent (e.decode.take mainLength)
      (fun i => (e.decode.drop (start i)).take (len i)) p h s J supply := by
    simpa only [he] using hnum
  have hcover (i : Fin n) (r : ℕ)
      (hr : r ∈ wordPrimeSupport ((e.decode.drop (start i)).take (len i))) :
      ∃ z, (e.2.2.1 z).val = r := by
    apply e.tuple_support_covered hc hi hprime r
    apply wordPrimeSupport_mono (fun t ht => List.mem_of_mem_drop (List.mem_of_mem_take ht)) hr
  exact ⟨e, ⟨hc, hi, hnum'.relabel _ hinj (fun z => hprime _ (e.2.2.1 z).property) hcover⟩,
    he, hweight⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.RecordedWitnessSegments
namespace OAI

/-! Every actual main/witness family is represented in the finite segment catalog. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


theorem recorded_witness_segments {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) :
    ∃ d : WitnessSegmentation n (recordedWitnessWord main word).length,
      (recordedWitnessWord main word).take d.1.val = main ∧
      ∀ i, ((recordedWitnessWord main word).drop (d.2.1 i).val).take (d.2.2 i).val = word i := by
  let v := recordedWitnessWord main word
  have hmain : main.length ≤ v.length := by simp [v, recordedWitnessWord]
  have hseg (i : Fin n) : ∃ start len : Fin (v.length + 1),
      (v.drop start.val).take len.val = word i := by
    obtain ⟨before, after, he⟩ := List.mem_iff_append.mp
      (List.mem_ofFn.mpr ⟨i, rfl⟩ : word i ∈ List.ofFn word)
    let preword := main ++ before.flatten
    have hv : v = preword ++ (word i ++ after.flatten) := by
      simp only [v, recordedWitnessWord, he, List.flatten_append, List.flatten_cons,
        preword, List.append_assoc]
    have hs : preword.length ≤ v.length := by rw [hv]; simp
    have hl : (word i).length ≤ v.length := by rw [hv]; simp; omega
    refine ⟨⟨preword.length, by omega⟩, ⟨(word i).length, by omega⟩, ?_⟩
    change (v.drop preword.length).take (word i).length = word i
    rw [hv, List.drop_left, List.take_left]
  choose start len hsegments using hseg
  refine ⟨(⟨main.length, Nat.lt_succ_of_le hmain⟩, start, len), ?_, hsegments⟩
  exact List.take_left

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.AttachedWitnessCatalog
namespace OAI

/-! The residue test also records the attachment positions on the main path. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical




theorem recorded_witness_record {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (attachment : Fin n → ℕ)
    (hattachment : ∀ i, attachment i ≤ main.length) :
    ∃ d : WitnessRecord n (recordedWitnessWord main word).length,
      (recordedWitnessWord main word).take d.1.1.val = main ∧
      (∀ i, ((recordedWitnessWord main word).drop (d.1.2.1 i).val).take
        (d.1.2.2 i).val = word i) ∧ ∀ i, (d.2 i).val = attachment i := by
  obtain ⟨d, hd, hw⟩ := recorded_witness_segments main word
  have hmain : main.length ≤ (recordedWitnessWord main word).length := by
    simp [recordedWitnessWord]
  exact ⟨(d, fun i => ⟨attachment i, Nat.lt_succ_of_le ((hattachment i).trans hmain)⟩),
    hd, hw, fun _ => rfl⟩


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualWitnessRecord
namespace OAI

/-! Encode an actual attached witness family without adding any numerical choices. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem actual_witness_has_encoded_record {n : ℕ} {ι : Type*}
    (main : List SignedStep) (word : Fin n → List SignedStep)
    (attachment : Fin n → ℕ) (hatt : ∀ i, attachment i ≤ main.length)
    (P Q : Finset ℕ) (T h s J : ℕ) (supply : ℕ → ℕ → Prop) (p : ι → ℕ)
    (hnum : NumericalWitnessEvent main word p h s J supply)
    (hT : Fintype.card (ActualPrimeSlot (recordedWitnessWord main word).get) ≤ T)
    (ht : ∀ t ∈ recordedWitnessWord main word, Squarefree t.tuple)
    (hq : ∀ t ∈ recordedWitnessWord main word, Squarefree t.padding)
    (hP : ∀ t ∈ recordedWitnessWord main word, t.tuple.primeFactors ⊆ P)
    (hQ : ∀ t ∈ recordedWitnessWord main word, t.padding.primeFactors ⊆ Q)
    (hd : ∀ t ∈ recordedWitnessWord main word, ∀ u ∈ recordedWitnessWord main word,
      Disjoint t.tuple.primeFactors u.padding.primeFactors)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∃ d : WitnessRecord n (recordedWitnessWord main word).length,
      ∃ e : PrimeWordEncoding (recordedWitnessWord main word).length T P Q,
        e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply ∧
        e.decode = recordedWitnessWord main word ∧
        e.decode.take d.1.1.val = main ∧
        (∀ i, (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val = word i) ∧
        (∀ i, (d.2 i).val = attachment i) ∧
        e.weight = ∏ q ∈ wordDivisorPrimeSupport e.decode, (q : ℝ)⁻¹ := by
  let v := recordedWitnessWord main word
  obtain ⟨d, hdmain, hdword, hdatt⟩ := recorded_witness_record main word attachment hatt
  have hnum' : NumericalWitnessEvent ((List.ofFn v.get).take d.1.1.val)
      (fun i => ((List.ofFn v.get).drop (d.1.2.1 i).val).take (d.1.2.2 i).val)
      p h s J supply := by
    simpa only [List.ofFn_get, v, hdmain, hdword] using hnum
  obtain ⟨e, he, hdecode, hweight⟩ := PrimeWordEncoding.covers_witnesses v.get hT
    (fun i => ht _ (List.get_mem v i)) (fun i => hq _ (List.get_mem v i))
    (fun i => hP _ (List.get_mem v i)) (fun i => hQ _ (List.get_mem v i))
    (fun i j => hd _ (List.get_mem v i) _ (List.get_mem v j)) hprime
    d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
    h s J supply p hnum'
  rw [List.ofFn_get] at hdecode hweight
  refine ⟨d, e, he, hdecode, ?_, ?_, hdatt, ?_⟩
  · simpa only [hdecode] using hdmain
  · intro i
    simpa only [hdecode] using hdword i
  · simpa only [hdecode] using hweight

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


theorem retainedMainTests_congr {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (x y : ι → Fin B) (hxy : ∀ i, i ∉ S → x i = y i) :
    RetainedMainTests p S h B main x ↔ RetainedMainTests p S h B main y := by
  constructor
  · intro hx i hi k hk
    rw [← hxy i hi]
    exact hx i hi k hk
  · intro hy i hi k hk
    rw [hxy i hi]
    exact hy i hi k hk

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference
namespace OAI

/-! Forcing lit nonsingletons commutes with singleton differences; padding stays outside them. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem selectedMixedDifference_invariant_factor {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (S M : Finset ι) (hSM : S ⊆ M) (a x : ι → A)
    (R F : (ι → A) → ℝ)
    (hR : ∀ y z, (∀ i, i ∉ M → y i = z i) → R y = R z) :
    selectedMixedDifference S a (fun y => R y * F y) x =
      R x * selectedMixedDifference S a F x := by
  have hsame (z : S → A) :
      R (joinCoordinates S z (fun i : {i // i ∉ S} => x i)) = R x := by
    apply hR
    intro i hi
    have hiS : i ∉ S := fun his => hi (hSM his)
    simp only [joinCoordinates, hiS, dite_false]
  unfold selectedMixedDifference
  simp_rw [hsame]
  exact mixedDifference_const_mul _ _ _ _

theorem selectedMixedDifference_force_disjoint {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [DecidableEq A] (S T : Finset ι) (hST : Disjoint S T)
    (a b x : ι → A) (F : (ι → A) → ℝ) :
    selectedMixedDifference S a (fun y => F (forceCoordinates T b y)) x =
      selectedMixedDifference S a F (forceCoordinates T b x) := by
  have hcomm (z : S → A) :
      forceCoordinates T b (joinCoordinates S z (fun i : {i // i ∉ S} => x i)) =
        joinCoordinates S z (fun i : {i // i ∉ S} => forceCoordinates T b x i) := by
    funext i
    by_cases hiS : i ∈ S
    · have hiT : i ∉ T := fun hiT => disjoint_left.mp hST hiS hiT
      simp only [forceCoordinates_apply, hiT, ite_false, joinCoordinates, hiS, dite_true]
    · simp only [joinCoordinates, hiS, dite_false, forceCoordinates_apply]
  have hx : (fun i : S => forceCoordinates T b x i) = (fun i : S => x i) := by
    funext i
    have hiT : i.val ∉ T := fun hiT => disjoint_left.mp hST i.property hiT
    simp only [forceCoordinates_apply, hiT, ite_false]
  unfold selectedMixedDifference
  simp_rw [hcomm]
  rw [hx]


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MainPaddingTests
namespace OAI

/-! The actual main-word padding tests imply all tests retained after tuple centering. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem mainPaddingTests_retained {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep) (x : ι → Fin B)
    (hpad : ∀ t ∈ main, t.padding ≠ 0) (htuple : ∀ t ∈ main, t.tuple ≠ 0)
    (hcover : ∀ (k : Fin main.length) i, p i ∈ (main.get k).tuple.primeFactors → i ∈ S)
    (hx : MainPaddingTests p h B main x) : RetainedMainTests p S h B main x := by
  intro i hi k hk
  rw [Nat.primeFactors_mul (hpad _ (List.get_mem main k))
    (htuple _ (List.get_mem main k)), mem_union] at hk
  rcases hk with hk | hk
  · exact hx k i hk
  · exact (hi (hcover k i hk)).elim

theorem mainPaddingTests_congr {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (hsep : ∀ (k : Fin main.length) i, p i ∈ (main.get k).padding.primeFactors → i ∉ S)
    (x y : ι → Fin B) (hxy : ∀ i, i ∉ S → x i = y i) :
    MainPaddingTests p h B main x ↔ MainPaddingTests p h B main y := by
  constructor
  · intro hx k i hi
    rw [← hxy i (hsep k i hi)]
    exact hx k i hi
  · intro hy k i hi
    rw [hxy i (hsep k i hi)]
    exact hy k i hi


lemma paddingWeightedFunction_nonneg {ι : Type*} (p : ι → ℕ)
    (h B : ℕ) (main : List SignedStep) (R : (ι → Fin B) → ℝ)
    (hR : ∀ x, 0 ≤ R x) (x : ι → Fin B) :
    0 ≤ paddingWeightedFunction p h B main R x := by
  unfold paddingWeightedFunction
  split_ifs
  · exact hR x
  · exact le_rfl

lemma paddingWeightedFunction_le {ι : Type*} (p : ι → ℕ)
    (h B : ℕ) (main : List SignedStep) (R : (ι → Fin B) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hR : ∀ x, R x ≤ C) (x : ι → Fin B) :
    paddingWeightedFunction p h B main R x ≤ C := by
  unfold paddingWeightedFunction
  split_ifs
  · exact hR x
  · exact hC

theorem paddingWeightedFunction_retained {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (R : (ι → Fin B) → ℝ) (x : ι → Fin B)
    (hpad : ∀ t ∈ main, t.padding ≠ 0) (htuple : ∀ t ∈ main, t.tuple ≠ 0)
    (hcover : ∀ (k : Fin main.length) i, p i ∈ (main.get k).tuple.primeFactors → i ∈ S)
    (hx : paddingWeightedFunction p h B main R x ≠ 0) :
    RetainedMainTests p S h B main x := by
  apply mainPaddingTests_retained p S h B main x hpad htuple hcover
  by_contra hn
  exact hx (if_neg hn)

theorem paddingWeightedFunction_invariant {ι : Type*} [DecidableEq ι]
    (p : ι → ℕ) (S : Finset ι) (h B : ℕ) (main : List SignedStep)
    (R : (ι → Fin B) → ℝ)
    (hsep : ∀ (k : Fin main.length) i, p i ∈ (main.get k).padding.primeFactors → i ∉ S)
    (hR : ∀ x y, (∀ i, i ∉ S → x i = y i) → R x = R y)
    (x y : ι → Fin B) (hxy : ∀ i, i ∉ S → x i = y i) :
    paddingWeightedFunction p h B main R x = paddingWeightedFunction p h B main R y := by
  unfold paddingWeightedFunction
  rw [mainPaddingTests_congr p S h B main hsep x y hxy, hR x y hxy]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedCenteredWord
namespace OAI

/-! Keep the nonnegative weight inside the expectation when it is independent of tuple residues. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem uniform_weighted_centered_word_majorant {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x)
    (hRdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → R x = R y) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R x * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        if LitConsistent (nonsingletonSlots label \ U) label target then
          designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
            (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
              (fun x => R x * |selectedMixedDifference (singletonLabels label)
                (singletonTarget label target base)
                (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
                  (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|)
        else 0 := by
  have hS : singletonLabels label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, ht⟩ := singleton_occurrence_exists label ⟨i, hi⟩
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  have hforce (U : Finset τ) (x : ι → Fin B) :
      R (forceCoordinates ((nonsingletonSlots label \ U).image label)
        (litForcedTarget (nonsingletonSlots label \ U) label target base) x) = R x := by
    apply hRdep
    intro i hi
    have hiT : i ∉ (nonsingletonSlots label \ U).image label := by
      intro hit
      obtain ⟨t, _, ht⟩ := mem_image.mp hit
      exact hi (mem_image.mpr ⟨t, mem_univ _, ht⟩)
    simp only [forceCoordinates_apply, hiT, ite_false]
  have hdelta (U : Finset τ) (x : ι → Fin B) :
      selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
        (fun y => R (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y) *
          G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x =
      R x * selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
        (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x := by
    simp_rw [hforce]
    exact selectedMixedDifference_invariant_factor _ _ hS _ x R _ hRdep
  have he : (fun x => R x * (∏ t,
      ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x) =
      (fun x => (1 : ℝ) * (∏ t,
      ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * (R x * G x)) := by
    funext x
    ring
  rw [he]
  apply (uniform_centered_word_majorant B p hp hpB label target base htarget
    1 (by norm_num) (fun x => R x * G x)).trans_eq
  apply sum_congr rfl
  intro U _
  split_ifs
  · simp only [one_mul, hdelta, abs_mul, abs_of_nonneg (hR _)]
  · rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WeightedWordEnvelope
namespace OAI

/-! A single positive envelope for all lit designations of a weighted centered word. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma centeredWordEnvelope_nonneg {ι τ A : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (hR : ∀ x, 0 ≤ R x) (x : ι → A) :
    0 ≤ centeredWordEnvelope label target base R G x := by
  apply sum_nonneg
  intro U _
  split_ifs
  · exact mul_nonneg (hR x) (abs_nonneg _)
  · exact le_rfl

lemma centeredWordEnvelope_le {ι τ A : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hRC : ∀ x, R x ≤ C)
    (hG : ∀ x, |G x| ≤ 1) (x : ι → A) :
    centeredWordEnvelope label target base R G x ≤
      C * 2 ^ (Fintype.card τ + (singletonLabels label).card) := by
  have hi (U : Finset τ) :
      (if LitConsistent (nonsingletonSlots label \ U) label target then
        R x * |selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|
      else 0) ≤ C * 2 ^ (singletonLabels label).card := by
    split_ifs
    · exact mul_le_mul (hRC x)
        (selectedMixedDifference_bound _ _ _ (fun _ => hG _) x)
        (abs_nonneg _) hC
    · positivity
  calc
    _ ≤ ∑ _U ∈ (nonsingletonSlots label).powerset,
        C * 2 ^ (singletonLabels label).card := sum_le_sum (fun U _ => hi U)
    _ = ((nonsingletonSlots label).powerset.card : ℝ) *
        (C * 2 ^ (singletonLabels label).card) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ Fintype.card τ * (C * 2 ^ (singletonLabels label).card) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      exact pow_le_pow_right₀ (by norm_num) (card_le_univ _)
    _ = _ := by rw [pow_add]; ring

lemma centeredWordEnvelope_ne_zero {ι τ A : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base : ι → A)
    (R G : (ι → A) → ℝ) (x : ι → A)
    (hx : centeredWordEnvelope label target base R G x ≠ 0) :
    ∃ U ∈ (nonsingletonSlots label).powerset,
      LitConsistent (nonsingletonSlots label \ U) label target ∧ R x ≠ 0 ∧
      selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
        (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x ≠ 0 := by
  by_contra hn
  apply hx
  apply sum_eq_zero
  intro U hU
  split_ifs with hL
  · by_cases hRx : R x = 0
    · rw [hRx, zero_mul]
    · have hd : selectedMixedDifference (singletonLabels label)
          (singletonTarget label target base)
          (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x = 0 := by
        by_contra hd
        exact hn ⟨U, hU, hL, hRx, hd⟩
      rw [hd, abs_zero, mul_zero]
  · rfl

theorem uniform_weighted_centered_word_envelope {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x)
    (hRdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → R x = R y) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R x * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) *
        (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
          (centeredWordEnvelope label target base R G) := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  apply (uniform_weighted_centered_word_majorant B p hp hpB label target base
    htarget R G hR hRdep).trans
  calc
    _ ≤ ∑ U ∈ (nonsingletonSlots label).powerset,
        (∏ i ∈ univ.image label, (p i : ℝ)⁻¹) * μ.average
          (fun x => if LitConsistent (nonsingletonSlots label \ U) label target then
            R x * |selectedMixedDifference (singletonLabels label)
              (singletonTarget label target base)
              (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
                (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|
          else 0) := by
      apply sum_le_sum
      intro U hU
      split_ifs
      · apply mul_le_mul_of_nonneg_right
        · simpa only [inv_one, one_pow, mul_one] using
            full_word_designated_reciprocal_bound label U (mem_powerset.mp hU) p 1
              (by norm_num) (fun i => by exact_mod_cast hp i)
        · exact μ.average_nonneg (fun x => mul_nonneg (hR x) (abs_nonneg _))
      · simp only [FiniteLaw.average_const, mul_zero, le_refl]
    _ = _ := by
      rw [← mul_sum]
      congr 1
      simp only [centeredWordEnvelope, FiniteLaw.average, mul_sum]
      rw [sum_comm]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessRecordBounds
namespace OAI

/-! Concrete size and prime-slot bounds for an attached witness record. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma mem_recordedWitnessWord {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (t : SignedStep) :
    t ∈ recordedWitnessWord main word ↔ t ∈ main ∨ ∃ i, t ∈ word i := by
  simp [recordedWitnessWord]

lemma recordedWitnessWord_length {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) :
    (recordedWitnessWord main word).length = main.length + ∑ i, (word i).length := by
  simp [recordedWitnessWord, List.length_flatten, List.sum_ofFn]

lemma recordedWitnessWord_length_le {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (s : ℕ) (hlen : ∀ i, (word i).length ≤ s) :
    (recordedWitnessWord main word).length ≤ main.length + n * s := by
  rw [recordedWitnessWord_length]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin n, s := sum_le_sum (fun i _ => hlen i)
    _ = _ := by simp

theorem recordedWitnessWord_slots_le {n : ℕ} (main : List SignedStep)
    (word : Fin n → List SignedStep) (J M : ℕ)
    (hmain : ∀ t ∈ main, t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M)
    (hword : ∀ i t, t ∈ word i →
      t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M) :
    Fintype.card (ActualPrimeSlot (recordedWitnessWord main word).get) ≤
      (recordedWitnessWord main word).length * (J + M) := by
  have hvalid (t : SignedStep) (ht : t ∈ recordedWitnessWord main word) :
      t.tuple.primeFactors.card ≤ J ∧ t.padding.primeFactors.card ≤ M := by
    rcases (mem_recordedWitnessWord main word t).mp ht with ht | ⟨i, hi⟩
    · exact hmain t ht
    · exact hword i t hi
  exact actualPrimeSlot_card_le _ J M
    (fun i => (hvalid _ (List.get_mem _ i)).1)
    (fun i => (hvalid _ (List.get_mem _ i)).2)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedPaddingWitness
namespace OAI

/-! The singleton trace term keeps the main padding event inside the residue average. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma EncodedPaddingWitnessEvent.congr {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (d : WitnessRecord n R)
    (e : PrimeWordEncoding R T P Q) (main : List SignedStep) (p : ι → ℕ)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop) (x z : ι → Fin B)
    (hxz : ∀ i, i ∉ S → x i = z i) :
    EncodedPaddingWitnessEvent S d e main p B h s J supply x ↔
      EncodedPaddingWitnessEvent S d e main p B h s J supply z := by
  constructor
  · rintro ⟨hw, hr, hm, y, hy, ht⟩
    refine ⟨hw, hr, (retainedMainTests_congr p S h B main x z hxz).mp hm, y, ?_, ht⟩
    intro i hi
    exact (hy i hi).trans (hxz i hi)
  · rintro ⟨hw, hr, hm, y, hy, ht⟩
    refine ⟨hw, hr, (retainedMainTests_congr p S h B main x z hxz).mpr hm, y, ?_, ht⟩
    intro i hi
    exact (hy i hi).trans (hxz i hi).symm

theorem encoded_padding_witness_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ι) (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (main : List SignedStep) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hS : ∀ i ∈ S, p i ∈ wordDivisorPrimeSupport main)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport e.decode, ∃ i, p i = q) :
    (∏ i ∈ S, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (EncodedPaddingWitnessEvent S d e main p B h s J supply) ≤
      if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
        h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  have hnonneg : 0 ≤ ∏ i ∈ S, (p i : ℝ)⁻¹ := by positivity
  by_cases hw : e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
      (fun i => (d.1.2.2 i).val) h s J supply
  · rw [if_pos hw]
    by_cases hr : d.Realizes e main
    · have hc : ∀ q ∈ wordDivisorPrimeSupport (recordedWitnessWord main
          (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val)),
          ∃ i, p i = q := by
        simpa only [← hr.2.1] using hcover
      have hb := tuple_weight_mul_padding_hybrid_probability_le n B h p hinj hp hpB S main
        (fun i => (e.decode.drop (d.1.2.1 i).val).take (d.1.2.2 i).val)
        (fun i => wordDisplacement h (main.take (d.2 i).val)) hS hc
      have hmono := μ.probability_mono_of_imp
        (fun x (he : EncodedPaddingWitnessEvent S d e main p B h s J supply x) => he.2.2)
      apply (mul_le_mul_of_nonneg_left hmono hnonneg).trans
      simpa only [← hr.2.1, ← hr.2.2] using hb
    · have he : ∀ x, ¬EncodedPaddingWitnessEvent S d e main p B h s J supply x :=
        fun _ hx => hr hx.2.1
      simp only [FiniteLaw.probability, FiniteLaw.average, he, ite_false, mul_zero,
        sum_const_zero]
      exact e.weight_nonneg
  · rw [if_neg hw]
    have he : ∀ x, ¬EncodedPaddingWitnessEvent S d e main p B h s J supply x :=
      fun _ hx => hw hx.1
    simp only [FiniteLaw.probability, FiniteLaw.average, he, ite_false, mul_zero,
      sum_const_zero, le_refl]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedPaddingUnion
namespace OAI

/-! Sum the retained padding-event probabilities over all main words exactly once. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem sum_main_encoded_padding_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : WitnessRecord n R) (e : PrimeWordEncoding R T P Q)
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hcover : ∀ q ∈ wordDivisorPrimeSupport e.decode, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (EncodedPaddingWitnessEvent (S main) d e main p B h s J supply)) ≤
      if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
        h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let g (main : List SignedStep) :=
    (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      μ.probability (EncodedPaddingWitnessEvent (S main) d e main p B h s J supply)
  have hzero (main : List SignedStep) (hne : main ≠ e.decode.take d.1.1.val) : g main = 0 := by
    have hfalse : ∀ x, ¬EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x := by
      intro x hx
      exact hne hx.2.1.1.symm
    simp only [g, FiniteLaw.probability, FiniteLaw.average, hfalse, ite_false,
      mul_zero, sum_const_zero]
  change ∑ main ∈ F, g main ≤ _
  by_cases hm : e.decode.take d.1.1.val ∈ F
  · rw [sum_eq_single_of_mem (e.decode.take d.1.1.val) hm (fun main _ hne => hzero main hne)]
    exact encoded_padding_witness_probability_le (S _) d e _ p hinj B h s J supply hp hpB (hS _ hm) hcover
  · rw [sum_eq_zero (fun main hmain => hzero main (fun he => hm (he ▸ hmain)))]
    split_ifs
    · exact e.weight_nonneg
    · exact le_refl 0

theorem main_sum_padding_witness_union_probability_le {R T n : ℕ} {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => ∃ d : WitnessRecord n R, ∃ e : PrimeWordEncoding R T P Q,
          EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x)) ≤
      ∑ d : WitnessRecord n R, ∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  calc
    _ ≤ ∑ main ∈ F, ∑ d : WitnessRecord n R, ∑ e : PrimeWordEncoding R T P Q,
        (∏ i ∈ S main, (p i : ℝ)⁻¹) *
          μ.probability (EncodedPaddingWitnessEvent (S main) d e main p B h s J supply) := by
      apply sum_le_sum
      intro main _
      simp only [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun _ _ => by positivity))
      apply (μ.probability_exists_le _).trans
      exact sum_le_sum (fun d _ => μ.probability_exists_le _)
    _ ≤ _ := by
      rw [sum_comm]
      apply sum_le_sum
      intro d _
      rw [sum_comm]
      apply sum_le_sum
      intro e _
      exact sum_main_encoded_padding_probability_le d e F S p hinj B h s J supply hp hpB
        (fun q hq => hcover q (e.divisor_support_subset hP hQ hq)) hS

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BoundedPaddingUnion
namespace OAI

/-! The finite witness union includes all record lengths and all original main words. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem main_sum_bounded_padding_union_probability_le {D n : ℕ} (T : ℕ → ℕ) {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).probability
        (fun x => ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
          ∃ e : PrimeWordEncoding R.val (T R.val) P Q,
            EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x)) ≤
      ∑ R : Fin (D + 1), ∑ d : WitnessRecord n R.val,
        ∑ e : PrimeWordEncoding R.val (T R.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
            h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  calc
    _ ≤ ∑ main ∈ F, ∑ R : Fin (D + 1),
        (∏ i ∈ S main, (p i : ℝ)⁻¹) * μ.probability
          (fun x => ∃ d : WitnessRecord n R.val, ∃ e : PrimeWordEncoding R.val (T R.val) P Q,
            EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x) := by
      apply sum_le_sum
      intro main _
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (μ.probability_exists_le _)
        (prod_nonneg (fun _ _ => by positivity))
    _ ≤ _ := by
      rw [sum_comm]
      apply sum_le_sum
      intro R _
      exact main_sum_padding_witness_union_probability_le F S p hinj B h s J supply hp hpB hP hQ hcover hS

theorem weighted_supported_padding_averages_le_catalog {D n : ℕ} (T : ℕ → ℕ) {P Q : Finset ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : Finset (List SignedStep)) (S : List SignedStep → Finset ι) (p : ι → ℕ) (hinj : Function.Injective p)
    (B h s J : ℕ) (supply : ℕ → ℕ → Prop)
    (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (hS : ∀ main ∈ F, ∀ i ∈ S main, p i ∈ wordDivisorPrimeSupport main)
    (f : List SignedStep → (ι → Fin B) → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ main ∈ F, ∀ x, |f main x| ≤ C)
    (hsupport : ∀ main ∈ F, ∀ x, f main x ≠ 0 →
      ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
        ∃ e : PrimeWordEncoding R.val (T R.val) P Q,
          EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x) :
    (∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
      (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => |f main x|)) ≤
      C * ∑ R : Fin (D + 1), ∑ d : WitnessRecord n R.val,
        ∑ e : PrimeWordEncoding R.val (T R.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
            h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let E (main : List SignedStep) (x : ι → Fin B) :=
    ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
      ∃ e : PrimeWordEncoding R.val (T R.val) P Q, EncodedPaddingWitnessEvent (S main) d e main p B h s J supply x
  calc
    _ ≤ ∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
        (C * μ.probability (E main)) := by
      apply sum_le_sum
      intro main hm
      exact mul_le_mul_of_nonneg_left
        (μ.average_abs_le_support (f main) (E main) C (hf main hm) (hsupport main hm))
        (prod_nonneg (fun _ _ => by positivity))
    _ = C * ∑ main ∈ F, (∏ i ∈ S main, (p i : ℝ)⁻¹) *
        μ.probability (E main) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro main _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (main_sum_bounded_padding_union_probability_le T F S p hinj B h s J supply hp hpB hP hQ hcover hS) hC

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CenteredWitnessCatalog
namespace OAI

/-! Sum full centered-word averages against the numerical witness catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem centered_words_le_witness_catalog {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι] {D n : ℕ} (slots : ℕ → ℕ)
    (P Q : Finset ℕ) (F : Finset (List SignedStep))
    (p : ι → ℕ) (hinj : Function.Injective p) (B h s J : ℕ)
    (supply : ℕ → ℕ → Prop) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (label : List SignedStep → τ → ι) (target : List SignedStep → τ → Fin B)
    (base : ι → Fin B) (R G : List SignedStep → (ι → Fin B) → ℝ)
    (C : List SignedStep → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < p (label main t))
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hG : ∀ main ∈ F, ∀ x, |G main x| ≤ 1)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ K)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hS : ∀ main ∈ F, ∀ i ∈ univ.image (label main), p i ∈ wordDivisorPrimeSupport main)
    (hsupport : ∀ main ∈ F, ∀ x,
      centeredWordEnvelope (label main) (target main) base (R main) (G main) x ≠ 0 →
      ∃ r : Fin (D + 1), ∃ d : WitnessRecord n r.val,
        ∃ e : PrimeWordEncoding r.val (slots r.val) P Q,
          EncodedPaddingWitnessEvent (univ.image (label main)) d e main p B h s J supply x) :
    (∑ main ∈ F,
      |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
        (fun x => R main x * (∏ t,
          ((if x (label main t) = target main t then (1 : ℝ) else 0) -
            (p (label main t) : ℝ)⁻¹)) * G main x)|) ≤
      K * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (slots r.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J supply then e.weight else 0 := by
  let μ := FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))
  let envelope (main : List SignedStep) :=
    centeredWordEnvelope (label main) (target main) base (R main) (G main)
  calc
    _ ≤ ∑ main ∈ F, (∏ i ∈ univ.image (label main), (p i : ℝ)⁻¹) *
        μ.average (fun x => |envelope main x|) := by
      apply sum_le_sum
      intro main hm
      have hb := uniform_weighted_centered_word_envelope B p hp hpB (label main)
        (target main) base (htarget main hm) (R main) (G main) (hR main hm) (hRdep main hm)
      have he : (fun x => |envelope main x|) = envelope main := by
        funext x
        exact abs_of_nonneg (centeredWordEnvelope_nonneg _ _ _ _ _ (hR main hm) x)
      rw [he]
      exact hb
    _ ≤ _ := by
      apply weighted_supported_padding_averages_le_catalog slots F
        (fun main => univ.image (label main)) p hinj B h s J supply hp hpB hP hQ
        hcover hS envelope K hK _ hsupport
      intro main hm x
      rw [abs_of_nonneg (centeredWordEnvelope_nonneg _ _ _ _ _ (hR main hm) x)]
      exact (centeredWordEnvelope_le (label main) (target main) base (R main) (G main)
        (C main) (hC main hm) (hRC main hm) (hG main hm) x).trans (hcost main hm)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SingletonPaddingSupport
namespace OAI

/-! The selected singleton support retains the original padding event. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem selected_residue_has_padding_witness {ι W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (S : Finset ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J n M D : ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (a x : ι → Fin B)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ S, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : S → ℕ)
    (hmain : ∀ i : S, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (V : Finset ι) (hSV : S ⊆ V) (hretain : RetainedMainTests p V h B main x)
    (hmainvalid : ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ w t, t ∈ word w → WitnessStepAdmissible P Q J M t)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : Disjoint P Q)
    (hD : main.length + n * s ≤ D)
    (hnonzero : selectedMixedDifference S a
      (witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B z))) x ≠ 0)
    (hn : n * (s * J) < S.card) :
    ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
      ∃ e : PrimeWordEncoding R.val (R.val * (J + M)) P Q,
        EncodedPaddingWitnessEvent V d e main p B h s J supply x := by
  have hsq (w) (t) (ht : t ∈ word w) := (hwordvalid w t ht).1
  obtain ⟨index, _hindex, hnum, y, hy, htests⟩ :=
    selected_residue_witnesses_and_hybrid S p hprime hinj B h s J n supply main word
      attachment a x hatt hminimal hlen hsq hdivsq hcard hsupport hpad hcover
      position hmain hnonzero hn
  let v := recordedWitnessWord main (fun i => word (index i))
  have hvlen : v.length ≤ D :=
    (recordedWitnessWord_length_le main (fun i => word (index i)) s
      (fun i => hlen (index i))).trans hD
  have hvalid (t) (ht : t ∈ v) : WitnessStepAdmissible P Q J M t := by
    rcases (mem_recordedWitnessWord main (fun i => word (index i)) t).mp ht with
      ht | ⟨i, hi⟩
    · exact hmainvalid t ht
    · exact hwordvalid (index i) t hi
  have hslots : Fintype.card (ActualPrimeSlot v.get) ≤ v.length * (J + M) := by
    exact recordedWitnessWord_slots_le main (fun i => word (index i)) J M
      (fun t ht => ⟨(hmainvalid t ht).2.2.1, (hmainvalid t ht).2.2.2.1⟩)
      (fun i t ht => ⟨(hwordvalid (index i) t ht).2.2.1,
        (hwordvalid (index i) t ht).2.2.2.1⟩)
  have hdisjoint (t) (ht : t ∈ v) (u) (hu : u ∈ v) :
      Disjoint t.tuple.primeFactors u.padding.primeFactors :=
    hPQ.mono (hvalid t ht).2.2.2.2.1 (hvalid u hu).2.2.2.2.2
  obtain ⟨d, e, he, hdecode, hem, hew, hea, heweight⟩ :=
    actual_witness_has_encoded_record main (fun i => word (index i))
      (fun i => attachment (index i)) (fun i => hatt (index i)) P Q (v.length * (J + M))
      h s J supply p hnum hslots (fun t ht => (hvalid t ht).1)
      (fun t ht => (hvalid t ht).2.1) (fun t ht => (hvalid t ht).2.2.2.2.1)
      (fun t ht => (hvalid t ht).2.2.2.2.2) hdisjoint hP
  refine ⟨⟨v.length, Nat.lt_succ_of_le hvlen⟩, d, e, he, ⟨hem, ?_, heweight⟩, hretain, y, ?_, ?_⟩
  · rw [hdecode]
    congr 1
    funext i
    simpa only [hdecode] using (hew i).symm
  · intro i hi
    exact hy i (fun his => hi (hSV his))
  · intro i
    rw [hew i, hea i]
    exact htests i

theorem forced_selected_residue_has_padding_witness {ι W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype W] [DecidableEq W]
    (S : Finset ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J n M D : ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (a b x : ι → Fin B) (lit : Finset ι) (hSlit : Disjoint S lit)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ S, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : S → ℕ)
    (hmain : ∀ i : S, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (V : Finset ι) (hSV : S ⊆ V) (hlitV : lit ⊆ V)
    (hretain : RetainedMainTests p V h B main x)
    (hmainvalid : ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ w t, t ∈ word w → WitnessStepAdmissible P Q J M t)
    (hP : ∀ p ∈ P, p.Prime) (hPQ : Disjoint P Q)
    (hD : main.length + n * s ≤ D)
    (hnonzero : selectedMixedDifference S a
      (fun z => witnessAvoidance (fun w y => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B y)) (forceCoordinates lit b z)) x ≠ 0)
    (hn : n * (s * J) < S.card) :
    ∃ R : Fin (D + 1), ∃ d : WitnessRecord n R.val,
      ∃ e : PrimeWordEncoding R.val (R.val * (J + M)) P Q,
        EncodedPaddingWitnessEvent V d e main p B h s J supply x := by
  let F : (ι → Fin B) → ℝ := witnessAvoidance (fun w z => decide
    (AttachedResiduePositiveWord p h (word w)
      (wordDisplacement h (main.take (attachment w))) B z))
  have hnz : selectedMixedDifference S a F (forceCoordinates lit b x) ≠ 0 := by
    rw [← selectedMixedDifference_force_disjoint S lit hSlit a b x F]
    exact hnonzero
  have hsame : ∀ i, i ∉ V → forceCoordinates lit b x i = x i := by
    intro i hi
    have hilit : i ∉ lit := fun hilit => hi (hlitV hilit)
    simp only [forceCoordinates_apply, hilit, ite_false]
  have hretain' : RetainedMainTests p V h B main (forceCoordinates lit b x) :=
    (retainedMainTests_congr p V h B main _ x hsame).mpr hretain
  obtain ⟨R, d, e, he⟩ := selected_residue_has_padding_witness S p hprime hinj
    B h s J n M D P Q supply main word attachment a (forceCoordinates lit b x)
    hatt hminimal hlen hdivsq hcard hsupport hpad hcover position hmain V hSV hretain'
    hmainvalid hwordvalid hP hPQ hD hnz hn
  exact ⟨R, d, e, (EncodedPaddingWitnessEvent.congr V d e main p B h s J supply
    (forceCoordinates lit b x) x hsame).mp he⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SingletonWordEnvelope
namespace OAI

/-! Every nonzero full-word envelope supplies the same bounded numerical witness record. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem singleton_envelope_has_padding_witness {ι τ W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype W] [DecidableEq W]
    (label : τ → ι) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (B h s J n M D : ℕ)
    (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (main : List SignedStep) (word : W → List SignedStep) (attachment : W → ℕ)
    (target : τ → Fin B) (base x : ι → Fin B) (R : (ι → Fin B) → ℝ)
    (hatt : ∀ w, attachment w ≤ main.length)
    (hminimal : ∀ w, MinimalWord (ForwardProhibited h s supply) (word w))
    (hlen : ∀ w, (word w).length ≤ s)
    (hdivsq : ∀ w t, t ∈ word w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ w t, t ∈ word w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ w q j, TuplePrimeAt (word w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word w, ¬q ∣ t.padding)
    (hpad : ∀ i ∈ singletonLabels label, ∀ w t, t ∈ word w → ¬p i ∣ t.padding)
    (hcover : ∀ w q, q ∈ wordDivisorPrimeSupport (word w) → ∃ i, p i = q)
    (position : singletonLabels label → ℕ)
    (hmain : ∀ i : singletonLabels label, ∀ v, TuplePrimeAt main (p i) v → v = position i)
    (hretain : R x ≠ 0 → RetainedMainTests p (univ.image label) h B main x)
    (hmainvalid : ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ w t, t ∈ word w → WitnessStepAdmissible P Q J M t)
    (hP : ∀ q ∈ P, q.Prime) (hPQ : Disjoint P Q)
    (hD : main.length + n * s ≤ D)
    (hn : n * (s * J) < (singletonLabels label).card)
    (hne : centeredWordEnvelope label target base R
      (witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word w)
        (wordDisplacement h (main.take (attachment w))) B z))) x ≠ 0) :
    ∃ r : Fin (D + 1), ∃ d : WitnessRecord n r.val,
      ∃ e : PrimeWordEncoding r.val (r.val * (J + M)) P Q,
        EncodedPaddingWitnessEvent (univ.image label) d e main p B h s J supply x := by
  obtain ⟨U, _hU, _hL, hRx, hd⟩ := centeredWordEnvelope_ne_zero label target base R _ x hne
  have hS : singletonLabels label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, ht⟩ := singleton_occurrence_exists label ⟨i, hi⟩
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  have hlit : (nonsingletonSlots label \ U).image label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, _, ht⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  exact forced_selected_residue_has_padding_witness (singletonLabels label) p hprime hinj
    B h s J n M D P Q supply main word attachment (singletonTarget label target base)
    (litForcedTarget (nonsingletonSlots label \ U) label target base) x
    ((nonsingletonSlots label \ U).image label) (singleton_disjoint_designated label U)
    hatt hminimal hlen hdivsq hcard hsupport hpad hcover position hmain
    (univ.image label) hS hlit (hretain hRx) hmainvalid hwordvalid hP hPQ hD hd hn

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SingletonCenteredCatalog
namespace OAI

/-! The complete singleton word contribution is bounded by the numerical witness catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem singleton_centered_words_le_catalog {ι τ W : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [Fintype W] [DecidableEq W]
    (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (B h s J n M D : ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop)
    (F : Finset (List SignedStep))
    (label : List SignedStep → τ → ι) (target : List SignedStep → τ → Fin B)
    (base : ι → Fin B) (R : List SignedStep → (ι → Fin B) → ℝ)
    (word : List SignedStep → W → List SignedStep)
    (attachment : List SignedStep → W → ℕ)
    (C : List SignedStep → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hpB : ∀ i, p i ≤ B) (hP : ∀ q ∈ P, q.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (hcover : ∀ q ∈ P ∪ Q, ∃ i, p i = q)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < p (label main t))
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ K)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hS : ∀ main ∈ F, ∀ i ∈ univ.image (label main), p i ∈ wordDivisorPrimeSupport main)
    (hatt : ∀ main ∈ F, ∀ w, attachment main w ≤ main.length)
    (hminimal : ∀ main ∈ F, ∀ w,
      MinimalWord (ForwardProhibited h s supply) (word main w))
    (hlen : ∀ main ∈ F, ∀ w, (word main w).length ≤ s)
    (hdivsq : ∀ main ∈ F, ∀ w t, t ∈ word main w → Squarefree (t.padding * t.tuple))
    (hcard : ∀ main ∈ F, ∀ w t, t ∈ word main w → t.tuple.primeFactors.card = J)
    (hsupport : ∀ main ∈ F, ∀ w q j, TuplePrimeAt (word main w) q j →
      ¬q ∣ h ∧ ∀ t ∈ word main w, ¬q ∣ t.padding)
    (hpad : ∀ main ∈ F, ∀ i ∈ singletonLabels (label main), ∀ w t,
      t ∈ word main w → ¬p i ∣ t.padding)
    (hwordcover : ∀ main ∈ F, ∀ w q,
      q ∈ wordDivisorPrimeSupport (word main w) → ∃ i, p i = q)
    (position : ∀ main, singletonLabels (label main) → ℕ)
    (hmain : ∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
      TuplePrimeAt main (p i) v → v = position main i)
    (hretain : ∀ main ∈ F, ∀ x,
      R main x ≠ 0 → RetainedMainTests p (univ.image (label main)) h B main x)
    (hmainvalid : ∀ main ∈ F, ∀ t ∈ main, WitnessStepAdmissible P Q J M t)
    (hwordvalid : ∀ main ∈ F, ∀ w t, t ∈ word main w → WitnessStepAdmissible P Q J M t)
    (hD : ∀ main ∈ F, main.length + n * s ≤ D)
    (hn : ∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) :
    (∑ main ∈ F,
      |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hprime i).pos (hpB i))).average
        (fun x => R main x * (∏ t,
          ((if x (label main t) = target main t then (1 : ℝ) else 0) -
            (p (label main t) : ℝ)⁻¹)) *
          witnessAvoidance (fun w z => decide (AttachedResiduePositiveWord p h (word main w)
            (wordDisplacement h (main.take (attachment main w))) B z)) x)|) ≤
      K * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (r.val * (J + M)) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J supply then e.weight else 0 := by
  apply centered_words_le_witness_catalog (fun r => r * (J + M)) P Q F p hinj B h s J supply
    (fun i => (hprime i).pos) hpB hP hQ hcover label target base R _ C K hK
    htarget hR hRC hC (fun _ _ x => witnessAvoidance_abs_le_one _ x) hcost hRdep hS
  intro main hm x hx
  exact singleton_envelope_has_padding_witness (label main) p hprime hinj B h s J n M D
    P Q supply main (word main) (attachment main) (target main) base x (R main)
    (hatt main hm) (hminimal main hm) (hlen main hm) (hdivsq main hm) (hcard main hm)
    (hsupport main hm) (hpad main hm) (hwordcover main hm) (position main) (hmain main hm)
    (hretain main hm x) (hmainvalid main hm) (hwordvalid main hm) hP hPQ (hD main hm)
    (hn main hm) hx

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

lemma catalog_admissible (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : WitnessStepAdmissible F.P F.Q J M t := by
  have hp := F.catalog_pairs s c t ht
  exact ⟨F.tuple_squarefree _ hp, F.padding_squarefree _ hp,
    (F.tuple_card _ hp).le, F.padding_card _ hp, F.tuple_pool _ hp, F.padding_pool _ hp⟩

lemma catalog_whole_squarefree (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : Squarefree (t.padding * t.tuple) :=
  F.whole_squarefree _ (F.catalog_pairs s c t ht)

lemma catalog_tuple_card (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (t : SignedStep) (ht : t ∈ decodeStepWord c.val) : t.tuple.primeFactors.card = J :=
  F.tuple_card _ (F.catalog_pairs s c t ht)

lemma catalog_prime_support (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (q v : ℕ) (hq : TuplePrimeAt (decodeStepWord c.val) q v) :
    ¬q ∣ h ∧ ∀ t ∈ decodeStepWord c.val, ¬q ∣ t.padding := by
  obtain ⟨hqprime, t, ht, hqt⟩ := hq
  have htpairs := F.catalog_pairs s c t (List.mem_of_getElem? ht)
  have hqP : q ∈ F.P := F.tuple_pool _ htpairs
    (hqprime.mem_primeFactors hqt (F.tuple_squarefree _ htpairs).ne_zero)
  refine ⟨F.excluded q hqP, ?_⟩
  intro a ha hqa
  have hapairs := F.catalog_pairs s c a ha
  have hqQ : q ∈ F.Q := F.padding_pool _ hapairs
    (hqprime.mem_primeFactors hqa (F.padding_squarefree _ hapairs).ne_zero)
  exact disjoint_left.mp F.disjoint hqP hqQ

lemma catalog_padding_excluded (s : ℕ) (c : ProhibitedCatalog F.pairs h s)
    (q : ℕ) (hq : q ∈ F.P) (t : SignedStep) (ht : t ∈ decodeStepWord c.val) :
    ¬q ∣ t.padding := by
  intro hd
  have hpairs := F.catalog_pairs s c t ht
  have hqQ : q ∈ F.Q := F.padding_pool _ hpairs
    ((F.primeP q hq).mem_primeFactors hd (F.padding_squarefree _ hpairs).ne_zero)
  exact disjoint_left.mp F.disjoint hq hqQ

end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedSingletonCatalog
namespace OAI

/-! Full singleton cancellation for the actual finite vertex-deletion catalog and padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem prohibited_singleton_words_le_catalog_oai {h J M : ℕ} {τ : Type*} [Fintype τ]
    (data : ProhibitedPrimeFamily h J M) (B s n D : ℕ)
    (F : Finset (List SignedStep))
    (label : List SignedStep → τ → ↥(data.P ∪ data.Q))
    (target : List SignedStep → τ → Fin B) (base : ↥(data.P ∪ data.Q) → Fin B)
    (R : List SignedStep → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (C : List SignedStep → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (htarget : ∀ main ∈ F, ∀ t, (target main t).val < (label main t).val)
    (hR : ∀ main ∈ F, ∀ x, 0 ≤ R main x)
    (hRC : ∀ main ∈ F, ∀ x, R main x ≤ C main)
    (hC : ∀ main ∈ F, 0 ≤ C main)
    (hcost : ∀ main ∈ F,
      C main * 2 ^ (Fintype.card τ + (singletonLabels (label main)).card) ≤ A)
    (hRdep : ∀ main ∈ F, ∀ x y,
      (∀ i, i ∉ univ.image (label main) → x i = y i) → R main x = R main y)
    (hseen : ∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ wordDivisorPrimeSupport main)
    (hlabelP : ∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ data.P)
    (hmainpairs : ∀ main ∈ F, ∀ t ∈ main, (t.tuple, t.padding) ∈ data.pairs)
    (htupleCover : ∀ main ∈ F, ∀ (k : Fin main.length) (i : ↥(data.P ∪ data.Q)),
      i.val ∈ (main.get k).tuple.primeFactors → i ∈ univ.image (label main))
    (position : ∀ main, singletonLabels (label main) → ℕ)
    (hposition : ∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
      TuplePrimeAt main i.val v → v = position main i)
    (hD : ∀ main ∈ F, main.length + n * s ≤ D)
    (hn : ∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) :
    (∑ main ∈ F,
      |(data.residueLaw B hB).average (fun x =>
        paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (R main) x *
        (∏ t, ((if x (label main t) = target main t then (1 : ℝ) else 0) -
          ((label main t).val : ℝ)⁻¹)) * attachedCatalogAvoidance data s B D main x)|) ≤
      A * ∑ r : Fin (D + 1), ∑ d : WitnessRecord n r.val,
        ∑ e : PrimeWordEncoding r.val (r.val * (J + M)) data.P data.Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
            (fun i => (d.1.2.2 i).val) h s J (fun d q => (d, q) ∈ data.pairs)
          then e.weight else 0 := by
  let p : ↥(data.P ∪ data.Q) → ℕ := Subtype.val
  let R' (main : List SignedStep) := paddingWeightedFunction p h B main (R main)
  let word (_main : List SignedStep) (a : Fin (D + 1) × ProhibitedCatalog data.pairs h s) :=
    decodeStepWord a.2.val
  let attachment (main : List SignedStep) (a : Fin (D + 1) × ProhibitedCatalog data.pairs h s) :=
    min a.1.val main.length
  have hsingle (main : List SignedStep) (hm : main ∈ F)
      (i : ↥(data.P ∪ data.Q)) (hi : i ∈ singletonLabels (label main)) : i.val ∈ data.P := by
    obtain ⟨t, ht⟩ := singleton_occurrence_exists (label main) ⟨i, hi⟩
    exact hlabelP main hm i (mem_image.mpr ⟨t, mem_univ _, ht⟩)
  apply singleton_centered_words_le_catalog p data.prime Subtype.val_injective B h s J n M D
    data.P data.Q (fun d q => (d, q) ∈ data.pairs) F label target base R' word attachment C A hA
    (fun i => hB i.val i.property) data.primeP data.primeQ data.disjoint
    (fun q hq => ⟨⟨q, hq⟩, rfl⟩) htarget
    (fun main hm => paddingWeightedFunction_nonneg p h B main (R main) (hR main hm))
    (fun main hm => paddingWeightedFunction_le p h B main (R main) (C main)
      (hC main hm) (hRC main hm)) hC hcost ?_ hseen
    (fun _ _ a => Nat.min_le_right a.1.val _) (fun _ _ a => a.2.property)
    (fun _ _ a => a.2.property.1.2.1)
    (fun _ _ a => data.catalog_whole_squarefree s a.2)
    (fun _ _ a => data.catalog_tuple_card s a.2)
    (fun _ _ a => data.catalog_prime_support s a.2)
    (fun main hm i hi a => data.catalog_padding_excluded s a.2 i.val (hsingle main hm i hi))
    (fun _ _ a q hq => ⟨⟨q, data.support_subset s a.2 hq⟩, rfl⟩)
    position hposition ?_ ?_ (fun _ _ a => data.catalog_admissible s a.2) hD hn
  · intro main hm x y hxy
    apply paddingWeightedFunction_invariant p (univ.image (label main)) h B main (R main)
      _ (hRdep main hm) x y hxy
    intro k i hi his
    have hq := data.padding_pool _ (hmainpairs main hm _ (List.get_mem main k)) hi
    exact disjoint_left.mp data.disjoint (hlabelP main hm i his) hq
  · intro main hm x hx
    exact paddingWeightedFunction_retained p (univ.image (label main)) h B main (R main) x
      (fun t ht => (data.padding_squarefree _ (hmainpairs main hm t ht)).ne_zero)
      (fun t ht => (data.tuple_squarefree _ (hmainpairs main hm t ht)).ne_zero)
      (htupleCover main hm) hx
  · intro main hm t ht
    have ht' := hmainpairs main hm t ht
    exact ⟨data.tuple_squarefree _ ht', data.padding_squarefree _ ht',
      (data.tuple_card _ ht').le, data.padding_card _ ht', data.tuple_pool _ ht',
      data.padding_pool _ ht'⟩

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.prohibited_singleton_words_le_catalog_oai := @OAI.TwoPointCorrelations.prohibited_singleton_words_le_catalog_oai
