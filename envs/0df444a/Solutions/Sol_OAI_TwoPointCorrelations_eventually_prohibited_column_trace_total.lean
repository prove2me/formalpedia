-- Prove2me | solution 1 for OAI.TwoPointCorrelations.eventually_prohibited_column_trace_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:14:13.616611+00:00
-- url     : https://prove2.me/submissions/82d59e05-8c50-4829-90af-acd0068e51ac

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_column_singleton_decay
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_good_trace_total
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_many_unlit_decay
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_weighted_high_rank_words

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



lemma average_sum (μ : FiniteLaw α) (f : ι → α → ℝ) :
    μ.average (fun x => ∑ i, f i x) = ∑ i, μ.average (f i) := by
  simp only [average, mul_sum]
  rw [sum_comm]













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

lemma uniformResidueLaw_support (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin B) :
    (uniformResidueLaw B p hp hpB).weight x ≠ 0 ↔ x.val < p := by
  simp [uniformResidueLaw, ne_of_gt hp]

@[simp] lemma uniformResidueLaw_castLE (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (x : Fin p) :
    (uniformResidueLaw B p hp hpB).weight (Fin.castLE hpB x) = (p : ℝ)⁻¹ := by
  exact uniformResidueLaw_weight B p hp hpB _ x.isLt

/-- Every actual residue assignment with nonzero product mass lies below
its coordinate's modulus. This applies to the very same sample used for
the mixed-difference identity. -/
lemma uniformResidueLaw_independent_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (x : ι → Fin B) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).weight x ≠ 0 ↔
      ∀ i, (x i).val < p i := by
  simp only [FiniteLaw.independent, prod_ne_zero_iff, mem_univ, true_implies,
    uniformResidueLaw_support]

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






lemma mixedDifference_const_mul (a : ι → A) (c : ℝ) (F : (ι → A) → ℝ) (x : ι → A) :
    mixedDifference a (fun y => c * F y) x = c * mixedDifference a F x := by
  unfold mixedDifference
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring







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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RankDecay
namespace OAI

/-! The high-rank square-root saving dominates the full crude counting cost. -/

namespace TwoPointCorrelations

open _root_.Filter






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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.RankSliceCost
namespace OAI

/-! The finite choice of perfect rows, lit designation and offending column
is negligible compared with the rank saving. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma rank_slice_cost_bound (L Cj : ℝ) (R J : ℕ) (hL : 1 ≤ L)
    (hlog : 1 ≤ Real.log L) (hCj : 0 ≤ Cj)
    (hR : (R : ℝ) ≤ 2 * L) (hJ : (J : ℝ) ≤ Cj * Real.log L) :
    (2 : ℝ) ^ (R * J) * 2 ^ R * J ≤
      Real.exp ((3 * Cj + 2) * L * (Real.log L) ^ 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hJexp : (J : ℝ) ≤ Real.exp J := by linarith [Real.add_one_le_exp (J : ℝ)]
  have hprod : ((R * J : ℕ) : ℝ) ≤ 2 * Cj * L * Real.log L := by
    push_cast
    exact (mul_le_mul hR hJ (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
  have hl : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hl1 : (1 : ℝ) ≤ (Real.log L) ^ 2 := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * Cj * L by positivity)
  have h2 := mul_le_mul_of_nonneg_left hl1 (show 0 ≤ 2 * L by positivity)
  have h3 : (J : ℝ) ≤ Cj * L * (Real.log L) ^ 2 := by
    calc
      _ ≤ Cj * Real.log L := hJ
      _ ≤ Cj * (Real.log L) ^ 2 := mul_le_mul_of_nonneg_left hl hCj
      _ ≤ _ := by nlinarith [mul_nonneg hCj (sq_nonneg (Real.log L))]
  calc
    _ ≤ (Real.exp 1) ^ (R * J) * (Real.exp 1) ^ R * Real.exp J :=
      mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by norm_num) htwo _)
        (pow_le_pow_left₀ (by norm_num) htwo _) (by positivity) (by positivity))
        hJexp (by positivity) (by positivity)
    _ = Real.exp (((R * J : ℕ) : ℝ) + R + J) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem eventually_rank_slice_decay (Cj : ℝ) (hCj : 0 ≤ Cj) :
    ∀ᶠ L : ℝ in atTop, ∀ R J : ℕ,
      (R : ℝ) ≤ 2 * L → (J : ℝ) ≤ Cj * Real.log L →
      ((2 : ℝ) ^ (R * J) * 2 ^ R * J) *
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  have hgap := (tendsto_rpow_atTop (show 0 < (1 / 200 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 16)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_crude_cost_small (2 * (3 * Cj + 2)) (by positivity), hgap]
    with L hL hlog hcost hgap
  intro R J hR hJ
  have hLp : 0 < L := by linarith
  have hsmall : (3 * Cj + 2) * L * (Real.log L) ^ 2 ≤
      (1 / 16 : ℝ) * L ^ (203 / 200 : ℝ) := by nlinarith
  have hpower : L ^ (101 / 100 : ℝ) * L ^ (1 / 200 : ℝ) =
      L ^ (203 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hgap' := mul_le_mul_of_nonneg_left hgap
    (Real.rpow_nonneg hLp.le (101 / 100 : ℝ))
  rw [hpower] at hgap'
  calc
    _ ≤ Real.exp ((3 * Cj + 2) * L * (Real.log L) ^ 2) *
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) :=
      mul_le_mul_of_nonneg_right (rank_slice_cost_bound L Cj R J hL hlog hCj hR hJ) (by positivity)
    _ = Real.exp ((3 * Cj + 2) * L * (Real.log L) ^ 2 -
        (1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueCentering
namespace OAI

/-! Exact passage from divisibility centers to the common-carrier singleton formula. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.average_congr_on_support {A : Type*} [Fintype A]
    (μ : FiniteLaw A) {f g : A → ℝ} (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.average f = μ.average g := by
  apply sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]


lemma forcedResidue_lt (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B) (offset : ℤ) :
    (forcedResidue B p hp hpB offset).val < p := by
  let : NeZero p := ⟨hp.ne'⟩
  exact ZMod.val_lt _

lemma divisor_test_iff_forcedResidue (B p : ℕ) (hp : 0 < p) (hpB : p ≤ B)
    (offset : ℤ) (z : Fin B) (hz : z.val < p) :
    (p : ℤ) ∣ (z.val : ℤ) + offset ↔ z = forcedResidue B p hp hpB offset := by
  let : NeZero p := ⟨hp.ne'⟩
  have he : (p : ℤ) ∣ (z.val : ℤ) + offset ↔
      (z.val : ZMod p) = -(offset : ZMod p) :=
    residue_offset_divisibility (z.val : ZMod p) (z.val : ℤ) offset (by simp)
  rw [he]
  constructor
  · intro h
    apply Fin.ext
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt hz, forcedResidue] using hv
  · intro h
    subst z
    exact ZMod.natCast_zmod_val _

/-- The equality is needed only on the support of the product law. Values
in the common carrier above a coordinate's modulus have zero mass. -/
theorem uniform_divisor_word_average {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (offset : τ → ℤ) (R : ℝ) (G : (ι → Fin B) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R * (∏ t,
        ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
          (p (label t) : ℝ)⁻¹)) * G z) =
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R * (∏ t,
        ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
          then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G z) := by
  apply FiniteLaw.average_congr_on_support
  intro z hz
  have hs := (uniformResidueLaw_independent_support B p hp hpB z).mp hz
  have he (t : τ) := divisor_test_iff_forcedResidue B (p (label t)) (hp _) (hpB _)
    (offset t) (z (label t)) (hs (label t))
  simp only [he]




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.LitCommonOrigin
namespace OAI

/-! Consistent lit residues admit one integer origin for every selected departure. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem lit_consistency_common_origin {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (L : Finset τ) (label : τ → ι) (offset : τ → ℤ)
    (base : ι → Fin B)
    (hL : LitConsistent L label
      (fun t => forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t))) :
    ∃ n : ℤ, ∀ t ∈ L, (p (label t) : ℤ) ∣ n + offset t := by
  let (i : ι) : NeZero (p i) := ⟨(hprime i).ne_zero⟩
  have hcop : Pairwise (fun i j => (p i).Coprime (p j)) := by
    intro i j hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr (fun he => hij (hinj he))
  let target (t : τ) := forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t)
  let r (i : ι) : ZMod (p i) := ((litForcedTarget L label target base i).val : ZMod (p i))
  obtain ⟨n, hn⟩ := exists_common_integer_residue p hcop r
  refine ⟨n, ?_⟩
  intro t ht
  apply (residue_offset_divisibility (r (label t)) n (offset t) (hn _)).mpr
  change ((litForcedTarget L label target base (label t)).val : ZMod (p (label t))) = _
  rw [litForcedTarget_at L label target base hL t ht]
  exact ZMod.natCast_zmod_val _

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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.AmbientLitOrigin
namespace OAI

/-! Lit consistency in the full prime pool supplies the common tuple-column origins. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem ambient_lit_common_origin {ι : Type*} [Fintype ι] [DecidableEq ι] {R J : ℕ}
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (label : Fin R × Fin J → ι)
    (U : Finset (Fin R × Fin J)) (offset : Fin R → ℤ) (base : ι → Fin B)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t.1))) :
    ∃ n : ℤ, ∀ i ∈ perfectRows label U, ∀ j, (p (label (i, j)) : ℤ) ∣ n + offset i := by
  obtain ⟨n, hn⟩ := lit_consistency_common_origin B p hprime hinj hpB
    (nonsingletonSlots label \ U) label (fun t => offset t.1) base hL
  exact ⟨n, fun i hi j => hn (i, j) (perfectRows_lit label U i hi j)⟩

theorem ambient_tuple_lit_origin {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R J : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val)
    (U : Finset (Fin R × Fin J)) (offset : Fin R → ℤ) (base : ι → Fin B)
    (perfect : Finset (Fin R)) (hperfect : perfect ⊆ perfectRows label U)
    (hL : LitConsistent (nonsingletonSlots label \ U) label
      (fun t => forcedResidue B (p (label t)) (hprime _).pos (hpB _) (offset t.1))) :
    ∃ n : ℤ, ∀ i ∈ perfect, ∀ j, ((w j i).val : ℤ) ∣ n + offset i := by
  obtain ⟨n, hn⟩ := ambient_lit_common_origin B p hprime hinj hpB label U offset base hL
  refine ⟨n, ?_⟩
  intro i hi j
  simpa only [hlabel] using hn i (hperfect hi) j

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleLitOrigins
namespace OAI

/-! Choose the actual common origins for a finite numerical rank catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem ambient_tuple_lit_origins {α ι : Type*} [Fintype ι] [DecidableEq ι]
    {R J : ℕ} {P : Fin J → Finset ℕ} (F : Finset α)
    (w : α → ColumnPrimeAssignment J R P)
    (B : ℕ) (p : ι → ℕ) (hprime : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (hpB : ∀ i, p i ≤ B) (label : α → Fin R × Fin J → ι)
    (hlabel : ∀ a ∈ F, ∀ i j, p (label a (i, j)) = (w a j i).val)
    (U : Finset (Fin R × Fin J)) (offset : α → Fin R → ℤ) (base : ι → Fin B)
    (perfect : Finset (Fin R)) (hperfect : ∀ a ∈ F, perfect ⊆ perfectRows (label a) U)
    (hL : ∀ a ∈ F, LitConsistent (nonsingletonSlots (label a) \ U) (label a)
      (fun t => forcedResidue B (p (label a t)) (hprime _).pos (hpB _) (offset a t.1))) :
    ∃ origin : α → ℤ, ∀ a ∈ F, ∀ i ∈ perfect, ∀ j,
      ((w a j i).val : ℤ) ∣ origin a + offset a i := by
  have he (a : α) : ∃ n : ℤ, a ∈ F → ∀ i ∈ perfect, ∀ j,
      ((w a j i).val : ℤ) ∣ n + offset a i := by
    by_cases ha : a ∈ F
    · obtain ⟨n, hn⟩ := ambient_tuple_lit_origin (w a) B p hprime hinj hpB (label a)
        (hlabel a ha) U (offset a) base perfect (hperfect a ha) (hL a ha)
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose origin horigin using he
  exact ⟨origin, horigin⟩

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



/-- The numerical whole tuple determines its column choices, as used by
the nonbacktracking matrix's actual copy labels. -/
theorem primeTuple_injective {J : ℕ} {P : Fin J → Finset ℕ}
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun x : (j : Fin J) → P j => ∏ j, (x j).val) := by
  intro x y he
  change (∏ j, (x j).val) = (∏ j, (y j).val) at he
  funext j
  apply Subtype.ext
  have hp := hprime j _ (x j).property
  have hd : (x j).val ∣ ∏ l, (y l).val := by
    rw [← he]
    exact dvd_prod_of_mem (fun l => (x l).val) (mem_univ j)
  obtain ⟨l, _, hdiv⟩ := (hp.prime.dvd_finsetProd_iff (fun l => (y l).val)).mp hd
  have hv : (x j).val = (y l).val :=
    (Nat.prime_dvd_prime_iff_eq hp (hprime l _ (y l).property)).mp hdiv
  have hjl : j = l := by
    by_contra hne
    exact (disjoint_left.mp (hdisjoint j l (Ne.symm hne)))
      (x j).property (hv.symm ▸ (y l).property)
  subst l
  exact hv

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


/-- Fixed signs and the numerical step list recover every tuple column
and every padding. Thus the full-word counting bound applies injectively
to the actual matrix-word catalog. -/
theorem columnTupleWord_injective {J R : ℕ} {P : Fin J → Finset ℕ}
    (forward : Fin R → Bool) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (fun a : ColumnPrimeAssignment J R P × (Fin R → ℕ) =>
      columnTupleWord a.1 forward a.2) := by
  intro a b hab
  have hsteps := List.ofFn_injective hab
  apply Prod.ext
  · funext j i
    have htuple := congrArg SignedStep.tuple (congrFun hsteps i)
    have hvalues := primeTuple_injective hprime hdisjoint htuple
    exact congrFun hvalues j
  · funext i
    exact congrArg SignedStep.padding (congrFun hsteps i)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceCatalogMaps
namespace OAI

/-! Injective encodings of the same trace catalog.  Numerical-word estimates
and column-wise forest estimates therefore have identical multiplicities. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma columnNatCode_injective {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ} :
    Function.Injective (columnNatCode (P := P) (Q := Q) (R := R)) := by
  intro a b hab
  dsimp only [columnNatCode] at hab
  apply Prod.ext
  · exact congrArg (@Prod.fst (ColumnPrimeAssignment J R P) (Fin R → ℕ)) hab
  · funext i
    exact Subtype.ext (congrFun
      (congrArg (@Prod.snd (ColumnPrimeAssignment J R P) (Fin R → ℕ)) hab) i)


lemma columnStepCode_word {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (forward : Fin R → Bool) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    List.ofFn (columnStepCode forward a) =
      columnTupleWord a.1 forward (fun i => (a.2 i).val) := rfl

lemma columnStepCode_injective {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (forward : Fin R → Bool) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Function.Injective (columnStepCode (P := P) (Q := Q) forward) := by
  intro a b hab
  apply columnNatCode_injective
  apply columnTupleWord_injective forward hprime hdisjoint
  exact congrArg List.ofFn hab

lemma largeUnlitCatalog_sum {R J : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Finset (Fin R → SignedStep))
    (label : (Fin R → SignedStep) → Fin R × Fin J → ι) (L : ℝ) (hL : 0 ≤ L)
    (term : (Fin R → SignedStep) → Finset (Fin R × Fin J) → ℝ) :
    (∑ a ∈ largeUnlitCatalog F label L, term a.1 a.2) =
      ∑ w ∈ F, ∑ U ∈ (nonsingletonSlots (label w)).powerset.filter
        (fun U => ⌊L ^ (1 / 50 : ℝ)⌋₊ < U.card), term w U := by
  rw [largeUnlitCatalog, sum_sigma]
  apply sum_congr rfl
  intro w _
  apply sum_congr
  · ext U
    simp only [mem_filter, Nat.floor_lt (Real.rpow_nonneg hL _)]
  · intro U _
    rfl


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.WeightedDivisorWord
namespace OAI

/-! Convert the full residue-weighted divisor word to its exact centered form. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem uniform_weighted_divisor_word_average {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (offset : τ → ℤ) (R G : (ι → Fin B) → ℝ) :
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R z * (∏ t,
        ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
          (p (label t) : ℝ)⁻¹)) * G z) =
    (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun z => R z * (∏ t,
        ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
          then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G z) := by
  have he := uniform_divisor_word_average B p hp hpB label offset 1 (fun z => R z * G z)
  have hl : (fun z : ι → Fin B => R z * (∏ t,
      ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
        (p (label t) : ℝ)⁻¹)) * G z) =
      (fun z => (1 : ℝ) * (∏ t,
      ((if (p (label t) : ℤ) ∣ (z (label t)).val + offset t then (1 : ℝ) else 0) -
        (p (label t) : ℝ)⁻¹)) * (R z * G z)) := by
    funext z
    ring
  have hr : (fun z : ι → Fin B => R z * (∏ t,
      ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
        then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G z) =
      (fun z => (1 : ℝ) * (∏ t,
      ((if z (label t) = forcedResidue B (p (label t)) (hp _) (hpB _) (offset t)
        then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * (R z * G z)) := by
    funext z
    ring
  rw [hl, hr]
  exact he

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.TupleResidueLabels
namespace OAI

/-! Recover singleton positions and tuple-coordinate support from the actual numerical word. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma tuple_label_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J R : ℕ} {P : Fin J → Finset ℕ} (w : ColumnPrimeAssignment J R P)
    (p : ι → ℕ) (hinj : Function.Injective p) (label : Fin R × Fin J → ι)
    (hlabel : ∀ i j, p (label (i, j)) = (w j i).val) (c : ι) :
    c ∈ univ.image label ↔ p c ∈ tuplePrimeSupport w := by
  rw [mem_tuplePrimeSupport]
  constructor
  · rintro hc
    obtain ⟨⟨i, j⟩, _, hc⟩ := mem_image.mp hc
    exact ⟨j, i, (hlabel i j).symm.trans (congrArg p hc)⟩
  · rintro ⟨j, i, hi⟩
    exact mem_image.mpr ⟨(i, j), mem_univ _, hinj ((hlabel i j).trans hi)⟩


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




end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SuppliedTupleWords
namespace OAI

/-! The literal supplied tuple words discharge the ambient support and padding-test hypotheses. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma columnTupleWord_pairs {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs) :
    ∀ a ∈ columnTupleWord w forward padding, (a.tuple, a.padding) ∈ data.pairs := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hpairs i

lemma ProhibitedPrimeFamily.supplied_word_support_subset {h J M : ℕ}
    (data : ProhibitedPrimeFamily h J M) (word : List SignedStep)
    (hpairs : ∀ a ∈ word, (a.tuple, a.padding) ∈ data.pairs) :
    wordDivisorPrimeSupport word ⊆ data.P ∪ data.Q := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := mem_biUnion.mp hp
  have hpair := hpairs a (List.mem_toFinset.mp ha)
  rw [Nat.primeFactors_mul (data.padding_squarefree _ hpair).ne_zero
    (data.tuple_squarefree _ hpair).ne_zero, mem_union] at hpa
  rcases hpa with hp | hp
  · exact mem_union_right _ (data.padding_pool _ hpair hp)
  · exact mem_union_left _ (data.tuple_pool _ hpair hp)

lemma supplied_tuple_support {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (padding : Fin R → ℕ) (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    tuplePrimeSupport w ⊆ data.P ∧ paddingPrimeSupport padding ⊆ data.Q := by
  constructor
  · intro p hp
    obtain ⟨j, i, rfl⟩ := (mem_tuplePrimeSupport w p).mp hp
    apply data.tuple_pool _ (hpairs i)
    rw [columnTuple_primeFactors w i hprime hdisjoint]
    exact mem_image.mpr ⟨j, mem_univ _, rfl⟩
  · intro p hp
    obtain ⟨i, _, hp⟩ := mem_biUnion.mp hp
    exact data.padding_pool _ (hpairs i) hp

lemma supplied_tuple_padding_disjoint {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (padding : Fin R → ℕ) (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) :
    Disjoint (tuplePrimeSupport w) (paddingPrimeSupport padding) := by
  have hs := supplied_tuple_support data w padding hpairs hprime hdisjoint
  exact data.disjoint.mono hs.1 hs.2


lemma supplied_tuple_label_seen {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) :
    ∀ i ∈ univ.image label, i.val ∈ wordDivisorPrimeSupport (columnTupleWord w forward padding) := by
  intro i hi
  rw [tupleWord_primeSupport w forward padding hprime hdisjoint
    (fun i => (data.padding_squarefree _ (hpairs i)).ne_zero)]
  exact mem_union_left _ ((tuple_label_support w Subtype.val Subtype.val_injective label hlabel i).mp hi)

lemma supplied_tuple_label_cover {h J M R : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val) :
    ∀ (k : Fin (columnTupleWord w forward padding).length) (p : ↥(data.P ∪ data.Q)),
      p.val ∈ ((columnTupleWord w forward padding).get k).tuple.primeFactors →
        p ∈ univ.image label := by
  intro k p hp
  have hk : k.val < R := by simpa only [columnTupleWord, List.length_ofFn] using k.isLt
  let i : Fin R := ⟨k.val, hk⟩
  have hi : ((columnTupleWord w forward padding).get k).tuple = columnTuple w i := by
    change ((List.ofFn (fun i => SignedStep.mk (forward i) (columnTuple w i) (padding i)))[k.val]).tuple = _
    simp only [List.getElem_ofFn]
    rfl
  rw [hi, columnTuple_primeFactors w i hprime hdisjoint] at hp
  obtain ⟨j, _, hj⟩ := mem_image.mp hp
  exact mem_image.mpr ⟨(i, j), mem_univ _, Subtype.ext ((hlabel i j).trans hj)⟩

theorem supplied_tuple_padding_retained {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ)
    (hpairs : ∀ i, (columnTuple w i, padding i) ∈ data.pairs)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i j, (label (i, j)).val = (w j i).val)
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : MainPaddingTests Subtype.val h B (columnTupleWord w forward padding) x) :
    RetainedMainTests Subtype.val (univ.image label) h B (columnTupleWord w forward padding) x := by
  apply mainPaddingTests_retained Subtype.val (univ.image label) h B
    (columnTupleWord w forward padding) x
    (fun a ha => (data.padding_squarefree _
      (columnTupleWord_pairs data w forward padding hpairs a ha)).ne_zero)
    (fun a ha => (data.tuple_squarefree _
      (columnTupleWord_pairs data w forward padding hpairs a ha)).ne_zero)
    (supplied_tuple_label_cover data w forward padding hprime hdisjoint label hlabel) hx

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedTraceTerms
namespace OAI

/-! Literal centered and designated terms of the prohibited-vertex trace expansion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma prohibitedDesignatedTerm_nonneg {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) (hw : ∀ x, 0 ≤ weight x)
    (U : Finset (Fin R × Fin J)) :
    0 ≤ prohibitedDesignatedTerm data hB s D word label base weight U := by
  unfold prohibitedDesignatedTerm
  split_ifs
  · apply mul_nonneg
    · unfold designatedReciprocal
      positivity
    · exact (data.residueLaw B hB).average_nonneg (fun x => mul_nonneg (hw x) (abs_nonneg _))
  · exact le_rfl

theorem prohibited_centering_bound {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (word : List SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (↥(data.P ∪ data.Q) → Fin B) → ℝ) (hw : ∀ x, 0 ≤ weight x)
    (hdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → weight x = weight y) :
    |prohibitedCenteredAverage data hB s D word label weight| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        prohibitedDesignatedTerm data hB s D word label base weight U := by
  have hb := uniform_weighted_centered_word_majorant B
    (fun p : ↥(data.P ∪ data.Q) => p.val) (fun p => (data.prime p).pos)
    (fun p => hB _ p.property) label (tupleForcedTarget data hB word label) base
    (fun t => forcedResidue_lt B (label t).val (data.prime _).pos
      (hB _ (label t).property) (wordDisplacement h (word.take t.1.val)))
    weight (attachedCatalogAvoidance data s B D word) hw hdep
  unfold prohibitedCenteredAverage
  change |(FiniteLaw.independent _).average _| ≤ _
  rw [uniform_weighted_divisor_word_average B
    (fun p : ↥(data.P ∪ data.Q) => p.val) (fun p => (data.prime p).pos)
    (fun p => hB _ p.property) label
    (fun t => wordDisplacement h (word.take t.1.val)) weight
    (attachedCatalogAvoidance data s B D word)]
  apply hb.trans_eq
  apply sum_congr rfl
  intro U _
  unfold prohibitedDesignatedTerm prohibitedWordDifference
  simp only [designation_sdiff_decidable (fun a b => Classical.propDecidable (a = b))
    (inferInstance : DecidableEq (Fin R × Fin J))]
  rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceClassPartition
namespace OAI

/-! Partition the actual trace majorant into singleton, many-unlit, high-rank and good classes. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem prohibited_trace_class_bound {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hdep : ∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) →
      weight a x = weight a y)
    (Smax Umax : ℕ) (rankBad : α → Finset (Fin R × Fin J) → Prop) :
    (∑ a ∈ F, |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) ≤
      (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card),
        |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) +
      (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
        ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (fun U => Umax < U.card),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) +
      (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
        ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ Umax ∧ rankBad a U),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) +
      (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
        ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
          (fun U => U.card ≤ Umax ∧ ¬rankBad a U),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) := by
  let A (a : α) := |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|
  let T (a : α) (U : Finset (Fin R × Fin J)) :=
    prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U
  have hp (a : α) : (∑ U ∈ (nonsingletonSlots (label a)).powerset, T a U) =
      (∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (fun U => Umax < U.card), T a U) +
      (∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ rankBad a U), T a U) +
      (∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ ¬rankBad a U), T a U) := by
    simp only [sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro U _
    by_cases hu : Umax < U.card <;> by_cases hr : rankBad a U
    · simp [hu, Nat.not_le.mpr hu]
    · simp [hu, Nat.not_le.mpr hu]
    · simp [hu, Nat.le_of_not_gt hu, hr]
    · simp [hu, Nat.le_of_not_gt hu, hr]
  change (∑ a ∈ F, A a) ≤ _
  calc
    _ = (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card), A a) +
        (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax), A a) := by
      rw [sum_filter, sum_filter, ← sum_add_distrib]
      apply sum_congr rfl
      intro a _
      by_cases ha : Smax < (singletonLabels (label a)).card
      · simp [ha, Nat.not_le.mpr ha]
      · simp [ha, Nat.le_of_not_gt ha]
    _ ≤ (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card), A a) +
        (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
          ∑ U ∈ (nonsingletonSlots (label a)).powerset, T a U) := by
      apply add_le_add_right
      apply sum_le_sum
      intro a ha
      exact prohibited_centering_bound data hB s D (word a) (label a) base
        (weight a) (hw a (mem_filter.mp ha).1) (hdep a (mem_filter.mp ha).1)
    _ = _ := by
      simp_rw [hp, sum_add_distrib]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceFourBounds
namespace OAI

/-! Combine the four estimates on one literal word catalog.  The bad classes
may be estimated on the larger catalog before the earlier restrictions. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem prohibited_trace_four_bounds {α : Type*} {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D : ℕ) (F : Finset α) (word : α → List SignedStep)
    (label : α → Fin R × Fin J → ↥(data.P ∪ data.Q))
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : α → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x)
    (hdep : ∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) →
      weight a x = weight a y)
    (Smax Umax : ℕ) (rankBad : α → Finset (Fin R × Fin J) → Prop)
    (single unlit rank good : ℝ)
    (hsingle : (∑ a ∈ F.filter (fun a => Smax < (singletonLabels (label a)).card),
      |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) ≤ single)
    (hunlit : (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
      ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => Umax < U.card),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ unlit)
    (hrank : (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (rankBad a),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ rank)
    (hgood : (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
      ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ ¬rankBad a U),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ good) :
    (∑ a ∈ F, |prohibitedCenteredAverage data hB s D (word a) (label a) (weight a)|) ≤
      single + unlit + rank + good := by
  have hnonneg (a : α) (ha : a ∈ F) (U : Finset (Fin R × Fin J)) :
      0 ≤ prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U :=
    prohibitedDesignatedTerm_nonneg data hB s D (word a) (label a) base (weight a) (hw a ha) U
  have hr : (∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
      ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => U.card ≤ Umax ∧ rankBad a U),
      prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U) ≤ rank := by
    apply le_trans _ hrank
    calc
      _ ≤ ∑ a ∈ F.filter (fun a => (singletonLabels (label a)).card ≤ Smax),
          ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter (rankBad a),
          prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum_of_subset_of_nonneg
        · intro U hU
          exact mem_filter.mpr ⟨(mem_filter.mp hU).1, (mem_filter.mp hU).2.2⟩
        · intro U _ _
          exact hnonneg a (mem_filter.mp ha).1 U
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro a ha _
        exact sum_nonneg (fun U _ => hnonneg a ha U)
  exact (prohibited_trace_class_bound data hB s D F word label base weight hw hdep
    Smax Umax rankBad).trans (add_le_add (add_le_add (add_le_add hsingle hunlit) hr) hgood)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedHighRankDecay
namespace OAI

/-! The high-rank estimate for the literal designated trace terms.  Common integer
origins and all prime-support conditions follow from the supplied words. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_high_rank_decay (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Q D Y H Z s N : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hZ : ∀ p ∈ data.P ∪ data.Q, p ≤ Z)
      (P : Fin J → Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (j : Fin J) (perfect : Finset (Fin R)) (cut : Fin R)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin Z) (U : Finset (Fin R × Fin J))
      (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        (↥(data.P ∪ data.Q) → Fin Z) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, P l ⊆ data.P) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) → 1 ≤ primeHarmonicMass (P j) →
      (∀ l, ∀ p ∈ P l, p.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, a.2 i) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
        (by change 0 < R; omega) h perfect cut ⌊L ^ (1 / 50 : ℝ)⌋₊) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      (∀ a ∈ F, perfect ⊆ perfectRows (label a) U) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, U ⊆ nonsingletonSlots (label a)) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        MainPaddingTests Subtype.val h Z (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, prohibitedDesignatedTerm data hZ s N
        (columnTupleWord a.1 forward a.2) (label a) base (weight a) U) ≤
        Real.exp (-(1 / 8 : ℝ) * L ^ (203 / 200 : ℝ)) := by
  filter_upwards [eventually_weighted_high_rank_words h Cj Cm Cw hCj hCm hCw] with L hdecay
  intro J R M Q D Y H Z s N data hZ P F forward j perfect cut label base U weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
    hpairs hq hd hrank hlabel hperfect hW hWexp hU hcap hw hwcap hpadding hcost
  let E := F.filter (fun a => LitConsistent (nonsingletonSlots (label a) \ U) (label a)
    (tupleForcedTarget data hZ (columnTupleWord a.1 forward a.2) (label a)))
  have hEF : E ⊆ F := filter_subset _ _
  obtain ⟨origin, horigin⟩ := ambient_tuple_lit_origins E
    (fun a => a.1) Z Subtype.val data.prime Subtype.val_injective
    (fun p => hZ _ p.property) label (fun a ha => hlabel a (hEF ha)) U
    (fun a i => wordDisplacement h ((columnTupleWord a.1 forward a.2).take i.val))
    base perfect (fun a ha => hperfect a (hEF ha)) (fun a ha => (mem_filter.mp ha).2)
  have hlow : ∀ a ∈ E, ∀ p ∈ nonsingletonLabels (label a), (H : ℝ) ≤ p.val := by
    intro a ha p hp
    have hn : 0 < (labelOccurrences (label a) p).card :=
      lt_of_lt_of_le (by norm_num) (mem_filter.mp hp).2
    obtain ⟨t, ht⟩ := card_pos.mp hn
    have he : label a t = p := (mem_filter.mp ht).2
    rw [← he, hlabel a (hEF ha) t.1 t.2]
    exact_mod_cast hlo _ (hP t.2 (a.1 t.2 t.1).property)
  have hb := hdecay ↥(data.P ∪ data.Q) J R M Q D Y H Z P data.Q E forward j perfect cut
    (fun w q => origin (w, q)) Subtype.val (fun p => (data.prime p).pos)
    (fun p => hZ _ p.property) label
    (fun a => tupleForcedTarget data hZ (columnTupleWord a.1 forward a.2) (label a))
    base U weight (fun a => attachedCatalogAvoidance data s Z N (columnTupleWord a.1 forward a.2))
    cap W hR hRL hJ hM hT hRp hmass hQmass hV hprime hdisjoint
    (fun p hp => hlo p (hP j hp)) (fun p hp => hY p (hP j hp)) hQ hD hYexp hH
    (fun a ha => hq a (hEF ha)) (fun a ha => hd a (hEF ha))
    (fun a ha i => data.padding_squarefree _ (hpairs a (hEF ha) i))
    (fun a ha i => data.padding_pool _ (hpairs a (hEF ha) i))
    (fun a ha i => data.padding_card _ (hpairs a (hEF ha) i))
    (fun a ha => hrank a (hEF ha))
    (fun a ha i hi => horigin a ha i hi j) hW hWexp Subtype.val_injective
    (fun a ha => hU a (hEF ha)) hlow
    (fun a ha => supplied_tuple_padding_disjoint data a.1 a.2
      (hpairs a (hEF ha)) hprime hdisjoint)
    (fun a ha => supplied_tuple_label_seen data a.1 forward a.2 (hpairs a (hEF ha))
      hprime hdisjoint (label a) (hlabel a (hEF ha)))
    (fun a ha p hp => ⟨⟨p, data.supplied_word_support_subset _
      (columnTupleWord_pairs data a.1 forward a.2 (hpairs a (hEF ha))) hp⟩, rfl⟩)
    (fun a ha => hcap a (hEF ha)) (fun a ha => hw a (hEF ha))
    (fun a ha => hwcap a (hEF ha))
    (fun _ _ _ => witnessAvoidance_abs_le_one _ _)
    (fun a ha x hx => supplied_tuple_padding_retained data a.1 forward a.2
      (hpairs a (hEF ha)) hprime hdisjoint (label a) (hlabel a (hEF ha)) x
      (hpadding a (hEF ha) x hx))
    (fun a ha => hcost a (hEF ha))
  apply le_trans _ hb
  simp only [E, sum_filter, prohibitedDesignatedTerm, prohibitedWordDifference]
  rfl

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankTraceSlices
namespace OAI

/-! Sum the actual variable perfect-row and offending-column choices by fixed
rank slices.  Only finite positive sums are enlarged. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem prohibited_high_rank_sum_le_slices {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D r : ℕ) (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      Fin R × Fin J → ↥(data.P ∪ data.Q))
    (forward : Fin R → Bool) (hR : 0 < R) (cut : Fin R)
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j)
        hR h (perfectRows (label a) U) cut r),
      prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
        (label a) base (weight a) U) ≤
      ∑ U : Finset (Fin R × Fin J), ∑ perfect : Finset (Fin R), ∑ j : Fin J,
        ∑ a ∈ highRankTraceSlice F label forward hR h r cut U perfect j,
          prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
            (label a) base (weight a) U := by
  let T a U := prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
    (label a) base (weight a) U
  let S a U perfect j := U ⊆ nonsingletonSlots (label a) ∧
    perfectRows (label a) U = perfect ∧
    ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j) hR h perfect cut r
  have hT a (ha : a ∈ F) U : 0 ≤ T a U :=
    prohibitedDesignatedTerm_nonneg data hB s D _ _ base _ (hw a ha) U
  have hnonneg a (ha : a ∈ F) U perfect j :
      0 ≤ if S a U perfect j then T a U else 0 := by
    split_ifs
    · exact hT a ha U
    · exact le_rfl
  have hpoint a (ha : a ∈ F) U (hU : U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j)
        hR h (perfectRows (label a) U) cut r)) :
      T a U ≤ ∑ perfect : Finset (Fin R), ∑ j : Fin J, if S a U perfect j then T a U else 0 := by
    obtain ⟨hU, j, hj⟩ := mem_filter.mp hU
    have hs : S a U (perfectRows (label a) U) j := ⟨mem_powerset.mp hU, rfl, hj⟩
    calc
      T a U = if S a U (perfectRows (label a) U) j then T a U else 0 := (if_pos hs).symm
      _ ≤ ∑ j : Fin J, if S a U (perfectRows (label a) U) j then T a U else 0 :=
        single_le_sum (f := fun j => if S a U (perfectRows (label a) U) j then T a U else 0)
          (fun j _ => hnonneg a ha U _ j) (mem_univ j)
      _ ≤ _ := single_le_sum
        (f := fun perfect => ∑ j : Fin J, if S a U perfect j then T a U else 0)
        (fun perfect _ => sum_nonneg (fun j _ => hnonneg a ha U perfect j))
        (mem_univ (perfectRows (label a) U))
  calc
    _ ≤ ∑ a ∈ F, ∑ U : Finset (Fin R × Fin J), ∑ perfect : Finset (Fin R), ∑ j : Fin J,
        if S a U perfect j then T a U else 0 := by
      apply sum_le_sum
      intro a ha
      apply (sum_le_sum (fun U hU => hpoint a ha U hU)).trans
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro U _ _
      exact sum_nonneg (fun perfect _ => sum_nonneg (fun j _ => hnonneg a ha U perfect j))
    _ = _ := by
      simp only [highRankTraceSlice, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro U _
      rw [sum_comm]
      apply sum_congr rfl
      intro perfect _
      rw [sum_comm]

theorem prohibited_high_rank_sum_le_uniform_slices {h J M R B : ℕ} {P : Fin J → Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
    (s D r : ℕ) (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
    (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      Fin R × Fin J → ↥(data.P ∪ data.Q))
    (forward : Fin R → Bool) (hR : 0 < R) (cut : Fin R)
    (base : ↥(data.P ∪ data.Q) → Fin B)
    (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
      (↥(data.P ∪ data.Q) → Fin B) → ℝ)
    (hw : ∀ a ∈ F, ∀ x, 0 ≤ weight a x) (E : ℝ)
    (hE : ∀ U perfect j,
      (∑ a ∈ highRankTraceSlice F label forward hR h r cut U perfect j,
        prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
          (label a) base (weight a) U) ≤ E) :
    (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
      (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 hR forward a.2 j)
        hR h (perfectRows (label a) U) cut r),
      prohibitedDesignatedTerm data hB s D (columnTupleWord a.1 forward a.2)
        (label a) base (weight a) U) ≤ (2 : ℝ) ^ (R * J) * 2 ^ R * J * E := by
  apply (prohibited_high_rank_sum_le_slices data hB s D r F label forward hR cut base weight hw).trans
  calc
    _ ≤ ∑ _U : Finset (Fin R × Fin J), ∑ _perfect : Finset (Fin R), ∑ _j : Fin J, E :=
      sum_le_sum (fun U _ => sum_le_sum (fun perfect _ => sum_le_sum (fun j _ => hE U perfect j)))
    _ = _ := by
      simp only [sum_const, card_univ, nsmul_eq_mul, Fintype.card_finset, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.HighRankTraceTotal
namespace OAI

/-! The high-rank contribution with all designations, perfect-row sets and
columns summed.  Lit consistency supplies the arithmetic origin in each slice. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_high_rank_total (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Q D Y H B s N : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → ℕ)))
      (forward : Fin R → Bool) (cut : Fin R)
      (label : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → ℕ)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, P l ⊆ data.P) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) → (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ l, ∀ p ∈ P l, p.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      (Q : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, a.2 i) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, a.2 i ≤ Q) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        MainPaddingTests Subtype.val h B (columnTupleWord a.1 forward a.2) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward a.2 j)
          (by change 0 < R; omega) h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
        prohibitedDesignatedTerm data hB s N (columnTupleWord a.1 forward a.2)
          (label a) base (weight a) U) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_prohibited_high_rank_decay h Cj Cm Cw hCj hCm hCw,
    eventually_rank_slice_decay Cj hCj] with L hdecay hslice
  intro J R M Q D Y H B s N data hB P F forward cut label base weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
    hpairs hq hd hlabel hW hWexp hcap hw hwcap hpadding hcost
  refine le_trans ?_ (hslice R J hRL hJ)
  apply prohibited_high_rank_sum_le_uniform_slices data hB s N _ F label forward (by omega)
    cut base weight hw
  intro U perfect j
  let E := highRankTraceSlice F label forward (show 0 < R by omega) h
    ⌊L ^ (1 / 50 : ℝ)⌋₊ cut U perfect j
  have hEF : E ⊆ F := filter_subset _ _
  exact hdecay J R M Q D Y H B s N data hB P E forward j perfect cut label base U weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass (hV j) hprime hdisjoint hlo hY hQ hD hYexp hH
    (fun a ha => hpairs a (hEF ha)) (fun a ha => hq a (hEF ha))
    (fun a ha i => hd a (hEF ha) i j)
    (fun _ ha => (mem_filter.mp ha).2.2.2)
    (fun a ha => hlabel a (hEF ha))
    (fun _ ha => by rw [(mem_filter.mp ha).2.2.1]) hW hWexp
    (fun _ ha => (mem_filter.mp ha).2.1)
    (fun a ha => hcap a (hEF ha)) (fun a ha => hw a (hEF ha))
    (fun a ha => hwcap a (hEF ha)) (fun a ha => hpadding a (hEF ha))
    (fun a ha => hcost a (hEF ha))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnHighRankTraceTotal
namespace OAI

/-! The high-rank bound on the same column/padding catalog as the good class. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_column_high_rank_total (h : ℕ) (Cj Cm Cw : ℝ)
    (hCj : 0 ≤ Cj) (hCm : 0 ≤ Cm) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (J R M Qmax D Y H B s N : ℕ)
      (data : ProhibitedPrimeFamily h J M)
      (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (forward : Fin R → Bool) (cut : Fin R)
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (W : ℝ),
      (hR : 1 ≤ R) → (R : ℝ) ≤ 2 * L →
      (J : ℝ) ≤ Cj * Real.log L → (M : ℝ) ≤ Cm * Real.log L →
      ((R * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ l, P l ⊆ data.P) →
      (∀ l, primeHarmonicMass (P l) ≤ L ^ (2 : ℕ)) →
      primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) → (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ l, ∀ p ∈ P l, p.Prime) →
      (∀ l m, m ≠ l → Disjoint (P l) (P m)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      (Qmax : ℝ) ≤ Real.exp (100 * L + 1) → (D : ℝ) ≤ Real.exp (2 * L) →
      (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, (a.2 i).val ≤ Qmax) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ D) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 →
        MainPaddingTests Subtype.val h B (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      (∀ a ∈ F, cap a * 2 ^ (singletonLabels (label a)).card ≤ W) →
      (∑ a ∈ F, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
        (fun U => ∃ j, ¬ColumnLowRank (tupleColumnPattern a.1 (by omega) forward (fun i => (a.2 i).val) j)
          (by change 0 < R; omega) h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊),
        prohibitedDesignatedTerm data hB s N (columnTupleWord a.1 forward (fun i => (a.2 i).val))
          (label a) base (weight a) U) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_prohibited_high_rank_total h Cj Cm Cw hCj hCm hCw] with L hdecay
  intro J R M Qmax D Y H B s N data hB P Q F forward cut label base weight cap W
    hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
    hpairs hq hd hlabel hW hWexp hcap hweight hwcap hpadding hcost
  by_cases hF : F.Nonempty
  · have : Nonempty (ColumnPrimeAssignment J R P × (Fin R → Q)) := ⟨hF.choose⟩
    let encode := columnNatCode (P := P) (Q := Q) (R := R)
    have hinj : Function.Injective encode := columnNatCode_injective
    let decode := Function.invFun encode
    have hdecode (a : ColumnPrimeAssignment J R P × (Fin R → Q)) : decode (encode a) = a :=
      Function.leftInverse_invFun hinj a
    let E := F.image encode
    have hpull (a : ColumnPrimeAssignment J R P × (Fin R → ℕ)) (ha : a ∈ E) :
        ∃ b ∈ F, a = encode b := by
      obtain ⟨b, hb, rfl⟩ := mem_image.mp ha
      exact ⟨b, hb, rfl⟩
    have hb := hdecay J R M Qmax D Y H B s N data hB P E forward cut
      (fun a => label (decode a)) base (fun a => weight (decode a)) (fun a => cap (decode a)) W
      hR hRL hJ hM hT hRp hP hmass hQmass hV hprime hdisjoint hlo hY hQ hD hYexp hH
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; exact hpairs b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; exact hq b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; exact hd b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hlabel b hb)
      hW hWexp
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hcap b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hweight b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hwcap b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hpadding b hb)
      (by intro a ha; obtain ⟨b,hb,rfl⟩ := hpull a ha; simp only [hdecode]; simpa only [encode, columnNatCode] using hcost b hb)
    rw [show E = F.image encode from rfl, sum_image (fun _ _ _ _ he => hinj he)] at hb
    simp only [hdecode] at hb
    simp only [encode, columnNatCode] at hb
    convert (preTransparency := .instances) hb using 1
    apply sum_congr rfl
    intro a _
    apply sum_congr
    · ext U
      constructor
      · intro hU
        exact mem_filter.mpr (mem_filter.mp hU)
      · intro hU
        exact mem_filter.mpr (mem_filter.mp hU)
    · intro U _
      rfl
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnManyUnlitDecay
namespace OAI

/-! The complete many-unlit sum on the same column/padding catalog as the
good and high-rank classes. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_column_many_unlit_decay (C Ce Cs : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∀ᶠ L : ℝ in atTop, ∀ (R J M S B h s D : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ) (forward : Fin R → Bool)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (external H : ℝ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      1 ≤ R → (R : ℝ) ≤ 2 * L →
      ((S + R * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((R * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (∀ p ∈ data.P, H ≤ p) →
      (∀ w ∈ F, ∀ i, (columnTuple w.1 i, (w.2 i).val) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i j, (label w (i, j)).val = (w.1 j i).val) →
      (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) →
      (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) x) →
      (∀ w ∈ F, cap w * 2 ^ (singletonLabels (label w)).card ≤
        crudeTraceWeight R S (fun i => (w.2 i).val) L external) →
      (∑ w ∈ F, ∑ U ∈ (nonsingletonSlots (label w)).powerset.filter
        (fun U => ⌊L ^ (1 / 50 : ℝ)⌋₊ < U.card),
        prohibitedDesignatedTerm data hB s D
          (columnTupleWord w.1 forward (fun i => (w.2 i).val)) (label w) base (weight w) U) ≤
        Real.exp (-L ^ (101 / 100 : ℝ)) := by
  filter_upwards [eventually_prohibited_many_unlit_decay C Ce Cs hC hCe hCs,
    eventually_ge_atTop (0 : ℝ)] with L hdecay hL
  intro R J M S B h s D data hB P Q forward F label base weight cap external H
    hprime hdisjoint hR hRL hS hJM hT hRp hext hextL hPmass hQmass hM hH hlo
    hpairs hlabel hcap hweight hwcap hpadding hcost
  by_cases hF : F.Nonempty
  · have : Nonempty (ColumnPrimeAssignment J R P × (Fin R → Q)) := ⟨hF.choose⟩
    let encode := columnStepCode (P := P) (Q := Q) forward
    have hinj : Function.Injective encode := columnStepCode_injective forward hprime hdisjoint
    let decode := Function.invFun encode
    have hdecode (w : ColumnPrimeAssignment J R P × (Fin R → Q)) : decode (encode w) = w :=
      Function.leftInverse_invFun hinj w
    let E := F.image encode
    have hpull (w : Fin R → SignedStep) (hw : w ∈ E) : ∃ v ∈ F, w = encode v := by
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
      exact ⟨v, hv, rfl⟩
    have hb := hdecay R J M S B h s D data hB E (fun w => label (decode w)) base
      (fun w => weight (decode w)) (fun w => cap (decode w)) external H
      hR hRL hS hJM hT hRp hext hextL hPmass hQmass hM hH hlo
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; exact hpairs v hv)
      (by
        intro w hw
        obtain ⟨v,hv,rfl⟩ := hpull w hw
        intro i
        change (columnTuple v.1 i).primeFactors = univ.image (fun j => (label (decode (encode v)) (i,j)).val)
        rw [hdecode, columnTuple_primeFactors v.1 i hprime hdisjoint]
        congr 1
        funext j
        exact (hlabel v hv i j).symm)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hweight v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hwcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode, encode, columnStepCode_word] using hpadding v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw
          simpa only [hdecode, encode, columnStepCode] using hcost v hv)
    rw [largeUnlitCatalog_sum E (fun w => label (decode w)) L hL
      (fun w U => prohibitedDesignatedTerm data hB s D (List.ofFn w)
        (label (decode w)) base (weight (decode w)) U)] at hb
    rw [show E = F.image encode from rfl, sum_image (fun _ _ _ _ he => hinj he)] at hb
    simpa only [hdecode, encode, columnStepCode_word] using hb
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnTraceTotal
namespace OAI

/-! All four contributions to the literal centered trace on a single
column/padding catalog, with the full external dimension allowance retained. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_column_trace_total_oai (h : ℕ) (C Ce Cs Cw W : ℝ)
    (hC : 0 ≤ C) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B s D k n K₀ H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (F : Finset (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)))
      (_hR : 0 < 2 * k) (forward : Fin (2 * k) → Bool)
      (label : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        Fin (2 * k) × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) → ℝ)
      (A external : ℝ) (cut : Fin (2 * k))
      (u : ℕ → ℝ) (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
      (g : ℤ → ℝ) (K : ℝ)
      (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
      (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
      (origin : (↥(data.P ∪ data.Q) → Fin B) → ℤ),
      1 ≤ J → L / 2 ≤ (k : ℝ) → (k : ℝ) ≤ L →
      ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      ((⌊L ^ (1 / 4 : ℝ)⌋₊ + 2 * k * J : ℕ) : ℝ) ≤ Cs * L * Real.log L →
      ((2 * k * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      ((2 * k : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      (∀ j, P j ⊆ data.P) →
      (∀ j, 1 ≤ primeHarmonicMass (P j)) →
      (∀ j, primeHarmonicMass (P j) ≤ 2 * W) →
      (∀ j, primeHarmonicMass (P j) ≤ L ^ (2 : ℕ)) →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      (M : ℝ) ≤ 100 * Real.log L →
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      (Qmax : ℝ) ≤ Real.exp (100 * L + 1) → (Dmax : ℝ) ≤ Real.exp (2 * L) →
      (∀ a ∈ F, ∀ i, (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs) →
      (∀ a ∈ F, ∀ i, (a.2 i).val ≤ Qmax) →
      (∀ a ∈ F, ∀ i j, (∏ l ∈ univ.erase j, (a.1 l i).val) ≤ Dmax) →
      (∀ a ∈ F, ∀ i j, (label a (i, j)).val = (a.1 j i).val) →
      0 ≤ A → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      0 ≤ external → external ≤ Real.exp (Ce * L) →
      (∀ a ∈ F, 0 ≤ cap a) →
      (∀ a ∈ F, ∀ x, 0 ≤ weight a x) →
      (∀ a ∈ F, ∀ x, weight a x ≤ cap a) →
      (∀ a ∈ F, cap a * 2 ^ (2 * k * J + (singletonLabels (label a)).card) ≤ A) →
      (∀ a ∈ F, (singletonLabels (label a)).card ≤ ⌊L ^ (1 / 4 : ℝ)⌋₊ →
        cap a * 2 ^ (singletonLabels (label a)).card ≤
        crudeTraceWeight (2 * k) ⌊L ^ (1 / 4 : ℝ)⌋₊ (fun i => (a.2 i).val) L external) →
      (∀ a ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label a) → x i = y i) → weight a x = weight a y) →
      (∀ a ∈ F, ∀ x, weight a x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x) →
      2 * k + n * s ≤ D →
      (∀ a ∈ F, ⌊L ^ (1 / 4 : ℝ)⌋₊ < (singletonLabels (label a)).card →
        n * (s * J) < (singletonLabels (label a)).card) →
      (D : ℝ) ≤ 4 * L → 0 < n → (n : ℝ) ≤ 4 * L → 8 * K₀ ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K₀ : ℝ) → (K₀ : ℝ) ≤ L →
      0 < h → 0 < s → L ^ (1 / 10 : ℝ) / 2 ≤ (s : ℝ) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      (∀ a ∈ F, ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop cut.val).IsChain
        (fun a b => a.tuple ≠ b.tuple)) →
      0 ≤ K → (∀ q, 0 ≤ u q) →
      (∀ a ∈ F, ∀ x, weight a x ≤
        retainedColumnPaddingWeight Q u eligible g L K extra next (origin x) a.1 a.2) →
      Real.exp (108 * L) * (∑ a ∈ F, |prohibitedCenteredAverage data hB s D
        (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (label a) (weight a)|) ≤
        Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
          2 * Real.exp (-L ^ (101 / 100 : ℝ))) +
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_prohibited_column_singleton_decay C Cw hC hCw,
    eventually_prohibited_column_many_unlit_decay C Ce Cs hC hCe hCs,
    eventually_prohibited_column_high_rank_total h C C Cw hC hC hCw,
    eventually_prohibited_good_trace_total W hW, eventually_ge_atTop (0 : ℝ)]
    with L hsingle hunlit hrank hgood hL
  intro J M B s D k n K₀ H Y Qmax Dmax data hB P Q F hR forward label base weight cap
    A external cut u eligible g K extra next origin hJ hklo hkhi hJM hS hslots hRp
    hP hVm hVM hVpoly hmass hPmass hQmass hM hprime hdisjoint hlo hhi hY hYexp hH
    hQmax hDmax hpairs hq hd hlabel hA hAexp hext hextL hcap hw hwcap hcost hcrude
    hdep hpadding hD hn hDL hnpos hnL hKn hKlo hKhi hh hs hsL hleft hright hK hu hpad
  let word (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    columnTupleWord a.1 forward (fun i => (a.2 i).val)
  let large := F.filter (fun a => ⌊L ^ (1 / 4 : ℝ)⌋₊ < (singletonLabels (label a)).card)
  let small := F.filter (fun a => (singletonLabels (label a)).card ≤ ⌊L ^ (1 / 4 : ℝ)⌋₊)
  let bad (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
      (U : Finset (Fin (2 * k) × Fin J)) := ∃ j, ¬ColumnLowRank
    (tupleColumnPattern a.1 hR forward (fun i => (a.2 i).val) j)
    hR h (perfectRows (label a) U) cut ⌊L ^ (1 / 50 : ℝ)⌋₊
  have hlarge : large ⊆ F := filter_subset _ _
  have hsmall : small ⊆ F := filter_subset _ _
  have hRL : ((2 * k : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith
  have hJC : (J : ℝ) ≤ C * Real.log L := by
    have : (J : ℝ) ≤ (J + M : ℕ) := by exact_mod_cast Nat.le_add_right J M
    exact this.trans hJM
  have hMC : (M : ℝ) ≤ C * Real.log L := by
    have : (M : ℝ) ≤ (J + M : ℕ) := by exact_mod_cast Nat.le_add_left M J
    exact this.trans hJM
  have hRM : ((2 * k * M : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    apply le_trans _ hslots
    have : 2 * k * M ≤ 2 * k * (J + M) := Nat.mul_le_mul_left _ (Nat.le_add_left M J)
    exact_mod_cast Nat.add_le_add_right this 1
  have hsbound := hsingle h J M (2 * k) B s n D K₀ H Y data hB P Q forward large label base
    weight cap A hprime hdisjoint hA (fun a ha => hcap a (hlarge ha))
    (fun a ha => hw a (hlarge ha)) (fun a ha => hwcap a (hlarge ha))
    (fun a ha => hcost a (hlarge ha)) (fun a ha => hdep a (hlarge ha))
    (fun a ha => hpadding a (hlarge ha)) (fun a ha => hpairs a (hlarge ha))
    (fun a ha => hlabel a (hlarge ha)) hD (fun a ha => hn a (hlarge ha) (mem_filter.mp ha).2)
    hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hY hYexp hlo hhi hH hAexp
  have hubound := hunlit (2 * k) J M ⌊L ^ (1 / 4 : ℝ)⌋₊ B h s D data hB P Q forward small
    label base weight cap external H hprime hdisjoint hR hRL hS hJM hslots hRp
    hext hextL hPmass hQmass hM hH (fun p hp => by exact_mod_cast hlo p hp)
    (fun a ha => hpairs a (hsmall ha)) (fun a ha => hlabel a (hsmall ha))
    (fun a ha => hcap a (hsmall ha)) (fun a ha => hw a (hsmall ha))
    (fun a ha => hwcap a (hsmall ha)) (fun a ha => hpadding a (hsmall ha))
    (fun a ha => hcrude a (hsmall ha) (mem_filter.mp ha).2)
  have hrcost (a) (ha : a ∈ F) : cap a * 2 ^ (singletonLabels (label a)).card ≤ A := by
    apply le_trans _ (hcost a ha)
    apply mul_le_mul_of_nonneg_left _ (hcap a ha)
    exact pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (by omega)
  have hrbound := hrank J (2 * k) M Qmax Dmax Y H B s D data hB P Q F forward cut label
    base weight cap A hR hRL hJC hMC hRM hRp hP hVpoly hQmass hVm hprime hdisjoint
    hlo hhi hQmax hDmax hYexp hH hpairs hq hd hlabel hA hAexp hcap hw hwcap hpadding hrcost
  let good : ℝ := ∑ a ∈ small, ∑ U ∈ (nonsingletonSlots (label a)).powerset.filter
    (fun U => U.card ≤ ⌊L ^ (1 / 50 : ℝ)⌋₊ ∧ ¬bad a U),
    prohibitedDesignatedTerm data hB s D (word a) (label a) base (weight a) U
  have hgbound : Real.exp (108 * L) * good ≤
      (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
    have hb := hgood h J M B s D k ⌊L ^ (1 / 4 : ℝ)⌋₊ data hB P Q small hR forward
      label base weight cut u eligible g K extra next origin hJ hklo hkhi
      (Nat.floor_le (Real.rpow_nonneg hL _)) hprime hdisjoint
      (fun a ha => hpairs a (hsmall ha)) (by omega) (fun a ha => hlabel a (hsmall ha))
      (fun a ha => hdep a (hsmall ha)) (fun a ha => hpadding a (hsmall ha)) hh hs hsL
      (fun a ha => hleft a (hsmall ha)) (fun a ha => hright a (hsmall ha)) hK hu hVM
      (by
        intro a ha
        rw [← tuple_label_singleton_count a.1 hdisjoint Subtype.val Subtype.val_injective
          (label a) (hlabel a (hsmall ha))]
        exact (mem_filter.mp ha).2)
      (fun a ha => hw a (hsmall ha)) (fun a ha => hpad a (hsmall ha))
    convert (preTransparency := .instances) hb using 1
    congr 1
    apply sum_congr rfl
    intro a _
    apply sum_congr
    · ext U
      constructor
      · intro hU
        obtain ⟨hmem, hcard, hbad⟩ := mem_filter.mp hU
        apply mem_filter.mpr
        refine ⟨hmem, hcard, ?_⟩
        intro j
        by_contra hj
        exact hbad ⟨j, hj⟩
      · intro hU
        obtain ⟨hmem, hcard, hlow⟩ := mem_filter.mp hU
        apply mem_filter.mpr
        refine ⟨hmem, hcard, ?_⟩
        rintro ⟨j, hj⟩
        exact hj (hlow j)
    · intro U _
      rfl
  have hb := prohibited_trace_four_bounds data hB s D F word label base weight hw hdep
    ⌊L ^ (1 / 4 : ℝ)⌋₊ ⌊L ^ (1 / 50 : ℝ)⌋₊ bad
    (Real.exp (-L ^ (21 / 20 : ℝ))) (Real.exp (-L ^ (101 / 100 : ℝ)))
    (Real.exp (-L ^ (101 / 100 : ℝ))) good hsbound hubound
    (by
      convert (preTransparency := .instances) hrbound using 1
      apply sum_congr rfl
      intro a _
      apply sum_congr
      · dsimp only [bad]
        exact filter_congr_decidable _ _ _
      · intro U _
        rfl)
    (by
      dsimp only [good, small]
      apply le_of_eq
      apply sum_congr
      · exact filter_congr_decidable _ _ _
      · intro a _
        apply sum_congr
        · exact filter_congr_decidable _ _ _
        · intro U _
          rfl)
  calc
    _ ≤ Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        Real.exp (-L ^ (101 / 100 : ℝ)) + Real.exp (-L ^ (101 / 100 : ℝ)) + good) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) + Real.exp (108 * L) * good := by ring
    _ ≤ _ := add_le_add le_rfl hgbound

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.eventually_prohibited_column_trace_total_oai := @OAI.TwoPointCorrelations.eventually_prohibited_column_trace_total_oai
