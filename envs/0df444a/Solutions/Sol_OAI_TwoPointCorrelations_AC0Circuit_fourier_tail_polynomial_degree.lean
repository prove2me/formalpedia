-- Prove2me | solution 1 for OAI.TwoPointCorrelations.AC0Circuit.fourier_tail_polynomial_degree
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:23:38.949182+00:00
-- url     : https://prove2.me/submissions/bdef1701-5751-4fe1-bfd5-df1dd950e7a8

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

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

open _root_.Finset hiding sum_le_sum_of_injOn
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

open _root_.Finset hiding sum_le_sum_of_injOn

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

open _root_.Finset hiding sum_le_sum_of_injOn

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
namespace OAI

/-! Elementary finite averaging identities used to assemble encoded marginals. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn


@[simp] lemma uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by simp [uniformAverage]








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




lemma cubeAverage_sub {n : ℕ} (f g : BooleanCube n → ℝ) :
    cubeAverage (fun x => f x - g x) = cubeAverage f - cubeAverage g := by
  simp [cubeAverage, Finset.sum_sub_distrib, sub_div]



lemma cubeAverage_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → BooleanCube n → ℝ) :
    cubeAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage (f i) := by
  simp only [cubeAverage, Finset.sum_div]
  rw [Finset.sum_comm]

lemma cubeAverage_mono {n : ℕ} {f g : BooleanCube n → ℝ}
    (h : ∀ x, f x ≤ g x) : cubeAverage f ≤ cubeAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)


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


lemma walsh_flipBit {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (x : BooleanCube n) :
    walsh S (flipBit i x) = if i ∈ S then -walsh S x else walsh S x := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have hrest : (∏ j ∈ S.erase i, booleanSign ((flipBit i x) j)) =
        ∏ j ∈ S.erase i, booleanSign (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [flipBit, Function.update_of_ne (mem_erase.mp hj).1]
    unfold walsh
    rw [← Finset.prod_erase_mul _ _ hi, hrest,
      ← Finset.prod_erase_mul _ (fun j => booleanSign (x j)) hi]
    simp [flipBit]
  · rw [if_neg hi]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by intro h; subst j; exact hi hj
    simp [flipBit, Function.update_of_ne hji]

lemma cubeAverage_eq_zero_of_flip {n : ℕ} (f : BooleanCube n → ℝ) (i : Fin n)
    (hf : ∀ x, f (flipBit i x) = -f x) : cubeAverage f = 0 := by
  have hsum : (∑ x, f (flipBit i x)) = ∑ x, f x :=
    (flipBit i).sum_comp f
  simp_rw [hf] at hsum
  rw [Finset.sum_neg_distrib] at hsum
  have hz : (∑ x, f x) = 0 := by linarith
  simp [cubeAverage, hz]


lemma cubeAverage_walsh_mul {n : ℕ} (S T : Finset (Fin n)) :
    cubeAverage (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T; simp
  · rw [if_neg hST]
    have hex : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      simpa only [Finset.ext_iff, not_forall] using hST
    obtain ⟨i, hi⟩ := hex
    apply cubeAverage_eq_zero_of_flip _ i
    intro x
    by_cases hSi : i ∈ S
    · have hTi : i ∉ T := fun h => hi ⟨fun _ => h, fun _ => hSi⟩
      simp [walsh_flipBit, hSi, hTi]
    · have hTi : i ∈ T := by
        by_contra hnot
        apply hi
        simp [hSi, hnot]
      simp [walsh_flipBit, hSi, hTi]



















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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ReciprocalPaddingLaw
namespace OAI

/-! The harmonic divisor law `4^omega(q)/(q S)` is an actual finite
independent prime-selection law with inclusion probabilities `4/(p+4)`. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical







lemma FiniteLaw.independent_average_coordinate {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] (μ : ι → FiniteLaw A) (i : ι) (f : A → ℝ) :
    (FiniteLaw.independent μ).average (fun x => f (x i)) = (μ i).average f := by
  have hh := FiniteLaw.independent_average_product μ (fun j x => if j = i then f x else 1)
  have he (j : ι) : (μ j).average (fun x => if j = i then f x else 1) =
      if j = i then (μ i).average f else 1 := by
    by_cases hj : j = i
    · subst j
      simp
    · simp [hj]
  simpa only [he, prod_ite_eq', mem_univ, ite_true] using hh



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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ResidueRestriction
namespace OAI

/-! Restriction of a product law to selected prime coordinates.  The
coordinate laws may depend on the prime; no common-modulus uniformity is
assumed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw


lemma independent_average_restrict {ι A : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype A]
    (μ : ι → FiniteLaw A) (S : Finset ι) (f : (S → A) → ℝ) :
    (independent μ).average (fun x => f (fun i : S => x i)) =
      (independent (fun i : S => μ i)).average f := by
  rw [independent_average_split μ S]
  simp only [joinCoordinates_mem, average_const]


end FiniteLaw

namespace ProhibitedPrimeFamily

variable {h J M B : ℕ} (data : ProhibitedPrimeFamily h J M)









end ProhibitedPrimeFamily

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialAlgebra
namespace OAI

/-! Algebra of the low-degree functions used in the circuit approximation.
Multiplication adds degrees, including after Boolean multilinearization. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical _root_.symmDiff

variable {n : ℕ}

lemma walsh_mul (S T : Finset (Fin n)) (x : BooleanCube n) :
    walsh S x * walsh T x = walsh (S ∆ T) x := by
  have hd : Disjoint (S ∆ T) (S ∩ T) := by
    rw [disjoint_left]
    intro i hi hi'
    simp only [mem_symmDiff, mem_inter] at hi hi'
    tauto
  have hu : (S ∆ T) ∪ (S ∩ T) = S ∪ T := by
    ext i
    simp only [mem_union, mem_symmDiff, mem_inter]
    tauto
  have he : walsh (S ∪ T) x * walsh (S ∩ T) x = walsh S x * walsh T x :=
    prod_union_inter
  have hh : walsh (S ∪ T) x = walsh (S ∆ T) x * walsh (S ∩ T) x := by
    simpa only [walsh, hu] using
      (prod_union hd : (∏ i ∈ (S ∆ T) ∪ (S ∩ T), booleanSign (x i)) = _)
  rw [hh, mul_assoc, walsh_mul_self, mul_one] at he
  exact he.symm





lemma WalshDegreeLE.sum {ι : Type*} (I : Finset ι) (F : ι → BooleanCube n → ℝ)
    {t : ℕ} (hF : ∀ i ∈ I, WalshDegreeLE (F i) t) :
    WalshDegreeLE (fun x => ∑ i ∈ I, F i x) t := by
  choose a ha using fun i : I => hF i i.property
  refine ⟨fun S => ∑ i : I, a i S, ?_⟩
  intro x
  dsimp only
  rw [← sum_coe_sort I]
  simp_rw [ha]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  exact (sum_mul _ _ _).symm

lemma WalshDegreeLE.mul {F G : BooleanCube n → ℝ} {p q : ℕ}
    (hF : WalshDegreeLE F p) (hG : WalshDegreeLE G q) :
    WalshDegreeLE (fun x => F x * G x) (p + q) := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hG
  let A := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ p)
  let B := (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ q)
  have heq : (fun x => F x * G x) = fun x =>
      ∑ S ∈ A, ∑ T ∈ B, (a S * b T) * walsh (S ∆ T) x := by
    funext x
    rw [ha, hb, sum_mul]
    apply sum_congr rfl
    intro S _
    rw [mul_sum]
    apply sum_congr rfl
    intro T _
    rw [← walsh_mul]
    ring
  rw [heq]
  apply WalshDegreeLE.sum A
  intro S hS
  apply WalshDegreeLE.sum B
  intro T hT
  apply WalshDegreeLE.smul
  apply WalshDegreeLE.of_walsh
  calc
    (S ∆ T).card ≤ (S ∪ T).card := card_le_card symmDiff_subset_union
    _ ≤ S.card + T.card := card_union_le S T
    _ ≤ p + q := add_le_add (mem_filter.mp hS).2 (mem_filter.mp hT).2

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SieveModel
namespace OAI

/-! The exact independent model and a generating-function bound for its
Bonferroni remainder, using only finite probability identities. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitGateApproximation
namespace OAI

/-! A single fixed polynomial approximates an arbitrarily wide AND gate
under any supplied finite input law. The sampling and its error bound are
explicit, and the polynomial degree is bounded by the number of sampled
linear factors. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma FiniteLaw.probability_mono {α : Type*} [Fintype α]
    (μ : FiniteLaw α) {E F : α → Prop} (h : ∀ x, E x → F x) :
    μ.probability E ≤ μ.probability F := by
  unfold FiniteLaw.probability
  apply μ.average_mono
  intro x
  by_cases he : E x
  · simp [he, h x he]
  · simp [he]
    split_ifs <;> norm_num



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitApproximationDegree
namespace OAI

/-! Degree bookkeeping for the random polynomial construction. The recursive
degree uses the largest child degree, rather than the number of leaves. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma WalshDegreeLE.mono {n p q : ℕ} {F : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F p) (hpq : p ≤ q) : WalshDegreeLE F q := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun S => if S.card ≤ p then a S else 0, ?_⟩
  intro x
  rw [ha]
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro S _
  by_cases hS : S.card ≤ p
  · simp [hS, hS.trans hpq]
  · simp [hS]


namespace AC0Circuit


end AC0Circuit

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionTree
namespace OAI

/-! A decision tree making at most `d` queries on any branch has Walsh
degree at most `d`. This is the spectral consequence of circuit switching. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma WalshDegreeLE.add {n d : ℕ} {F G : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F d) (hG : WalshDegreeLE G d) :
    WalshDegreeLE (fun x => F x + G x) d := by
  have h := hF.sub (hG.smul (-1))
  convert (preTransparency := .instances) h using 1
  funext x
  ring


namespace BooleanDecisionTree




theorem indicator_degree {n : ℕ} (c : BooleanDecisionTree n) :
    WalshDegreeLE c.indicator c.depth := by
  induction c with
  | leaf b =>
    cases b <;> exact WalshDegreeLE.const _ _
  | query i low high hl hh =>
    let d := max low.depth high.depth
    have hlow : WalshDegreeLE low.indicator d := hl.mono (Nat.le_max_left _ _)
    have hhigh : WalshDegreeLE high.indicator d := hh.mono (Nat.le_max_right _ _)
    have hbit := literal_indicator_degree i true
    have hnot := literal_indicator_degree i false
    have h := (hnot.mul hlow).add (hbit.mul hhigh)
    have heq : (fun x => (AC0Circuit.literal i false).indicator x * low.indicator x +
        (AC0Circuit.literal i true).indicator x * high.indicator x) =
        (query i low high).indicator := by
      funext x
      cases hx : x i <;>
        simp [indicator, eval, AC0Circuit.indicator, AC0Circuit.eval, hx]
    rw [heq] at h
    simpa only [depth, d, Nat.add_comm 1] using h

end BooleanDecisionTree

lemma WalshDegreeLE.high_coefficient_zero {n d : ℕ} {F : BooleanCube n → ℝ}
    (hF : WalshDegreeLE F d) (S : Finset (Fin n)) (hS : d < S.card) :
    walshCoefficient F S = 0 := by
  obtain ⟨a, ha⟩ := hF
  unfold walshCoefficient
  simp_rw [ha, Finset.sum_mul]
  rw [cubeAverage_sum]
  simp_rw [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  simp [Nat.not_le.mpr hS]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitWalshExpansion
namespace OAI

/-! Finite Walsh inversion and squared-error identities. These supply the
Fourier truncations used in the circuit approximation argument. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma walsh_kernel {n : ℕ} (x y : BooleanCube n) :
    (∑ S : Finset (Fin n), walsh S x * walsh S y) =
      if x = y then (2 : ℝ) ^ n else 0 := by
  have heq : (∑ S : Finset (Fin n), walsh S x * walsh S y) =
      ∏ i : Fin n, (1 + booleanSign (x i) * booleanSign (y i)) := by
    simp only [walsh, ← prod_mul_distrib]
    simpa using (prod_one_add (f := fun i : Fin n =>
      booleanSign (x i) * booleanSign (y i)) univ).symm
  rw [heq]
  by_cases hxy : x = y
  · subst y
    norm_num
  · rw [if_neg hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      simpa only [funext_iff, not_forall] using hxy
    apply prod_eq_zero (mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [booleanSign]

theorem walsh_inversion {n : ℕ} (f : BooleanCube n → ℝ) (x : BooleanCube n) :
    (∑ S : Finset (Fin n), walshCoefficient f S * walsh S x) = f x := by
  have heq : (∑ S : Finset (Fin n), walshCoefficient f S * walsh S x) =
      cubeAverage (fun y => f y * ∑ S : Finset (Fin n), walsh S y * walsh S x) := by
    simp only [mul_sum, cubeAverage_sum]
    apply sum_congr rfl
    intro S _
    unfold walshCoefficient
    have hp : (fun y => f y * (walsh S y * walsh S x)) =
        fun y => walsh S x * (f y * walsh S y) := by funext y; ring
    rw [hp, cubeAverage_mul_const, mul_comm]
  rw [heq]
  simp only [walsh_kernel, cubeAverage, mul_ite, mul_zero]
  simp [Fintype.card_bool, eq_comm]

theorem walsh_parseval {n : ℕ} (f : BooleanCube n → ℝ) :
    cubeAverage (fun x => (f x) ^ 2) =
      ∑ S : Finset (Fin n), (walshCoefficient f S) ^ 2 := by
  have heq : (fun x => (f x) ^ 2) = fun x =>
      ∑ S : Finset (Fin n), walshCoefficient f S * (f x * walsh S x) := by
    funext x
    calc
      _ = f x * (∑ S : Finset (Fin n), walshCoefficient f S * walsh S x) := by
        rw [walsh_inversion]
        ring
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro S _
        ring
  rw [heq, cubeAverage_sum]
  apply sum_congr rfl
  intro S _
  rw [cubeAverage_mul_const]
  change walshCoefficient f S * walshCoefficient f S = _
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierTruncation
namespace OAI

/-! The canonical low-degree approximation and its exact Fourier-tail error. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical



lemma walshTruncation_coefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (S : Finset (Fin n)) :
    walshCoefficient (walshTruncation f t) S =
      if S.card ≤ t then walshCoefficient f S else 0 := by
  unfold walshCoefficient walshTruncation
  simp only [sum_mul]
  rw [cubeAverage_sum]
  simp_rw [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  simp [walshCoefficient]

lemma walshCoefficient_sub {n : ℕ} (f g : BooleanCube n → ℝ)
    (S : Finset (Fin n)) :
    walshCoefficient (fun x => f x - g x) S =
      walshCoefficient f S - walshCoefficient g S := by
  unfold walshCoefficient
  simp only [sub_mul, cubeAverage_sub]

theorem walshTruncation_error {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    cubeAverage (fun x => (f x - walshTruncation f t x) ^ 2) =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => t < S.card),
        (walshCoefficient f S) ^ 2 := by
  rw [walsh_parseval, sum_filter]
  apply sum_congr rfl
  intro S _
  rw [walshCoefficient_sub, walshTruncation_coefficient]
  by_cases hS : S.card ≤ t
  · simp [hS, Nat.not_lt.mpr hS]
  · simp [hS, Nat.lt_of_not_ge hS]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestriction
namespace OAI

/-! Restrictions retain the coordinates in `L` and fix every other bit.
Walsh characters factor into their live and fixed coordinates. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


lemma walsh_restrictCube {n : ℕ} (L S : Finset (Fin n)) (y x : BooleanCube n) :
    walsh S (restrictCube L y x) = walsh (S \ L) y * walsh (S ∩ L) x := by
  have hu : S \ L ∪ S ∩ L = S := sdiff_union_inter S L
  calc
    _ = walsh (S \ L) (restrictCube L y x) *
        walsh (S ∩ L) (restrictCube L y x) := by
      simp only [walsh, ← prod_union (disjoint_sdiff_inter S L), hu]
    _ = _ := by
      congr 1
      · apply prod_congr rfl
        intro i hi
        simp only [restrictCube, if_neg (mem_sdiff.mp hi).2]
      · apply prod_congr rfl
        intro i hi
        simp only [restrictCube, if_pos (mem_inter.mp hi).2]


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment
namespace OAI

/-! Partial assignments and the consistent terms used in the canonical
decision tree of a DNF. Each term contains at most one literal per variable. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


namespace PartialAssignment





@[simp] lemma assign_empty {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) :
    ρ.assign ∅ x = ρ := by funext i; simp [assign]

lemma assign_insert {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x : BooleanCube n) (i : Fin n) :
    ρ.assign (insert i S) x = assign (Function.update ρ i (some (x i))) S x := by
  funext j
  by_cases hji : j = i <;> by_cases hj : j ∈ S <;> simp [assign, hji, hj]

lemma apply_assign_free {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (hS : S ⊆ ρ.free) (x : BooleanCube n) :
    (ρ.assign S x).apply x = ρ.apply x := by
  funext i
  by_cases hi : i ∈ S
  · have hρ : ρ i = none := (mem_filter.mp (hS hi)).2
    simp [assign, apply, hi, hρ]
  · simp [assign, apply, hi]



end PartialAssignment


namespace CubeTerm





lemma live_subset_free {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n) :
    C.live ρ ⊆ ρ.free := by
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩

lemma incompatible_mono {n : ℕ} (C : CubeTerm n) {ρ τ : PartialAssignment n}
    (hρ : ¬ C.Compatible ρ) (h : ρ.Extends τ) : ¬ C.Compatible τ := by
  intro hτ
  apply hρ
  intro i hi
  cases hri : ρ i with
  | none => exact Or.inl rfl
  | some b =>
    have hti := h i b hri
    rcases hτ i hi with hn | hv
    · rw [hti] at hn
      cases hn
    · have hb : b = C.value i := Option.some.inj (hti.symm.trans hv)
      exact Or.inr (congrArg some hb)

lemma eval_apply_of_incompatible {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hρ : ¬ C.Compatible ρ) (x : BooleanCube n) :
    C.eval (ρ.apply x) = false := by
  apply Bool.eq_false_iff.mpr
  intro he
  apply hρ
  have he : ∀ i ∈ C.support, ρ.apply x i = C.value i := of_decide_eq_true he
  intro i hi
  cases hr : ρ i with
  | none => exact Or.inl rfl
  | some b =>
    right
    have hb := he i hi
    simpa [PartialAssignment.apply, hr] using hb

lemma satisfied_assign_live_iff {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hρ : C.Compatible ρ) (x : BooleanCube n) :
    C.Satisfied (ρ.assign (C.live ρ) x) ↔ C.eval (ρ.apply x) = true := by
  simp only [Satisfied, eval, decide_eq_true_eq]
  constructor
  · intro hs i hi
    by_cases hl : i ∈ C.live ρ
    · have hn := (mem_filter.mp hl).2
      have hb := hs i hi
      simpa [PartialAssignment.assign, PartialAssignment.apply, hl, hn] using hb
    · have hn : ρ i ≠ none := fun hn => hl (mem_filter.mpr ⟨hi, hn⟩)
      have hv := (hρ i hi).resolve_left hn
      simp [PartialAssignment.apply, hv]
  · intro hx i hi
    by_cases hn : ρ i = none
    · have hl : i ∈ C.live ρ := mem_filter.mpr ⟨hi, hn⟩
      have hv := hx i hi
      simpa [PartialAssignment.assign, PartialAssignment.apply, hl, hn] using hv
    · have hl : i ∉ C.live ρ := fun hl => hn (mem_filter.mp hl).2
      simp [PartialAssignment.assign, hl, (hρ i hi).resolve_left hn]

lemma satisfied_assign_value {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hρ : C.Compatible ρ) :
    C.Satisfied (ρ.assign (C.live ρ) C.value) := by
  rw [C.satisfied_assign_live_iff ρ hρ]
  apply decide_eq_true
  intro i hi
  rcases hρ i hi with hn | hv
  · simp [PartialAssignment.apply, hn]
  · simp [PartialAssignment.apply, hv]

end CubeTerm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitAssignmentUpdates
namespace OAI

/-! Updates along the disjoint blocks of a canonical DNF path. These lemmas
also justify recovering the original restriction after decoding a block. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace PartialAssignment

lemma free_assign {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x : BooleanCube n) : (ρ.assign S x).free = ρ.free \ S := by
  ext i
  simp only [free, mem_filter, mem_univ, true_and, mem_sdiff]
  by_cases hi : i ∈ S <;> simp [assign, hi]

lemma assign_comm {n : ℕ} (ρ : PartialAssignment n) (S T : Finset (Fin n))
    (hST : Disjoint S T) (x y : BooleanCube n) :
    (ρ.assign S x).assign T y = (ρ.assign T y).assign S x := by
  funext i
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact False.elim (Finset.disjoint_left.mp hST hiS hiT)
  all_goals simp [assign, hiS, hiT]

lemma assign_injective_of_free {n : ℕ} (ρ τ : PartialAssignment n)
    (S : Finset (Fin n)) (hρ : S ⊆ ρ.free) (hτ : S ⊆ τ.free)
    (x y : BooleanCube n) (h : ρ.assign S x = τ.assign S y) : ρ = τ := by
  funext i
  by_cases hi : i ∈ S
  · exact (mem_filter.mp (hρ hi)).2.trans (mem_filter.mp (hτ hi)).2.symm
  · have he := congrFun h i
    simpa [assign, hi] using he

lemma assign_congr_on {n : ℕ} (ρ : PartialAssignment n) (S : Finset (Fin n))
    (x y : BooleanCube n) (h : ∀ i ∈ S, x i = y i) : ρ.assign S x = ρ.assign S y := by
  funext i
  by_cases hi : i ∈ S <;> simp [assign, hi, h i]

end PartialAssignment

namespace CubeTerm

lemma live_update_disjoint {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n)
    (x : BooleanCube n) : Disjoint C.support (ρ.assign (C.live ρ) x).free := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  rw [PartialAssignment.free_assign] at hf
  have hn := (mem_filter.mp (mem_sdiff.mp hf).1).2
  exact (mem_sdiff.mp hf).2 (mem_filter.mpr ⟨hi, hn⟩)



end CubeTerm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitCanonicalTree
namespace OAI

/-! The canonical tree queries the unset variables of the first compatible
term, then continues through the remaining terms. This concrete tree is the
one encoded in the switching argument. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace BooleanDecisionTree


lemma queryVariables_eval {n : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n) (ρ : PartialAssignment n)
    (x : BooleanCube n) :
    (queryVariables is k ρ).eval x = (k (ρ.assign is.toFinset x)).eval x := by
  induction is generalizing ρ with
  | nil => simp [queryVariables]
  | cons i is ih =>
    simp only [queryVariables, eval]
    cases hx : x i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · rw [ih]
      have ha := PartialAssignment.assign_insert ρ is.toFinset x i
      rw [hx] at ha
      simp only [List.toFinset_cons, ha]
    · rw [ih]
      have ha := PartialAssignment.assign_insert ρ is.toFinset x i
      rw [hx] at ha
      simp only [List.toFinset_cons, ha]


end BooleanDecisionTree



theorem canonicalDNFTree_eval {n : ℕ} (F : List (CubeTerm n))
    (ρ : PartialAssignment n) (x : BooleanCube n) :
    (canonicalDNFTree F ρ).eval x = dnfEval F (ρ.apply x) := by
  induction F generalizing ρ with
  | nil => simp [canonicalDNFTree, dnfEval, BooleanDecisionTree.eval]
  | cons C F ih =>
    by_cases hC : C.Compatible ρ
    · rw [canonicalDNFTree, if_pos hC, BooleanDecisionTree.queryVariables_eval]
      simp only [Finset.sort_toFinset]
      have happly := ρ.apply_assign_free (C.live ρ) (C.live_subset_free ρ) x
      have hs := C.satisfied_assign_live_iff ρ hC x
      by_cases hsat : C.Satisfied (ρ.assign (C.live ρ) x)
      · have he := hs.mp hsat
        simp [hsat, BooleanDecisionTree.eval, dnfEval, he]
      · have he : C.eval (ρ.apply x) = false := Bool.eq_false_iff.mpr (mt hs.mpr hsat)
        simp only [hsat, ite_false, ih, happly, dnfEval, List.any_cons, he,
          Bool.false_or]
    · have he := C.eval_apply_of_incompatible ρ hC x
      simp only [canonicalDNFTree, hC, ite_false, ih, dnfEval, List.any_cons, he,
        Bool.false_or]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionDNF
namespace OAI

/-! A decision tree of depth r is a DNF of width at most r. Both Boolean
polarities have such a representation, so gates can be switched without
counting the number of clauses produced by earlier switches. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace BooleanDecisionTree


@[simp] lemma negate_eval {n : ℕ} (T : BooleanDecisionTree n) (x : BooleanCube n) :
    T.negate.eval x = !(T.eval x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hx : x i <;> simp [negate, eval, hx, hl, hh]

@[simp] lemma negate_depth {n : ℕ} (T : BooleanDecisionTree n) : T.negate.depth = T.depth := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh => simp [negate, depth, hl, hh]

end BooleanDecisionTree


lemma CubeTerm.withLiteral_eval {n : ℕ} (C : CubeTerm n) (i : Fin n) (b : Bool)
    (hc : i ∉ C.support ∨ C.value i = b) (x : BooleanCube n) :
    (C.withLiteral i b).eval x = true ↔ x i = b ∧ C.eval x = true := by
  simp only [eval, decide_eq_true_eq]
  constructor
  · intro h
    have hi := h i (mem_insert_self _ _)
    have hx : x i = b := by simpa [withLiteral] using hi
    refine ⟨hx, ?_⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      exact hx.trans ((hc.resolve_left (not_not.mpr hj)).symm)
    · have hh := h j (mem_insert_of_mem hj)
      simpa [withLiteral, hji] using hh
  · rintro ⟨hi, h⟩ j hj
    rcases mem_insert.mp hj with rfl | hj
    · simpa [withLiteral] using hi
    · by_cases hji : j = i
      · subst j
        simpa [withLiteral] using hi
      · simpa [withLiteral, hji] using h j hj


lemma dnfEval_eq_true {n : ℕ} (F : List (CubeTerm n)) (x : BooleanCube n) :
    dnfEval F x = true ↔ ∃ C ∈ F, C.eval x = true := by
  simp [dnfEval]

lemma addDNFLiteral_eval {n : ℕ} (F : List (CubeTerm n)) (i : Fin n) (b : Bool)
    (x : BooleanCube n) :
    dnfEval (addDNFLiteral F i b) x = true ↔ x i = b ∧ dnfEval F x = true := by
  simp only [dnfEval_eq_true, addDNFLiteral, List.mem_flatMap]
  constructor
  · rintro ⟨D, ⟨C, hC, hD⟩, he⟩
    split_ifs at hD with hc
    · have hDC : D = C.withLiteral i b := by simpa using hD
      subst D
      have hh := (C.withLiteral_eval i b hc x).mp he
      exact ⟨hh.1, C, hC, hh.2⟩
    · simp at hD
  · rintro ⟨hxi, C, hC, he⟩
    have hc : i ∉ C.support ∨ C.value i = b := by
      by_cases hi : i ∈ C.support
      · right
        have hh := (of_decide_eq_true he) i hi
        exact hh.symm.trans hxi
      · exact Or.inl hi
    refine ⟨C.withLiteral i b, ⟨C, hC, ?_⟩, (C.withLiteral_eval i b hc x).mpr ⟨hxi, he⟩⟩
    simp [hc]

lemma addDNFLiteral_width {n r : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ r) (i : Fin n) (b : Bool) :
    ∀ C ∈ addDNFLiteral F i b, C.support.card ≤ r + 1 := by
  intro D hD
  obtain ⟨C, hC, hD⟩ := List.mem_flatMap.mp hD
  split_ifs at hD with hc
  · have hDC : D = C.withLiteral i b := by simpa using hD
    subst D
    exact (card_insert_le i C.support).trans (Nat.add_le_add_right (hF C hC) 1)
  · simp at hD

namespace BooleanDecisionTree


theorem toDNF_eval {n : ℕ} (T : BooleanDecisionTree n) (x : BooleanCube n) :
    dnfEval T.toDNF x = T.eval x := by
  apply Bool.eq_iff_iff.mpr
  induction T with
  | leaf b => cases b <;> simp [toDNF, dnfEval, eval, CubeTerm.eval]
  | query i low high hl hh =>
    simp only [toDNF, dnfEval, List.any_append, Bool.or_eq_true]
    change (dnfEval (addDNFLiteral low.toDNF i false) x = true ∨
      dnfEval (addDNFLiteral high.toDNF i true) x = true) ↔ _
    rw [addDNFLiteral_eval, addDNFLiteral_eval, hl, hh]
    cases hx : x i <;> simp [eval, hx]

theorem toDNF_width {n : ℕ} (T : BooleanDecisionTree n) :
    ∀ C ∈ T.toDNF, C.support.card ≤ T.depth := by
  induction T with
  | leaf b => cases b <;> simp [toDNF, depth]
  | query i low high hl hh =>
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact (addDNFLiteral_width low.toDNF hl i false C hC).trans
        (Nat.add_le_add_right (Nat.le_max_left _ _) 1)
    · exact (addDNFLiteral_width high.toDNF hh i true C hC).trans
        (Nat.add_le_add_right (Nat.le_max_right _ _) 1)

end BooleanDecisionTree

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDecisionRestriction
namespace OAI

/-! Decision-tree certificates are preserved by fixing additional coordinates.
We also package the two Boolean polarities of a certificate. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

namespace BooleanDecisionTree


@[simp] theorem restrict_eval {n : ℕ} (T : BooleanDecisionTree n)
    (ρ : PartialAssignment n) (x : BooleanCube n) :
    (T.restrict ρ).eval x = T.eval (ρ.apply x) := by
  induction T with
  | leaf b => rfl
  | query i low high hl hh =>
    cases hρ : ρ i with
    | none =>
      cases hx : x i <;> simp [restrict, eval, PartialAssignment.apply, hρ, hx, hl, hh]
    | some b =>
      cases b <;> simp [restrict, eval, PartialAssignment.apply, hρ, hl, hh]

theorem restrict_depth_le {n : ℕ} (T : BooleanDecisionTree n)
    (ρ : PartialAssignment n) : (T.restrict ρ).depth ≤ T.depth := by
  induction T with
  | leaf b => exact le_rfl
  | query i low high hl hh =>
    cases hρ : ρ i with
    | none => simpa [restrict, hρ, depth] using Nat.add_le_add_right (max_le_max hl hh) 1
    | some b =>
      cases b
      · simpa only [restrict, hρ, depth] using
          hl.trans ((Nat.le_max_left _ _).trans (Nat.le_succ _))
      · simpa only [restrict, hρ, depth] using
          hh.trans ((Nat.le_max_right _ _).trans (Nat.le_succ _))

end BooleanDecisionTree


theorem HasSmallDecisionTree.restrict {n r : ℕ} {f : BooleanCube n → Bool}
    (h : HasSmallDecisionTree f r) (ρ : PartialAssignment n) :
    HasSmallDecisionTree (fun x => f (ρ.apply x)) r := by
  obtain ⟨T, hT, he⟩ := h
  exact ⟨T.restrict ρ, (T.restrict_depth_le ρ).trans hT, fun x => by simp [he]⟩

theorem HasSmallDecisionTree.negate {n r : ℕ} {f : BooleanCube n → Bool}
    (h : HasSmallDecisionTree f r) : HasSmallDecisionTree (fun x => !(f x)) r := by
  obtain ⟨T, hT, he⟩ := h
  exact ⟨T.negate, by simpa using hT, fun x => by simp [he]⟩

@[simp] theorem hasSmallDecisionTree_negate_iff {n r : ℕ} {f : BooleanCube n → Bool} :
    HasSmallDecisionTree (fun x => !(f x)) r ↔ HasSmallDecisionTree f r := by
  constructor
  · intro h
    simpa only [Bool.not_not] using h.negate
  · exact HasSmallDecisionTree.negate

theorem literal_hasSmallDecisionTree {n r : ℕ} (i : Fin n) (b : Bool)
    (hr : 1 ≤ r) (ρ : PartialAssignment n) :
    HasSmallDecisionTree (fun x => (AC0Circuit.literal i b).eval (ρ.apply x)) r := by
  have h : HasSmallDecisionTree (AC0Circuit.literal i b).eval r := by
    refine ⟨.query i (.leaf (!b)) (.leaf b), ?_, ?_⟩
    · simpa [BooleanDecisionTree.depth] using hr
    · intro x
      cases b <;> cases hx : x i <;>
        simp [BooleanDecisionTree.eval, AC0Circuit.eval, hx]
  exact h.restrict ρ

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitQueryWalk
namespace OAI

/-! Complete query blocks along a canonical DNF path. A prefix of a path is
enough for the switching encoding; the final Boolean answer is irrelevant. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


namespace DNFQueryBlock




end DNFQueryBlock


namespace CanonicalDNFWalk

lemma support_subset_free {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs) :
    DNFQueryBlock.support bs ⊆ ρ.free := by
  induction h with
  | nil => simp [DNFQueryBlock.support]
  | skip _ _ ih => exact ih
  | @step C F ρ bs x _ _ _ ih =>
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · exact C.live_subset_free ρ hi
    · have hh := ih hi
      rw [PartialAssignment.free_assign] at hh
      exact (mem_sdiff.mp hh).1

lemma head_disjoint_tail {n : ℕ} {C : CubeTerm n} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)} (x : BooleanCube n)
    (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
    Disjoint (C.live ρ) (DNFQueryBlock.support bs) := by
  apply Finset.disjoint_left.mpr
  intro i hi htail
  have hh := h.support_subset_free htail
  rw [PartialAssignment.free_assign] at hh
  exact (mem_sdiff.mp hh).2 hi

lemma length_eq_card_support {n : ℕ} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (h : CanonicalDNFWalk F ρ bs) :
    DNFQueryBlock.length bs = (DNFQueryBlock.support bs).card := by
  induction h with
  | nil => simp [DNFQueryBlock.length, DNFQueryBlock.support]
  | skip _ _ ih => exact ih
  | @step C F ρ bs x _ _ h ih =>
    simp only [DNFQueryBlock.length, DNFQueryBlock.support]
    rw [card_union_of_disjoint (head_disjoint_tail x h), ih]

lemma length_le_dimension {n : ℕ} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (h : CanonicalDNFWalk F ρ bs) : DNFQueryBlock.length bs ≤ n := by
  rw [h.length_eq_card_support]
  exact (card_le_card (subset_univ _)).trans_eq (by simp)

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBlockCode
namespace OAI

/-! A query block is encoded by positions within its term, the path answers,
and one separator. Term indices are recovered from the modified restriction,
so the code alphabet is independent of the number of terms. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical


lemma CubeTerm.slot_le {n : ℕ} (C : CubeTerm n) (i : Fin n) :
    C.slot i ≤ C.support.card := by
  unfold slot
  split_ifs with hi
  · exact Nat.le_of_lt (Fin.isLt _)
  · exact le_rfl

lemma CubeTerm.slot_injective {n : ℕ} (C : CubeTerm n) {i j : Fin n}
    (hi : i ∈ C.support) (hj : j ∈ C.support) (h : C.slot i = C.slot j) : i = j := by
  have he : C.support.equivFin ⟨i, hi⟩ = C.support.equivFin ⟨j, hj⟩ := by
    apply Fin.ext
    simpa only [slot, dif_pos hi, dif_pos hj] using h
  exact congrArg Subtype.val (C.support.equivFin.injective he)

namespace DNFQueryBlock





lemma literalCode_injective {n : ℕ} (C : CubeTerm n) (S T : Finset (Fin n))
    (hS : S ⊆ C.support) (hT : T ⊆ C.support) (x y : BooleanCube n)
    (h : literalCode ⟨C, S, x⟩ = literalCode ⟨C, T, y⟩) :
    S = T ∧ ∀ i ∈ S, x i = y i := by
  have hmem (i : Fin n) (hi : i ∈ S) : i ∈ T ∧ x i = y i := by
    have hc : (C.slot i, x i) ∈ literalCode ⟨C, S, x⟩ := by
      apply List.mem_map.mpr
      exact ⟨i, (Finset.mem_sort _).mpr hi, rfl⟩
    rw [h] at hc
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hc
    have hjT : j ∈ T := (Finset.mem_sort _).mp hj
    have hji : j = i := C.slot_injective (hT hjT) (hS hi) (congrArg Prod.fst he)
    subst j
    exact ⟨hjT, (congrArg Prod.snd he).symm⟩
  refine ⟨?_, fun i hi => (hmem i hi).2⟩
  apply Finset.Subset.antisymm (fun i hi => (hmem i hi).1)
  intro i hi
  have hc : (C.slot i, y i) ∈ literalCode ⟨C, T, y⟩ := by
    apply List.mem_map.mpr
    exact ⟨i, (Finset.mem_sort _).mpr hi, rfl⟩
  rw [← h] at hc
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hc
  have hjS : j ∈ S := (Finset.mem_sort _).mp hj
  have hji : j = i := C.slot_injective (hS hjS) (hT hi) (congrArg Prod.fst he)
  exact hji ▸ hjS

end DNFQueryBlock

lemma separated_option_lists_injective {α : Type*} (xs ys : List α)
    (u v : List (Option α))
    (h : xs.map some ++ none :: u = ys.map some ++ none :: v) : xs = ys ∧ u = v := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact ⟨rfl, List.cons.inj h |>.2⟩
    | cons y ys => simp at h
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have hp := List.cons.inj h
      have hxy : x = y := Option.some.inj hp.1
      obtain ⟨hxs, huv⟩ := ih ys hp.2
      exact ⟨by rw [hxy, hxs], huv⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitFiniteCodes
namespace OAI

/-! The finite alphabet for query positions and responses. Allowing one
separator per block at most doubles the length of a query code. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical




lemma read_packRestrictionSymbol (w : ℕ) (z : Option (ℕ × Bool))
    (hz : ∀ a b, z = some (a, b) → a ≤ w) :
    (packRestrictionSymbol w z hz).map (fun v => (v.1.val, v.2)) = z := by
  cases z with
  | none => rfl
  | some z => cases z; rfl


lemma read_packRestrictionCode (w k : ℕ) (l : List (Option (ℕ × Bool)))
    (hl : l.length ≤ k)
    (hw : ∀ z ∈ l, ∀ a b, z = some (a, b) → a ≤ w) :
    readRestrictionCode (packRestrictionCode w k l hl hw) = l := by
  unfold readRestrictionCode packRestrictionCode
  simp only [read_packRestrictionSymbol]
  exact List.ofFn_get l

lemma boundedRestrictionCode_card (w k : ℕ) :
    Fintype.card (BoundedRestrictionCode w k) ≤ (k + 1) * (2 * w + 3) ^ k := by
  rw [Fintype.card_sigma]
  calc
    _ = ∑ l : Fin (k + 1), (2 * w + 3) ^ l.val := by
      apply sum_congr rfl
      intro l _
      simp [Nat.add_mul, Nat.mul_comm, Nat.add_assoc]
    _ ≤ ∑ _l : Fin (k + 1), (2 * w + 3) ^ k := by
      apply sum_le_sum
      intro l _
      exact Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ l.isLt)
    _ = _ := by simp

lemma two_mul_add_one_le_three_pow (h : ℕ) : 2 * h + 1 ≤ 3 ^ h := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    have hp : 1 ≤ 3 ^ h := Nat.one_le_pow h 3 (by omega)
    rw [pow_succ]
    omega

lemma boundedRestrictionCode_card_queries (w h : ℕ) :
    Fintype.card (BoundedRestrictionCode w (2 * h)) ≤
      (3 * (2 * w + 3) ^ 2) ^ h := by
  apply (boundedRestrictionCode_card w (2 * h)).trans
  calc
    (2 * h + 1) * (2 * w + 3) ^ (2 * h) ≤ 3 ^ h * (2 * w + 3) ^ (2 * h) :=
      Nat.mul_le_mul_right _ (two_mul_add_one_le_three_pow h)
    _ = _ := by rw [mul_pow, ← pow_mul]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionFourier
namespace OAI

/-! Orthogonality after fixing coordinates. Averaging over the fixed bits
removes all cross terms with different original Walsh supports. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

lemma restricted_walshCoefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (L T : Finset (Fin n)) (y : BooleanCube n) :
    walshCoefficient (fun x => f (restrictCube L y x)) T =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S ∩ L = T),
        walshCoefficient f S * walsh (S \ L) y := by
  have hf : (fun x => f (restrictCube L y x)) = fun x =>
      ∑ S : Finset (Fin n),
        (walshCoefficient f S * walsh (S \ L) y) * walsh (S ∩ L) x := by
    funext x
    rw [← walsh_inversion f (restrictCube L y x)]
    apply sum_congr rfl
    intro S _
    rw [walsh_restrictCube]
    ring
  rw [hf]
  change cubeAverage (fun x => (∑ S : Finset (Fin n),
      (walshCoefficient f S * walsh (S \ L) y) * walsh (S ∩ L) x) * walsh T x) = _
  simp only [sum_mul]
  rw [cubeAverage_sum, sum_filter]
  apply sum_congr rfl
  intro S _
  simp only [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  split_ifs <;> simp

lemma restriction_support_injective {n : ℕ} (L T S U : Finset (Fin n))
    (hS : S ∩ L = T) (hU : U ∩ L = T) (h : S \ L = U \ L) : S = U := by
  calc
    S = S \ L ∪ S ∩ L := (sdiff_union_inter S L).symm
    _ = U \ L ∪ U ∩ L := by rw [h, hS, hU]
    _ = U := sdiff_union_inter U L

theorem restricted_walshCoefficient_mean_sq {n : ℕ} (f : BooleanCube n → ℝ)
    (L T : Finset (Fin n)) :
    cubeAverage (fun y => (walshCoefficient (fun x => f (restrictCube L y x)) T) ^ 2) =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S ∩ L = T),
        (walshCoefficient f S) ^ 2 := by
  let I := (univ : Finset (Finset (Fin n))).filter (fun S => S ∩ L = T)
  have heq : (fun y => (walshCoefficient (fun x => f (restrictCube L y x)) T) ^ 2) =
      fun y => ∑ S ∈ I, ∑ U ∈ I,
        (walshCoefficient f S * walshCoefficient f U) *
          (walsh (S \ L) y * walsh (U \ L) y) := by
    funext y
    rw [restricted_walshCoefficient, pow_two, sum_mul]
    apply sum_congr rfl
    intro S _
    rw [mul_sum]
    apply sum_congr rfl
    intro U _
    ring
  rw [heq, cubeAverage_sum]
  apply sum_congr rfl
  intro S hS
  rw [cubeAverage_sum]
  simp_rw [cubeAverage_mul_const, cubeAverage_walsh_mul]
  rw [sum_eq_single S]
  · simp [pow_two]
  · intro U hU hUS
    have hd : S \ L ≠ U \ L := by
      intro hd
      apply hUS
      exact (restriction_support_injective L T S U
        (mem_filter.mp hS).2 (mem_filter.mp hU).2 hd).symm
    simp [hd]
  · exact fun h => (h hS).elim

theorem restricted_fourier_tail_mean {n : ℕ} (f : BooleanCube n → ℝ)
    (L : Finset (Fin n)) (t : ℕ) :
    cubeAverage (fun y => cubeAverage (fun x =>
      (f (restrictCube L y x) - walshTruncation (fun z => f (restrictCube L y z)) t x) ^ 2)) =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => t < (S ∩ L).card),
        (walshCoefficient f S) ^ 2 := by
  simp_rw [walshTruncation_error]
  rw [cubeAverage_sum]
  simp_rw [restricted_walshCoefficient_mean_sq, sum_filter]
  have hsum (T : Finset (Fin n)) :
      (if t < T.card then ∑ S : Finset (Fin n),
        if S ∩ L = T then (walshCoefficient f S) ^ 2 else 0 else 0) =
      ∑ S : Finset (Fin n), if t < T.card then
        (if S ∩ L = T then (walshCoefficient f S) ^ 2 else 0) else 0 := by
    by_cases h : t < T.card <;> simp [h]
  simp_rw [hsum]
  rw [sum_comm]
  apply sum_congr rfl
  intro S _
  rw [sum_eq_single (S ∩ L)]
  · simp
  · intro T _ hT
    by_cases ht : t < T.card <;> simp [ht, Ne.symm hT]
  · intro h
    exact (h (mem_univ _)).elim

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionLaw
namespace OAI

/-! The three-valued product law for independent random restrictions.
Fixing `s` previously free coordinates changes weight by an exact factor. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



theorem restrictionLaw_assign_weight {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (ρ : PartialAssignment n) (S : Finset (Fin n)) (hS : S ⊆ ρ.free)
    (x : BooleanCube n) :
    (restrictionLaw n p hp hp1.le).weight ρ =
      (2 * p / (1 - p)) ^ S.card *
        (restrictionLaw n p hp hp1.le).weight (ρ.assign S x) := by
  have hn : 1 - p ≠ 0 := by linarith
  have hpoint (i : Fin n) :
      (restrictionBitLaw p hp hp1.le).weight (ρ i) =
        (if i ∈ S then 2 * p / (1 - p) else 1) *
          (restrictionBitLaw p hp hp1.le).weight (ρ.assign S x i) := by
    by_cases hi : i ∈ S
    · have hρ := (mem_filter.mp (hS hi)).2
      simp only [restrictionBitLaw, PartialAssignment.assign, hi, hρ, ite_true]
      field_simp
    · simp [PartialAssignment.assign, hi]
  change (∏ i, (restrictionBitLaw p hp hp1.le).weight (ρ i)) = _
  simp_rw [hpoint]
  rw [prod_mul_distrib, Fintype.prod_ite_mem, prod_const]
  rfl

theorem FiniteLaw.probability_le_of_encoding {α β : Type*}
    [Fintype α] [Fintype β] (μ : FiniteLaw α) (E : α → Prop)
    (encode : α → α × β) (r : ℝ) (hr : 0 ≤ r)
    (hinj : ∀ x, E x → ∀ y, E y → encode x = encode y → x = y)
    (hweight : ∀ x, E x → μ.weight x ≤ r * μ.weight (encode x).1) :
    μ.probability E ≤ Fintype.card β * r := by
  calc
    μ.probability E = ∑ x ∈ (univ : Finset α).filter E, μ.weight x := by
      simp [FiniteLaw.probability, FiniteLaw.average, sum_filter, mul_ite]
    _ ≤ ∑ y : α × β, r * μ.weight y.1 := by
      apply sum_le_sum_of_injOn encode
      · intro x hx y hy h
        exact hinj x (mem_filter.mp hx).2 y (mem_filter.mp hy).2 h
      · exact fun _ _ => mem_univ _
      · exact fun x hx => hweight x (mem_filter.mp hx).2
      · exact fun y _ _ => mul_nonneg hr (μ.nonneg y.1)
    _ = Fintype.card β * r := by
      simp only [Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul]
      rw [← mul_sum, ← mul_sum, μ.total]
      ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionDistribution
namespace OAI

/-! The three-valued restriction law is exactly the experiment that first
chooses live bits and then independent uniform values for the fixed bits. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.independent_average_pair {n : ℕ} {α β : Type*}
    [Fintype α] [Fintype β] (μ : Fin n → FiniteLaw α) (ν : Fin n → FiniteLaw β)
    (f : (Fin n → α) → (Fin n → β) → ℝ) :
    (independent (fun i => (μ i).product (ν i))).average
      (fun z => f (fun i => (z i).1) (fun i => (z i).2)) =
      (independent μ).average (fun x => (independent ν).average (f x)) := by
  let e : (Fin n → α × β) ≃ ((Fin n → α) × (Fin n → β)) :=
    { toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      invFun := fun z i => (z.1 i, z.2 i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ z : (Fin n → α) × (Fin n → β),
        (independent (fun i => (μ i).product (ν i))).weight (fun i => (z.1 i, z.2 i)) *
          f z.1 z.2 := by
      exact (e.symm.sum_comp (fun z =>
        (independent (fun i => (μ i).product (ν i))).weight z *
          f (fun i => (z i).1) (fun i => (z i).2))).symm
    _ = _ := by
      simp only [average, independent, product, prod_mul_distrib, Fintype.sum_prod_type,
        mul_sum, mul_assoc]

lemma bernoulli_half_average {n : ℕ} (f : BooleanCube n → ℝ) :
    (bernoulliCubeLaw n (1 / 2) (by norm_num) (by norm_num)).average f = cubeAverage f := by
  have hw (x : BooleanCube n) :
      (bernoulliCubeLaw n (1 / 2) (by norm_num) (by norm_num)).weight x =
        (1 / 2 : ℝ) ^ n := by
    norm_num [bernoulliCubeLaw, FiniteLaw.independent, booleanLaw, one_div]
    simp only [one_div, inv_pow]
  simp only [FiniteLaw.average, hw, ← mul_sum]
  simp [cubeAverage, BooleanCube, div_eq_mul_inv, mul_comm]


lemma partialAssignmentOfMask_apply {n : ℕ} (mask y x : BooleanCube n) :
    (partialAssignmentOfMask mask y).apply x = restrictCube (sampledCoordinates mask) y x := by
  funext i
  cases hi : mask i <;> simp [partialAssignmentOfMask, PartialAssignment.apply,
    restrictCube, sampledCoordinates, hi]

lemma restriction_pair_atom (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (z : Option Bool) :
    ((booleanLaw p hp hp1).product (booleanLaw (1 / 2) (by norm_num) (by norm_num))).probability
      (fun b => (if b.1 then none else some b.2) = z) =
        (restrictionBitLaw p hp hp1).weight z := by
  cases z with
  | none => simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
      booleanLaw, restrictionBitLaw, Fintype.sum_prod_type]; ring
  | some b => cases b <;>
      simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
        booleanLaw, restrictionBitLaw, Fintype.sum_prod_type] <;> ring

theorem restrictionLaw_average {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : PartialAssignment n → ℝ) :
    (restrictionLaw n p hp hp1).average f =
      (bernoulliCubeLaw n p hp hp1).average (fun mask =>
        cubeAverage (fun y => f (partialAssignmentOfMask mask y))) := by
  have hm := FiniteLaw.independent_average_map
    (fun _ : Fin n => (booleanLaw p hp hp1).product
      (booleanLaw (1 / 2) (by norm_num) (by norm_num)))
    (fun _ : Fin n => restrictionBitLaw p hp hp1)
    (fun _ b => if b.1 then none else some b.2)
    (fun _ z => restriction_pair_atom p hp hp1 z) f
  unfold restrictionLaw
  rw [← hm]
  change (FiniteLaw.independent (fun _ : Fin n => (booleanLaw p hp hp1).product
    (booleanLaw (1 / 2) (by norm_num) (by norm_num)))).average
      (fun z => f (partialAssignmentOfMask (fun i => (z i).1) (fun i => (z i).2))) = _
  refine (FiniteLaw.independent_average_pair (fun _ : Fin n => booleanLaw p hp hp1)
    (fun _ : Fin n => booleanLaw (1 / 2) (by norm_num) (by norm_num))
    (fun mask y => f (partialAssignmentOfMask mask y))).trans ?_
  apply congrArg (bernoulliCubeLaw n p hp hp1).average
  funext mask
  exact bernoulli_half_average _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionComposition
namespace OAI

/-! Applying two independent restrictions multiplies their live-coordinate
parameters. This is the distribution identity used for depth reduction. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical



lemma composeRestriction_apply {n : ℕ} (ρ τ : PartialAssignment n) (x : BooleanCube n) :
    (composeRestriction ρ τ).apply x = ρ.apply (τ.apply x) := by
  funext i
  cases hρ : ρ i <;> simp [composeRestriction, composeRestrictionBit, PartialAssignment.apply, hρ]

lemma restriction_compose_atom (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : Option Bool) :
    ((restrictionBitLaw p hp hp1).product (restrictionBitLaw q hq hq1)).probability
      (fun b => composeRestrictionBit b.1 b.2 = z) =
      (restrictionBitLaw (p * q) (mul_nonneg hp hq) (by nlinarith)).weight z := by
  cases z with
  | none =>
    simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
      restrictionBitLaw, Fintype.sum_prod_type, Fintype.sum_option, composeRestrictionBit]
  | some b =>
    cases b <;>
      simp [FiniteLaw.probability, FiniteLaw.average, FiniteLaw.product,
        restrictionBitLaw, Fintype.sum_prod_type, Fintype.sum_option, composeRestrictionBit] <;>
      ring

theorem restrictionLaw_compose {n : ℕ} (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (f : PartialAssignment n → ℝ) :
    (restrictionLaw n p hp hp1).average (fun ρ =>
      (restrictionLaw n q hq hq1).average (fun τ => f (composeRestriction ρ τ))) =
        (restrictionLaw n (p * q) (mul_nonneg hp hq) (by nlinarith)).average f := by
  have hm := FiniteLaw.independent_average_map
    (fun _ : Fin n => (restrictionBitLaw p hp hp1).product (restrictionBitLaw q hq hq1))
    (fun _ : Fin n => restrictionBitLaw (p * q) (mul_nonneg hp hq) (by nlinarith))
    (fun _ b => composeRestrictionBit b.1 b.2)
    (fun _ z => restriction_compose_atom p q hp hp1 hq hq1 z) f
  have hpair := FiniteLaw.independent_average_pair
    (fun _ : Fin n => restrictionBitLaw p hp hp1)
    (fun _ : Fin n => restrictionBitLaw q hq hq1)
    (fun ρ τ => f (composeRestriction ρ τ))
  exact hpair.symm.trans hm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitTreeWalk
namespace OAI

/-! A longest branch of the concrete canonical tree supplies a query walk
with at least that many queried variables. -/

namespace TwoPointCorrelations

open _root_.Finset hiding sum_le_sum_of_injOn
open scoped _root_.Classical

namespace BooleanDecisionTree

lemma queryVariables_depth_state {n : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n) (ρ : PartialAssignment n) :
    ∃ τ : PartialAssignment n,
      (queryVariables is k ρ).depth = is.length + (k τ).depth ∧
      (∀ j ∉ is.toFinset, τ j = ρ j) ∧
      (∀ j ∈ is.toFinset, ∃ b, τ j = some b) := by
  induction is generalizing ρ with
  | nil => exact ⟨ρ, by simp [queryVariables], fun _ _ => rfl, by simp⟩
  | cons i is ih =>
    obtain ⟨b, hb⟩ : ∃ b : Bool,
        max (queryVariables is k (Function.update ρ i (some false))).depth
            (queryVariables is k (Function.update ρ i (some true))).depth =
          (queryVariables is k (Function.update ρ i (some b))).depth := by
      by_cases h : (queryVariables is k (Function.update ρ i (some false))).depth ≤
          (queryVariables is k (Function.update ρ i (some true))).depth
      · exact ⟨true, max_eq_right h⟩
      · exact ⟨false, max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))⟩
    obtain ⟨τ, ht, hout, hin⟩ := ih (Function.update ρ i (some b))
    refine ⟨τ, ?_, ?_, ?_⟩
    · simp only [queryVariables, depth, hb, ht, List.length_cons]
      omega
    · intro j hj
      have hj' : j ∉ is.toFinset := fun h => hj (by simp [h])
      have hji : j ≠ i := fun h => hj (by simp [h])
      rw [hout j hj']
      simp [hji]
    · intro j hj
      by_cases hj' : j ∈ is.toFinset
      · exact hin j hj'
      · have hji : j = i := by simpa [hj'] using hj
        subst j
        exact ⟨b, by simpa using hout i hj'⟩

lemma queryVariables_depth_witness {n : ℕ} (is : List (Fin n))
    (k : PartialAssignment n → BooleanDecisionTree n) (ρ : PartialAssignment n) :
    ∃ x : BooleanCube n, (queryVariables is k ρ).depth =
      is.length + (k (ρ.assign is.toFinset x)).depth := by
  obtain ⟨τ, ht, hout, hin⟩ := queryVariables_depth_state is k ρ
  let x : BooleanCube n := fun i => (τ i).getD false
  have he : τ = ρ.assign is.toFinset x := by
    funext i
    by_cases hi : i ∈ is.toFinset
    · obtain ⟨b, hb⟩ := hin i hi
      simp [PartialAssignment.assign, hi, x, hb]
    · simp [PartialAssignment.assign, hi, hout i hi]
  exact ⟨x, by simpa only [he] using ht⟩

end BooleanDecisionTree

lemma CubeTerm.satisfied_of_live_empty {n : ℕ} (C : CubeTerm n)
    (ρ : PartialAssignment n) (hC : C.Compatible ρ) (h : C.live ρ = ∅) :
    C.Satisfied ρ := by
  intro i hi
  rcases hC i hi with hn | hv
  · have hm : i ∈ C.live ρ := mem_filter.mpr ⟨hi, hn⟩
    rw [h] at hm
    exact False.elim (notMem_empty i hm)
  · exact hv

theorem canonicalDNFTree_depth_walk {n : ℕ} (F : List (CubeTerm n))
    (ρ : PartialAssignment n) : ∃ bs : List (DNFQueryBlock n),
      CanonicalDNFWalk F ρ bs ∧ (canonicalDNFTree F ρ).depth ≤ DNFQueryBlock.length bs := by
  induction F generalizing ρ with
  | nil => exact ⟨[], .nil _ _, le_refl _⟩
  | cons C F ih =>
    by_cases hC : C.Compatible ρ
    · by_cases he : C.live ρ = ∅
      · refine ⟨[], .nil _ _, ?_⟩
        have hs := C.satisfied_of_live_empty ρ hC he
        simp [canonicalDNFTree, hC, he, BooleanDecisionTree.queryVariables, hs,
          BooleanDecisionTree.depth, DNFQueryBlock.length]
      · have hne := Finset.nonempty_iff_ne_empty.mpr he
        let k := fun τ => if C.Satisfied τ then BooleanDecisionTree.leaf true
          else canonicalDNFTree F τ
        obtain ⟨x, hx⟩ := BooleanDecisionTree.queryVariables_depth_witness
          ((C.live ρ).sort (· ≤ ·)) k ρ
        simp only [Finset.sort_toFinset, Finset.length_sort] at hx
        have hdepth : (canonicalDNFTree (C :: F) ρ).depth =
            (C.live ρ).card + (k (ρ.assign (C.live ρ) x)).depth := by
          simpa only [canonicalDNFTree, hC, ite_true] using hx
        by_cases hs : C.Satisfied (ρ.assign (C.live ρ) x)
        · refine ⟨[⟨C, C.live ρ, x⟩], .step x hC hne (.nil _ _), ?_⟩
          simp [hdepth, k, hs, BooleanDecisionTree.depth, DNFQueryBlock.length]
        · obtain ⟨bs, hbs, hb⟩ := ih (ρ.assign (C.live ρ) x)
          refine ⟨⟨C, C.live ρ, x⟩ :: bs, .step x hC hne hbs, ?_⟩
          simpa only [hdepth, k, hs, ite_false, DNFQueryBlock.length] using
            Nat.add_le_add_left hb (C.live ρ).card
    · obtain ⟨bs, hbs, hb⟩ := ih ρ
      refine ⟨bs, .skip hC hbs, ?_⟩
      simpa only [canonicalDNFTree, hC, ite_false] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitWalkImage
namespace OAI

/-! The switching encoding changes each queried block to the values that
satisfy its term. Query blocks are disjoint, so their responses can later be
restored without disturbing the remaining encoding. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace DNFQueryBlock

lemma image_eq_outside {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n))
    (i : Fin n) (hi : i ∉ support bs) : image ρ bs i = ρ i := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons b bs ih =>
    have hb : i ∉ b.queried := fun hb => hi (mem_union_left _ hb)
    have ht : i ∉ support bs := fun ht => hi (mem_union_right _ ht)
    rw [image, ih _ ht]
    simp [PartialAssignment.assign, hb]

lemma image_extends {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n))
    (h : support bs ⊆ ρ.free) : ρ.Extends (image ρ bs) := by
  intro i b hb
  have hi : i ∉ support bs := by
    intro hi
    have hn := (mem_filter.mp (h hi)).2
    rw [hb] at hn
    cases hn
  rw [image_eq_outside ρ bs i hi, hb]

lemma image_free {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n)) :
    (image ρ bs).free = ρ.free \ support bs := by
  induction bs generalizing ρ with
  | nil => simp [image, support]
  | cons b bs ih =>
    rw [image, ih, PartialAssignment.free_assign, support]
    ext i
    simp only [mem_sdiff, mem_union]
    tauto

lemma image_assign_comm {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n))
    (S : Finset (Fin n)) (hS : Disjoint S (support bs)) (x : BooleanCube n) :
    image (ρ.assign S x) bs = (image ρ bs).assign S x := by
  induction bs generalizing ρ with
  | nil => rfl
  | cons b bs ih =>
    have hh := disjoint_union_right.mp hS
    rw [image, PartialAssignment.assign_comm ρ S b.queried hh.1, ih _ hh.2]
    rfl

lemma image_eq_assign {n : ℕ} (ρ : PartialAssignment n) (bs : List (DNFQueryBlock n)) :
    image ρ bs = ρ.assign (support bs) (fun i => (image ρ bs i).getD false) := by
  funext i
  by_cases hi : i ∈ support bs
  · have hn : image ρ bs i ≠ none := by
      intro hn
      have hf : i ∈ (image ρ bs).free := mem_filter.mpr ⟨mem_univ _, hn⟩
      rw [image_free] at hf
      exact (mem_sdiff.mp hf).2 hi
    cases hb : image ρ bs i with
    | none => exact False.elim (hn hb)
    | some b => simp [PartialAssignment.assign, hi, hb]
  · simp [PartialAssignment.assign, hi, image_eq_outside ρ bs i hi]

lemma image_compatible {n : ℕ} (C : CubeTerm n) (ρ : PartialAssignment n)
    (bs : List (DNFQueryBlock n)) (hS : Disjoint C.support (support bs))
    (hC : C.Compatible ρ) : C.Compatible (image ρ bs) := by
  intro i hi
  have hn : i ∉ support bs := fun hs => Finset.disjoint_left.mp hS hi hs
  rw [image_eq_outside ρ bs i hn]
  exact hC i hi

end DNFQueryBlock

namespace CanonicalDNFWalk

lemma image_extends {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs) :
    ρ.Extends (DNFQueryBlock.image ρ bs) :=
  DNFQueryBlock.image_extends ρ bs h.support_subset_free

lemma step_image_compatible {n : ℕ} {C : CubeTerm n} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (x : BooleanCube n) (hC : C.Compatible ρ)
    (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
    C.Compatible (DNFQueryBlock.image ρ (⟨C, C.live ρ, x⟩ :: bs)) := by
  have hd : Disjoint C.support (DNFQueryBlock.support bs) := by
    apply Finset.disjoint_left.mpr
    intro i hi ht
    exact Finset.disjoint_left.mp (C.live_update_disjoint ρ x) hi
      (h.support_subset_free ht)
  apply DNFQueryBlock.image_compatible C _ bs hd
  intro i hi
  exact Or.inr (C.satisfied_assign_value ρ hC i hi)

lemma step_image_restore {n : ℕ} {C : CubeTerm n} {F : List (CubeTerm n)}
    {ρ : PartialAssignment n} {bs : List (DNFQueryBlock n)}
    (x : BooleanCube n) (h : CanonicalDNFWalk F (ρ.assign (C.live ρ) x) bs) :
    (DNFQueryBlock.image ρ (⟨C, C.live ρ, x⟩ :: bs)).assign (C.live ρ) x =
      DNFQueryBlock.image (ρ.assign (C.live ρ) x) bs := by
  change (DNFQueryBlock.image (ρ.assign (C.live ρ) C.value) bs).assign (C.live ρ) x = _
  rw [← DNFQueryBlock.image_assign_comm _ bs _ (head_disjoint_tail x h)]
  congr 1
  funext i
  by_cases hi : i ∈ C.live ρ <;> simp [PartialAssignment.assign, hi]

theorem image_weight {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    (restrictionLaw n p hp hp1.le).weight ρ =
      (2 * p / (1 - p)) ^ DNFQueryBlock.length bs *
        (restrictionLaw n p hp hp1.le).weight (DNFQueryBlock.image ρ bs) := by
  have hw := restrictionLaw_assign_weight p hp hp1 ρ (DNFQueryBlock.support bs)
    h.support_subset_free (fun i => (DNFQueryBlock.image ρ bs i).getD false)
  rw [← DNFQueryBlock.image_eq_assign, ← h.length_eq_card_support] at hw
  exact hw

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitWalkCode
namespace OAI

/-! Injectivity of the switching encoding. Earlier incompatible terms stay
incompatible, while the first queried term becomes compatible in the image.
The first block and its responses can therefore be decoded and removed. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace DNFQueryBlock

lemma codes_cons {n : ℕ} (b : DNFQueryBlock n) (bs : List (DNFQueryBlock n)) :
    codes (b :: bs) = b.literalCode.map some ++ none :: codes bs := by
  simp [codes, code, List.append_assoc]

lemma codes_eq_nil_iff {n : ℕ} (bs : List (DNFQueryBlock n)) : codes bs = [] ↔ bs = [] := by
  cases bs with
  | nil => simp [codes]
  | cons b bs => simp [codes_cons]

end DNFQueryBlock

namespace CanonicalDNFWalk

lemma codes_length_le {n : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs) :
    (DNFQueryBlock.codes bs).length ≤ 2 * DNFQueryBlock.length bs := by
  induction h with
  | nil => simp [DNFQueryBlock.codes, DNFQueryBlock.length]
  | skip _ _ ih => exact ih
  | @step C F ρ bs x _ hne _ ih =>
    have hc : 1 ≤ (C.live ρ).card := card_pos.mpr hne
    simp only [DNFQueryBlock.codes_cons, List.length_append, List.length_map,
      List.length_cons, DNFQueryBlock.literalCode, Finset.length_sort,
      DNFQueryBlock.length]
    omega

lemma code_positions_le {n w : ℕ} {F : List (CubeTerm n)} {ρ : PartialAssignment n}
    {bs : List (DNFQueryBlock n)} (h : CanonicalDNFWalk F ρ bs)
    (hF : ∀ C ∈ F, C.support.card ≤ w) :
    ∀ z ∈ DNFQueryBlock.codes bs, ∀ a b, z = some (a, b) → a ≤ w := by
  induction h with
  | nil => simp [DNFQueryBlock.codes]
  | @skip C F ρ bs _ _ ih =>
    exact ih (fun D hD => hF D (List.mem_cons_of_mem C hD))
  | @step C F ρ bs x _ _ _ ih =>
    intro z hz a b hza
    rw [DNFQueryBlock.codes_cons] at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨q, hq, hqz⟩ := List.mem_map.mp hz
      obtain ⟨i, hi, hiq⟩ := List.mem_map.mp hq
      have hp : (C.slot i, x i) = (a, b) := Option.some.inj
        ((congrArg some hiq).trans (hqz.trans hza))
      have hslot : C.slot i = a := congrArg Prod.fst hp
      rw [← hslot]
      exact (C.slot_le i).trans (hF C (by simp))
    · rcases List.mem_cons.mp hz with hz | hz
      · rw [hz] at hza
        cases hza
      · exact ih (fun D hD => hF D (List.mem_cons_of_mem C hD)) z hz a b hza

theorem image_code_injective {n : ℕ} {F : List (CubeTerm n)}
    {ρ τ : PartialAssignment n} {bs cs : List (DNFQueryBlock n)}
    (hρ : CanonicalDNFWalk F ρ bs) (hτ : CanonicalDNFWalk F τ cs)
    (hi : DNFQueryBlock.image ρ bs = DNFQueryBlock.image τ cs)
    (hc : DNFQueryBlock.codes bs = DNFQueryBlock.codes cs) : ρ = τ := by
  induction F generalizing ρ τ bs cs with
  | nil =>
    cases hρ
    cases hτ
    exact hi
  | cons C F ih =>
    by_cases hb : bs = []
    · subst bs
      have hc' : cs = [] := (DNFQueryBlock.codes_eq_nil_iff cs).mp hc.symm
      subst cs
      exact hi
    by_cases hd : cs = []
    · subst cs
      have hb' : bs = [] := (DNFQueryBlock.codes_eq_nil_iff bs).mp hc
      exact False.elim (hb hb')
    cases hρ with
    | nil => exact False.elim (hb rfl)
    | skip hC hρ =>
      cases hτ with
      | nil => exact False.elim (hd rfl)
      | skip hD hτ => exact ih hρ hτ hi hc
      | step y hD hne hτ =>
        have hbad := C.incompatible_mono hC hρ.image_extends
        apply False.elim
        apply hbad
        rw [hi]
        exact step_image_compatible y hD hτ
    | @step _ _ _ bs x hC hne hρ =>
      cases hτ with
      | nil => exact False.elim (hd rfl)
      | skip hD hτ =>
        have hbad := C.incompatible_mono hD hτ.image_extends
        apply False.elim
        apply hbad
        rw [← hi]
        exact step_image_compatible x hC hρ
      | @step _ _ _ cs y hD hne' hτ =>
        rw [DNFQueryBlock.codes_cons, DNFQueryBlock.codes_cons] at hc
        obtain ⟨hlit, hrest⟩ := separated_option_lists_injective _ _ _ _ hc
        obtain ⟨hS, hxy⟩ := DNFQueryBlock.literalCode_injective C (C.live ρ) (C.live τ)
          (filter_subset _ _) (filter_subset _ _) x y hlit
        have hr := congrArg (fun σ : PartialAssignment n => σ.assign (C.live ρ) x) hi
        rw [step_image_restore x hρ] at hr
        have hright :
            (DNFQueryBlock.image τ (⟨C, C.live τ, y⟩ :: cs)).assign (C.live ρ) x =
              DNFQueryBlock.image (τ.assign (C.live τ) y) cs := by
          rw [PartialAssignment.assign_congr_on _ _ x y hxy, hS]
          exact step_image_restore y hτ
        rw [hright] at hr
        have hnext := ih hρ hτ hr hrest
        apply PartialAssignment.assign_injective_of_free ρ τ (C.live ρ)
          (C.live_subset_free ρ) (by rw [hS]; exact C.live_subset_free τ) x y
        simpa only [hS] using hnext

end CanonicalDNFWalk

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitSwitchingMass
namespace OAI

/-! The weighted injection bounds the probability of canonical query walks
of any specified length. The bound depends on term width and query count,
and is independent of the number of terms. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem canonicalWalk_probability {n w h : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ w)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) :
    (restrictionLaw n p hp hp1.le).probability
        (fun ρ => ∃ bs, CanonicalDNFWalk F ρ bs ∧ DNFQueryBlock.length bs = h) ≤
      ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) ^ h * (2 * p / (1 - p)) ^ h := by
  let E := fun ρ : PartialAssignment n =>
    ∃ bs, CanonicalDNFWalk F ρ bs ∧ DNFQueryBlock.length bs = h
  let pick (ρ : PartialAssignment n) (he : E ρ) := Classical.choose he
  have hpick (ρ : PartialAssignment n) (he : E ρ) :
      CanonicalDNFWalk F ρ (pick ρ he) ∧ DNFQueryBlock.length (pick ρ he) = h :=
    Classical.choose_spec he
  let code (ρ : PartialAssignment n) (he : E ρ) : BoundedRestrictionCode w (2 * h) :=
    packRestrictionCode w (2 * h) (DNFQueryBlock.codes (pick ρ he))
      (by rw [← (hpick ρ he).2]; exact (hpick ρ he).1.codes_length_le)
      ((hpick ρ he).1.code_positions_le hF)
  let empty : BoundedRestrictionCode w (2 * h) :=
    ⟨⟨0, Nat.succ_pos _⟩, Fin.elim0⟩
  let encode (ρ : PartialAssignment n) : PartialAssignment n × BoundedRestrictionCode w (2 * h) :=
    if he : E ρ then (DNFQueryBlock.image ρ (pick ρ he), code ρ he) else (ρ, empty)
  have hinj : ∀ ρ, E ρ → ∀ τ, E τ → encode ρ = encode τ → ρ = τ := by
    intro ρ hρ τ hτ heq
    have heq' : (DNFQueryBlock.image ρ (pick ρ hρ), code ρ hρ) =
        (DNFQueryBlock.image τ (pick τ hτ), code τ hτ) := by
      simpa only [encode, dif_pos hρ, dif_pos hτ] using heq
    have hc := congrArg (fun z : PartialAssignment n × BoundedRestrictionCode w (2 * h) =>
      readRestrictionCode z.2) heq'
    simp only [code, read_packRestrictionCode] at hc
    exact (hpick ρ hρ).1.image_code_injective (hpick τ hτ).1 (congrArg Prod.fst heq') hc
  have hr : 0 ≤ (2 * p / (1 - p)) ^ h := by positivity
  have hw : ∀ ρ, E ρ → (restrictionLaw n p hp hp1.le).weight ρ ≤
      (2 * p / (1 - p)) ^ h * (restrictionLaw n p hp hp1.le).weight (encode ρ).1 := by
    intro ρ he
    have heq := (hpick ρ he).1.image_weight p hp hp1
    rw [(hpick ρ he).2] at heq
    simpa only [encode, dif_pos he] using heq.le
  have hprob := (restrictionLaw n p hp hp1.le).probability_le_of_encoding E encode
    ((2 * p / (1 - p)) ^ h) hr hinj hw
  apply hprob.trans
  apply mul_le_mul_of_nonneg_right _ hr
  exact_mod_cast boundedRestrictionCode_card_queries w h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitSwitchingLemma
namespace OAI

/-! A switching estimate sufficient for the fixed-depth application. The
position/separator encoding gives a quadratic dependence on term width;
this still yields polylogarithmic degree for every fixed circuit depth. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma finite_geometric_tail (n s : ℕ) (q : ℝ) (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (∑ i : Fin (n + 1), if s ≤ i.val then q ^ i.val else 0) ≤ 2 * q ^ s := by
  let I := (univ : Finset (Fin (n + 1))).filter (fun i => s ≤ i.val)
  have hs : (∑ i : Fin (n + 1), if s ≤ i.val then q ^ i.val else 0) =
      ∑ i ∈ I, q ^ i.val := (sum_filter _ _).symm
  rw [hs]
  calc
    _ ≤ ∑ j ∈ range (n + 1), q ^ s * (1 / 2 : ℝ) ^ j := by
      apply sum_le_sum_of_injOn (fun i : Fin (n + 1) => i.val - s)
      · intro i hi j hj hij
        apply Fin.ext
        have his := (mem_filter.mp hi).2
        have hjs := (mem_filter.mp hj).2
        change i.val - s = j.val - s at hij
        omega
      · intro _ hj
        obtain ⟨i, _, rfl⟩ := mem_image.mp hj
        exact mem_range.mpr (Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)
      · intro i hi
        have his := (mem_filter.mp hi).2
        calc
          q ^ i.val = q ^ s * q ^ (i.val - s) := by rw [← pow_add, Nat.add_sub_of_le his]
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqhalf _) (pow_nonneg hq _)
      · intro j _ _
        positivity
    _ = q ^ s * ∑ j ∈ range (n + 1), (1 / 2 : ℝ) ^ j := by rw [mul_sum]
    _ ≤ q ^ s * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (pow_nonneg hq _)
    _ = _ := mul_comm _ _

theorem canonicalDNFTree_switching {n w : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ w)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (s : ℕ) :
    (restrictionLaw n p hp hp1.le).probability
      (fun ρ => s ≤ (canonicalDNFTree F ρ).depth) ≤
      2 * (((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ s := by
  let μ := restrictionLaw n p hp hp1.le
  let q := ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))
  let E := fun i : Fin (n + 1) => fun ρ : PartialAssignment n =>
    s ≤ i.val ∧ ∃ bs, CanonicalDNFWalk F ρ bs ∧ DNFQueryBlock.length bs = i.val
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hcover : μ.probability (fun ρ => s ≤ (canonicalDNFTree F ρ).depth) ≤
      μ.probability (fun ρ => ∃ i : Fin (n + 1), E i ρ) := by
    apply μ.probability_mono
    intro ρ hρ
    obtain ⟨bs, hb, hdepth⟩ := canonicalDNFTree_depth_walk F ρ
    let i : Fin (n + 1) := ⟨DNFQueryBlock.length bs, Nat.lt_succ_of_le hb.length_le_dimension⟩
    exact ⟨i, hρ.trans hdepth, bs, hb, rfl⟩
  have heach (i : Fin (n + 1)) : μ.probability (E i) ≤
      if s ≤ i.val then q ^ i.val else 0 := by
    by_cases his : s ≤ i.val
    · rw [if_pos his]
      apply (μ.probability_mono (fun ρ hρ => hρ.2)).trans
      have hb := canonicalWalk_probability F hF p hp hp1 (h := i.val)
      simpa only [q, mul_pow] using hb
    · rw [if_neg his]
      have he : μ.probability (E i) = 0 := by
        unfold FiniteLaw.probability
        calc
          _ = μ.average (fun _ => 0) := by
            apply congrArg μ.average
            funext ρ
            simp [E, his]
          _ = 0 := μ.average_const 0
      exact he.le
  exact hcover.trans ((μ.probability_exists_le E).trans
    ((sum_le_sum (fun i _ => heach i)).trans (finite_geometric_tail n s q hq0 hq)))

theorem dnf_restriction_has_shallow_tree {n w : ℕ} (F : List (CubeTerm n))
    (hF : ∀ C ∈ F, C.support.card ≤ w)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (t : ℕ) :
    (restrictionLaw n p hp hp1.le).probability
      (fun ρ => ¬ ∃ T : BooleanDecisionTree n, T.depth ≤ t ∧
        ∀ x, T.eval x = dnfEval F (ρ.apply x)) ≤
      2 * (((3 * (2 * w + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (t + 1) := by
  apply (FiniteLaw.probability_mono _ ?_).trans
    (canonicalDNFTree_switching F hF p hp hp1 hq (t + 1))
  intro ρ hρ
  have hn : ¬ (canonicalDNFTree F ρ).depth ≤ t := by
    intro ht
    exact hρ ⟨canonicalDNFTree F ρ, ht, canonicalDNFTree_eval F ρ⟩
  omega

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitGateSwitching
namespace OAI

/-! Switching a gate whose inputs already have shallow decision trees.
The number of clauses is irrelevant to the switching estimate. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


theorem decisionTreeDisjunction_eval {n k : ℕ} (T : Fin k → BooleanDecisionTree n)
    (x : BooleanCube n) :
    dnfEval (decisionTreeDisjunction T) x = decide (∃ i, (T i).eval x = true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [dnfEval_eq_true, decisionTreeDisjunction, List.mem_flatMap,
    Finset.mem_toList, mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨C, ⟨i, hC⟩, he⟩
    exact ⟨i, (T i).toDNF_eval x ▸ (dnfEval_eq_true _ _).mpr ⟨C, hC, he⟩⟩
  · rintro ⟨i, hi⟩
    have hh : dnfEval (T i).toDNF x = true := by rwa [(T i).toDNF_eval]
    obtain ⟨C, hC, he⟩ := (dnfEval_eq_true _ _).mp hh
    exact ⟨C, ⟨i, hC⟩, he⟩

theorem decisionTreeDisjunction_width {n k r : ℕ} (T : Fin k → BooleanDecisionTree n)
    (hT : ∀ i, (T i).depth ≤ r) :
    ∀ C ∈ decisionTreeDisjunction T, C.support.card ≤ r := by
  intro C hC
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hC
  exact ((T i).toDNF_width C hi).trans (hT i)

theorem disjunction_restriction_switching {n k r : ℕ} (f : Fin k → BooleanCube n → Bool)
    (hf : ∀ i, HasSmallDecisionTree (f i) r)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2) :
    (restrictionLaw n p hp hp1.le).probability (fun ρ =>
      ¬ HasSmallDecisionTree (fun x => decide (∃ i, f i (ρ.apply x) = true)) r) ≤
      2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1) := by
  choose T hT he using hf
  have hF := decisionTreeDisjunction_width T hT
  have hh := dnf_restriction_has_shallow_tree (decisionTreeDisjunction T) hF p hp hp1 hq r
  apply (FiniteLaw.probability_mono _ ?_).trans hh
  intro ρ hρ hgood
  apply hρ
  obtain ⟨S, hS, hs⟩ := hgood
  refine ⟨S, hS, ?_⟩
  intro x
  rw [hs, decisionTreeDisjunction_eval]
  simp only [he]

theorem conjunction_restriction_switching {n k r : ℕ} (f : Fin k → BooleanCube n → Bool)
    (hf : ∀ i, HasSmallDecisionTree (f i) r)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2) :
    (restrictionLaw n p hp hp1.le).probability (fun ρ =>
      ¬ HasSmallDecisionTree (fun x => decide (∀ i, f i (ρ.apply x) = true)) r) ≤
      2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1) := by
  have hh := disjunction_restriction_switching (fun i x => Bool.not (f i x))
    (fun i => (hf i).negate) p hp hp1 hq
  apply (FiniteLaw.probability_mono _ ?_).trans hh
  intro ρ hρ hgood
  apply hρ
  have heq : (fun x => Bool.not (decide (∃ i, Bool.not (f i (ρ.apply x)) = true))) =
      (fun x => decide (∀ i, f i (ρ.apply x) = true)) := by
    funext x
    by_cases hall : ∀ i, f i (ρ.apply x) = true
    · simp [hall]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hn : ∃ i, Bool.not (f i (ρ.apply x)) = true := by
        refine ⟨i, ?_⟩
        cases h : f i (ρ.apply x) <;> simp_all
      simp only [hn, decide_true, Bool.not_true, hall, decide_false]
  have hneg := hgood.negate
  exact Eq.mp (congrArg (fun f => HasSmallDecisionTree f r) heq) hneg

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDepthSwitching
namespace OAI

/-! Iterate switching through arbitrary AND/OR circuits. Each gate pays
one switching error, so the total loss is bounded by circuit size. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem FiniteLaw.average_probability_le_union {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (E : α → β → Prop)
    (bad : ι → α → Prop) (δ : ℝ) (hδ : 0 ≤ δ)
    (hgood : ∀ x, (∀ i, ¬ bad i x) → ν.probability (E x) ≤ δ) :
    μ.average (fun x => ν.probability (E x)) ≤
      (∑ i, μ.probability (bad i)) + δ := by
  calc
    _ ≤ μ.average (fun x => (if ∃ i, bad i x then 1 else 0) + δ) := by
      apply μ.average_mono
      intro x
      by_cases hx : ∃ i, bad i x
      · simpa only [if_pos hx] using
          (ν.probability_le_one (E x)).trans (by linarith)
      · simpa only [if_neg hx, zero_add] using
          hgood x (fun i hi => hx ⟨i, hi⟩)
    _ = μ.probability (fun x => ∃ i, bad i x) + δ := by
      simp only [FiniteLaw.probability, FiniteLaw.average, mul_add,
        sum_add_distrib, ← sum_mul, μ.total, one_mul]
      congr 1
      apply sum_congr rfl
      intro x _
      by_cases hx : ∃ i, bad i x <;> simp [hx]
    _ ≤ _ := add_le_add (μ.probability_exists_le bad) le_rfl

namespace AC0Circuit

theorem restriction_shallow {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1)
    (r : ℕ) (hr : 1 ≤ r)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (d : ℕ) (c : AC0Circuit n) (hc : c.depth ≤ d) :
    (restrictionLaw n (p ^ d) (pow_nonneg hp _) (pow_le_one₀ hp hp1.le)).probability
      (fun ρ => ¬ HasSmallDecisionTree (fun x => c.eval (ρ.apply x)) r) ≤
      (c.size : ℝ) *
        (2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1)) := by
  let δ := 2 * (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  induction d generalizing c with
  | zero =>
    cases c with
    | literal i b =>
      have he (ρ : PartialAssignment n) :
          ¬ (¬ HasSmallDecisionTree (fun x => (literal i b).eval (ρ.apply x)) r) :=
        not_not.mpr (literal_hasSmallDecisionTree i b hr ρ)
      simpa only [FiniteLaw.probability, he, ite_false, FiniteLaw.average_const,
        size, Nat.cast_one, one_mul] using hδ
    | andGate children => simp [depth] at hc
    | orGate children => simp [depth] at hc
  | succ d ih =>
    let μ := restrictionLaw n (p ^ d) (pow_nonneg hp _) (pow_le_one₀ hp hp1.le)
    let ν := restrictionLaw n p hp hp1.le
    have hcompose (E : PartialAssignment n → Prop) :
        (restrictionLaw n (p ^ (d + 1)) (pow_nonneg hp _)
          (pow_le_one₀ hp hp1.le)).probability E =
        μ.average (fun ρ => ν.probability (fun τ => E (composeRestriction ρ τ))) := by
      unfold FiniteLaw.probability
      exact (restrictionLaw_compose (p ^ d) p (pow_nonneg hp _)
        (pow_le_one₀ hp hp1.le) hp hp1.le (fun ρ => if E ρ then 1 else 0)).symm
    cases c with
    | literal i b =>
      have he (ρ : PartialAssignment n) :
          ¬ (¬ HasSmallDecisionTree (fun x => (literal i b).eval (ρ.apply x)) r) :=
        not_not.mpr (literal_hasSmallDecisionTree i b hr ρ)
      simpa only [FiniteLaw.probability, he, ite_false, FiniteLaw.average_const,
        size, Nat.cast_one, one_mul] using hδ
    | andGate children =>
      have hchild (i) : (children i).depth ≤ d := by
        have hi := Finset.le_sup (f := fun i => (children i).depth) (mem_univ i)
        simp only [depth] at hc
        omega
      rw [hcompose]
      apply (FiniteLaw.average_probability_le_union μ ν _
        (fun i ρ => ¬ HasSmallDecisionTree (fun x => (children i).eval (ρ.apply x)) r)
        δ hδ ?_).trans
      · calc
          _ ≤ (∑ i, ((children i).size : ℝ) * δ) + δ := by
            exact add_le_add (sum_le_sum (fun i _ => ih (children i) (hchild i))) le_rfl
          _ = _ := by simp only [size, Nat.cast_add, Nat.cast_one, Nat.cast_sum]; rw [← sum_mul]; ring
      · intro ρ hρ
        have hh := conjunction_restriction_switching
          (fun i x => (children i).eval (ρ.apply x)) (fun i => not_not.mp (hρ i))
          p hp hp1 hq
        simpa only [eval, composeRestriction_apply] using hh
    | orGate children =>
      have hchild (i) : (children i).depth ≤ d := by
        have hi := Finset.le_sup (f := fun i => (children i).depth) (mem_univ i)
        simp only [depth] at hc
        omega
      rw [hcompose]
      apply (FiniteLaw.average_probability_le_union μ ν _
        (fun i ρ => ¬ HasSmallDecisionTree (fun x => (children i).eval (ρ.apply x)) r)
        δ hδ ?_).trans
      · calc
          _ ≤ (∑ i, ((children i).size : ℝ) * δ) + δ := by
            exact add_le_add (sum_le_sum (fun i _ => ih (children i) (hchild i))) le_rfl
          _ = _ := by simp only [size, Nat.cast_add, Nat.cast_one, Nat.cast_sum]; rw [← sum_mul]; ring
      · intro ρ hρ
        have hh := disjunction_restriction_switching
          (fun i x => (children i).eval (ρ.apply x)) (fun i => not_not.mp (hρ i))
          p hp hp1 hq
        simpa only [eval, composeRestriction_apply] using hh


end AC0Circuit

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PrimeRowSecondMoment
namespace OAI

/-! Finite second moments for the positive row majorant used to delete
rare sites. Independence is used only under the auxiliary product law. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace FiniteLaw

lemma average_add {α : Type*} [Fintype α] (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.average (fun x => f x + g x) = μ.average f + μ.average g := by
  simp only [average, mul_add, sum_add_distrib]

lemma independent_average_coordinate_mul {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] (μ : ι → FiniteLaw α) (i j : ι) (hij : i ≠ j) (f g : α → ℝ) :
    (independent μ).average (fun x => f (x i) * g (x j)) =
      (μ i).average f * (μ j).average g := by
  let F : ι → α → ℝ := fun k a =>
    (if k = i then f a else 1) * (if k = j then g a else 1)
  have he (x : ι → α) : (∏ k, F k (x k)) = f (x i) * g (x j) := by
    simp only [F, prod_mul_distrib]
    simp
  have hm (k : ι) : (μ k).average (F k) =
      (if k = i then (μ i).average f else 1) *
        (if k = j then (μ j).average g else 1) := by
    by_cases hki : k = i
    · subst k
      simp [F, hij]
    · by_cases hkj : k = j
      · subst k
        simp [F, hki]
      · simp [F, hki, hkj]
  calc
    _ = (independent μ).average (fun x => ∏ k, F k (x k)) := by simp only [he]
    _ = ∏ k, (μ k).average (F k) := independent_average_product μ F
    _ = _ := by simp only [hm, prod_mul_distrib]; simp

end FiniteLaw

lemma booleanLaw_indicator_average (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (booleanLaw q hq0 hq1).average (fun b => if b then (1 : ℝ) else 0) = q := by
  simp [booleanLaw, FiniteLaw.average]

lemma independent_boolean_count_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      booleanCount = ∑ i, q i := by
  rw [show booleanCount = (fun a : ι → Bool => ∑ i, if a i then (1 : ℝ) else 0) from rfl,
    FiniteLaw.average_sum]
  apply sum_congr rfl
  intro i _
  rw [FiniteLaw.independent_average_coordinate
    (fun k => booleanLaw (q k) (hq0 k) (hq1 k)) i
    (fun b => if b then (1 : ℝ) else 0), booleanLaw_indicator_average]

lemma independent_boolean_count_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun a => (booleanCount a) ^ 2) ≤ (∑ i, q i) ^ 2 + ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  have hp (i j : ι) : μ.average (fun a =>
      (if a i then (1 : ℝ) else 0) * (if a j then 1 else 0)) ≤
        q i * q j + if i = j then q i else 0 := by
    by_cases hij : i = j
    · subst j
      have he (a : ι → Bool) :
          (if a i then (1 : ℝ) else 0) * (if a i then 1 else 0) =
            if a i then 1 else 0 := by cases a i <;> norm_num
      simp only [he, ite_true]
      rw [FiniteLaw.independent_average_coordinate
        (fun k => booleanLaw (q k) (hq0 k) (hq1 k)) i
        (fun b => if b then (1 : ℝ) else 0), booleanLaw_indicator_average]
      nlinarith [sq_nonneg (q i)]
    · simp only [hij, ite_false, add_zero]
      exact le_of_eq ((FiniteLaw.independent_average_coordinate_mul
        (fun i => booleanLaw (q i) (hq0 i) (hq1 i)) i j hij
        (fun b => if b then (1 : ℝ) else 0) (fun b => if b then (1 : ℝ) else 0)).trans
          (by rw [booleanLaw_indicator_average, booleanLaw_indicator_average]))
  have he (a : ι → Bool) : (booleanCount a) ^ 2 =
      ∑ i, ∑ j, (if a i then (1 : ℝ) else 0) * (if a j then 1 else 0) := by
    simp only [booleanCount, pow_two, sum_mul, mul_sum]
    rw [sum_comm]
  change μ.average (fun a => (booleanCount a) ^ 2) ≤ (∑ i, q i) ^ 2 + ∑ i, q i
  simp_rw [he, μ.average_sum]
  calc
    _ ≤ ∑ i, ∑ j, (q i * q j + if i = j then q i else 0) :=
      sum_le_sum (fun i _ => sum_le_sum (fun j _ => hp i j))
    _ = _ := by
      simp only [sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true, ← sum_mul]
      ring



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionProbability
namespace OAI

/-! A finite second-moment lower-tail bound for the live coordinates of a
random restriction. It is used to transfer high-degree Fourier mass. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.probability_mul_le_average {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) (f : α → ℝ) (a : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hE : ∀ x, E x → a ≤ f x) :
    a * μ.probability E ≤ μ.average f := by
  calc
    _ = μ.average (fun x => if E x then a else 0) := by
      unfold FiniteLaw.probability FiniteLaw.average
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      by_cases hx : E x <;> simp [hx]
      ring
    _ ≤ _ := μ.average_mono (fun x => by by_cases hx : E x <;> simp [hx, hf x, hE x])

lemma independent_boolean_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).average
      (fun b => (booleanCount b - ∑ i, q i) ^ 2) ≤ ∑ i, q i := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  let V := ∑ i, q i
  have hm : μ.average booleanCount = V := independent_boolean_count_average q hq0 hq1
  have hs : μ.average (fun b => (booleanCount b) ^ 2) ≤ V ^ 2 + V :=
    independent_boolean_count_square q hq0 hq1
  have he (b : ι → Bool) : (booleanCount b - V) ^ 2 =
      (booleanCount b) ^ 2 + booleanCount b * (-2 * V) + V ^ 2 := by ring
  change μ.average (fun b => (booleanCount b - V) ^ 2) ≤ V
  simp_rw [he]
  rw [μ.average_add, μ.average_add, μ.average_mul_const, μ.average_const, hm]
  nlinarith

theorem independent_boolean_lower_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (a : ℝ) (ha : 2 * a ≤ ∑ i, q i) (hlarge : 8 ≤ ∑ i, q i) :
    (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => booleanCount b ≤ a) ≤ 1 / 2 := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  let V := ∑ i, q i
  have hV : 0 < V := by dsimp [V]; linarith
  have hp : ∀ b : ι → Bool, booleanCount b ≤ a →
      2 * V ≤ (booleanCount b - V) ^ 2 := by
    intro b hb
    have h1 : 0 ≤ V / 2 - booleanCount b := by dsimp [V]; linarith
    have h2 : 0 ≤ 3 * V / 2 - booleanCount b := by dsimp [V]; linarith
    have hh := mul_nonneg h1 h2
    have hv := mul_nonneg hV.le (show 0 ≤ V - 8 by dsimp [V]; linarith)
    nlinarith
  have hm := μ.probability_mul_le_average (fun b => booleanCount b ≤ a)
    (fun b => (booleanCount b - V) ^ 2) (2 * V) (fun _ => sq_nonneg _) hp
  have hv := independent_boolean_variance q hq0 hq1
  change μ.average (fun b => (booleanCount b - V) ^ 2) ≤ V at hv
  apply (mul_le_mul_iff_right₀ (show 0 < 2 * V by positivity)).mp
  calc
    2 * V * μ.probability (fun b => booleanCount b ≤ a) ≤ V := hm.trans hv
    _ = 2 * V * (1 / 2) := by ring

theorem independent_boolean_survival {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1)
    (a : ℝ) (ha : 2 * a ≤ ∑ i, q i) (hlarge : 8 ≤ ∑ i, q i) :
    1 / 2 ≤ (FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))).probability
      (fun b => a < booleanCount b) := by
  let μ := FiniteLaw.independent (fun i => booleanLaw (q i) (hq0 i) (hq1 i))
  have h := independent_boolean_lower_tail q hq0 hq1 a ha hlarge
  have hc : μ.probability (fun b => a < booleanCount b) =
      1 - μ.probability (fun b => booleanCount b ≤ a) := by
    simpa only [not_le] using μ.probability_complement (fun b => booleanCount b ≤ a)
  rw [hc]
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionSurvival
namespace OAI

/-! A Fourier support with sufficiently many expected live coordinates
retains more than `t` coordinates with probability at least one half. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma booleanCount_restrict {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    booleanCount (fun i : S => x i) = ((S ∩ sampledCoordinates x).card : ℝ) := by
  unfold booleanCount
  rw [sum_coe_sort S (fun i => if x i then (1 : ℝ) else 0)]
  have hset : S ∩ sampledCoordinates x = S.filter (fun i => x i = true) := by
    ext i
    simp [sampledCoordinates]
  rw [hset]
  exact sum_boole (fun i => x i = true) S

theorem bernoulli_support_survival {n : ℕ} (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) (t : ℕ)
    (ht : 2 * (t : ℝ) ≤ p * S.card) (hlarge : 8 ≤ p * S.card) :
    1 / 2 ≤ (bernoulliCubeLaw n p hp hp1).probability
      (fun x => t < (S ∩ sampledCoordinates x).card) := by
  have h := independent_boolean_survival (fun _ : S => p) (fun _ => hp) (fun _ => hp1)
    (t : ℝ) (by simpa [mul_comm] using ht) (by simpa [mul_comm] using hlarge)
  have heq : (bernoulliCubeLaw n p hp hp1).probability
      (fun x => t < (S ∩ sampledCoordinates x).card) =
      (FiniteLaw.independent (fun _ : S => booleanLaw p hp hp1)).probability
        (fun x => (t : ℝ) < booleanCount x) := by
    unfold FiniteLaw.probability
    refine Eq.trans ?_ (FiniteLaw.independent_average_restrict
      (fun _ : Fin n => booleanLaw p hp hp1) S
      (fun x => if (t : ℝ) < booleanCount x then (1 : ℝ) else 0))
    apply congrArg (bernoulliCubeLaw n p hp hp1).average
    funext x
    simp only [booleanCount_restrict, Nat.cast_lt]
    by_cases hx : t < (S ∩ sampledCoordinates x).card <;> simp [hx]
  rw [heq]
  exact h

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRandomRestriction
namespace OAI

/-! Transfer from low-degree approximation after a random restriction to
the Fourier tail of the original function. All probability spaces are finite. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

theorem restriction_fourier_average {n : ℕ} (f : BooleanCube n → ℝ)
    (μ : FiniteLaw (BooleanCube n)) (t : ℕ) :
    μ.average (fun mask => cubeAverage (fun y => cubeAverage (fun x =>
      (f (restrictCube (sampledCoordinates mask) y x) -
        walshTruncation (fun z => f (restrictCube (sampledCoordinates mask) y z)) t x) ^ 2))) =
      ∑ S : Finset (Fin n), (walshCoefficient f S) ^ 2 *
        μ.probability (fun mask => t < (S ∩ sampledCoordinates mask).card) := by
  simp_rw [restricted_fourier_tail_mean, sum_filter]
  rw [μ.average_sum]
  apply sum_congr rfl
  intro S _
  have heq : (fun mask : BooleanCube n =>
      if t < (S ∩ sampledCoordinates mask).card then (walshCoefficient f S) ^ 2 else 0) =
      fun mask => (if t < (S ∩ sampledCoordinates mask).card then (1 : ℝ) else 0) *
        (walshCoefficient f S) ^ 2 := by
    funext mask
    split_ifs <;> simp
  rw [heq, μ.average_mul_const]
  rw [mul_comm]
  congr 1
  unfold FiniteLaw.probability
  apply congrArg μ.average
  funext mask
  by_cases h : t < (S ∩ sampledCoordinates mask).card <;> simp [h]

theorem fourier_tail_le_random_restriction {n : ℕ} (f : BooleanCube n → ℝ)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t d : ℕ)
    (ht : 2 * (t : ℝ) ≤ p * (d + 1)) (hd : 8 ≤ p * (d + 1)) :
    cubeAverage (fun x => (f x - walshTruncation f d x) ^ 2) ≤
      2 * (bernoulliCubeLaw n p hp hp1).average (fun mask =>
        cubeAverage (fun y => cubeAverage (fun x =>
          (f (restrictCube (sampledCoordinates mask) y x) -
            walshTruncation (fun z => f (restrictCube (sampledCoordinates mask) y z)) t x) ^ 2))) := by
  rw [walshTruncation_error, restriction_fourier_average, sum_filter, mul_sum]
  apply sum_le_sum
  intro S _
  by_cases hS : d < S.card
  · rw [if_pos hS]
    have hcard : (d : ℝ) + 1 ≤ S.card := by exact_mod_cast hS
    have hmul := mul_le_mul_of_nonneg_left hcard hp
    have hsurv := bernoulli_support_survival p hp hp1 S t (ht.trans hmul) (hd.trans hmul)
    have h := mul_le_mul_of_nonneg_left hsurv (sq_nonneg (walshCoefficient f S))
    nlinarith
  · rw [if_neg hS]
    exact mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _)
      ((bernoulliCubeLaw n p hp hp1).probability_nonneg _))

lemma walshTruncation_error_le_square {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    cubeAverage (fun x => (f x - walshTruncation f t x) ^ 2) ≤
      cubeAverage (fun x => (f x) ^ 2) := by
  rw [walshTruncation_error, walsh_parseval]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun S _ _ => sq_nonneg (walshCoefficient f S))

lemma walshTruncation_error_eq_zero {n t : ℕ} {f : BooleanCube n → ℝ}
    (hf : WalshDegreeLE f t) :
    cubeAverage (fun x => (f x - walshTruncation f t x) ^ 2) = 0 := by
  rw [walshTruncation_error]
  apply sum_eq_zero
  intro S hS
  rw [hf.high_coefficient_zero S (mem_filter.mp hS).2]
  simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRestrictionDecay
namespace OAI

/-! The spectral consequence of simplifying a Boolean function under random
restrictions: only restrictions whose decision trees remain deep contribute. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma restricted_error_le_degree_failure {n t : ℕ} (f : BooleanCube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1) (L : Finset (Fin n)) (y : BooleanCube n) :
    cubeAverage (fun x => (f (restrictCube L y x) -
      walshTruncation (fun z => f (restrictCube L y z)) t x) ^ 2) ≤
      if WalshDegreeLE (fun x => f (restrictCube L y x)) t then (0 : ℝ) else 1 := by
  split_ifs with h
  · rw [walshTruncation_error_eq_zero h]
  · apply (walshTruncation_error_le_square _ _).trans
    calc
      cubeAverage (fun x => (f (restrictCube L y x)) ^ 2) ≤
          cubeAverage (fun _ : BooleanCube n => (1 : ℝ)) := by
        apply cubeAverage_mono
        intro x
        rcases hf (restrictCube L y x) with hx | hx <;> simp [hx]
      _ = 1 := cubeAverage_const 1

theorem fourier_tail_le_degree_failure {n : ℕ} (f : BooleanCube n → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t d : ℕ)
    (ht : 2 * (t : ℝ) ≤ p * (d + 1)) (hd : 8 ≤ p * (d + 1)) :
    cubeAverage (fun x => (f x - walshTruncation f d x) ^ 2) ≤
      2 * (bernoulliCubeLaw n p hp hp1).average (fun mask => cubeAverage (fun y =>
        if WalshDegreeLE (fun x => f (restrictCube (sampledCoordinates mask) y x)) t
          then (0 : ℝ) else 1)) := by
  apply (fourier_tail_le_random_restriction f p hp hp1 t d ht hd).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply FiniteLaw.average_mono
  intro mask
  apply cubeAverage_mono
  intro y
  exact restricted_error_le_degree_failure f hf _ y


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierSwitching
namespace OAI

/-! Quantitative Fourier concentration obtained from the proved switching
estimate. All parameters remain explicit for the fixed-depth application. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

theorem fourier_tail_le_small_tree_failure {n : ℕ} (f : BooleanCube n → Bool)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (r D : ℕ)
    (hr : 2 * (r : ℝ) ≤ p * (D + 1)) (hD : 8 ≤ p * (D + 1)) :
    cubeAverage (fun x => ((if f x then (1 : ℝ) else 0) -
      walshTruncation (fun y => if f y then 1 else 0) D x) ^ 2) ≤
      2 * (restrictionLaw n p hp hp1).probability
        (fun ρ => ¬ HasSmallDecisionTree (fun x => f (ρ.apply x)) r) := by
  have hf (x) : (if f x then (1 : ℝ) else 0) = 0 ∨
      (if f x then (1 : ℝ) else 0) = 1 := by cases f x <;> simp
  apply (fourier_tail_le_degree_failure _ hf p hp hp1 r D hr hD).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [FiniteLaw.probability, restrictionLaw_average]
  apply FiniteLaw.average_mono
  intro mask
  apply cubeAverage_mono
  intro y
  by_cases h : HasSmallDecisionTree
      (fun x => f ((partialAssignmentOfMask mask y).apply x)) r
  · obtain ⟨T, hT, he⟩ := h
    have hd : WalshDegreeLE
        (fun x => if f (restrictCube (sampledCoordinates mask) y x) then (1 : ℝ) else 0) r := by
      have hi : (fun x => if f (restrictCube (sampledCoordinates mask) y x)
          then (1 : ℝ) else 0) = T.indicator := by
        funext x
        simp only [BooleanDecisionTree.indicator, he, partialAssignmentOfMask_apply]
      rw [hi]
      exact T.indicator_degree.mono hT
    simp only [hd, ite_true]
    split_ifs <;> norm_num
  · simp only [h, not_false_eq_true, ite_true]
    split_ifs <;> norm_num

theorem AC0Circuit.fourier_tail_switching {n : ℕ} (c : AC0Circuit n)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (r : ℕ) (hr : 1 ≤ r)
    (hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2)
    (d D : ℕ) (hc : c.depth ≤ d)
    (hDr : 2 * (r : ℝ) ≤ p ^ d * (D + 1)) (hD : 8 ≤ p ^ d * (D + 1)) :
    cubeAverage (fun x => (c.indicator x - walshTruncation c.indicator D x) ^ 2) ≤
      4 * (c.size : ℝ) *
        (((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p))) ^ (r + 1) := by
  have hf := fourier_tail_le_small_tree_failure c.eval (p ^ d) (pow_nonneg hp _)
    (pow_le_one₀ hp hp1.le) r D hDr hD
  apply hf.trans
  have hh := c.restriction_shallow p hp hp1 r hr hq d hc
  have hmul := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 2 by norm_num)
  convert (preTransparency := .instances) hmul using 1
  ring

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitFourierDegree
namespace OAI

/-! A polynomial degree bound and exponential Fourier error, with no
analytic parameter hypotheses left over from the switching argument. -/

namespace TwoPointCorrelations

open scoped _root_.Classical



lemma switchingDenominator_pos (r : ℕ) : 0 < switchingDenominator r := by
  unfold switchingDenominator
  positivity

theorem AC0Circuit.fourier_tail_polynomial_degree {n : ℕ} (c : AC0Circuit n)
    (d r : ℕ) (hc : c.depth ≤ d) (hr : 1 ≤ r) :
    cubeAverage (fun x => (c.indicator x -
      walshTruncation c.indicator (switchingDegree d r) x) ^ 2) ≤
      4 * (c.size : ℝ) * (1 / 2 : ℝ) ^ (r + 1) := by
  let R : ℝ := switchingDenominator r
  let p : ℝ := 1 / R
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast switchingDenominator_pos r
  have hR2 : 2 ≤ R := by
    dsimp [R, switchingDenominator]
    push_cast
    nlinarith [sq_nonneg (2 * (r : ℝ) + 2), show (0 : ℝ) ≤ r from Nat.cast_nonneg r]
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hphalf : p ≤ 1 / 2 := by
    dsimp [p]
    exact (div_le_div_iff₀ hR (by norm_num)).mpr (by linarith)
  have hp1 : p < 1 := lt_of_le_of_lt hphalf (by norm_num)
  have hRp : R * p = 1 := by dsimp [p]; field_simp
  have hA : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * 8 = R := by
    dsimp [R, switchingDenominator]
    push_cast
    ring
  have hq : ((3 * (2 * r + 3) ^ 2 : ℕ) : ℝ) * (2 * p / (1 - p)) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 1 - p by linarith)).mpr
    rw [← hA] at hRp
    nlinarith [hRp]
  have hmain : p ^ d * (switchingDegree d r : ℝ) = 8 * (r + 1 : ℝ) := by
    dsimp [switchingDegree, p, R]
    push_cast
    field_simp [ne_of_gt (show (0 : ℝ) < switchingDenominator r from hR)]
    rw [← mul_pow]
    simp [ne_of_gt (show (0 : ℝ) < switchingDenominator r from hR)]
  have hprod : 8 * (r + 1 : ℝ) ≤ p ^ d * ((switchingDegree d r : ℝ) + 1) := by
    calc
      _ = p ^ d * (switchingDegree d r : ℝ) := hmain.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hp _)
  have hh := c.fourier_tail_switching p hp hp1 r hr hq d (switchingDegree d r) hc
    (by nlinarith [show (0 : ℝ) ≤ r by positivity]) (by linarith)
  apply hh.trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _)
    (by positivity)

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.AC0Circuit.fourier_tail_polynomial_degree := @OAI.TwoPointCorrelations.AC0Circuit.fourier_tail_polynomial_degree
