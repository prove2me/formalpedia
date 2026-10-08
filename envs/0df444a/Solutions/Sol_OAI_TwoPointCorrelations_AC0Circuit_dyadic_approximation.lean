-- Prove2me | solution 1 for OAI.TwoPointCorrelations.AC0Circuit.dyadic_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:22:22.706695+00:00
-- url     : https://prove2.me/submissions/59d7414d-a299-49a6-aeda-2a520c3dc13d

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


lemma average_comm (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.average (fun x => ν.average (f x)) = ν.average (fun y => μ.average (fun x => f x y)) := by
  simp only [average, mul_sum]
  rw [sum_comm]
  congr 1
  funext y
  apply sum_congr rfl
  intro x _
  ring







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

open _root_.Finset


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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitComparison
namespace OAI

/-!
# Bounded-independence circuit comparison after Fourier correction

The comparison uses the fixed-depth specialization of Mark Braverman,
*Polylogarithmic independence fools AC⁰ circuits*, J. ACM 57 (2010), Article 28,
Corollary 2 in the author's version. We use depth 22, with absolute constants
and natural logarithms. Circuits below have actual finite syntax: literals
and arbitrary finite-fan-in AND/OR gates. They are tree circuits, a subclass
of the circuits covered by Braverman's theorem. The size counts both input
occurrences and gates; the depth counts AND/OR levels.
-/

namespace TwoPointCorrelations

open _root_.Finset


namespace AC0Circuit




lemma size_pos {n : ℕ} (c : AC0Circuit n) : 0 < c.size := by
  cases c <;> simp [size]



end AC0Circuit





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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialAlgebra
namespace OAI

/-! Algebra of the low-degree functions used in the circuit approximation.
Multiplication adds degrees, including after Boolean multilinearization. -/

namespace TwoPointCorrelations

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBernoulli
namespace OAI

/-! The finite sampling calculation in the circuit approximation: a random
subset hits a prescribed nonempty set exactly once with probability
`k*p*(1-p)^(k-1)`. No asymptotic input is used. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma bernoulliCubeLaw_pattern (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) (z : BooleanCube n) :
    (bernoulliCubeLaw n p hp hp1).average (cubePattern S z) =
      ∏ i ∈ S, (if z i then p else 1 - p) := by
  let F := fun i : Fin n => fun b : Bool =>
    if i ∈ S then (if b = z i then (1 : ℝ) else 0) else 1
  have heq (x : BooleanCube n) : cubePattern S z x = ∏ i, F i (x i) := by
    dsimp only [F]
    rw [Fintype.prod_ite_mem, prod_boole]
    unfold cubePattern
    split_ifs <;> rfl
  have hlocal (i : Fin n) : (booleanLaw p hp hp1).average (F i) =
      if i ∈ S then (if z i then p else 1 - p) else 1 := by
    by_cases hi : i ∈ S
    · cases hz : z i <;> simp [FiniteLaw.average, booleanLaw, F, hi, hz]
    · simp [F, hi]
  have hfun : cubePattern S z = fun x => ∏ i, F i (x i) := funext heq
  rw [hfun]
  change (FiniteLaw.independent (fun _ : Fin n => booleanLaw p hp hp1)).average
    (fun x => ∏ i, F i (x i)) = _
  rw [FiniteLaw.independent_average_product]
  simp_rw [hlocal]
  exact Fintype.prod_ite_mem S _



lemma bernoulliCubeLaw_singleHitScore (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) :
    (bernoulliCubeLaw n p hp hp1).average (singleHitScore S) =
      (S.card : ℝ) * p * (1 - p) ^ (S.card - 1) := by
  have hterm (i : Fin n) (hi : i ∈ S) :
      (bernoulliCubeLaw n p hp hp1).average (cubePattern S (singleBitPattern i)) =
        p * (1 - p) ^ (S.card - 1) := by
    rw [bernoulliCubeLaw_pattern, ← prod_erase_mul _ _ hi]
    have hprod : (∏ j ∈ S.erase i, if singleBitPattern i j then p else 1 - p) =
        (1 - p) ^ (S.card - 1) := by
      have heq : (∏ j ∈ S.erase i, if singleBitPattern i j then p else 1 - p) =
          ∏ _j ∈ S.erase i, (1 - p) := by
        apply prod_congr rfl
        intro j hj
        simp [singleBitPattern, (mem_erase.mp hj).1]
      rw [heq, prod_const, card_erase_of_mem hi]
    rw [hprod]
    simp [singleBitPattern, mul_comm]
  have heq : (bernoulliCubeLaw n p hp hp1).average (singleHitScore S) =
      ∑ i ∈ S, (bernoulliCubeLaw n p hp hp1).average (cubePattern S (singleBitPattern i)) := by
    unfold singleHitScore FiniteLaw.average
    simp only [mul_sum]
    rw [sum_comm]
  rw [heq, sum_congr rfl (fun i hi => hterm i hi)]
  simp [mul_assoc]

/-- A dyadic sampling scale with expected hit count between 1/4 and 1/2
has a uniformly positive chance of isolating one marked coordinate. -/
lemma single_hit_probability_lower (k : ℕ) (hk : 0 < k) (p : ℝ)
    (hp : 0 ≤ p) (hsmall : (k : ℝ) * p ≤ 1 / 2)
    (hlarge : 1 / 4 ≤ (k : ℝ) * p) :
    1 / 8 ≤ (k : ℝ) * p * (1 - p) ^ (k - 1) := by
  have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpone : p ≤ 1 := by nlinarith
  have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ -p by linarith) (k - 1)
  have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk, Nat.cast_one]
  have hpow : (1 / 2 : ℝ) ≤ (1 - p) ^ (k - 1) := by
    rw [hkcast] at hbern
    have heq : 1 + -p = 1 - p := by ring
    rw [heq] at hbern
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg k) hp)
  nlinarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicSampling
namespace OAI

/-! Only logarithmically many Bernoulli parameters are needed to isolate a
zero among the inputs of an AND gate. The success constant 1/8 is sufficient
for the application's unspecified absolute circuit constants. -/

namespace TwoPointCorrelations

lemma exists_dyadic_single_hit (k z : ℕ) (hz : 0 < z) (hzk : z ≤ k) :
    ∃ a : ℕ, a ≤ Nat.log 2 k + 2 ∧
      1 / 8 ≤ (z : ℝ) * (1 / (2 : ℝ) ^ a) *
        (1 - 1 / (2 : ℝ) ^ a) ^ (z - 1) := by
  let l := Nat.log 2 z
  have hlog := Nat.log_mono_right (b := 2) hzk
  refine ⟨l + 2, by dsimp only [l]; omega, ?_⟩
  have hlow : (2 : ℝ) ^ l ≤ z := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt hz)
  have hhigh : (z : ℝ) < (2 : ℝ) ^ (l + 1) := by
    exact_mod_cast (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2)
      (Nat.ne_of_gt hz)).mp (Nat.lt_succ_self l)
  have hpow : (2 : ℝ) ^ (l + 2) = 4 * (2 : ℝ) ^ l := by
    rw [pow_add]
    norm_num
    ring
  have hpow' : (2 : ℝ) ^ (l + 2) = 2 * (2 : ℝ) ^ (l + 1) := by
    rw [show l + 2 = (l + 1) + 1 by omega, pow_add]
    ring
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (l + 2) := by positivity
  apply single_hit_probability_lower z hz _ (by positivity)
  · rw [mul_one_div, div_le_iff₀ hpos, hpow']
    linarith
  · rw [mul_one_div, le_div_iff₀ hpos, hpow]
    linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitProbabilisticMethod
namespace OAI

/-! The averaging step that chooses one polynomial approximation from a
finite random construction, for an arbitrary input distribution. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma FiniteLaw.exists_average_le {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (f : α → ℝ) {a : ℝ} (ha : μ.average f ≤ a) :
    ∃ x, f x ≤ a := by
  by_contra hn
  have hf : ∀ x, a < f x := by simpa only [not_exists, not_le] using hn
  have hpos : ∃ x, 0 < μ.weight x := by
    have ht : 0 < ∑ x, μ.weight x := by rw [μ.total]; norm_num
    simpa only [sum_pos_iff_of_nonneg (fun x _ => μ.nonneg x), mem_univ, true_and] using ht
  obtain ⟨x, hx⟩ := hpos
  have hlt : (∑ y, μ.weight y * a) < ∑ y, μ.weight y * f y := by
    apply sum_lt_sum
    · intro y _
      exact mul_le_mul_of_nonneg_left (hf y).le (μ.nonneg y)
    · exact ⟨x, mem_univ _, mul_lt_mul_of_pos_left (hf x) hx⟩
  change μ.average (fun _ => a) < μ.average f at hlt
  rw [μ.average_const] at hlt
  exact (not_lt_of_ge ha) hlt

/-- If every fixed input has small failure probability over random choices,
one fixed choice has small failure probability for the supplied input law. -/
theorem exists_choice_of_pointwise_failure {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : FiniteLaw β) (E : α → β → Prop) {ε : ℝ}
    (hE : ∀ x, μ.probability (fun a => E a x) ≤ ε) :
    ∃ a, ν.probability (E a) ≤ ε := by
  apply μ.exists_average_le
  unfold FiniteLaw.probability
  rw [μ.average_comm ν]
  exact (ν.average_mono hE).trans_eq (ν.average_const ε)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitPartialAssignment
namespace OAI

/-! Partial assignments and the consistent terms used in the canonical
decision tree of a DNF. Each term contains at most one literal per variable. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


namespace PartialAssignment





@[simp] lemma assign_empty {n : ℕ} (ρ : PartialAssignment n) (x : BooleanCube n) :
    ρ.assign ∅ x = ρ := by funext i; simp [assign]





end PartialAssignment


namespace CubeTerm










end CubeTerm

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitIsolation
namespace OAI

/-! Independent repetition amplifies the single-hit experiment. These finite
identities are the random-subset step of the circuit polynomial construction. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma singleHitScore_eq_indicator {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    singleHitScore S x = if isolatesOne S x then 1 else 0 := by
  by_cases hx : isolatesOne S x
  · rw [if_pos hx]
    obtain ⟨i, hi, hxi⟩ := hx
    unfold singleHitScore
    rw [sum_eq_single i]
    · exact if_pos hxi
    · intro j hj hji
      unfold cubePattern
      apply if_neg
      intro hxj
      have hh := (hxi i hi).symm.trans (hxj i hi)
      simp [singleBitPattern, Ne.symm hji] at hh
    · exact fun h => (h hi).elim
  · rw [if_neg hx]
    unfold singleHitScore
    apply sum_eq_zero
    intro i hi
    unfold cubePattern
    exact if_neg (fun h => hx ⟨i, hi, h⟩)

theorem bernoulliCubeLaw_isolatesOne (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) :
    (bernoulliCubeLaw n p hp hp1).probability (isolatesOne S) =
      (S.card : ℝ) * p * (1 - p) ^ (S.card - 1) := by
  unfold FiniteLaw.probability
  have heq : (fun x => if isolatesOne S x then (1 : ℝ) else 0) = singleHitScore S :=
    funext (fun x => (singleHitScore_eq_indicator S x).symm)
  rw [heq]
  exact bernoulliCubeLaw_singleHitScore n p hp hp1 S

theorem FiniteLaw.independent_failure {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) (s : ℕ) :
    (FiniteLaw.independent (fun _ : Fin s => μ)).probability
      (fun x => ∀ i, ¬E (x i)) = (1 - μ.probability E) ^ s := by
  calc
    _ = ∏ _i : Fin s, μ.probability (fun x => ¬E x) :=
      FiniteLaw.independent_probability_all (fun _ : Fin s => μ) (fun _ x => ¬E x)
    _ = _ := by
      simp only [μ.probability_complement, prod_const, card_univ, Fintype.card_fin]

theorem FiniteLaw.independent_failure_le {α : Type*} [Fintype α]
    (μ : FiniteLaw α) (E : α → Prop) (s : ℕ)
    (hE : (1 / 8 : ℝ) ≤ μ.probability E) :
    (FiniteLaw.independent (fun _ : Fin s => μ)).probability
      (fun x => ∀ i, ¬E (x i)) ≤ (7 / 8 : ℝ) ^ s := by
  rw [μ.independent_failure]
  apply pow_le_pow_left₀
  · linarith [μ.probability_le_one E]
  · linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitRandomGate
namespace OAI

/-! Polynomial gate replacement. A sampled subset contributes a linear
factor that is one on an all-true input and zero when the subset contains
exactly one false input. Repetition is a product of these factors. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {n : ℕ}

lemma WalshDegreeLE.prod {ι : Type*} (I : Finset ι) (F : ι → BooleanCube n → ℝ)
    (d : ℕ) (hF : ∀ i ∈ I, WalshDegreeLE (F i) d) :
    WalshDegreeLE (fun x => ∏ i ∈ I, F i x) (d * I.card) := by
  induction I using Finset.induction_on with
  | empty => simpa using WalshDegreeLE.const (n := n) 1 0
  | @insert i I hi ih =>
    have hFi := hF i (mem_insert_self i I)
    have hI := ih (fun j hj => hF j (mem_insert_of_mem hj))
    have hh := hFi.mul hI
    have heq : (fun x => ∏ j ∈ insert i I, F j x) =
        fun x => F i x * ∏ j ∈ I, F j x := by
      funext x
      exact prod_insert hi
    rw [heq]
    convert (preTransparency := .instances) hh using 1
    simp only [card_insert_of_notMem hi]
    ring



lemma WalshDegreeLE.andGateFactor {k : ℕ} (S : Finset (Fin k))
    (P : Fin k → BooleanCube n → ℝ) (d : ℕ)
    (hP : ∀ i ∈ S, WalshDegreeLE (P i) d) :
    WalshDegreeLE (fun x => TwoPointCorrelations.andGateFactor S (fun i => P i x)) d := by
  have hsum := WalshDegreeLE.sum S (fun i x => 1 - P i x)
    (fun i hi => (WalshDegreeLE.const (n := n) 1 d).sub (hP i hi))
  exact (WalshDegreeLE.const (n := n) 1 d).sub hsum


lemma andGateFactor_all_true {k : ℕ} (S : Finset (Fin k))
    (b : Fin k → Bool) (hb : ∀ i ∈ S, b i = true) :
    andGateFactor S (fun i => if b i then 1 else 0) = 1 := by
  unfold andGateFactor
  have hz : (∑ i ∈ S, (1 - (if b i then (1 : ℝ) else 0))) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [hb i hi]
  rw [hz, sub_zero]

lemma andGateFactor_one_false {k : ℕ} (S : Finset (Fin k))
    (b : Fin k → Bool) (hb : (S.filter (fun i => b i = false)).card = 1) :
    andGateFactor S (fun i => if b i then 1 else 0) = 0 := by
  unfold andGateFactor
  have heq : (∑ i ∈ S, (1 - (if b i then (1 : ℝ) else 0))) =
      ((S.filter (fun i => b i = false)).card : ℝ) := by
    calc
      _ = ∑ i ∈ S, (if b i = false then (1 : ℝ) else 0) := by
        apply sum_congr rfl
        intro i _
        cases b i <;> norm_num
      _ = _ := by simp
  rw [heq, hb]
  norm_num



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitSamplingGrid
namespace OAI

/-! A logarithmic grid of repeated Bernoulli samplers isolates a member of
every nonempty marked set, with failure at most `(7/8)^s`. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




theorem gateSamplingLaw_failure (n k s : ℕ) (S : Finset (Fin n))
    (hS : S.Nonempty) (hSk : S.card ≤ k) :
    (gateSamplingLaw n k s).probability
      (fun x => ∀ a i, ¬isolatesOne S (x a i)) ≤ (7 / 8 : ℝ) ^ s := by
  obtain ⟨a, ha, hhit⟩ := exists_dyadic_single_hit k S.card hS.card_pos hSk
  let a₀ : Fin (Nat.log 2 k + 3) := ⟨a, by omega⟩
  have hsingle : (1 / 8 : ℝ) ≤ (dyadicCubeLaw n a).probability (isolatesOne S) := by
    simpa only [dyadicCubeLaw, bernoulliCubeLaw_isolatesOne] using hhit
  calc
    _ = ∏ b : Fin (Nat.log 2 k + 3),
      (FiniteLaw.independent (fun _ : Fin s => dyadicCubeLaw n b.val)).probability
        (fun x => ∀ i, ¬isolatesOne S (x i)) :=
      FiniteLaw.independent_probability_all _ _
    (∏ b : Fin (Nat.log 2 k + 3),
      (FiniteLaw.independent (fun _ : Fin s => dyadicCubeLaw n b.val)).probability
        (fun x => ∀ i, ¬isolatesOne S (x i))) ≤
        ∏ b : Fin (Nat.log 2 k + 3), if b = a₀ then (7 / 8 : ℝ) ^ s else 1 := by
      apply Finset.prod_le_prod
      · intro b _
        exact FiniteLaw.probability_nonneg _ _
      · intro b _
        by_cases hb : b = a₀
        · subst b
          rw [if_pos rfl]
          exact (dyadicCubeLaw n a).independent_failure_le (isolatesOne S) s hsingle
        · rw [if_neg hb]
          exact FiniteLaw.probability_le_one _ _
    _ = (7 / 8 : ℝ) ^ s := by simp

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitGateFailure
namespace OAI

/-! The sampled AND polynomial agrees with the Boolean gate whenever the
samplers isolate a false child; all-true inputs are always exact. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





lemma sampledAndPolynomial_degree {n k s : ℕ} (x : GateSamplingChoices k k s)
    (P : Fin k → BooleanCube n → ℝ) (d : ℕ) (hP : ∀ i, WalshDegreeLE (P i) d) :
    WalshDegreeLE (fun y => sampledAndPolynomial x (fun i => P i y))
      (d * s * (Nat.log 2 k + 3)) := by
  have hinner (a : Fin (Nat.log 2 k + 3)) :
      WalshDegreeLE (fun y => ∏ i : Fin s,
        andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) (d * s) := by
    have hh := WalshDegreeLE.prod univ
      (fun i y => andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) d
        (fun i _ => WalshDegreeLE.andGateFactor _ P d (fun j _ => hP j))
    simpa only [card_univ, Fintype.card_fin] using hh
  have hh := WalshDegreeLE.prod univ
    (fun a y => ∏ i : Fin s,
      andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) (d * s)
      (fun a _ => hinner a)
  change WalshDegreeLE (fun y => ∏ a, ∏ i : Fin s,
    andGateFactor (sampledCoordinates (x a i)) (fun j => P j y)) _
  simpa only [card_univ, Fintype.card_fin] using hh

lemma isolatesOne_card {k : ℕ} {S : Finset (Fin k)} {x : BooleanCube k}
    (h : isolatesOne S x) : (S.filter (fun i => x i = true)).card = 1 := by
  obtain ⟨i, hi, hx⟩ := h
  have heq : S.filter (fun j => x j = true) = {i} := by
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hj, htrue⟩
      have hh := hx j hj
      rw [htrue] at hh
      simpa [singleBitPattern] using hh.symm
    · intro hj
      subst j
      exact ⟨hi, by simpa [singleBitPattern] using hx i hi⟩
  rw [heq, card_singleton]

lemma sampled_false_card {k : ℕ} (b : Fin k → Bool) (x : BooleanCube k)
    (h : isolatesOne (falseCoordinates b) x) :
    ((sampledCoordinates x).filter (fun i => b i = false)).card = 1 := by
  have heq : (sampledCoordinates x).filter (fun i => b i = false) =
      (falseCoordinates b).filter (fun i => x i = true) := by
    ext i
    simp only [sampledCoordinates, falseCoordinates, mem_filter, mem_univ, true_and]
    tauto
  rw [heq]
  exact isolatesOne_card h

lemma sampledAndPolynomial_all_true {k s : ℕ} (x : GateSamplingChoices k k s)
    (b : Fin k → Bool) (hb : ∀ i, b i = true) :
    sampledAndPolynomial x (fun i => if b i then 1 else 0) = 1 := by
  unfold sampledAndPolynomial
  have hh (a : Fin (Nat.log 2 k + 3)) (i : Fin s) :
      andGateFactor (sampledCoordinates (x a i)) (fun j => if b j then 1 else 0) = 1 :=
    andGateFactor_all_true _ b (fun j _ => hb j)
  simp only [hh, prod_const_one]

lemma sampledAndPolynomial_isolated {k s : ℕ} (x : GateSamplingChoices k k s)
    (b : Fin k → Bool) (h : ∃ a i, isolatesOne (falseCoordinates b) (x a i)) :
    sampledAndPolynomial x (fun i => if b i then 1 else 0) = 0 := by
  obtain ⟨a, i, hi⟩ := h
  unfold sampledAndPolynomial
  apply prod_eq_zero (mem_univ a)
  apply prod_eq_zero (mem_univ i)
  exact andGateFactor_one_false _ b (sampled_false_card b (x a i) hi)

lemma sampledAndPolynomial_failure {k s : ℕ} (x : GateSamplingChoices k k s)
    (b : Fin k → Bool)
    (h : sampledAndPolynomial x (fun i => if b i then 1 else 0) ≠ boolAndValue b) :
    ∀ a i, ¬isolatesOne (falseCoordinates b) (x a i) := by
  have hn : ¬∀ i, b i = true := by
    intro hb
    apply h
    rw [sampledAndPolynomial_all_true x b hb]
    exact (if_pos hb).symm
  intro a i hi
  apply h
  rw [sampledAndPolynomial_isolated x b ⟨a, i, hi⟩]
  exact (if_neg hn).symm

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

open _root_.Finset
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

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDegreeBound
namespace OAI

/-! At fixed depth, the sampled polynomial degree is a power of the
sampling count times the logarithm of the circuit size. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset
open scoped _root_.Classical

theorem approximationDegree_le {n : ℕ} (s : ℕ) (hs : 1 ≤ s)
    (c : AC0Circuit n) (m : ℕ) (hm : c.size ≤ m) :
    c.approximationDegree s ≤ (s * (Nat.log 2 m + 3)) ^ c.depth := by
  induction c generalizing m with
  | literal i b => simp [approximationDegree, depth]
  | @andGate k children ih | @orGate k children ih =>
    have hm' : 1 + ∑ i, (children i).size ≤ m := hm
    have hsize (i : Fin k) : (children i).size ≤ m := by
      have hh := single_le_sum (fun j _ => Nat.zero_le (children j).size) (mem_univ i)
      omega
    have hcount : k ≤ ∑ i, (children i).size := by
      calc
        k = ∑ _i : Fin k, 1 := by simp
        _ ≤ _ := sum_le_sum (fun i _ => (children i).size_pos)
    have hk : k ≤ m := by omega
    let B := s * (Nat.log 2 m + 3)
    let D := univ.sup (fun i => (children i).depth)
    have hB : 0 < B := by dsimp [B]; positivity
    have hsup : (univ.sup fun i => (children i).approximationDegree s) ≤ B ^ D := by
      apply Finset.sup_le
      intro i _
      exact (ih i m (hsize i)).trans
        (Nat.pow_le_pow_right hB (le_sup (f := fun i => (children i).depth) (mem_univ i)))
    have hlog : s * (Nat.log 2 k + 3) ≤ B :=
      Nat.mul_le_mul_left s (Nat.add_le_add_right (Nat.log_mono_right hk) 3)
    change (univ.sup fun i => (children i).approximationDegree s) * s *
      (Nat.log 2 k + 3) ≤ B ^ (1 + D)
    calc
      _ ≤ B ^ D * s * (Nat.log 2 k + 3) := by gcongr
      _ = B ^ D * (s * (Nat.log 2 k + 3)) := by ring
      _ ≤ B ^ D * B := Nat.mul_le_mul_left _ hlog
      _ = B ^ (1 + D) := by rw [Nat.add_comm 1 D, pow_succ]

end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitSampleNorm
namespace OAI

/-! Pointwise norm bounds for the sampled polynomial. These control the
exceptional values when the Fourier approximation is used as a cutoff. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma andGateFactor_abs_le {k : ℕ} (S : Finset (Fin k)) (u : Fin k → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hu : ∀ i, |u i| ≤ B) :
    |andGateFactor S u| ≤ 1 + (k : ℝ) * (1 + B) := by
  have hcard : (S.card : ℝ) ≤ k := by
    exact_mod_cast (card_le_card (subset_univ S)).trans_eq (card_fin k)
  calc
    _ ≤ |(1 : ℝ)| + |∑ i ∈ S, (1 - u i)| := abs_sub _ _
    _ ≤ 1 + ∑ i ∈ S, |1 - u i| := by
      simpa only [abs_one] using add_le_add (le_refl (1 : ℝ))
        (abs_sum_le_sum_abs (fun i => 1 - u i) S)
    _ ≤ 1 + ∑ _i ∈ S, (1 + B) := by
      apply add_le_add (le_refl (1 : ℝ))
      apply sum_le_sum
      intro i _
      exact (abs_sub _ _).trans
        (by simpa only [abs_one] using (add_le_add (le_refl (1 : ℝ)) (hu i)))
    _ = 1 + (S.card : ℝ) * (1 + B) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := add_le_add (le_refl (1 : ℝ))
      (mul_le_mul_of_nonneg_right hcard (by positivity))

lemma sampledAndPolynomial_abs_le {k s : ℕ} (sample : GateSamplingChoices k k s)
    (u : Fin k → ℝ) {B : ℝ} (hB : 0 ≤ B) (hu : ∀ i, |u i| ≤ B) :
    |sampledAndPolynomial sample u| ≤
      (1 + (k : ℝ) * (1 + B)) ^ (s * (Nat.log 2 k + 3)) := by
  calc
    _ = ∏ a : Fin (Nat.log 2 k + 3), ∏ j : Fin s,
        |andGateFactor (sampledCoordinates (sample a j)) u| := by
      simp only [sampledAndPolynomial, abs_prod]
    _ ≤ ∏ _a : Fin (Nat.log 2 k + 3), ∏ _j : Fin s,
        (1 + (k : ℝ) * (1 + B)) := by
      apply Finset.prod_le_prod
      · intro a _
        exact prod_nonneg (fun _ _ => abs_nonneg _)
      · intro a _
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun j _ => andGateFactor_abs_le _ u hB hu)
    _ = _ := by simp only [prod_const, card_univ, Fintype.card_fin, ← pow_mul]

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

open _root_.Finset
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







namespace BooleanDecisionTree




end BooleanDecisionTree

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps
namespace OAI

/-! Relabel, complement and conjoin the residue circuits used in a
closed-word expansion without increasing their internal depth. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset


lemma negate_eval {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.eval x = true ↔ c.eval x ≠ true := by
  induction c with
  | literal i b => cases b <;> cases hx : x i <;> simp [negate, eval, hx]
  | andGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_forall]
  | orGate c ih => simp only [negate, eval, ne_eq, decide_eq_true_eq, ih, not_exists]

lemma negate_depth {n : ℕ} (c : AC0Circuit n) : c.negate.depth = c.depth := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, depth, ih]
  | orGate c ih => simp only [negate, depth, ih]

lemma negate_size {n : ℕ} (c : AC0Circuit n) : c.negate.size = c.size := by
  induction c with
  | literal i b => rfl
  | andGate c ih => simp only [negate, size, ih]
  | orGate c ih => simp only [negate, size, ih]






lemma conjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (conjunction c).eval x = true ↔ ∀ i, (c i).eval x = true := by
  simp only [conjunction, eval, decide_eq_true_eq]
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h ((Fintype.equivFin ι) i)
  · intro h i
    exact h _

lemma conjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (conjunction c).depth ≤ d + 1 := by
  simp only [conjunction, depth]
  have hh : (univ.sup fun i : Fin (Fintype.card ι) =>
      (c ((Fintype.equivFin ι).symm i)).depth) ≤ d :=
    Finset.sup_le (fun i _ => hc _)
  omega

lemma conjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (conjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [conjunction, size]
  congr 1
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (c i).size)

end TwoPointCorrelations.AC0Circuit

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


end BooleanDecisionTree






end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitIsolationEvent
namespace OAI

/-! The single-hit test used by the random polynomial is itself a small
constant-depth circuit on the original child outputs. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit


lemma certificateDisjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (certificateDisjunction c).eval x = true ↔ ∃ i, (c i).eval x = true := by
  rw [certificateDisjunction, negate_eval]
  simp only [ne_eq, conjunction_eval, negate_eval, not_forall, not_not]

lemma certificateDisjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (certificateDisjunction c).depth ≤ d + 1 := by
  simp only [certificateDisjunction, negate_depth]
  exact conjunction_depth _ (fun i => by simpa only [negate_depth] using hc i)

lemma certificateDisjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (certificateDisjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [certificateDisjunction, negate_size, conjunction_size]


lemma uniqueFalseTerm_eval {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (i : S) (x : BooleanCube n) :
    (uniqueFalseTerm c S i).eval x = true ↔
      (c i).eval x = false ∧ ∀ j : S, j ≠ i → (c j).eval x = true := by
  rw [uniqueFalseTerm, conjunction_eval]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have hi := h i
      apply Bool.eq_false_iff.mpr
      simpa only [ite_true, negate_eval] using hi
    · simpa only [if_neg hj] using h j
  · rintro ⟨hi, h⟩ j
    by_cases hj : j = i
    · subst j
      rw [if_pos rfl, negate_eval, hi]
      decide
    · simpa only [if_neg hj] using h j hj


lemma uniqueFalseCircuit_eval {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (x : BooleanCube n) :
    (uniqueFalseCircuit c S).eval x = true ↔
      ∃ i : S, (c i).eval x = false ∧ ∀ j : S, j ≠ i → (c j).eval x = true := by
  simp only [uniqueFalseCircuit, certificateDisjunction_eval, uniqueFalseTerm_eval]

lemma uniqueFalseTerm_depth {n k d : ℕ} (c : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) (S : Finset (Fin k)) (i : S) :
    (uniqueFalseTerm c S i).depth ≤ d + 1 := by
  apply conjunction_depth
  intro j
  split_ifs <;> simpa only [negate_depth] using hc j

lemma uniqueFalseCircuit_depth {n k d : ℕ} (c : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) (S : Finset (Fin k)) :
    (uniqueFalseCircuit c S).depth ≤ d + 2 := by
  exact certificateDisjunction_depth _ (uniqueFalseTerm_depth c hc S)

lemma uniqueFalseTerm_size {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) (i : S) :
    (uniqueFalseTerm c S i).size = 1 + ∑ j : S, (c j).size := by
  rw [uniqueFalseTerm, conjunction_size]
  congr 1
  apply sum_congr rfl
  intro j _
  split_ifs <;> simp only [negate_size]

lemma uniqueFalseCircuit_size {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) :
    (uniqueFalseCircuit c S).size = 1 + S.card * (1 + ∑ j : S, (c j).size) := by
  simp only [uniqueFalseCircuit, certificateDisjunction_size, uniqueFalseTerm_size, sum_const,
    card_univ, Fintype.card_coe, nsmul_eq_mul, Nat.cast_id]

lemma uniqueFalseCircuit_size_le {n k : ℕ} (c : Fin k → AC0Circuit n)
    (S : Finset (Fin k)) :
    (uniqueFalseCircuit c S).size ≤ 1 + k * (1 + ∑ j, (c j).size) := by
  rw [uniqueFalseCircuit_size]
  have hcard : S.card ≤ k := (card_le_card (subset_univ S)).trans_eq (card_fin k)
  have hsum : ∑ j : S, (c j).size ≤ ∑ j, (c j).size := by
    calc
      _ = ∑ j ∈ S, (c j).size := sum_coe_sort S (fun j => (c j).size)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)
  exact Nat.add_le_add_left (Nat.mul_le_mul hcard (Nat.add_le_add_left hsum 1)) 1

end AC0Circuit

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitSamplingException
namespace OAI

/-! The exceptional event is expressed by the single-hit circuits, so it
can itself be approximated by Fourier truncation in the next stage. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma isolatesOne_false_iff {k : ℕ} (b mask : BooleanCube k) :
    isolatesOne (falseCoordinates b) mask ↔
      ∃ i : sampledCoordinates mask, b i = false ∧
        ∀ j : sampledCoordinates mask, j ≠ i → b j = true := by
  constructor
  · rintro ⟨i, hi, hm⟩
    have hbi : b i = false := (mem_filter.mp hi).2
    have hmi : mask i = true := by simpa [singleBitPattern] using hm i hi
    let v : sampledCoordinates mask := ⟨i, by simp [sampledCoordinates, hmi]⟩
    refine ⟨v, hbi, ?_⟩
    intro j hji
    have hval : j.val ≠ i := fun h => hji (Subtype.ext h)
    have hmj : mask j = true := (mem_filter.mp j.property).2
    cases hb : b j
    · have hj : j.val ∈ falseCoordinates b := by simp [falseCoordinates, hb]
      have ht := hm j hj
      simp [singleBitPattern, hval, hmj] at ht
    · rfl
  · rintro ⟨i, hbi, hj⟩
    refine ⟨i, by simp [falseCoordinates, hbi], ?_⟩
    intro j hjfalse
    have hbj : b j = false := (mem_filter.mp hjfalse).2
    by_cases hji : j = i.val
    · subst j
      have hmi : mask i = true := (mem_filter.mp i.property).2
      simpa [singleBitPattern] using hmi
    · have hmj : mask j = false := by
        cases hmask : mask j
        · rfl
        · let v : sampledCoordinates mask := ⟨j, by simp [sampledCoordinates, hmask]⟩
          have hne : v ≠ i := fun h => hji (congrArg Subtype.val h)
          have htrue := hj v hne
          rw [show b v = false from hbj] at htrue
          contradiction
      simp [singleBitPattern, hji, hmj]

namespace AC0Circuit


lemma gateSamplingException_eval {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n)
    (x : BooleanCube n) :
    (gateSamplingException sample c).eval x = true ↔
      (¬∀ i, (c i).eval x = true) ∧
        ∀ a j, ¬isolatesOne (falseCoordinates (fun i => (c i).eval x)) (sample a j) := by
  simp only [gateSamplingException, conjunction_eval, Bool.forall_bool, Bool.false_eq_true,
    ite_false, ite_true, negate_eval, ne_eq, certificateDisjunction_eval, uniqueFalseCircuit_eval,
    eval, decide_eq_true_eq, not_exists, Prod.forall, isolatesOne_false_iff]

lemma gateSamplingException_depth {n k s d : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) :
    (gateSamplingException sample c).depth ≤ d + 4 := by
  apply conjunction_depth
  intro flag
  cases flag
  · simp only [Bool.false_eq_true, ite_false, negate_depth, depth]
    have h := Finset.sup_le (fun i (_ : i ∈ univ) => hc i)
    omega
  · simp only [ite_true, negate_depth]
    apply certificateDisjunction_depth
    intro j
    exact uniqueFalseCircuit_depth c hc _

lemma gateSamplingException_size {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n) :
    (gateSamplingException sample c).size ≤
      3 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) := by
  rw [gateSamplingException, conjunction_size]
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, negate_size,
    certificateDisjunction_size, size]
  have hsum : (∑ j : Fin (Nat.log 2 k + 3) × Fin s,
      (uniqueFalseCircuit c (sampledCoordinates (sample j.1 j.2))).size) ≤
        s * (Nat.log 2 k + 3) * (1 + k * (1 + ∑ i, (c i).size)) := by
    calc
      _ ≤ ∑ _j : Fin (Nat.log 2 k + 3) × Fin s,
          (1 + k * (1 + ∑ i, (c i).size)) :=
        sum_le_sum (fun j _ => uniqueFalseCircuit_size_le c _)
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]; ring
  omega

end AC0Circuit

lemma sampledAndPolynomial_error_detected {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c : Fin k → AC0Circuit n)
    (x : BooleanCube n)
    (h : sampledAndPolynomial sample (fun i => (c i).indicator x) ≠
      (AC0Circuit.andGate c).indicator x) :
    (AC0Circuit.gateSamplingException sample c).eval x = true := by
  rw [AC0Circuit.gateSamplingException_eval]
  have hb : sampledAndPolynomial sample (fun i => if (c i).eval x then 1 else 0) ≠
      boolAndValue (fun i => (c i).eval x) := by
    simpa only [AC0Circuit.indicator, AC0Circuit.eval, decide_eq_true_eq, boolAndValue] using h
  refine ⟨?_, sampledAndPolynomial_failure sample _ hb⟩
  intro hall
  apply hb
  rw [sampledAndPolynomial_all_true sample _ hall]
  exact (if_pos hall).symm

lemma gateSamplingException_pointwise_probability {n k : ℕ} (s : ℕ)
    (c : Fin k → AC0Circuit n) (x : BooleanCube n) :
    (gateSamplingLaw k k s).probability
      (fun sample => (AC0Circuit.gateSamplingException sample c).eval x = true) ≤
        (7 / 8 : ℝ) ^ s := by
  by_cases hall : ∀ i, (c i).eval x = true
  · have hz : (gateSamplingLaw k k s).probability
        (fun sample => (AC0Circuit.gateSamplingException sample c).eval x = true) = 0 := by
      have he (sample : GateSamplingChoices k k s) :
          ¬(AC0Circuit.gateSamplingException sample c).eval x = true := by
        intro h
        exact ((AC0Circuit.gateSamplingException_eval sample c x).mp h).1 hall
      unfold FiniteLaw.probability
      simp only [if_neg (he _)]
      exact FiniteLaw.average_const (gateSamplingLaw k k s) 0
    rw [hz]
    positivity
  · have hnonempty : (falseCoordinates (fun i => (c i).eval x)).Nonempty := by
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine ⟨i, ?_⟩
      cases hb : (c i).eval x <;> simp_all [falseCoordinates]
    have hcard : (falseCoordinates (fun i => (c i).eval x)).card ≤ k := by
      exact (card_le_card (filter_subset _ _)).trans_eq (card_fin k)
    apply le_trans ((gateSamplingLaw k k s).probability_mono ?_)
      (gateSamplingLaw_failure k k s _ hnonempty hcard)
    intro sample hsample
    exact (AC0Circuit.gateSamplingException_eval sample c x).mp hsample |>.2

theorem exists_gateSamplingException_small {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : Fin k → AC0Circuit n) :
    ∃ sample : GateSamplingChoices k k s,
      ν.probability (fun x => (AC0Circuit.gateSamplingException sample c).eval x = true) ≤
        (7 / 8 : ℝ) ^ s := by
  exact exists_choice_of_pointwise_failure (gateSamplingLaw k k s) ν _
    (gateSamplingException_pointwise_probability s c)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitCertifiedGate
namespace OAI

/-! The sampled gate carries a Boolean certificate for all its errors:
the new single-hit failure test together with the child certificates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit


lemma combineGateException_eval {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n)
    (x : BooleanCube n) :
    (combineGateException sample c E).eval x = true ↔
      (gateSamplingException sample c).eval x = true ∨ ∃ i, (E i).eval x = true := by
  simp only [combineGateException, certificateDisjunction_eval, Option.exists]

lemma combineGateException_size {n k s : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n) :
    (combineGateException sample c E).size =
      1 + (gateSamplingException sample c).size + ∑ i, (E i).size := by
  simp only [combineGateException, certificateDisjunction_size, Fintype.sum_option]
  omega

lemma combineGateException_depth {n k s d D : ℕ}
    (sample : GateSamplingChoices k k s) (c E : Fin k → AC0Circuit n)
    (hc : ∀ i, (c i).depth ≤ d) (hE : ∀ i, (E i).depth ≤ D)
    (hd : d + 4 ≤ D) :
    (combineGateException sample c E).depth ≤ D + 1 := by
  apply certificateDisjunction_depth
  intro i
  cases i with
  | none => exact (gateSamplingException_depth sample c hc).trans hd
  | some i => exact hE i

end AC0Circuit

theorem exists_certified_and_sample {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c E : Fin k → AC0Circuit n)
    (P : Fin k → BooleanCube n → ℝ) (δ : Fin k → ℝ)
    (hδ : ∀ i, ν.probability (fun x => (E i).eval x = true) ≤ δ i)
    (hcorrect : ∀ i x, (E i).eval x ≠ true → P i x = (c i).indicator x) :
    ∃ sample : GateSamplingChoices k k s,
      ν.probability (fun x => (AC0Circuit.combineGateException sample c E).eval x = true) ≤
        (7 / 8 : ℝ) ^ s + ∑ i, δ i ∧
      ∀ x, (AC0Circuit.combineGateException sample c E).eval x ≠ true →
        sampledAndPolynomial sample (fun i => P i x) = (AC0Circuit.andGate c).indicator x := by
  obtain ⟨sample, hs⟩ := exists_gateSamplingException_small ν s c
  refine ⟨sample, ?_, ?_⟩
  · let events : Option (Fin k) → BooleanCube n → Prop
      | none => fun x => (AC0Circuit.gateSamplingException sample c).eval x = true
      | some i => fun x => (E i).eval x = true
    have hcover : ∀ x,
        (AC0Circuit.combineGateException sample c E).eval x = true → ∃ i, events i x := by
      intro x hx
      rcases (AC0Circuit.combineGateException_eval sample c E x).mp hx with h | ⟨i, hi⟩
      · exact ⟨none, h⟩
      · exact ⟨some i, hi⟩
    calc
      _ ≤ ν.probability (fun x => ∃ i, events i x) := ν.probability_mono hcover
      _ ≤ ∑ i, ν.probability (events i) := ν.probability_exists_le events
      _ = ν.probability (events none) + ∑ i : Fin k, ν.probability (events (some i)) := by
        simp only [Fintype.sum_option]
      _ ≤ _ := add_le_add hs (sum_le_sum (fun i _ => hδ i))
  · intro x hx
    have hc : ∀ i, P i x = (c i).indicator x := by
      intro i
      apply hcorrect i x
      intro hi
      exact hx ((AC0Circuit.combineGateException_eval sample c E x).mpr (Or.inr ⟨i, hi⟩))
    have hp : (fun i => P i x) = fun i => (c i).indicator x := funext hc
    rw [hp]
    by_contra h
    have hlocal := sampledAndPolynomial_error_detected sample c x h
    exact hx ((AC0Circuit.combineGateException_eval sample c E x).mpr (Or.inl hlocal))

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitCertificateBounds
namespace OAI

/-! Numerical bounds carried by the recursive polynomial/error-circuit
construction. They retain explicit circuit dependence until the final
size and depth estimates. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

namespace AC0Circuit



lemma sampleNormBound_nonneg {n : ℕ} (s : ℕ) (c : AC0Circuit n) :
    0 ≤ c.sampleNormBound s := by
  induction c with
  | literal i b => exact zero_le_one
  | andGate c ih | orGate c ih =>
    have hh : 0 ≤ ∑ i, (c i).sampleNormBound s := sum_nonneg (fun i _ => ih i)
    simp only [sampleNormBound]
    positivity

lemma negate_indicator {n : ℕ} (c : AC0Circuit n) (x : BooleanCube n) :
    c.negate.indicator x = 1 - c.indicator x := by
  have he : c.negate.eval x = !(c.eval x) := by
    apply Bool.eq_iff_iff.mpr
    rw [negate_eval]
    simp
  simp only [indicator, he]
  cases c.eval x <;> norm_num

end AC0Circuit



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitAndCertificate
namespace OAI

/-! An AND gate preserves the full approximation certificate: polynomial,
small Boolean error circuit, and pointwise norm bound. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def CircuitCertificate.andGate {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : Fin k → AC0Circuit n)
    (H : ∀ i, CircuitCertificate ν s (c i)) :
    CircuitCertificate ν s (.andGate c) := by
  let P := fun i => (H i).polynomial
  let E := fun i => (H i).error
  let hs := exists_certified_and_sample ν s c E P
    (fun i => ((c i).size : ℝ) * (7 / 8 : ℝ) ^ s)
    (fun i => (H i).error_probability) (fun i => (H i).exact_off_error)
  let sample := Classical.choose hs
  have hprob := (Classical.choose_spec hs).1
  have hexact := (Classical.choose_spec hs).2
  refine
    { polynomial := fun x => sampledAndPolynomial sample (fun i => P i x)
      error := AC0Circuit.combineGateException sample c E
      degree_bound := ?_
      error_depth := ?_
      error_size := ?_
      error_probability := ?_
      exact_off_error := hexact
      norm_bound := ?_ }
  · exact sampledAndPolynomial_degree sample P _ (fun i =>
      ((H i).degree_bound).mono
        (le_sup (f := fun j => (c j).approximationDegree s) (mem_univ i)))
  · let D := univ.sup (fun i => (c i).depth)
    have hc (i : Fin k) : (c i).depth ≤ D :=
      le_sup (f := fun j => (c j).depth) (mem_univ i)
    have hE (i : Fin k) : (E i).depth ≤ 4 * D + 4 := by
      have hh := (H i).error_depth
      have hd := hc i
      dsimp only [E]
      omega
    have hh := AC0Circuit.combineGateException_depth sample c E hc hE (by omega)
    change (AC0Circuit.combineGateException sample c E).depth ≤ 4 * (1 + D) + 1
    omega
  · rw [AC0Circuit.combineGateException_size]
    have hs := AC0Circuit.gateSamplingException_size sample c
    have he : ∑ i, (E i).size ≤ ∑ i, (c i).exceptionSizeBound s :=
      sum_le_sum (fun i _ => (H i).error_size)
    change 1 + (AC0Circuit.gateSamplingException sample c).size + ∑ i, (E i).size ≤
      4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, (c i).exceptionSizeBound s
    omega
  · convert (preTransparency := .instances) hprob using 1
    simp only [AC0Circuit.size, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_mul,
      one_mul, sum_mul]
  · intro x
    let B := ∑ i, (c i).sampleNormBound s
    have hB : 0 ≤ B := sum_nonneg (fun i _ => AC0Circuit.sampleNormBound_nonneg s (c i))
    have hP (i : Fin k) : |P i x| ≤ B :=
      ((H i).norm_bound x).trans
        (single_le_sum (fun j _ => AC0Circuit.sampleNormBound_nonneg s (c j)) (mem_univ i))
    have hb := sampledAndPolynomial_abs_le sample (fun i => P i x) hB hP
    have hp : (1 + (k : ℝ) * (1 + B)) ^ (s * (Nat.log 2 k + 3)) ≤
        (1 + (k : ℝ) * (2 + B)) ^ (s * (Nat.log 2 k + 3)) :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    change |sampledAndPolynomial sample (fun i => P i x)| ≤
      1 + (1 + (k : ℝ) * (2 + B)) ^ (s * (Nat.log 2 k + 3))
    linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitOrCertificate
namespace OAI

/-! The OR step uses complementary child polynomials and the same Boolean
error certificates. Both polarities therefore admit the same recursive bounds. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

noncomputable def CircuitCertificate.orGate {n k : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (c : Fin k → AC0Circuit n)
    (H : ∀ i, CircuitCertificate ν s (c i)) :
    CircuitCertificate ν s (.orGate c) := by
  let P := fun i x => 1 - (H i).polynomial x
  let E := fun i => (H i).error
  let c' := fun i => (c i).negate
  have hcorrect (i : Fin k) (x : BooleanCube n) (hx : (E i).eval x ≠ true) :
      P i x = (c' i).indicator x := by
    change 1 - (H i).polynomial x = (c i).negate.indicator x
    rw [(H i).exact_off_error x hx, AC0Circuit.negate_indicator]
  let hs := exists_certified_and_sample ν s c' E P
    (fun i => ((c i).size : ℝ) * (7 / 8 : ℝ) ^ s)
    (fun i => (H i).error_probability) hcorrect
  let sample := Classical.choose hs
  have hprob := (Classical.choose_spec hs).1
  have hexact := (Classical.choose_spec hs).2
  refine
    { polynomial := fun x => 1 - sampledAndPolynomial sample (fun i => P i x)
      error := AC0Circuit.combineGateException sample c' E
      degree_bound := ?_
      error_depth := ?_
      error_size := ?_
      error_probability := ?_
      exact_off_error := ?_
      norm_bound := ?_ }
  · let d := univ.sup (fun i => (c i).approximationDegree s)
    have hP (i : Fin k) : WalshDegreeLE (P i) d :=
      (WalshDegreeLE.const 1 d).sub ((H i).degree_bound.mono
        (le_sup (f := fun j => (c j).approximationDegree s) (mem_univ i)))
    exact (WalshDegreeLE.const 1 _).sub (sampledAndPolynomial_degree sample P d hP)
  · let D := univ.sup (fun i => (c i).depth)
    have hc (i : Fin k) : (c' i).depth ≤ D := by
      simpa only [c', AC0Circuit.negate_depth] using
        (le_sup (f := fun j => (c j).depth) (mem_univ i))
    have hE (i : Fin k) : (E i).depth ≤ 4 * D + 4 := by
      have hh := (H i).error_depth
      have hd := le_sup (f := fun j => (c j).depth) (mem_univ i)
      change (H i).error.depth ≤ 4 * D + 4
      omega
    have hh := AC0Circuit.combineGateException_depth sample c' E hc hE (by omega)
    change (AC0Circuit.combineGateException sample c' E).depth ≤ 4 * (1 + D) + 1
    omega
  · rw [AC0Circuit.combineGateException_size]
    have hs := AC0Circuit.gateSamplingException_size sample c'
    simp only [c', AC0Circuit.negate_size] at hs
    have he : ∑ i, (E i).size ≤ ∑ i, (c i).exceptionSizeBound s :=
      sum_le_sum (fun i _ => (H i).error_size)
    change 1 + (AC0Circuit.gateSamplingException sample c').size + ∑ i, (E i).size ≤
      4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, (c i).exceptionSizeBound s
    dsimp only [c']
    omega
  · convert (preTransparency := .instances) hprob using 1
    simp only [AC0Circuit.size, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_mul,
      one_mul, sum_mul]
  · intro x hx
    have hh := hexact x hx
    change 1 - sampledAndPolynomial sample (fun i => P i x) = _
    rw [hh]
    have he := AC0Circuit.negate_indicator (.orGate c) x
    change (AC0Circuit.andGate c').indicator x = 1 - (AC0Circuit.orGate c).indicator x at he
    rw [he]
    ring
  · intro x
    let B := ∑ i, (c i).sampleNormBound s
    have hB : 0 ≤ B := sum_nonneg (fun i _ => AC0Circuit.sampleNormBound_nonneg s (c i))
    have hP (i : Fin k) : |P i x| ≤ 1 + B := by
      have hi : |(H i).polynomial x| ≤ B :=
        ((H i).norm_bound x).trans
          (single_le_sum (fun j _ => AC0Circuit.sampleNormBound_nonneg s (c j)) (mem_univ i))
      exact (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) hi)
    have hb := sampledAndPolynomial_abs_le sample (fun i => P i x) (by positivity : 0 ≤ 1 + B) hP
    have hbase : 1 + (k : ℝ) * (1 + (1 + B)) = 1 + (k : ℝ) * (2 + B) := by ring
    rw [hbase] at hb
    change |1 - sampledAndPolynomial sample (fun i => P i x)| ≤
      1 + (1 + (k : ℝ) * (2 + B)) ^ (s * (Nat.log 2 k + 3))
    exact (abs_sub _ _).trans (by simpa only [abs_one] using add_le_add (le_refl (1 : ℝ)) hb)

noncomputable def AC0Circuit.certificate {n : ℕ} (ν : FiniteLaw (BooleanCube n))
    (s : ℕ) (c : AC0Circuit n) : CircuitCertificate ν s c := by
  induction c with
  | literal i b => exact CircuitCertificate.literal ν s i b
  | andGate c ih => exact CircuitCertificate.andGate ν s c ih
  | orGate c ih => exact CircuitCertificate.orGate ν s c ih

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitExceptionBudget
namespace OAI

/-! The recursive error certificate has polynomial size. Only this coarse
bound, rather than the detailed shape of its gates, is used by the next stage. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset
open scoped _root_.Classical


theorem exceptionSizeBound_le {n : ℕ} (s : ℕ) (c : AC0Circuit n)
    (m : ℕ) (hm : c.size ≤ m) :
    c.exceptionSizeBound s ≤ exceptionPolynomialBound m s * c.size := by
  induction c generalizing m with
  | literal i b =>
    simp only [exceptionSizeBound, size, mul_one, exceptionPolynomialBound]
    omega
  | @andGate k c ih | @orGate k c ih =>
    have hm' : 1 + ∑ i, (c i).size ≤ m := hm
    have hsize (i : Fin k) : (c i).size ≤ m := by
      have hh := single_le_sum (fun j _ => Nat.zero_le (c j).size) (mem_univ i)
      omega
    have hcount : k ≤ ∑ i, (c i).size := by
      calc
        k = ∑ _i : Fin k, 1 := by simp
        _ ≤ _ := sum_le_sum (fun i _ => (c i).size_pos)
    have hk : k ≤ m := by omega
    have hsum : ∑ i, (c i).exceptionSizeBound s ≤
        exceptionPolynomialBound m s * ∑ i, (c i).size := by
      rw [mul_sum]
      exact sum_le_sum (fun i _ => ih i m (hsize i))
    have hlocal : 4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) ≤ exceptionPolynomialBound m s := by
      unfold exceptionPolynomialBound
      have hsumsize : ∑ i, (c i).size ≤ m := by omega
      have hlog := Nat.log_mono_right (b := 2) hk
      gcongr
      norm_num
    change 4 + (∑ i, (c i).size) + s * (Nat.log 2 k + 3) *
        (1 + k * (1 + ∑ i, (c i).size)) + ∑ i, (c i).exceptionSizeBound s ≤
      exceptionPolynomialBound m s * (1 + ∑ i, (c i).size)
    calc
      _ ≤ exceptionPolynomialBound m s +
          exceptionPolynomialBound m s * ∑ i, (c i).size := Nat.add_le_add hlocal hsum
      _ = _ := by ring

end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitNormBudget
namespace OAI

/-! A coarse uniform bound on the exceptional values of the polynomial.
For fixed depth its logarithm is polynomial in the sampling count and log size. -/

namespace TwoPointCorrelations.AC0Circuit

open _root_.Finset
open scoped _root_.Classical

theorem sampleNormBound_le {n : ℕ} (s : ℕ) (c : AC0Circuit n)
    (m : ℕ) (hm : c.size ≤ m) :
    c.sampleNormBound s ≤ (2 * ((m : ℝ) + 1) ^ 2) ^
      ((2 * (s * (Nat.log 2 m + 3)) + 2) ^ c.depth) := by
  induction c generalizing m with
  | literal i b =>
    simp only [sampleNormBound, depth, pow_zero, pow_one]
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  | @andGate k c ih | @orGate k c ih =>
    have hm' : 1 + ∑ i, (c i).size ≤ m := hm
    have hsize (i : Fin k) : (c i).size ≤ m := by
      have hh := single_le_sum (fun j _ => Nat.zero_le (c j).size) (mem_univ i)
      omega
    have hcount : k ≤ ∑ i, (c i).size := by
      calc
        k = ∑ _i : Fin k, 1 := by simp
        _ ≤ _ := sum_le_sum (fun i _ => (c i).size_pos)
    have hk : k ≤ m := by omega
    have hkreal : (k : ℝ) ≤ m := by exact_mod_cast hk
    let A : ℝ := 2 * ((m : ℝ) + 1) ^ 2
    let R := s * (Nat.log 2 m + 3)
    let D := univ.sup (fun i => (c i).depth)
    let E := (2 * R + 2) ^ D
    let V := A ^ E
    have hA : 2 ≤ A := by dsimp [A]; nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hA1 : 1 ≤ A := by linarith
    have hV : 1 ≤ V := one_le_pow₀ hA1
    have hE : 1 ≤ E := by dsimp [E]; exact Nat.one_le_pow D (2 * R + 2) (by omega)
    have hchildren (i : Fin k) : (c i).sampleNormBound s ≤ V := by
      have hdepth := le_sup (f := fun j => (c j).depth) (mem_univ i)
      exact (ih i m (hsize i)).trans (pow_le_pow_right₀ hA1
        (Nat.pow_le_pow_right (by omega : 0 < 2 * R + 2) hdepth))
    have hsum : ∑ i, (c i).sampleNormBound s ≤ (m : ℝ) * V := by
      calc
        _ ≤ ∑ _i : Fin k, V := sum_le_sum (fun i _ => hchildren i)
        _ = (k : ℝ) * V := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hkreal (by linarith)
    have hS0 : 0 ≤ ∑ i, (c i).sampleNormBound s :=
      sum_nonneg (fun i _ => sampleNormBound_nonneg s (c i))
    have hbase : 1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s) ≤ A * V := by
      have hh := mul_le_mul hkreal (add_le_add (le_refl (2 : ℝ)) hsum)
        (by linarith : (0 : ℝ) ≤ 2 + ∑ i, (c i).sampleNormBound s) (Nat.cast_nonneg m)
      have hpoly := mul_le_mul_of_nonneg_left hV
        (show 0 ≤ (m : ℝ) ^ 2 + 4 * m + 2 by positivity)
      dsimp [A]
      nlinarith
    have hnonneg : 0 ≤ 1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s) := by
      positivity
    have hR : s * (Nat.log 2 k + 3) ≤ R :=
      Nat.mul_le_mul_left s (Nat.add_le_add_right (Nat.log_mono_right hk) 3)
    have hpow : (1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s)) ^
        (s * (Nat.log 2 k + 3)) ≤ (A * V) ^ R :=
      (pow_le_pow_left₀ hnonneg hbase _).trans
        (pow_le_pow_right₀ (by nlinarith) hR)
    have heq : (A * V) ^ R = A ^ ((E + 1) * R) := by
      dsimp only [V]
      rw [← pow_succ', ← pow_mul]
    have hplus : 1 + A ^ ((E + 1) * R) ≤ A ^ ((E + 1) * R + 1) := by
      have hz : 1 ≤ A ^ ((E + 1) * R) := one_le_pow₀ hA1
      rw [pow_succ]
      nlinarith
    have hexponent : (E + 1) * R + 1 ≤ (2 * R + 2) ^ (D + 1) := by
      have hRE : R ≤ R * E := by simpa using Nat.mul_le_mul_left R hE
      rw [pow_succ]
      change (E + 1) * R + 1 ≤ E * (2 * R + 2)
      nlinarith
    change 1 + (1 + (k : ℝ) * (2 + ∑ i, (c i).sampleNormBound s)) ^
      (s * (Nat.log 2 k + 3)) ≤ A ^ ((2 * R + 2) ^ (1 + D))
    calc
      _ ≤ 1 + (A * V) ^ R := add_le_add (le_refl (1 : ℝ)) hpow
      _ = 1 + A ^ ((E + 1) * R) := by rw [heq]
      _ ≤ A ^ ((E + 1) * R + 1) := hplus
      _ ≤ _ := pow_le_pow_right₀ hA1 (by simpa [Nat.add_comm] using hexponent)

end TwoPointCorrelations.AC0Circuit

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitBravermanApproximation
namespace OAI

/-! The combinatorial approximation stage of Braverman's proof, with a
fully explicit error circuit and coarse quantitative bounds. The depth
estimate is sufficient for the fixed-depth comparison. -/

namespace TwoPointCorrelations

theorem AC0Circuit.polynomial_error_approximation {n : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (s : ℕ) (hs : 1 ≤ s) (c : AC0Circuit n) :
    ∃ (P : BooleanCube n → ℝ) (E : AC0Circuit n),
      WalshDegreeLE P ((s * (Nat.log 2 c.size + 3)) ^ c.depth) ∧
      E.depth ≤ 4 * c.depth + 1 ∧
      E.size ≤ exceptionPolynomialBound c.size s * c.size ∧
      ν.probability (fun x => E.eval x = true) ≤ (c.size : ℝ) * (7 / 8 : ℝ) ^ s ∧
      (∀ x, E.eval x ≠ true → P x = c.indicator x) ∧
      ∀ x, |P x| ≤ (2 * ((c.size : ℝ) + 1) ^ 2) ^
        ((2 * (s * (Nat.log 2 c.size + 3)) + 2) ^ c.depth) := by
  let H := c.certificate ν s
  refine ⟨H.polynomial, H.error, ?_, H.error_depth, ?_, H.error_probability,
    H.exact_off_error, ?_⟩
  · exact H.degree_bound.mono (AC0Circuit.approximationDegree_le s hs c c.size le_rfl)
  · exact H.error_size.trans (AC0Circuit.exceptionSizeBound_le s c c.size le_rfl)
  · intro x
    exact (H.norm_bound x).trans (AC0Circuit.sampleNormBound_le s c c.size le_rfl)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicBudgets
namespace OAI

/-! Natural-number budgets for the fixed depth twenty-two application.
Using powers of two keeps the exponential error calculation elementary. -/

namespace TwoPointCorrelations

open scoped _root_.Classical


lemma bravermanSamples_pos (j : ℕ) : 1 ≤ bravermanSamples j := by
  unfold bravermanSamples
  omega

lemma bravermanBase_pos (j : ℕ) : 1 ≤ bravermanBase j := by
  unfold bravermanBase
  have := bravermanSamples_pos j
  nlinarith


lemma nat_log_le_of_dyadic {m j : ℕ} (hm : m ≤ 2 ^ j) : Nat.log 2 m ≤ j := by
  simpa only [Nat.log_pow (by norm_num : 1 < 2)] using Nat.log_mono_right (b := 2) hm

lemma braverman_error_size_budget {m j : ℕ} (hm : m ≤ 2 ^ j) :
    AC0Circuit.exceptionPolynomialBound m (bravermanSamples j) * m ≤
      2 ^ bravermanErrorExponent j := by
  have hj : j + 1 ≤ 2 ^ j := Nat.succ_le_of_lt j.lt_two_pow_self
  have hs : bravermanSamples j ≤ 2 ^ (j + 6) := by
    unfold bravermanSamples
    calc
      40 * (j + 1) ≤ 64 * 2 ^ j := Nat.mul_le_mul (by norm_num) hj
      _ = 2 ^ (j + 6) := by rw [pow_add]; ring
  have hl : Nat.log 2 m + 3 ≤ 2 ^ (j + 2) := by
    have hh := nat_log_le_of_dyadic hm
    rw [pow_add]
    norm_num
    omega
  have hp : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by omega)
  have hbracket : 1 + m * (1 + m) ≤ 2 ^ (2 * j + 2) := by
    calc
      1 + m * (1 + m) ≤ 4 * (2 ^ j) ^ 2 := by nlinarith [hm]
      _ = 2 ^ (2 * j + 2) := by
        rw [pow_add, show 2 * j = j * 2 by omega, pow_mul]
        ring
  have hadd : 5 + m ≤ 2 ^ (4 * j + 10) := by
    calc
      5 + m ≤ 8 * 2 ^ j := by omega
      _ = 2 ^ (j + 3) := by rw [pow_add]; ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hprod : bravermanSamples j * (Nat.log 2 m + 3) * (1 + m * (1 + m)) ≤
      2 ^ (4 * j + 10) := by
    calc
      _ ≤ 2 ^ (j + 6) * 2 ^ (j + 2) * 2 ^ (2 * j + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul hs hl) hbracket
      _ = _ := by simp only [← pow_add]; congr 1; omega
  calc
    _ ≤ (2 ^ (4 * j + 10) + 2 ^ (4 * j + 10)) * 2 ^ j :=
      Nat.mul_le_mul (Nat.add_le_add hadd hprod) hm
    _ = 2 ^ (5 * j + 11) := by simp only [pow_succ]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by unfold bravermanErrorExponent; omega)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Circuits.CircuitDyadicApproximation
namespace OAI

/-! Specialize the proved approximation construction to dyadic size
budgets and circuit depth twenty-two. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

lemma braverman_approx_degree_bound {m j d : ℕ} (hm : m ≤ 2 ^ j) (hd : d ≤ 22) :
    (bravermanSamples j * (Nat.log 2 m + 3)) ^ d ≤ bravermanBase j ^ 22 := by
  have hbase : bravermanSamples j * (Nat.log 2 m + 3) ≤ bravermanBase j :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (nat_log_le_of_dyadic hm) 3)
  exact (Nat.pow_le_pow_left hbase _).trans
    (Nat.pow_le_pow_right (bravermanBase_pos j) hd)

lemma braverman_norm_power_bound {m j d : ℕ} (hm : m ≤ 2 ^ j) (hd : d ≤ 22) :
    (2 * (bravermanSamples j * (Nat.log 2 m + 3)) + 2) ^ d ≤
      (2 * bravermanBase j + 2) ^ 22 := by
  have hbase : bravermanSamples j * (Nat.log 2 m + 3) ≤ bravermanBase j :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (nat_log_le_of_dyadic hm) 3)
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hbase) 2) _).trans
    (Nat.pow_le_pow_right (by omega) hd)

lemma braverman_norm_base_bound {m j : ℕ} (hm : m ≤ 2 ^ j) :
    2 * ((m : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (2 * j + 3) := by
  have hmreal : (m : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hm
  have htwo : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hsum : (m : ℝ) + 1 ≤ 2 * (2 : ℝ) ^ j := by linarith only [hmreal, htwo]
  calc
    _ ≤ 2 * (2 * (2 : ℝ) ^ j) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg m) zero_le_one) hsum 2) (by norm_num)
    _ = _ := by
      rw [pow_add, show 2 * j = j * 2 by omega, pow_mul]
      ring

theorem AC0Circuit.dyadic_approximation {n j : ℕ}
    (ν : FiniteLaw (BooleanCube n)) (c : AC0Circuit n)
    (hc : c.depth ≤ 22) (hm : c.size ≤ 2 ^ j) :
    ∃ (P : BooleanCube n → ℝ) (E : AC0Circuit n),
      WalshDegreeLE P (bravermanBase j ^ 22) ∧
      E.depth ≤ 89 ∧ E.size ≤ 2 ^ bravermanErrorExponent j ∧
      ν.probability (fun x => E.eval x = true) ≤
        (2 : ℝ) ^ j * (7 / 8 : ℝ) ^ bravermanSamples j ∧
      (∀ x, E.eval x ≠ true → P x = c.indicator x) ∧
      ∀ x, |P x| ≤ (2 : ℝ) ^ bravermanNormExponent j := by
  obtain ⟨P, E, hP, hd, hsize, hprob, he, hnorm⟩ :=
    c.polynomial_error_approximation ν (bravermanSamples j) (bravermanSamples_pos j)
  have hmreal : (c.size : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast hm
  have h89 : E.depth ≤ 89 := hd.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hc) 1)
  refine ⟨P, E, hP.mono (braverman_approx_degree_bound hm hc), h89,
    hsize.trans (braverman_error_size_budget hm), ?_, he, ?_⟩
  · exact hprob.trans (mul_le_mul_of_nonneg_right hmreal (by positivity))
  · intro x
    calc
      |P x| ≤ _ := hnorm x
      _ ≤ ((2 : ℝ) ^ (2 * j + 3)) ^
          ((2 * (bravermanSamples j * (Nat.log 2 c.size + 3)) + 2) ^ c.depth) :=
        pow_le_pow_left₀ (by positivity) (braverman_norm_base_bound hm) _
      _ ≤ ((2 : ℝ) ^ (2 * j + 3)) ^ ((2 * bravermanBase j + 2) ^ 22) :=
        pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (braverman_norm_power_bound hm hc)
      _ = _ := by rw [← pow_mul]; rfl

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.AC0Circuit.dyadic_approximation := @OAI.TwoPointCorrelations.AC0Circuit.dyadic_approximation
