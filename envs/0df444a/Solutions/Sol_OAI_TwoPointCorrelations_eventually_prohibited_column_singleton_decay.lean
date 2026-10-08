-- Prove2me | solution 1 for OAI.TwoPointCorrelations.eventually_prohibited_column_singleton_decay
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T02:48:24.967507+00:00
-- url     : https://prove2.me/submissions/8387f378-8950-43fe-ab21-56a2da5b38ec

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_encoded_witness_sum_le
import Theorems.Thm_OAI_TwoPointCorrelations_prohibited_singleton_words_le_catalog

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeWordCounting
namespace OAI

/-! Finite descriptions used by the reciprocal crude count. -/

namespace TwoPointCorrelations

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSystemCodes
namespace OAI

/-! Finite endpoint, partner, and label descriptions for selected witness systems. -/

namespace TwoPointCorrelations

open _root_.Finset







lemma card_witnessRelationSlot (n N : ℕ) (ι : Type*) [Fintype ι] :
    Fintype.card (WitnessRelationSlot n N ι) = Fintype.card ι ^ 2 * n * (N + 1) ^ 4 := by
  simp only [WitnessRelationSlot, Fintype.card_prod, Fintype.card_fin]
  ring

/-- A single optional-slot function records the chosen set as well as all
its data, so no extra subset-count factor is needed. -/
theorem card_witnessSystemData_le (n N : ℕ) (ι : Type*) [Fintype ι] :
    Fintype.card (WitnessSystemData n N ι) ≤
      4 * (1 + Fintype.card ι ^ 2 * n * (N + 1) ^ 4) ^ n := by
  have hc := Fintype.card_le_of_injective (@witnessSystemCode n N ι)
    (witnessSystemCode_injective n N ι)
  have heq : Fintype.card (Fin 4 × (Fin n → Option (WitnessRelationSlot n N ι))) =
      4 * (1 + Fintype.card ι ^ 2 * n * (N + 1) ^ 4) ^ n := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_option, card_witnessRelationSlot, Nat.add_comm]
  rw [heq] at hc
  exact hc

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessCodeBounds
namespace OAI

/-! The concrete witness relation records have polynomial cost per witness. -/

namespace TwoPointCorrelations

lemma card_witnessSystemData_exp (n N : ℕ) (ι : Type*) [Fintype ι]
    (hlabels : Fintype.card ι ≤ N + 1) (hn : n ≤ N + 1) :
    (Fintype.card (WitnessSystemData n N ι) : ℝ) ≤
      Real.exp (Real.log 4 + (n : ℝ) * (Real.log 2 + 7 * Real.log (N + 1))) := by
  have hpoly : Fintype.card ι ^ 2 * n * (N + 1) ^ 4 ≤ (N + 1) ^ 7 := by
    calc
      _ ≤ (N + 1) ^ 2 * (N + 1) * (N + 1) ^ 4 := by gcongr
      _ = _ := by ring
  have h1 : 1 ≤ (N + 1) ^ 7 := one_le_pow₀ (by omega)
  have hcount := card_witnessSystemData_le n N ι
  have hmajor : Fintype.card (WitnessSystemData n N ι) ≤
      4 * (2 * (N + 1) ^ 7) ^ n := by
    apply hcount.trans
    gcongr
    omega
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have h7 : Real.exp (7 * Real.log ((N : ℝ) + 1)) = ((N : ℝ) + 1) ^ (7 : ℕ) := by
    simpa only [Nat.cast_ofNat, Real.exp_log hpos] using
      (Real.exp_nat_mul (Real.log ((N : ℝ) + 1)) 7)
  calc
    _ ≤ (4 : ℝ) * (2 * ((N : ℝ) + 1) ^ (7 : ℕ)) ^ n := by exact_mod_cast hmajor
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_nat_mul,
        Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2), h7]

/-- The selected-system metadata fits within the same `exp(O(L log²L))`
allowance as the underlying word patterns. -/
theorem card_witnessSystemData_scale (n N : ℕ) (ι : Type*) [Fintype ι]
    (L : ℝ) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hlabels : Fintype.card ι ≤ N + 1) (hnN : n ≤ N + 1)
    (hn : (n : ℝ) ≤ 4 * L) (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (WitnessSystemData n N ι) : ℝ) ≤
      Real.exp (63 * L * (Real.log L) ^ 2) := by
  have hlog4 : Real.log 4 ≤ 3 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogN : Real.log ((N : ℝ) + 1) ≤ 2 * Real.log L := by
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < N + 1) hN
    simpa only [Real.log_pow, Nat.cast_ofNat] using ht
  have hm := mul_le_mul_of_nonneg_left
    (show Real.log 2 + 7 * Real.log ((N : ℝ) + 1) ≤ 15 * Real.log L by linarith)
    (show (0 : ℝ) ≤ n by positivity)
  have hn' := mul_le_mul_of_nonneg_right hn (show 0 ≤ 15 * Real.log L by linarith)
  have hl : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ 60 * L by positivity)
  have hsq : 1 ≤ L * (Real.log L) ^ 2 := by nlinarith [sq_nonneg (Real.log L)]
  apply (card_witnessSystemData_exp n N ι hlabels hnN).trans
  apply Real.exp_le_exp.mpr
  nlinarith

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









lemma TuplePrimeAt.index_lt {w : List SignedStep} {p i : ℕ} (hp : TuplePrimeAt w p i) :
    i < w.length := by
  obtain ⟨_, a, ha, _⟩ := hp
  exact (List.getElem?_eq_some_iff.mp ha).1



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WordBlockGeometry
namespace OAI

/-! Geometry of actual surviving positive words, including the prime-support checks. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma tuplePrimeAt_iff_getElem (w : List SignedStep) (p i : ℕ) (hi : i < w.length) :
    TuplePrimeAt w p i ↔ p.Prime ∧ p ∣ w[i].tuple := by
  simp [TuplePrimeAt, List.getElem?_eq_getElem hi]









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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SingletonDecay
namespace OAI

/-! The selected singleton savings dominate the complete crude trace cost. -/

namespace TwoPointCorrelations

open _root_.Filter


/-- `647/600 = 1/12 + 199/200` exceeds the desired exponent `21/20`.
All fixed coefficients in the enumeration affect only the threshold. -/
theorem eventually_singleton_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ r : ℕ,
      L ^ (1 / 12 : ℝ) / 32 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      Real.exp (C * L * (Real.log L) ^ 2) *
        (Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  have h8 := (tendsto_rpow_atTop (show 0 < (19 / 300 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 8)
  have h64 := (tendsto_rpow_atTop (show 0 < (17 / 600 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 64)
  filter_upwards [eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_crude_cost_small (2 * C) (by positivity), h8, h64] with L hL hlog hcost h8 h64
  intro r hrlo hrhi
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have heq1 : L ^ (203 / 200 : ℝ) * L ^ (19 / 300 : ℝ) = L ^ (647 / 600 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have heq2 : L ^ (21 / 20 : ℝ) * L ^ (17 / 600 : ℝ) = L ^ (647 / 600 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have heq3 : L ^ (1 / 12 : ℝ) * L ^ (199 / 200 : ℝ) = L ^ (647 / 600 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  have hp1 := mul_le_mul_of_nonneg_left h8 (Real.rpow_nonneg hLp.le (203 / 200 : ℝ))
  rw [heq1] at hp1
  have hp2 := mul_le_mul_of_nonneg_left h64 (Real.rpow_nonneg hLp.le (21 / 20 : ℝ))
  rw [heq2] at hp2
  have hnegative := mul_le_mul_of_nonneg_right hrlo
    (Real.rpow_nonneg hLp.le (199 / 200 : ℝ))
  rw [div_mul_eq_mul_div, heq3] at hnegative
  have hpositive := mul_le_mul_of_nonneg_left hrhi
    (show 0 ≤ C * Real.log L by positivity)
  have hlog' : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
  have hpos2 := mul_le_mul_of_nonneg_left hlog' (show 0 ≤ C * L by positivity)
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- The one-coordinate progression factor in exponential form. -/
lemma progression_factor_le_exp (N : ℕ) (H T D : ℝ)
    (hH : Real.exp T ≤ H) (hN : 2 + Real.log N ≤ Real.exp D) :
    H⁻¹ + (1 + Real.log N) / H ≤ Real.exp (D - T) := by
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  calc
    _ = (2 + Real.log N) * H⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ Real.exp D * Real.exp (-T) := by
      apply mul_le_mul hN _ (inv_nonneg.mpr hHp.le) (by positivity)
      rw [Real.exp_neg]
      exact inv_anti₀ (Real.exp_pos _) hH
    _ = _ := by simp only [sub_eq_add_neg, Real.exp_add]

/-- The actual cutoffs `N ≤ exp L` and `H ≥ exp(L^(199/200))`
give a progression factor at most one for all sufficiently large `L`. -/
lemma eventually_singleton_progression_factor :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ) (H : ℝ), 1 ≤ N → (N : ℝ) ≤ Real.exp L →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      H⁻¹ + (1 + Real.log N) / H ≤ Real.exp (2 * Real.log L - L ^ (199 / 200 : ℝ)) ∧
        H⁻¹ + (1 + Real.log N) / H ≤ 1 := by
  have hs := (isLittleO_log_rpow_atTop (show 0 < (199 / 200 : ℝ) by norm_num)).bound
    (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards [eventually_ge_atTop 2, hs] with L hL hs
  intro N H hN hNL hH
  have hLp : 0 < L := by linarith
  have hl : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hl, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hs
  have hlogN : Real.log (N : ℝ) ≤ L := by
    have ht := Real.log_le_log (show (0 : ℝ) < N by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hN) hNL
    simpa only [Real.log_exp] using ht
  have hnum : 2 + Real.log N ≤ Real.exp (2 * Real.log L) := by
    have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
      rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
        Real.exp_add, Real.exp_log hLp]
      ring
    rw [he]
    nlinarith
  have hb := progression_factor_le_exp N H (L ^ (199 / 200 : ℝ)) (2 * Real.log L) hH hnum
  refine ⟨hb, hb.trans ?_⟩
  rw [← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  linarith

/-- Transfer the finite progression estimate to the same exponential
scale. Its harmless numerator `2 + log N` is kept explicitly. -/
theorem eventually_singleton_total (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (r N : ℕ) (H cost total : ℝ),
      L ^ (1 / 12 : ℝ) / 32 ≤ (r : ℝ) → (r : ℝ) ≤ L →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      2 + Real.log N ≤ Real.exp (C * Real.log L) →
      0 ≤ cost → cost ≤ Real.exp (C * L * (Real.log L) ^ 2) →
      total ≤ cost * (H⁻¹ + (1 + Real.log N) / H) ^ r →
      total ≤ Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_singleton_decay C hC] with L hL
  intro r N H cost total hrlo hrhi hH hN hcost hcost' htotal
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hnum : 0 ≤ 2 + Real.log N := by
    by_cases hzero : N = 0
    · simp [hzero]
    · have hn : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero
      have hl := Real.log_nonneg hn
      linarith
  have hbase := progression_factor_le_exp N H (L ^ (199 / 200 : ℝ))
    (C * Real.log L) hH hN
  have hnonneg : 0 ≤ H⁻¹ + (1 + Real.log N) / H := by
    rw [show H⁻¹ + (1 + Real.log N) / H = (2 + Real.log N) * H⁻¹ by
      rw [div_eq_mul_inv]; ring]
    positivity
  apply htotal.trans
  calc
    _ ≤ cost * (Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg hbase r) hcost
    _ ≤ Real.exp (C * L * (Real.log L) ^ 2) *
        (Real.exp (C * Real.log L - L ^ (199 / 200 : ℝ))) ^ r :=
      mul_le_mul_of_nonneg_right hcost' (by positivity)
    _ ≤ _ := hL r hrlo hrhi

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessRecordBudget
namespace OAI

/-! One explicit polynomial budget covers all concatenated witness lengths and prime slots. -/

namespace TwoPointCorrelations

open _root_.Filter




lemma witnessRecordBudget_slots (D J M n r : ℕ) (hr : r ≤ D) :
    r * (J + M) ≤ witnessRecordBudget D J M n := by
  exact (Nat.mul_le_mul_right (J + M) hr).trans (by unfold witnessRecordBudget; omega)

lemma eventually_witnessRecordBudget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ D J M n : ℕ,
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
      (n : ℝ) ≤ 4 * L → (witnessRecordBudget D J M n : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
  have hsmall := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show 0 < 1 / (16 * (C + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (64 : ℝ), hsmall] with L hL hlog
  intro D J M n hD hJM hn
  have hLp : 0 < L := by linarith
  have hlogpos : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg hlogpos, Real.norm_eq_abs,
    Real.rpow_one, abs_of_pos hLp] at hlog
  have hbudget : C * Real.log L ≤ L / 16 := by
    have hh : 16 * (C + 1) * Real.log L ≤ L := by
      have ht := hlog
      rw [one_div, inv_mul_eq_div] at ht
      simpa only [mul_comm] using
        (le_div_iff₀ (show 0 < 16 * (C + 1) by positivity)).mp ht
    nlinarith
  have hslots : (D : ℝ) * ((J + M : ℕ) : ℝ) ≤ L ^ (2 : ℕ) / 4 := by
    have hj : ((J + M : ℕ) : ℝ) ≤ L / 16 := hJM.trans hbudget
    have hm := mul_le_mul hD hj (Nat.cast_nonneg _) (by positivity : 0 ≤ 4 * L)
    nlinarith
  unfold witnessRecordBudget
  push_cast
  push_cast at hslots
  nlinarith

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

open _root_.Finset
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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeNumericalWordSum
namespace OAI

/-! Complete reciprocal counting for actual numerical tuple and padding words. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical





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



end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessCatalogCost
namespace OAI

/-! Complete finite equality-pattern and witness-metadata cost. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma witnessCatalogCost_nonneg (R T n M : ℕ) (VP VQ : ℝ)
    (hP : 0 ≤ VP) (hQ : 0 ≤ VQ) : 0 ≤ witnessCatalogCost R T n M VP VQ := by
  unfold witnessCatalogCost
  positivity

theorem witnessCatalogCost_exp_bound (R T n M : ℕ) (L C : ℝ)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hslots : (T : ℝ) ≤ C * R * Real.log L)
    (hT : (T : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hRp : (R : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (hTM : T ≤ M + 1) (hnM : n ≤ M + 1) (hn : (n : ℝ) ≤ 4 * L)
    (hM : (M : ℝ) + 1 ≤ L ^ (2 : ℕ))
    (VP VQ : ℝ) (hP : 0 ≤ VP) (hQ : 0 ≤ VQ)
    (hPup : VP ≤ L ^ (2 : ℕ)) (hQup : VQ ≤ L ^ (2 : ℕ)) :
    witnessCatalogCost R T n M VP VQ ≤
      Real.exp (63 * L * (Real.log L) ^ 2 + (3 + 7 * C) * R * (Real.log L) ^ 2) := by
  have hU : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL
  have hmeta (t : Fin (T + 1)) (c : CrudeWordCode R t.val R) :
      (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) ≤
        Real.exp (63 * L * (Real.log L) ^ 2) := by
    apply card_witnessSystemData_scale n M c.tupleClasses L hL hlog _ hnM hn hM
    have hc := c.class_count_le_slots
    omega
  calc
    _ ≤ ∑ t : Fin (T + 1), ∑ c : CrudeWordCode R t.val R,
        Real.exp (63 * L * (Real.log L) ^ 2) * (L ^ (2 : ℕ)) ^ T := by
      apply sum_le_sum
      intro t _
      apply sum_le_sum
      intro c _
      have hmass := (c.class_mass_le hP hQ hPup hQup hU).trans
        (pow_le_pow_right₀ hU (show t.val ≤ T by omega))
      calc
        _ = (Fintype.card (WitnessSystemData n M c.tupleClasses) : ℝ) *
            (VP ^ Fintype.card c.tupleClasses *
              VQ ^ Fintype.card {z : c.usedClasses // z ∉ c.tupleClasses}) := by ring
        _ ≤ _ := mul_le_mul (hmeta t c) hmass (by positivity) (by positivity)
    _ = Real.exp (63 * L * (Real.log L) ^ 2) *
        ((∑ t : Fin (T + 1), (Fintype.card (CrudeWordCode R t.val R) : ℝ)) *
          (L ^ (2 : ℕ)) ^ T) := by
      simp only [sum_const, card_univ, nsmul_eq_mul]
      rw [sum_mul, mul_sum]
      apply sum_congr rfl
      intro t _
      ring
    _ ≤ Real.exp (63 * L * (Real.log L) ^ 2) *
        Real.exp ((3 + 7 * C) * R * (Real.log L) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      convert (preTransparency := .instances) crude_numerical_cost_exp_bound R T 2 L C (L ^ (2 : ℕ)) hR
        (zero_lt_one.trans_le hL) hlog hslots hT hRp hU le_rfl using 1
      congr 1
      ring
    _ = _ := (Real.exp_add _ _).symm

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.EncodedWitnessDecay
namespace OAI

/-! Exponential singleton saving for the entire encoded numerical witness catalog. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_encoded_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (R T n K M mainLength h s J H B : ℕ)
      (start len : Fin n → ℕ) (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop) (W : ℝ),
      1 ≤ R → (R : ℝ) ≤ 4 * L → R ≤ M →
      (T : ℝ) ≤ C * R * Real.log L →
      (T : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      T ≤ M + 1 → n ≤ M + 1 → (n : ℝ) ≤ 4 * L → (M : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      8 * K ≤ n → L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      (∀ p ∈ P, p.Prime) → 1 ≤ primeHarmonicMass P →
      primeHarmonicMass P ≤ L ^ (2 : ℕ) → primeHarmonicMass Q ≤ L ^ (2 : ℕ) →
      1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ P, H ≤ p) → (∀ p ∈ P, p ≤ B) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      W * (∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n mainLength start len h s J supply then e.weight else 0) ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  let A := 63 + Cw + 4 * (3 + 7 * C)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA2 : 2 ≤ A := by dsimp [A]; linarith
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_singleton_progression_factor, eventually_singleton_total A hA]
      with L hL hlog hfactor hdecay
  intro R T n K M mainLength h s J H B start len P Q supply W
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  have hLp : 0 < L := by linarith
  have hHp : (0 : ℝ) < H := (Real.exp_pos _).trans_le hH
  have hHN : 0 < H := by exact_mod_cast hHp
  have hraw := encoded_witness_sum_le R T n K M mainLength h s J start len P Q supply
    hRM hsize hP hV H B hHN hB hlo hhi (hfactor B H hB hBexp hH).2
  have hcost : W * witnessCatalogCost R T n M (primeHarmonicMass P) (primeHarmonicMass Q) ≤
      Real.exp (A * L * (Real.log L) ^ 2) := by
    have hb := witnessCatalogCost_exp_bound R T n M L C hR (by linarith) hlog
      hslots hT hRp hTM hnM hn hM (primeHarmonicMass P) (primeHarmonicMass Q)
      (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity) hPup hQup
    have hr := mul_le_mul_of_nonneg_right hRL
      (show 0 ≤ (3 + 7 * C) * (Real.log L) ^ 2 by positivity)
    calc
      _ ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (63 * L * (Real.log L) ^ 2 + (3 + 7 * C) * R * (Real.log L) ^ 2) :=
        mul_le_mul hWup hb (witnessCatalogCost_nonneg _ _ _ _ _ _
          (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))
          (Real.exp_pos _).le
      _ = Real.exp (Cw * L * (Real.log L) ^ 2 +
          (63 * L * (Real.log L) ^ 2 + (3 + 7 * C) * R * (Real.log L) ^ 2)) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A]; nlinarith)
  have hlogB : Real.log (B : ℝ) ≤ L := by
    have hb := Real.log_le_log (show (0 : ℝ) < B by exact_mod_cast (by omega : 0 < B)) hBexp
    simpa only [Real.log_exp] using hb
  have hnum : 2 + Real.log B ≤ Real.exp (A * Real.log L) := by
    have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
      rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
        Real.exp_add, Real.exp_log hLp]
      ring
    calc
      _ ≤ L ^ (2 : ℕ) := by nlinarith
      _ = Real.exp (2 * Real.log L) := he.symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA2 (by linarith))
  apply hdecay K B H (W * witnessCatalogCost R T n M (primeHarmonicMass P) (primeHarmonicMass Q))
    _ hKlo hKhi hH hnum (mul_nonneg hW (witnessCatalogCost_nonneg _ _ _ _ _ _
      (by unfold primeHarmonicMass; positivity) (by unfold primeHarmonicMass; positivity))) hcost
  have hb := mul_le_mul_of_nonneg_left hraw hW
  simpa only [witnessCatalogCost, mul_assoc] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessSegmentation
namespace OAI

/-! Explicit finite metadata for splitting one recorded word into witness paths. -/

namespace TwoPointCorrelations

open _root_.Finset


lemma card_witnessSegmentation (n R : ℕ) :
    Fintype.card (WitnessSegmentation n R) = (R + 1) ^ (2 * n + 1) := by
  simp only [WitnessSegmentation, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [show 2 * n + 1 = n + n + 1 by omega, pow_add, pow_add]
  ring

lemma witnessSegmentation_cost (n R : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hn : (n : ℝ) ≤ 4 * L) (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (WitnessSegmentation n R) : ℝ) ≤
      Real.exp (18 * L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hLp]
    ring
  calc
    _ = ((R : ℝ) + 1) ^ (2 * n + 1) := by
      rw [card_witnessSegmentation]
      push_cast
      rfl
    _ ≤ (L ^ (2 : ℕ)) ^ (2 * n + 1) :=
      pow_le_pow_left₀ (by positivity) hR _
    _ = Real.exp (((2 * n + 1 : ℕ) : ℝ) * (2 * Real.log L)) := by
      rw [Real.exp_nat_mul, he]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      push_cast
      have hs : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
      have hcoef : 4 * (n : ℝ) + 2 ≤ 18 * L := by linarith
      have hm := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ Real.log L by linarith)
      have hm' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 18 * L by positivity)
      nlinarith

/-- A common scalar bound with the exact finite cardinality pays for every record. -/
lemma sum_le_of_card_mul_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (B : ℝ) (hf : ∀ i, (Fintype.card ι : ℝ) * f i ≤ B) :
    ∑ i, f i ≤ B := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    (Fintype.card ι : ℝ) * (∑ i, f i) = ∑ i, (Fintype.card ι : ℝ) * f i :=
      mul_sum _ _ _
    _ ≤ ∑ _i : ι, B := sum_le_sum (fun i _ => hf i)
    _ = (Fintype.card ι : ℝ) * B := by simp

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


lemma witnessAttachment_cost (n R : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hn : (n : ℝ) ≤ 4 * L) (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (Fin n → Fin (R + 1)) : ℝ) ≤
      Real.exp (8 * L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hLp]
    ring
  calc
    _ = ((R : ℝ) + 1) ^ n := by simp
    _ ≤ (L ^ (2 : ℕ)) ^ n := pow_le_pow_left₀ (by positivity) hR n
    _ = Real.exp ((n : ℝ) * (2 * Real.log L)) := by rw [Real.exp_nat_mul, he]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * Real.log L by positivity)
      have hm' := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8 * L by positivity)
      nlinarith

lemma witnessRecord_cost (n R : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hn : (n : ℝ) ≤ 4 * L) (hR : (R : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (WitnessRecord n R) : ℝ) ≤
      Real.exp (26 * L * (Real.log L) ^ 2) := by
  change (Fintype.card (WitnessSegmentation n R × (Fin n → Fin (R + 1))) : ℝ) ≤ _
  rw [Fintype.card_prod, Nat.cast_mul]
  calc
    _ ≤ Real.exp (18 * L * (Real.log L) ^ 2) *
        Real.exp (8 * L * (Real.log L) ^ 2) :=
      mul_le_mul (witnessSegmentation_cost n R L hL hlog hn hR)
        (witnessAttachment_cost n R L hL hlog hn hR) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring


theorem eventually_attached_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (R T n K M h s J H B : ℕ)
      (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop) (W : ℝ),
      1 ≤ R → (R : ℝ) ≤ 4 * L → R ≤ M →
      (T : ℝ) ≤ C * R * Real.log L →
      (T : ℝ) + 1 ≤ L ^ (2 : ℕ) → (R : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      T ≤ M + 1 → n ≤ M + 1 → (n : ℝ) ≤ 4 * L → (M : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      8 * K ≤ n → L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      (∀ p ∈ P, p.Prime) → 1 ≤ primeHarmonicMass P →
      primeHarmonicMass P ≤ L ^ (2 : ℕ) → primeHarmonicMass Q ≤ L ^ (2 : ℕ) →
      1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ P, H ≤ p) → (∀ p ∈ P, p ≤ B) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ d : WitnessRecord n R, W * (∑ e : PrimeWordEncoding R T P Q,
        if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
          h s J supply then e.weight else 0)) ≤
          Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_encoded_witness_decay C (Cw + 26) hC (by positivity)]
      with L hL hlog hdecay
  intro R T n K M h s J H B P Q supply W
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  let W' := W * (Fintype.card (WitnessRecord n R) : ℝ)
  have hW' : W' ≤ Real.exp ((Cw + 26) * L * (Real.log L) ^ 2) := by
    calc
      W' ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (26 * L * (Real.log L) ^ 2) :=
        mul_le_mul hWup (witnessRecord_cost n R L hL hlog hn hRp)
          (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply sum_le_of_card_mul_le
  intro d
  have hb := hdecay R T n K M d.1.1.val h s J H B
    (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val) P Q supply W'
    hR hRL hRM hslots hT hRp hTM hnM hn hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH (by dsimp [W']; positivity) hW'
  dsimp only [W'] at hb
  rw [mul_assoc, mul_left_comm W (Fintype.card (WitnessRecord n R) : ℝ)] at hb
  exact hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.BoundedWitnessDecay
namespace OAI

/-! The singleton saving absorbs all record lengths, including the empty-word case. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

lemma PrimeWordEncoding.Witnesses.length_pos {R T n mainLength h s J : ℕ}
    {P Q : Finset ℕ} {start len : Fin n → ℕ} {supply : ℕ → ℕ → Prop}
    {e : PrimeWordEncoding R T P Q}
    (he : e.Witnesses n mainLength start len h s J supply) (hn : 0 < n) : 0 < R := by
  obtain ⟨_, _, _, _, _, _, _, hminimal, _⟩ := he.2.2
  have hl := (hminimal ⟨0, hn⟩).1.1
  have ht := List.length_take_le' (len ⟨0, hn⟩) (e.decode.drop (start ⟨0, hn⟩))
  have hd : (e.decode.drop (start ⟨0, hn⟩)).length ≤ e.decode.length := by
    rw [List.length_drop]
    exact Nat.sub_le _ _
  have heLen : e.decode.length = R := e.2.1.numericalWord_length _
  have hR : 3 ≤ R := hl.trans (ht.trans (hd.trans_eq heLen))
  omega

lemma witnessLengthRecord_cost (D : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hD : (D : ℝ) + 1 ≤ L ^ (2 : ℕ)) :
    (Fintype.card (Fin (D + 1)) : ℝ) ≤ Real.exp (2 * L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
    rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
      Real.exp_add, Real.exp_log hLp]
    ring
  calc
    _ = (D : ℝ) + 1 := by simp
    _ ≤ L ^ (2 : ℕ) := hD
    _ = Real.exp (2 * Real.log L) := he.symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hL (sq_nonneg (Real.log L))
      nlinarith

theorem eventually_bounded_witness_decay (C Cw : ℝ) (hC : 0 ≤ C) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (D n K M h s J H B : ℕ) (slots : ℕ → ℕ)
      (P Q : Finset ℕ) (supply : ℕ → ℕ → Prop) (W : ℝ),
      (D : ℝ) ≤ 4 * L → D ≤ M →
      (∀ R ≤ D, (slots R : ℝ) ≤ C * R * Real.log L) →
      (∀ R ≤ D, (slots R : ℝ) + 1 ≤ L ^ (2 : ℕ)) →
      (D : ℝ) + 1 ≤ L ^ (2 : ℕ) → (∀ R ≤ D, slots R ≤ M + 1) →
      0 < n → n ≤ M + 1 → (n : ℝ) ≤ 4 * L → (M : ℝ) + 1 ≤ L ^ (2 : ℕ) →
      8 * K ≤ n → L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      (∀ p ∈ P, p.Prime) → 1 ≤ primeHarmonicMass P →
      primeHarmonicMass P ≤ L ^ (2 : ℕ) → primeHarmonicMass Q ≤ L ^ (2 : ℕ) →
      1 ≤ B → (B : ℝ) ≤ Real.exp L →
      (∀ p ∈ P, H ≤ p) → (∀ p ∈ P, p ≤ B) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      0 ≤ W → W ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ R : Fin (D + 1), ∑ d : WitnessRecord n R.val,
        W * (∑ e : PrimeWordEncoding R.val (slots R.val) P Q,
          if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val) (fun i => (d.1.2.2 i).val)
            h s J supply then e.weight else 0)) ≤ Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_attached_witness_decay C (Cw + 2) hC (by positivity)]
      with L hL hlog hdecay
  intro D n K M h s J H B slots P Q supply W
    hD hDM hslots hslotpoly hDp hslotM hn hnM hnL hM hsize hKlo hKhi hP hV hPup hQup
    hB hBexp hlo hhi hH hW hWup
  let W' := W * (Fintype.card (Fin (D + 1)) : ℝ)
  have hW' : W' ≤ Real.exp ((Cw + 2) * L * (Real.log L) ^ 2) := by
    calc
      W' ≤ Real.exp (Cw * L * (Real.log L) ^ 2) *
          Real.exp (2 * L * (Real.log L) ^ 2) :=
        mul_le_mul hWup (witnessLengthRecord_cost D L hL hlog hDp)
          (by positivity) (by positivity)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply sum_le_of_card_mul_le
  intro r
  have hrD : r.val ≤ D := by omega
  by_cases hr : 0 < r.val
  · have hrL : (r.val : ℝ) ≤ 4 * L :=
      (by exact_mod_cast hrD : (r.val : ℝ) ≤ D).trans hD
    have hrp : (r.val : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
      have hh : (r.val : ℝ) ≤ D := by exact_mod_cast hrD
      linarith
    have hb := hdecay r.val (slots r.val) n K M h s J H B P Q supply W'
      hr hrL (hrD.trans hDM) (hslots _ hrD) (hslotpoly _ hrD) hrp
      (hslotM _ hrD) hnM hnL hM hsize hKlo hKhi hP hV hPup hQup
      hB hBexp hlo hhi hH (by dsimp [W']; positivity) hW'
    calc
      _ = ∑ d : WitnessRecord n r.val, W' *
          (∑ e : PrimeWordEncoding r.val (slots r.val) P Q,
            if e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
                (fun i => (d.1.2.2 i).val) h s J supply then e.weight else 0) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        dsimp only [W']
        ring
      _ ≤ _ := hb
  · have he (d : WitnessRecord n r.val) (e : PrimeWordEncoding r.val (slots r.val) P Q) :
        ¬e.Witnesses n d.1.1.val (fun i => (d.1.2.1 i).val)
          (fun i => (d.1.2.2 i).val) h s J supply := fun he => hr (he.length_pos hn)
    simp only [he, ite_false, sum_const_zero, mul_zero]
    exact (Real.exp_pos _).le

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.NumericalTupleLabels
namespace OAI

/-! Prime-slot coverage for the numerical words in the trace catalog. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma ofFn_step_get {R : ℕ} (step : Fin R → SignedStep) (k : Fin (List.ofFn step).length) :
    (List.ofFn step).get k = step ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩ := by
  change (List.ofFn step)[k.val] = _
  simp only [List.getElem_ofFn]

lemma numerical_label_cover {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val)) :
    ∀ k : Fin (List.ofFn step).length, ∀ p : ↥(data.P ∪ data.Q),
      p.val ∈ ((List.ofFn step).get k).tuple.primeFactors → p ∈ univ.image label := by
  intro k p hp
  rw [ofFn_step_get, hlabel] at hp
  obtain ⟨j, _, hj⟩ := mem_image.mp hp
  exact mem_image.mpr ⟨(_, j), mem_univ _, Subtype.ext hj⟩

lemma numerical_label_pool {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val)) :
    ∀ p ∈ univ.image label, p.val ∈ data.P := by
  intro p hp
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hp
  apply data.tuple_pool _ (hpairs i)
  rw [hlabel]
  exact mem_image.mpr ⟨j, mem_univ _, rfl⟩

lemma numerical_word_pairs {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep)
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs) :
    ∀ a ∈ List.ofFn step, (a.tuple, a.padding) ∈ data.pairs := by
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  exact hpairs i

lemma numerical_label_seen {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val)) :
    ∀ p ∈ univ.image label, p.val ∈ wordDivisorPrimeSupport (List.ofFn step) := by
  intro p hp
  obtain ⟨⟨i, j⟩, _, rfl⟩ := mem_image.mp hp
  apply mem_biUnion.mpr
  refine ⟨step i, List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩), ?_⟩
  rw [Nat.primeFactors_mul (data.padding_squarefree _ (hpairs i)).ne_zero
    (data.tuple_squarefree _ (hpairs i)).ne_zero]
  apply mem_union_right
  rw [hlabel]
  exact mem_image.mpr ⟨j, mem_univ _, rfl⟩


lemma numerical_singleton_position {h J M R : ℕ} (data : ProhibitedPrimeFamily h J M)
    (step : Fin R → SignedStep) (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hpairs : ∀ i, ((step i).tuple, (step i).padding) ∈ data.pairs)
    (hlabel : ∀ i, (step i).tuple.primeFactors = univ.image (fun j => (label (i, j)).val))
    (c : singletonLabels label) (v : ℕ)
    (hv : TuplePrimeAt (List.ofFn step) c.val.val v) :
    v = (singletonRepresentative label c).1.val := by
  have hvR : v < R := by simpa only [List.length_ofFn] using hv.index_lt
  let i : Fin R := ⟨v, hvR⟩
  have hd := ((tuplePrimeAt_iff_getElem _ _ _ hv.index_lt).mp hv).2
  have hd' : c.val.val ∣ (step i).tuple := by
    simpa only [List.getElem_ofFn] using hd
  have hm : c.val.val ∈ (step i).tuple.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hv.1, hd', (data.tuple_squarefree _ (hpairs i)).ne_zero⟩
  rw [hlabel] at hm
  obtain ⟨j, _, hj⟩ := mem_image.mp hm
  have he : label (i, j) = c.val := Subtype.ext hj
  exact congrArg (fun t : Fin R × Fin J => t.1.val)
    (singleton_occurrence_unique label c (i, j) he)

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedSingletonDecay
namespace OAI

/-! Full singleton decay for the original divisibility-centered word and literal vertex deletion. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_singleton_decay (Cs Cw : ℝ) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (F : Finset (List SignedStep))
      (label : List SignedStep → Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : List SignedStep → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : List SignedStep → ℝ) (A : ℝ),
      0 ≤ A →
      (∀ main ∈ F, 0 ≤ cap main) →
      (∀ main ∈ F, ∀ x, 0 ≤ weight main x) →
      (∀ main ∈ F, ∀ x, weight main x ≤ cap main) →
      (∀ main ∈ F, cap main * 2 ^ (R * J + (singletonLabels (label main)).card) ≤ A) →
      (∀ main ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label main) → x i = y i) →
        weight main x = weight main y) →
      (∀ main ∈ F, ∀ x, weight main x ≠ 0 → MainPaddingTests
        (fun p : ↥(data.P ∪ data.Q) => p.val) h B main x) →
      (∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ wordDivisorPrimeSupport main) →
      (∀ main ∈ F, ∀ i ∈ univ.image (label main), i.val ∈ data.P) →
      (∀ main ∈ F, ∀ t ∈ main, (t.tuple, t.padding) ∈ data.pairs) →
      (∀ main ∈ F, ∀ (k : Fin main.length) (i : ↥(data.P ∪ data.Q)),
        i.val ∈ (main.get k).tuple.primeFactors → i ∈ univ.image (label main)) →
      (∀ main ∈ F, ∀ i : singletonLabels (label main), ∀ v,
        TuplePrimeAt main i.val v → v = (singletonRepresentative (label main) i).1.val) →
      (∀ main ∈ F, main.length + n * s ≤ D) →
      (∀ main ∈ F, n * (s * J) < (singletonLabels (label main)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ main ∈ F, |prohibitedCenteredAverage data hB s D main (label main) (weight main)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_bounded_witness_decay Cs Cw hCs hCw,
    eventually_witnessRecordBudget Cs hCs] with L hdecay hbudgetScale
  intro h J M R B s n D K H Y data hB F label base weight cap A hA hcap hw hwcap hcost
    hdep hpadding hseen hlabelP hpairs hcover hposition hD hn hDL hJM
    hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
  let N := witnessRecordBudget D J M n
  have hbudget := hbudgetScale D J M n hDL hJM hnL
  have hDN : D ≤ N := by dsimp [N, witnessRecordBudget]; omega
  have hnN : n ≤ N := by dsimp [N, witnessRecordBudget]; omega
  have hslotsN (r : ℕ) (hr : r ≤ D) : r * (J + M) ≤ N :=
    witnessRecordBudget_slots D J M n r hr
  have hslots (r : ℕ) (_hr : r ≤ D) : ((r * (J + M) : ℕ) : ℝ) ≤ Cs * r * Real.log L := by
    have he := mul_le_mul_of_nonneg_left hJM (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    push_cast at he ⊢
    nlinarith
  have hmasked (main : List SignedStep) (hm : main ∈ F) (x : ↥(data.P ∪ data.Q) → Fin B) :
      paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (weight main) x =
        weight main x := by
    by_cases hx : weight main x = 0
    · simp [paddingWeightedFunction, hx]
    · simp [paddingWeightedFunction, hpadding main hm x hx]
  have hc := prohibited_singleton_words_le_catalog data B s n D F label
    (fun main => tupleForcedTarget data hB main (label main)) base weight cap A hA hB
    (fun main _ t => forcedResidue_lt B (label main t).val (data.prime _).pos
      (hB _ (label main t).property) (wordDisplacement h (main.take t.1.val)))
    hw hwcap hcap (by simpa only [Fintype.card_prod, Fintype.card_fin] using hcost)
    hdep hseen hlabelP hpairs hcover (fun main i => (singletonRepresentative (label main) i).1.val)
    hposition hD hn
  have hslotpoly (r : ℕ) (hr : r ≤ D) : ((r * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have he : ((r * (J + M) : ℕ) : ℝ) + 1 ≤ (N : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right (hslotsN r hr) 1
    exact he.trans hbudget
  have hDpoly : (D : ℝ) + 1 ≤ L ^ (2 : ℕ) := by
    have he : (D : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hDN 1
    exact he.trans hbudget
  have hb := hdecay D n K N h s J H Y (fun r => r * (J + M)) data.P data.Q
    (fun d q => (d, q) ∈ data.pairs) A hDL hDN hslots hslotpoly hDpoly
    (fun r hr => (hslotsN r hr).trans (Nat.le_succ _)) hnpos
    (hnN.trans (Nat.le_succ _)) hnL hbudget hKn hKlo hKhi data.primeP hmass hPmass hQmass
    hYpos hYexp hlo hhi hH hA hAexp
  have hleft : (∑ main ∈ F, |prohibitedCenteredAverage data hB s D main (label main) (weight main)|) =
      ∑ main ∈ F, |(data.residueLaw B hB).average (fun x =>
        paddingWeightedFunction (fun p : ↥(data.P ∪ data.Q) => p.val) h B main (weight main) x *
        (∏ t, ((if x (label main t) = tupleForcedTarget data hB main (label main) t
          then (1 : ℝ) else 0) - ((label main t).val : ℝ)⁻¹)) *
        attachedCatalogAvoidance data s B D main x)| := by
    apply sum_congr rfl
    intro main hm
    unfold prohibitedCenteredAverage
    simp_rw [hmasked main hm]
    congr 1
    exact uniform_weighted_divisor_word_average B _ (fun p => (data.prime p).pos)
      (fun p => hB _ p.property) (label main)
      (fun t => wordDisplacement h (main.take t.1.val)) (weight main)
      (attachedCatalogAvoidance data s B D main)
  rw [hleft]
  apply hc.trans
  convert (preTransparency := .instances) hb using 1
  simp only [mul_sum]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedNumericalSingletonDecay
namespace OAI

/-! Singleton decay on the same fixed-length numerical catalog as the other
trace classes.  The list encoding introduces no multiplicity. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_numerical_singleton_decay (Cs Cw : ℝ)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (F : Finset (Fin R → SignedStep))
      (label : (Fin R → SignedStep) → Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (Fin R → SignedStep) → (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (Fin R → SignedStep) → ℝ) (A : ℝ),
      0 ≤ A → (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) → (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, cap w * 2 ^ (R * J + (singletonLabels (label w)).card) ≤ A) →
      (∀ w ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label w) → x i = y i) → weight w x = weight w y) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B (List.ofFn w) x) →
      (∀ w ∈ F, ∀ i, ((w i).tuple, (w i).padding) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i, (w i).tuple.primeFactors = univ.image (fun j => (label w (i, j)).val)) →
      R + n * s ≤ D → (∀ w ∈ F, n * (s * J) < (singletonLabels (label w)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ w ∈ F, |prohibitedCenteredAverage data hB s D (List.ofFn w) (label w) (weight w)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_prohibited_singleton_decay Cs Cw hCs hCw] with L hdecay
  intro h J M R B s n D K H Y data hB F label base weight cap A hA hcap hweight hwcap hcost
    hdep hpadding hpairs hlabel hD hn hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass
    hYpos hYexp hlo hhi hH hAexp
  have : Nonempty (Fin R → SignedStep) := ⟨fun _ => ⟨true, 1, 1⟩⟩
  let decode : List SignedStep → Fin R → SignedStep := Function.invFun List.ofFn
  have hdecode (w : Fin R → SignedStep) : decode (List.ofFn w) = w :=
    Function.leftInverse_invFun List.ofFn_injective w
  let E := F.image List.ofFn
  have hpull (w : List SignedStep) (hw : w ∈ E) : ∃ v ∈ F, w = List.ofFn v := by
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    exact ⟨v, hv, rfl⟩
  have hb := hdecay h J M R B s n D K H Y data hB E (fun w => label (decode w)) base
    (fun w => weight (decode w)) (fun w => cap (decode w)) A hA
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcap v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hweight v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hwcap v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcost v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hdep v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hpadding v hv)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using
      numerical_label_seen data v (label v) (hpairs v hv) (hlabel v hv))
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using
      numerical_label_pool data v (label v) (hpairs v hv) (hlabel v hv))
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; exact numerical_word_pairs data v (hpairs v hv))
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using
      numerical_label_cover data v (label v) (hlabel v hv))
    (by
      intro w hw
      obtain ⟨v,hv,rfl⟩ := hpull w hw
      rw [hdecode]
      exact numerical_singleton_position data v (label v) (hpairs v hv) (hlabel v hv))
    (by intro w hw; obtain ⟨v,_,rfl⟩ := hpull w hw; simpa only [List.length_ofFn] using hD)
    (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hn v hv)
    hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
  simpa only [E, sum_image (fun _ _ _ _ he => List.ofFn_injective he), hdecode] using hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnSingletonDecay
namespace OAI

/-! The singleton estimate on the column/padding catalog used by the good
forest estimate.  Prime factorization proves that the encoding is injective. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_prohibited_column_singleton_decay_oai (Cs Cw : ℝ)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    ∀ᶠ L : ℝ in atTop, ∀ (h J M R B s n D K H Y : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (forward : Fin R → Bool)
      (F : Finset (ColumnPrimeAssignment J R P × (Fin R → Q)))
      (label : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        Fin R × Fin J → ↥(data.P ∪ data.Q))
      (_base : ↥(data.P ∪ data.Q) → Fin B)
      (weight : (ColumnPrimeAssignment J R P × (Fin R → Q)) →
        (↥(data.P ∪ data.Q) → Fin B) → ℝ)
      (cap : (ColumnPrimeAssignment J R P × (Fin R → Q)) → ℝ) (A : ℝ),
      (∀ j, ∀ p ∈ P j, p.Prime) →
      (∀ j l, l ≠ j → Disjoint (P j) (P l)) →
      0 ≤ A → (∀ w ∈ F, 0 ≤ cap w) →
      (∀ w ∈ F, ∀ x, 0 ≤ weight w x) → (∀ w ∈ F, ∀ x, weight w x ≤ cap w) →
      (∀ w ∈ F, cap w * 2 ^ (R * J + (singletonLabels (label w)).card) ≤ A) →
      (∀ w ∈ F, ∀ x y, (∀ i, i ∉ univ.image (label w) → x i = y i) → weight w x = weight w y) →
      (∀ w ∈ F, ∀ x, weight w x ≠ 0 → MainPaddingTests Subtype.val h B
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) x) →
      (∀ w ∈ F, ∀ i, (columnTuple w.1 i, (w.2 i).val) ∈ data.pairs) →
      (∀ w ∈ F, ∀ i j, (label w (i, j)).val = (w.1 j i).val) →
      R + n * s ≤ D → (∀ w ∈ F, n * (s * J) < (singletonLabels (label w)).card) →
      (D : ℝ) ≤ 4 * L → ((J + M : ℕ) : ℝ) ≤ Cs * Real.log L →
      0 < n → (n : ℝ) ≤ 4 * L → 8 * K ≤ n →
      L ^ (1 / 12 : ℝ) / 32 ≤ (K : ℝ) → (K : ℝ) ≤ L →
      1 ≤ primeHarmonicMass data.P →
      primeHarmonicMass data.P ≤ L ^ (2 : ℕ) → primeHarmonicMass data.Q ≤ L ^ (2 : ℕ) →
      1 ≤ Y → (Y : ℝ) ≤ Real.exp L →
      (∀ p ∈ data.P, H ≤ p) → (∀ p ∈ data.P, p ≤ Y) →
      Real.exp (L ^ (199 / 200 : ℝ)) ≤ H → A ≤ Real.exp (Cw * L * (Real.log L) ^ 2) →
      (∑ w ∈ F, |prohibitedCenteredAverage data hB s D
        (columnTupleWord w.1 forward (fun i => (w.2 i).val)) (label w) (weight w)|) ≤
        Real.exp (-L ^ (21 / 20 : ℝ)) := by
  filter_upwards [eventually_prohibited_numerical_singleton_decay Cs Cw hCs hCw] with L hdecay
  intro h J M R B s n D K H Y data hB P Q forward F label base weight cap A hprime hdisjoint
    hA hcap hweight hwcap hcost hdep hpadding hpairs hlabel hD hn hDL hJM hnpos hnL hKn
    hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
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
    have hb := hdecay h J M R B s n D K H Y data hB E (fun w => label (decode w)) base
      (fun w => weight (decode w)) (fun w => cap (decode w)) A hA
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hweight v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hwcap v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hcost v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hdep v hv)
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode, encode, columnStepCode_word] using hpadding v hv)
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
      hD
      (by intro w hw; obtain ⟨v,hv,rfl⟩ := hpull w hw; simpa only [hdecode] using hn v hv)
      hDL hJM hnpos hnL hKn hKlo hKhi hmass hPmass hQmass hYpos hYexp hlo hhi hH hAexp
    rw [show E = F.image encode from rfl, sum_image (fun _ _ _ _ he => hinj he)] at hb
    simpa only [hdecode, encode, columnStepCode_word] using hb
  · rw [not_nonempty_iff_eq_empty.mp hF, sum_empty]
    exact (Real.exp_pos _).le

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.eventually_prohibited_column_singleton_decay_oai := @OAI.TwoPointCorrelations.eventually_prohibited_column_singleton_decay_oai
