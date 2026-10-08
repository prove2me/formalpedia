-- Prove2me | solution 1 for OAI.TwoPointCorrelations.eventually_actual_matrix_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T03:18:26.353646+00:00
-- url     : https://prove2.me/submissions/087dc9c3-7fc2-48bd-99c0-11ae906640e7

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs
import Theorems.Thm_OAI_TwoPointCorrelations_eventually_prohibited_column_trace_total
import Theorems.Thm_OAI_TwoPointCorrelations_matrix_residue_trace_of_column_bounds

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.CrudeTraceWeights
namespace OAI

/-! Padding, mixed-difference, and external factors in the crude trace count. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma crudePaddingWeight_exp_bound (q : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hq : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    crudePaddingWeight q ≤ Real.exp (200 * Real.log L) := by
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using congrArg Real.log
        (show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num)
    linarith
  have hp : (q.primeFactors.card : ℝ) * Real.log 4 ≤ 200 * Real.log L := by
    calc
      _ ≤ (100 * Real.log L) * Real.log 4 :=
        mul_le_mul_of_nonneg_right hq (Real.log_nonneg (by norm_num))
      _ ≤ (100 * Real.log L) * 2 :=
        mul_le_mul_of_nonneg_left hlog4 (by positivity)
      _ = _ := by ring
  unfold crudePaddingWeight
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr hp

lemma crudePaddingFactors_exp_bound (R : ℕ) (q : Fin R → ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hq : ∀ i, ((q i).primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    (∏ i, L * crudePaddingWeight (q i)) ≤ Real.exp (201 * R * Real.log L) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hi (i : Fin R) : L * crudePaddingWeight (q i) ≤
      Real.exp (201 * Real.log L) := by
    calc
      _ ≤ L * Real.exp (200 * Real.log L) :=
        mul_le_mul_of_nonneg_left (crudePaddingWeight_exp_bound (q i) L hL (hq i)) hLp.le
      _ = Real.exp (201 * Real.log L) := by
        conv_lhs => lhs; rw [← Real.exp_log hLp]
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    _ ≤ ∏ _i : Fin R, Real.exp (201 * Real.log L) :=
      Finset.prod_le_prod (fun _ _ => by unfold crudePaddingWeight; positivity) (fun i _ => hi i)
    _ = Real.exp (201 * R * Real.log L) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      congr 1
      ring



/-- Fixed exponential dimension factors and all step weights are
absorbed by an explicit `L log² L` cost. -/
theorem crudeTraceWeight_exp_bound (R S : ℕ) (q : Fin R → ℕ)
    (L external Cexternal Csingle : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hR : (R : ℝ) ≤ 2 * L) (hS : (S : ℝ) ≤ Csingle * L * Real.log L)
    (hCexternal : 0 ≤ Cexternal)
    (hext : external ≤ Real.exp (Cexternal * L))
    (hq : ∀ i, ((q i).primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    crudeTraceWeight R S q L external ≤
      Real.exp ((Cexternal + Csingle + 402) * L * (Real.log L) ^ 2) := by
  have hpad := crudePaddingFactors_exp_bound R q L hL hq
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have htwo : (2 : ℝ) ^ S ≤ Real.exp (Csingle * L * (Real.log L) ^ 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hSpos : 0 ≤ Csingle * L * Real.log L := (Nat.cast_nonneg S).trans hS
    calc
      _ ≤ (S : ℝ) := by nlinarith
      _ ≤ Csingle * L * Real.log L := hS
      _ ≤ Csingle * L * (Real.log L) ^ 2 := by
        have ht := mul_le_mul_of_nonneg_left hlog hSpos
        nlinarith
  have hext' : external ≤ Real.exp (Cexternal * L * (Real.log L) ^ 2) := by
    apply hext.trans
    apply Real.exp_le_exp.mpr
    have ht : 1 ≤ (Real.log L) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ Cexternal * L by positivity)]
  have hpad' : (∏ i, L * crudePaddingWeight (q i)) ≤
      Real.exp (402 * L * (Real.log L) ^ 2) := by
    apply hpad.trans
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right hR (show 0 ≤ 201 * Real.log L by linarith)
    have hu := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 402 * L * Real.log L by positivity)
    nlinarith
  unfold crudeTraceWeight
  calc
    _ ≤ Real.exp (Cexternal * L * (Real.log L) ^ 2) *
        Real.exp (Csingle * L * (Real.log L) ^ 2) *
        Real.exp (402 * L * (Real.log L) ^ 2) := by
      apply mul_le_mul _ hpad' (by unfold crudePaddingWeight; positivity) (by positivity)
      exact mul_le_mul hext' htwo (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftMatrixWords
namespace OAI

/-! Expand finite shift matrices using step labels, without enumerating intermediate sites. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {V E S : Type*} [Fintype V] [DecidableEq V] [Fintype E]



omit [DecidableEq V] [Fintype E] in
lemma retainedShiftWeight_nonzero (embed : V → S) (next : E → S → S)
    (weight : E → S → ℝ) (e : E) (x : S)
    (hw : retainedShiftWeight embed next weight e x ≠ 0) :
    next e x ∈ Set.range embed ∧ weight e x ≠ 0 := by
  classical
  unfold retainedShiftWeight at hw
  split_ifs at hw with he
  · exact ⟨he, hw⟩
  · contradiction












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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ShiftedIntegerPaths
namespace OAI

/-! Arithmetic translation leaves the physical copy and block gates fixed. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*}



variable [Fintype V] [DecidableEq D]

lemma retained_physicalShiftWeight (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) (e : D × (Q × Bool)) (x : D × ℤ) :
    retainedShiftWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) e x =
      integerStepMask embed Q tuple h gate e x *
        weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 := by
  by_cases hc : x.1 ≠ e.1
  · by_cases hg : gate e.1 x.2 (integerShiftNext Q tuple h e x).2
    · by_cases hr : integerShiftNext Q tuple h e x ∈ Set.range embed
      · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc, hg, hr]
      · simp [retainedShiftWeight, integerStepMask, hr]
    · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc, hg]
  · simp [retainedShiftWeight, physicalShiftWeight, integerStepMask, hc]

theorem physicalShiftWord_product (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool)) :
    shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w =
      integerPathMask embed Q tuple h gate x w *
        scalarWalkProduct h weight x.2 (integerStepWord Q tuple w) := by
  induction k generalizing x with
  | zero => simp [shiftWordWeight, integerPathMask, integerStepWord, scalarWalkProduct]
  | succ k ih =>
      rw [shiftWordWeight, retained_physicalShiftWeight, ih]
      simp only [integerPathMask, integerStepWord, List.ofFn_succ, List.map_cons, scalarWalkProduct]
      dsimp only [integerShiftNext, Fin.tail_def]
      ring





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

lemma wordDisplacement_take (h : ℕ) (w : List SignedStep) (n : ℕ) :
    wordDisplacement h (w.take n) = ∑ i ∈ range n, wordStepDisplacement h w i := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
      cases w with
      | nil => simp
      | cons a w =>
          rw [List.take_succ_cons, wordDisplacement_cons, Finset.sum_range_succ']
          simp only [wordStepDisplacement_cons_zero, wordStepDisplacement_cons_succ, ih]
          ring











end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ReversedSegments
namespace OAI

/-! Reversed prohibited subwords used in the active-label descent. -/

namespace TwoPointCorrelations






lemma reverseWord_chain {w : List SignedStep}
    (hw : w.IsChain (fun a b => a.tuple ≠ b.tuple)) :
    (reverseWord w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  rw [List.isChain_iff_getElem] at hw ⊢
  intro i hi
  have hi' : i + 1 < w.length := by simpa using hi
  have h := hw (w.length - 2 - i) (by omega)
  have heq : w.length - 2 - i + 1 = w.length - 1 - i := by omega
  simp only [reverseWord, List.getElem_map, List.getElem_reverse,
    SignedStep.flip] at *
  simpa only [heq, show w.length - 1 - (i + 1) = w.length - 2 - i by omega] using h.symm


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.PhysicalPathSupport
namespace OAI

/-! The numerical support of a nonzero translated matrix path. -/

namespace TwoPointCorrelations

open scoped _root_.Classical

variable {D V : Type*} [DecidableEq D] [Fintype V]

lemma physicalShiftWeight_nonzero (Q : Finset ℕ) (tuple : D → ℕ) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ)
    (e : D × (Q × Bool)) (x : D × ℤ)
    (he : physicalShiftWeight Q tuple h gate weight e x ≠ 0) :
    x.1 ≠ e.1 ∧ weight ⟨e.2.2, tuple e.1, e.2.1⟩ x.2 ≠ 0 := by
  unfold physicalShiftWeight at he
  split_ifs at he with hc
  · exact ⟨hc.1, he⟩
  · contradiction

lemma physicalShiftWord_copy_chain (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (h : ℕ) (gate : D → ℤ → ℤ → Prop)
    (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w ≠ 0) :
    (x.1 :: (List.ofFn w).map Prod.fst).IsChain (fun a b => a ≠ b) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      have hp := mul_ne_zero_iff.mp hw
      have he := (retainedShiftWeight_nonzero _ _ _ _ _ hp.1).2
      have hc := (physicalShiftWeight_nonzero Q tuple h gate weight (w 0) x he).1
      have ht := ih (integerShiftNext Q tuple h (w 0) x) (Fin.tail w) hp.2
      simp only [List.ofFn_succ, List.map_cons]
      exact ht.cons_cons hc

theorem physicalShiftWord_tuple_chain (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (hinj : Function.Injective tuple) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) (weight : SignedStep → ℤ → ℝ) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : shiftWordWeight embed (integerShiftNext Q tuple h)
      (physicalShiftWeight Q tuple h gate weight) x w ≠ 0) :
    (integerStepWord Q tuple w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  have hc := (physicalShiftWord_copy_chain embed Q tuple h gate weight x w hw).tail
  have hs := (List.isChain_map Prod.fst).mp hc
  apply (List.isChain_map (fun e : D × (Q × Bool) =>
    SignedStep.mk e.2.2 (tuple e.1) e.2.1.val)).mpr
  exact hs.imp (fun _ _ hne he => hne (hinj he))


lemma scalarWalkProduct_one (h : ℕ) (n : ℤ) (w : List SignedStep) :
    scalarWalkProduct h (fun _ _ => 1) n w = 1 := by
  induction w generalizing n with
  | nil => rfl
  | cons t w ih => simp only [scalarWalkProduct, ih, one_mul]

theorem integerPathMask_tuple_chain (embed : V → D × ℤ) (Q : Finset ℕ)
    (tuple : D → ℕ) (hinj : Function.Injective tuple) (h : ℕ)
    (gate : D → ℤ → ℤ → Prop) {k : ℕ}
    (x : D × ℤ) (w : Fin k → D × (Q × Bool))
    (hw : integerPathMask embed Q tuple h gate x w ≠ 0) :
    (integerStepWord Q tuple w).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  apply physicalShiftWord_tuple_chain embed Q tuple hinj h gate (fun _ _ => 1) x w
  rw [physicalShiftWord_product, scalarWalkProduct_one, mul_one]
  exact hw

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.SingletonDecay
namespace OAI

/-! The selected singleton savings dominate the complete crude trace cost. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_singleton_floor_bounds :
    ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 12 : ℝ) / 32 ≤ ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ∧
        ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ≤ L := by
  have hr := (tendsto_rpow_atTop (show 0 < (1 / 12 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 32)
  filter_upwards [eventually_ge_atTop 1, hr] with L hL hpow
  have hf := Nat.lt_floor_add_one (L ^ (1 / 12 : ℝ))
  have hd : ⌊L ^ (1 / 12 : ℝ)⌋₊ < 8 * (⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 + 1) := by
    have he := Nat.mod_add_div ⌊L ^ (1 / 12 : ℝ)⌋₊ 8
    have hm := Nat.mod_lt ⌊L ^ (1 / 12 : ℝ)⌋₊ (show 0 < 8 by decide)
    omega
  have hd' : (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) <
      8 * ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) + 8 := by exact_mod_cast hd
  constructor
  · linarith
  · apply (show ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ≤
        (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) by exact_mod_cast Nat.div_le_self _ 8).trans
    apply (Nat.floor_le (Real.rpow_nonneg (by linarith) _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le hL (show (1 / 12 : ℝ) ≤ 1 by norm_num)





end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.WitnessScaleParameters
namespace OAI

/-! The actual singleton threshold supplies enough short witnesses within the trace length budget. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_witness_cover_budget (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s J S R : ℕ),
      (s : ℝ) ≤ L ^ (1 / 10 : ℝ) → (J : ℝ) ≤ C * Real.log L →
      L ^ (1 / 4 : ℝ) < S → (R : ℝ) ≤ 2 * L →
      ⌊L ^ (1 / 12 : ℝ)⌋₊ * (s * J) < S ∧
      ((R + ⌊L ^ (1 / 12 : ℝ)⌋₊ * s : ℕ) : ℝ) ≤ 4 * L := by
  have hsmall := (isLittleO_log_rpow_atTop (show 0 < (1 / 15 : ℝ) by norm_num)).bound
    (show 0 < 1 / (2 * (C + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hsmall] with L hL hslog
  intro s J S R hs hJ hS hR
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, abs_of_nonneg hlog, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hslog
  have hslog' : Real.log L ≤ L ^ (1 / 15 : ℝ) / (2 * (C + 1)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hslog
  have hlogmul := (le_div_iff₀ (show 0 < 2 * (C + 1) by positivity)).mp hslog'
  have hcoeff : C * Real.log L < L ^ (1 / 15 : ℝ) := by
    have hp := Real.rpow_pos_of_pos hLp (1 / 15 : ℝ)
    nlinarith
  have hT : (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) ≤ L ^ (1 / 12 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hLp.le _)
  have hTs : ((⌊L ^ (1 / 12 : ℝ)⌋₊ * s : ℕ) : ℝ) ≤ L ^ (11 / 60 : ℝ) := by
    push_cast
    calc
      _ ≤ L ^ (1 / 12 : ℝ) * L ^ (1 / 10 : ℝ) :=
        mul_le_mul hT hs (by positivity) (by positivity)
      _ = _ := by rw [← Real.rpow_add hLp]; norm_num
  have hcover : ((⌊L ^ (1 / 12 : ℝ)⌋₊ * (s * J) : ℕ) : ℝ) < S := by
    calc
      _ = ((⌊L ^ (1 / 12 : ℝ)⌋₊ * s : ℕ) : ℝ) * J := by push_cast; ring
      _ ≤ L ^ (11 / 60 : ℝ) * (C * Real.log L) :=
        mul_le_mul hTs hJ (by positivity) (by positivity)
      _ < L ^ (11 / 60 : ℝ) * L ^ (1 / 15 : ℝ) :=
        mul_lt_mul_of_pos_left hcoeff (Real.rpow_pos_of_pos hLp _)
      _ = L ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hLp]; norm_num
      _ < S := hS
  refine ⟨by exact_mod_cast hcover, ?_⟩
  have hpow : L ^ (11 / 60 : ℝ) ≤ L := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (show (11 / 60 : ℝ) ≤ 1 by norm_num)
  push_cast at hTs ⊢
  linarith

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceParameterBudget
namespace OAI

/-! Elementary bounds for the actual trace and witness lengths. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_trace_slot_budgets (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ k J M : ℕ,
      (k : ℝ) ≤ L → (J + M : ℕ) ≤ C * Real.log L →
      ((⌊L ^ (1 / 4 : ℝ)⌋₊ + 2 * k * J : ℕ) : ℝ) ≤
          (2 * C + 1) * L * Real.log L ∧
      ((2 * k * (J + M) : ℕ) : ℝ) + 1 ≤ L ^ 2 ∧
      ((2 * k : ℕ) : ℝ) + 1 ≤ L ^ 2 := by
  have hs := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).bound
    (show 0 < 1 / (4 * (C + 1)) by positivity)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1), hs] with L hL hlog hs
  intro k J M hk hJM
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Real.log L),
    Real.norm_eq_abs, Real.rpow_one, abs_of_pos hLp] at hs
  have hs' : 4 * (C + 1) * Real.log L ≤ L := by
    have ht : Real.log L ≤ L / (4 * (C + 1)) := by
      simpa only [div_eq_mul_inv, one_mul, mul_comm] using hs
    have ht' := (le_div_iff₀ (show 0 < 4 * (C + 1) by positivity)).mp ht
    nlinarith
  have hJ : (J : ℝ) ≤ C * Real.log L := by
    exact (show (J : ℝ) ≤ (J + M : ℕ) by exact_mod_cast Nat.le_add_right J M).trans hJM
  have hf : (⌊L ^ (1 / 4 : ℝ)⌋₊ : ℝ) ≤ L := by
    apply (Nat.floor_le (Real.rpow_nonneg hLp.le _)).trans
    simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L)
      (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hprod : (2 * k * J : ℕ) ≤ 2 * L * (C * Real.log L) := by
    push_cast
    exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hJ
      (by positivity) (by positivity)
  have hprod' : (2 * k * (J + M) : ℕ) ≤ 2 * L * (C * Real.log L) := by
    push_cast at hJM ⊢
    exact mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hJM
      (by positivity) (by positivity)
  have hCL : C * Real.log L ≤ L / 4 := by nlinarith
  have hlogL : L ≤ L * Real.log L := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hCL (show 0 ≤ 2 * L by positivity)
    nlinarith
  · push_cast
    nlinarith

lemma eventually_trace_witness_budgets (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      L / 2 ≤ (⌊L⌋₊ : ℝ) ∧ (⌊L⌋₊ : ℝ) ≤ L ∧
      0 < ⌊L ^ (1 / 10 : ℝ)⌋₊ ∧
      L ^ (1 / 10 : ℝ) / 2 ≤ (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) ∧
      0 < ⌊L ^ (1 / 12 : ℝ)⌋₊ ∧
      (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) ≤ 4 * L ∧
      8 * (⌊L ^ (1 / 12 : ℝ)⌋₊ / 8) ≤ ⌊L ^ (1 / 12 : ℝ)⌋₊ ∧
      L ^ (1 / 12 : ℝ) / 32 ≤ ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ∧
      ((⌊L ^ (1 / 12 : ℝ)⌋₊ / 8 : ℕ) : ℝ) ≤ L ∧
      ((2 * ⌊L⌋₊ + ⌊L ^ (1 / 12 : ℝ)⌋₊ * ⌊L ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) ≤ 4 * L ∧
      ∀ J S : ℕ, (J : ℝ) ≤ C * Real.log L → ⌊L ^ (1 / 4 : ℝ)⌋₊ < S →
        ⌊L ^ (1 / 12 : ℝ)⌋₊ * (⌊L ^ (1 / 10 : ℝ)⌋₊ * J) < S := by
  have hs := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 10 by norm_num)).eventually
    (eventually_ge_atTop 2)
  have hn := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 12 by norm_num)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop (2 : ℝ), hs, hn,
    eventually_singleton_floor_bounds, eventually_witness_cover_budget C hC] with
    L hL hs hn hfloor hcover
  have hLp : 0 < L := by linarith
  have hk : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hLp.le
  have hklo : L / 2 ≤ (⌊L⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one L
    linarith
  have hslo : L ^ (1 / 10 : ℝ) / 2 ≤ (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) := by
    have ht := Nat.lt_floor_add_one (L ^ (1 / 10 : ℝ))
    linarith
  have hspos : 0 < ⌊L ^ (1 / 10 : ℝ)⌋₊ := by
    have ht : (0 : ℝ) < (⌊L ^ (1 / 10 : ℝ)⌋₊ : ℝ) := by linarith
    exact_mod_cast ht
  have hnpos : 0 < ⌊L ^ (1 / 12 : ℝ)⌋₊ := by
    have ht := Nat.lt_floor_add_one (L ^ (1 / 12 : ℝ))
    have hp : (0 : ℝ) < (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) := by linarith
    exact_mod_cast hp
  have hnhi : (⌊L ^ (1 / 12 : ℝ)⌋₊ : ℝ) ≤ 4 * L := by
    have hp : L ^ (1 / 12 : ℝ) ≤ L := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L)
        (show (1 / 12 : ℝ) ≤ 1 by norm_num)
    have ht := Nat.floor_le (Real.rpow_nonneg hLp.le (1 / 12 : ℝ))
    linarith
  have hsbound := Nat.floor_le (Real.rpow_nonneg hLp.le (1 / 10 : ℝ))
  have hR : ((2 * ⌊L⌋₊ : ℕ) : ℝ) ≤ 2 * L := by push_cast; linarith
  have hD := (hcover ⌊L ^ (1 / 10 : ℝ)⌋₊ 0 (⌊L ^ (1 / 4 : ℝ)⌋₊ + 1)
    (2 * ⌊L⌋₊) hsbound (by simpa using mul_nonneg hC (Real.log_nonneg (by linarith)))
    (by simpa using Nat.lt_floor_add_one (L ^ (1 / 4 : ℝ))) hR).2
  refine ⟨hklo, hk, hspos, hslo, hnpos, hnhi, Nat.mul_div_le _ _,
    hfloor.1, hfloor.2, hD, ?_⟩
  intro J S hJ hS
  apply (hcover _ J S _ hsbound hJ _ hR).1
  exact (Nat.floor_lt (Real.rpow_nonneg hLp.le _)).mp hS

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.TraceErrorAbsorption
namespace OAI

/-! The three exceptional trace classes are absorbed by an absolute change
of the square-root harmonic-mass constant. -/

namespace TwoPointCorrelations

open _root_.Filter

lemma eventually_trace_exceptional_cost :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) ≤ 1 := by
  have hgrow := (tendsto_rpow_atTop (show 0 < (1 / 100 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 110)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hgrow] with L hL hgrow
  have hLp : 0 < L := by linarith
  have hpower : L * L ^ (1 / 100 : ℝ) = L ^ (101 / 100 : ℝ) := by
    rw [show (101 / 100 : ℝ) = 1 + 1 / 100 by norm_num,
      Real.rpow_add hLp, Real.rpow_one]
  have hlarge : 110 * L ≤ L ^ (101 / 100 : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left hgrow hLp.le
    rw [hpower] at hb
    linarith
  have hs : Real.exp (-L ^ (21 / 20 : ℝ)) ≤ Real.exp (-L ^ (101 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  have hthree : (3 : ℝ) ≤ Real.exp (2 * L) := by
    apply le_trans (show (3 : ℝ) ≤ Real.exp 2 by linarith [Real.add_one_le_exp (2 : ℝ)])
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (108 * L) * (Real.exp (-L ^ (101 / 100 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hs le_rfl) (Real.exp_pos _).le
    _ = 3 * Real.exp (108 * L - L ^ (101 / 100 : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ 3 * Real.exp (-(2 * L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ Real.exp (2 * L) * Real.exp (-(2 * L)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma trace_base_double_absorbs_one (J k : ℕ) (K W : ℝ)
    (hJ : 1 ≤ J) (hk : 1 ≤ k) (hK : 1 ≤ K) (hW : 1 ≤ W) :
    1 + (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) ≤
      (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  let b := Real.exp 150 * Real.sqrt W
  have hb : 1 ≤ b := by
    have he : (1 : ℝ) ≤ Real.exp 150 := Real.one_le_exp (by norm_num)
    have hw : (1 : ℝ) ≤ Real.sqrt W := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hW
    exact one_le_mul_of_one_le_of_one_le he hw
  have hA : 1 ≤ (K * b ^ J) ^ (2 * k) :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hb))
  have ht : 2 ≤ (2 : ℝ) ^ (J * (2 * k)) := by
    have hn : 1 ≤ J * (2 * k) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hn
  calc
    _ = 1 + (K * b ^ J) ^ (2 * k) := rfl
    _ ≤ 2 * (K * b ^ J) ^ (2 * k) := by linarith
    _ ≤ 2 ^ (J * (2 * k)) * (K * b ^ J) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
      rw [pow_mul, ← mul_pow]
      congr 1
      dsimp [b]
      simp only [mul_pow]
      ring

theorem eventually_trace_absorption :
    ∀ᶠ L : ℝ in atTop, ∀ (J k : ℕ) (K W M : ℝ),
      1 ≤ J → 1 ≤ k → 1 ≤ K → 1 ≤ W →
      M ≤ Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) +
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) →
      M ≤ (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_trace_exceptional_cost] with L herr
  intro J k K W M hJ hk hK hW hM
  exact (hM.trans (add_le_add herr le_rfl)).trans (trace_base_double_absorbs_one J k K W hJ hk hK hW)

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




theorem residueValue_independent_tuple {h J M B : ℕ} {τ : Type*} [Fintype τ]
    (data : ProhibitedPrimeFamily h J M) (label : τ → ↥(data.P ∪ data.Q))
    (hlabel : ∀ p ∈ univ.image label, p.val ∈ data.P)
    (f : ℤ → ℝ)
    (hf : ∀ n m : ℤ, (∀ q ∈ data.Q, (n : ZMod q) = (m : ZMod q)) → f n = f m)
    (x y : ↥(data.P ∪ data.Q) → Fin B)
    (hxy : ∀ p, p ∉ univ.image label → x p = y p) :
    data.residueValue f x = data.residueValue f y := by
  apply hf
  intro q hq
  let p : ↥(data.P ∪ data.Q) := ⟨q, mem_union_right _ hq⟩
  have hp : p ∉ univ.image label := by
    intro hp
    exact disjoint_left.mp data.disjoint (hlabel p hp) hq
  rw [data.residueOrigin_spec x p, data.residueOrigin_spec y p, hxy p hp]

end TwoPointCorrelations.ProhibitedPrimeFamily

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualPaddingProduct
namespace OAI

/-! Identify recursive padding weights with the literal product at the numerical departures. -/

namespace TwoPointCorrelations

open _root_.Finset

theorem paddingWordWeight_eq_prod_sites (Q : Finset ℕ)
    (weight : ℕ → ℤ → ℕ → ℝ) (next : ℕ → ℤ → ℕ → ℤ)
    {m : ℕ} (i : ℕ) (n : ℤ) (q : Fin m → Q) (site : Fin (m + 1) → ℤ)
    (hzero : site 0 = n)
    (hstep : ∀ t : Fin m, site t.succ = next (i + t.val) (site t.castSucc) (q t).val) :
    paddingWordWeight Q weight next i n q =
      ∏ t : Fin m, weight (i + t.val) (site t.castSucc) (q t).val := by
  induction m generalizing i n with
  | zero => simp [paddingWordWeight]
  | succ m ih =>
      rw [paddingWordWeight, Fin.prod_univ_succ]
      have hz : site (Fin.succ 0) = next i n (q 0).val := by
        simpa only [Fin.val_zero, Nat.add_zero, Fin.castSucc_zero, hzero] using hstep 0
      have hs : ∀ t : Fin m, (fun u : Fin (m + 1) => site u.succ) t.succ =
          next (i + 1 + t.val) ((fun u : Fin (m + 1) => site u.succ) t.castSucc)
            ((Fin.tail q) t).val := by
        intro t
        simpa only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 t.val,
          Fin.succ_castSucc, Fin.tail] using hstep t.succ
      rw [ih (i + 1) _ (Fin.tail q) (fun u => site u.succ) hz hs]
      simp only [Fin.val_zero, Nat.add_zero, Fin.castSucc_zero, hzero]
      congr 1
      apply prod_congr rfl
      intro t _
      simp only [Fin.val_succ, Nat.add_assoc, Nat.add_comm 1 t.val,
        Fin.succ_castSucc, Fin.tail]

lemma wordDisplacement_take_succ (h : ℕ) (word : List SignedStep) (t : ℕ) :
    wordDisplacement h (word.take (t + 1)) =
      wordDisplacement h (word.take t) + wordStepDisplacement h word t := by
  simp only [wordDisplacement_take, sum_range_succ]

theorem paddingWordWeight_eq_departure_product {Q : Finset ℕ} {m : ℕ}
    (h : ℕ) (step : Fin m → SignedStep) (q : Fin m → Q)
    (weight : ℕ → ℤ → ℕ → ℝ) (next : ℕ → ℤ → ℕ → ℤ) (n : ℤ)
    (hnext : ∀ t : Fin m, ∀ z, next t.val z (q t).val = z + (step t).displacement h) :
    paddingWordWeight Q weight next 0 n q =
      ∏ t : Fin m, weight t.val
        (n + wordDisplacement h ((List.ofFn step).take t.val)) (q t).val := by
  let site (t : Fin (m + 1)) := n + wordDisplacement h ((List.ofFn step).take t.val)
  have hz : site 0 = n := by simp [site]
  have hs (t : Fin m) : site t.succ = next (0 + t.val) (site t.castSucc) (q t).val := by
    rw [Nat.zero_add, hnext]
    simp only [site, Fin.val_succ, Fin.val_castSucc, wordDisplacement_take_succ]
    have ht : wordStepDisplacement h (List.ofFn step) t.val = (step t).displacement h := by
      simp only [wordStepDisplacement, List.getElem?_ofFn, t.isLt, dite_true, Fin.eta,
        Option.map_some, Option.getD_some]
    rw [ht, add_assoc]
  simpa only [Nat.zero_add, site, Fin.val_castSucc] using
    paddingWordWeight_eq_prod_sites Q weight next 0 n q site hz hs

theorem retainedColumnPaddingWeight_eq_departure_product {J k : ℕ}
    {P : Fin J → Finset ℕ} (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ColumnPrimeAssignment J (2 * k) P → ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ)
    (extra : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → Prop)
    (next : ColumnPrimeAssignment J (2 * k) P → ℕ → ℤ → ℕ → ℤ)
    (h : ℕ) (n : ℤ) (w : ColumnPrimeAssignment J (2 * k) P)
    (forward : Fin (2 * k) → Bool) (q : Fin (2 * k) → Q)
    (hnext : ∀ i : Fin (2 * k), ∀ z, next w i.val z (q i).val =
      z + (SignedStep.mk (forward i) (columnTuple w i) (q i).val).displacement h) :
    retainedColumnPaddingWeight Q u eligible g L K extra next n w q =
      ∏ i : Fin (2 * k), retainedPaddingAtom Q u (eligible w i.val) g L K (extra w i.val)
        (n + wordDisplacement h ((columnTupleWord w forward (fun i => (q i).val)).take i.val))
        (q i).val := by
  exact paddingWordWeight_eq_departure_product h
    (fun i => SignedStep.mk (forward i) (columnTuple w i) (q i).val) q
    (fun i z r => retainedPaddingAtom Q u (eligible w i) g L K (extra w i) z r)
    (next w) n hnext

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedWordPadding
namespace OAI

/-! Separate the actual closed matrix word into centered factors and its retained padding weight. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma retainedEdgeDeparture_nonneg (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (t : SignedStep) (n : ℤ) :
    0 ≤ retainedEdgeDeparture Q u eligible g L K extra h t n := by
  unfold retainedEdgeDeparture
  split_ifs
  · exact div_nonneg (mul_nonneg hL (hu _)) (sq_nonneg _)
  · exact le_rfl

lemma retainedEdgeDeparture_le_atom (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (t : SignedStep) (n : ℤ) :
    retainedEdgeDeparture Q u eligible g L K extra h t n ≤
      retainedPaddingAtom Q u (eligible t) g L K (extra t) n t.padding := by
  unfold retainedEdgeDeparture
  split_ifs with ht
  · have hs : eligible t t.padding ∧ (t.padding : ℤ) ∣ n ∧
        integerEdgeKeep Q u (eligible t) g L K (extra t) n :=
      ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1⟩
    simp only [retainedPaddingAtom, if_pos hs, le_refl]
  · exact retainedPaddingAtom_nonneg Q u (eligible t) g L K (extra t) n t.padding hL (hu _)


lemma scalarWalkProduct_nonneg (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (hw : ∀ t n, 0 ≤ weight t n) (n : ℤ) (word : List SignedStep) :
    0 ≤ scalarWalkProduct h weight n word := by
  induction word generalizing n with
  | nil => exact zero_le_one
  | cons t word ih => exact mul_nonneg (hw t n) (ih _)



theorem scalarWalkProduct_ofFn {m : ℕ} (h : ℕ) (weight : SignedStep → ℤ → ℝ)
    (step : Fin m → SignedStep) (n : ℤ) :
    scalarWalkProduct h weight n (List.ofFn step) =
      ∏ i : Fin m, weight (step i) (n + wordDisplacement h ((List.ofFn step).take i.val)) := by
  induction m generalizing n with
  | zero => simp [scalarWalkProduct]
  | succ m ih =>
      rw [List.ofFn_succ, scalarWalkProduct, ih, Fin.prod_univ_succ]
      simp only [Fin.val_zero, List.take_zero, wordDisplacement_nil, add_zero]
      congr 1
      apply prod_congr rfl
      intro i _
      simp only [Fin.val_succ, List.take_succ_cons, wordDisplacement_cons,
        add_assoc]

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
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnClosedEncoding
namespace OAI

/-! Recover the column data of the actual joined matrix paths. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma ofFn_rev_eq_reverse {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega


lemma closedColumnRows_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    integerStepWord Q (fun d => ∏ j, (d j).val) (closedColumnRows Q a b) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b) := by
  unfold integerStepWord closedColumnRows integerClosedWordCode
  rw [List.ofFn_fin_append, List.map_append]
  congr 1
  rw [reverseWord]
  simp only [integerStepWord, List.map_reverse, List.map_ofFn, Function.comp_def]
  rw [← ofFn_rev_eq_reverse]
  simp only [SignedStep.flip]




theorem closedColumn_encoding_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    columnTupleWord (closedColumnAssignment Q a b) (closedColumnForward Q a b)
      (fun i => (closedColumnPadding Q a b i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b) := by
  rw [← closedColumnRows_word]
  simp only [columnTupleWord, columnTuple, closedColumnAssignment, closedColumnForward,
    closedColumnPadding, integerStepWord, List.map_ofFn, Function.comp_def]

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedTraceEncoding
namespace OAI

/-! The actual closed-pair catalog has length `2*k`, as in the trace bounds. -/

namespace TwoPointCorrelations

open _root_.Finset

lemma columnTupleWord_reindex {J R S : ℕ} {P : Fin J → Finset ℕ}
    (he : R = S) (w : ColumnPrimeAssignment J R P)
    (forward : Fin R → Bool) (padding : Fin R → ℕ) :
    columnTupleWord (fun j i => w j (Fin.cast he.symm i))
      (fun i => forward (Fin.cast he.symm i)) (fun i => padding (Fin.cast he.symm i)) =
      columnTupleWord w forward padding := by
  subst S
  rfl


theorem closedTraceEncoding_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (p : (Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool))) :
    columnTupleWord (closedTraceEncoding Q p).2.1 (closedTraceEncoding Q p).1
      (fun i => ((closedTraceEncoding Q p).2.2 i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) p := by
  dsimp only [closedTraceEncoding]
  exact (columnTupleWord_reindex (show k + k = 2 * k by omega)
    (closedColumnAssignment Q p.1 p.2) (closedColumnForward Q p.1 p.2)
    (fun i => (closedColumnPadding Q p.1 p.2 i).val)).trans
      (closedColumn_encoding_word Q p.1 p.2)


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ClosedTraceSummation
namespace OAI

/-! Partition the actual path-pair catalog by its signs without multiplicity loss. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma mem_closedTraceFiber {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :
    a ∈ closedTraceFiber Q F forward ↔
      ∃ p ∈ F, (closedTraceEncoding Q p).1 = forward ∧ (closedTraceEncoding Q p).2 = a := by
  simp only [closedTraceFiber, mem_image, mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hf⟩, ha⟩
    exact ⟨p, hp, hf, ha⟩
  · rintro ⟨p, hp, hf, ha⟩
    exact ⟨p, ⟨hp, hf⟩, ha⟩

lemma closedTraceFiber_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (F : Finset ((Fin k → ((j : Fin J) → P j) × (Q × Bool)) ×
      (Fin k → ((j : Fin J) → P j) × (Q × Bool)))) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q F forward) :
    ∃ p ∈ F, columnTupleWord a.1 forward (fun i => (a.2 i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) p := by
  obtain ⟨p, hp, hf, he⟩ := (mem_closedTraceFiber Q F forward a).mp ha
  refine ⟨p, hp, ?_⟩
  simpa only [hf, he] using closedTraceEncoding_word Q p


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ProhibitedWeightSupport
namespace OAI

/-! Positivity, crude size and retained divisibility of the actual departure weights. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma retainedEdgeDeparture_le_crude (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ) (hL : 0 ≤ L)
    (hu : ∀ q, 0 ≤ u q) (hub : ∀ q, u q ≤ crudePaddingWeight q)
    (hg : ∀ n, 1 ≤ (g n) ^ 2) (t : SignedStep) (n : ℤ) :
    retainedEdgeDeparture Q u eligible g L K extra h t n ≤ L * crudePaddingWeight t.padding := by
  unfold retainedEdgeDeparture
  split_ifs
  · exact (div_le_self (mul_nonneg hL (hu _)) (hg n)).trans
      (mul_le_mul_of_nonneg_left (hub _) hL)
  · exact mul_nonneg hL (by unfold crudePaddingWeight; positivity)

theorem retained_word_le_crude {R : ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop)
    (h : ℕ) (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (hub : ∀ q, u q ≤ crudePaddingWeight q) (hg : ∀ n, 1 ≤ (g n) ^ 2)
    (step : Fin R → SignedStep) (n : ℤ) :
    scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step) ≤
      ∏ i, L * crudePaddingWeight (step i).padding := by
  rw [scalarWalkProduct_ofFn]
  apply Finset.prod_le_prod
  · intro i _
    exact retainedEdgeDeparture_nonneg Q u eligible g L K extra h hL hu _ _
  · intro i _
    exact retainedEdgeDeparture_le_crude Q u eligible g L K extra h hL hu hub hg _ _

theorem retained_word_padding_divisibility {R : ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop)
    (h : ℕ) (step : Fin R → SignedStep) (n : ℤ)
    (hn : scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h)
      n (List.ofFn step) ≠ 0) (i : Fin R) :
    ((step i).padding : ℤ) ∣ n + wordDisplacement h ((List.ofFn step).take i.val) := by
  rw [scalarWalkProduct_ofFn] at hn
  have hi : retainedEdgeDeparture Q u eligible g L K extra h (step i)
      (n + wordDisplacement h ((List.ofFn step).take i.val)) ≠ 0 := by
    intro hi
    exact hn (prod_eq_zero (mem_univ i) hi)
  unfold retainedEdgeDeparture at hi
  split_ifs at hi with ht
  · exact ht.2.2.1
  · exact (hi rfl).elim

theorem lifted_retained_word_padding_tests {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (step : Fin R → SignedStep)
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : data.residueValue (fun n => scalarWalkProduct h
      (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step)) x ≠ 0) :
    MainPaddingTests Subtype.val h B (List.ofFn step) x := by
  intro k p hp
  have hk : k.val < R := by simpa only [List.length_ofFn] using k.isLt
  let i : Fin R := ⟨k.val, hk⟩
  have he : (List.ofFn step).get k = step i := by
    change (List.ofFn step)[k.val] = step i
    simp only [List.getElem_ofFn]
    rfl
  rw [he] at hp
  have hd := retained_word_padding_divisibility Q u eligible g L K extra h step
    (data.residueOrigin x) hx i
  have hpdiv : (p.val : ℤ) ∣ data.residueOrigin x +
      wordDisplacement h ((List.ofFn step).take k.val) :=
    (show (p.val : ℤ) ∣ ((step i).padding : ℤ) by
      exact_mod_cast (Nat.mem_primeFactors.mp hp).2.1).trans hd
  exact (residue_offset_divisibility ((x p).val : ZMod p.val) _ _
    (data.residueOrigin_spec x p)).mp hpdiv

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Walks.ColumnPaddingBridge
namespace OAI

/-! The actual departure product has the retained-column majorant and
the precise small-singleton crude bound used by the trace theorem. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical




lemma columnTupleAtNat_val {J R : ℕ} {P : Fin J → Finset ℕ}
    (w : ColumnPrimeAssignment J R P) (i : Fin R) :
    columnTupleAtNat w i.val = columnTuple w i := by
  simp only [columnTupleAtNat, i.isLt, dite_true, Fin.eta]

lemma columnForwardAtNat_val {R : ℕ} (forward : Fin R → Bool) (i : Fin R) :
    columnForwardAtNat forward i.val = forward i := by
  simp only [columnForwardAtNat, i.isLt, dite_true, Fin.eta]

theorem retained_word_le_column {J k : ℕ} {P : Fin J → Finset ℕ}
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (w : ColumnPrimeAssignment J (2 * k) P) (forward : Fin (2 * k) → Bool)
    (q : Fin (2 * k) → Q) (n : ℤ) :
    scalarWalkProduct h
      (retainedEdgeDeparture Q u (fun t => eligible t.tuple) g L K (fun t => extra t.tuple) h)
      n (columnTupleWord w forward (fun i => (q i).val)) ≤
      retainedColumnPaddingWeight Q u (fun w i => eligible (columnTupleAtNat w i)) g L K
        (fun w i => extra (columnTupleAtNat w i)) (actualColumnNext h forward) n w q := by
  rw [retainedColumnPaddingWeight_eq_departure_product Q u _ g L K _ _ h n w forward q]
  · unfold columnTupleWord
    rw [scalarWalkProduct_ofFn]
    apply Finset.prod_le_prod
    · intro i _
      exact retainedEdgeDeparture_nonneg Q u _ g L K _ h hL hu _ _
    · intro i _
      simp only [columnTupleAtNat_val]
      exact retainedEdgeDeparture_le_atom Q u _ g L K _ h hL hu _ _
  · intro i z
    simp only [actualColumnNext, columnForwardAtNat_val, columnTupleAtNat_val]


lemma columnCrudeCap_nonneg {J R : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L : ℝ) (hL : 0 ≤ L) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) :
    0 ≤ columnCrudeCap L a := by
  unfold columnCrudeCap crudePaddingWeight
  positivity

theorem columnCrudeCap_small {J R S T : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L : ℝ) (hL : 0 ≤ L) (a : ColumnPrimeAssignment J R P × (Fin R → Q)) (hST : S ≤ T) :
    columnCrudeCap L a * 2 ^ S ≤ crudeTraceWeight R T (fun i => (a.2 i).val) L 1 := by
  unfold crudeTraceWeight
  rw [one_mul, mul_comm (2 ^ T)]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hST) (columnCrudeCap_nonneg L hL a)

theorem columnCrudeCap_exp {J R S : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (L Cs : ℝ) (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hR : (R : ℝ) ≤ 2 * L)
    (hS : (S : ℝ) ≤ Cs * L * Real.log L)
    (hq : ∀ i, (((a.2 i).val).primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    columnCrudeCap L a * 2 ^ S ≤ Real.exp ((Cs + 402) * L * (Real.log L) ^ 2) := by
  have hb := crudeTraceWeight_exp_bound R S (fun i => (a.2 i).val) L 1 0 Cs
    hL hlog hR hS (by norm_num) (by simp) hq
  simpa only [crudeTraceWeight, columnCrudeCap, one_mul, zero_add, mul_comm] using hb

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

lemma paddingDensity_eq_of_prime_residues (Qp Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (n m : ℤ) (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) (hg : g n = g m) :
    paddingDensity Q u eligible g n = paddingDensity Q u eligible g m := by
  unfold paddingDensity
  rw [hg]
  congr 1
  apply sum_congr rfl
  intro q hq
  simp only [squarefree_divisor_congr Qp q (hsq q hq) (hpool q hq) n m hnm]

lemma retainedEdgeDeparture_eq_of_prime_residues (Qp Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (h : ℕ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (hg : ∀ n m : ℤ, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ t n m, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) →
      (extra t n ↔ extra t m))
    (t : SignedStep) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    retainedEdgeDeparture Q u eligible g L K extra h t n =
      retainedEdgeDeparture Q u eligible g L K extra h t m := by
  by_cases hq : t.padding ∈ Q
  · have hdiv := squarefree_divisor_congr Qp t.padding (hsq _ hq) (hpool _ hq) n m hnm
    have hshift : ∀ p ∈ Qp, ((n + t.displacement h : ℤ) : ZMod p) =
        ((m + t.displacement h : ℤ) : ZMod p) := by
      intro p hp
      simp only [Int.cast_add, hnm p hp]
    have hkeep (n m : ℤ) (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
        integerEdgeKeep Q u (eligible t) g L K (extra t) n ↔
          integerEdgeKeep Q u (eligible t) g L K (extra t) m := by
      unfold integerEdgeKeep
      rw [paddingDensity_eq_of_prime_residues Qp Q u (eligible t) g hsq hpool n m hnm
        (hg n m hnm), hextra t n m hnm]
    unfold retainedEdgeDeparture
    simp only [hdiv, hkeep n m hnm, hkeep _ _ hshift, hg n m hnm]
  · simp only [retainedEdgeDeparture, hq, false_and, ite_false]

theorem retained_word_eq_of_prime_residues {R : ℕ}
    (Qp Q : Finset ℕ) (u : ℕ → ℝ) (eligible : SignedStep → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : SignedStep → ℤ → Prop) (h : ℕ)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ Qp)
    (hg : ∀ n m : ℤ, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ t n m, (∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) →
      (extra t n ↔ extra t m))
    (step : Fin R → SignedStep) (n m : ℤ)
    (hnm : ∀ p ∈ Qp, (n : ZMod p) = (m : ZMod p)) :
    scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step) =
      scalarWalkProduct h (retainedEdgeDeparture Q u eligible g L K extra h) m (List.ofFn step) := by
  rw [scalarWalkProduct_ofFn, scalarWalkProduct_ofFn]
  apply prod_congr rfl
  intro i _
  apply retainedEdgeDeparture_eq_of_prime_residues Qp Q u eligible g L K extra h hsq hpool hg hextra
  intro p hp
  simp only [Int.cast_add, hnm p hp]

theorem lifted_retained_word_independent_tuple {h J M R B : ℕ}
    (data : ProhibitedPrimeFamily h J M) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : SignedStep → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : SignedStep → ℤ → Prop) (step : Fin R → SignedStep)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ t n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra t n ↔ extra t m))
    (label : Fin R × Fin J → ↥(data.P ∪ data.Q))
    (hlabel : ∀ p ∈ univ.image label, p.val ∈ data.P)
    (x y : ↥(data.P ∪ data.Q) → Fin B)
    (hxy : ∀ p, p ∉ univ.image label → x p = y p) :
    data.residueValue (fun n => scalarWalkProduct h
      (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step)) x =
    data.residueValue (fun n => scalarWalkProduct h
      (retainedEdgeDeparture Q u eligible g L K extra h) n (List.ofFn step)) y := by
  apply data.residueValue_independent_tuple label hlabel _ _ x y hxy
  exact retained_word_eq_of_prime_residues data.Q Q u eligible g L K extra h hsq hpool hg hextra step

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualClosedPairCatalog
namespace OAI

/-! The actual trace catalog retains the numerical masks and allowed pair support. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

variable {D V : Type*} [DecidableEq D] [Fintype D] [Fintype V]





theorem actualClosedPairCatalog_chains {h k : ℕ}
    (embed : V → D × ℤ) (Q : Finset ℕ) (tuple : D → ℕ) (hinj : Function.Injective tuple)
    (gate : D → ℤ → ℤ → Prop) (pairs : Finset (ℕ × ℕ)) (x : D × ℤ)
    (p : (Fin k → D × (Q × Bool)) × (Fin k → D × (Q × Bool)))
    (hp : p ∈ actualClosedPairCatalog embed Q tuple h gate pairs k x) :
    ((integerClosedWordCode Q tuple p).take k).IsChain (fun a b => a.tuple ≠ b.tuple) ∧
      ((integerClosedWordCode Q tuple p).drop k).IsChain (fun a b => a.tuple ≠ b.tuple) := by
  have ht := (mem_filter.mp hp).2.1
  have ha := integerPathMask_tuple_chain embed Q tuple hinj h gate x p.1 ht.2.1
  have hb := integerPathMask_tuple_chain embed Q tuple hinj h gate x p.2 ht.2.2
  have hlen : (integerStepWord Q tuple p.1).length = k := by
    simp only [integerStepWord, List.length_map, List.length_ofFn]
  have htake : (integerStepWord Q tuple p.1).take k = integerStepWord Q tuple p.1 := by
    simpa only [hlen] using (List.take_length (l := integerStepWord Q tuple p.1))
  have hdrop : (integerStepWord Q tuple p.1).drop k = [] := by
    simpa only [hlen] using (List.drop_length (l := integerStepWord Q tuple p.1))
  simp only [integerClosedWordCode, List.take_append, List.drop_append, hlen, Nat.sub_self,
    List.take_zero, List.drop_zero, List.append_nil, List.nil_append, htake, hdrop]
  exact ⟨ha, reverseWord_chain hb⟩

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualColumnWeights
namespace OAI

/-! Verify all weight hypotheses of the trace estimate for the literal
departure product appearing in the matrix expansion. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical


lemma actualColumnWeight_nonneg {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    0 ≤ actualColumnWeight data u eligible g L K extra forward a x :=
  scalarWalkProduct_nonneg h _
    (retainedEdgeDeparture_nonneg Q u _ g L K _ h hL hu) _ _

lemma actualColumnWeight_le_cap {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q) (hub : ∀ q, u q ≤ crudePaddingWeight q)
    (hg : ∀ n, 1 ≤ (g n) ^ 2)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    actualColumnWeight data u eligible g L K extra forward a x ≤ columnCrudeCap L a :=
  retained_word_le_crude Q u _ g L K _ h hL hu hub hg
    (fun i => SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val) _

lemma actualColumnWeight_padding {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B)
    (hx : actualColumnWeight data u eligible g L K extra forward a x ≠ 0) :
    MainPaddingTests Subtype.val h B (columnTupleWord a.1 forward (fun i => (a.2 i).val)) x :=
  lifted_retained_word_padding_tests data Q u _ g L K _
    (fun i => SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val) x hx

lemma actualColumnWeight_independent {h J M R B : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (hP : ∀ j, P j ⊆ data.P)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℕ → ℤ → Prop) (forward : Fin R → Bool)
    (hsq : ∀ q ∈ Q, Squarefree q) (hpool : ∀ q ∈ Q, q.primeFactors ⊆ data.Q)
    (hg : ∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m)
    (hextra : ∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
      (extra d n ↔ extra d m))
    (a : ColumnPrimeAssignment J R P × (Fin R → Q))
    (x y : ↥(data.P ∪ data.Q) → Fin B)
    (hxy : ∀ p, p ∉ univ.image (actualColumnLabel data hP a.1) → x p = y p) :
    actualColumnWeight data u eligible g L K extra forward a x =
      actualColumnWeight data u eligible g L K extra forward a y := by
  apply lifted_retained_word_independent_tuple data Q u _ g L K _
    (fun i => SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val)
    hsq hpool hg (fun t => hextra t.tuple) (actualColumnLabel data hP a.1) _ x y hxy
  intro p hp
  obtain ⟨i, _, rfl⟩ := mem_image.mp hp
  exact hP i.2 (a.1 i.2 i.1).property

lemma actualColumnWeight_le_retained {h J M B k : ℕ} {P : Fin J → Finset ℕ} {Q : Finset ℕ}
    (data : ProhibitedPrimeFamily h J M) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (forward : Fin (2 * k) → Bool)
    (hL : 0 ≤ L) (hu : ∀ q, 0 ≤ u q)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (x : ↥(data.P ∪ data.Q) → Fin B) :
    actualColumnWeight data u eligible g L K extra forward a x ≤
      retainedColumnPaddingWeight Q u (fun w i => eligible (columnTupleAtNat w i)) g L K
        (fun w i => extra (columnTupleAtNat w i)) (actualColumnNext h forward)
        (data.residueOrigin x) a.1 a.2 :=
  retained_word_le_column Q u eligible g L K extra h hL hu a.1 forward a.2 _

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualColumnCatalog
namespace OAI

/-! Structural properties of the column fiber of actual closed matrix paths. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma singletonLabels_card_le_slots {ι τ : Type*} [Fintype ι] [Fintype τ]
    [DecidableEq ι] (label : τ → ι) :
    (singletonLabels label).card ≤ Fintype.card τ := by
  rw [← singleton_slot_count label]
  exact (card_le_card (filter_subset _ _)).trans_eq (card_univ)

variable {h J M k : ℕ} {P : Fin J → Finset ℕ}
    {V : Type*} [Fintype V]

omit [Fintype V] in
lemma actualColumnCatalog_pairs (data : ProhibitedPrimeFamily h J M)
    (embed : V → ((j : Fin J) → P j) × ℤ) (Q : Finset ℕ)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q
      (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward)
    (i : Fin (2 * k)) : (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs := by
  obtain ⟨p, hp, hw⟩ := closedTraceFiber_word Q _ forward a ha
  have hs := (mem_filter.mp hp).2.2
  apply hs (SignedStep.mk (forward i) (columnTuple a.1 i) (a.2 i).val)
  rw [← hw]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

lemma actualColumnCatalog_chains (data : ProhibitedPrimeFamily h J M)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (embed : V → ((j : Fin J) → P j) × ℤ) (Q : Finset ℕ)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q
      (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward) :
    ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).take k).IsChain
        (fun a b => a.tuple ≠ b.tuple) ∧
      ((columnTupleWord a.1 forward (fun i => (a.2 i).val)).drop k).IsChain
        (fun a b => a.tuple ≠ b.tuple) := by
  obtain ⟨p, hp, hw⟩ := closedTraceFiber_word Q _ forward a ha
  rw [hw]
  exact actualClosedPairCatalog_chains embed Q _ (primeTuple_injective hprime hdisjoint)
    gate data.pairs x p hp

omit [Fintype V] in
lemma actualColumnCatalog_crude_cost (data : ProhibitedPrimeFamily h J M)
    (hP : ∀ j, P j ⊆ data.P) (L C : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hk : (k : ℝ) ≤ L)
    (hJ : (J : ℝ) ≤ C * Real.log L) (hM : (M : ℝ) ≤ 100 * Real.log L)
    (embed : V → ((j : Fin J) → P j) × ℤ) (Q : Finset ℕ)
    (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
    (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * k) → Bool)
    (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q))
    (ha : a ∈ closedTraceFiber Q
      (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward) :
    columnCrudeCap L a * 2 ^ (2 * k * J + (singletonLabels (actualColumnLabel data hP a.1)).card) ≤
      Real.exp ((4 * C + 402) * L * (Real.log L) ^ 2) := by
  have hs : (singletonLabels (actualColumnLabel data hP a.1)).card ≤ 2 * k * J := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      singletonLabels_card_le_slots (actualColumnLabel data hP a.1)
  apply columnCrudeCap_exp L (4 * C) a hL hlog (by push_cast; linarith)
  · have hs' : ((singletonLabels (actualColumnLabel data hP a.1)).card : ℝ) ≤ 2 * k * J := by
      exact_mod_cast hs
    have hp := mul_le_mul (mul_le_mul_of_nonneg_left hk (by norm_num)) hJ
      (show (0 : ℝ) ≤ J by positivity) (show 0 ≤ 2 * L by positivity)
    push_cast
    nlinarith
  · intro i
    exact (show (((a.2 i).val).primeFactors.card : ℝ) ≤ M by
      exact_mod_cast data.padding_card _
        (actualColumnCatalog_pairs data embed Q gate x forward a ha i)).trans hM

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualColumnTrace
namespace OAI

/-! The four trace estimates applied to the actual matrix-path fiber.
All caps, singleton costs, padding majorants and witness lengths are discharged. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_actual_column_trace (h : ℕ) (C W : ℝ)
    (hh : 0 < h) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (hP : ∀ j, P j ⊆ data.P),
      1 ≤ J → ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
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
      (∀ dq ∈ data.pairs, dq.2 ≤ Qmax) →
      (∀ w : (j : Fin J) → P j, ∀ j, (∏ l ∈ univ.erase j, (w l).val) ≤ Dmax) →
      (∀ q ∈ Q, Squarefree q) → (∀ q ∈ Q, q.primeFactors ⊆ data.Q) →
      ∀ (u : ℕ → ℝ) (g : ℤ → ℝ) (K : ℝ)
        (eligible : ℕ → ℕ → Prop) (extra : ℕ → ℤ → Prop),
      (∀ q, 0 ≤ u q) → (∀ q, u q ≤ crudePaddingWeight q) →
      (∀ n, 1 ≤ (g n) ^ 2) → 1 ≤ K →
      (∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m) →
      (∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
        (extra d n ↔ extra d m)) →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (embed : V → ((j : Fin J) → P j) × ℤ)
        (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop)
        (x : ((j : Fin J) → P j) × ℤ) (forward : Fin (2 * ⌊L⌋₊) → Bool),
      let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
      let D := 2 * ⌊L⌋₊ + ⌊L ^ (1 / 12 : ℝ)⌋₊ * s
      Real.exp (108 * L) * (∑ a ∈ closedTraceFiber Q
        (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs ⌊L⌋₊ x) forward,
        |prohibitedCenteredAverage data hB s D
          (columnTupleWord a.1 forward (fun i => (a.2 i).val)) (actualColumnLabel data hP a.1)
          (actualColumnWeight data u eligible g L K extra forward a)|) ≤
        (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_prohibited_column_trace_total h C 0 (2 * C + 1) (4 * C + 402) W
      hC (by norm_num) (by positivity) (by positivity) hW,
    eventually_trace_slot_budgets C hC, eventually_trace_witness_budgets C hC,
    eventually_trace_absorption, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)] with
    L htrace hslots hwitness habs hL hlog
  intro J M B H Y Qmax Dmax data hB P Q hP hJ hJM hVm hVM hVpoly hmass hPmass hQmass
    hM hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hqmax hdmax hsq hpool
    u g K eligible extra hu hub hg hK hgdep hextra V _ _ embed gate x forward
  dsimp only
  let k := ⌊L⌋₊
  let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
  let n := ⌊L ^ (1 / 12 : ℝ)⌋₊
  let D := 2 * k + n * s
  let F := closedTraceFiber Q
    (actualClosedPairCatalog embed Q (fun d => ∏ j, (d j).val) h gate data.pairs k x) forward
  let label (a : ColumnPrimeAssignment J (2 * k) P × (Fin (2 * k) → Q)) :=
    actualColumnLabel data hP a.1
  let base (p : ↥(data.P ∪ data.Q)) : Fin B :=
    ⟨0, (data.prime p).pos.trans_le (hB p.val p.property)⟩
  have hklo : L / 2 ≤ (k : ℝ) := hwitness.1
  have hkhi : (k : ℝ) ≤ L := hwitness.2.1
  have hk : 0 < k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hR : 0 < 2 * k := by omega
  have hJC : (J : ℝ) ≤ C * Real.log L :=
    (show (J : ℝ) ≤ (J + M : ℕ) by exact_mod_cast Nat.le_add_right J M).trans hJM
  have hs := hslots k J M hkhi hJM
  obtain ⟨_, _, hspos, hslo, hnpos, hnhi, hKn, hKlo, hKhi, hDL, hcover⟩ := hwitness
  have hpairs (a) (ha : a ∈ F) (i) : (columnTuple a.1 i, (a.2 i).val) ∈ data.pairs :=
    actualColumnCatalog_pairs data embed Q gate x forward a ha i
  have hchains (a) (ha : a ∈ F) :=
    actualColumnCatalog_chains data hprime hdisjoint embed Q gate x forward a ha
  have hb := htrace J M B s D k n (n / 8) H Y Qmax Dmax data hB P Q F hR forward label base
    (actualColumnWeight data u eligible g L K extra forward) (columnCrudeCap L)
    (Real.exp ((4 * C + 402) * L * (Real.log L) ^ 2)) 1 ⟨k, by omega⟩
    u (fun w i => eligible (columnTupleAtNat w i)) g K
    (fun w i => extra (columnTupleAtNat w i)) (actualColumnNext h forward) data.residueOrigin
    hJ hklo hkhi hJM hs.1 hs.2.1 hs.2.2 hP hVm hVM hVpoly hmass hPmass hQmass hM
    hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hpairs
    (fun a ha i => hqmax _ (hpairs a ha i))
    (fun a _ i j => hdmax (fun l => a.1 l i) j) (fun _ _ _ _ => rfl)
    (Real.exp_pos _).le le_rfl (by norm_num) (by simp)
    (fun a _ => columnCrudeCap_nonneg L (by linarith) a)
    (fun a _ z => actualColumnWeight_nonneg data u eligible g L K extra forward
      (by linarith) hu a z)
    (fun a _ z => actualColumnWeight_le_cap data u eligible g L K extra forward
      (by linarith) hu hub hg a z)
    (fun a ha => actualColumnCatalog_crude_cost data hP L C (by linarith) hlog hkhi hJC hM
      embed Q gate x forward a ha)
    (fun a _ ha => columnCrudeCap_small L (by linarith) a ha)
    (fun a _ z t ht => actualColumnWeight_independent data hP u eligible g L K extra forward
      hsq hpool hgdep hextra a z t ht)
    (fun a _ z hz => actualColumnWeight_padding data u eligible g L K extra forward a z hz)
    le_rfl (fun a _ ha => hcover J _ hJC ha) hDL hnpos hnhi hKn hKlo hKhi hh hspos hslo
    (fun a ha => (hchains a ha).1) (fun a ha => (hchains a ha).2) (by linarith) hu
    (fun a _ z => actualColumnWeight_le_retained data u eligible g L K extra forward
      (by linarith) hu a z)
  exact habs J k K W _ hJ (by omega) hK hW hb

end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.MatrixTraceSummation
namespace OAI

/-! Sum the actual column bounds over signs and starting vertices. -/

namespace TwoPointCorrelations

open _root_.Finset
open scoped _root_.Classical

lemma trace_dimension_allowance (L : ℝ) (k N : ℕ) (_hL : 0 ≤ L)
    (hk : (k : ℝ) ≤ L) (hN : (N : ℝ) ≤ Real.exp (106 * L)) :
    (N : ℝ) * (2 : ℝ) ^ (2 * k) ≤ Real.exp (108 * L) := by
  have hlog : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  calc
    _ ≤ Real.exp (106 * L) * (2 : ℝ) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right hN (by positivity)
    _ = Real.exp (106 * L + (2 * k : ℕ) * Real.log 2) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hb := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 2 * k by positivity)
      push_cast at hb ⊢
      nlinarith


end TwoPointCorrelations

end OAI

end

section
-- module Solutions.OAIChowla.OAI.NumberTheory.TwoPoint.Bounds.ActualMatrixTrace
namespace OAI

/-! The actual residue-model matrix moment at the canonical trace length. -/

namespace TwoPointCorrelations

open _root_.Finset _root_.Filter
open scoped _root_.Classical

theorem eventually_actual_matrix_trace_oai (h : ℕ) (C W : ℝ)
    (hh : 0 < h) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (J M B H Y Qmax Dmax : ℕ)
      (data : ProhibitedPrimeFamily h J M) (hB : ∀ p ∈ data.P ∪ data.Q, p ≤ B)
      (P : Fin J → Finset ℕ) (Q : Finset ℕ)
      (_hP : ∀ j, P j ⊆ data.P),
      1 ≤ J → ((J + M : ℕ) : ℝ) ≤ C * Real.log L →
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
      (∀ dq ∈ data.pairs, dq.2 ≤ Qmax) →
      (∀ w : (j : Fin J) → P j, ∀ j, (∏ l ∈ univ.erase j, (w l).val) ≤ Dmax) →
      (∀ q ∈ Q, Squarefree q) → (∀ q ∈ Q, q.primeFactors ⊆ data.Q) →
      ∀ (u : ℕ → ℝ) (g : ℤ → ℝ) (K : ℝ)
        (eligible : ℕ → ℕ → Prop) (extra : ℕ → ℤ → Prop),
      (∀ q, 0 ≤ u q) → (∀ q, u q ≤ crudePaddingWeight q) →
      (∀ n, 1 ≤ (g n) ^ 2) → 1 ≤ K →
      (∀ n m : ℤ, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) → g n = g m) →
      (∀ d n m, (∀ p ∈ data.Q, (n : ZMod p) = (m : ZMod p)) →
        (extra d n ↔ extra d m)) →
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (embed : V → ((j : Fin J) → P j) × ℤ), Function.Injective embed →
      (Fintype.card V : ℝ) ≤ Real.exp (106 * L) →
      ∀ (gate : ((j : Fin J) → P j) → ℤ → ℤ → Prop),
      (∀ d q, eligible d q → (d, q) ∈ data.pairs) →
      let s := ⌊L ^ (1 / 10 : ℝ)⌋₊
      let tuple := fun d : (j : Fin J) → P j => ∏ j, (d j).val
      let weight := maskedSignedIntegerWeight Q u eligible g (fun d => centeredTuple d.primeFactors)
        L K extra h (fun n => ¬ProhibitedSite h s (fun d q => (d, q) ∈ data.pairs) n)
      (data.residueLaw B hB).average (fun r => matrixFrobeniusSq
        (shiftMatrix embed (integerShiftNext Q tuple h) (physicalShiftWeight Q tuple h gate
          (fun t n => weight t (n + data.residueOrigin r))) ^ ⌊L⌋₊)) ≤
        (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * ⌊L⌋₊) := by
  filter_upwards [eventually_actual_column_trace h C W hh hC hW,
    eventually_ge_atTop (2 : ℝ)] with L hcolumn hL
  intro J M B H Y Qmax Dmax data hB P Q hP hJ hJM hVm hVM hVpoly hmass hPmass hQmass
    hM hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hqmax hdmax hsq hpool
    u g K eligible extra hu hub hg hK hgdep hextra V _ _ embed hinj hdim gate hallowed
  dsimp only
  have hkhi : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le (by linarith)
  have hk : 0 < ⌊L⌋₊ := by
    have ht := Nat.lt_floor_add_one L
    have hp : (0 : ℝ) < (⌊L⌋₊ : ℝ) := by linarith
    exact_mod_cast hp
  have hgzero (n : ℤ) : g n ≠ 0 := by
    intro he
    have hb := hg n
    rw [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hb
    linarith
  apply matrix_residue_trace_of_column_bounds data hB hP hprime hdisjoint
    ⌊L ^ (1 / 10 : ℝ)⌋₊
    (2 * ⌊L⌋₊ + ⌊L ^ (1 / 12 : ℝ)⌋₊ * ⌊L ^ (1 / 10 : ℝ)⌋₊)
    (by omega) (by omega) embed hinj Q u eligible g L K _ extra gate hsq hpool
    hgzero hgdep hextra hallowed (by positivity)
    (trace_dimension_allowance L ⌊L⌋₊ (Fintype.card V) (by linarith) hkhi hdim)
  exact hcolumn J M B H Y Qmax Dmax data hB P Q hP hJ hJM hVm hVM hVpoly hmass
    hPmass hQmass hM hprime hdisjoint hlo hhi hY hYexp hH hQmax hDmax hqmax hdmax
    hsq hpool u g K eligible extra hu hub hg hK hgdep hextra V embed gate

end TwoPointCorrelations

end OAI

end

theorem solution : type_of% @OAI.TwoPointCorrelations.eventually_actual_matrix_trace_oai := @OAI.TwoPointCorrelations.eventually_actual_matrix_trace_oai
