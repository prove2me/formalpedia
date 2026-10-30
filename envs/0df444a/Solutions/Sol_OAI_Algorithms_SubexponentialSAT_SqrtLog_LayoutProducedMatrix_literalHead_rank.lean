-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:50:34.422629+00:00
-- url     : https://prove2.me/submissions/bdcfdf12-513c-48ae-84f6-a3b5edeb8c8a

import Mathlib
import Definitions.Def_OAIQ081S107
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_paddedConstraint_cover
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_paddedConstraint_shape

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutEnumeration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Bridges for an explicit runtime enumeration of raw integer rows.
The enumeration need not agree with the semantic `Fintype.equivFin` order. -/
namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators

variable {J K H V I : Type*} [Fintype V] [Fintype K]

omit [Fintype V] in
theorem rationalRowSpan_pullback [Fintype I] [DecidableEq V]
    (owner : I → V) (C : J → I → ℤ) (A : K → I → ℤ)
    (hspan : RationalRowSpan C A) :
    RationalRowSpan (pulledConstraints owner C) (pulledConstraints owner A) := by
  classical
  intro j
  obtain ⟨c, hc⟩ := hspan j
  refine ⟨c, ?_⟩
  intro v
  simp only [pulledConstraints, LayoutPullback.row, Int.cast_sum, Int.cast_ite,
    Int.cast_zero]
  simp_rw [hc]
  calc
    _ = ∑ i, ∑ k, c k * (if owner i = v then (A k i : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : owner i = v <;> simp [h]
    _ = ∑ k, ∑ i, c k * (if owner i = v then (A k i : ℚ) else 0) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact (Finset.mul_sum Finset.univ
        (fun i => if owner i = v then (A k i : ℚ) else 0) (c k)).symm

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutZeroRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A physical row table may enumerate every incidence, putting zero rows
where no constraint is present.  Such padding changes neither rank nor
exact integer buckets. -/
namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators

variable {J K V : Type*} [Fintype J] [Fintype K] [Fintype V]

omit [Fintype J] [Fintype V] in
theorem rationalRowSpan_of_row_occurs (C : J → V → ℤ) (A : K → V → ℤ)
    (h : ∀ j, ∃ k, A k = C j) : RationalRowSpan C A := by
  classical
  intro j
  obtain ⟨k,hk⟩ := h j
  refine ⟨Pi.single k 1, ?_⟩
  intro v
  simp [Pi.single_apply, hk]

omit [Fintype K] [Fintype V] in
theorem rationalRowSpan_of_zero_or_row (C : J → V → ℤ) (A : K → V → ℤ)
    (h : ∀ k, A k = 0 ∨ ∃ j, A k = C j) : RationalRowSpan A C := by
  classical
  intro k
  rcases h k with hk | ⟨j,hj⟩
  · exact ⟨0, by intro v; simp [hk]⟩
  · refine ⟨Pi.single j 1, ?_⟩
    intro v
    simp [Pi.single_apply, hj]

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

namespace SubexponentialSAT.SqrtLog.LayoutRank

open scoped BigOperators
open LayoutExactBuckets LayoutRowSelection

variable {J K V : Type*} [Fintype J] [Fintype K] [Fintype V]

omit [Fintype J] [Fintype V] in
theorem rowSpace_le_of_rationalRowSpan (C : J → V → ℤ) (A : K → V → ℤ)
    (hspan : RationalRowSpan C A) : rowSpace C ≤ rowSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  obtain ⟨c,hc⟩ := hspan j
  apply (Submodule.mem_span_range_iff_exists_fun ℚ).2
  refine ⟨c, ?_⟩
  funext v
  simpa [rationalRows] using (hc v).symm

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrixRank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Selecting columns in their physical order cannot increase the rational
rank. The map may omit or repeat columns; no runtime permutation is assumed. -/
namespace SubexponentialSAT.SqrtLog.LayoutRank
open Module LayoutExactBuckets LayoutRowSelection

variable {J K V W : Type*} [Fintype J] [Fintype K] [Fintype V] [Fintype W]

omit [Fintype V] in
theorem rowRank_eq_of_mutual_span (C : J → V → ℤ) (A : K → V → ℤ)
    (hCA : RationalRowSpan C A) (hAC : RationalRowSpan A C) :
    rowRank C = rowRank A := by
  unfold rowRank
  rw [le_antisymm (rowSpace_le_of_rationalRowSpan C A hCA)
    (rowSpace_le_of_rationalRowSpan A C hAC)]

end SubexponentialSAT.SqrtLog.LayoutRank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntrySemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact joint-membership meaning of the three selected-color comparisons. -/

namespace SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

open MulticolorTypes

variable {r Q Δ : ℕ}

theorem anchorValid_iff_joint (i : Fin Δ) (t : Fin Q) (u y : UniversalType r Q Δ) :
    anchorValid i t u y ↔ u ∈ joint t (y.head t) i ∧ y ∈ joint t (y.head t) i := by
  simp [anchorValid, and_assoc]

end SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical entry dispatch does not need a head-color oracle. The actual
head-ID scan supplies the column-head invariant; the joint guard compares the
two decoded type words at the requested node. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.Subexp.MatrixExtendedEntryProgram

variable {r Q : ℕ} {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
theorem lookup_label (P : PackingData I (UniversalType r Q 1))
    (w : I) (k : Fin P.blockCount) (y : UniversalType r Q 1)
    (hw : P.lookup w = some (k,y)) : P.label w = y := by
  rw [← P.lookup_sound w (k,y) hw,P.label_at]

omit [Fintype I] in
theorem localEntry_eq (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (v w : I)
    (hwhead : (P.label w).head t = g) :
    localEntry P A R t v w = paddedEntry P A R t g v w := by
  cases hv : P.lookup v with
  | none =>
    by_cases he : w = v
    · subst w
      simp [localEntry,paddedEntry,hv,hwhead]
    · simp [localEntry,paddedEntry,hv,he]
  | some z =>
    rcases z with ⟨j,u⟩
    cases hw : P.lookup w with
    | none => simp [localEntry,paddedEntry,hv,hw]
    | some z =>
      rcases z with ⟨k,y⟩
      have hy : y.head t = g := by
        rw [← lookup_label P w k y hw]
        exact hwhead
      have ha : anchorValid (0 : Fin 1) t u y ↔
          u ∈ joint t g (0 : Fin 1) ∧ y ∈ joint t g (0 : Fin 1) := by
        rw [anchorValid_iff_joint,hy]
      simp [localEntry,paddedEntry,hv,hw,ha,and_assoc]

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramPaddedSpan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! All incidence-indexed rows may be retained. The semantic basis is used only
to count attained signatures, never to select a runtime subset. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutExactBuckets

variable {r Q : ℕ} {I O V : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]
variable {node : Fin Q → O}

theorem paddedConstraint_spans
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    RationalRowSpan
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g) (paddedConstraint P A R t g) ∧
    RationalRowSpan (paddedConstraint P A R t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g) := by
  classical
  exact ⟨rationalRowSpan_of_row_occurs _ _
      (paddedConstraint_cover P A R denom hdenom units t g),
    rationalRowSpan_of_zero_or_row _ _
      (paddedConstraint_shape P A R denom hdenom units t g)⟩

/-- Fiber-summing preserves both span inclusions. Original variable addresses
are arbitrary labels; no compact renumbering is part of the argument. -/
theorem paddedConstraint_pullback_spans [Fintype V] [DecidableEq V]
    (P : PackingData I (UniversalType r Q 1)) (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r)
    (owner : IncidenceHead P t g → V) :
    RationalRowSpan
      (pulledConstraints owner (LayoutBlocks.constraints
        (LayoutUniversal.data A R denom hdenom units) P.completeBlocks t g))
      (pulledConstraints owner (paddedConstraint P A R t g)) ∧
    RationalRowSpan (pulledConstraints owner (paddedConstraint P A R t g))
      (pulledConstraints owner (LayoutBlocks.constraints
        (LayoutUniversal.data A R denom hdenom units) P.completeBlocks t g)) := by
  classical
  obtain ⟨h1,h2⟩ := paddedConstraint_spans P A R denom hdenom units t g
  exact ⟨rationalRowSpan_pullback owner _ _ h1,rationalRowSpan_pullback owner _ _ h2⟩

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProducedMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual integer entry program is a literal owner-fiber sum. Restricting
its columns to the emitted head IDs has exactly the canonical pulled row span,
up to harmless column omission/repetition. All incidence rows are retained. -/
namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutProgram

variable {r Q : ℕ} {I V O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [CommRing O]
variable {node : Fin Q → O}

omit [Fintype V] in
theorem literalMatrix_head (P : PackingData I (UniversalType r Q 1))
    (owner : I → V) (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (t : Fin Q) (g : Fin r) (j : I) (v : {v : V // head t v=g}) :
    literalMatrix P owner A R t j v.val =
      pulledConstraints (headOwner P owner head hhead t g)
        (paddedConstraint P A R t g) j v := by
  rw [literalMatrix,LayoutHeadPullback.row_restrict owner
    (fun i=>(P.label i).head t) (head t) (fun i=>hhead i t) g]
  apply congrArg (fun f => row (headOwner P owner head hhead t g) f v)
  funext w
  exact localEntry_eq P A R t g j w.val w.property

theorem literalHead_rank_oai (P : PackingData I (UniversalType r Q 1))
    (owner : I → V) (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    LayoutRank.rowRank (fun j (v : {v : V // head t v=g}) =>
      literalMatrix P owner A R t j v.val) =
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  have he : (fun j (v : {v : V // head t v=g}) =>literalMatrix P owner A R t j v.val) =
      pulledConstraints (headOwner P owner head hhead t g) (paddedConstraint P A R t g) := by
    funext j v
    exact literalMatrix_head P owner head hhead A R t g j v
  rw [he]
  obtain ⟨h1,h2⟩ := paddedConstraint_pullback_spans P A R denom hdenom units t g
    (headOwner P owner head hhead t g)
  exact LayoutRank.rowRank_eq_of_mutual_span _ _ h2 h1

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank_oai.{u_1, u_2, u_3} := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank_oai.{u_1, u_2, u_3}
