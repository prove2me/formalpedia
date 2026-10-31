-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:56:29.293919+00:00
-- url     : https://prove2.me/submissions/76de7137-b7fe-4e1e-8459-89099e1d5d51

import Mathlib
import Definitions.Def_OAIQ081S169
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_paddedConstraint_cover
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_paddedConstraint_shape

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutExactBuckets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Exact integer signatures survive every coefficient-ring reduction

The assignments in this module are integer vectors. In the counting
application they are Boolean vectors or differences of Boolean vectors.
Equality of signatures is an equality in `ℤ`, before any reduction.
No claim about the kernel of a matrix reduced modulo a prime is used.
-/

namespace SubexponentialSAT.SqrtLog.LayoutExactBuckets

open scoped BigOperators
open LayoutPullback

variable {V J R : Type*} [Fintype V] [CommRing R]

theorem signature_sub (A : J → V → ℤ) (x y : V → ℤ) (j : J) :
    signature A (x - y) j = signature A x j - signature A y j := by
  simp [signature, mul_sub, Finset.sum_sub_distrib]

section RationalRowReduction

variable {J' : Type*} [Fintype J']

theorem integer_kernel_of_rational_span (C : J → V → ℤ) (A : J' → V → ℤ)
    (hspan : RationalRowSpan C A) (z : V → ℤ)
    (hz : ∀ j, signature A z j = 0) : ∀ j, signature C z j = 0 := by
  intro j
  obtain ⟨c, hc⟩ := hspan j
  have hA (k : J') : ∑ v, (A k v : ℚ) * (z v : ℚ) = 0 := by
    exact_mod_cast hz k
  have hC : ∑ v, (C j v : ℚ) * (z v : ℚ) = 0 := by
    simp_rw [hc, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, hA, mul_zero]
    simp
  exact_mod_cast hC

end RationalRowReduction

end SubexponentialSAT.SqrtLog.LayoutExactBuckets

end OAI.Algorithms
end

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

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixExtendedEntrySemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.allCompatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
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
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramNodeConcreteLocality
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Equality of the integer signatures emitted by the actual matrix implies
exact equality of the source-row baseline in the full coefficient ring. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutExactBuckets LayoutPullback

variable {r Q d D n : ℕ}

theorem literal_signature_eq_oai (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (t : Fin Q) (g : Fin r) (x y : {v : Fin n //head t v=g} → ℤ)
    (hxy : signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
      p.aWord.length p.R t j.val v.val.val) x =
      signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
      p.aWord.length p.R t j.val v.val.val) y) :
    (pulled p P owner head hhead).bucketLabel t g x =
      (pulled p P owner head hhead).bucketLabel t g y := by
  have he : (fun (j : Fin D) (v : {v : Fin n //head t v=g}) =>
      LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t j.val v.val.val) =
      pulledConstraints (LayoutProducedMatrix.headOwner P owner head hhead t g)
        (paddedConstraint P p.aWord.length p.R t g) := by
    funext j v
    rw [LayoutProducedMatrix.literalNat_fin]
    exact LayoutProducedMatrix.literalMatrix_head P owner head hhead _ _ t g j v
  rw [he] at hxy
  have hs := (paddedConstraint_pullback_spans P p.aWord.length p.R p.denom p.hdenom
    (p.model.nodeUnits p.t Q p.ht p.hfield) t g
    (LayoutProducedMatrix.headOwner P owner head hhead t g)).1
  have hr : signature (pulledConstraints (LayoutProducedMatrix.headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (universal p) P.completeBlocks t g)) x =
      signature (pulledConstraints (LayoutProducedMatrix.headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (universal p) P.completeBlocks t g)) y := by
    funext j
    apply sub_eq_zero.mp
    rw [← signature_sub]
    apply integer_kernel_of_rational_span _ _ hs (x-y) _ j
    intro k
    rw [signature_sub,congrFun hxy k,sub_self]
  funext j
  exact congrFun hr ((Fintype.equivFin (LayoutBlocks.RowIndex (universal p) P.completeBlocks t g)).symm j)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq_oai
