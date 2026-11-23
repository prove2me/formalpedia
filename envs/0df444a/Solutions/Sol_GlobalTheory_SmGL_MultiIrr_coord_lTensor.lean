-- Prove2me | solution 1 for GlobalTheory.SmGL.MultiIrr.coord_lTensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:24.038924+00:00
-- url     : https://prove2.me/submissions/9031a253-fd93-4999-a61c-2f802aa46872

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LowerEquivUpperSwap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr
variable {F G H M V W U : Type} [Field F] [Group G] [Group H] [Group M] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [IsTopologicalGroup H]
namespace GlobalTheory.SmGL.MultiIrr
theorem _root_.solution (l : V →ₗ[F] F) (A : W →ₗ[F] U) (x : V ⊗[F] W) :
    coord l U (A.lTensor V x) = A (coord l W x) := by
  induction x with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul v w => simp [coord]
end GlobalTheory.SmGL.MultiIrr
