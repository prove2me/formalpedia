-- Prove2me | solution 1 for GlobalTheory.JR.Step.UNormal.full_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:11:18.682161+00:00
-- url     : https://prove2.me/submissions/890e78cd-76ba-4a56-af49-448440cf2da4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjTransposeVecMulVecSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitNormalFormUnitInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.UNormal
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step.UNormal
theorem _root_.solution (Y : Gl r k) (i j : Fin r) : full Y (Fin.castSucc i) (Fin.castSucc j) = Y.1 i j := by
  simp [full, Matrix.reindex_apply, Matrix.submatrix_apply]
end GlobalTheory.JR.Step.UNormal
