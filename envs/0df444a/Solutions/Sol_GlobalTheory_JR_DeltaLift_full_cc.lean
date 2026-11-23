-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.full_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:06.935683+00:00
-- url     : https://prove2.me/submissions/3f030bf2-af45-4330-8f7a-aa4a25d7f093

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisHankelDetNeZeroOfLift

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DeltaLift
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.DeltaLift
theorem _root_.solution (Z : Gl r k) (i j : Fin r) : full Z (Fin.castSucc i) (Fin.castSucc j) = Z.1 i j := by
  simp [full]
end GlobalTheory.JR.DeltaLift
