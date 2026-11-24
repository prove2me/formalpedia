-- Prove2me | solution 1 for GlobalTheory.JR.DeltaLift.full_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:34.963325+00:00
-- url     : https://prove2.me/submissions/809ce2a1-39f6-4b9d-83bd-c2370e81859e

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
theorem _root_.solution (Z : Gl r k) (j : Fin r) : full Z (Fin.last r) (Fin.castSucc j) = Z.2.2.1 j := by
  simp [full]
end GlobalTheory.JR.DeltaLift
