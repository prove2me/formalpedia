-- Prove2me | solution 1 for GlobalTheory.HermUnimod.norm_det_conjT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:29:25.238065+00:00
-- url     : https://prove2.me/submissions/7873560d-4aeb-4e53-88f4-d6b08d5c68d5

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne

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
open GlobalTheory GlobalTheory.HermUnimod
variable {E : Type} [NormedField E]
namespace GlobalTheory.HermUnimod
theorem _root_.solution [StarRing E] (hs : ∀ y : E, ‖star y‖ = ‖y‖) {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n E) : ‖Aᴴ.det‖ = ‖A.det‖ := by
  rw [det_conjTranspose, hs]
end GlobalTheory.HermUnimod
