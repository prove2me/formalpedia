-- Prove2me | solution 1 for GlobalTheory.JR.FourDesc.continuous_star_E
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:58:37.517591+00:00
-- url     : https://prove2.me/submissions/26f49c01-df11-41b5-883c-5d9f50aca8e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaarStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourierDescendedFunctionEqPartialFourier

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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.FourDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.FourDesc
theorem _root_.solution [Unram F E] : Continuous (star : E → E) :=
  (Isometry.of_dist_eq fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous
end GlobalTheory.JR.FourDesc
