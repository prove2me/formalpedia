-- Prove2me | solution 1 for GlobalTheory.CechDR.dOne_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:47.431827+00:00
-- url     : https://prove2.me/submissions/53f0946e-4cf6-4420-8646-ede9222c0d72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open KaehlerDifferential
open GlobalTheory GlobalTheory.CechDR
variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
variable {R B}
namespace GlobalTheory.CechDR
theorem _root_.solution (b : B) (ω : Ω[B⁄R]) :
    dOne R B (b • ω) = wedge R B (D R B b) ω + b • dOne R B ω :=
  Subtype.ext (by simp [dDR_smul])
end GlobalTheory.CechDR
