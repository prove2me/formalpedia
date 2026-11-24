-- Prove2me | solution 1 for GlobalTheory.CechDR.dOne_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:26.151393+00:00
-- url     : https://prove2.me/submissions/30f6a4fc-6162-481c-86ed-afd2211fa236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CrystallineConnectionFormCoboundaryZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OneFormMapEqKaehlerDifferentialMap
import Theorems.Thm_GlobalTheory_CechDR_dOne_smul

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
theorem _root_.solution (b c : B) : dOne R B (b • D R B c) = wedge R B (D R B b) (D R B c) := by
  rw [dOne_smul, dOne_D, smul_zero, add_zero]
end GlobalTheory.CechDR
