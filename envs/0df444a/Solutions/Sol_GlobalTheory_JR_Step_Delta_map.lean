-- Prove2me | solution 1 for GlobalTheory.JR.Step.Delta_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:29.628614+00:00
-- url     : https://prove2.me/submissions/17822a39-557c-42d7-ab91-53b9515f21ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftMatch
import Theorems.Thm_GlobalTheory_JR_Step_mom_glMap
import Theorems.Thm_GlobalTheory_JR_Step_sec_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k')
namespace GlobalTheory.JR.Step
theorem _root_.solution (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  have : hankel (a.map φ) = (hankel a).map φ := by
    ext i j
    simp only [hankel, Matrix.of_apply, Matrix.map_apply, sec_map, mom_glMap]
  rw [Delta, Delta, this, RingHom.map_det]
  rfl
end GlobalTheory.JR.Step
