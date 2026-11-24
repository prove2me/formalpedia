-- Prove2me | solution 1 for GlobalTheory.JR.Step.InvMap.inv_glMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:40.685509+00:00
-- url     : https://prove2.me/submissions/9ee6603e-92f4-494d-b537-6ee2d957bc45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Theorems.Thm_GlobalTheory_JR_Step_InvMap_mom_glMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.InvMap
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {r : ℕ}
namespace GlobalTheory.JR.Step.InvMap
theorem _root_.solution (Y : Gl r k) : GlobalTheory.JR.inv (glMap φ Y) = (GlobalTheory.JR.inv Y).map φ := by
  refine Prod.ext ?_ (Prod.ext ?_ rfl)
  · funext i
    simp only [GlobalTheory.JR.inv, Inv.map, glMap, Matrix.charpoly_map, Polynomial.coeff_map]
  · funext i
    exact mom_glMap φ Y i
end GlobalTheory.JR.Step.InvMap
