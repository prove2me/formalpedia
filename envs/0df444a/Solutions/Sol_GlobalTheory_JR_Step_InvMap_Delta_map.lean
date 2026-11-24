-- Prove2me | solution 1 for GlobalTheory.JR.Step.InvMap.Delta_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:29:47.959902+00:00
-- url     : https://prove2.me/submissions/fba05e19-fd0f-40f0-80e2-7cdc4d1f3f4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Theorems.Thm_GlobalTheory_JR_Step_InvMap_mom_glMap
import Theorems.Thm_GlobalTheory_JR_Step_InvMap_sec_map

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
theorem _root_.solution (a : Inv r k) : Delta (a.map φ) = φ (Delta a) := by
  rw [Delta, Delta, RingHom.map_det]
  congr 1
  ext i j
  simp only [hankel, sec_map, mom_glMap, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
end GlobalTheory.JR.Step.InvMap
