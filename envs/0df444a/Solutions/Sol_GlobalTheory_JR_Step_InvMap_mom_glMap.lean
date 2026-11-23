-- Prove2me | solution 1 for GlobalTheory.JR.Step.InvMap.mom_glMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:34.556869+00:00
-- url     : https://prove2.me/submissions/2c7c4a7b-39eb-47bd-b638-2a6c3ac21ef5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom

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
theorem _root_.solution (Y : Gl r k) (i : ℕ) : mom (glMap φ Y) i = φ (mom Y i) := by
  have hp : (Y.1.map φ) ^ i = (Y.1 ^ i).map φ := by
    have := map_pow φ.mapMatrix Y.1 i
    simpa only [RingHom.mapMatrix_apply] using this.symm
  simp only [mom, glMap, hp, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]
end GlobalTheory.JR.Step.InvMap
