-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.Bm_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:44.088879+00:00
-- url     : https://prove2.me/submissions/04c5ad39-775d-4434-b7a8-7aa853e5311c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
import Theorems.Thm_GlobalTheory_JR_OrbitProper_companionMatrixOfCoeffs_pow_mulVec_first_basis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OrbitProper
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.OrbitProper
theorem _root_.solution (a : Inv r k) : Bm (sec a) = 1 := by
  ext i j
  simp only [Bm, sec, of_apply]
  rw [companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, one_apply, Pi.single_apply]
end GlobalTheory.JR.OrbitProper
