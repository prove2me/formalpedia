-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.Cm_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:38.557017+00:00
-- url     : https://prove2.me/submissions/68370600-a60b-46dc-8b2b-362416c666bc

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
theorem _root_.solution (a : Inv r k) : Cm (sec a) = hankel a := by
  ext i j
  simp only [Cm, hankel, mom, sec, of_apply]
  rw [pow_add, ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_first_basis a.1 j j.2, mulVec_single_one, dotProduct_comm]
  simp [vecMul, dotProduct, transpose_apply, mul_comm]
end GlobalTheory.JR.OrbitProper
