-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.Bm_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:43.430194+00:00
-- url     : https://prove2.me/submissions/c7050598-1184-4e18-896a-b72627acc1d1

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisOrbitInvariantMapProper
import Theorems.Thm_GlobalTheory_JR_OrbitProper_conj_pow_GL

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
theorem _root_.solution (g : GL (Fin r) k) (Y : Gl r k) :
    Bm (act g Y) = (g : Matrix (Fin r) (Fin r) k) * Bm Y := by
  ext i j
  simp only [Bm, act, of_apply]
  rw [conj_pow_GL, mulVec_mulVec, mul_assoc _ _ (g : Matrix (Fin r) (Fin r) k), Units.inv_mul, mul_one,
    ← mulVec_mulVec]
  simp [mul_apply, mulVec, dotProduct]
end GlobalTheory.JR.OrbitProper
