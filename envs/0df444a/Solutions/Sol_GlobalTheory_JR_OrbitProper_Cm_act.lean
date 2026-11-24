-- Prove2me | solution 1 for GlobalTheory.JR.OrbitProper.Cm_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:09:37.752005+00:00
-- url     : https://prove2.me/submissions/431ee940-b698-49cf-9d93-cbe4f8fac03b

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
    Cm (act g Y) = Cm Y * ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  ext i j
  simp only [Cm, act, of_apply]
  rw [conj_pow_GL, vecMul_vecMul, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← vecMul_vecMul]
  simp [mul_apply, vecMul, dotProduct]
end GlobalTheory.JR.OrbitProper
