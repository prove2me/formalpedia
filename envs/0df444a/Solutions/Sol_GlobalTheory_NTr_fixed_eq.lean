-- Prove2me | solution 1 for GlobalTheory.NTr.fixed_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:37.338124+00:00
-- url     : https://prove2.me/submissions/777e0076-3291-4b9b-97fc-ecc67ce8386b

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
import Theorems.Thm_GlobalTheory_NTr_trace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
namespace GlobalTheory.NTr
theorem _root_.solution {z : E} (hz : star z = z) : algebraMap F E (Algebra.trace F E z / 2) = z := by
  haveI := hU.charZero
  have h := trace_eq (F := F) z
  rw [hz] at h
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero (algebraMap F E)).mpr two_ne_zero
  rw [div_eq_mul_inv, map_mul, h, map_inv₀, map_ofNat, ← two_mul, mul_comm, ← mul_assoc,
    inv_mul_cancel₀ h2E, one_mul]
end GlobalTheory.NTr
