-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.LocIn.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:56.809881+00:00
-- url     : https://prove2.me/submissions/570f2f8d-05e7-438f-a3ca-8fbc21988812

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinPartEqOneOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_iota_mul
import Theorems.Thm_GlobalTheory_CMVal_Euler_mul_coord
import Theorems.Thm_GlobalTheory_CMVal_Euler_val_iota_le_one
import Theorems.Thm_GlobalTheory_CMVal_Euler_LocIn_val_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
namespace LocIn
theorem _root_.solution {n : ℕ} {v : HeightOneSpectrum (OF E)} {z z' : Af E} (h : LocIn n v z) (h' : LocIn n v z') :
    LocIn n v (z * z') := by
  have hz := fun P hP => h.val_le (P := P) hP
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := h'
  refine ⟨a * b, fun P hP => ?_⟩
  have : (z * z') P - iota (a * b) P = z P * (z' P - iota b P) + (z P - iota a P) * iota b P := by
    rw [iota_mul, mul_coord, mul_coord]; ring
  rw [this]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul]; exact (mul_le_mul' (hz P hP) (hb P hP)).trans_eq (one_mul _)
  · rw [map_mul]; exact (mul_le_mul' (ha P hP) (val_iota_le_one P b)).trans_eq (mul_one _)
end LocIn
end GlobalTheory.CMVal.Euler
