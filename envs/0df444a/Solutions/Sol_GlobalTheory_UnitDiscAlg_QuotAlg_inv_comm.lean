-- Prove2me | solution 1 for GlobalTheory.UnitDiscAlg.QuotAlg.inv_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:49:49.789089+00:00
-- url     : https://prove2.me/submissions/d353d079-ef98-469d-ac6f-0bb3f82ac33f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormDetLeOneOfEntriesNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitAndIntegInvOfNormDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltrametricNormDetOneAddSmulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuotientIntegralUnit
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.QuotAlg
namespace GlobalTheory.UnitDiscAlg.QuotAlg
theorem _root_.solution {E : Type} [Field E] {n : ℕ} {x N : Matrix (Fin n) (Fin n) E}
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by
  by_cases hd : IsUnit x.det
  · calc x⁻¹ * N = x⁻¹ * N * (x * x⁻¹) := by rw [Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
      _ = x⁻¹ * (x * N) * x⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
      _ = N * x⁻¹ := by rw [← Matrix.mul_assoc x⁻¹, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hd]; simp
end GlobalTheory.UnitDiscAlg.QuotAlg
