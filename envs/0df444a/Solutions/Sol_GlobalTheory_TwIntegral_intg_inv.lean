-- Prove2me | solution 1 for GlobalTheory.TwIntegral.intg_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:21.512411+00:00
-- url     : https://prove2.me/submissions/7a46031b-ca6b-4a0b-99b8-aac667840848

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TwistedCentralizerIsNormOneTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryTwistInvolutionGLProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCommutantMulIntegralConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitDiscriminantMatrixQuotientIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralTwConjMemCentMul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_norm_det_le_one_of_entries_le_one
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
open GlobalTheory.Tw Matrix
open GlobalTheory GlobalTheory.TwIntegral
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
open Matrix
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
namespace GlobalTheory.TwIntegral
namespace _root_.GlobalTheory.TwIntegral
theorem _root_.solution {A : Matrix (Fin n) (Fin n) E}
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hd : ‖A.det‖ = 1) :
    ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
  intro i j
  have hadj : ‖A.adjugate i j‖ ≤ 1 := by
    rw [adjugate_apply]
    apply _root_.GlobalTheory.norm_det_le_one_of_entries_le_one
    intro k l
    by_cases hk : k = j
    · subst hk
      rw [updateRow_self]
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_apply, hl]
    · rw [updateRow_ne hk]
      exact hA k l
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, hd,
    inv_one, one_mul]
  exact hadj
end _root_.GlobalTheory.TwIntegral
end GlobalTheory.TwIntegral
