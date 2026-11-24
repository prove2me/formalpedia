-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.X_mem_jacobson
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:34.354848+00:00
-- url     : https://prove2.me/submissions/a2e6f24b-b85d-46b9-92fc-bafe1f4357fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
open MvPowerSeries IsLocalRing
open MvPowerSeries IsLocalRing
open scoped TensorProduct
namespace GlobalTheory.DiscrJacobian
namespace _root_.GlobalTheory.DiscrJacobian
theorem _root_.solution {R : Type} [CommRing R] {σ : Type} (j : σ) :
    (X j : MvPowerSeries σ R) ∈ (⊥ : Ideal (MvPowerSeries σ R)).jacobson := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  rw [MvPowerSeries.isUnit_iff_constantCoeff]
  simp
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
