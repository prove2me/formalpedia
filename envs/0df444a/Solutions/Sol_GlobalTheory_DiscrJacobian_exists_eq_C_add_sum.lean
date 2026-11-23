-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.exists_eq_C_add_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:30.390571+00:00
-- url     : https://prove2.me/submissions/c4b34d5b-2c9b-41c3-82b6-954cd0309806

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
import Theorems.Thm_GlobalTheory_SocleDet_mem_span_X_of_coeff

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
theorem _root_.solution {R : Type} [CommRing R] {g : ℕ}
    (s : MvPowerSeries (Fin g) R) :
    ∃ u : Fin g → MvPowerSeries (Fin g) R, s = C (constantCoeff s) + ∑ j, X j * u j := by
  have hmem : s - C (constantCoeff s) ∈
      Ideal.span ((fun i => (X i : MvPowerSeries (Fin g) R)) '' ↑(Finset.univ : Finset (Fin g))) := by
    apply _root_.GlobalTheory.SocleDet.mem_span_X_of_coeff
    intro m hm
    have : m = 0 := by ext j; simpa using hm j (Finset.mem_univ j)
    subst this
    simp
  rw [Finset.coe_univ, Set.image_univ, Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, ?_⟩
  rw [← sub_eq_iff_eq_add', ← hc]
  simp [mul_comm]
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
