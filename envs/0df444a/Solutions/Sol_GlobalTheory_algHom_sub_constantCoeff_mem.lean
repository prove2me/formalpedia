-- Prove2me | solution 1 for GlobalTheory.algHom_sub_constantCoeff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:48.237801+00:00
-- url     : https://prove2.me/submissions/6810496d-b54a-414c-9553-3ca019fe68b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_algHom_mem_pow_of_le_order
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mem_germIdeal_pow_iff_le_order
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.pderivEval_X


attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_C

set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
namespace GlobalTheory
theorem _root_.solution (φ : MvPowerSeries σ A →ₐ[A] S) {K : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ K) (g : MvPowerSeries σ A) :
    φ g - algebraMap A S (constantCoeff g) ∈ K := by
  have h : φ (g - C (constantCoeff g)) ∈ K ^ 1 :=
    algHom_mem_pow_of_le_order φ hφ (mem_germIdeal_pow_iff_le_order.1 (by simp [RingHom.mem_ker]))
  rw [pow_one, map_sub] at h
  rwa [← φ.commutes]
end GlobalTheory
