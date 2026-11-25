-- Prove2me | solution 1 for GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:59.415544+00:00
-- url     : https://prove2.me/submissions/2a79fd74-78a3-47fc-86dc-b3c2274ec0e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_eq_of_forall_sub_mem_ideal_pow
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_algHom_sub_mem_pow
import Theorems.Thm_GlobalTheory_constDerivEval_X
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
theorem _root_.solution (J : Ideal S) [IsHausdorff J S]
    {φ ψ : MvPowerSeries σ A →ₐ[A] S} (hφ : ∀ i, φ (X i) ∈ J) (h : ∀ i, φ (X i) = ψ (X i)) :
    φ = ψ :=
  AlgHom.ext fun g => eq_of_forall_sub_mem_ideal_pow J fun n =>
    algHom_sub_mem_pow φ ψ hφ (fun i => h i ▸ hφ i) (fun i => by simp [h i]) g
end GlobalTheory
