-- Prove2me | solution 1 for GlobalTheory.algHom_sub_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:54.681864+00:00
-- url     : https://prove2.me/submissions/0c81a6e2-7c21-4493-9631-821f2ac2c212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_algHom_sub_aeval_truncTotal_mem
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
theorem _root_.solution (φ ψ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (hψ : ∀ i, ψ (X i) ∈ J) {n : ℕ}
    (h : ∀ i, φ (X i) - ψ (X i) ∈ J ^ n) (g : MvPowerSeries σ A) : φ g - ψ g ∈ J ^ n := by
  have h1 := algHom_sub_aeval_truncTotal_mem φ hφ n g
  have h2 := algHom_sub_aeval_truncTotal_mem ψ hψ n g
  have h3 : MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) -
      MvPolynomial.aeval (fun i => ψ (X i)) (truncTotal n g) ∈ J ^ n := by
    have : (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => φ (X i))) =
        (Ideal.Quotient.mkₐ A (J ^ n)).comp (MvPolynomial.aeval (fun i => ψ (X i))) := by
      ext i
      simpa [Ideal.Quotient.eq] using h i
    rw [← Ideal.Quotient.eq]
    exact DFunLike.congr_fun this _
  have := sub_mem (add_mem h1 h3) h2
  convert this using 1
  ring
end GlobalTheory
