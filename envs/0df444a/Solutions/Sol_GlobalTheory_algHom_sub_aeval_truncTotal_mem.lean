-- Prove2me | solution 1 for GlobalTheory.algHom_sub_aeval_truncTotal_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:49:53.548159+00:00
-- url     : https://prove2.me/submissions/698d2321-5075-4386-9b2f-4b592d2432b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Theorems.Thm_GlobalTheory_algHom_mem_pow_of_le_order
import Theorems.Thm_GlobalTheory_algHom_coe_mvPolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
namespace GlobalTheory
theorem _root_.solution (φ : MvPowerSeries σ A →ₐ[A] S) {J : Ideal S}
    (hφ : ∀ i, φ (X i) ∈ J) (n : ℕ) (g : MvPowerSeries σ A) :
    φ g - MvPolynomial.aeval (fun i => φ (X i)) (truncTotal n g) ∈ J ^ n := by
  rw [← algHom_coe_mvPolynomial, ← map_sub]
  refine algHom_mem_pow_of_le_order φ hφ (nat_le_order fun d hd => ?_)
  rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, sub_self]
end GlobalTheory
