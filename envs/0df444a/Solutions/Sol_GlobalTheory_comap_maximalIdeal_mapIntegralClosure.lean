-- Prove2me | solution 1 for GlobalTheory.comap_maximalIdeal_mapIntegralClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:18.953095+00:00
-- url     : https://prove2.me/submissions/fab3363c-1fa1-4199-a3a1-878342fe77a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_isLocalHom_of_injective_integralClosure
import Theorems.Thm_GlobalTheory_mapIntegralClosure_padicInt_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
namespace GlobalTheory
theorem _root_.solution (σ : K →ₐ[ℚ_[p]] L) :
    (maximalIdeal (integralClosure ℤ_[p] L)).comap
        ((σ.restrictScalars ℤ_[p]).mapIntegralClosure :
          integralClosure ℤ_[p] K →+* integralClosure ℤ_[p] L) =
      maximalIdeal (integralClosure ℤ_[p] K) := by
  haveI := isLocalHom_of_injective_integralClosure _ (mapIntegralClosure_padicInt_injective σ)
  exact maximalIdeal_comap _
end GlobalTheory
