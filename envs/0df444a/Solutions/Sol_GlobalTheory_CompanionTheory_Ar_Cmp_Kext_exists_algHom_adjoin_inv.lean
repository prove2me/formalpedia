-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.Kext.exists_algHom_adjoin_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:04:48.930245+00:00
-- url     : https://prove2.me/submissions/c825f728-ff70-4e48-8e0a-2db244f354ec

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsRestAlt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ExistsAlgHomAdjoinInv
import Theorems.Thm_UpperTheory_Reformulated_B_Yde9_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.Kext
namespace GlobalTheory.CompanionTheory.Ar.Cmp.Kext
theorem _root_.solution :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (σ : Type) (τ : σ → Ω) (F : MvPolynomial σ ℚ)
      (S : Subalgebra ℚ Ω) (E : Type) [CommRing E] [Algebra ℚ E] (u : σ → E),
      aeval τ F ≠ 0 → S = Algebra.adjoin ℚ (insert (aeval τ F)⁻¹ (Set.range τ)) →
      (∀ G : MvPolynomial σ ℚ, aeval τ G = 0 → aeval u G = 0) → IsUnit (aeval u F) →
      ∃ φ : S →ₐ[ℚ] E, ∀ (G : MvPolynomial σ ℚ) (s : S), (s : Ω) = aeval τ G →
        φ s = aeval u G :=
  _root_.UpperTheory.Reformulated.B.Yde9.main
end GlobalTheory.CompanionTheory.Ar.Cmp.Kext
