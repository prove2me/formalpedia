-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.pairHerm_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:42.87456+00:00
-- url     : https://prove2.me/submissions/f2ff4b9d-e941-49e9-92eb-84b44361675f

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_nondeg_of
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_pairHerm_hermUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SelfDualInf
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution [CharZero F] [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (S : HermR R σ n)
    (h : ∀ T, L (pairHerm R σ n S T) = 0) : S = 0 := by
  apply Subtype.ext
  funext a b
  refine trace_nondeg_of R L hL _ fun u => ?_
  rw [← pairHerm_hermUnit R σ hσ n S a b u]
  exact h _
end GlobalTheory.CompanionTheory.SelfDualInf
