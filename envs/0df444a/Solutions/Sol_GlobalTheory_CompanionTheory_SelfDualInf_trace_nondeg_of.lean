-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.trace_nondeg_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:08.006707+00:00
-- url     : https://prove2.me/submissions/b809217e-d97f-4011-84cd-ba3aae13a2d5

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_trace_nondeg

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
theorem _root_.solution [Algebra.IsSeparable F E] (L : R →+ ℝ)
    (hL : ∀ t, (∀ r, L (r * t) = 0) → t = 0) (z : R ⊗[F] E)
    (h : ∀ u, L (Algebra.trace R (R ⊗[F] E) (z * u)) = 0) : z = 0 :=
  trace_nondeg R z fun u => hL _ fun r => by
    have := h (r • u)
    rwa [mul_smul_comm, map_smul, smul_eq_mul] at this
end GlobalTheory.CompanionTheory.SelfDualInf
