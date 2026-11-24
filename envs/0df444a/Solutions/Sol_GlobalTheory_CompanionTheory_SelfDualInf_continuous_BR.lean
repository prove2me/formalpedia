-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.continuous_BR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:39:41.200011+00:00
-- url     : https://prove2.me/submissions/27295e53-8a7e-44b5-a3cd-ecbee0544f34

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_isTopologicalRing_tens
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_continuous_trace

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
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  (σ : E →ₐ[F] E)
namespace GlobalTheory.CompanionTheory.SelfDualInf
theorem _root_.solution {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : Continuous (BR R σ J X) := by
  have := isTopologicalRing_tens (F := F) (E := E) R
  show Continuous fun Y : Fin n → Fin M → R ⊗[F] E => ∑ a, Algebra.trace R (R ⊗[F] E)
    (∑ i, ∑ j, sigR R σ (X a i) * JR R J i j * Y a j)
  exact continuous_finset_sum _ fun a _ => (continuous_trace R).comp
    (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))
end GlobalTheory.CompanionTheory.SelfDualInf
