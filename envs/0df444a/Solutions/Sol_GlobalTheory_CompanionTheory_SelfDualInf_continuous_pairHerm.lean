-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.continuous_pairHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:02:22.647814+00:00
-- url     : https://prove2.me/submissions/94cd5b88-bb51-4922-b178-d992c3f8fd27

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
theorem _root_.solution (n : ℕ) (S : HermR R σ n) : Continuous (pairHerm R σ n S) := by
  have := isTopologicalRing_tens (F := F) (E := E) R
  show Continuous fun T : HermR R σ n => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
    (∑ a, ∑ b, (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a b * (T : Matrix (Fin n) (Fin n) _) b a)
  exact continuous_const.mul ((continuous_trace R).comp
    (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      continuous_const.mul (continuous_subtype_val.matrix_elem b a)))
end GlobalTheory.CompanionTheory.SelfDualInf
