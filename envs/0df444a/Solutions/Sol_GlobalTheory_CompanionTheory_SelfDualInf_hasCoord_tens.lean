-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SelfDualInf.hasCoord_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:25:07.118378+00:00
-- url     : https://prove2.me/submissions/c22b3b55-129d-4b02-ae6e-31f8d205db75

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_BijectiveLinearCombinationOfRankAtStalk
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_HasCoordOfFiniteDimensional
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_of_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_HasCoord_pi
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_isModuleTopology_tens
import Theorems.Thm_GlobalTheory_CompanionTheory_SelfDualInf_isTopologicalRing_tens

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
theorem _root_.solution (h : HasCoord R) : HasCoord (R ⊗[F] E) := by
  have := isModuleTopology_tens (F := F) (E := E) R
  have := isTopologicalRing_tens (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact HasCoord.of_equiv e.toAddEquiv (IsModuleTopology.continuous_of_linearMap e.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap) (h.pi _)
end GlobalTheory.CompanionTheory.SelfDualInf
