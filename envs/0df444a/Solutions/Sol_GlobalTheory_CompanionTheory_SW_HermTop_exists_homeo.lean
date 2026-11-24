-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermTop.exists_homeo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:24:03.174299+00:00
-- url     : https://prove2.me/submissions/605f7c67-835c-4cbf-b677-500c4d891715

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_isModTop
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_isTopRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
variable [TopologicalSpace R] [IsTopologicalRing R]
namespace GlobalTheory.CompanionTheory.SW.HermTop
theorem _root_.solution [Module.Finite F E] :
    Nonempty ((R ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI := isModTop (F := F) (E := E) R
  haveI := isTopRing (F := F) (E := E) R
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩
end GlobalTheory.CompanionTheory.SW.HermTop
