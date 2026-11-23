-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermTop.isTopRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:33.736423+00:00
-- url     : https://prove2.me/submissions/ae41a009-efd7-4b2c-9af9-e78d2883342a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermTop_isModTop

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
theorem _root_.solution [Module.Finite F E] : IsTopologicalRing (R ⊗[F] E) :=
  haveI := isModTop (F := F) (E := E) R
  IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
end GlobalTheory.CompanionTheory.SW.HermTop
