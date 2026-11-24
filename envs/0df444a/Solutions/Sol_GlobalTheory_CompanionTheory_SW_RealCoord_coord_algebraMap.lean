-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.coord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:29.539306+00:00
-- url     : https://prove2.me/submissions/be27e575-1b6b-42ca-9741-80653faec83b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_rho_coe

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealCoord
open InfinitePlace InfinitePlace.Completion
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.CompanionTheory.SW.RealCoord
theorem _root_.solution (x : F) (w : InfinitePlace F) :
    coord F (algebraMap F (Ainf F) x) w = rho F w x := by
  have h : ((coord F (algebraMap F (Ainf F) x) w : ℝ) : ℂ) = ((rho F w x : ℝ) : ℂ) := by
    rw [rho_coe, coord_apply, InfiniteAdeleRing.algebraMap_apply, ringEquivRealOfIsReal_apply,
      extensionEmbeddingOfIsReal_apply]
    exact extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)
  exact Complex.ofReal_injective h
end GlobalTheory.CompanionTheory.SW.RealCoord
