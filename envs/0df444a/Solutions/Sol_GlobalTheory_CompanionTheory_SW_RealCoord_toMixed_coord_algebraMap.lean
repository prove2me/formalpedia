-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.toMixed_coord_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:08:14.710606+00:00
-- url     : https://prove2.me/submissions/83286e50-8e28-4f37-ab79-d89ce7e3e2f1

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RealCoord_coord_algebraMap

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
theorem _root_.solution (x : F) :
    toMixed F (coord F (algebraMap F (Ainf F) x)) = mixedEmbedding F x := by
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  funext w
  rw [mixedEmbedding.mixedEmbedding_apply_isReal]
  exact coord_algebraMap F x w.1
end GlobalTheory.CompanionTheory.SW.RealCoord
