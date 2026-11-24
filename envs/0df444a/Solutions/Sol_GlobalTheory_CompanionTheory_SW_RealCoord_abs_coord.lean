-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.abs_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:30:45.392881+00:00
-- url     : https://prove2.me/submissions/b8062fc1-6386-4a53-ba41-4584edca6e0e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume

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
theorem _root_.solution (y : Ainf F) (w : InfinitePlace F) : |coord F y w| = ‖y w‖ := by
  have h := (isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).isometry.norm_map_of_map_zero
    (map_zero (ringEquivRealOfIsReal (IsTotallyReal.isReal w))) (y w)
  exact h
end GlobalTheory.CompanionTheory.SW.RealCoord
