-- Prove2me | solution 1 for GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:51.466737+00:00
-- url     : https://prove2.me/submissions/f52a451c-2d7f-4423-ac61-5095233c2dd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmulStatement
import Theorems.Thm_GlobalTheory_TripInv_trip_encard_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  first | exact @GlobalTheory.TripInv.trip_encard_smul | exact GlobalTheory.TripInv.trip_encard_smul | (intros; apply GlobalTheory.TripInv.trip_encard_smul <;> assumption)
end _root_.GlobalTheory.T
