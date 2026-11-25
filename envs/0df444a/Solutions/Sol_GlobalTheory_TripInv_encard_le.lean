-- Prove2me | solution 1 for GlobalTheory.TripInv.encard_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:22.771907+00:00
-- url     : https://prove2.me/submissions/4e5643b0-7d47-4938-b7e4-1fe27605aa26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_tr_injective
import Theorems.Thm_GlobalTheory_TripInv_tr_mapsTo

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
noncomputable section
open GlobalTheory GlobalTheory.TripInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V}
namespace GlobalTheory.TripInv
theorem _root_.solution (HW : HermSpace K V) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) V) :
    (Trip HW g L j x x').encard ≤ (Trip HW g (s • L) j x x').encard :=
  Set.encard_le_encard_of_injOn (tr_mapsTo s.2 g L j x x') (tr_injective _).injOn
end GlobalTheory.TripInv
