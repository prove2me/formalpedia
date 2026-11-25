-- Prove2me | solution 1 for GlobalTheory.TripInv.discN_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:03:36.784527+00:00
-- url     : https://prove2.me/submissions/ff74e98e-cac2-4308-be82-4eb89beba5b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_idxN_gmap
import Theorems.Thm_GlobalTheory_TripInv_dual_gmap

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
theorem _root_.solution {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.discN H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = GlobalTheory.Mass.discN H.B.flip M := by
  unfold GlobalTheory.Mass.discN
  rw [dual_gmap hs, idxN_gmap]
end GlobalTheory.TripInv
