-- Prove2me | solution 1 for GlobalTheory.TripInv.trip_encard_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:59.76516+00:00
-- url     : https://prove2.me/submissions/236a817d-d30f-4a5f-a451-e54898920631

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_encard_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_inv


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
theorem _root_.solution : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip)
    (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  intro K W _ _ _ _ _ _ _ HW g j x x' s L
  refine le_antisymm ?_ (encard_le HW g j x x' s L)
  have := encard_le HW g j x x' s⁻¹ (s • L)
  exact this.trans_eq (congrArg (fun M => (Trip HW g M j x x').encard)
    (Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (s : W ≃ₗ[K] W) L))
end GlobalTheory.TripInv
