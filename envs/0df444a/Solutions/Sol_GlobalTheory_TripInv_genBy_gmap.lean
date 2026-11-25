-- Prove2me | solution 1 for GlobalTheory.TripInv.genBy_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:28.205975+00:00
-- url     : https://prove2.me/submissions/a1d45db5-01bc-4aa0-b5e1-de25667a32d9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_gmap_eq

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
theorem _root_.solution (s : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} {j : ℕ} (h : GenBy A B j) :
    GenBy (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) j := by
  classical
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨t.image s, (Finset.card_image_le).trans ht, ?_⟩
  rw [gmap_eq, gmap_eq, Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl
end GlobalTheory.TripInv
