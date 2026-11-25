-- Prove2me | solution 1 for GlobalTheory.TripInv.isDat_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:34:39.323352+00:00
-- url     : https://prove2.me/submissions/79874f4a-4e19-4a00-bff4-c0b152676e28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_fixLat_pmap
import Theorems.Thm_GlobalTheory_TripInv_idx_gmap
import Theorems.Thm_GlobalTheory_TripInv_isIntLat_gmap
import Theorems.Thm_GlobalTheory_TripInv_discN_gmap
import Theorems.Thm_GlobalTheory_TripInv_genBy_gmap
import Theorems.Thm_GlobalTheory_TripInv_isModIso_gmap

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
theorem _root_.solution {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : ℕ} {L : Submodule (𝓞 K) V}
    {j x : ℕ} {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (h : IsDat H g L j x d) :
    IsDat H g (Formalism.HermitianLatticesTheory.gmap s L) j x (Formalism.HermitianLatticesTheory.gmap s d.1, pmap s d.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isIntLat_gmap hs h1, ?_, isModIso_gmap hs h3, ?_, ?_⟩
  · rw [discN_gmap hs, discN_gmap hs, h2]
  · rw [fixLat_pmap, idx_gmap, h4]
  · rw [fixLat_pmap]
    exact genBy_gmap s h5
end GlobalTheory.TripInv
