-- Prove2me | solution 1 for GlobalTheory.TripInv.isIntLat_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:20.224236+00:00
-- url     : https://prove2.me/submissions/04402171-3fc6-4911-aa01-938cd68a64c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_gmap_eq
import Theorems.Thm_GlobalTheory_TripInv_mem_gmap
import Theorems.Thm_GlobalTheory_TripInv_isom_symm
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.TripInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V}
namespace GlobalTheory.TripInv
theorem _root_.solution {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {M : Submodule (𝓞 K) V}
    (hM : GlobalTheory.Mass.IsIntLat H.B.flip M) : GlobalTheory.Mass.IsIntLat H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) := by
  obtain ⟨hL, hI⟩ := hM
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [gmap_eq]
    exact hL.fg.map _
  · rw [gmap_eq, Submodule.map_coe]
    change Submodule.span K ((s : V →ₗ[K] V) '' (M : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top]
    exact LinearEquiv.range s
  · intro x hx y hy
    rw [mem_gmap] at hx hy
    have := hI _ hx _ hy
    simp only [LinearMap.flip_apply] at this ⊢
    rwa [isom_symm hs] at this
end GlobalTheory.TripInv
