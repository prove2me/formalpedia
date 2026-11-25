-- Prove2me | solution 1 for GlobalTheory.TripInv.isModIso_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:08.086196+00:00
-- url     : https://prove2.me/submissions/2afd014e-0a65-4d7e-9924-375576876cd2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_mem_gmap
import Theorems.Thm_GlobalTheory_TripInv_mem_pmap
import Theorems.Thm_GlobalTheory_TripInv_smulLat_gmap
import Theorems.Thm_GlobalTheory_TripInv_prod_gmap
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
theorem _root_.solution {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : 𝓞 K}
    {M L : Submodule (𝓞 K) V} {Γ : Submodule (𝓞 K) (V × V)} (h : IsModIso H g M L Γ) :
    IsModIso H g (Formalism.HermitianLatticesTheory.gmap s M) (Formalism.HermitianLatticesTheory.gmap s L) (pmap s Γ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prod_gmap]
    exact Submodule.map_mono h1
  · rw [smulLat_gmap, smulLat_gmap, prod_gmap]
    exact Submodule.map_mono h2
  · intro y' hy'
    rw [mem_gmap] at hy'
    obtain ⟨y, hy⟩ := h3 _ hy'
    exact ⟨s y, by simpa [mem_pmap] using hy⟩
  · intro y hy
    rw [mem_gmap] at hy
    obtain ⟨y', hy'⟩ := h4 _ hy
    exact ⟨s y', by simpa [mem_pmap] using hy'⟩
  · intro y hy
    rw [mem_pmap] at hy
    rw [smulLat_gmap, mem_gmap]
    exact h5 _ (by simpa using hy)
  · intro y' hy'
    rw [mem_pmap] at hy'
    rw [smulLat_gmap, mem_gmap]
    exact h6 _ (by simpa using hy')
  · intro p hp q hq
    rw [mem_pmap] at hp hq
    obtain ⟨t, ht⟩ := h7 _ hp _ hq
    exact ⟨t, by simpa only [isom_symm hs] using ht⟩
end GlobalTheory.TripInv
