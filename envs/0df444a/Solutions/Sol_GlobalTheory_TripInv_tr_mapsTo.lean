-- Prove2me | solution 1 for GlobalTheory.TripInv.tr_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:56:07.660512+00:00
-- url     : https://prove2.me/submissions/397ef1d1-07da-4705-8db9-7946b147d9c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_mem_pmap
import Theorems.Thm_GlobalTheory_TripInv_isDat_gmap
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_inv
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HermLat_mem_isomGrp
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
theorem _root_.solution {s : V ≃ₗ[K] V} (hs : s ∈ isomGrp H) (g : ℕ) (L : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set.MapsTo (tr s) (Trip H g L j x x') (Trip H g (Formalism.HermitianLatticesTheory.gmap s L) j x x') := by
  have hs' := (mem_isomGrp H s).1 hs
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨hA, hB, hη, him, hgr⟩
  refine ⟨isDat_gmap hs' hA, isDat_gmap hs' hB, ?_, ?_, ?_⟩
  · exact (isomGrp H).mul_mem ((isomGrp H).mul_mem hs hη) ((isomGrp H).inv_mem hs)
  · change Formalism.HermitianLatticesTheory.gmap (s * η * s⁻¹) (Formalism.HermitianLatticesTheory.gmap s b1) = Formalism.HermitianLatticesTheory.gmap s a1
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv, Formalism.HermitianLatticesTheory.genusBasic_gmap_mul]
    exact congrArg _ him
  · intro y y'
    change (y, y') ∈ pmap s b2 ↔ (s (η (s.symm y)), y') ∈ pmap s a2
    rw [mem_pmap, mem_pmap]
    simpa using hgr (s.symm y) (s.symm y')
end GlobalTheory.TripInv
