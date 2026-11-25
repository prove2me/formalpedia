-- Prove2me | solution 1 for GlobalTheory.TripInv.tr_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:08.846488+00:00
-- url     : https://prove2.me/submissions/338cbd7a-7df3-40ee-8c2c-adf787f29b02

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_gmap_injective
import Theorems.Thm_GlobalTheory_TripInv_pmap_injective
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
theorem _root_.solution (s : V ≃ₗ[K] V) : Function.Injective (tr (K := K) s) := by
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨⟨a1', a2'⟩, ⟨b1', b2'⟩, η'⟩ h
  simp only [tr, Prod.mk.injEq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, e4⟩, e5⟩ := h
  simp only [gmap_injective s e1, pmap_injective s e2, gmap_injective s e3, pmap_injective s e4,
    mul_left_cancel (mul_right_cancel e5)]
end GlobalTheory.TripInv
