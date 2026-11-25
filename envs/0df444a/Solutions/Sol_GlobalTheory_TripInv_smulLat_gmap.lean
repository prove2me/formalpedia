-- Prove2me | solution 1 for GlobalTheory.TripInv.smulLat_gmap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:38.507295+00:00
-- url     : https://prove2.me/submissions/c268d16c-6185-4c13-a7f2-7729f7acc2bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_AdaptSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometricEmbeddedDatumPairsEncardIsometrySmul
import Theorems.Thm_GlobalTheory_TripInv_gmap_eq
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
namespace GlobalTheory.TripInv
theorem _root_.solution (s : V ≃ₗ[K] V) (g : 𝓞 K) (M : Submodule (𝓞 K) V) :
    smulLat g (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (smulLat g M) := by
  rw [gmap_eq, gmap_eq, smulLat, smulLat, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  rw [← algebraMap_smul K g x, ← algebraMap_smul K g (s x), map_smul]
end GlobalTheory.TripInv
