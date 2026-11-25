-- Prove2me | solution 1 for GlobalTheory.DegCnt.StabInv.Keeps.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:14:36.800797+00:00
-- url     : https://prove2.me/submissions/d7f93eaa-31eb-45f4-96d0-28ca0439f953

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CommonUnipotentStabiliserPreservesTermsAndDatum
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_Keeps_flagX
import Theorems.Thm_GlobalTheory_DegCnt_StabInv_apply_inv
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
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.StabInv
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.StabInv
namespace Keeps
theorem _root_.solution {F : FlagD H r} {s : V ≃ₗ[K] V} (hs : Keeps F s) : Keeps F s⁻¹ := by
  refine ⟨fun x y => ?_, fun a x => ?_, fun a => ?_, fun y hy => ?_⟩
  · rw [← hs.iso, apply_inv, apply_inv]
  · rw [← hs.flag, apply_inv]
  · rw [← hs.flag, map_sub, apply_inv]
    simpa using neg_mem (hs.vec a)
  · rw [← hs.flagX, map_sub, apply_inv]
    simpa using neg_mem (hs.mid y hy)
end Keeps
end GlobalTheory.DegCnt.StabInv
