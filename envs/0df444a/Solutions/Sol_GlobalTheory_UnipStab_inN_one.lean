-- Prove2me | solution 1 for GlobalTheory.UnipStab.inN_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:56:30.978+00:00
-- url     : https://prove2.me/submissions/e09dda5b-ad42-4743-adcb-b15eb5da1626

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairCommonUnipotentStabiliserSummary
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
open GlobalTheory GlobalTheory.UnipStab
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
variable {F}
open NumberField
open scoped Pointwise ENNReal Classical
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  {H : _root_.Formalism.HermitianLatticeCounting.S6.HermSpace K V} {r : ℕ} (F : _root_.Formalism.HermitianLatticeCounting.S6.FlagD H r)
variable {F}
namespace GlobalTheory.UnipStab
namespace _root_.GlobalTheory.UnipStab
theorem _root_.solution : F.InN ((1 : V ≃ₗ[K] V) : V →ₗ[K] V) := by
  unfold _root_.Formalism.HermitianLatticeCounting.S6.FlagD.InN
  refine ⟨fun x y => rfl, (1 : V ≃ₗ[K] V).bijective, fun a => ?_, fun y _ => ?_⟩ <;>
    simp [LinearEquiv.coe_coe]
end _root_.GlobalTheory.UnipStab
end GlobalTheory.UnipStab
