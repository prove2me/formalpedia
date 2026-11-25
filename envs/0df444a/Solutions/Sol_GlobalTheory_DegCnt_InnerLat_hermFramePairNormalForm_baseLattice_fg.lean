-- Prove2me | solution 1 for GlobalTheory.DegCnt.InnerLat.hermFramePairNormalForm_baseLattice_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:46.671141+00:00
-- url     : https://prove2.me/submissions/b24d8b2c-8223-465c-8aee-edbf8c1f44fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive
import Theorems.Thm_GlobalTheory_DegCnt_InnerLat_ipow_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.InnerLat
open GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}
namespace GlobalTheory.DegCnt.InnerLat
theorem _root_.solution (N : NF H r) : N.P0.FG := by
  have h1 : (1 : Submodule (𝓞 K) K).FG := by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  exact (((Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _).sup
    (Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _)).sup (h1.map _)).sup
    (Submodule.fg_iSup _ fun _ => Submodule.fg_iSup _ fun _ => (ipow_fg _ _).map _)
end GlobalTheory.DegCnt.InnerLat
