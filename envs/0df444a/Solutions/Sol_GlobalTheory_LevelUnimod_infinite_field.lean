-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.infinite_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:24.229443+00:00
-- url     : https://prove2.me/submissions/fccbc0a0-33d6-464f-9e58-f25e34022f19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_neBot_punctured
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open scoped Topology
open GlobalTheory GlobalTheory.LevelUnimod
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution : Infinite k := by
  haveI := neBot_punctured (k := k)
  haveI := t2Space k
  by_contra h
  haveI : Finite k := not_infinite_iff_finite.1 h
  exact (neBot_punctured (k := k)).ne (discreteTopology_iff_nhds_ne.1 inferInstance 0)
end GlobalTheory.LevelUnimod
