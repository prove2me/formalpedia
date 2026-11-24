-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.modular_aut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:57:16.548593+00:00
-- url     : https://prove2.me/submissions/05031e09-fe6a-4959-a5c5-2f3238b5a176

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_smul_inj
import Theorems.Thm_GlobalTheory_LevelUnimod_map_mul_right_eq

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
open scoped Pointwise NNReal ENNReal
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
omit [T2Space G]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution (e : G ≃* G) (hc : Continuous e) (hc' : Continuous e.symm) (g : G) :
    Measure.modularCharacter (e g) = Measure.modularCharacter g := by
  let μ : Measure G := Measure.haar
  haveI : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ hc hc'
  refine smul_inj (μ := μ.map e) ?_
  rw [← map_mul_right_eq, ← Measure.map_smul, ← map_mul_right_eq,
    Measure.map_map (measurable_mul_const _) hc.measurable, Measure.map_map hc.measurable (measurable_mul_const _)]
  congr 1
  funext x
  simp
end GlobalTheory.LevelUnimod
