-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.smul_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:26.564061+00:00
-- url     : https://prove2.me/submissions/17def822-6792-4bf0-86e6-ba2c30137fb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels

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
omit [SecondCountableTopology G] [T2Space G] [BorelSpace G]
namespace GlobalTheory.LevelUnimod
theorem _root_.solution {μ : Measure G} [μ.IsHaarMeasure] {a b : ℝ≥0} (h : a • μ = b • μ) : a = b := by
  obtain ⟨K, hK, h1⟩ := exists_compact_mem_nhds (1 : G)
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.coe_nnreal_smul_apply] at h2
  exact_mod_cast (ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ h1).ne' hK.measure_lt_top.ne).1 h2
end GlobalTheory.LevelUnimod
