-- Prove2me | solution 1 for GlobalTheory.LevelUnimod.modular_bdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:41:25.056917+00:00
-- url     : https://prove2.me/submissions/b4bb52cc-402d-4b3a-9943-3219cf878e70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_GlCharacterEqOneOfTransposeInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsUnimodularBlockUpperTriangularSymmetricLevels
import Theorems.Thm_GlobalTheory_LevelUnimod_map_mul_right_eq
import Theorems.Thm_GlobalTheory_StepData_IntM_mul


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
namespace GlobalTheory.LevelUnimod
theorem _root_.solution : ∃ K ∈ nhds (1 : G), ∃ C : ℝ≥0, ∀ g ∈ K, Measure.modularCharacter g ≤ C := by
  let μ : Measure G := Measure.haar
  obtain ⟨K, hK, h1⟩ := exists_compact_mem_nhds (1 : G)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ h1).ne'
  have ht : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have ht2 : μ (K * K⁻¹) ≠ ⊤ := (hK.mul hK.inv).measure_lt_top.ne
  refine ⟨K, h1, (μ (K * K⁻¹) / μ K).toNNReal, fun g hg => ?_⟩
  have h2 := congrArg (fun m : Measure G => m K) (map_mul_right_eq μ g)
  simp only [Measure.coe_nnreal_smul_apply] at h2
  rw [Measure.map_apply (measurable_mul_const _) hK.isClosed.measurableSet] at h2
  have h3 : μ ((fun x => x * g) ⁻¹' K) ≤ μ (K * K⁻¹) :=
    measure_mono fun x hx => ⟨x * g, hx, g⁻¹, Set.inv_mem_inv.2 hg, by simp⟩
  rw [h2] at h3
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ENNReal.div_ne_top ht2 h0)]
  exact (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht)).2 h3
end GlobalTheory.LevelUnimod
