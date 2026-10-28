-- Prove2me | solution 1 for OAI.HardSphere.Groups.physical_group_common_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:20:32.220948+00:00
-- url     : https://prove2.me/submissions/26b4bb0a-d551-4557-8bb1-a9c2489fcdc3

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_Groups_physicalBranchLaw_collision
import Theorems.Thm_OAI_HardSphere_Groups_physical_common_observed_estimates
import Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_probability

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Index
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Wiener.instIsProbabilityMeasureContinuousMapElemRealTimeBridgeLaw _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma coordinate_preserving (i : Index) :
    MeasurePreserving (fun ω : Noise ↦ ω i) law (gaussianReal 0 1) :=
  measurePreserving_eval_infinitePi _ _

lemma tent_at_zero (n : ℕ) (k : Fin (2 ^ n)) : tent n k 0 = 0 := by
  simp only [tent, mul_zero, zero_sub, abs_neg]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (k:ℝ) + 1)]
  apply max_eq_left
  norm_num

lemma tent_at_one (n : ℕ) (k : Fin (2 ^ n)) : tent n k 1 = 0 := by
  have hk : (k : ℝ) + 1 ≤ (2:ℝ)^n := by exact_mod_cast k.isLt
  simp only [tent, mul_one, pow_succ]
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (2:ℝ)^n*2-(2*(k:ℝ)+1))]
  exact max_eq_left (by linarith)

lemma level_at_zero (n : ℕ) (ω : Noise) : level n ω 0 = 0 := by
  simp [level, tentMap, tent_at_zero]

lemma level_at_one (n : ℕ) (ω : Noise) : level n ω 1 = 0 := by
  simp [level, tentMap, tent_at_one]

lemma path_at_zero (ω : Noise) : path ω 0 = 0 := by
  by_cases h : Summable (fun n ↦ level n ω)
  · simp only [path, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
      smul_eq_mul]
    change ω (.inl ()) * 0 + _ = 0
    rw [← ContinuousMap.tsum_apply h]
    simp [level_at_zero]
  · simp [path, tsum_eq_zero_of_not_summable h]

lemma path_at_one (ω : Noise) : path ω 1 = ω (.inl ()) := by
  by_cases h : Summable (fun n ↦ level n ω)
  · simp only [path, ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.coe_mk,
      smul_eq_mul]
    change ω (.inl ()) * 1 + _ = _
    rw [← ContinuousMap.tsum_apply h]
    simp [level_at_one]
  · simp [path, tsum_eq_zero_of_not_summable h]

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PartialIndex
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.coordinateWiener_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

lemma independent_coordinates : iIndepFun (fun i ω ↦ ω i) law :=
  iIndepFun_infinitePi (fun _ ↦ measurable_id)

lemma independent_base_rest : IndepFun (fun ω : Noise ↦ ω (.inl ())) rest law := by
  classical
  apply IndepFun.indepFun_process (measurable_pi_apply _) (fun i ↦ measurable_pi_apply _)
  intro I
  let S : Finset Index := {.inl ()}
  let T : Finset Index := I.image Sum.inr
  have hd : Disjoint S T := by simp [S,T]
  have h := iIndepFun.indepFun_finset S T hd independent_coordinates (fun i ↦ measurable_pi_apply i)
  let a : S := ⟨.inl (), by simp [S]⟩
  let b (i : I) : T := ⟨.inr i.val, Finset.mem_image.mpr ⟨i.val,i.property,rfl⟩⟩
  exact h.comp (measurable_pi_apply a)
    (Measurable.of_eval fun coordinate ↦ measurable_pi_apply (b coordinate))

lemma independent_base_bridge : IndepFun (fun ω : Noise ↦ ω (.inl ())) bridge law :=
  independent_base_rest.comp measurable_id measurable_bridgeMap

lemma bridge_eq (ω : Noise) : bridge ω = ∑' n, level n ω := by
  simp only [bridge, bridgeMap, path, embedRest, Sum.elim_inl, zero_smul, zero_add]
  congr 1

lemma path_decomposition (ω : Noise) : path ω = ω (.inl ()) • linearPath + bridge ω := by
  rw [bridge_eq]
  rfl

lemma bridge_at_zero (ω : Noise) : bridge ω 0 = 0 := path_at_zero _
lemma bridge_at_one (ω : Noise) : bridge ω 1 = 0 := path_at_one _

lemma endpoint_bridge_law :
    HasLaw (fun ω : Noise ↦ (ω (.inl ()), bridge ω))
      ((gaussianReal 0 1).prod bridgeLaw) law := by
  refine ⟨((measurable_pi_apply _).prodMk measurable_bridge).aemeasurable, ?_⟩
  rw [independent_base_bridge.map_prod_eq_prod_map_map (measurable_pi_apply _).aemeasurable
    measurable_bridge.aemeasurable, (coordinate_preserving (.inl ())).map_eq]
  rfl

lemma wiener_disintegration : wiener = ((gaussianReal 0 1).prod bridgeLaw).map
    (fun p : ℝ × C(Time,ℝ) ↦ p.1 • linearPath + p.2) := by
  rw [wiener, ← endpoint_bridge_law.map_eq,
    Measure.map_map (by fun_prop) ((measurable_pi_apply _).prodMk measurable_bridge)]
  congr 1
  funext ω
  exact path_decomposition ω

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_Chi
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma dist_coord_le_torusDistance (L : Length) (x y : Torus L) (j : Fin 3) :
    dist (x j) (y j) ≤ torusDistance L x y := by
  calc
    _ = Real.sqrt (dist (x j) (y j)^2) := (Real.sqrt_sq (dist_nonneg)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun k _ ↦ sq_nonneg (dist (x k) (y k))) (Finset.mem_univ j))

end HardSphere.CellOrbital

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

lemma euclideanTorusPoint_dist (L : Length) (x y : Torus L) :
    dist (euclideanTorusPoint L x) (euclideanTorusPoint L y)=torusDistance L x y :=
  PiLp.dist_eq_of_L2 _ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CenteredCircleLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

lemma torusDistance_triangle' (L : Length) (x y z : Torus L) :
    torusDistance L x z≤torusDistance L x y+torusDistance L y z := by
  simpa only [euclideanTorusPoint_dist] using dist_triangle
    (euclideanTorusPoint L x) (euclideanTorusPoint L y) (euclideanTorusPoint L z)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathDiameter
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener
attribute [local irreducible] torusDistance freeTrajectory

lemma intervalDistance_le {L : Length} (a b s q : Time) (ω : ConfigurationPath 1 L) :
    torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ intervalDiameter a b ω := by
  exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm (diameterMap a b ω) (s,q))

lemma intervalDiameter_le {L : Length} (a b : Time) (ω : ConfigurationPath 1 L) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s q, torusDistance L (ω (intervalTime a b s) 0) (ω (intervalTime a b q) 0) ≤ R) :
    intervalDiameter a b ω ≤ R := by
  apply (ContinuousMap.norm_le _ hR).mpr
  intro p
  change |torusDistance L _ _| ≤ R
  rw [abs_of_nonneg (by unfold torusDistance; positivity)]
  exact h p.1 p.2

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GroundPathWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section
variable {N : ℕ} {L : Length} {a t : ℝ}

lemma groundPathWeight_measurable (u : Jet N L) (t : ℝ) : Measurable (groundPathWeight u t) := by
  exact measurable_const.mul (((Lp.stronglyMeasurable u.1).measurable.comp
    (continuous_eval_const (0:Time)).measurable).norm.mul
    (((Lp.stronglyMeasurable u.1).measurable.comp (continuous_eval_const (1:Time)).measurable).norm))

end
end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_PathLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

lemma liftDiff_coe {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (j : Fin 3) (s q : Time) :
    ((ζ j s-ζ j q : ℝ) : AddCircle L.val)=ω s 0 j-ω q 0 j := by
  rw [AddCircle.coe_sub,hζ j s,hζ j q]

lemma liftDiff_lt_half_period {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2)
    (j : Fin 3) (s q : Time) :
    |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| < L.val/2 := by
  by_contra h
  have hf : Continuous (fun v ↦ |ζ j (intervalTime a b v)-ζ j (intervalTime a b q)|) :=
    (((ζ j).continuous.comp (intervalTime_continuous a b)).sub continuous_const).abs
  obtain ⟨v,hv⟩ := intermediate_value_univ q s hf ⟨by simp; exact div_nonneg L.property.le (by norm_num),
    le_of_not_gt h⟩
  dsimp only at hv
  have ha : |ζ j (intervalTime a b v)-ζ j (intervalTime a b q)| ≤ |L.val|/2 := by
    rw [hv,abs_of_pos L.property]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ha
  rw [liftDiff_coe hζ,← dist_eq_norm,hv] at he
  have hb := (CellOrbital.dist_coord_le_torusDistance L (ω (intervalTime a b v) 0)
    (ω (intervalTime a b q) 0) j).trans (intervalDistance_le a b v q ω)
  linarith

lemma liftDiff_norm_eq {L : Length} {ω : ConfigurationPath 1 L} {ζ : EuclideanPath}
    (hζ : IsPathLift ω ζ) (a b : Time) (hsmall : intervalDiameter a b ω < L.val/2)
    (j : Fin 3) (s q : Time) :
    dist (ω (intervalTime a b s) 0 j) (ω (intervalTime a b q) 0 j)=
      |ζ j (intervalTime a b s)-ζ j (intervalTime a b q)| := by
  have hle := (liftDiff_lt_half_period hζ a b hsmall j s q).le
  rw [← abs_of_pos L.property] at hle
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hle
  simpa only [liftDiff_coe hζ,←dist_eq_norm] using he

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CenteredCell
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centered_rep_abs (L : Length) (x : AddCircle L.val) :
    |((AddCircle.equivIco L.val (-L.val/2)) x).val|=‖x‖ := by
  let t := (AddCircle.equivIco L.val (-L.val/2)) x
  have ht : |t.val| ≤ |L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    constructor <;> linarith [t.property.1,t.property.2]
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr ht
  rw [AddCircle.coe_equivIco] at he
  exact he.symm

end
end HardSphere.CellOrbital

namespace HardSphere.CellOrbital
open MeasureTheory Set Filter
noncomputable section

lemma centeredCell_image {L : Length} (hL : 1 ≤ L.val) (c x : Torus L) :
    x∈centeredCell L c ↔ ∀ j, ∃ t∈Ico (-1/2:ℝ) (1/2), (t : AddCircle L.val)=x j-c j := by
  constructor
  · intro hx j
    exact ⟨_,hx j,AddCircle.coe_equivIco⟩
  · intro hx j
    obtain ⟨t,ht,he⟩ := hx j
    have ht' : t∈Ico (-L.val/2) (-L.val/2+L.val) := by constructor <;> linarith [ht.1,ht.2]
    rw [← he,AddCircle.equivIco_coe_eq ht']
    exact ht

lemma fin_circle_dist {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) {v w : Fin K} (hvw : v≠w) :
    1 ≤ dist ((v:ℝ) : AddCircle L.val) ((w:ℝ) : AddCircle L.val) := by
  have hi (v : Fin K) : (v:ℝ)∈Ico (0:ℝ) (0+L.val) := by
    constructor
    · positivity
    · simpa only [zero_add,hL] using (show (v:ℝ)<(K:ℝ) by exact_mod_cast v.isLt)
  have hne : ((v:ℝ):AddCircle L.val)≠((w:ℝ):AddCircle L.val) := by
    intro he
    have he' := (AddCircle.coe_eq_coe_iff_of_mem_Ico (hi v) (hi w)).mp he
    exact hvw (Fin.ext (by exact_mod_cast he'))
  let z : ℤ := (v.val:ℤ)-(w.val:ℤ)-round (L.val⁻¹*((v:ℝ)-(w:ℝ)))*(K:ℤ)
  have hd : dist ((v:ℝ):AddCircle L.val) ((w:ℝ):AddCircle L.val)=|(z:ℝ)| := by
    rw [dist_eq_norm,← QuotientAddGroup.mk_sub,AddCircle.norm_eq]
    dsimp [z]
    push_cast
    rw [hL]
  have hz : z≠0 := by
    intro hz
    apply hne
    apply dist_eq_zero.mp
    rw [hd,hz,Int.cast_zero,abs_zero]
  have ha : (1:ℤ)≤|z| := by
    have hh : 0 < |z| := abs_pos.mpr hz
    omega
  rw [hd,← Int.cast_abs]
  exact_mod_cast ha

end
end HardSphere.CellOrbital

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_CellPartition
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace HardSphere.CellOrbital

lemma gridHome_mem {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K) (x : Torus L) :
    x∈centeredCell L (gridCenter L (gridHome hL x)) := by
  apply (centeredCell_image (by rw [hL]; exact_mod_cast hK) _ _).mpr
  intro j
  let z := (AddCircle.equivIco L.val 0) (x j+(1/2:ℝ))
  have hz0 : 0≤z.val := z.property.1
  let n : ℕ := ⌊z.val⌋₊
  refine ⟨z.val-(n:ℝ)-1/2,⟨?_,?_⟩,?_⟩
  · linarith [Nat.floor_le hz0]
  · have hh := Nat.lt_floor_add_one z.val
    dsimp [n]
    linarith
  · have he : (z.val : AddCircle L.val)=x j+((1/2:ℝ):AddCircle L.val) := AddCircle.coe_equivIco
    change ((z.val-(n:ℝ)-1/2:ℝ):AddCircle L.val)=x j-((n:ℝ):AddCircle L.val)
    simp only [QuotientAddGroup.mk_sub]
    rw [he]
    abel

lemma centeredCell_disjoint {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {v w : Fin 3→Fin K} (hvw : v≠w) : Disjoint (centeredCell L (gridCenter L v)) (centeredCell L (gridCenter L w)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,hj⟩ : ∃j,v j≠w j := by
    by_contra h
    push Not at h
    exact hvw (funext h)
  have h1 : 1≤L.val := by rw [hL]; exact_mod_cast hK
  obtain ⟨s,hs,hes⟩ := (centeredCell_image h1 _ _).mp hx j
  obtain ⟨t,ht,het⟩ := (centeredCell_image h1 _ _).mp hy j
  have he : gridCenter L v j-gridCenter L w j=((t-s:ℝ):AddCircle L.val) := by
    rw [QuotientAddGroup.mk_sub,het,hes]
    abel
  have ha : |t-s|<1 := by rw [abs_lt]; constructor <;> linarith [ht.1,ht.2,hs.1,hs.2]
  have hd : dist (gridCenter L v j) (gridCenter L w j)<1 := by
    rw [dist_eq_norm,he]
    exact lt_of_le_of_lt (QuotientAddGroup.norm_mk_le_norm (m:=t-s)) (by simpa only [Real.norm_eq_abs] using ha)
  exact (not_lt_of_ge (fin_circle_dist hL hj)) hd

lemma gridHome_eq_iff {K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (x : Torus L) (v : Fin 3→Fin K) : gridHome hL x=v ↔ x∈centeredCell L (gridCenter L v) := by
  constructor
  · intro h; exact h ▸ gridHome_mem hL hK x
  · intro hx
    by_contra h
    exact Set.disjoint_left.mp (centeredCell_disjoint hL hK h) (gridHome_mem hL hK x) hx

end HardSphere.CellOrbital

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_Allocation
attribute [-instance] _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Sampling.siteAllocationKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Sampling
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_large (E : Finset I) (m : ℕ) (h : m≤E.card)
    [Nonempty (Fin m↪E)] :
    allocationPMF E m=(PMF.uniformOfFintype (Fin m↪E)).map (fun f ↦ some (f.trans (Function.Embedding.subtype _))) := by
  simp [allocationPMF,h]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_small (E : Finset I) (m : ℕ) (h : ¬m≤E.card) :
    allocationPMF E m=PMF.pure none := by simp [allocationPMF,h]

omit [Fintype I] [DecidableEq I] in
lemma allocationPMF_support (E : Finset I) (m : ℕ) (a : Allocation m I)
    (h : a∈(allocationPMF E m).support) :
    ∀f,a=some f→∀k,f k∈E := by
  classical
  by_cases hm : m≤E.card
  · have : Nonempty (Fin m↪E) := Function.Embedding.nonempty_of_card_le (by simpa using hm)
    rw [allocationPMF_large E m hm,PMF.support_map] at h
    obtain ⟨g,_,rfl⟩ := h
    intro f hf k
    have he : g.trans (Function.Embedding.subtype _)=f := Option.some.inj hf
    exact he ▸ (g k).property
  · rw [allocationPMF_small E m hm,PMF.support_pure] at h
    have ha : a=none := h
    simp only [ha,reduceCtorEq,false_implies,implies_true]

end HardSphere.Sampling

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeResidual
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace HardSphere
open Wiener

lemma reconstructCoordinates_continuous (N : ℕ) : Continuous (reconstructCoordinates N) := by
  unfold reconstructCoordinates
  fun_prop

lemma reconstructCoordinates_preserving (N : ℕ) :
    MeasurePreserving (reconstructCoordinates N) ((gaussianCoordinates N).prod (coordinateBridge N)) (coordinateWiener N) := by
  refine ⟨(reconstructCoordinates_continuous N).measurable,?_⟩
  have h := measurePreserving_arrowProdEquivProdArrow ℝ C(Time,ℝ) (Direction N)
    (fun _ ↦ gaussianReal 0 1) (fun _ ↦ bridgeLaw)
  change (Measure.prod (Measure.pi (fun _ : Direction N ↦ gaussianReal 0 1))
    (Measure.pi (fun _ : Direction N ↦ bridgeLaw))).map _=Measure.pi (fun _ ↦ wiener)
  rw [←h.map_eq,Measure.map_map (reconstructCoordinates_continuous N).measurable h.measurable]
  change (Measure.pi (fun _ : Direction N ↦ (gaussianReal 0 1).prod bridgeLaw)).map
    (fun p j ↦ (p j).1 • linearPath+(p j).2)=_
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable (fun p : ℝ×C(Time,ℝ) ↦ p.1 • linearPath+p.2) from by fun_prop).aemeasurable)]
  simp_rw [←wiener_disintegration]

lemma bridge_endpoints : ∀ᵐ β ∂bridgeLaw, β (0:Time)=0 ∧ β (1:Time)=0 := by
  have hm : MeasurableSet {β : C(Time,ℝ) | β (0:Time)=0 ∧ β (1:Time)=0} :=
    ((isClosed_eq (continuous_eval_const (0:Time)) continuous_const).inter (isClosed_eq (continuous_eval_const (1:Time)) continuous_const)).measurableSet
  rw [bridgeLaw,ae_map_iff measurable_bridge.aemeasurable hm]
  exact ae_of_all _ (fun ω ↦ ⟨bridge_at_zero ω,bridge_at_one ω⟩)

lemma coordinateBridge_endpoints (N : ℕ) :
    ∀ᵐ β ∂coordinateBridge N, ∀j, β j (0:Time)=0 ∧ β j (1:Time)=0 := by
  apply ae_all_iff.mpr
  intro j
  exact (measurePreserving_eval (fun _ : Direction N ↦ bridgeLaw) j).quasiMeasurePreserving.ae bridge_endpoints

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GaussianMixture
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma leg_continuous (t : ℝ) (y u : Point) : Continuous (leg t y u) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Noise×Time ↦ fun j ↦ mean y u p.2 j+Real.sqrt (2*t)*p.1 j p.2)
  unfold mean
  fun_prop

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeStrongRegular
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma projectCurve_lift (L : Length) (f : C(Time,Point)) : IsPathLift (projectCurve L f) (pathCoordinates f) := by
  intro j s
  rfl

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeWindow
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking

lemma torusDistance_nonnegative (L : Length) (x y : Torus L) : 0≤torusDistance L x y := Real.sqrt_nonneg _

lemma nearestLift_project (L : Length) (v : Point) (x : Torus L) :
    projectPoint L (nearestLift L v x)=x := by
  ext j
  simp only [projectPoint,nearestLift,AddCircle.coe_add,AddCircle.coe_equivIco,sub_add_cancel]

lemma nearestLift_coord (L : Length) (v : Point) (x : Torus L) (j : Fin 3) :
    |nearestLift L v x j-v j|=dist (x j) (projectPoint L v j) := by
  let z := (AddCircle.equivIco L.val (-L.val/2)) (x j-(v j : AddCircle L.val))
  have hz : |z.val|≤|L.val|/2 := by
    rw [abs_of_pos L.property,abs_le]
    exact ⟨by linarith [z.property.1],by linarith [z.property.2]⟩
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr hz
  rw [AddCircle.coe_equivIco,←dist_eq_norm] at he
  simpa only [nearestLift,add_sub_cancel_right] using he.symm

lemma nearestLift_bound (L : Length) (v : Point) (x : Torus L) {R : ℝ}
    (h : torusDistance L x (projectPoint L v)≤R) : ‖nearestLift L v x-v‖≤R := by
  apply (pi_norm_le_iff_of_nonneg ((torusDistance_nonnegative L x _).trans h)).mpr
  intro j
  change |nearestLift L v x j-v j|≤R
  rw [nearestLift_coord]
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ j).trans h

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TrialCutoff
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma trialConfined_measurable (L : Length) (v : Point) : MeasurableSet {f | TrialConfined L v f} := by
  have he : {f | TrialConfined L v f}=⋂s : Time,{f : C(Time,Point) | ‖f s-v‖≤10 ∧ torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10} := by ext f; simp [TrialConfined]
  rw [he]
  apply IsClosed.measurableSet
  apply isClosed_iInter
  intro s
  change IsClosed ({f : C(Time,Point) | ‖f s-v‖≤10} ∩ {f | torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10})
  apply IsClosed.inter
  · exact isClosed_le ((continuous_eval_const s).sub continuous_const).norm continuous_const
  · apply isClosed_le _ continuous_const
    unfold torusDistance projectPoint
    fun_prop

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSuccess
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma trialCollision_closed {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    IsClosed {f | TrialCollision r ω f} := by
  let E : Set (C(Time,Point)×Time) := {p | torusDistance L (projectPoint L (p.1 p.2)) (ω p.2 0) ≤ r}
  have hE : IsClosed E := by
    apply isClosed_le _ continuous_const
    apply (torusDistance_continuous_pair L).comp (f := fun p : C(Time,Point)×Time ↦
      (projectPoint L (p.1 p.2),ω p.2 0))
    apply Continuous.prodMk
    · change Continuous (fun p : C(Time,Point)×Time ↦ fun j : Fin 3 ↦ (p.1 p.2 j:AddCircle L.val))
      fun_prop
    · exact (continuous_apply 0).comp (ω.continuous.comp continuous_snd)
  convert isClosedMap_fst_of_compactSpace E hE using 1
  all_goals try with_reducible_and_instances rfl
  ext f
  simp only [TrialCollision,mem_ofPred_eq,mem_image,E]
  exact ⟨fun ⟨s,hs⟩ ↦ ⟨(f,s),hs,rfl⟩,fun ⟨⟨g,s⟩,hs,hg⟩ ↦ by
    change g=f at hg
    subst g
    exact ⟨s,hs⟩⟩

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ReferenceHit
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff
attribute [local irreducible] torusDistance

lemma leg_endpoints_ae (t : ℝ) (y z : Point) :
    ∀ᵐβ ∂law,leg t y z β 0=y ∧ leg t y z β 1=z := by
  have he : ∀ᵐβ ∂law,∀j : Fin 3,β j 0=0 ∧ β j 1=0 := by
    exact ae_all_iff.mpr (fun j ↦ (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j).quasiMeasurePreserving.ae bridge_endpoints)
  filter_upwards [he] with β hβ
  constructor <;> ext j <;> simp [leg,mean,(hβ j).1,(hβ j).2]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_JointCollision
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

variable {I : Type*} [DecidableEq I] {L : Length}
  (S : I→Set C(Time,Point))

lemma physicalPairCheck_symmetric (r : ℝ) (f g : C(Time,Point)) :
    TrialCollision (L:=L) r (projectCurve L g) f ↔ TrialCollision r (projectCurve L f) g := by
  unfold TrialCollision
  apply exists_congr
  intro s
  change torusDistance L (projectPoint L (f s)) (projectPoint L (g s)) ≤ r ↔
    torusDistance L (projectPoint L (g s)) (projectPoint L (f s)) ≤ r
  rw [torusDistance_comm]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_FiberNormalize
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]

lemma fiberRestrict_apply (κ : Kernel W V) [IsSFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) (w : W) :
    fiberRestrict κ C w=(κ w).restrict {v | (w,v)∈C} := by
  have hm : Measurable (Function.uncurry (fun w : W ↦ fun v : V ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))) := by
    change Measurable (C.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    exact measurable_const.indicator hC
  rw [fiberRestrict,Kernel.withDensity_apply _ hm]
  have he : (fun v ↦ C.indicator (fun _ ↦ (1 : ℝ≥0∞)) (w,v))=
      {v | (w,v)∈C}.indicator (fun _ ↦ (1 : ℝ≥0∞)) := rfl
  rw [he]
  have hs : MeasurableSet {v : V | (w,v)∈C} := hC.preimage (measurable_const.prodMk measurable_id)
  exact withDensity_indicator_one hs

lemma fiberNormalize_mass (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) {w : W} (hw : 0<κ w {v | (w,v)∈C}) :
    fiberNormalize κ C w univ=1 := by
  change ((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) univ=1
  rw [fiberRestrict_apply κ hC,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hw.ne' (measure_ne_top _ _)

lemma fiberNormalize_fst (μ : Measure W) [SFinite μ] (κ : Kernel W V) [IsFiniteKernel κ]
    {C : Set (W×V)} (hC : MeasurableSet C)
    (hpos : ∀ᵐ w ∂μ,0<κ w {v | (w,v)∈C}) :
    (μ.compProd (fiberNormalize κ C)).map Prod.fst=μ := by
  ext B hB
  rw [Measure.map_apply measurable_fst hB,Measure.compProd_apply (hB.preimage measurable_fst)]
  have he : (fun w ↦ fiberNormalize κ C w ((fun v ↦ (w,v))⁻¹' (Prod.fst⁻¹' B)))=ᵐ[μ]
      B.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    filter_upwards [hpos] with w hw
    by_cases hb : w∈B
    · have hs : (fun v : V ↦ (w,v))⁻¹' (Prod.fst⁻¹' B)=univ := by ext v; simp [hb]
      rw [hs,fiberNormalize_mass κ hC hw,Set.indicator_of_mem hb]
    · have hs : (fun v : V ↦ (w,v))⁻¹' (Prod.fst⁻¹' B)=∅ := by ext v; simp [hb]
      rw [hs,measure_empty,Set.indicator_of_notMem hb]
  rw [lintegral_congr_ae he,lintegral_indicator_const hB,one_mul]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_FiberDisintegrate
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {W V : Type*} [MeasurableSpace W] [MeasurableSpace V]

lemma fiberRestrict_le (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)} (hC : MeasurableSet C) (w : W) :
    fiberRestrict κ C w≤κ w := by rw [fiberRestrict_apply κ hC]; exact Measure.restrict_le_self

lemma exposed_mass_positive (μ : Measure W) (κ : Kernel W V) [IsFiniteKernel κ]
    {C : Set (W×V)} (hC : MeasurableSet C) :
    ∀ᵐ w ∂μ.withDensity (fun w ↦ fiberRestrict κ C w univ),0<κ w {v | (w,v)∈C} := by
  rw [ae_withDensity_iff ((fiberRestrict κ C).measurable_coe MeasurableSet.univ)]
  exact ae_of_all _ fun w hw ↦ by
    rw [fiberRestrict_apply κ hC,Measure.restrict_apply_univ] at hw
    exact pos_iff_ne_zero.mpr hw

lemma fiber_rescale (κ : Kernel W V) [IsFiniteKernel κ] {C : Set (W×V)}
    (hC : MeasurableSet C) (w : W) (B : Set V) :
    (fiberRestrict κ C w univ) * (fiberNormalize κ C w B)=fiberRestrict κ C w B := by
  change (fiberRestrict κ C w univ) * (((fiberRestrict κ C w univ)⁻¹ • fiberRestrict κ C w) B)=_
  rw [Measure.smul_apply,smul_eq_mul,←mul_assoc]
  by_cases hz : fiberRestrict κ C w univ=0
  · have h0 : fiberRestrict κ C w=0 := Measure.measure_univ_eq_zero.mp hz
    simp [h0]
  · have hfin : fiberRestrict κ C w univ≠⊤ := ne_of_lt ((fiberRestrict_le κ hC w univ).trans_lt (measure_lt_top _ _))
    rw [ENNReal.mul_inv_cancel hz hfin,one_mul]

lemma fiber_disintegrate (μ : Measure W) [SFinite μ] (κ : Kernel W V) [IsFiniteKernel κ]
    {C : Set (W×V)} (hC : MeasurableSet C)
    [SFinite (μ.withDensity (fun w ↦ fiberRestrict κ C w univ))] :
    (μ.withDensity (fun w ↦ fiberRestrict κ C w univ)).compProd (fiberNormalize κ C)=
      (μ.compProd κ).restrict C := by
  ext B hB
  rw [Measure.compProd_apply hB,lintegral_withDensity_eq_lintegral_mul₀]
  · simp only [Pi.mul_apply]
    simp_rw [fiber_rescale κ hC]
    rw [Measure.restrict_apply hB,Measure.compProd_apply (hB.inter hC)]
    apply lintegral_congr
    intro w
    have hBw : MeasurableSet (Prod.mk w ⁻¹' B) := hB.preimage (measurable_const.prodMk measurable_id)
    rw [fiberRestrict_apply κ hC,Measure.restrict_apply hBw]
    rfl
  · exact ((fiberRestrict κ C).measurable_coe MeasurableSet.univ).aemeasurable
  · exact ((fiberNormalize κ C).measurable_kernel_prodMk_left hB).aemeasurable

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ProductExpose
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma blockGlue_preserving (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] :
    MeasurePreserving (blockGlue (E:=E) p)
      ((μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i)).prod (Measure.pi fun i : {i // p i} ↦ ν i))
      (μ.prod (Measure.pi ν)) := by
  have h₁ := measurePreserving_prodAssoc μ (Measure.pi fun i : {i // ¬p i} ↦ ν i) (Measure.pi fun i : {i // p i} ↦ ν i)
  have h₂ := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap
    (μ:=Measure.pi fun i : {i // ¬p i} ↦ ν i) (ν:=Measure.pi fun i : {i // p i} ↦ ν i))
  have h₃ := (MeasurePreserving.id μ).prod ((measurePreserving_piEquivPiSubtypeProd ν p).symm (MeasurableEquiv.piEquivPiSubtypeProd X p))
  exact h₃.comp (h₂.comp h₁)

omit [Fintype I] in
lemma blockGlue_measurable (p : I→Prop) [DecidablePred p] : Measurable (blockGlue (E:=E) (X:=X) p) :=
  measurable_fst.fst.prodMk ((MeasurableEquiv.piEquivPiSubtypeProd X p).symm.measurable.comp (measurable_snd.prodMk measurable_fst.snd))

lemma exposed_block_reconstruct (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] {B : Set (E×(∀i,X i))} (hB : MeasurableSet B)
    [SFinite (exposedLaw μ ν p B)] :
    ((exposedLaw μ ν p B).compProd
       (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (blockEvent p B))).map (blockGlue p)=
      (μ.prod (Measure.pi ν)).restrict B := by
  have hC : MeasurableSet (blockEvent p B) := hB.preimage (blockGlue_measurable p)
  have h := fiber_disintegrate (μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i))
    (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) hC
  change ((exposedLaw μ ν p B).compProd _).map _=_
  rw [show (exposedLaw μ ν p B).compProd (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (blockEvent p B))=
      ((μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i)).prod (Measure.pi fun i : {i // p i} ↦ ν i)).restrict (blockEvent p B) by simpa only [Measure.compProd_const,exposedLaw] using h]
  exact ((blockGlue_preserving μ ν p).restrict_preimage hB).map_eq

lemma exposed_block_positive (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] {B : Set (E×(∀i,X i))} (hB : MeasurableSet B) :
    ∀ᵐw ∂exposedLaw μ ν p B,0<(Measure.pi fun i : {i // p i} ↦ ν i) {v | blockGlue p (w,v)∈B} := by
  exact exposed_mass_positive (μ.prod (Measure.pi fun i : {i // ¬p i} ↦ ν i))
    (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i)) (hB.preimage (blockGlue_measurable p))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ProductNormalize
attribute [-instance] _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma conditioned_probability {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {S : Set A} (h : μ S≠0) : IsProbabilityMeasure (conditionedMeasure μ S) := by
  constructor
  simp only [conditionedMeasure,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel h (measure_ne_top _ _)

lemma pi_conditioned (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (S : ∀i,Set (X i)) (hS : ∀i,MeasurableSet (S i)) (hpos : ∀i,ν i (S i)≠0) :
    Measure.pi (fun i ↦ conditionedMeasure (ν i) (S i))=
      conditionedMeasure (Measure.pi ν) (univ.pi S) := by
  let : ∀i,IsProbabilityMeasure (conditionedMeasure (ν i) (S i)) := fun i ↦ conditioned_probability (ν i) (hpos i)
  apply Measure.pi_eq
  intro B hB
  simp only [conditionedMeasure,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hB),←Set.pi_inter_distrib,Measure.pi_pi,Measure.pi_pi]
  simp_rw [Measure.restrict_apply' (hS _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact ENNReal.prod_inv_distrib (fun i _ j _ _ ↦ Or.inl (hpos i))

lemma condition_product_factorization (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (S : ∀i,Set (X i)) (hS : ∀i,MeasurableSet (S i)) (hpos : ∀i,ν i (S i)≠0)
    (B : Set (∀i,X i)) (hB : MeasurableSet B) (hfull : (Measure.pi ν) (B∩univ.pi S)≠0) :
    conditionedMeasure (Measure.pi ν) (B∩univ.pi S)=
      conditionedMeasure (Measure.pi (fun i ↦ conditionedMeasure (ν i) (S i))) B := by
  rw [pi_conditioned ν S hS hpos]
  let μ := Measure.pi ν
  have hz : μ (univ.pi S)≠0 := by
    change (Measure.pi ν) (univ.pi S)≠0
    exact ne_of_gt ((pos_iff_ne_zero.mpr hfull).trans_le (measure_mono inter_subset_right))
  have hzinf : μ (univ.pi S)≠⊤ := measure_ne_top _ _
  unfold conditionedMeasure
  rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB,Measure.restrict_smul,
    Measure.restrict_restrict hB,smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (ENNReal.inv_ne_top.mpr hz)),inv_inv]
  change (μ (B∩univ.pi S))⁻¹=μ (univ.pi S)*(μ (B∩univ.pi S))⁻¹*(μ (univ.pi S))⁻¹
  rw [mul_comm (μ (univ.pi S)),mul_assoc,ENNReal.mul_inv_cancel hz hzinf,mul_one]

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E I J : Type*} [MeasurableSpace E] [Fintype I] [Fintype J]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma flagEvent_measurable (f : ∀i,E×X i→Bool) (hf : ∀i,Measurable (f i)) (b : I→Bool) :
    MeasurableSet (flagEvent f b) := by
  have he : flagEvent f b=⋂i,{z : E×(∀i,X i) | f i (z.1,z.2 i)=b i} := by ext z; simp [flagEvent]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun ((hf i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))) measurable_const

omit [MeasurableSpace E] [Fintype I] in
lemma blockGlue_inside (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) (i : {i // p i}) :
    (blockGlue p (w,v)).2 i=v i := by
  simp [blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,i.property]

omit [MeasurableSpace E] [Fintype I] in
lemma blockGlue_outside (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) (i : {i // ¬p i}) :
    (blockGlue p (w,v)).2 i=w.2 i := by
  simp [blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,i.property]

omit [MeasurableSpace E] [Fintype I] in
lemma blockGlue_fst (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) :
    (blockGlue p (w,v)).1=w.1 := rfl

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_GroundBridge
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener

lemma preserving_weighted {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {T : A→B} (hT : MeasurePreserving T μ ν)
    (f : B→ℝ≥0∞) (hf : Measurable f) :
    MeasurePreserving T (μ.withDensity (f∘T)) (ν.withDensity f) := by
  refine ⟨hT.measurable,?_⟩
  ext S hS
  rw [Measure.map_apply hT.measurable hS,withDensity_apply _ (hS.preimage hT.measurable),withDensity_apply _ hS]
  exact (hT.restrict_preimage hS).lintegral_comp hf

lemma endpointBridgePath_continuous (N : ℕ) (L : Length) (t : ℝ) :
    Continuous (endpointBridgePath N L t) := by
  exact (freeTrajectory_continuous N L t).comp
    (((reconstructCoordinates_continuous N).comp (continuous_fst.fst.prodMk continuous_snd)).prodMk continuous_fst.snd)

lemma endpointBridgePath_preserving (N : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (endpointBridgePath N L t)
      ((bridgeEndpointBase N L).prod (coordinateBridge N)) (freePathLaw N L t) := by
  have h₁ := measurePreserving_prodAssoc (gaussianCoordinates N) (volume : Measure (Configuration N L)) (coordinateBridge N)
  have h₂ := (MeasurePreserving.id (gaussianCoordinates N)).prod
    (Measure.measurePreserving_swap (μ:=(volume : Measure (Configuration N L))) (ν:=coordinateBridge N))
  have h₃ := (measurePreserving_prodAssoc (gaussianCoordinates N) (coordinateBridge N) (volume : Measure (Configuration N L))).symm MeasurableEquiv.prodAssoc
  have h₄ := (reconstructCoordinates_preserving N).prod (MeasurePreserving.id (volume : Measure (Configuration N L)))
  have h₅ : MeasurePreserving (fun p : CoordinatePaths N×Configuration N L ↦ freeTrajectory N L t p.1 p.2)
      ((coordinateWiener N).prod volume) (freePathLaw N L t) := ⟨(freeTrajectory_continuous N L t).measurable,rfl⟩
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

lemma bridgeEnd_continuous (N : ℕ) (L : Length) (t : ℝ) : Continuous (bridgeEnd N L t) := by
  unfold bridgeEnd
  fun_prop

lemma endpointWeight_measurable {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) : Measurable (endpointWeight u t) := by
  unfold endpointWeight
  exact (measurable_const.mul (((Lp.stronglyMeasurable u.1).measurable.comp measurable_snd).norm.mul
    (((Lp.stronglyMeasurable u.1).measurable.comp (bridgeEnd_continuous N L t).measurable).norm))).ennreal_ofReal

lemma endpointBridge_weight {N : ℕ} {L : Length} (u : Jet N L) (t : ℝ) :
    (fun p : BridgeEndpoints N L×CoordinatePaths N ↦ endpointWeight u t p.1)=ᵐ[(bridgeEndpointBase N L).prod (coordinateBridge N)]
      fun p ↦ ENNReal.ofReal (groundPathWeight u t (endpointBridgePath N L t p)) := by
  have h : ∀ᵐ p : BridgeEndpoints N L×CoordinatePaths N ∂(bridgeEndpointBase N L).prod (coordinateBridge N),
      ∀j, p.2 j (0:Time)=0 ∧ p.2 j (1:Time)=0 :=
    (Measure.ae_prod_iff_ae_ae (by measurability)).mpr (ae_of_all _ (fun _ ↦ coordinateBridge_endpoints N))
  filter_upwards [h] with p hp
  have h0 : endpointBridgePath N L t p 0=p.1.2 := by
    ext i j
    change p.1.2 i j+((Real.sqrt (2*t)*(p.1.1 (i,j) • linearPath+p.2 (i,j)) 0:ℝ):AddCircle L.val)=p.1.2 i j
    simp [hp,linearPath]
  have h1 : endpointBridgePath N L t p 1=bridgeEnd N L t p.1 := by
    ext i j
    change p.1.2 i j+((Real.sqrt (2*t)*(p.1.1 (i,j) • linearPath+p.2 (i,j)) 1:ℝ):AddCircle L.val)=_
    simp [hp,linearPath,bridgeEnd]
  simp [endpointWeight,groundPathWeight,h0,h1]

lemma endpointInteraction_measurable (N : ℕ) (L : Length) (a t : ℝ) : MeasurableSet (endpointInteraction N L a t) :=
  (staysAllowed_open N L a).measurableSet.preimage (endpointBridgePath_continuous N L t).measurable

lemma genuine_ground_bridge {N : ℕ} {L : Length} (u : Jet N L) (a t : ℝ) :
    (((endpointWeightedBase u t).prod (coordinateBridge N)).restrict (endpointInteraction N L a t)).map (endpointBridgePath N L t)=
      groundPathLaw N L a t u := by
  have hf := endpointBridgePath_preserving N L t
  have hw := preserving_weighted (hf.restrict_preimage (staysAllowed_open N L a).measurableSet)
    (fun ω ↦ ENNReal.ofReal (groundPathWeight u t ω)) (groundPathWeight_measurable u t).ennreal_ofReal
  change _=(killedPathLaw N L a t).withDensity _
  rw [endpointWeightedBase,prod_withDensity_left (endpointWeight_measurable u t),restrict_withDensity (endpointInteraction_measurable N L a t)]
  have he : ((fun p : BridgeEndpoints N L×CoordinatePaths N ↦ endpointWeight u t p.1))=ᵐ[((bridgeEndpointBase N L).prod (coordinateBridge N)).restrict (endpointInteraction N L a t)]
      ((fun ω ↦ ENNReal.ofReal (groundPathWeight u t ω))∘endpointBridgePath N L t) :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_le (endpointBridge_weight u t)
  rw [withDensity_congr_ae he]
  exact hw.map_eq

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeBlocks
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Comparison Bridge

lemma uncurveBridge_preserving (N : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin 3) C(Time,ℝ)).symm
      (Measure.pi fun _ : Fin N ↦ Bridge.law) (coordinateBridge N) := by
  refine ⟨(MeasurableEquiv.curry _ _ _).symm.measurable,?_⟩
  simpa only [Measure.infinitePi_eq_pi,Bridge.law,coordinateBridge] using Measure.infinitePi_map_curry_symm (fun _ : Fin N ↦ fun _ : Fin 3 ↦ bridgeLaw)

lemma labelBridgePath_preserving (N : ℕ) (L : Length) (t : ℝ) :
    MeasurePreserving (labelBridgePath N L t) ((bridgeEndpointBase N L).prod (Measure.pi fun _ : Fin N ↦ Bridge.law)) (freePathLaw N L t) :=
  (endpointBridgePath_preserving N L t).comp ((MeasurePreserving.id (bridgeEndpointBase N L)).prod (uncurveBridge_preserving N))
lemma labelBridgePath_measurable (N : ℕ) (L : Length) (t : ℝ) : Measurable (labelBridgePath N L t) :=
  (labelBridgePath_preserving N L t).measurable

lemma labelInteraction_measurable (N : ℕ) (L : Length) (a t : ℝ) : MeasurableSet (labelInteraction N L a t) :=
  (staysAllowed_open N L a).measurableSet.preimage (labelBridgePath_measurable N L t)

lemma genuine_ground_label_bridge {N : ℕ} {L : Length} (u : Jet N L) (a t : ℝ) :
    (((endpointWeightedBase u t).prod (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict (labelInteraction N L a t)).map (labelBridgePath N L t)=
      groundPathLaw N L a t u := by
  have h := ((MeasurePreserving.id (endpointWeightedBase u t)).prod (uncurveBridge_preserving N)).restrict_preimage
    (endpointInteraction_measurable N L a t)
  have he := congrArg (fun μ : Measure (BridgeEndpoints N L×CoordinatePaths N) ↦ μ.map (endpointBridgePath N L t)) h.map_eq
  rw [Measure.map_map (endpointBridgePath_continuous N L t).measurable h.measurable] at he
  exact he.trans (genuine_ground_bridge u a t)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EndpointLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Bridge GaussianPacking

lemma labelBridgePath_lift {N : ℕ} {L : Length} (t : ℝ)
    (e : BridgeEndpoints N L) (β : Fin N→Bridge.Noise) (i : Fin N) :
    onePathAt i (labelBridgePath N L t (e,β))=
      projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) (β i)) := by
  ext s k j
  have hp := congrFun (congrFun (project_representative N L e.2) i) j
  change e.2 i j+((Real.sqrt (2*t)*(e.1 (i,j)*(s:ℝ)+β i j s):ℝ):AddCircle L.val)=
    (((1-(s:ℝ))*labelStartLift e i j+(s:ℝ)*labelEndLift t e i j+Real.sqrt (2*t)*β i j s:ℝ):AddCircle L.val)
  change ((labelStartLift e i j:ℝ):AddCircle L.val)=e.2 i j at hp
  rw [←hp,←QuotientAddGroup.mk_add]
  congr 1
  unfold labelEndLift
  ring

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PairFiber
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I E : Type*} [Fintype I] [MeasurableSpace E]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma shifted_fiber (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (flag : ∀i,X i→Bool) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i) (v : ∀i : {i // p i},X i) :
    (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
      (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i) ↔
    frozenCompatible p C w ∧ (∀i : {i // ¬p i},flag i (w i)=b i) ∧
      v∈pairEvent (fun i j : {i // p i} ↦ C i j) ∩ univ.pi (individualFiber p C flag b w) := by
  constructor
  · rintro ⟨hp,hf⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro i j hij
      have hne : i.val≠j.val := fun he ↦ hij (Subtype.ext he)
      simpa [pairEvent,i.property,j.property] using hp i j hne
    · intro i
      simpa only [dite_eq_right i.property] using hf i
    · intro i j hij
      have hne : i.val≠j.val := fun he ↦ hij (Subtype.ext he)
      simpa only [dite_eq_left i.property,dite_eq_left j.property] using hp i j hne
    · intro i _
      constructor
      · simpa only [dite_eq_left i.property] using hf i
      · intro j
        have hne : i.val≠j.val := by intro h; exact j.property (h ▸ i.property)
        constructor
        · simpa only [dite_eq_left i.property,dite_eq_right j.property] using hp i j hne
        · simpa only [dite_eq_left i.property,dite_eq_right j.property] using hp j i hne.symm
  · rintro ⟨hout,hflag,hpair,hown⟩
    constructor
    · intro i j hij
      by_cases hi : p i <;> by_cases hj : p j
      · simpa only [dite_eq_left hi,dite_eq_left hj] using hpair ⟨i,hi⟩ ⟨j,hj⟩ (fun h ↦ hij (congrArg Subtype.val h))
      · simpa only [dite_eq_left hi,dite_eq_right hj] using ((hown ⟨i,hi⟩ (mem_univ _)).2 ⟨j,hj⟩).1
      · simpa only [dite_eq_right hi,dite_eq_left hj] using ((hown ⟨j,hj⟩ (mem_univ _)).2 ⟨i,hi⟩).2
      · simpa only [dite_eq_right hi,dite_eq_right hj] using hout ⟨i,hi⟩ ⟨j,hj⟩ (fun h ↦ hij (congrArg Subtype.val h))
    · intro i
      by_cases hi : p i
      · simpa only [dite_eq_left hi] using (hown ⟨i,hi⟩ (mem_univ _)).1
      · simpa only [dite_eq_right hi] using hflag ⟨i,hi⟩

lemma pairEvent_measurable (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2}) :
    MeasurableSet (pairEvent C) := by
  simp only [pairEvent,ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun (_ : i≠j) ↦ (hC i j).preimage ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

lemma individualFiber_measurable (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2})
    (flag : ∀i,X i→Bool) (hflag : ∀i,Measurable (flag i)) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i) (i : {i // p i}) :
    MeasurableSet (individualFiber p C flag b w i) := by
  have he : individualFiber p C flag b w i={v | flag i v=b i} ∩
      ⋂j : {j // ¬p j}, {v | C i j v (w j)} ∩ {v | C j i (w j) v} := by
    ext v
    simp [individualFiber]
  rw [he]
  apply (measurableSet_eq_fun (hflag i) measurable_const).inter
  apply MeasurableSet.iInter
  intro j
  exact ((hC i j).preimage (measurable_id.prodMk measurable_const)).inter
    ((hC j i).preimage (measurable_const.prodMk measurable_id))

lemma positive_product_factors (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (S : ∀i,Set (X i)) (B : Set (∀i,X i))
    (h : (Measure.pi ν) (B∩univ.pi S)≠0) : ∀i,ν i (S i)≠0 := by
  have hpi : (Measure.pi ν) (univ.pi S)≠0 := ne_of_gt ((pos_iff_ne_zero.mpr h).trans_le (measure_mono inter_subset_right))
  rw [Measure.pi_pi] at hpi
  exact fun i ↦ (Finset.prod_ne_zero_iff.mp hpi) i (Finset.mem_univ i)

lemma conditional_pair_fiber (p : I→Prop) (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2})
    (flag : ∀i,X i→Bool) (hflag : ∀i,Measurable (flag i)) (b : I→Bool)
    (w : ∀i : {i // ¬p i},X i)
    (ν : ∀i : {i // p i},Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (hpos : (Measure.pi ν) {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
      (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)}≠0) :
    frozenCompatible p C w ∧
      (∀i,ν i (individualFiber p C flag b w i)≠0) ∧
      conditionedMeasure (Measure.pi ν)
        {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
          (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)}=
      conditionedMeasure
        (Measure.pi fun i ↦ conditionedMeasure (ν i) (individualFiber p C flag b w i))
        (pairEvent (fun i j : {i // p i} ↦ C i j)) := by
  have he : {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
          (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)}=
      pairEvent (fun i j : {i // p i} ↦ C i j) ∩ univ.pi (individualFiber p C flag b w) := by
    obtain ⟨v,hv⟩ := nonempty_of_measure_ne_zero hpos
    obtain ⟨hout,hf,_⟩ := (shifted_fiber p C flag b w v).mp hv
    ext u
    exact (shifted_fiber p C flag b w u).trans (by simp only [hout,hf,implies_true,true_and])
  rw [he] at hpos ⊢
  obtain ⟨v,hv⟩ := nonempty_of_measure_ne_zero hpos
  have hout : frozenCompatible p C w := by
    have hv' : v∈{v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)∈pairEvent C ∧
          (∀i,flag i (if h : p i then v ⟨i,h⟩ else w ⟨i,h⟩)=b i)} := by rw [he]; exact hv
    exact ((shifted_fiber p C flag b w v).mp hv').1
  have hnormal := positive_product_factors ν (individualFiber p C flag b w) _ hpos
  exact ⟨hout,hnormal,condition_product_factorization ν _
    (individualFiber_measurable p C hC flag hflag b w) hnormal _
    (pairEvent_measurable _ (fun i j ↦ hC i j)) hpos⟩

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere
open Wiener Bridge GaussianPacking Comparison
attribute [local irreducible] torusDistance leg

lemma noisePairAvoid_measurable {N : ℕ} {L : Length} (a t : ℝ)
    (e : BridgeEndpoints N L) (i j : Fin N) :
    MeasurableSet {z : Bridge.Noise×Bridge.Noise | noisePairAvoid a t e i j z.1 z.2} := by
  exact ((jointCollision_closed (L:=L) a).measurableSet.preimage
    (((leg_continuous t _ _).comp continuous_fst).prodMk
      ((leg_continuous t _ _).comp continuous_snd)).measurable).compl

lemma labelInteraction_pair {N : ℕ} {L : Length} (a t : ℝ)
    (e : BridgeEndpoints N L) (β : Fin N→Bridge.Noise) :
    (e,β)∈labelInteraction N L a t ↔ β∈pairEvent (noisePairAvoid a t e) := by
  have hcoord (i : Fin N) (s : Time) :
      labelBridgePath N L t (e,β) s i =
        projectPoint L (leg t (labelStartLift e i) (labelEndLift t e i) (β i) s) := by
    exact congrArg (fun f : C(Time,Configuration 1 L) ↦ f s 0) (labelBridgePath_lift t e β i)
  change (∀X,X∈Set.range (labelBridgePath N L t (e,β))→X∈allowed N L a) ↔ _
  simp only [Set.forall_mem_range,allowed_iff_ne,pairEvent,mem_ofPred_eq,
    noisePairAvoid,TrialCollision,not_exists,not_le]
  constructor
  · intro h i j hij s
    change a<torusDistance L (projectPoint L (leg t (labelStartLift e i) (labelEndLift t e i) (β i) s)) (projectPoint L (leg t (labelStartLift e j) (labelEndLift t e j) (β j) s))
    rw [←hcoord i s,←hcoord j s]
    exact h s i j hij
  · intro h s i j hij
    rw [hcoord i s,hcoord j s]
    exact h i j hij s

attribute [local instance] Classical.propDecidable

lemma noise_blockGlue {N : ℕ} {L : Length} (p : Fin N→Prop)
    (w : BridgeEndpoints N L×({i // ¬p i}→Bridge.Noise))
    (v : {i // p i}→Bridge.Noise) :
    (blockGlue p (w,v)).2=(fun i ↦ if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩) := by
  funext i
  by_cases hi : p i
  · simpa only [dite_eq_left hi] using blockGlue_inside (X:=fun _ : Fin N ↦ Bridge.Noise) p w v ⟨i,hi⟩
  · simpa only [dite_eq_right hi] using blockGlue_outside (X:=fun _ : Fin N ↦ Bridge.Noise) p w v ⟨i,hi⟩

lemma noise_flag_fiber {N : ℕ} {L : Length} (a t : ℝ)
    (flag : Fin N→BridgeEndpoints N L×Bridge.Noise→Bool)
    (b : Fin N→Bool) (p : Fin N→Prop)
    (w : BridgeEndpoints N L×({i // ¬p i}→Bridge.Noise)) :
    {v | blockGlue p (w,v)∈labelInteraction N L a t ∩ flagEvent flag b}=
      {v | (fun i ↦ if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩)∈pairEvent (noisePairAvoid a t w.1) ∧
        ∀i,flag i (w.1,if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩)=b i} := by
  ext v
  have hglue : blockGlue p (w,v)=
      (w.1,fun i ↦ if h : p i then v ⟨i,h⟩ else w.2 ⟨i,h⟩) := by
    apply Prod.ext
    · exact blockGlue_fst (X:=fun _ : Fin N ↦ Bridge.Noise) p w v
    · exact noise_blockGlue p w v
  simp only [Set.mem_ofPred_eq]
  rw [hglue]
  simp only [mem_ofPred_eq,mem_inter_iff,labelInteraction_pair,flagEvent]

lemma recorded_physical_fiber {N : ℕ} {L : Length} (μ : Measure (BridgeEndpoints N L)) [SFinite μ] (a t : ℝ)
    (flag : Fin N→BridgeEndpoints N L×Bridge.Noise→Bool)
    (hflag : ∀i,Measurable (flag i)) (b : Fin N→Bool) (p : Fin N→Prop) :
    ∀ᵐw ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
        (labelInteraction N L a t ∩ flagEvent flag b),
      frozenCompatible p (noisePairAvoid a t w.1) w.2 ∧
      (∀i : {i // p i},Bridge.law
        (individualFiber p (noisePairAvoid a t w.1) (fun j β ↦ flag j (w.1,β)) b w.2 i)≠0) ∧
      conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
        {v | blockGlue p (w,v)∈labelInteraction N L a t ∩ flagEvent flag b}=
      conditionedMeasure (Measure.pi fun i : {i // p i} ↦
        conditionedMeasure Bridge.law
          (individualFiber p (noisePairAvoid a t w.1) (fun j β ↦ flag j (w.1,β)) b w.2 i))
        (pairEvent (fun i j : {i // p i} ↦ noisePairAvoid a t w.1 i j)) := by
  filter_upwards [exposed_block_positive μ
    (fun _ : Fin N ↦ Bridge.law) p
    ((labelInteraction_measurable N L a t).inter (flagEvent_measurable flag hflag b))] with w hw
  have he := noise_flag_fiber a t flag b p w
  rw [he] at hw ⊢
  exact conditional_pair_fiber p (noisePairAvoid a t w.1)
    (noisePairAvoid_measurable a t w.1) (fun i β ↦ flag i (w.1,β))
    (fun i ↦ (hflag i).comp (measurable_const.prodMk measurable_id)) b w.2
    (fun _ ↦ Bridge.law) (ne_of_gt hw)

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_WeightedExpose
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge CellOrbital Sampling Comparison
attribute [local instance] Classical.propDecidable

lemma ownPath_measurable {N : ℕ} {L : Length} (i : Fin N) (t : ℝ) :
    Measurable (ownPath (L:=L) i t) :=
  (onePathAt_continuous i).measurable.comp
    ((labelBridgePath_measurable N L t).comp (by fun_prop))

lemma ownPath_eq {N : ℕ} {L : Length} (i : Fin N) (t : ℝ)
    (e : BridgeEndpoints N L) (β : Fin N→Bridge.Noise) :
    ownPath i t (e,β i)=onePathAt i (labelBridgePath N L t (e,β)) := by
  simp only [ownPath,labelBridgePath_lift]

lemma ownEligible_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) : MeasurableSet {p | ownEligible (K:=K) (L:=L) m r R C S s₀ t u i p} := by
  simp only [ownEligible,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro v
  exact ((endpointEligible_measurable v s₀ i).preimage
    (measurable_snd.comp measurable_fst |>.prodMk ((bridgeEnd_continuous N L t).measurable.comp measurable_fst))).inter
      (((PathCutoff.regular_measurable m r R C u S).preimage (ownPath_measurable i t)).inter
        ((confined_closed (gridCenter L v)).measurableSet.preimage (ownPath_measurable i t)))

lemma eligibilityFlag_measurable {N K : ℕ} {L : Length} (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) : Measurable (eligibilityFlag (K:=K) (L:=L) m r R C S s₀ t u i) := by
  apply measurable_to_countable'
  intro b
  cases b
  · change MeasurableSet {p | decide (ownEligible (K:=K) m r R C S s₀ t u i p)=false}
    simpa only [decide_eq_false_iff_not,←Set.compl_ofPred]
      using (ownEligible_measurable (K:=K) (L:=L) m r R C S s₀ t u i).compl
  · change MeasurableSet {p | decide (ownEligible (K:=K) m r R C S s₀ t u i p)=true}
    simpa only [decide_eq_true_eq]
      using ownEligible_measurable (K:=K) (L:=L) m r R C S s₀ t u i

lemma exposed_endpoints {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L) :
    ∀ᵐβ ∂(Measure.pi fun _ : Fin N ↦ Bridge.law),
      labelBridgePath N L t (e,β) 0=e.2 ∧
      labelBridgePath N L t (e,β) 1=bridgeEnd N L t e := by
  have he : ∀ᵐβ ∂(Measure.pi fun _ : Fin N ↦ Bridge.law),∀i : Fin N,
      leg t (labelStartLift e i) (labelEndLift t e i) (β i) 0=labelStartLift e i ∧
      leg t (labelStartLift e i) (labelEndLift t e i) (β i) 1=labelEndLift t e i :=
    ae_all_iff.mpr (fun i ↦ (measurePreserving_eval (fun _ : Fin N ↦ Bridge.law) i).quasiMeasurePreserving.ae
      (leg_endpoints_ae t _ _))
  filter_upwards [he] with β hβ
  constructor
  · ext i j
    have hi := congrFun (congrFun (congrArg (fun ω : ConfigurationPath 1 L ↦ ω 0) (labelBridgePath_lift t e β i)) 0) j
    change _=((leg t (labelStartLift e i) (labelEndLift t e i) (β i) 0) j : AddCircle L.val) at hi
    rw [(hβ i).1] at hi
    exact hi.trans (congrFun (congrFun (project_representative N L e.2) i) j)
  · ext i j
    have hi := congrFun (congrFun (congrArg (fun ω : ConfigurationPath 1 L ↦ ω 1) (labelBridgePath_lift t e β i)) 0) j
    change _=((leg t (labelStartLift e i) (labelEndLift t e i) (β i) 1) j : AddCircle L.val) at hi
    rw [(hβ i).2] at hi
    exact hi.trans (by
      change ((labelStartLift e i j+Real.sqrt (2*t)*e.1 (i,j):ℝ):AddCircle L.val)=_
      rw [QuotientAddGroup.mk_add]
      have hp := congrFun (congrFun (project_representative N L e.2) i) j
      change ((labelStartLift e i j:ℝ):AddCircle L.val)=e.2 i j at hp
      rw [hp]
      rfl)

lemma recordedList_eq {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (v : Fin 3→Fin K) (e : BridgeEndpoints N L)
    (β : Fin N→Bridge.Noise) (h0 : labelBridgePath N L t (e,β) 0=e.2)
    (h1 : labelBridgePath N L t (e,β) 1=bridgeEnd N L t e) :
    recordedList hL v (e,fun i ↦ eligibilityFlag (K:=K) m r R C S s₀ t u i (e,β i))=
      eligibleList m r R C S s₀ u v (labelBridgePath N L t (e,β)) := by
  ext i
  simp only [recordedList,eligibleList,Finset.mem_filter,Finset.mem_univ,true_and,
    eligibilityFlag,decide_eq_true_eq,ownEligible,Eligible,h0,h1,ownPath_eq]
  constructor
  · rintro ⟨hi,w,hw,hr,hc⟩
    have hw' : gridHome hL (e.2 i)=w := (gridHome_eq_iff hL hK _ _).mpr hw.1
    have hvw : w=v := hw'.symm.trans hi
    rw [hvw] at hw hc
    exact ⟨hw,hr,hc⟩
  · intro hv
    exact ⟨(gridHome_eq_iff hL hK _ _).mpr hv.1.1,v,hv⟩

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Kernels_FiniteKernelPi
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HardSphere.Comparison

lemma finiteKernelPi_apply {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    (κ : ∀ i, Kernel α (β i)) [∀ i, IsFiniteKernel (κ i)] (a : α) :
    finiteKernelPi κ a = Measure.pi (fun i ↦ κ i a) :=
  (exists_kernel_pi β κ).choose_spec.2 a

end HardSphere.Comparison

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAllocation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Sampling.siteAllocationKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

lemma gridAllocationKernel_apply {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ)
    (p : BridgeEndpoints N L×(Fin N→Bool)) :
    gridAllocationKernel hL q p=Measure.pi (fun v ↦ (allocationPMF (recordedList hL v p) q).toMeasure) := by
  rw [gridAllocationKernel,finiteKernelPi_apply]
  rfl

instance gridAllocationKernel_markov {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ) :
    IsMarkovKernel (gridAllocationKernel (N:=N) hL q) := by
  constructor
  intro p
  rw [gridAllocationKernel_apply]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma groupAt_mem_list {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (p : BridgeEndpoints N L×(Fin N→Bool)) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (recordedList hL v p) (G*M)).support)
    (g : Fin G) (v : Fin 3→Fin K) : groupAt g a v⊆recordedList hL v p := by
  intro i hi
  cases he : a v with
  | none => simp [groupAt,he] at hi
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hi
    obtain ⟨k,rfl⟩ := hi
    exact allocationPMF_support _ _ _ (ha v) f he _

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital
attribute [local instance] Classical.propDecidable

lemma allocation_support_ae {I : Type*} [Fintype I] [DecidableEq I]
    (E : Finset I) (m : ℕ) : ∀ᵐa ∂(allocationPMF E m).toMeasure,a∈(allocationPMF E m).support := by
  have h := ae_restrict_mem (μ:=(allocationPMF E m).toMeasure) ((allocationPMF E m).support_countable.measurableSet)
  rw [PMF.restrict_toMeasure_support] at h
  exact h

lemma gridAllocation_support_ae {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (q : ℕ)
    (p : BridgeEndpoints N L×(Fin N→Bool)) :
    ∀ᵐa ∂gridAllocationKernel hL q p,∀v,a v∈(allocationPMF (recordedList hL v p) q).support := by
  rw [gridAllocationKernel_apply]
  apply ae_all_iff.mpr
  intro v
  exact (MeasureTheory.measurePreserving_eval (fun w ↦ (allocationPMF (recordedList hL w p) q).toMeasure) v).quasiMeasurePreserving.tendsto_ae
    (allocation_support_ae _ _)

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_AllocationJoint
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff Comparison CellOrbital

lemma endpointEligible_unique {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {v w : Fin 3→Fin K} {s₀ : ℝ} {Y Z : Configuration N L} {i : Fin N}
    (hv : EndpointEligible v s₀ Y Z i) (hw : EndpointEligible w s₀ Y Z i) : v=w := by
  by_contra h
  exact Set.disjoint_left.mp (centeredCell_disjoint hL hK h) hv.1 hw.1

lemma ownEligible_at {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (e : BridgeEndpoints N L) (β : Bridge.Noise) (v : Fin 3→Fin K)
    (he : EndpointEligible v s₀ e.2 (bridgeEnd N L t e) i) :
    ownEligible (K:=K) m r R C S s₀ t u i (e,β) ↔
      Regular m r R C u S (projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) β)) ∧
      Confined (gridCenter L v) (projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) β)) := by
  have hp : ownPath i t (e,β)=projectCurve L (leg t (labelStartLift e i) (labelEndLift t e i) β) := by
    exact labelBridgePath_lift t e (fun _ ↦ β) i
  unfold ownEligible
  rw [hp]
  constructor
  · rintro ⟨w,hw,hreg,hconf⟩
    have hh := endpointEligible_unique hL hK he hw
    subst w
    exact ⟨hreg,hconf⟩
  · rintro ⟨hreg,hconf⟩
    exact ⟨v,he,hreg,hconf⟩

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma fixedEndpoints_measurable (y z : Point) : MeasurableSet (fixedEndpoints y z) :=
  (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
    (measurableSet_eq_fun (continuous_eval_const 1).measurable measurable_const)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ConfinedLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener PathCutoff GaussianPacking
attribute [local irreducible] torusDistance

lemma intervalTime_full (s : Time) : intervalTime 0 1 s=s := by
  apply Subtype.ext
  simp [intervalTime]

lemma tube_diameter {L : Length} (ω : ConfigurationPath 1 L) (c : Torus L)
    (hc : ∀s : Time,torusDistance L (ω s 0) c≤10) : intervalDiameter 0 1 ω≤20 := by
  apply intervalDiameter_le _ _ _ (by norm_num)
  intro s q
  simp only [intervalTime_full]
  have htri := torusDistance_triangle' L (ω s 0) c (ω q 0)
  rw [torusDistance_comm L c] at htri
  linarith [hc s,hc q]

lemma lift_norm_increment {L : Length} (hL : 50<L.val) (f : C(Time,Point))
    (hd : intervalDiameter 0 1 (projectCurve L f)≤20) (s : Time) :
    ‖f s-f 0‖≤20 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤20)).mpr
  intro j
  have he := liftDiff_norm_eq (projectCurve_lift L f) 0 1 (hd.trans_lt (by linarith)) j s 0
  simp only [intervalTime_full] at he
  change dist (projectPoint L (f s) j) (projectPoint L (f 0) j)=|f s j-f 0 j| at he
  change |f s j-f 0 j|≤20
  rw [←he]
  have hd' := intervalDistance_le 0 1 s 0 (projectCurve L f)
  simp only [intervalTime_full] at hd'
  exact (CellOrbital.dist_coord_le_torusDistance L _ _ j).trans (hd'.trans hd)

lemma scalar_dist_eq {L : Length} (x y : ℝ) (h : |x-y|≤L.val/2) :
    dist (x : AddCircle L.val) (y : AddCircle L.val)=|x-y| := by
  have he := (AddCircle.norm_coe_eq_abs_iff L.val L.property.ne').mpr
    (show |x-y|≤|L.val|/2 by simpa only [abs_of_pos L.property] using h)
  simpa only [AddCircle.coe_sub,dist_eq_norm] using he

lemma local_norm_le_torus {L : Length} (hL : 50<L.val) (x v : Point)
    (hx : ‖x-v‖≤23) : ‖x-v‖≤torusDistance L (projectPoint L x) (projectPoint L v) := by
  apply (pi_norm_le_iff_of_nonneg (torusDistance_nonnegative _ _ _)).mpr
  intro j
  have hb : ‖(x-v) j‖≤23 := (norm_le_pi_norm (x-v) j).trans hx
  have hbound : |x j-v j|≤23 := hb
  have he : dist (projectPoint L x j) (projectPoint L v j)=|x j-v j| :=
    scalar_dist_eq (x j) (v j) (by linarith)
  change |x j-v j|≤_
  rw [←he]
  exact CellOrbital.dist_coord_le_torusDistance L _ _ j

lemma confined_lift {L : Length} (hL : 50<L.val) (v : Point) (f : C(Time,Point))
    (h0 : ‖f 0-v‖≤3)
    (hc : ∀s : Time,torusDistance L (projectPoint L (f s)) (projectPoint L v)≤10) :
    TrialConfined L v f := by
  have hd := tube_diameter (projectCurve L f) (projectPoint L v) hc
  intro s
  refine ⟨?_,hc s⟩
  have hin := lift_norm_increment hL f hd s
  have h23 : ‖f s-v‖≤23 := by
    have htri := norm_sub_le (f s - f 0) (v - f 0)
    have he : f s-v = (f s-f 0)-(v-f 0) := by abel
    have hev : ‖v-f 0‖=‖f 0-v‖ := norm_sub_rev _ _
    rw [←he,hev] at htri
    linarith
  exact (local_norm_le_torus hL (f s) v h23).trans (hc s)

lemma leg_translate (t : ℝ) (y z c : Point) (β : Noise) :
    leg t (y+c) (z+c) β=leg t y z β+ContinuousMap.const _ c := by
  ext s j
  change (1-(s:ℝ))*(y j+c j)+(s:ℝ)*(z j+c j)+Real.sqrt (2*t)*β j s=
    ((1-(s:ℝ))*y j+(s:ℝ)*z j+Real.sqrt (2*t)*β j s)+c j
  ring

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma permittedPath_measurable {J : Type*} [Countable J] {L : Length}
    (n : ℕ) (r R Creg S : ℝ) (w : Time) (y z v : Point) (F : J → ConfigurationPath 1 L) :
    MeasurableSet (permittedPath n r R Creg S w y z v F) := by
  apply ((regular_measurable n r R Creg w S).preimage (projectCurve_continuous L).measurable).inter
  apply (trialConfined_measurable L v).inter
  apply (fixedEndpoints_measurable y z).inter
  change MeasurableSet {f : C(Time,Point) | ∀j,¬TrialCollision r (F j) f}
  have he : {f : C(Time,Point) | ∀j,¬TrialCollision r (F j) f}=⋂j,{f | ¬TrialCollision r (F j) f} := by
    ext f
    simp only [mem_ofPred_eq,mem_iInter]
  rw [he]
  exact MeasurableSet.iInter (fun j ↦ (trialCollision_closed r (F j)).measurableSet.compl)

lemma near_end_of_confined_leg {L : Length} (hL : 50<L.val) (t : ℝ)
    (y z v : Point) (β : Noise) (hy : ‖y-v‖≤3)
    (hβ : leg t y z β 0=y ∧ leg t y z β 1=z)
    (hc : ∀s : Time,torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10)
    (hz : torusDistance L (projectPoint L z) (projectPoint L v)≤3) : ‖z-v‖≤3 := by
  have htube := confined_lift hL v (leg t y z β) (by simpa only [hβ.1] using hy) hc
  have h10 : ‖z-v‖≤10 := by simpa only [hβ.2] using (htube 1).1
  exact (local_norm_le_torus hL z v (h10.trans (by norm_num))).trans hz

lemma near_end_of_positive_confined {L : Length} (hL : 50<L.val) (t : ℝ)
    (y z v : Point) (hy : ‖y-v‖≤3)
    (hz : torusDistance L (projectPoint L z) (projectPoint L v)≤3)
    (hp : law {β | ∀s : Time,torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10}≠0) :
    ‖z-v‖≤3 := by
  by_contra h
  apply hp
  have hh : ∀ᵐβ ∂law,¬(∀s : Time,torusDistance L (projectPoint L (leg t y z β s)) (projectPoint L v)≤10) := by
    filter_upwards [leg_endpoints_ae t y z] with β hβ hc
    exact h (near_end_of_confined_leg hL t y z v β hy hβ hc hz)
  simpa only [not_not] using ae_iff.mp hh

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ConditionTransport
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
lemma conditioned_map_preimage (μ : Measure X) (f : X→Y) (hf : Measurable f)
    {S : Set Y} (hS : MeasurableSet S) :
    (conditionedMeasure μ (f⁻¹' S)).map f=conditionedMeasure (μ.map f) S := by
  unfold conditionedMeasure
  rw [Measure.map_smul,Measure.map_apply hf hS]
  congr 1
  ext B hB
  rw [Measure.map_apply hf hB,Measure.restrict_apply (hB.preimage hf),
    Measure.restrict_apply hB,Measure.map_apply hf (hB.inter hS)]
  rfl

lemma conditioned_map_ae (μ : Measure X) (f : X→Y) (hf : Measurable f)
    (E : Set X) {S : Set Y} (hS : MeasurableSet S) (hE : E=ᵐ[μ] f⁻¹' S) :
    (conditionedMeasure μ E).map f=conditionedMeasure (μ.map f) S := by
  have he : conditionedMeasure μ E=conditionedMeasure μ (f⁻¹' S) := by
    unfold conditionedMeasure
    rw [measure_congr hE,Measure.restrict_congr_set hE]
  rw [he]
  exact conditioned_map_preimage μ f hf hS

lemma conditioned_pi_map {I : Type*} [Fintype I] {X Y : I→Type*}
    [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]
    (μ : ∀i,Measure (X i)) [∀i,IsFiniteMeasure (μ i)]
    (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i))
    {S : Set (∀i,Y i)} (hS : MeasurableSet S) :
    (conditionedMeasure (Measure.pi μ) ((fun x i ↦ f i (x i))⁻¹' S)).map
      (fun x i ↦ f i (x i))=
      conditionedMeasure (Measure.pi fun i ↦ (μ i).map (f i)) S := by
  have hmf : Measurable (fun x : ∀i,X i ↦ fun i ↦ f i (x i)) := by
    exact Measurable.of_eval (fun i ↦ (hf i).comp (measurable_pi_apply i))
  rw [conditioned_map_preimage _ _ hmf hS,Measure.pi_map_pi (fun i ↦ (hf i).aemeasurable)]
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma noise_reference_identification (t : ℝ) (y z : Point) (E : Set Noise)
    {S : Set C(Time,Point)} (hS : MeasurableSet S)
    (hE : E=ᵐ[law] (leg (2*t) y z)⁻¹' S) :
    (conditionedMeasure law E).map (leg (2*t) y z)=individualReference t y z S :=
  conditioned_map_ae law _ (leg_continuous _ _ _).measurable E hS hE

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff Comparison CellOrbital
attribute [local instance] Classical.propDecidable

lemma actual_reference_event {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (e : BridgeEndpoints N L) (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise)
    (b : Fin N→Bool) (i : {i // p i}) (hbi : b i=true)
    (v : Fin 3→Fin K) (vLift : Point)
    (hvLift : projectPoint L vLift=gridCenter L v)
    (hy : ‖labelStartLift e i-vLift‖≤3)
    (he : EndpointEligible v s₀ e.2 (bridgeEnd N L (2*t) e) i) :
    individualFiber p (noisePairAvoid r (2*t) e)
      (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i
      =ᵐ[Bridge.law]
    (leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))⁻¹'
      permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
        vLift (frozenPaths (2*t) e p w) := by
  filter_upwards [leg_endpoints_ae (2*t) (labelStartLift e i) (labelEndLift (2*t) e i)] with β hβ
  apply propext
  have hown := ownEligible_at hL hK m r R C S s₀ (2*t) u i e β v he
  change (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u i (e,β)=b i ∧
    ∀j : {j // ¬p j},noisePairAvoid r (2*t) e i j β (w j) ∧ noisePairAvoid r (2*t) e j i (w j) β) ↔ _
  rw [hbi]
  simp only [eligibilityFlag,decide_eq_true_eq,hown]
  constructor
  · rintro ⟨⟨hreg,hconf⟩,havoid⟩
    refine ⟨hreg,?_,hβ,?_⟩
    · apply confined_lift h50 vLift _ (by simpa only [hβ.1] using hy)
      intro s
      rw [hvLift]
      exact hconf s
    · intro j
      exact (havoid j).1
  · rintro ⟨hreg,hconf,_,havoid⟩
    refine ⟨⟨hreg,?_⟩,?_⟩
    · intro s
      rw [←hvLift]
      exact (hconf s).2
    · intro j
      refine ⟨havoid j,?_⟩
      exact fun h ↦ havoid j ((physicalPairCheck_symmetric r _ _).mp h)

lemma actual_individual_reference {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (e : BridgeEndpoints N L) (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise)
    (b : Fin N→Bool) (i : {i // p i}) (hbi : b i=true)
    (v : Fin 3→Fin K) (vLift : Point)
    (hvLift : projectPoint L vLift=gridCenter L v)
    (hy : ‖labelStartLift e i-vLift‖≤3)
    (he : EndpointEligible v s₀ e.2 (bridgeEnd N L (2*t) e) i) :
    (conditionedMeasure Bridge.law (individualFiber p (noisePairAvoid r (2*t) e)
      (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i)).map
      (leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))=
    individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
      (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
        vLift (frozenPaths (2*t) e p w)) := by
  exact noise_reference_identification t _ _ _ (permittedPath_measurable ..)
    (actual_reference_event hL hK h50 m r R C S s₀ t u e p w b i hbi v vLift hvLift hy he)

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking Comparison CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalMutual_measurable {I : Type*} [Fintype I] {L : Length} (r : ℝ) :
    MeasurableSet (physicalMutual (I:=I) (L:=L) r) :=
  pairEvent_measurable _ (fun _ _ ↦ (jointCollision_closed (L:=L) r).measurableSet.compl)

lemma physical_product_reference {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (e : BridgeEndpoints N L) (p : Fin N → Prop) (w : {i // ¬p i} → Bridge.Noise)
    (b : Fin N → Bool) (hbi : ∀i : {i // p i},b i=true)
    (v : {i // p i} → Fin 3 → Fin K) (vLift : {i // p i} → Point)
    (hvLift : ∀i,projectPoint L (vLift i)=gridCenter L (v i))
    (hy : ∀i : {i // p i},‖labelStartLift e i-vLift i‖≤3)
    (he : ∀i : {i // p i},EndpointEligible (v i) s₀ e.2 (bridgeEnd N L (2*t) e) i)
    (hnormal : ∀i : {i // p i},Bridge.law
      (individualFiber p (noisePairAvoid r (2*t) e)
        (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i)≠0) :
    (conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      conditionedMeasure Bridge.law (individualFiber p (noisePairAvoid r (2*t) e)
        (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i))
      (pairEvent (fun i j : {i // p i} ↦ noisePairAvoid r (2*t) e i j))).map
      (fun β (i : {i // p i}) ↦ leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i) (β i))=
    conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
        (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
          (vLift i) (frozenPaths (2*t) e p w))) (physicalMutual (L:=L) r) := by
  let μ := fun i : {i // p i} ↦ conditionedMeasure Bridge.law
    (individualFiber p (noisePairAvoid r (2*t) e)
      (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (e,β)) b w i)
  let : ∀i,IsProbabilityMeasure (μ i) := fun i ↦ conditioned_probability Bridge.law (hnormal i)
  have hh := conditioned_pi_map μ
    (fun i ↦ leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))
    (fun i ↦ (leg_continuous ..).measurable) (physicalMutual_measurable (I:={i // p i}) (L:=L) r)
  have hm : ∀i,(μ i).map (leg (2*t) (labelStartLift e i) (labelEndLift (2*t) e i))=
      individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
        (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
          (vLift i) (frozenPaths (2*t) e p w)) := fun i ↦
    actual_individual_reference hL hK h50 m r R C S s₀ t u e p w b i (hbi i)
      (v i) (vLift i) (hvLift i) (hy i) (he i)
  simp_rw [hm] at hh
  exact hh

lemma physical_recorded_reference {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool) (hbi : ∀i : {i // p i},b i=true) :
    ∀ᵐw ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ∀(v : {i // p i} → Fin 3 → Fin K) (vLift : {i // p i} → Point),
      (∀i,projectPoint L (vLift i)=gridCenter L (v i)) →
      (∀i : {i // p i},‖labelStartLift w.1 i-vLift i‖≤3) →
      (∀i : {i // p i},EndpointEligible (v i) s₀ w.1.2 (bridgeEnd N L (2*t) w.1) i) →
      (conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
        {β | blockGlue p (w,β)∈labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b}).map
        (fun β (i : {i // p i}) ↦ leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i))=
      conditionedMeasure (Measure.pi fun i : {i // p i} ↦
        individualReference t (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
          (permittedPath m r R C S u (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i)
            (vLift i) (frozenPaths (2*t) w.1 p w.2))) (physicalMutual (L:=L) r) := by
  filter_upwards [recorded_physical_fiber μ r (2*t)
    (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u)
    (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b p] with w hw
  intro v vLift hv hy he
  rw [hw.2.2]
  exact physical_product_reference hL hK h50 m r R C S s₀ t u w.1 p w.2 b hbi v vLift hv hy he hw.2.1

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_VisitCounts
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital PathCutoff FreeVisits
attribute [local instance] Classical.propDecidable

lemma centeredCell_distance {L : Length} {c x : Torus L} (hx : x∈centeredCell L c) :
    torusDistance L x c≤1 := by
  have hd (j : Fin 3) : dist (x j) (c j)≤(1/2:ℝ) := by
    rw [dist_eq_norm,←centered_rep_abs]
    exact abs_le.mpr ⟨by linarith [(hx j).1], (hx j).2.le⟩
  unfold torusDistance
  apply Real.sqrt_le_one.mpr
  calc
    _ ≤ ∑ _j : Fin 3,(1/4:ℝ) := Finset.sum_le_sum (fun j _ ↦ by nlinarith [dist_nonneg (x:=x j) (y:=c j),hd j])
    _ ≤ 1 := by norm_num

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAssembly
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace HardSphere.Comparison

lemma finite_allocation_joint {E A : Type*} [MeasurableSpace E]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure E) [SFinite μ] (κ : Kernel E A) [IsSFiniteKernel κ] :
    (∑ a, (μ.withDensity (fun e ↦ κ e {a})).map (fun e ↦ (e,a))) = μ.compProd κ := by
  classical
  ext B hB
  rw [Measure.finsetSum_apply, Measure.compProd_apply hB]
  let F : A → E → ℝ≥0∞ := fun a ↦
    ((fun e ↦ (e,a)) ⁻¹' B).indicator (fun e ↦ κ e {a})
  have hF (a : A) : Measurable (F a) :=
    (κ.measurable_coe (measurableSet_singleton a)).indicator
      (hB.preimage measurable_prodMk_right)
  trans ∑ a, ∫⁻ e, F a e ∂μ
  · apply Finset.sum_congr rfl
    intro a _
    rw [Measure.map_apply measurable_prodMk_right hB,
      withDensity_apply _ (hB.preimage measurable_prodMk_right)]
    exact (lintegral_indicator (hB.preimage measurable_prodMk_right) _).symm
  rw [← lintegral_finsetSum _ (fun a _ ↦ hF a)]
  apply lintegral_congr
  intro e
  rw [← lintegral_indicator_one (hB.preimage measurable_prodMk_left), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (e,a) ∈ B <;> simp [F, h]

lemma recorded_density_sum {E J : Type*} [MeasurableSpace E]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (μ : Measure E) (r : E → J) (hr : Measurable r)
    (f : J → E → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    (∑ j, (μ.withDensity (f j)).restrict {e | r e = j}) =
      μ.withDensity (fun e ↦ f (r e) e) := by
  classical
  have hset (j : J) : MeasurableSet {e | r e = j} :=
    measurableSet_eq_fun hr measurable_const
  have h := withDensity_tsum (μ := μ)
    (fun j ↦ (hf j).indicator (hset j))
  rw [Measure.sum_fintype] at h
  have heq : (∑' j, {e | r e = j}.indicator (f j)) = (fun e ↦ f (r e) e) := by
    funext e
    rw [tsum_fintype, Finset.sum_apply]
    simp [Set.indicator]
  rw [heq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [restrict_withDensity (hset j), withDensity_indicator (hset j)]

lemma allocated_flag_joint {E Y J A : Type*}
    [MeasurableSpace E] [MeasurableSpace Y]
    [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (μ : Measure E) [SFinite μ] (ν : Measure Y) [SFinite ν]
    (κ : Kernel (E × J) A) [IsSFiniteKernel κ]
    (r : E × Y → J) (hr : Measurable r)
    {B : Set (E × Y)} (hB : MeasurableSet B) :
    (∑ b, ∑ a, (((μ.withDensity (fun e ↦ κ (e,b) {a})).prod ν).restrict
      (B ∩ {z | r z = b})).map (fun z ↦ (z,a))) =
      ((μ.prod ν).restrict B).compProd
        (κ.comap (fun z ↦ (z.1,r z)) (measurable_fst.prodMk hr)) := by
  classical
  let μB := (μ.prod ν).restrict B
  have hm (b : J) (a : A) : Measurable (fun e : E ↦ κ (e,b) {a}) :=
    (κ.measurable_coe (measurableSet_singleton a)).comp measurable_prodMk_right
  have hs (b : J) : MeasurableSet {z : E × Y | r z = b} :=
    measurableSet_eq_fun hr measurable_const
  have hd (a : A) :
      (∑ b, ((μ.withDensity fun e ↦ κ (e,b) {a}).prod ν).restrict
        (B ∩ {z | r z = b})) = μB.withDensity (fun z ↦ κ (z.1,r z) {a}) := by
    trans ∑ b, (μB.withDensity (fun z ↦ κ (z.1,b) {a})).restrict {z | r z = b}
    · apply Finset.sum_congr rfl
      intro b _
      rw [prod_withDensity_left (hm b a), restrict_withDensity (hB.inter (hs b)),
        restrict_withDensity (hs b)]
      congr 1
      simp only [μB, Measure.restrict_restrict (hs b), Set.inter_comm]
    · exact recorded_density_sum μB r hr _ (fun b ↦ (hm b a).comp measurable_fst)
  rw [Finset.sum_comm]
  trans ∑ a, (μB.withDensity (fun z ↦ κ (z.1,r z) {a})).map (fun z ↦ (z,a))
  · apply Finset.sum_congr rfl
    intro a _
    rw [← Measure.map_finset_sum' measurable_prodMk_right.aemeasurable, hd a]
  · exact finite_allocation_joint μB
      (κ.comap (fun z ↦ (z.1,r z)) (measurable_fst.prodMk hr))

lemma map_retained_compProd {E F A : Type*} [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace A]
    (μ : Measure E) [SFinite μ] (f : E → F) (hf : Measurable f)
    (κ : Kernel F A) [IsSFiniteKernel κ] :
    (μ.compProd (κ.comap f hf)).map (fun z ↦ (f z.1,z.2)) =
      (μ.map f).compProd κ := by
  ext B hB
  have hmap : Measurable (fun z : E × A ↦ (f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_apply hmap hB, Measure.compProd_apply (hB.preimage hmap),
    Measure.compProd_apply hB,
    lintegral_map (κ.measurable_kernel_prodMk_left hB) hf]
  rfl

end HardSphere.Comparison

namespace HardSphere.Comparison
variable {E I A : Type*} [MeasurableSpace E] [Fintype I]
variable {X : I → Type*} [∀ i, MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

lemma allocationBase_ae_support {E J A : Type*} [MeasurableSpace E]
    [MeasurableSpace J] [Fintype J] [MeasurableSpace A] [Fintype A]
    [MeasurableSingletonClass A] (μ : Measure E) (κ : Kernel (E × J) A)
    (b : J) (a : A) (P : E → A → Prop)
    (hP : ∀ e, ∀ᵐ a' ∂κ (e,b), P e a') :
    ∀ᵐ e ∂allocationBase μ κ b a, P e a := by
  apply (ae_withDensity_iff ((κ.measurable_coe (measurableSet_singleton a)).comp
    (measurable_id.prodMk measurable_const))).mpr
  apply ae_of_all
  intro e hn
  by_contra h
  apply hn
  exact measure_mono_null (by simpa only [singleton_subset_iff, mem_ofPred_eq] using h)
    (ae_iff.mp (hP e))

lemma exposed_endpoint_ae {E I : Type*} [MeasurableSpace E] [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure E) [SFinite μ] (ν : ∀ i, Measure (X i))
    [∀ i, IsProbabilityMeasure (ν i)] (p : I → Prop) [DecidablePred p]
    (B : Set (E × (∀ i, X i))) {P : E → Prop} (hP : ∀ᵐ e ∂μ, P e) :
    ∀ᵐ w ∂exposedLaw μ ν p B, P w.1 := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact Measure.quasiMeasurePreserving_fst.ae hP

end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison CellOrbital GaussianPacking
attribute [local instance] Classical.propDecidable

lemma recorded_allocation_is_physical {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (μ : Measure (BridgeEndpoints N L))
    (m q : ℕ) (r R C S s₀ t : ℝ) (u : Time) :
    ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin N ↦ Bridge.law),
      gridAllocationKernel hL q
        (z.1, fun i ↦ eligibilityFlag (K:=K) m r R C S s₀ t u i (z.1,z.2 i)) =
      physicalAllocationKernel (K:=K) m q r R C S s₀ u (labelBridgePath N L t z) := by
  have he : ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin N ↦ Bridge.law),
      labelBridgePath N L t z 0 = z.1.2 ∧
      labelBridgePath N L t z 1 = bridgeEnd N L t z.1 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_eq_fun ((continuous_eval_const (0:Time)).measurable.comp
          (labelBridgePath_measurable N L t)) measurable_fst.snd).inter
        (measurableSet_eq_fun ((continuous_eval_const (1:Time)).measurable.comp
          (labelBridgePath_measurable N L t))
          ((bridgeEnd_continuous N L t).measurable.comp measurable_fst)))).mpr
    exact ae_of_all _ (exposed_endpoints t)
  filter_upwards [he] with z hz
  rw [gridAllocationKernel_apply, physicalAllocationKernel, Kernel.comap_apply]
  change Measure.pi _ = Measure.pi _
  congr 1
  funext v
  rw [recordedList_eq hL hK m r R C S s₀ t u v z.1 z.2 hz.1 hz.2]

lemma allocated_selected_flags {N K M G : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N → Bool) (a : GridAllocation N K (G*M))
    (B : Set (BridgeEndpoints N L × (Fin N → Bridge.Noise))) :
    ∀ᵐ _ ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) (fun i ↦ i ∈ groupUnion g a) B,
        ∀ i ∈ groupUnion g a, b i = true := by
  apply exposed_endpoint_ae
    (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
    (fun _ : Fin N ↦ Bridge.law) (fun i ↦ i ∈ groupUnion g a) B
    (P:=fun _ ↦ ∀ i ∈ groupUnion g a, b i = true)
  filter_upwards [allocationBase_ae_support μ (gridAllocationKernel hL (G*M)) b a
    (fun e a' ↦ ∀ v, a' v ∈ (allocationPMF (recordedList hL v (e,b)) (G*M)).support)
    (fun e ↦ gridAllocation_support_ae hL (G*M) (e,b))] with e he
  intro i hi
  obtain ⟨v, _, hiv⟩ := Finset.mem_biUnion.mp hi
  exact (Finset.mem_filter.mp (groupAt_mem_list hL (e,b) a he g v hiv)).2.2

lemma true_flag_endpoint {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (i : Fin N) (e : BridgeEndpoints N L) (β : Bridge.Noise)
    (hb : eligibilityFlag (K:=K) m r R C S s₀ t u i (e,β) = true) :
    EndpointEligible (gridHome hL (e.2 i)) s₀ e.2 (bridgeEnd N L t e) i := by
  have ho : ownEligible (K:=K) m r R C S s₀ t u i (e,β) :=
    of_decide_eq_true hb
  obtain ⟨v, hv, _⟩ := ho
  rwa [(gridHome_eq_iff hL hK _ _).mpr hv.1]

lemma exposed_selected_endpoints {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool)
    (hb : ∀ i : {i // p i}, b i = true) :
    ∀ᵐ w ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r t ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ t u) b),
      ∀ i : {i // p i}, EndpointEligible (gridHome hL (w.1.2 i))
        s₀ w.1.2 (bridgeEnd N L t w.1) i := by
  filter_upwards [exposed_block_positive μ (fun _ : Fin N ↦ Bridge.law) p
    ((labelInteraction_measurable N L r t).inter
      (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ t u i) b))]
    with w hw
  obtain ⟨β,hβ⟩ := nonempty_of_measure_ne_zero hw.ne'
  intro i
  apply true_flag_endpoint hL hK m r R C S s₀ t u i w.1 (β i)
  have hflag := hβ.2 i
  simpa only [blockGlue_fst, blockGlue_inside, hb i] using hflag

lemma exposedAnchorLift_project {N K : ℕ} {L : Length} (hL : L.val = (K : ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) :
    projectPoint L (exposedAnchorLift hL e i) = gridCenter L (gridHome hL (e.2 i)) :=
  nearestLift_project ..

lemma exposedAnchorLift_near {N K : ℕ} {L : Length} (hL : L.val = (K : ℝ))
    (hK : 1 ≤ K) (e : BridgeEndpoints N L) (i : Fin N) :
    ‖labelStartLift e i - exposedAnchorLift hL e i‖ ≤ 3 := by
  rw [norm_sub_rev]
  change ‖nearestLift L (labelStartLift e i) _ - labelStartLift e i‖ ≤ 3
  refine (nearestLift_bound L _ _ (R:=1) ?_).trans (by norm_num)
  have he : projectPoint L (labelStartLift e i) = e.2 i := by
    exact congrFun (project_representative N L e.2) i
  rw [he]
  simpa only [torusDistance, dist_comm] using centeredCell_distance (gridHome_mem hL hK (e.2 i))

lemma canonical_physical_reference {N K : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K) (h50 : 50 < L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (p : Fin N → Prop) (b : Fin N → Bool) (hb : ∀i : {i // p i}, b i = true) :
    ∀ᵐ w ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t) ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ExposedPhysicalIdentity hL m r R C S s₀ t u p b w := by
  unfold ExposedPhysicalIdentity
  filter_upwards [physical_recorded_reference hL hK h50 μ m r R C S s₀ t u p b hb,
    exposed_selected_endpoints hL hK μ m r R C S s₀ (2*t) u p b hb] with w hw he
  exact hw (fun i ↦ gridHome hL (w.1.2 i)) (fun i ↦ exposedAnchorLift hL w.1 i)
    (fun i ↦ exposedAnchorLift_project hL w.1 i)
    (fun i ↦ exposedAnchorLift_near hL hK w.1 i) he

theorem actual_allocated_physical_reference {N K M G : ℕ} {L : Length}
    (hL : L.val = (K : ℝ)) (hK : 1 ≤ K) (h50 : 50 < L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N → Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i ∈ groupUnion g a
    ∀ᵐ w ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t) ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ExposedPhysicalIdentity hL m r R C S s₀ t u p b w := by
  dsimp only
  let p := fun i ↦ i ∈ groupUnion g a
  let base := allocationBase μ (gridAllocationKernel hL (G*M)) b a
  by_cases hb : ∀ i : {i // p i}, b i = true
  · have h := canonical_physical_reference hL hK h50 base m r R C S s₀ t u p b hb
    have hd : (fun i ↦ Classical.propDecidable (p i)) =
        (fun i ↦ Finset.decidableMem i (groupUnion g a)) := Subsingleton.elim _ _
    rw [hd] at h
    exact h
  · filter_upwards [allocated_selected_flags hL μ g b a
      (labelInteraction N L r (2*t) ∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)] with w hw
    exact (hb (fun i ↦ hw i i.property)).elim

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ExposedReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {E : Type*} [MeasurableSpace E]

lemma exposedBridgeKernel_apply (t : ℝ) (y z : Point) :
    exposedBridgeKernel t (y,z)=law.map (leg t y z) := by
  rw [exposedBridgeKernel,Kernel.map_apply _ (leg_all_continuous t).measurable,
    Kernel.prod_apply,Kernel.deterministic_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (leg_all_continuous t).measurable
      (measurable_const.prodMk measurable_id : Measurable (Prod.mk (id (y,z))))]
  rfl

lemma parameterBridgeKernel_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z) (e : E) :
    parameterBridgeKernel t y z hy hz e=law.map (leg t (y e) (z e)) := exposedBridgeKernel_apply _ _ _

lemma parameterIndividualReference_apply (t : ℝ) (y z : E→Point) (hy : Measurable y) (hz : Measurable z)
    (S : Set (E×C(Time,Point))) (hS : MeasurableSet S) (e : E) :
    parameterIndividualReference t y z hy hz S hS e=individualReference t (y e) (z e) (Prod.mk e ⁻¹' S) := by
  rw [parameterIndividualReference,parameterSuccessKernel_apply,parameterBridgeKernel_apply]
  rfl

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PeriodShift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma project_shift {L : Length} (c : Point) (hc : projectPoint L c=0) (f : C(Time,Point)) :
    projectCurve L (shiftPath c f)=projectCurve L f := by
  ext s i j
  change (((f s j+c j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun hc j
  change ((c j:ℝ):AddCircle L.val)=0 at h
  rw [h,add_zero]
  rfl

lemma projectPoint_shift {L : Length} (c : Point) (hc : projectPoint L c=0) (v : Point) :
    projectPoint L (v+c)=projectPoint L v := by
  ext j
  change (((v j+c j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun hc j
  change ((c j:ℝ):AddCircle L.val)=0 at h
  rw [h,add_zero]

lemma permittedPath_shift {J : Type*} {L : Length} (n : ℕ) (r R C S : ℝ)
    (w : Time) (y z v c : Point) (hc : projectPoint L c=0) (F : J → ConfigurationPath 1 L)
    (f : C(Time,Point)) :
    shiftPath c f∈permittedPath n r R C S w (y+c) (z+c) (v+c) F ↔
      f∈permittedPath n r R C S w y z v F := by
  simp only [permittedPath,mem_ofPred_eq,project_shift c hc]
  have hconf : TrialConfined L (v+c) (shiftPath c f) ↔ TrialConfined L v f := by
    simp only [TrialConfined,shiftPath,ContinuousMap.add_apply,ContinuousMap.const_apply,
      add_sub_add_right_eq_sub,projectPoint_shift c hc]
  rw [hconf]
  have hpin : shiftPath c f∈fixedEndpoints (y+c) (z+c) ↔ f∈fixedEndpoints y z := by
    simp only [fixedEndpoints,mem_ofPred_eq,shiftPath,ContinuousMap.add_apply,ContinuousMap.const_apply,
      add_left_inj]
  rw [hpin]
  have hp (s : Time) : projectPoint L (shiftPath c f s)=projectPoint L (f s) :=
    projectPoint_shift c hc (f s)
  simp only [TrialCollision,hp]

lemma individualReference_shift (t : ℝ) (y z c : Point)
    (S T : Set C(Time,Point)) (hT : MeasurableSet T)
    (hST : ∀f,shiftPath c f∈T ↔ f∈S) :
    (individualReference t y z S).map (shiftPath c)=
      individualReference t (y+c) (z+c) T := by
  have he : S=(shiftPath c)⁻¹' T := by ext f;exact (hST f).symm
  change (conditionedMeasure (law.map (leg (2*t) y z)) S).map (shiftPath c)=_
  rw [he,conditioned_map_preimage _ _ (shiftPath_continuous c).measurable hT,
    Measure.map_map (shiftPath_continuous c).measurable (leg_continuous ..).measurable]
  congr 1
  congr 1
  funext β
  exact (leg_translate (2*t) y z c β).symm

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDatum
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalDatum_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) :
    Measurable (physicalDatum (N:=N) (K:=K) (M:=M) (L:=L) g m r R C S s₀ u) := by
  unfold physicalDatum
  apply ((continuous_eval_const 0).measurable.comp measurable_fst).prodMk
  apply ((continuous_eval_const 1).measurable.comp measurable_fst).prodMk
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro i
    have h : MeasurableSet {z : ConfigurationPath N L × GridAllocation N K (G*M) |
        ∃v : Fin 3 → Fin K, Eligible m r R C S s₀ u v i z.1} := by
      simp only [Set.ofPred_exists]
      exact MeasurableSet.iUnion fun v ↦
        (eligible_measurable m r R C S s₀ u v i).preimage measurable_fst
    apply measurable_to_countable'
    intro b
    cases b
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_false_iff_not,←Set.compl_ofPred] using h.compl
    · simpa only [Set.preimage,Set.mem_singleton_iff,decide_eq_true_eq] using h
  apply measurable_snd.prodMk
  apply Measurable.of_eval
  intro i
  apply Measurable.ite
    (measurable_snd ((Set.to_countable {a : GridAllocation N K (G*M) | i∈groupUnion g a}).measurableSet))
    measurable_const
  exact (onePathAt_continuous i).measurable.comp measurable_fst

lemma physicalDatumLaw_probability {N K M G : ℕ} {L : Length} (g : Fin G)
    {ψ : Jet N L} {r : ℝ} (hψ : IsGroundVector N L r ψ)
    (m : ℕ) (R C S s₀ T : ℝ) (hT : 0≤T) (u : Time) :
    IsProbabilityMeasure (physicalDatumLaw (K:=K) (M:=M) g ψ m r R C S s₀ T u) := by
  have := hψ.groundPathLaw_probability hT
  unfold physicalDatumLaw
  exact Measure.isProbabilityMeasure_map (physicalDatum_measurable g m r R C S s₀ u).aemeasurable

lemma anchorPoint_project {K : ℕ} (L : Length) (v : Fin 3 → Fin K) :
    projectPoint L (anchorPoint v)=gridCenter L v := rfl

attribute [local irreducible] TrialCollision

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_NearLift
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking PathCutoff CellOrbital

lemma nearestLift_eq_of_near {L : Length} (hL : 50<L.val) (c y : Point)
    (hy : ‖y-c‖≤3) : nearestLift L c (projectPoint L y)=y := by
  ext j
  have hj : |y j-c j|≤3 := (norm_le_pi_norm (y-c) j).trans hy
  have hmem : y j-c j∈Set.Ico (-L.val/2) (-L.val/2+L.val) := by
    rw [abs_le] at hj
    constructor <;> linarith
  change ((AddCircle.equivIco L.val (-L.val/2)) ((y j:AddCircle L.val)-(c j:AddCircle L.val))).val+c j=y j
  rw [←AddCircle.coe_sub,AddCircle.equivIco_coe_eq hmem]
  simp

lemma near_lift_unique {L : Length} (hL : 50<L.val) (c y : Point) (x : Torus L)
    (hp : projectPoint L y=x) (hy : ‖y-c‖≤3) : y=nearestLift L c x := by
  subst x
  exact (nearestLift_eq_of_near hL c y hy).symm

attribute [local instance] Classical.propDecidable

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma labelStartLift_project {N : ℕ} {L : Length} (e : BridgeEndpoints N L) (i : Fin N) :
    projectPoint L (labelStartLift e i)=e.2 i :=
  congrFun (project_representative N L e.2) i

lemma labelEndLift_project {N : ℕ} {L : Length} (t : ℝ) (e : BridgeEndpoints N L) (i : Fin N) :
    projectPoint L (labelEndLift t e i)=bridgeEnd N L t e i := by
  ext j
  change ((labelStartLift e i j+Real.sqrt (2*t)*e.1 (i,j):ℝ):AddCircle L.val)=_
  rw [AddCircle.coe_add]
  have h := congrFun (labelStartLift_project e i) j
  change ((labelStartLift e i j:ℝ):AddCircle L.val)=e.2 i j at h
  rw [h]
  rfl

lemma exposed_selected_near {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (hK : 1≤K) (h50 : 50<L.val) (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (p : Fin N→Prop) (b : Fin N→Bool)
    (hb : ∀i : {i // p i},b i=true) :
    ∀ᵐw ∂exposedLaw μ (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ∀i : {i // p i},‖labelEndLift (2*t) w.1 i-exposedAnchorLift hL w.1 i‖≤3 := by
  filter_upwards [recorded_physical_fiber μ r (2*t)
    (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u)
    (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b p,
    exposed_selected_endpoints hL hK μ m r R C S s₀ (2*t) u p b hb] with w hw he
  intro i
  apply near_end_of_positive_confined h50 (2*t) (labelStartLift w.1 i)
    (labelEndLift (2*t) w.1 i) (exposedAnchorLift hL w.1 i)
    (exposedAnchorLift_near hL hK w.1 i)
  · rw [labelEndLift_project,exposedAnchorLift_project]
    exact (he i).2.1
  · have hs : individualFiber p (noisePairAvoid r (2*t) w.1)
        (fun j β ↦ eligibilityFlag (K:=K) m r R C S s₀ (2*t) u j (w.1,β)) b w.2 i ⊆
        {β | ∀s : Time,torusDistance L
          (projectPoint L (leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) β s))
          (projectPoint L (exposedAnchorLift hL w.1 i))≤10} := by
      intro β hβ
      have hf := hβ.1
      rw [hb i] at hf
      have ho : ownEligible (K:=K) m r R C S s₀ (2*t) u i (w.1,β) := by
        simpa only [eligibilityFlag,decide_eq_true_eq] using hf
      rw [ownEligible_at hL hK m r R C S s₀ (2*t) u i w.1 β _ (he i)] at ho
      intro s
      rw [exposedAnchorLift_project]
      exact ho.2 s
    exact ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr (hw.2.1 i)) (measure_mono hs))

lemma canonicalShift_period {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) : projectPoint L (canonicalShift hL e i)=0 := by
  ext j
  change (((anchorPoint (gridHome hL (e.2 i)) j-exposedAnchorLift hL e i j):ℝ):AddCircle L.val)=0
  rw [AddCircle.coe_sub]
  exact sub_eq_zero.mpr (congrFun ((anchorPoint_project L _).trans (exposedAnchorLift_project hL e i).symm) j)

lemma canonicalShift_anchor {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (e : BridgeEndpoints N L) (i : Fin N) :
    exposedAnchorLift hL e i+canonicalShift hL e i=anchorPoint (gridHome hL (e.2 i)) := by
  unfold canonicalShift
  abel

lemma canonicalShift_start {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (hK : 1≤K) (h50 : 50<L.val) (e : BridgeEndpoints N L) (i : Fin N) :
    labelStartLift e i+canonicalShift hL e i=
      nearestLift L (anchorPoint (gridHome hL (e.2 i))) (e.2 i) := by
  apply near_lift_unique h50
  · rw [projectPoint_shift _ (canonicalShift_period hL e i),labelStartLift_project]
  · have he : labelStartLift e i+canonicalShift hL e i-anchorPoint (gridHome hL (e.2 i))=
        labelStartLift e i-exposedAnchorLift hL e i := by unfold canonicalShift; abel
    rw [he]
    exact exposedAnchorLift_near hL hK e i

lemma canonicalShift_end {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (h50 : 50<L.val) (e : BridgeEndpoints N L) (i : Fin N) (t : ℝ)
    (hz : ‖labelEndLift (2*t) e i-exposedAnchorLift hL e i‖≤3) :
    labelEndLift (2*t) e i+canonicalShift hL e i=
      nearestLift L (anchorPoint (gridHome hL (e.2 i))) (bridgeEnd N L (2*t) e i) := by
  apply near_lift_unique h50
  · rw [projectPoint_shift _ (canonicalShift_period hL e i),labelEndLift_project]
  · have he : labelEndLift (2*t) e i+canonicalShift hL e i-anchorPoint (gridHome hL (e.2 i))=
        labelEndLift (2*t) e i-exposedAnchorLift hL e i := by unfold canonicalShift; abel
    rwa [he]

lemma physicalMutual_shift_preimage {I : Type*} {L : Length} (r : ℝ)
    (c : I→Point) (hc : ∀i,projectPoint L (c i)=0) :
    (fun f : I→C(Time,Point) ↦ fun i ↦ Bridge.shiftPath (c i) (f i)) ⁻¹'
      physicalMutual (L:=L) r=physicalMutual (L:=L) r := by
  ext f
  simp only [physicalMutual,pairEvent,mem_preimage,mem_ofPred_eq,project_shift _ (hc _)]
  have he (i j : I) : TrialCollision (L:=L) r (projectCurve L (f j)) (Bridge.shiftPath (c i) (f i)) ↔
      TrialCollision (L:=L) r (projectCurve L (f j)) (f i) := by
    simp only [TrialCollision,Bridge.shiftPath,ContinuousMap.add_apply,ContinuousMap.const_apply,
      projectPoint_shift _ (hc i)]
  simp only [he]

lemma canonical_reference_transport {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (m : ℕ) (r R C S t : ℝ) (u : Time) (e : BridgeEndpoints N L)
    (p : Fin N→Prop) (w : {i // ¬p i}→Bridge.Noise)
    (hz : ∀i : {i // p i},‖labelEndLift (2*t) e i-exposedAnchorLift hL e i‖≤3) :
    (conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
        (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
          (exposedAnchorLift hL e i) (frozenPaths (2*t) e p w))) (physicalMutual (L:=L) r)).map
      (fun (f : {i // p i} → C(Time,Point)) (i : {i // p i}) ↦ Bridge.shiftPath (canonicalShift hL e i) (f i)) =
    conditionedMeasure (Measure.pi fun i : {i // p i} ↦
      individualReference t
        (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (e.2 i))
        (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (bridgeEnd N L (2*t) e i))
        (permittedPath m r R C S u
          (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (e.2 i))
          (nearestLift L (anchorPoint (gridHome hL (e.2 i))) (bridgeEnd N L (2*t) e i))
          (anchorPoint (gridHome hL (e.2 i))) (frozenPaths (2*t) e p w)))
      (physicalMutual (L:=L) r) := by
  let μ := fun i : {i // p i} ↦ individualReference t (labelStartLift e i) (labelEndLift (2*t) e i)
    (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
      (exposedAnchorLift hL e i) (frozenPaths (2*t) e p w))
  have (i : {i // p i}) : IsFiniteMeasure (μ i) := conditioned_finite _ _
  have H := conditioned_pi_map μ (fun i ↦ Bridge.shiftPath (canonicalShift hL e i))
    (fun i ↦ (Bridge.shiftPath_continuous _).measurable) (physicalMutual_measurable (I:={i // p i}) (L:=L) r)
  rw [physicalMutual_shift_preimage (I:={i // p i}) r
    (fun i ↦ canonicalShift hL e i) (fun i ↦ canonicalShift_period hL e i)] at H
  rw [H]
  congr 1
  apply congrArg Measure.pi
  funext i
  have h := individualReference_shift t (labelStartLift e i) (labelEndLift (2*t) e i) (canonicalShift hL e i)
    (permittedPath m r R C S u (labelStartLift e i) (labelEndLift (2*t) e i)
      (exposedAnchorLift hL e i) (frozenPaths (2*t) e p w))
    (permittedPath m r R C S u (labelStartLift e i+canonicalShift hL e i)
      (labelEndLift (2*t) e i+canonicalShift hL e i)
      (exposedAnchorLift hL e i+canonicalShift hL e i) (frozenPaths (2*t) e p w))
    (permittedPath_measurable ..)
    (permittedPath_shift m r R C S u _ _ _ _ (canonicalShift_period hL e i) _)
  simpa only [canonicalShift_start hL hK h50,canonicalShift_end hL h50 e i t (hz i),
    canonicalShift_anchor] using h

theorem actual_allocated_canonical_reference {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    ∀ᵐw ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ((fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
        (blockEvent p (labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b))) w).map
        (fun β (i : {i // p i}) ↦ Bridge.shiftPath (canonicalShift hL w.1 i)
          (leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i))) =
      conditionedMeasure (Measure.pi fun i : {i // p i} ↦
        individualReference t
          (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (w.1.2 i))
          (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (bridgeEnd N L (2*t) w.1 i))
          (permittedPath m r R C S u
            (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (w.1.2 i))
            (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (bridgeEnd N L (2*t) w.1 i))
            (anchorPoint (gridHome hL (w.1.2 i))) (frozenPaths (2*t) w.1 p w.2)))
        (physicalMutual (L:=L) r) := by
  dsimp only
  let p := fun i ↦ i∈groupUnion g a
  let base := allocationBase μ (gridAllocationKernel hL (G*M)) b a
  by_cases hb : ∀i : {i // p i},b i=true
  · have hn := exposed_selected_near hL hK h50 base m r R C S s₀ t u p b hb
    have hd : (fun i ↦ Classical.propDecidable (p i)) =
        (fun i ↦ Finset.decidableMem i (groupUnion g a)) := Subsingleton.elim _ _
    rw [hd] at hn
    filter_upwards [actual_allocated_physical_reference hL hK h50 μ m r R C S s₀ t u g b a,
      hn] with w hw hz
    have H := canonical_reference_transport hL hK h50 m r R C S t u w.1 p w.2 hz
    rw [←hw] at H
    have hm : Measurable (fun β : {i // p i}→Bridge.Noise ↦ fun i : {i // p i} ↦
        leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i)) :=
      Measurable.of_eval (fun i ↦ (leg_continuous (2*t) _ _).measurable.comp (measurable_pi_apply i))
    have hc : Measurable (fun f : {i // p i}→C(Time,Point) ↦ fun i : {i // p i} ↦
        Bridge.shiftPath (canonicalShift hL w.1 i) (f i)) := by fun_prop
    rw [Measure.map_map hc hm] at H
    have hC : MeasurableSet (blockEvent p (labelInteraction N L r (2*t)∩
        flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)) :=
      ((labelInteraction_measurable N L r (2*t)).inter
        (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)).preimage
          (blockGlue_measurable p)
    have he : fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
        (blockEvent p (labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)) w =
        conditionedMeasure (Measure.pi fun _ : {i // p i} ↦ Bridge.law)
          {β | blockGlue p (w,β) ∈ labelInteraction N L r (2*t)∩
            flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b} := by
      change (fiberRestrict _ _ w univ)⁻¹ • fiberRestrict _ _ w=_
      rw [fiberRestrict_apply _ hC]
      simp only [Kernel.const_apply,Measure.restrict_apply_univ,conditionedMeasure]
      rfl
    rw [he]
    convert H using 1 <;> congr 10
    all_goals try exact Subsingleton.elim _ _
    all_goals rw [hd]
  · filter_upwards [allocated_selected_flags hL μ g b a
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b)] with w hw
    exact (hb (fun i ↦ hw i i.property)).elim

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_GlobalExposure
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E I : Type*} [MeasurableSpace E] [Fintype I]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma blockExpose_measurable (p : I → Prop) : Measurable (blockExpose (E:=E) (X:=X) p) :=
  measurable_fst.prodMk (Measurable.of_eval fun i ↦
    (measurable_pi_apply i.val).comp measurable_snd)

omit [MeasurableSpace E] [Fintype I] in
lemma blockExpose_glue (p : I → Prop) [DecidablePred p] :
    blockExpose (E:=E) (X:=X) p ∘ blockGlue p = Prod.fst := by
  funext z
  apply Prod.ext
  · rfl
  funext i
  simp [blockExpose,blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,i.property]

lemma exposedLaw_marginal (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I → Prop) [DecidablePred p] {B : Set (E × (∀i,X i))}
    (hB : MeasurableSet B) :
    exposedLaw μ ν p B = ((μ.prod (Measure.pi ν)).restrict B).map (blockExpose p) := by
  have : SFinite (exposedLaw μ ν p B) := by unfold exposedLaw; infer_instance
  rw [←exposed_block_reconstruct μ ν p hB,
    Measure.map_map (blockExpose_measurable p) (blockGlue_measurable p),blockExpose_glue]
  symm
  exact fiberNormalize_fst (exposedLaw μ ν p B)
    (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i))
    (hB.preimage (blockGlue_measurable p)) (exposed_block_positive μ ν p hB)

variable {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
attribute [local instance] Classical.propDecidable

omit [Fintype I] in
lemma fillOutside_measurable (p : I → Prop) (x₀ : ∀i,X i) :
    Measurable (fillOutside p x₀) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : p i
  · simpa only [fillOutside,dite_eq_left hi] using
      (measurable_const : Measurable (fun _ : ∀i : {i // ¬p i},X i ↦ x₀ i))
  · simpa only [fillOutside,dite_eq_right hi] using (measurable_pi_apply (⟨i,hi⟩ : {i // ¬p i}))

end HardSphere.Comparison

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_CoarsePhysical
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma frozenPaths_joint_measurable {N : ℕ} {L : Length} (T : ℝ)
    (p : Fin N→Prop) (j : {i // ¬p i}) :
    Measurable (fun w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise) ↦
      frozenPaths T w.1 p w.2 j) := by
  have hp : Measurable (fun w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise) ↦
      (w.1,fillOutside p (fun _ ↦ (0 : Bridge.Noise)) w.2)) :=
    measurable_fst.prodMk ((fillOutside_measurable p (fun _ ↦ (0 : Bridge.Noise))).comp measurable_snd)
  have hω := (labelBridgePath_measurable N L T).comp hp
  have hm : Measurable (fun w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise) ↦
      onePathAt j (labelBridgePath N L T (w.1,fillOutside p (fun _ ↦ 0) w.2))) :=
    (onePathAt_continuous (j : Fin N)).measurable.comp hω
  simpa only [labelBridgePath_lift,fillOutside,dite_eq_right j.property,frozenPaths] using hm

lemma physicalBranchDatum_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (b : Fin N→Bool) (a : GridAllocation N K (G*M)) (T : ℝ) :
    Measurable (physicalBranchDatum (L:=L) g b a T) := by
  unfold physicalBranchDatum
  apply measurable_fst.snd.prodMk
  apply ((bridgeEnd_continuous N L T).measurable.comp measurable_fst).prodMk
  apply measurable_const.prodMk
  apply measurable_const.prodMk
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈groupUnion g a
  · simpa only [dite_eq_left hi] using (measurable_const : Measurable
      (fun _ : BridgeEndpoints N L × ({i // i∉groupUnion g a}→Bridge.Noise) ↦
        (0 : ConfigurationPath 1 L)))
  · simpa only [dite_eq_right hi] using frozenPaths_joint_measurable (L:=L) T
      (fun j ↦ j∈groupUnion g a) (⟨i,hi⟩ : {i // i∉groupUnion g a})

lemma datumPermitted_branch {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S T : ℝ) (u : Time)
    (w : BridgeEndpoints N L × ({i // i∉groupUnion g a}→Bridge.Noise)) (i : Fin N) :
    Prod.mk (physicalBranchDatum g b a T w) ⁻¹' datumPermitted hL g m r R C S u i =
      permittedPath m r R C S u
        (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (w.1.2 i))
        (nearestLift L (anchorPoint (gridHome hL (w.1.2 i))) (bridgeEnd N L T w.1 i))
        (anchorPoint (gridHome hL (w.1.2 i)))
        (frozenPaths T w.1 (fun j ↦ j∈groupUnion g a) w.2) := by
  ext f
  simp only [mem_preimage,datumPermitted,mem_ofPred_eq,physicalBranchDatum,
    datumStart,datumEnd,datumHome,datumSelected,permittedPath]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h j
    simpa only [dite_eq_right j.property] using h j j.property
  · intro h j hj
    simpa only [dite_eq_right hj] using h ⟨j,hj⟩

lemma datumIndividualReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N)
    (d : PhysicalDatum N K M G L) :
    datumIndividualReference hL g m r R C S t u i d=
      individualReference t (datumStart hL d i) (datumEnd hL d i)
        (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i) :=
  parameterIndividualReference_apply ..

lemma datumGroupReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) (d : PhysicalDatum N K M G L) :
    datumGroupReference hL g a m r R C S t u d=
      conditionedMeasure (Measure.pi fun i : {i // i∈groupUnion g a} ↦
        individualReference t (datumStart hL d i) (datumEnd hL d i)
          (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i)) (physicalMutual (L:=L) r) := by
  unfold datumGroupReference
  change (fiberRestrict _ _ d univ)⁻¹ • fiberRestrict _ _ d=_
  rw [fiberRestrict_apply _ ((physicalMutual_measurable r).preimage measurable_snd)]
  simp only [Measure.restrict_apply_univ,finiteKernelPi_apply,datumIndividualReference_apply]
  rfl

end HardSphere.Groups

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma projectGroup_measurable {I : Type*} {L : Length} :
    Measurable (projectGroup (I:=I) (L:=L)) :=
  Measurable.of_eval fun i ↦ (projectCurve_continuous L).measurable.comp (measurable_pi_apply i)

lemma selectedPhysicalPath_measurable {N : ℕ} {L : Length} (T : ℝ) (p : Fin N→Prop) :
    Measurable (selectedPhysicalPath (L:=L) T p) := by
  apply Measurable.of_eval
  intro i
  exact (onePathAt_continuous (i : Fin N)).measurable.comp
    ((labelBridgePath_measurable N L T).comp (blockGlue_measurable p))

lemma selectedPhysicalPath_apply {N : ℕ} {L : Length} (T : ℝ) (p : Fin N→Prop)
    (w : BridgeEndpoints N L × ({i // ¬p i}→Bridge.Noise))
    (β : {i // p i}→Bridge.Noise) (i : {i // p i}) :
    selectedPhysicalPath T p (w,β) i=
      projectCurve L (leg T (labelStartLift w.1 i) (labelEndLift T w.1 i) (β i)) := by
  unfold selectedPhysicalPath
  rw [labelBridgePath_lift,blockGlue_fst,blockGlue_inside]

theorem actual_allocated_physical_coarse_fiber {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    ∀ᵐw ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      ((fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
        (blockEvent p (labelInteraction N L r (2*t)∩
          flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b))) w).map
        (fun β ↦ selectedPhysicalPath (L:=L) (2*t) p (w,β)) =
      datumPhysicalReference hL g a m r R C S t u (physicalBranchDatum g b a (2*t) w) := by
  dsimp only
  filter_upwards [actual_allocated_canonical_reference hL hK h50 μ m r R C S s₀ t u g b a] with w hw
  rw [datumPhysicalReference,Kernel.map_apply _ projectGroup_measurable,
    datumGroupReference_apply]
  simp only [datumPermitted_branch]
  simp only [datumStart,datumEnd,datumHome,physicalBranchDatum]
  have hh := congrArg (fun ν ↦ ν.map (projectGroup (L:=L))) hw
  have hm : Measurable (fun β : {i // i ∈ groupUnion g a} → Bridge.Noise ↦
      fun i : {i // i ∈ groupUnion g a} ↦ Bridge.shiftPath (canonicalShift hL w.1 i)
        (leg (2*t) (labelStartLift w.1 i) (labelEndLift (2*t) w.1 i) (β i))) :=
    Measurable.of_eval fun i ↦
      (Bridge.shiftPath_continuous _).measurable.comp
        ((leg_continuous _ _ _).measurable.comp (measurable_pi_apply i))
  rw [Measure.map_map projectGroup_measurable hm] at hh
  rw [←hh]
  apply congrArg (Measure.map · _)
  funext β i
  simp only [Function.comp_apply,projectGroup,selectedPhysicalPath_apply,
    project_shift _ (canonicalShift_period hL w.1 i)]

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDisintegration
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma label_endpoints_ae {N : ℕ} {L : Length} (T : ℝ)
    (μ : Measure (BridgeEndpoints N L)) :
    ∀ᵐ z ∂μ.prod (Measure.pi fun _ : Fin N ↦ Bridge.law),
      labelBridgePath N L T z 0=z.1.2 ∧
      labelBridgePath N L T z 1=bridgeEnd N L T z.1 := by
  apply (Measure.ae_prod_iff_ae_ae
    ((measurableSet_eq_fun ((continuous_eval_const (0:Time)).measurable.comp
        (labelBridgePath_measurable N L T)) measurable_fst.snd).inter
      (measurableSet_eq_fun ((continuous_eval_const (1:Time)).measurable.comp
        (labelBridgePath_measurable N L T))
        ((bridgeEnd_continuous N L T).measurable.comp measurable_fst)))).mpr
  exact ae_of_all _ (exposed_endpoints T)

lemma physicalDatum_branch_of {N K M G : ℕ} {L : Length}
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time)
    (z : BridgeEndpoints N L × (Fin N→Bridge.Noise))
    (h0 : labelBridgePath N L T z 0=z.1.2)
    (h1 : labelBridgePath N L T z 1=bridgeEnd N L T z.1)
    (hb : z∈flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b) :
    physicalDatum g m r R C S s₀ u (labelBridgePath N L T z,a)=
      physicalBranchDatum g b a T (blockExpose (fun i ↦ i∈groupUnion g a) z) := by
  have hf : (fun i ↦ decide (∃v : Fin 3→Fin K,
      Eligible m r R C S s₀ u v i (labelBridgePath N L T z)))=b := by
    funext i
    have hi := hb i
    simpa only [eligibilityFlag,ownEligible,Eligible,h0,h1,ownPath_eq] using hi
  simp only [physicalDatum,physicalBranchDatum,h0,h1,hf,blockExpose]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
  funext i
  by_cases hi : i∈groupUnion g a
  · simp only [ite_eq_left hi,dite_eq_left hi]
  · simp only [ite_eq_right hi,dite_eq_right hi]
    rw [labelBridgePath_lift]
    rfl

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma individualReference_probability_of_nonzero (t : ℝ) (y z : Point)
    (E : Set C(Time,Point)) (h : individualReference t y z E≠0) :
    IsProbabilityMeasure (individualReference t y z E) := by
  have : IsProbabilityMeasure (law.map (leg (2*t) y z)) :=
    (Measure.isProbabilityMeasure_map_iff
      (leg_continuous (2*t) y z).measurable.aemeasurable).mpr inferInstance
  apply conditioned_probability
  intro hz
  apply h
  simp only [individualReference,Measure.restrict_eq_zero.mpr hz,smul_zero]

lemma datum_group_probability_factors {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S t : ℝ) (u : Time) (d : PhysicalDatum N K M G L)
    (hmass : datumGroupReference hL g a m r R C S t u d univ=1) :
    ∀i : {i // i∈groupUnion g a},
      IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u i d) := by
  let μ := fun i : {i // i∈groupUnion g a} ↦ datumIndividualReference hL g m r R C S t u i d
  have : ∀i,IsFiniteMeasure (μ i) := fun _ ↦ inferInstance
  have hcond : conditionedMeasure (Measure.pi μ) (physicalMutual (L:=L) r) univ=1 := by
    simpa only [μ,datumGroupReference_apply,datumIndividualReference_apply] using hmass
  have hprod : (Measure.pi μ) univ≠0 := by
    intro hz
    have he : (Measure.pi μ) (physicalMutual (L:=L) r)=0 := measure_mono_null (subset_univ _) hz
    simp only [conditionedMeasure,Measure.restrict_eq_zero.mpr he,smul_zero,Measure.coe_zero,Pi.zero_apply] at hcond
    exact zero_ne_one hcond
  intro i
  rw [datumIndividualReference_apply]
  apply individualReference_probability_of_nonzero
  intro hz
  have hi : μ i=0 := by simpa only [μ,datumIndividualReference_apply] using hz
  apply hprod
  rw [Measure.pi_univ]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; rfl)

lemma exposed_fiber_mass {E I : Type*} [MeasurableSpace E] [Fintype I]
    {X : I→Type*} [∀i,MeasurableSpace (X i)]
    (μ : Measure E) [SFinite μ] (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : I→Prop) [DecidablePred p] {B : Set (E×(∀i,X i))} (hB : MeasurableSet B) :
    ∀ᵐw ∂exposedLaw μ ν p B,
      fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i))
        (blockGlue p ⁻¹' B) w univ=1 := by
  filter_upwards [exposed_block_positive μ ν p hB] with w hw
  exact fiberNormalize_mass (Kernel.const _ (Measure.pi fun i : {i // p i} ↦ ν i))
    (hB.preimage (blockGlue_measurable p)) hw

theorem actual_branch_normalized {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    ∀ᵐw ∂exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p
      (labelInteraction N L r (2*t)∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b),
      IsProbabilityMeasure (datumGroupReference hL g a m r R C S t u
        (physicalBranchDatum g b a (2*t) w)) ∧
      ∀i : {i // i∈groupUnion g a},IsProbabilityMeasure
        (datumIndividualReference hL g m r R C S t u i (physicalBranchDatum g b a (2*t) w)) := by
  dsimp only
  let p := fun i ↦ i∈groupUnion g a
  let B := labelInteraction N L r (2*t)∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
  have hB : MeasurableSet B := (labelInteraction_measurable N L r (2*t)).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)
  have hpos := exposed_fiber_mass (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
    (fun _ : Fin N ↦ Bridge.law) p hB
  filter_upwards [actual_allocated_physical_coarse_fiber hL hK h50 μ m r R C S s₀ t u g b a,
    hpos] with w hw hp
  change (_ : ℝ≥0∞)=1 at hp
  have hh := congrArg (fun ν ↦ ν univ) hw
  rw [Measure.map_apply (by exact (selectedPhysicalPath_measurable (L:=L) (2*t) (fun i ↦ i∈groupUnion g a)).comp (measurable_const.prodMk measurable_id)) MeasurableSet.univ,preimage_univ] at hh
  change (fiberNormalize _ (blockGlue p ⁻¹' B) w) univ = _ at hh
  have hh' : (datumPhysicalReference hL g a m r R C S t u
      (physicalBranchDatum g b a (2*t) w)) univ=1 :=
    hh.symm.trans (by
      convert hp using 1
      all_goals try with_reducible_and_instances rfl
      congr
      exact Subsingleton.elim _ _)
  have hmass : datumGroupReference hL g a m r R C S t u (physicalBranchDatum g b a (2*t) w) univ=1 := by
    rw [datumPhysicalReference,Kernel.map_apply _ projectGroup_measurable,
      Measure.map_apply projectGroup_measurable MeasurableSet.univ,preimage_univ] at hh'
    exact hh'
  exact ⟨⟨hmass⟩,datum_group_probability_factors hL g a m r R C S t u _ hmass⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma measurable_probability_kernel {D W : Type*} [MeasurableSpace D] [MeasurableSpace W]
    (κ : Kernel D W) : MeasurableSet {d | IsProbabilityMeasure (κ d)} := by
  simp only [isProbabilityMeasure_iff]
  exact measurableSet_eq_fun (κ.measurable_coe MeasurableSet.univ) measurable_const

attribute [local irreducible] datumGroupReference datumIndividualReference

lemma physicalBranchLaw_raw {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    physicalBranchLaw hL μ g b a m r R C S s₀ T u =
    (((allocationBase μ (gridAllocationKernel hL (G*M)) b a).prod
      (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
      (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)).map
        (fun z ↦ physicalDatum g m r R C S s₀ u (labelBridgePath N L T z,a)) := by
  have hB := (labelInteraction_measurable N L r T).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable (K:=K) m r R C S s₀ T u i) b)
  rw [physicalBranchLaw,exposedLaw_marginal _ _ _ hB,
    Measure.map_map (physicalBranchDatum_measurable g b a T) (blockExpose_measurable _)]
  apply Measure.map_congr
  filter_upwards [ae_restrict_of_ae (label_endpoints_ae T
    (allocationBase μ (gridAllocationKernel hL (G*M)) b a)),ae_restrict_mem hB] with z hz hb
  exact (physicalDatum_branch_of g b a m r R C S s₀ T u z hz.1 hz.2 hb.2).symm

lemma genuine_ground_allocated_raw {N K : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (ψ : Jet N L)
    (m q : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    (∑b,∑a : GridAllocation N K q,
      (((allocationBase (endpointWeightedBase ψ T) (gridAllocationKernel hL q) b a).prod
        (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
        (labelInteraction N L r T∩flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b)).map
          (fun z ↦ (labelBridgePath N L T z,a)))=
      (groundPathLaw N L r T ψ).compProd (physicalAllocationKernel (K:=K) m q r R C S s₀ u) := by
  let flag := eligibilityFlag (N:=N) (K:=K) (L:=L) m r R C S s₀ T u
  have hflag : ∀i,Measurable (flag i) := fun i ↦ eligibilityFlag_measurable m r R C S s₀ T u i
  let base := ((endpointWeightedBase ψ T).prod (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict
    (labelInteraction N L r T)
  have hr : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦ fun i ↦ flag i (z.1,z.2 i)) :=
    Measurable.of_eval (fun i ↦ (hflag i).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
  have hf : Measurable (fun z : (BridgeEndpoints N L×(Fin N→Bridge.Noise))×GridAllocation N K q ↦
      (labelBridgePath N L T z.1,z.2)) :=
    ((labelBridgePath_measurable N L T).comp measurable_fst).prodMk measurable_snd
  have H := congrArg (fun μ ↦ μ.map (fun z : (BridgeEndpoints N L×(Fin N→Bridge.Noise))×GridAllocation N K q ↦
      (labelBridgePath N L T z.1,z.2)))
    (allocated_flag_joint (endpointWeightedBase ψ T) (Measure.pi fun _ : Fin N ↦ Bridge.law)
      (gridAllocationKernel hL q) (fun z ↦ fun i ↦ flag i (z.1,z.2 i)) hr
      (labelInteraction_measurable N L r T))
  have hκ : ∀ᵐz ∂base,
      (gridAllocationKernel hL q).comap (fun z ↦ (z.1,fun i ↦ flag i (z.1,z.2 i)))
        (measurable_fst.prodMk hr) z =
      (physicalAllocationKernel (K:=K) m q r R C S s₀ u).comap (labelBridgePath N L T)
        (labelBridgePath_measurable N L T) z := by
    simpa only [Kernel.comap_apply] using
      (ae_restrict_of_ae (s:=labelInteraction N L r T)
        (recorded_allocation_is_physical hL hK (endpointWeightedBase ψ T) m q r R C S s₀ T u))
  rw [Measure.compProd_congr hκ,map_retained_compProd base _ (labelBridgePath_measurable N L T),
    show base.map (labelBridgePath N L T)=groundPathLaw N L r T ψ from genuine_ground_label_bridge ψ r T] at H
  simp only [Measure.map_finset_sum' hf.aemeasurable,
    Measure.map_map hf measurable_prodMk_right,Function.comp_def] at H
  rw [←H]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  have he : flagEvent (eligibilityFlag (K:=K) m r R C S s₀ T u) b=
      {z | (fun i ↦ flag i (z.1,z.2 i))=b} := by
    ext z
    exact funext_iff.symm
  rw [he]
  rfl

theorem physicalBranchLaw_sum {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (ψ : Jet N L) (g : Fin G) (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    (∑b,∑a : GridAllocation N K (G*M),physicalBranchLaw hL (endpointWeightedBase ψ T) g b a m r R C S s₀ T u)=
      physicalDatumLaw g ψ m r R C S s₀ T u := by
  have hd := physicalDatum_measurable (N:=N) (K:=K) (M:=M) (L:=L) g m r R C S s₀ u
  have H := congrArg (fun μ ↦ μ.map (physicalDatum (K:=K) (M:=M) g m r R C S s₀ u))
    (genuine_ground_allocated_raw hL hK ψ m (G*M) r R C S s₀ T u)
  dsimp only [physicalDatumLaw]
  rw [←H]
  simp only [Measure.map_finset_sum' hd.aemeasurable]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [physicalBranchLaw_raw,Measure.map_map hd ((labelBridgePath_measurable N L T).prodMk measurable_const)]
  rfl

lemma physicalBranchLaw_le {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (ψ : Jet N L) (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    physicalBranchLaw hL (endpointWeightedBase ψ T) g b a m r R C S s₀ T u ≤
      physicalDatumLaw g ψ m r R C S s₀ T u := by
  rw [←physicalBranchLaw_sum hL hK]
  calc
    _ ≤ ∑a' : GridAllocation N K (G*M), physicalBranchLaw hL (endpointWeightedBase ψ T) g b a' m r R C S s₀ T u :=
      Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ a)
    _ ≤ _ := Finset.single_le_sum (f:=fun b' : Fin N→Bool ↦ ∑a' : GridAllocation N K (G*M),
      physicalBranchLaw hL (endpointWeightedBase ψ T) g b' a' m r R C S s₀ T u)
      (fun _ _ ↦ bot_le) (Finset.mem_univ b)

lemma physicalBranchLaw_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    {ψ : Jet N L} {r : ℝ} (hψ : IsGroundVector N L r ψ)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (R C S s₀ T : ℝ) (hT : 0≤T) (u : Time) :
    IsFiniteMeasure (physicalBranchLaw hL (endpointWeightedBase ψ T) g b a m r R C S s₀ T u) := by
  let := physicalDatumLaw_probability (K:=K) (M:=M) g hψ m R C S s₀ T hT u
  exact isFiniteMeasure_of_le _ (physicalBranchLaw_le hL hK ψ g b a m r R C S s₀ T u)

theorem physicalBranchLaw_normalized {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
      IsProbabilityMeasure (datumGroupReference hL g a m r R C S t u d) ∧
      ∀i : {i // i∈groupUnion g a},IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u i.val d) := by
  apply (ae_map_iff (physicalBranchDatum_measurable g b a (2*t)).aemeasurable
    ((measurable_probability_kernel _).inter ?_)).mpr
      (actual_branch_normalized hL hK h50 μ m r R C S s₀ t u g b a)
  change MeasurableSet {d : PhysicalDatum N K M G L | ∀i : {i // i∈groupUnion g a},
    IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u i.val d)}
  simp only [Set.ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ measurable_probability_kernel _

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupply
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalDatum_home {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (v : Fin 3 → Fin K) (i : Fin N) (hi : Eligible m r R C S s₀ u v i ω) :
    datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v :=
  (gridHome_eq_iff hL hK (ω 0 i) v).mpr hi.1.1

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PhysicalGeometry
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma supported_groupAt_eligible {N K M G : ℕ} {L : Length}
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (v : Fin 3→Fin K) (i : Fin N) (hi : i∈groupAt g a v) :
    Eligible m r R C S s₀ u v i ω := by
  cases he : a v with
  | none => simp [groupAt,he] at hi
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hi
    obtain ⟨k,rfl⟩ := hi
    exact (Finset.mem_filter.mp (allocationPMF_support _ _ _ (ha v) f he _)).2

lemma groupAt_card_le {N K M G : ℕ} (g : Fin G) (a : GridAllocation N K (G*M)) (v : Fin 3→Fin K) :
    (groupAt g a v).card≤M := by
  cases he : a v with
  | none => simp [groupAt,he]
  | some f => simpa only [groupAt,he,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le (s:=Finset.univ) (f:=fun k : Fin M ↦ f (groupPosition M G g k)))

theorem physicalDatum_group_multiplicity {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (g : Fin G) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (v : Fin 3→Fin K) :
    (Finset.univ.filter (fun i : {i // i∈groupUnion g a} ↦
      datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v)).card≤M := by
  let s := Finset.univ.filter (fun i : {i // i∈groupUnion g a} ↦
      datumHome hL (physicalDatum g m r R C S s₀ u (ω,a)) i=v)
  have hs : s.image Subtype.val⊆groupAt g a v := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨w,_,hjw⟩ := Finset.mem_biUnion.mp j.property
    have he := supported_groupAt_eligible g m r R C S s₀ u ω a ha w j hjw
    have hh := physicalDatum_home hL hK g m r R C S s₀ u ω a w j he
    have hv := (Finset.mem_filter.mp hj).2
    have hw : w=v := hh.symm.trans hv
    simpa only [hw] using hjw
  have hc := (Finset.card_le_card hs).trans (groupAt_card_le g a v)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLabelLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

instance physicalLabels_markov {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N) :
    IsMarkovKernel (physicalLabels (M:=M) hL g m t r R C S u particle) := by
  constructor
  intro d
  rw [physicalLabels,finiteKernelPi_apply]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

lemma physicalBranchLaw_ae {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time)
    (P : PhysicalDatum N K M G L→Prop) (hPm : MeasurableSet {d | P d})
    (hP : ∀ω : ConfigurationPath N L,
      (∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support) →
      P (physicalDatum g m r R C S s₀ u (ω,a))) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u,P d := by
  rw [physicalBranchLaw_raw]
  have hm : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      physicalDatum g m r R C S s₀ u (labelBridgePath N L T z,a)) :=
    (physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L T).prodMk measurable_const)
  apply (ae_map_iff hm.aemeasurable hPm).mpr
  have hB := (labelInteraction_measurable N L r T).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable (K:=K) m r R C S s₀ T u i) b)
  have hs := allocationBase_ae_support μ (gridAllocationKernel hL (G*M)) b a
    (fun e a' ↦ ∀v,a' v∈(allocationPMF (recordedList hL v (e,b)) (G*M)).support)
    (fun e ↦ gridAllocation_support_ae hL (G*M) (e,b))
  filter_upwards [ae_restrict_of_ae (Measure.quasiMeasurePreserving_fst.ae hs),
    ae_restrict_of_ae (label_endpoints_ae T (allocationBase μ (gridAllocationKernel hL (G*M)) b a)),
    ae_restrict_mem hB] with z hz hz01 hzB
  apply hP _
  intro v
  have hb : (fun i ↦ eligibilityFlag (K:=K) m r R C S s₀ T u i (z.1,z.2 i))=b := funext hzB.2
  have he := recordedList_eq hL hK m r R C S s₀ T u v z.1 z.2 hz01.1 hz01.2
  rw [hb] at he
  simpa only [←he] using hz v

lemma physicalBranchLaw_allocation {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u,d.2.2.2.1=a := by
  apply (ae_map_iff (physicalBranchDatum_measurable g b a T).aemeasurable
    (measurableSet_eq_fun measurable_snd.snd.snd.fst measurable_const)).mpr
  exact ae_of_all _ fun _ ↦ rfl

lemma physicalBranchLaw_multiplicity {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ T : ℝ) (u : Time) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ T u, ∀v,
      (Finset.univ.filter (fun i : {i // i∈groupUnion g a} ↦ datumHome hL d i=v)).card≤M := by
  apply physicalBranchLaw_ae hL hK μ g b a m r R C S s₀ T u _ ?_
    (fun ω hω v ↦ physicalDatum_group_multiplicity hL hK g m r R C S s₀ u ω a hω v)
  have hf : Measurable (fun d : PhysicalDatum N K M G L ↦ fun i : {i // i∈groupUnion g a} ↦ datumHome hL d i.val) :=
    Measurable.of_eval (fun i ↦ datumHome_measurable hL i.val)
  exact hf ((Set.to_countable {f : {i // i∈groupUnion g a}→(Fin 3→Fin K) |
      ∀v,(Finset.univ.filter (fun i ↦ f i=v)).card≤M}).measurableSet)

lemma branchAccessible_card {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : HardSphere.Lattice.DiscreteTorus K) (d : PhysicalDatum N K M G L) (hd : d.2.2.2.1=a) :
    (branchAccessible hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d).card=
      (datumAccessibleLabels hL g m t r R C S u (siteIndex v) d).card := by
  let s := branchAccessible hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d
  have he : s.image Subtype.val=datumAccessibleLabels hL g m t r R C S u (siteIndex v) d := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact (Finset.mem_filter.mp hj).2
    · intro hi
      have hsel : i∈groupUnion g a := by
        have h := (Finset.mem_filter.mp hi).1
        simpa only [datumSelected,hd] using h
      exact Finset.mem_image.mpr ⟨⟨i,hsel⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,rfl⟩
  rw [←he,Finset.card_image_of_injective _ Subtype.val_injective]

lemma branchAccessible_supply {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : HardSphere.Lattice.DiscreteTorus K) (d : PhysicalDatum N K M G L) (hd : d.2.2.2.1=a)
    (hv : siteIndex v∉datumBad hL g m t r R C S u d) :
    (M:ℝ)≤2*((branchAccessible hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d).card:ℝ) := by
  rw [branchAccessible_card hL g a m t r R C S u v d hd]
  have hh : M≤2*(datumAccessibleLabels hL g m t r R C S u (siteIndex v) d).card := by
    simpa only [datumBad,Finset.mem_filter,Finset.mem_univ,true_and,not_lt] using hv
  exact_mod_cast hh

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SharedRoute
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge
attribute [local instance] Classical.propDecidable

variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma ambientFirst_measurable (s : Finset I) (σ : Equiv.Perm I) :
    Measurable (ambientFirst (X:=X) s σ) :=
  measurable_updateFinset'.comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp measurable_snd))))

omit [Fintype I] in
lemma ambientSecond_measurable (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i) :
    Measurable (ambientSecond (X:=X) s σ hf) :=
  measurable_updateFinset'.comp (measurable_fst.prodMk
    (Measurable.of_eval (fun i ↦ measurable_fst.comp ((measurable_pi_apply i).comp
      ((reverseSelected σ s hf).measurable.comp measurable_snd)))))

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPrimary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma conditioned_prod_univ (μ : Measure X) [SFinite μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (A : Set X) :
    conditionedMeasure (μ.prod ν) (Prod.fst ⁻¹' A)=(conditionedMeasure μ A).prod ν := by
  have he : Prod.fst ⁻¹' A=A ×ˢ (univ : Set Y) := by ext p; simp
  rw [he,conditionedMeasure,conditionedMeasure,Measure.prod_smul_left,
    Measure.prod_prod,measure_univ,mul_one,←Measure.prod_restrict,Measure.restrict_univ]

lemma conditioned_option {J : Type*} [Fintype J]
    (μ : Option J→Measure X) [∀i,IsFiniteMeasure (μ i)] [IsProbabilityMeasure (μ none)]
    (A : Set (J→X)) (hA : MeasurableSet A) :
    conditionedMeasure (Measure.pi μ) ((fun x : Option J→X ↦ fun i ↦ x (some i)) ⁻¹' A)=
    ((conditionedMeasure (Measure.pi fun i ↦ μ (some i)) A).prod (μ none)).map
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option J ↦ X)).symm := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option J ↦ X)
  have hB : MeasurableSet ((fun x : Option J→X ↦ fun i ↦ x (some i)) ⁻¹' A) :=
    hA.preimage (Measurable.of_eval fun i ↦ measurable_pi_apply (some i))
  rw [←Measure.pi_map_piOptionEquivProd μ,
    ←conditioned_map_preimage _ e.symm e.symm.measurable hB]
  change (conditionedMeasure _ (Prod.fst ⁻¹' A)).map e.symm = _
  rw [conditioned_prod_univ]

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma physicalSlotMutual_measurable {L : Length} (r : ℝ) :
    MeasurableSet (physicalSlotMutual (J:=J) (L:=L) r) :=
  (physicalMutual_measurable r).preimage
    (Measurable.of_eval fun i ↦ measurable_pi_apply (some i))

omit [DecidableEq J] in
lemma physicalPrimaryReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    physicalPrimaryReference hL g m t r R C S u particle v d=
      conditionedMeasure (Measure.pi fun i ↦ physicalSlotReference hL g m t r R C S u particle v i d)
        (physicalSlotMutual (L:=L) r) := by
  unfold physicalPrimaryReference
  change (fiberRestrict _ _ d univ)⁻¹ • fiberRestrict _ _ d=_
  rw [fiberRestrict_apply _ ((physicalSlotMutual_measurable r).preimage measurable_snd)]
  simp only [Measure.restrict_apply_univ,finiteKernelPi_apply]
  rfl

theorem physicalPrimaryReference_actual {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    physicalPrimaryReference hL g m t r R C S u (fun i : {i // i∈groupUnion g a} ↦ i.val) v d=
      ((datumGroupReference hL g a m r R C S t u d).prod (cellPathReference v)).map
        (MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm := by
  have : IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) v none d) :=
    inferInstanceAs (IsProbabilityMeasure (cellPathReference v))
  rw [physicalPrimaryReference_apply,physicalSlotMutual,conditioned_option _ _ (physicalMutual_measurable r),
    datumGroupReference_apply]
  simp only [physicalSlotReference,Kernel.const_apply,datumIndividualReference_apply]

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RouteMatches
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Classical
namespace HardSphere.Comparison
open _root_.OAI.HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*} [DecidableEq J]

lemma departureSites_subset (p : SimplePath x y) : departureSites p⊆p.val.support.toFinset := by
  intro v hv
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
  exact List.mem_toFinset.mpr (p.val.getVert_mem_support i.castSucc.val)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchEstimates
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

lemma physicalBranchLaw_primary {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) (v : Fin 3→Fin K) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
      IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u (branchParticles g a) v d) := by
  filter_upwards [physicalBranchLaw_normalized hL hK h50 μ m r R C S s₀ t u g b a] with d hd
  change IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u
    (fun i : {i // i∈groupUnion g a} ↦ i.val) v d)
  rw [physicalPrimaryReference_actual]
  have := hd.1
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma mem_latticeDatumBad {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (d : PhysicalDatum N K M G L)
    (v : DiscreteTorus K) : v∈latticeDatumBad hL g m t r R C S u d ↔
      siteIndex v∈datumBad hL g m t r R C S u d := by
  change v∈Finset.image _ _ ↔ _
  constructor
  · rintro hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    simpa only [siteIndex_indexSite] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨siteIndex v,hv,indexSite_siteIndex v⟩

lemma physicalBranchLaw_path_supply {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) {x y : DiscreteTorus K}
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1) :
    ∀ᵐd ∂(physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).restrict E,
      ∀ᵐp ∂ν d,∀v∈departureSites p,
        (M:ℝ)≤2*((branchAccessible hL g m t r R C S u (branchParticles g a) v d).card:ℝ) := by
  filter_upwards [ae_restrict_of_ae (physicalBranchLaw_allocation hL μ g b a m r R C S s₀ (2*t) u),
    ae_restrict_mem hE] with d hd hdE
  have hp : ∀ᵐp ∂ν d,simplePathGood (latticeDatumBad hL g m t r R C S u d) p :=
    (mem_ae_iff_prob_eq_one (Set.to_countable _).measurableSet).mpr (hgood d hdE)
  filter_upwards [hp] with p hp
  intro v hv
  apply branchAccessible_supply hL g a m t r R C S u v d hd
  intro hvb
  exact hp v (List.mem_toFinset.mp (departureSites_subset p hv))
    ((mem_latticeDatumBad hL g m t r R C S u d v).mpr hvb)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPairedRoute
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Comparison
variable {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
lemma fiberNormalize_mass_le_one (κ : Kernel E X) [IsSFiniteKernel κ]
    (A : Set (E×X)) (e : E) : fiberNormalize κ A e univ≤1 := by
  change ((fiberRestrict κ A e univ)⁻¹ • fiberRestrict κ A e) univ≤1
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.inv_mul_le_one _

variable {I : Type*} [Fintype I] [DecidableEq I]
  {V : I→Type*} [∀i,MeasurableSpace (V i)]
omit [Fintype I] in
lemma ambientSharedKernel_mass_le (s : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉s→σ i=i) (ξ : Kernel E (∀i,V i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (V i×V (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,V i))) (e : E) :
    ambientSharedKernel s σ hσ ξ ρ A e univ≤ξ e univ := by
  rw [ambientSharedKernel,Kernel.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  calc
    _ ≤ ∫⁻_x,1 ∂ξ e := lintegral_mono fun _ ↦ fiberNormalize_mass_le_one _ _ _
    _ = _ := by simp
end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma physicalPairedRoute_total {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :
    physicalPairedRoute hL g m t r R C S u particle labels v steps d univ=
      physicalSharedRoute hL g m t r R C S u particle labels v steps d univ := by
  rw [physicalPairedRoute,Kernel.map_apply _ ((ambientFirst_measurable _ _).prodMk (ambientSecond_measurable _ _ _)),
    Measure.map_apply ((ambientFirst_measurable _ _).prodMk (ambientSecond_measurable _ _ _)) MeasurableSet.univ]
  rfl

lemma physicalPairedRoute_mass_le_one {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L) :
    physicalPairedRoute hL g m t r R C S u particle labels v steps d univ≤1 := by
  rw [physicalPairedRoute_total]
  exact (ambientSharedKernel_mass_le _ _ _ _ _ _ _).trans (fiberNormalize_mass_le_one _ _ _)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_RouteFields
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma physicalCodedRoute_mass_le_one {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (c : PhysicalRouteCode x y J) (d : PhysicalDatum N K M G L) :
    physicalCodedRoute hL g m t r R C S u particle hxy c d univ≤1 := by
  unfold physicalCodedRoute
  split
  · exact physicalPairedRoute_mass_le_one ..
  · change (0 : ℝ≥0∞)≤1
    exact bot_le
instance physicalCodedRoute_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (c : PhysicalRouteCode x y J) :
    IsFiniteKernel (physicalCodedRoute (M:=M) hL g m t r R C S u particle hxy c) :=
  ⟨1,by simp,physicalCodedRoute_mass_le_one hL g m t r R C S u particle hxy c⟩

instance physicalRouteFamily_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) : IsFiniteKernel (physicalRouteFamily (M:=M) hL g m t r R C S u particle hxy) :=
  ⟨1,by simp,fun z ↦ physicalCodedRoute_mass_le_one hL g m t r R C S u particle hxy z.2 z.1⟩

instance physicalMixedRoutes_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν] :
    IsFiniteKernel (physicalMixedRoutes hL g m t r R C S u particle hxy ν) := by
  unfold physicalMixedRoutes; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalFamilyLikelihood
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalRouteView_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :
    IsFiniteKernel (physicalRouteView (M:=M) hL g m t r R C S u particle hxy b) := by
  unfold physicalRouteView; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_UniformBath
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {E : Type*} [MeasurableSpace E]

attribute [local instance] OAI.HardSphere.Comparison.permBathSpace
attribute [local instance] OAI.HardSphere.Comparison.permBathSingleton
lemma orderedPrimaryObservation_measurable (b : Bool) (i : Fin (n+1)) :
    Measurable (orderedPrimaryObservation (E:=E) b i) := by
  apply measurable_from_prod_countable_left
  intro τ
  cases b <;> dsimp [orderedPrimaryObservation] <;> fun_prop

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalObservedLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalCodedRoute_finite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalMixedRoutes_finite _root_.OAI.HardSphere.Groups.physicalRouteFamily_finite _root_.OAI.HardSphere.Groups.physicalRouteView_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

instance primaryBathKernel_markov (b : Bool) (i : Fin (n+1)) :
    IsMarkovKernel (primaryBathKernel (E:=E) b i) :=
  Kernel.IsMarkovKernel.map _ (orderedPrimaryObservation_measurable b i)

end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalBathKernel_markov {N K M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (b : Bool) (i : J) : IsMarkovKernel (physicalBathKernel (K:=K) (M:=M) (G:=G) (L:=L) particle b i) := by
  unfold physicalBathKernel; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalMixedObservation
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

instance taggedPhysicalBathKernel_markov {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :
    IsMarkovKernel (taggedPhysicalBathKernel (K:=K) (M:=M) (G:=G) (L:=L) particle b) :=
  ⟨fun z ↦ inferInstanceAs (IsProbabilityMeasure (primaryBathKernel b z.1 (physicalFullMidpoint particle z.2)))⟩

instance physicalCodeObserver_markov {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool) :
    IsMarkovKernel (physicalCodeObserver (M:=M) (G:=G) (L:=L) particle hxy b) := by
  unfold physicalCodeObserver; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalObservedMixture
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalObservedMixture_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (b : Bool) : IsFiniteKernel (physicalObservedMixture hL g m t r R C S u particle hxy ν b) := by
  unfold physicalObservedMixture; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_MixtureMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma observed_second_moment (P ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (hac : ν≪P) (f : X→Y) (hf : Measurable f)
    (hi : Integrable (fun x ↦ (ν.rnDeriv P x).toReal^2) P) :
    Integrable (fun y ↦ ((ν.map f).rnDeriv (P.map f) y).toReal^2) (P.map f) ∧
    (∫y,((ν.map f).rnDeriv (P.map f) y).toReal^2 ∂P.map f)≤
      ∫x,(ν.rnDeriv P x).toReal^2 ∂P := by
  let g : X→ℝ := fun x ↦ (ν.rnDeriv P x).toReal
  let h : Y→ℝ := fun y ↦ ((ν.map f).rnDeriv (P.map f) y).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hh : Measurable h := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have he : h∘f=ᵐ[P] P[g|MeasurableSpace.comap f inferInstance] := toReal_rnDeriv_map hac hf
  have hl2 : MemLp g 2 P := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hi
  have hc : MemLp (P[g|MeasurableSpace.comap f inferInstance]) 2 P := hl2.condExp (by norm_num)
  have hci : Integrable (fun x ↦ (P[g|MeasurableSpace.comap f inferInstance] x)^2) P :=
    (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mp hc
  have hcomp : Integrable (fun x ↦ h (f x)^2) P := hci.congr (he.symm.fun_comp (fun x : ℝ ↦ x^2))
  constructor
  · exact (integrable_map_measure (hh.pow_const 2).aestronglyMeasurable hf.aemeasurable).mpr hcomp
  · change (∫y,h y^2 ∂P.map f)≤_
    rw [integral_map hf.aemeasurable (hh.pow_const 2).aestronglyMeasurable]
    calc
      _ = ∫x,(P[g|MeasurableSpace.comap f inferInstance] x)^2 ∂P :=
        integral_congr_ae (he.fun_comp (fun x : ℝ ↦ x^2))
      _ ≤ ∫x,g x^2 ∂P := by
        have hni : Integrable (fun x ↦ ‖g x‖^(2:ℝ)) P := by
          simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hi
        have hineq := integral_norm_condExp_rpow_le (m:=MeasurableSpace.comap f inferInstance)
          (by norm_num : (1:ℝ)≤2) hni
        simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hineq

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_TaggedMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X]

lemma taggedFunction_measurable (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    Measurable (fun p : I×X ↦ f p.1 p.2) :=
  measurable_from_prod_countable_right hf

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTaggedObservation
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

instance retainedTaggedPhysicalBath_markov {N M G : ℕ} {L : Length} (particle : J↪Fin (N+1)) (b : Bool) :
    IsMarkovKernel (retainedTaggedPhysicalBath (K:=K) (M:=M) (G:=G) (L:=L) particle b) := by
  unfold retainedTaggedPhysicalBath; infer_instance
instance physicalTaggedMixture_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) :
    IsFiniteMeasure (physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E) := by
  unfold physicalTaggedMixture; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalScaleData
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalBathKernel_markov _root_.OAI.HardSphere.Groups.physicalCodeObserver_markov _root_.OAI.HardSphere.Groups.physicalCodedRoute_finite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalMixedRoutes_finite _root_.OAI.HardSphere.Groups.physicalObservedMixture_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalRouteFamily_finite _root_.OAI.HardSphere.Groups.physicalRouteView_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedMixture_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.retainedTaggedPhysicalBath_markov _root_.OAI.HardSphere.Groups.taggedPhysicalBathKernel_markov _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable

variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem physical_branch_moment_data {N M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (h50 : 50 < L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (flags : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (t r R C S s₀ h : ℝ) (u : Time) (hs : PhysicalScaleBounds m t r R C S s₀ h u)
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1) :
    ∀ᵐd ∂(physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).restrict E,
      PhysicalMomentData hL g m t r R C S u (branchParticles g a) ν (datumCollisionBound t r h R C) d := by
  filter_upwards [physicalBranchLaw_path_supply hL μ g flags a m r R C S s₀ t u E hE ν hgood,
    ae_restrict_of_ae (physicalBranchLaw_multiplicity hL hK μ g flags a m r R C S s₀ (2*t) u),
    ae_restrict_of_ae (physicalBranchLaw_normalized hL hK h50 μ m r R C S s₀ t u g flags a),
    ae_restrict_of_ae (physicalBranchLaw_collision hL hK h50 hs.mesh_pos μ g flags a t r R C S s₀ h u
      hs.time_pos hs.radius_pos hs.radius_le hs.R_nonneg hs.C_nonneg hs.window_pos hs.prefix_eq
      hs.small hs.separation hs.mesh_radius hs.mesh_scale hs.window hs.large hs.drift)] with d h₁ h₂ h₃ h₄
  exact ⟨h₁,h₂,h₃.2,h₄⟩

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalObservedMass
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

instance physicalCommonObserved_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ] (E : Set (PhysicalDatum (N+1) K M G L)) :
    IsFiniteMeasure (physicalCommonObserved hL g m t r R C S u particle hxy ν μ E) := by
  unfold physicalCommonObserved; infer_instance

instance physicalObservedReference_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (b : Bool) (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ) := by
  unfold physicalObservedReference; infer_instance

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_SumMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I X : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace X]

omit [MeasurableSingletonClass I] in
lemma retainedFiniteSum_snd (P : I→Measure X) :
    (retainedFiniteSum P).map Prod.snd=∑i,P i := by
  simp only [retainedFiniteSum,Measure.map_finset_sum' measurable_snd.aemeasurable,
    Measure.map_map measurable_snd measurable_prodMk_left,Function.comp_def,Measure.map_id']

lemma retainedFiniteSum_density (P ν : I→Measure X) [∀i,IsFiniteMeasure (P i)]
    [∀i,IsFiniteMeasure (ν i)] (ha : ∀i,ν i≪P i) :
    retainedFiniteSum ν=(retainedFiniteSum P).withDensity (fun z ↦ (ν z.1).rnDeriv (P z.1) z.2) := by
  let F : I×X→ℝ≥0∞ := fun z ↦ (ν z.1).rnDeriv (P z.1) z.2
  have hF : Measurable F := taggedFunction_measurable _ (fun i ↦ Measure.measurable_rnDeriv _ _)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ hF hf]
  simp only [retainedFiniteSum,lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_map hf measurable_prodMk_left,lintegral_map (hF.mul hf) measurable_prodMk_left]
  have he := Measure.withDensity_rnDeriv_eq (ν i) (P i) (ha i)
  rw [←he]
  exact lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _)
    (show Measurable (fun x ↦ f (i,x)) from hf.comp measurable_prodMk_left)

theorem finite_sum_second_moment (P ν : I→Measure X) [∀i,IsFiniteMeasure (P i)]
    [∀i,IsFiniteMeasure (ν i)] (ha : ∀i,ν i≪P i)
    (hi : ∀i,Integrable (fun x ↦ ((ν i).rnDeriv (P i) x).toReal^2) (P i)) :
    Integrable (fun x ↦ ((∑i,ν i).rnDeriv (∑i,P i) x).toReal^2) (∑i,P i) ∧
    (∫x,((∑i,ν i).rnDeriv (∑i,P i) x).toReal^2 ∂(∑i,P i))≤
      ∑i,∫x,((ν i).rnDeriv (P i) x).toReal^2 ∂P i := by
  let F : I×X→ℝ≥0∞ := fun z ↦ (ν z.1).rnDeriv (P z.1) z.2
  have hF : Measurable F := taggedFunction_measurable _ (fun i ↦ Measure.measurable_rnDeriv _ _)
  have hfs := hF.ennreal_toReal.pow_const 2
  have hiF : ∀i,Integrable (fun z ↦ (F z).toReal^2) ((P i).map (Prod.mk i)) := by
    intro i
    exact (integrable_map_measure hfs.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr (hi i)
  have hiR : Integrable (fun z ↦ (F z).toReal^2) (retainedFiniteSum P) :=
    integrable_finsetSum_measure.mpr (fun i _ ↦ hiF i)
  have hd := retainedFiniteSum_density P ν ha
  have he : (fun z ↦ ((retainedFiniteSum ν).rnDeriv (retainedFiniteSum P) z).toReal^2)=ᵐ[retainedFiniteSum P]
      (fun z ↦ (F z).toReal^2) := by
    rw [hd]
    exact (Measure.rnDeriv_withDensity _ hF).fun_comp (fun a : ℝ≥0∞ ↦ a.toReal^2)
  have hac : retainedFiniteSum ν≪retainedFiniteSum P := by
    rw [hd]; exact withDensity_absolutelyContinuous _ _
  have H := observed_second_moment (retainedFiniteSum P) (retainedFiniteSum ν) hac
    Prod.snd measurable_snd (hiR.congr he.symm)
  simp only [retainedFiniteSum_snd] at H
  refine ⟨H.1,H.2.trans_eq ?_⟩
  rw [integral_congr_ae he,retainedFiniteSum,integral_finsetSum_measure (fun i _ ↦ hiF i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_map measurable_prodMk_left.aemeasurable hfs.aestronglyMeasurable

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalGroupComparison
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}

theorem physical_group_common_comparison_oai {N M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} {r : ℝ} (hψ : IsGroundVector (N+1) L r ψ)
    (g : Fin G) (m : ℕ) (t R C S s₀ h : ℝ) (u : Time) (hs : PhysicalScaleBounds m t r R C S s₀ h u)
    (hxy : x≠y) (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hgood : ∀d∈E,ν d {p | simplePathGood (latticeDatumBad hL g m t r R C S u d) p}=1)
    (hM : 0<M) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1 ≤ B) (hCpath : 0 ≤ Cpath)
    (hBt : routeDensityBound t ≤ ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ ≤ κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*datumCollisionBound t r h R C) ≤ 1)
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d
      ∂physicalDatumLaw g ψ m r R C S s₀ (2*t) u) ≤ ENNReal.ofReal Cpath) :
    ∃σ : Measure (Torus L×Torus L×Configuration N L), IsFiniteMeasure σ ∧
      σ univ=(physicalDatumLaw g ψ m r R C S s₀ (2*t) u) E ∧
      ∀b,
        let P := physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b
        IsFiniteMeasure P ∧ σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
          (∫z,(σ.rnDeriv P z).toReal^2 ∂P) ≤ B*Cpath := by
  classical
  let I := (Fin (N+1)→Bool)×GridAllocation (N+1) K (G*M)
  let μ : I→Measure (PhysicalDatum (N+1) K M G L) := fun i ↦
    physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g i.1 i.2 m r R C S s₀ (2*t) u
  have hT : 0 ≤ 2*t := by linarith [hs.time_pos]
  let (i : I) : IsFiniteMeasure (μ i) :=
    physicalBranchLaw_finite hL hK hψ g i.1 i.2 m R C S s₀ (2*t) hT u
  let σ : I→Measure (Torus L×Torus L×Configuration N L) := fun i ↦
    physicalCommonObserved hL g m t r R C S u (branchParticles g i.2) hxy ν (μ i) E
  let P : Bool→I→Measure (Torus L×Torus L×Configuration N L) := fun b i ↦
    physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u (branchParticles g i.2) b (μ i)
  have hsum : (∑i,μ i)=physicalDatumLaw g ψ m r R C S s₀ (2*t) u := by
    rw [Fintype.sum_prod_type]
    exact physicalBranchLaw_sum hL hK ψ g m r R C S s₀ (2*t) u
  let F := E.indicator (fun d ↦ ∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d)
  let e : I→ℝ≥0∞ := fun i ↦ ∫⁻d,F d ∂μ i
  have hesum : ∑i,e i ≤ ENNReal.ofReal Cpath := by
    rw [←lintegral_finsetSum_measure,hsum]
    simpa only [F,lintegral_indicator hE] using henc
  have hei (i : I) : e i≠⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    exact (Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i)).trans hesum
  have hbranch (i : I) :
      σ i univ=μ i E ∧ ∀b,(σ i≪P b i ∧
        Integrable (fun z ↦ ((σ i).rnDeriv (P b i) z).toReal^2) (P b i) ∧
        (∫z,((σ i).rnDeriv (P b i) z).toReal^2 ∂P b i) ≤ B*(e i).toReal) := by
    apply physical_common_observed_estimates hL g m t r R C S hs.time_pos hs.radius_le u
      (branchParticles g i.2) hxy ν (μ i) E hE hM (datumCollisionBound t r h R C)
      δ B κ (e i).toReal hδ hB ENNReal.toReal_nonneg hBt hκ hsmall
    · exact physical_branch_moment_data hL hK h50 (endpointWeightedBase ψ (2*t)) g i.1 i.2
        m t r R C S s₀ h u hs E hE ν hgood
    · exact ae_restrict_of_ae (physicalBranchLaw_primary hL hK h50 (endpointWeightedBase ψ (2*t))
        m r R C S s₀ t u g i.1 i.2 (siteIndex y))
    · rw [ENNReal.ofReal_toReal (hei i)]
      exact le_of_eq (lintegral_indicator hE _).symm
  let (i : I) : IsFiniteMeasure (σ i) := by dsimp only [σ]; infer_instance
  let (b : Bool) (i : I) : IsFiniteMeasure (P b i) := by dsimp only [P]; infer_instance
  refine ⟨∑i,σ i,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_⟩
  · rw [Measure.finsetSum_apply]
    simp_rw [fun i ↦ (hbranch i).1]
    rw [←Measure.finsetSum_apply,hsum]
  · intro b
    have hp : physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b=∑i,P b i := by
      rw [Fintype.sum_prod_type]; rfl
    dsimp only
    rw [hp]
    refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)),?_,?_⟩
    · have H : Measure.sum σ≪∑i,P b i := Measure.absolutelyContinuous_sum_left (fun i ↦
        ((hbranch i).2 b).1.trans (Measure.absolutelyContinuous_of_le
          (Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ i))))
      simpa only [Measure.sum_fintype] using H
    · have H := finite_sum_second_moment (P b) σ (fun i ↦ ((hbranch i).2 b).1)
        (fun i ↦ ((hbranch i).2 b).2.1)
      refine ⟨H.1,H.2.trans ?_⟩
      calc
        _ ≤ ∑i,B*(e i).toReal := Finset.sum_le_sum (fun i _ ↦ ((hbranch i).2 b).2.2)
        _ = B*(∑i,e i).toReal := by rw [←Finset.mul_sum,ENNReal.toReal_sum (fun i _ ↦ hei i)]
        _ ≤ B*Cpath := mul_le_mul_of_nonneg_left
          (by simpa only [ENNReal.toReal_ofReal hCpath] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hesum)
          (by linarith)

end HardSphere.Groups
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.Groups.physical_group_common_comparison_oai := @OAI.HardSphere.Groups.physical_group_common_comparison_oai
