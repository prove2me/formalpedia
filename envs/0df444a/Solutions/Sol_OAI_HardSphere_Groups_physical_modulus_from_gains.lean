-- Prove2me | solution 1 for OAI.HardSphere.Groups.physical_modulus_from_gains
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:21:19.221966+00:00
-- url     : https://prove2.me/submissions/4c7ca4ee-90bd-4da2-8bea-239cdb3cd06a

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_marginal
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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_NormSqIntegral
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
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
namespace IndicatorStrong
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, L2.inner_def, ← integral_re]
  · congr 1
    ext x
    simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]
  · exact L2.integrable_inner f f

end IndicatorStrong

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
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.Sampling.siteAllocationKernel_markov _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local irreducible] torusDistance

lemma eligibleList_disjoint {N K : ℕ} {L : Length} (hL : L.val=(K:ℝ)) (hK : 1≤K)
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (ω : ConfigurationPath N L)
    {v w : Fin 3→Fin K} (hvw : v≠w) :
    Disjoint (eligibleList m r R C S s₀ u v ω) (eligibleList m r R C S s₀ u w ω) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (centeredCell_disjoint hL hK hvw)
    (Finset.mem_filter.mp hi).2.1.1 (Finset.mem_filter.mp hj).2.1.1

end HardSphere.Groups

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

lemma groupPosition_disjoint (M G : ℕ) (g h : Fin G) (hgh : g≠h) (k l : Fin M) :
    groupPosition M G g k≠groupPosition M G h l := by
  intro he
  have he' := congrArg Fin.val he
  change g.val*M+k.val=h.val*M+l.val at he'
  wlog hlt : g.val<h.val generalizing g h k l
  · have hne : g.val≠h.val := fun h ↦ hgh (Fin.ext h)
    exact this h g hgh.symm l k he.symm he'.symm (by omega)
  have hh : (g.val+1)*M≤h.val*M := Nat.mul_le_mul_right M hlt
  have hk := k.isLt
  have : g.val*M+k.val<h.val*M+l.val := by
    calc
      g.val*M+k.val < g.val*M+M := Nat.add_lt_add_left hk _
      _ = (g.val+1)*M := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ h.val*M := hh
      _ ≤ h.val*M+l.val := Nat.le_add_right _ _
  omega

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothSiteWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
open MeasureTheory Set Filter ProbabilityTheory

lemma groundPositionLaw_probability {n : ℕ} {L : Length} (u : Jet n L) (hu : ‖u.1‖=1) :
    IsProbabilityMeasure (groundPositionLaw n L u) := by
  constructor
  rw [groundPositionLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ←ofReal_integral_eq_lintegral_ofReal
      ((Lp.memLp u.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0))
      (Eventually.of_forall (fun X ↦ sq_nonneg ‖u.1 X‖)),←IndicatorStrong.norm_sq_integral,hu]
  norm_num

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathPermutation
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma measurePreserving_weighted_ae_invariant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {R : α → α} (hR : MeasurePreserving R μ μ)
    (w : α → ℝ≥0∞) (hw : Measurable w) (hi : (fun x ↦ w (R x)) =ᵐ[μ] w) :
    MeasurePreserving R (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hR.measurable,Measure.ext fun S hS ↦ ?_⟩
  rw [Measure.map_apply hR.measurable hS,withDensity_apply _ (hS.preimage hR.measurable),
    withDensity_apply _ hS,←lintegral_indicator (hS.preimage hR.measurable),←lintegral_indicator hS]
  calc
    _ = ∫⁻ x, (S.indicator w) (R x) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hi] with x hx
      by_cases h : R x∈S
      · simp only [Set.indicator_of_mem h,Set.indicator_of_mem (show x∈R ⁻¹' S from h),hx]
      · simp only [Set.indicator_of_notMem h,Set.indicator_of_notMem (show x∉R ⁻¹' S from h)]
    _ = _ := hR.lintegral_comp (hw.indicator hS)

lemma groundPositionLaw_permute {n : ℕ} {L : Length} (u : Jet n L) (hb : bosonic u.1)
    (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (permuteConfiguration σ) (groundPositionLaw n L u) (groundPositionLaw n L u) := by
  apply measurePreserving_weighted_ae_invariant (measurePreserving_permute σ) _
    ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
  filter_upwards [hb σ] with X hX
  change ENNReal.ofReal (‖u.1 (fun i ↦ X (σ i))‖^2)=ENNReal.ofReal (‖u.1 X‖^2)
  rw [hX]

end HardSphere

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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_IntegratedFiber
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
variable {W A B : Type*} [MeasurableSpace W] [MeasurableSpace A] [MeasurableSpace B]

lemma map_density_comp (μ : Measure A) (f : A→B) (hf : Measurable f)
    (L : B→ℝ≥0∞) (hL : Measurable L) :
    (μ.withDensity (L∘f)).map f=(μ.map f).withDensity L := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf]
  change (∫⁻a,(F∘f) a ∂μ.withDensity (L∘f))=_
  rw [lintegral_withDensity_eq_lintegral_mul _ (hL.comp hf) (hF.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ hL hF,lintegral_map (hL.mul hF) hf]
  rfl

end HardSphere.Comparison

end
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
namespace HardSphere.Comparison

lemma coarse_joint_reference {W D X Y : Type*} [MeasurableSpace W]
    [MeasurableSpace D] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure W) [SFinite μ] (κ : Kernel W X) [IsSFiniteKernel κ]
    (R : Kernel D Y) [IsSFiniteKernel R] (d : W→D) (hd : Measurable d)
    (f : W×X→Y) (hf : Measurable f)
    (h : ∀ᵐw ∂μ,(κ w).map (fun x ↦ f (w,x))=R (d w)) :
    (μ.compProd κ).map (fun p ↦ (d p.1,f p))=(μ.map d).compProd R := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hm : Measurable (fun p : W×X ↦ (d p.1,f p)) :=
    (hd.comp measurable_fst).prodMk hf
  rw [lintegral_map hF hm]
  have hFm : Measurable (fun p : W×X ↦ F (d p.1,f p)) := hF.comp hm
  rw [Measure.lintegral_compProd hFm,Measure.lintegral_compProd hF,
    lintegral_map (hF.lintegral_kernel_prod_right' (κ:=R)) hd]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  rw [←hw]
  exact (lintegral_map (μ:=κ w)
    (show Measurable (fun y ↦ F (d w,y)) from hF.comp measurable_prodMk_left)
    (show Measurable (fun x ↦ f (w,x)) from hf.comp measurable_prodMk_left)).symm

end HardSphere.Comparison
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
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPrimary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_BathPhase
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere

lemma cons_preserving {n : ℕ} (L : Length) :
    MeasurePreserving (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1)
      (volume.prod volume) volume := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm
  have hh := h.comp (measurePreserving_swap (μ:= (volume : Measure (Configuration n L))) (ν:=volume))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p i
  simp [MeasurableEquiv.piFinSuccAbove]

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalDisintegration
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
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

theorem actual_physical_branch_joint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M)) :
    let p := fun i ↦ i∈groupUnion g a
    let B := labelInteraction N L r (2*t)∩
      flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
    let ν := exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p B
    (ν.compProd (fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law))
      (blockEvent p B))).map (fun z ↦
        (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) (blockGlue p z),a),
          selectedPhysicalPath (L:=L) (2*t) p z)) =
    (ν.map (physicalBranchDatum g b a (2*t))).compProd
      (datumPhysicalReference hL g a m r R C S t u) := by
  dsimp only
  let p := fun i ↦ i∈groupUnion g a
  let B := labelInteraction N L r (2*t)∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
  let μ₀ := allocationBase μ (gridAllocationKernel hL (G*M)) b a
  let ν := exposedLaw μ₀ (fun _ : Fin N ↦ Bridge.law) p B
  let κ := fiberNormalize (Kernel.const _ (Measure.pi fun _ : {i // p i} ↦ Bridge.law)) (blockEvent p B)
  have hB : MeasurableSet B := (labelInteraction_measurable N L r (2*t)).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)
  have : SFinite ν := by dsimp [ν,exposedLaw]; infer_instance
  have hr := exposed_block_reconstruct μ₀ (fun _ : Fin N ↦ Bridge.law) p hB
  have he : ∀ᵐ z ∂((μ₀.prod (Measure.pi fun _ : Fin N ↦ Bridge.law)).restrict B),
      physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a)=
        physicalBranchDatum g b a (2*t) (blockExpose p z) := by
    filter_upwards [ae_restrict_of_ae (label_endpoints_ae (2*t) μ₀),ae_restrict_mem hB] with z hz hzB
    exact physicalDatum_branch_of g b a m r R C S s₀ (2*t) u z hz.1 hz.2 hzB.2
  have he' : ∀ᵐ z ∂ν.compProd κ,
      physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) (blockGlue p z),a)=
        physicalBranchDatum g b a (2*t) z.1 := by
    rw [←hr] at he
    have ht := ae_of_ae_map (blockGlue_measurable p).aemeasurable he
    have ht' := ht.mono (fun z hz ↦ show
        physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) (blockGlue p z),a)=
          physicalBranchDatum g b a (2*t) z.1 from by
      have hzg := congrFun (blockExpose_glue (E:=BridgeEndpoints N L)
        (X:=fun _ : Fin N ↦ Bridge.Noise) p) z
      simpa only [Function.comp_apply] using hz.trans (congrArg (physicalBranchDatum g b a (2*t)) hzg))
    dsimp only [ν,κ]
    convert ht' using 1
    all_goals try with_reducible_and_instances rfl
    congr 20
    all_goals try exact Subsingleton.elim _ _
  trans (ν.compProd κ).map (fun z ↦
    (physicalBranchDatum g b a (2*t) z.1,selectedPhysicalPath (L:=L) (2*t) p z))
  · apply Measure.map_congr
    filter_upwards [he'] with z hz
    exact Prod.ext hz rfl
  · exact coarse_joint_reference ν κ _ _ (physicalBranchDatum_measurable g b a (2*t))
      _ (selectedPhysicalPath_measurable (2*t) p)
      (actual_allocated_physical_coarse_fiber hL hK h50 μ m r R C S s₀ t u g b a)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalBranchLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
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
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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

lemma primaryBathKernel_apply (b : Bool) (i : Fin (n+1)) (F : Option (Fin (n+1))→E) :
    primaryBathKernel b i F=(uniformBathOrder n).map (fun τ ↦ orderedPrimaryObservation b i (F,τ)) := by
  rw [primaryBathKernel,Kernel.map_apply _ (orderedPrimaryObservation_measurable b i),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (orderedPrimaryObservation_measurable b i) measurable_prodMk_left]
  rfl
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

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [NeZero K] in
lemma unitTarget_project {L : Length} (hL : 1≤L.val) (v : Fin 3→Fin K) (z : Point)
    (hz : z∈unitTarget (anchorPoint v)) : projectPoint L z∈centeredCell L (gridCenter L v) := by
  rw [centeredCell_image hL]
  intro j
  have hj := hz j (mem_univ j)
  refine ⟨z j-(v j:ℝ),⟨?_,?_⟩,?_⟩
  · change (v j:ℝ)-1/2≤z j ∧ z j<(v j:ℝ)+1/2 at hj
    linarith [hj.1]
  · change (v j:ℝ)-1/2≤z j ∧ z j<(v j:ℝ)+1/2 at hj
    linarith [hj.2]
  · change ((z j-(v j:ℝ):ℝ):AddCircle L.val)=((z j:ℝ):AddCircle L.val)-((v j:ℝ):AddCircle L.val)
    exact QuotientAddGroup.mk_sub _ _ _

omit [NeZero K] in
lemma cellPathReference_support {L : Length} (hL : 1≤L.val) (v : Fin 3→Fin K) :
    ∀ᵐp ∂cellPathReference v,projectPoint L (p midpointTime)∈centeredCell L (gridCenter L v) := by
  have hm : Measurable (fun p : C(Time,Point) ↦ projectPoint L (p midpointTime)) :=
    (projectPoint_continuous L).measurable.comp (continuous_eval_const midpointTime).measurable
  rw [cellPathReference,ae_map_iff pointAsPath_measurable.aemeasurable ((centeredCell_measurable L _).preimage hm)]
  unfold targetUniform
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (unitTarget_measurable (anchorPoint v))] with z hz
  exact unitTarget_project hL v z hz

omit [NeZero K] [DecidableEq J] in
lemma physicalTagEvent_measurable {N M G : ℕ} {L : Length} (particle : J↪Fin N)
    (v : Fin 3→Fin K) (i : Fin N) : MeasurableSet (physicalTagEvent (M:=M) (G:=G) (L:=L) particle v i) :=
  .inter (show MeasurableSet {z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) | i∈Set.range particle} from by
    by_cases h : i∈Set.range particle <;> simp [h]) ((centeredCell_measurable L _).preimage
    ((measurable_pi_apply (some i)).comp (physicalFullMidpoint_measurable particle)))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalCellUniform
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
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma point_chart_preserving (L : Length) (c : Point) :
    MeasurePreserving (projectPoint L)
      (volume.restrict (univ.pi (fun j ↦ Icc (c j-L.val/2) (c j+L.val/2)))) volume := by
  have hp (j : Fin 3) : MeasurePreserving (fun value : ℝ ↦ (value : AddCircle L.val))
      (volume.restrict (Icc (c j-L.val/2) (c j+L.val/2))) volume := by
    have hj := AddCircle.measurePreserving_mk L.val (c j-L.val/2)
    rw [restrict_Ioc_eq_restrict_Icc,show c j-L.val/2+L.val=c j+L.val/2 by ring] at hj
    exact hj
  change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _)
    (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
  simpa only [projectPoint,Measure.restrict_pi_pi] using measurePreserving_pi
    (fun j : Fin 3 ↦ volume.restrict (Icc (c j-L.val/2) (c j+L.val/2)))
    (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))) hp

lemma cellPathReference_midpoint_le {K : ℕ} [NeZero K] {L : Length} (hL : 1≤L.val)
    (v : Fin 3→Fin K) :
    (cellPathReference v).map (fun p ↦ projectPoint L (p midpointTime)) ≤
      volume.restrict (centeredCell L (gridCenter L v)) := by
  let f := fun p : C(Time,Point) ↦ projectPoint L (p midpointTime)
  have hf : Measurable f := (projectPoint_continuous L).measurable.comp
    (continuous_eval_const midpointTime).measurable
  have hs : ∀ᵐx ∂(cellPathReference v).map f,x∈centeredCell L (gridCenter L v) := by
    exact (ae_map_iff hf.aemeasurable (centeredCell_measurable L (gridCenter L v))).mpr
      (cellPathReference_support hL v)
  rw [←Measure.restrict_eq_self_of_ae_mem hs]
  apply Measure.restrict_mono_measure
  rw [cellPathReference,Measure.map_map hf pointAsPath_measurable]
  change (targetUniform (unitTarget (anchorPoint v))).map (projectPoint L)≤volume
  rw [targetUniform,unitTarget_volume,inv_one,one_smul]
  have hsub : unitTarget (anchorPoint v) ⊆
      univ.pi (fun j ↦ Icc (anchorPoint v j-L.val/2) (anchorPoint v j+L.val/2)) := by
    intro x hx j hj
    have h := hx j hj
    constructor <;> linarith [h.1,h.2]
  exact (Measure.map_mono (Measure.restrict_mono_set volume hsub) (projectPoint_continuous L).measurable).trans_eq
    (point_chart_preserving L (anchorPoint v)).map_eq

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalMidpointReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBathKernel_markov _root_.OAI.HardSphere.Groups.physicalCodeObserver_markov _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.taggedPhysicalBathKernel_markov _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
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

theorem physicalBranch_reference_raw {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) :
    (physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (datumPhysicalReference hL g a m r R C S t u)=
    (rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).map
      (fun z ↦ (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        fun i : {i // i∈groupUnion g a} ↦ onePathAt i (labelBridgePath N L (2*t) z))) := by
  let p := fun i ↦ i∈groupUnion g a
  let B := labelInteraction N L r (2*t)∩
    flagEvent (eligibilityFlag (K:=K) m r R C S s₀ (2*t) u) b
  have hB : MeasurableSet B := (labelInteraction_measurable N L r (2*t)).inter
    (flagEvent_measurable _ (fun i ↦ eligibilityFlag_measurable m r R C S s₀ (2*t) u i) b)
  have hm : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        fun i : {i // p i} ↦ onePathAt i (labelBridgePath N L (2*t) z))) :=
    ((physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L (2*t)).prodMk measurable_const)).prodMk
        (Measurable.of_eval fun i ↦ (onePathAt_continuous (i:Fin N)).measurable.comp
          (labelBridgePath_measurable N L (2*t)))
  rw [physicalBranchLaw,←actual_physical_branch_joint hL hK h50 μ m r R C S s₀ t u g b a]
  have : SFinite (exposedLaw (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p B) := by unfold exposedLaw; infer_instance
  have H := congrArg (fun ν ↦ ν.map (fun z ↦
    (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
      fun i : {i // p i} ↦ onePathAt i (labelBridgePath N L (2*t) z))))
    (exposed_block_reconstruct (allocationBase μ (gridAllocationKernel hL (G*M)) b a)
      (fun _ : Fin N ↦ Bridge.law) p hB)
  rw [Measure.map_map hm (blockGlue_measurable p)] at H
  dsimp only [Function.comp_def,rawPhysicalBranch,selectedPhysicalPath,p,B] at H ⊢
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 20
  all_goals try exact Subsingleton.elim _ _
  funext z
  unfold selectedPhysicalPath
  congr 20
  all_goals first | exact Subsingleton.elim _ _ | (funext index; congr 20)

lemma physicalRecoveredPath_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) :
    Measurable (physicalRecoveredPath (L:=L) g a) := by
  apply Measurable.of_eval
  intro i
  unfold physicalRecoveredPath
  by_cases hi : i∈groupUnion g a
  · simp only [dite_eq_left hi]
    exact (measurable_pi_apply (⟨i,hi⟩ : {i // i∈groupUnion g a})).comp measurable_snd
  · simp only [dite_eq_right hi]
    exact (datumFrozen_measurable i).comp measurable_fst
lemma physicalRecoveredPath_actual {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (F : ConfigurationPath N L) :
    physicalRecoveredPath g a (physicalDatum g m r R C S s₀ u (F,a),fun i ↦ onePathAt i F)=
      fun i ↦ onePathAt i F := by
  funext i
  by_cases hi : i∈groupUnion g a <;> simp [physicalRecoveredPath,physicalDatum,hi]

lemma physicalRecoveredMidpoint_measurable {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) : Measurable (physicalRecoveredMidpoint (L:=L) g a) :=
  Measurable.of_eval fun i ↦ (measurable_pi_apply 0).comp
    ((continuous_eval_const midpointTime).measurable.comp
      ((measurable_pi_apply i).comp (physicalRecoveredPath_measurable g a)))
lemma physicalRecoveredMidpoint_actual {N K M G : ℕ} {L : Length} (g : Fin G)
    (a : GridAllocation N K (G*M)) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (F : ConfigurationPath N L) :
    physicalRecoveredMidpoint g a (physicalDatum g m r R C S s₀ u (F,a),fun i ↦ onePathAt i F)=
      F midpointTime := by
  unfold physicalRecoveredMidpoint
  rw [physicalRecoveredPath_actual]
  rfl

theorem physicalBranch_midpoint_raw {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) :
    ((physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (datumGroupReference hL g a m r R C S t u)).map
        (fun z ↦ (z.1,physicalRecoveredMidpoint g a (z.1,projectGroup z.2)))=
    (rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).map
      (fun z ↦ (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        labelBridgePath N L (2*t) z midpointTime)) := by
  have hm := measurable_fst.prodMk (physicalRecoveredMidpoint_measurable (L:=L) g a)
  have H := congrArg (fun ν ↦ ν.map (fun z ↦ (z.1,physicalRecoveredMidpoint g a z)))
    (physicalBranch_reference_raw hL hK h50 μ g b a m r R C S s₀ t u)
  rw [datumPhysicalReference,Measure.compProd_map projectGroup_measurable,
    Measure.map_map hm (measurable_id.prodMap projectGroup_measurable)] at H
  have hr : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        fun i : {i // i∈groupUnion g a} ↦ onePathAt i (labelBridgePath N L (2*t) z))) :=
    ((physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L (2*t)).prodMk measurable_const)).prodMk
        (Measurable.of_eval fun i ↦ (onePathAt_continuous (i:Fin N)).measurable.comp
          (labelBridgePath_measurable N L (2*t)))
  rw [Measure.map_map hm hr] at H
  simpa only [Function.comp_def,Prod.map,Function.id_def,physicalRecoveredMidpoint_actual] using H

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalFullReference
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBathKernel_markov _root_.OAI.HardSphere.Groups.physicalCodeObserver_markov _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.taggedPhysicalBathKernel_markov _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {D W V : Type*} [MeasurableSpace D] [MeasurableSpace W] [MeasurableSpace V]

lemma compProd_prod_const (μ : Measure D) [SFinite μ] (κ : Kernel D W) [IsSFiniteKernel κ]
    (η : Measure V) [SFinite η] :
    (μ.compProd (κ ×ₖ Kernel.const D η)).map MeasurableEquiv.prodAssoc.symm =
      (μ.compProd κ).prod η := by
  have he : κ ×ₖ Kernel.const D η=κ ⊗ₖ Kernel.const (D×W) η := by
    ext d s hs
    rw [Kernel.prod_apply,Measure.prod_apply hs,Kernel.compProd_apply hs]
    rfl
  rw [he,Measure.compProd_assoc,Measure.compProd_const]
end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalFullMidpoint_split {N K M G : ℕ} {L : Length}
    (g : Fin G) (a : GridAllocation N K (G*M)) (d : PhysicalDatum N K M G L)
    (w : {i // i∈groupUnion g a}→C(Time,Point)) (e : C(Time,Point)) :
    physicalFullMidpoint (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a))
      (d,(MeasurableEquiv.piOptionEquivProd (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm (w,e)) =
    fun i ↦ i.elim (projectPoint L (e midpointTime))
      (physicalRecoveredMidpoint g a (d,projectGroup w)) := by
  let p := Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)
  funext i
  cases i with
  | none =>
    change fillGroup p _ _ (optionParticle p none)=_
    rw [fillGroup_selected]
    rfl
  | some i =>
    by_cases hi : i∈groupUnion g a
    · change fillGroup p _ _ (optionParticle p (some ⟨i,hi⟩))=_
      rw [fillGroup_selected]
      simp only [Option.elim_some,physicalRecoveredMidpoint,physicalRecoveredPath,dite_eq_left hi]
      rfl
    · have hn : some i∉Set.range (optionParticle p) := by
        rintro ⟨j,hj⟩
        cases j with
        | none => cases hj
        | some j => exact hi ((Option.some.inj hj) ▸ j.property)
      unfold physicalFullMidpoint fillGroup
      rw [Function.extend_apply' _ _ _ hn]
      simp only [Option.elim_some,physicalRecoveredMidpoint,physicalRecoveredPath,dite_eq_right hi]

theorem physicalPrimary_joint_split {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (μ : Measure (PhysicalDatum N K M G L)) [SFinite μ]
    (g : Fin G) (a : GridAllocation N K (G*M)) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (v : Fin 3→Fin K) :
    μ.compProd (physicalPrimaryReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) v)=
    ((μ.compProd (datumGroupReference hL g a m r R C S t u)).prod (cellPathReference v)).map
      (fun z ↦ (z.1.1,(MeasurableEquiv.piOptionEquivProd
        (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm (z.1.2,z.2))) := by
  let e := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i // i∈groupUnion g a} ↦ C(Time,Point))).symm
  have he : physicalPrimaryReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) v =
      ((datumGroupReference hL g a m r R C S t u) ×ₖ Kernel.const _ (cellPathReference v)).map e := by
    ext d : 1
    rw [physicalPrimaryReference_actual,Kernel.map_apply _ e.measurable,Kernel.prod_apply,Kernel.const_apply]
  rw [he,Measure.compProd_map e.measurable]
  rw [←compProd_prod_const μ (datumGroupReference hL g a m r R C S t u) (cellPathReference v),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem physicalBranch_full_midpoint_raw {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (v : Fin 3→Fin K) :
    ((physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (physicalPrimaryReference hL g m t r R C S u
        (fun i : {i // i∈groupUnion g a} ↦ i.val) v)).map
          (fun z ↦ (z.1,physicalFullMidpoint (Function.Embedding.subtype
            (fun i ↦ i∈groupUnion g a)) z)) =
    ((rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).prod (cellPathReference v)).map
      (fun z ↦ (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z.1,a),
        fun i ↦ i.elim (projectPoint L (z.2 midpointTime))
          (labelBridgePath N L (2*t) z.1 midpointTime))) := by
  let f := fun z : (PhysicalDatum N K M G L×Configuration N L)×C(Time,Point) ↦
    (z.1.1,fun i : Option (Fin N) ↦ i.elim (projectPoint L (z.2 midpointTime)) z.1.2)
  have hf : Measurable f := by
    apply measurable_fst.fst.prodMk
    apply Measurable.of_eval
    intro i
    cases i with
    | none =>
      exact (projectPoint_continuous L).measurable.comp
        ((continuous_eval_const midpointTime).measurable.comp measurable_snd)
    | some i => exact (measurable_pi_apply i).comp measurable_fst.snd
  have hg : Measurable (fun z : PhysicalDatum N K M G L×({i // i∈groupUnion g a}→C(Time,Point)) ↦
      (z.1,physicalRecoveredMidpoint g a (z.1,projectGroup z.2))) :=
    measurable_fst.prodMk ((physicalRecoveredMidpoint_measurable g a).comp
      (measurable_fst.prodMk (projectGroup_measurable.comp measurable_snd)))
  have hr : Measurable (fun z : BridgeEndpoints N L×(Fin N→Bridge.Noise) ↦
      (physicalDatum g m r R C S s₀ u (labelBridgePath N L (2*t) z,a),
        labelBridgePath N L (2*t) z midpointTime)) :=
    ((physicalDatum_measurable g m r R C S s₀ u).comp
      ((labelBridgePath_measurable N L (2*t)).prodMk measurable_const)).prodMk
        ((continuous_eval_const midpointTime).measurable.comp (labelBridgePath_measurable N L (2*t)))
  have H := congrArg (fun ν ↦ (ν.prod (cellPathReference v)).map f)
    (physicalBranch_midpoint_raw hL hK h50 μ g b a m r R C S s₀ t u)
  have fix (η : Measure C(Time,Point)) : η.map id=η := Measure.map_id
  conv_lhs at H => rw [←fix (cellPathReference v),Measure.map_prod_map _ _ hg measurable_id]
  conv_rhs at H => rw [←fix (cellPathReference v),Measure.map_prod_map _ _ hr measurable_id]
  rw [Measure.map_map hf (hg.prodMap measurable_id),Measure.map_map hf (hr.prodMap measurable_id)] at H
  rw [physicalPrimary_joint_split,Measure.map_map
    (measurable_fst.prodMk (physicalFullMidpoint_measurable _)) (by fun_prop)]
  convert H using 1
  · apply Measure.map_congr
    filter_upwards [] with z
    simp only [Function.comp_def,Prod.map,Function.id_def,f,physicalFullMidpoint_split]
  · rfl

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalProjectedPrimary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBathKernel_markov _root_.OAI.HardSphere.Groups.physicalCodeObserver_markov _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.taggedPhysicalBathKernel_markov _root_.OAI.HardSphere.Rescaling.config_haar
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

theorem physicalBranch_primary_midpoint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (v : Fin 3→Fin K) :
    ((physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u).compProd
      (physicalPrimaryReference hL g m t r R C S u
        (fun i : {i // i∈groupUnion g a} ↦ i.val) v)).map
          (physicalFullMidpoint (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a))) =
    (((rawPhysicalBranch hL μ g b a m r R C S s₀ (2*t) u).map
      (fun z ↦ labelBridgePath N L (2*t) z midpointTime)).prod
      ((cellPathReference v).map (fun e ↦ projectPoint L (e midpointTime)))).map
        (fun z i ↦ i.elim z.2 z.1) := by
  have H := congrArg (fun ν ↦ ν.map Prod.snd)
    (physicalBranch_full_midpoint_raw hL hK h50 μ g b a m r R C S s₀ t u v)
  rw [Measure.map_map measurable_snd
    (measurable_fst.prodMk (physicalFullMidpoint_measurable _)),
    Measure.map_map measurable_snd (by
      apply Measurable.prodMk
      · exact (physicalDatum_measurable g m r R C S s₀ u).comp
          (((labelBridgePath_measurable N L (2*t)).comp measurable_fst).prodMk measurable_const)
      · apply Measurable.of_eval
        intro i
        cases i with
        | none =>
          exact (projectPoint_continuous L).measurable.comp
            ((continuous_eval_const midpointTime).measurable.comp measurable_snd)
        | some i =>
          exact (measurable_pi_apply i).comp
            ((continuous_eval_const midpointTime).measurable.comp
              ((labelBridgePath_measurable N L (2*t)).comp measurable_fst)))] at H
  have hf : Measurable (fun z ↦ labelBridgePath N L (2*t) z midpointTime) :=
    (continuous_eval_const midpointTime).measurable.comp (labelBridgePath_measurable N L (2*t))
  have he : Measurable (fun e : C(Time,Point) ↦ projectPoint L (e midpointTime)) :=
    (projectPoint_continuous L).measurable.comp (continuous_eval_const midpointTime).measurable
  rw [Measure.map_prod_map _ _ hf he,Measure.map_map (by
    apply Measurable.of_eval
    intro i
    cases i with
    | none => exact measurable_snd
    | some i => exact (measurable_pi_apply i).comp measurable_fst) (hf.prodMap he)]
  exact H

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SymmetricTag
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.gridAllocationKernel_markov _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBathKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalCodeObserver_markov _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.taggedPhysicalBathKernel_markov _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
lemma splitFirst_measurable : Measurable (splitFirst (E:=E) (n:=n)) := by
  unfold splitFirst
  fun_prop

attribute [local instance] OAI.HardSphere.Comparison.permSpace
attribute [local instance] OAI.HardSphere.Comparison.permSingleton
lemma orderedObservation_measurable (i : Fin (n+1)) : Measurable (orderedObservation (E:=E) i) := by
  unfold orderedObservation
  have he (j : Fin n) : Measurable (fun p : (Fin (n+1)→E)×Equiv.Perm (Fin n) ↦ p.1 (i.succAbove (p.2 j))) := by
    exact measurable_from_prod_countable_left (fun τ ↦ show Measurable (fun x : Fin (n+1)→E ↦ x (i.succAbove (τ j))) from measurable_pi_apply _)
  exact ((measurable_pi_apply i).comp measurable_fst).prodMk (Measurable.of_eval he)

omit [MeasurableSpace E] in
lemma orderedObservation_eq (i : Fin (n+1)) (x : Fin (n+1)→E) (τ : Equiv.Perm (Fin n)) :
    orderedObservation i (x,τ)=splitFirst (fun j ↦ x (tagOrderPerm i τ j)) := by
  simp [orderedObservation,splitFirst]

lemma ordered_symmetric_law (μ : Measure (Fin (n+1)→E)) [SFinite μ]
    (hμ : ∀σ : Equiv.Perm (Fin (n+1)),MeasurePreserving (fun x j ↦ x (σ j)) μ μ)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    (μ.prod β).map (orderedObservation i)=μ.map splitFirst := by
  ext s hs
  rw [Measure.map_apply (orderedObservation_measurable i) hs,Measure.map_apply splitFirst_measurable hs]
  rw [Measure.prod_apply_symm ((orderedObservation_measurable i) hs)]
  have hh (τ : Equiv.Perm (Fin n)) : μ ((fun x : Fin (n+1)→E ↦ (x,τ)) ⁻¹' (orderedObservation i ⁻¹' s))=μ (splitFirst ⁻¹' s) := by
    have he : ((fun x : Fin (n+1)→E ↦ (x,τ)) ⁻¹' (orderedObservation i ⁻¹' s))=
        (fun x j ↦ x (tagOrderPerm i τ j)) ⁻¹' (splitFirst ⁻¹' s) := by
      ext x
      simp only [Set.mem_preimage,orderedObservation_eq]
    rw [he]
    exact (hμ (tagOrderPerm i τ)).measure_preimage ((splitFirst_measurable hs).nullMeasurableSet)
  simp_rw [hh]
  simp

lemma ground_ordered_law {L : Length} (u : Jet (n+1) L) (hb : bosonic u.1) (hu : ‖u.1‖=1)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    ((groundPositionLaw (n+1) L u).prod β).map (orderedObservation i)=
      (groundPositionLaw (n+1) L u).map splitFirst := by
  let := groundPositionLaw_probability u hu
  apply ordered_symmetric_law
  intro σ
  exact groundPositionLaw_permute u hb σ
lemma ground_first_density {L : Length} (u : Jet (n+1) L) :
    (groundPositionLaw (n+1) L u).map splitFirst=
      ((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)) := by
  let c : Torus L×Configuration n L → Configuration (n+1) L := fun p ↦ Fin.cons p.1 p.2
  have hc : Measurable c := by unfold c; fun_prop
  have hcP : MeasurePreserving c ((volume : Measure (Torus L)).prod volume) volume :=
    (cons_preserving L).comp Measure.measurePreserving_swap
  let g : Configuration (n+1) L→ℝ≥0∞ := fun X ↦ ENNReal.ofReal (‖u.1 X‖^2)
  have hg : Measurable g := ((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal
  have he := map_density_comp ((volume : Measure (Torus L)).prod volume) c hc g hg
  rw [hcP.map_eq] at he
  change _=groundPositionLaw (n+1) L u at he
  rw [←he,Measure.map_map splitFirst_measurable hc]
  have hid : splitFirst ∘ c=id := by
    funext p
    simp [c,splitFirst]
  rw [hid,Measure.map_id]
  rfl

instance orderedKernel_markov (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β]
    (i : Fin (n+1)) : IsMarkovKernel (orderedKernel (E:=E) β i) :=
  Kernel.IsMarkovKernel.map _ (orderedObservation_measurable i)
lemma orderedKernel_comp (μ : Measure (Fin (n+1)→E)) [SFinite μ]
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    orderedKernel β i ∘ₘ μ=(μ.prod β).map (orderedObservation i) := by
  unfold orderedKernel
  rw [←Measure.map_comp _ _ (orderedObservation_measurable i),←Measure.compProd_eq_comp_prod,
    Measure.compProd_const]

lemma ground_ordered_bind {L : Length} (u : Jet (n+1) L) (hb : bosonic u.1) (hu : ‖u.1‖=1)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β] (i : Fin (n+1)) :
    orderedKernel β i ∘ₘ groundPositionLaw (n+1) L u=
      ((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)) := by
  let := groundPositionLaw_probability u hu
  rw [orderedKernel_comp,ground_ordered_law u hb hu,ground_first_density]

lemma all_tags_reference {L : Length} {Y : Type*} [MeasurableSpace Y]
    (u : Jet (n+1) L) (hb : bosonic u.1) (hu : ‖u.1‖=1)
    (β : Measure (Equiv.Perm (Fin n))) [IsProbabilityMeasure β]
    (post : Kernel (Torus L×Configuration n L) Y) :
    (∑i : Fin (n+1),(post ∘ₖ orderedKernel β i) ∘ₘ groundPositionLaw (n+1) L u)=
      (n+1) • (post ∘ₘ (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration n L ↦ ENNReal.ofReal (‖u.1 (Fin.cons p.1 p.2)‖^2)))) := by
  simp_rw [←Measure.comp_assoc,ground_ordered_bind u hb hu β]
  simp

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
attribute [local instance] HardSphere.Comparison.permSpace HardSphere.Comparison.permSingleton
namespace HardSphere.Comparison
variable {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]

lemma comp_comap_map (μ : Measure A) (f : A→B) (hf : Measurable f) (κ : Kernel B C) :
    κ.comap f hf ∘ₘ μ=κ ∘ₘ μ.map f := by
  rw [←Kernel.comp_deterministic_eq_comap,←Measure.comp_assoc,Measure.deterministic_comp_eq_map]

lemma allocation_slice_law {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) (T : ℝ) (hT : 0≤T) (q : Wiener.Time)
    {Z : Type*} [MeasurableSpace Z]
    (κ : Kernel (ConfigurationPath N L) Z) [IsMarkovKernel κ] :
    ((groundPathLaw N L a T u) ⊗ₘ κ).map
      (fun p : ConfigurationPath N L×Z ↦ p.1 q)=groundPositionLaw N L u := by
  let := hu.groundPathLaw_probability hT
  have he : (fun p : ConfigurationPath N L×Z ↦ p.1 q)=
      (fun ω : ConfigurationPath N L ↦ ω q) ∘ Prod.fst := rfl
  rw [he,←Measure.map_map (continuous_eval_const q).measurable measurable_fst]
  change ((groundPathLaw N L a T u ⊗ₘ κ).fst).map _=_
  rw [Measure.fst_compProd]
  exact (hu.groundPathLaw_marginal T hT q).map_eq

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalCellReference
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
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma restrict_kernel_comp (κ : Kernel X Y) (μ : Measure X) {s : Set Y}
    (hs : MeasurableSet s) : κ.restrict hs ∘ₘ μ=(κ ∘ₘ μ).restrict s := by
  ext t ht
  rw [Measure.bind_apply ht (κ.restrict hs).aemeasurable,
    Measure.restrict_apply ht,Measure.bind_apply (ht.inter hs) κ.aemeasurable]
  congr 1
  funext x
  exact Kernel.restrict_apply' κ hs x ht

lemma cellExtraKernel_comp (μ : Measure (X×Y)) [SFinite μ]
    (ν : Measure X) [SFinite ν] (A B : Set X) (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    cellExtraKernel (Y:=Y) ν A B hA ∘ₘ μ=
      (μ.prod ν).restrict {p | p.1.1∈A ∧ p.2∈B} := by
  rw [cellExtraKernel,restrict_kernel_comp,←Measure.compProd_eq_comp_prod,
    Measure.compProd_const]
  have hp : μ.prod (ν.restrict B)=(μ.prod ν).restrict (univ×ˢB) := by
    simpa only [Measure.restrict_univ] using Measure.prod_restrict (μ:=μ) (ν:=ν) univ B
  rw [hp,Measure.restrict_restrict' (MeasurableSet.univ.prod hB)]
  congr 1
  ext p
  simp

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PrimaryProduct
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
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

lemma adjoinPoint_measurable : Measurable (adjoinPoint (n:=n) (E:=E)) := by
  apply Measurable.of_eval
  intro i
  cases i with
  | none => exact measurable_snd
  | some i => exact (measurable_pi_apply i).comp measurable_fst

lemma cellObservation_measurable (b : Bool) : Measurable (cellObservation (n:=n) (E:=E) b) := by
  unfold cellObservation
  split_ifs <;> fun_prop

theorem primaryBath_product (P : Measure (Fin (n+1)→E)) [SFinite P]
    (η : Measure E) [SFinite η] (b : Bool) (i : Fin (n+1)) :
    primaryBathKernel b i ∘ₘ (P.prod η).map adjoinPoint =
      (((P.prod (uniformBathOrder n)).map (orderedObservation i)).prod η).map (cellObservation b) := by
  ext s hs
  rw [Measure.bind_apply hs (primaryBathKernel b i).aemeasurable,
    lintegral_map ((primaryBathKernel b i).measurable_coe hs) adjoinPoint_measurable,
    lintegral_prod _ (show AEMeasurable (fun a ↦ primaryBathKernel b i (adjoinPoint a) s) (P.prod η) from
      (((primaryBathKernel b i).measurable_coe hs).comp adjoinPoint_measurable).aemeasurable),
    Measure.map_apply (cellObservation_measurable b) hs,Measure.prod_apply
      ((cellObservation_measurable b) hs)]
  have hm := measurable_measure_prodMk_left (ν:=η) ((cellObservation_measurable b) hs)
  rw [lintegral_map hm (orderedObservation_measurable i),
    lintegral_prod _ (show AEMeasurable (fun a ↦ η (Prod.mk (orderedObservation i a) ⁻¹' cellObservation b ⁻¹' s)) _ from
      (hm.comp (orderedObservation_measurable i)).aemeasurable)]
  apply lintegral_congr
  intro X
  simp_rw [primaryBathKernel_apply]
  have hh : Measurable (fun z : E×Equiv.Perm (Fin n) ↦
      (s.indicator (fun _ ↦ (1:ℝ≥0∞)))
        (orderedPrimaryObservation b i (adjoinPoint (X,z.1),z.2))) :=
    (measurable_const.indicator hs).comp ((orderedPrimaryObservation_measurable b i).comp
      ((adjoinPoint_measurable.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd))
  convert (lintegral_lintegral_swap (μ:=η) (ν:=uniformBathOrder n)
    (f:=fun e τ ↦ s.indicator (fun _ ↦ (1:ℝ≥0∞))
      (orderedPrimaryObservation b i (adjoinPoint (X,e),τ))) hh.aemeasurable) using 1
  · apply lintegral_congr
    intro e
    rw [←lintegral_indicator_one hs]
    exact lintegral_map (measurable_const.indicator hs)
      (show Measurable (fun τ ↦ orderedPrimaryObservation b i (adjoinPoint (X,e),τ)) from
        (orderedPrimaryObservation_measurable b i).comp (measurable_const.prodMk measurable_id))
  · apply lintegral_congr
    intro τ
    have he : (fun e ↦ orderedPrimaryObservation b i (adjoinPoint (X,e),τ))=
        (fun e ↦ cellObservation b (orderedObservation i (X,τ),e)) := by
      funext e
      cases b <;> rfl
    change η ((fun e ↦ cellObservation b (orderedObservation i (X,τ),e)) ⁻¹' s)=_
    have hm : Measurable (fun e ↦ cellObservation b (orderedObservation i (X,τ),e)) :=
      (cellObservation_measurable b).comp measurable_prodMk_left
    rw [←Measure.map_apply hm hs,←lintegral_indicator_one hs]
    refine (lintegral_map (measurable_const.indicator hs) hm).trans ?_
    exact congrArg (fun f ↦ ∫⁻e,s.indicator (fun _ ↦ (1:ℝ≥0∞)) (f e) ∂η) he.symm

end HardSphere.Comparison
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {n : ℕ} {E : Type*} [MeasurableSpace E]
attribute [local instance] permBathSpace permBathSingleton

lemma prod_restrict_first (P : Measure E) [SFinite P] {Y : Type*} [MeasurableSpace Y]
    (η : Measure Y) [SFinite η] (A : Set E) :
    (P.restrict A).prod η=(P.prod η).restrict (Prod.fst ⁻¹' A) := by
  have H := Measure.prod_restrict (μ:=P) (ν:=η) A univ
  simpa only [Measure.restrict_univ,Set.prod_univ] using H

lemma orderedKernel_restrict (P : Measure (Fin (n+1)→E)) [SFinite P]
    (i : Fin (n+1)) (A : Set E) (hA : MeasurableSet A) :
    (orderedKernel (uniformBathOrder n) i ∘ₘ P).restrict (Prod.fst ⁻¹' A)=
      orderedKernel (uniformBathOrder n) i ∘ₘ P.restrict ((fun X ↦ X i) ⁻¹' A) := by
  rw [orderedKernel_comp,orderedKernel_comp,Measure.restrict_map (orderedObservation_measurable i)
    (hA.preimage measurable_fst),prod_restrict_first]
  rfl

theorem primaryBath_cell_reference (P : Measure (Fin (n+1)→E)) [SFinite P]
    (η : Measure E) [SFinite η] (b : Bool) (i : Fin (n+1))
    (A : Set E) (hA : MeasurableSet A) :
    primaryBathKernel b i ∘ₘ ((P.prod η).map adjoinPoint).restrict ((fun F ↦ F (some i)) ⁻¹' A)=
      (((cellExtraKernel (Y:=Fin n→E) η A univ hA).map (cellObservation b)) ∘ₖ
        orderedKernel (uniformBathOrder n) i) ∘ₘ P := by
  rw [Measure.restrict_map adjoinPoint_measurable (hA.preimage (measurable_pi_apply (some i)))]
  have he : adjoinPoint ⁻¹' ((fun F : Option (Fin (n+1))→E ↦ F (some i)) ⁻¹' A)=
      Prod.fst ⁻¹' ((fun X : Fin (n+1)→E ↦ X i) ⁻¹' A) := rfl
  rw [he,←prod_restrict_first,primaryBath_product,←orderedKernel_comp,
    ←Measure.comp_assoc,←Measure.map_comp _ _ (cellObservation_measurable b),
    cellExtraKernel_comp _ η A univ hA MeasurableSet.univ]
  have he' : {p : (E×(Fin n→E))×E | p.1.1∈A ∧ p.2∈univ}=
      Prod.fst ⁻¹' (Prod.fst ⁻¹' A) := by ext p; simp
  rw [he',←prod_restrict_first,orderedKernel_restrict _ _ A hA]

end HardSphere.Comparison
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

lemma taggedEvent_measurable (E : I→Set X) (hE : ∀i,MeasurableSet (E i)) :
    MeasurableSet {p : I×X | p.2∈E p.1} := by
  have he : {p : I×X | p.2∈E p.1}=⋃i,({i}:Set I)×ˢE i := by ext p; simp
  rw [he]
  exact MeasurableSet.iUnion (fun i ↦ (measurableSet_singleton i).prod (hE i))

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_TagPushforward
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
variable {I X Y Z : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

lemma taggedReference_comp (P : Measure X) [SFinite P] (E : I→Set X)
    (hE : ∀i,MeasurableSet (E i)) (κ : Kernel (I×X) Y) :
    κ ∘ₘ taggedReference P E =
      ∑i,(κ.comap (Prod.mk i) measurable_prodMk_left) ∘ₘ P.restrict (E i) := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.bind_apply hs κ.aemeasurable]
  simp only [Measure.finsetSum_apply,Measure.bind_apply hs (κ.comap _ _).aemeasurable,
    Kernel.comap_apply]
  unfold taggedReference
  rw [←lintegral_indicator (taggedEvent_measurable E hE),lintegral_prod _
    (((κ.measurable_coe hs).indicator (taggedEvent_measurable E hE)).aemeasurable),
    lintegral_count,tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [←lintegral_indicator (hE i)]
  rfl

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalReferenceRaw
attribute [-instance] _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Rescaling.config_haar
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
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

theorem physical_branch_observed_reference {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints (N+1) L)) [SFinite μ]
    (g : Fin G) (flags : Fin (N+1)→Bool) (a : GridAllocation (N+1) K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (extra tag : Fin 3→Fin K) (b : Bool) :
    taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
      taggedReference
        ((physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).compProd
          (physicalPrimaryReference hL g m t r R C S u
            (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
        (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag) =
      ∑i : Fin (N+1), if i∈groupUnion g a then
        ((physicalCellPost (N:=N) L extra tag b) ∘ₖ orderedKernel (uniformBathOrder N) i) ∘ₘ
          (rawPhysicalBranch hL μ g flags a m r R C S s₀ (2*t) u).map
            (fun z ↦ labelBridgePath (N+1) L (2*t) z midpointTime)
        else 0 := by
  classical
  let particle := Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)
  let P := (physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).compProd
    (physicalPrimaryReference hL g m t r R C S u
      (fun i : {i // i∈groupUnion g a} ↦ i.val) extra)
  change taggedPhysicalBathKernel particle b ∘ₘ taggedReference P (physicalTagEvent particle tag)=_
  rw [taggedReference_comp P _ (physicalTagEvent_measurable particle tag)]
  apply Finset.sum_congr rfl
  intro i _
  have hk : (taggedPhysicalBathKernel (K:=K) (M:=M) (G:=G) (L:=L) particle b).comap (Prod.mk i) measurable_prodMk_left=
      (primaryBathKernel b i).comap (physicalFullMidpoint particle) (physicalFullMidpoint_measurable particle) := rfl
  rw [hk]
  have hrange : i∈Set.range particle ↔ i∈groupUnion g a := by
    constructor
    · rintro ⟨j,rfl⟩; exact j.property
    · intro hi; exact ⟨⟨i,hi⟩,rfl⟩
  by_cases hi : i∈groupUnion g a
  · rw [ite_eq_left hi]
    have he : physicalTagEvent (M:=M) (G:=G) (L:=L) particle tag i=(physicalFullMidpoint particle) ⁻¹'
        ((fun F : Option (Fin (N+1))→Torus L ↦ F (some i)) ⁻¹' centeredCell L (gridCenter L tag)) := by
      ext z
      simp only [physicalTagEvent,Set.mem_ofPred_eq,hrange,hi,true_and,Set.mem_preimage]
    rw [he,comp_comap_map,←Measure.restrict_map (physicalFullMidpoint_measurable particle)
      ((centeredCell_measurable L _).preimage (measurable_pi_apply (some i)))]
    change primaryBathKernel b i ∘ₘ (P.map (physicalFullMidpoint particle)).restrict _=_
    dsimp only [P,particle]
    rw [physicalBranch_primary_midpoint hL hK h50 μ g flags a m r R C S s₀ t u extra]
    exact primaryBath_cell_reference _ (cellPointReference L extra) b i _ (centeredCell_measurable L _)
  · rw [ite_eq_right hi]
    have he : physicalTagEvent (M:=M) (G:=G) (L:=L) particle tag i=∅ := by
      ext z; simp [physicalTagEvent,hrange,hi]
    simp [he]

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {Ω A G Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G]
lemma sum_allocatedTagLaw_le_ae (μ : Measure Ω) (I : G→Ω→Finset A)
    (hI : ∀g i,MeasurableSet {ω | i∈I g ω}) (κ : A→Kernel Ω Y)
    (hd : ∀ᵐω ∂μ, ∀g g',g≠g' → Disjoint (I g ω) (I g' ω)) :
    ∑g,allocatedTagLaw μ I κ g ≤ ∑i,κ i ∘ₘ μ := by
  classical
  apply Measure.le_iff.2
  intro s hs
  have hbind (i : A) (ν : Measure Ω) : (κ i ∘ₘ ν) s=∫⁻ω,κ i ω s ∂ν :=
    Measure.bind_apply hs (κ i).aemeasurable
  simp only [allocatedTagLaw,Measure.finsetSum_apply,hbind]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  simp_rw [←lintegral_indicator (hI _ i)]
  rw [←lintegral_finsetSum _ (fun g _ ↦ ((κ i).measurable_coe hs).indicator (hI g i))]
  apply lintegral_mono_ae
  filter_upwards [hd] with ω hdω
  let T : Finset G := Finset.univ.filter (fun g ↦ i∈I g ω)
  have hT : T.card≤1 := by
    rw [Finset.card_le_one]
    intro g hg g' hg'
    by_contra h
    exact Finset.disjoint_left.mp (hdω g g' h) (Finset.mem_filter.mp hg).2 (Finset.mem_filter.mp hg').2
  calc
    (∑g,({ω | i∈I g ω}.indicator (fun ω ↦ κ i ω s)) ω)=∑g∈T,κ i ω s := by
      change _=∑g∈Finset.univ.filter (fun g ↦ i∈I g ω),κ i ω s
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro g _
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    _ ≤ κ i ω s := by
      rw [Finset.sum_const]
      simpa only [one_nsmul] using nsmul_le_nsmul_left (show 0≤κ i ω s from bot_le) hT
end HardSphere.Comparison
namespace HardSphere.Groups
open Sampling Wiener PathCutoff Comparison
attribute [local instance] Classical.propDecidable

lemma groupAt_mem_eligible {N K M G : ℕ} {L : Length}
    (m : ℕ) (r R C S s₀ : ℝ) (u : Time) (ω : ConfigurationPath N L)
    (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (g : Fin G) (v : Fin 3→Fin K) : groupAt g a v⊆eligibleList m r R C S s₀ u v ω := by
  intro i hi
  cases he : a v with
  | none => simp [groupAt,he] at hi
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hi
    obtain ⟨k,rfl⟩ := hi
    exact allocationPMF_support _ _ _ (ha v) f he _

lemma physical_groups_disjoint {N K M G : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (ω : ConfigurationPath N L) (a : GridAllocation N K (G*M))
    (ha : ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) (G*M)).support)
    (g h : Fin G) (hgh : g≠h) : Disjoint (groupUnion g a) (groupUnion h a) := by
  apply Finset.disjoint_left.mpr
  intro i hig hih
  obtain ⟨v,_,hiv⟩ := Finset.mem_biUnion.mp hig
  obtain ⟨w,_,hiw⟩ := Finset.mem_biUnion.mp hih
  have hv := groupAt_mem_eligible m r R C S s₀ u ω a ha g v hiv
  have hw := groupAt_mem_eligible m r R C S s₀ u ω a ha h w hiw
  have hvw : v=w := by
    by_contra hn
    exact Finset.disjoint_left.mp (eligibleList_disjoint hL hK m r R C S s₀ u ω hn) hv hw
  rw [←hvw] at hiw
  cases he : a v with
  | none => simp [groupAt,he] at hiv
  | some f =>
    simp only [groupAt,he,Finset.mem_image,Finset.mem_univ,true_and] at hiv hiw
    obtain ⟨k,hk⟩ := hiv
    obtain ⟨l,hl⟩ := hiw
    exact groupPosition_disjoint M G g h hgh k l (f.injective (hk.trans hl.symm))

lemma physicalAllocation_supported_ae {N K : ℕ} {L : Length}
    (m total : ℕ) (r R C S s₀ : ℝ) (u : Time) (ω : ConfigurationPath N L) :
    ∀ᵐa ∂physicalAllocationKernel (K:=K) m total r R C S s₀ u ω,
      ∀v,a v∈(allocationPMF (eligibleList m r R C S s₀ u v ω) total).support := by
  change ∀ᵐa ∂Measure.pi (fun v ↦ (allocationPMF (eligibleList m r R C S s₀ u v ω) total).toMeasure), _
  apply ae_all_iff.mpr
  intro v
  exact (MeasureTheory.measurePreserving_eval
    (fun w ↦ (allocationPMF (eligibleList m r R C S s₀ u w ω) total).toMeasure) v).quasiMeasurePreserving.tendsto_ae
      (allocation_support_ae _ _)

theorem sum_physical_group_tags_le {N K M G : ℕ} {L : Length}
    {Y : Type*} [MeasurableSpace Y]
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (m : ℕ) (r R C S s₀ : ℝ) (u : Time)
    (μ : Measure (ConfigurationPath N L)) [SFinite μ]
    (κ : Fin N→Kernel (ConfigurationPath N L×GridAllocation N K (G*M)) Y) :
    (∑g,allocatedTagLaw (μ.compProd (physicalAllocationKernel m (G*M) r R C S s₀ u))
      (fun g p ↦ groupUnion g p.2) κ g) ≤
      ∑i,κ i ∘ₘ μ.compProd (physicalAllocationKernel m (G*M) r R C S s₀ u) := by
  apply sum_allocatedTagLaw_le_ae
  · intro g i
    exact ((measurable_of_countable (fun a : GridAllocation N K (G*M) ↦ i∈groupUnion g a)).comp measurable_snd).setOf
  · apply Measure.ae_compProd_of_ae_ae
      (((measurable_of_countable (fun a : GridAllocation N K (G*M) ↦
        ∀g h : Fin G,g≠h→Disjoint (groupUnion g a) (groupUnion h a))).comp measurable_snd).setOf)
    filter_upwards [] with ω
    filter_upwards [physicalAllocation_supported_ae m (G*M) r R C S s₀ u ω] with a ha
    exact fun g h hgh ↦ physical_groups_disjoint hL hK m r R C S s₀ u ω a ha g h hgh

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_AllocatedLinearity
attribute [-instance] _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {Ω A G Y J : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
  [Fintype A] [DecidableEq A] [Fintype G] [DecidableEq G] [Fintype J]
omit [DecidableEq A] [Fintype G] [DecidableEq G] in
lemma allocatedTagLaw_sum (μ : J→Measure Ω) (I : G→Ω→Finset A)
    (hI : ∀g i,MeasurableSet {ω | i∈I g ω}) (κ : A→Kernel Ω Y) (g : G) :
    allocatedTagLaw (∑j,μ j) I κ g=∑j,allocatedTagLaw (μ j) I κ g := by
  classical
  apply Measure.ext
  intro s hs
  simp only [allocatedTagLaw,Measure.finsetSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Measure.bind_apply hs (κ i).aemeasurable,←lintegral_indicator (hI g i)]
  exact lintegral_finsetSum_measure _ _ _
end HardSphere.Comparison
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable
attribute [local instance] Comparison.permBathSpace Comparison.permBathSingleton

lemma physical_branch_allocated_reference {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (μ : Measure (BridgeEndpoints (N+1) L)) [SFinite μ]
    (g : Fin G) (flags : Fin (N+1)→Bool) (a : GridAllocation (N+1) K (G*M))
    (m : ℕ) (r R C S s₀ t : ℝ) (u : Time) (extra tag : Fin 3→Fin K) (b : Bool) :
    taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
      taggedReference
        ((physicalBranchLaw hL μ g flags a m r R C S s₀ (2*t) u).compProd
          (physicalPrimaryReference hL g m t r R C S u
            (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
        (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag) =
    allocatedTagLaw ((rawPhysicalBranch hL μ g flags a m r R C S s₀ (2*t) u).map
      (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)))
      (fun g p ↦ groupUnion g p.2) (physicalRead L extra tag b) g := by
  classical
  rw [physical_branch_observed_reference hL hK h50]
  unfold allocatedTagLaw
  apply Finset.sum_congr rfl
  intro i _
  have hmap : Measurable (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)) :=
    (labelBridgePath_measurable (N+1) L (2*t)).prodMk measurable_const
  have hA : MeasurableSet {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2} :=
    ((measurable_of_countable (fun a ↦ i∈groupUnion g a)).comp measurable_snd).setOf
  rw [Measure.restrict_map hmap hA]
  by_cases hi : i∈groupUnion g a
  · rw [ite_eq_left hi]
    have he : (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)) ⁻¹'
        {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2}=univ := by
      ext z; simp [hi]
    rw [he,Measure.restrict_univ,physicalRead,comp_comap_map,
      Measure.map_map (show Measurable (fun p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) ↦ p.1 midpointTime) from
        (continuous_eval_const midpointTime).measurable.comp measurable_fst) hmap]
    rfl
  · rw [ite_eq_right hi]
    have he : (fun z ↦ (labelBridgePath (N+1) L (2*t) z,a)) ⁻¹'
        {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2}=∅ := by
      ext z; simp [hi]
    simp [he]

theorem physical_branch_reference_sum {N K M G : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    (ψ : Jet (N+1) L) (g : Fin G) (m : ℕ) (r R C S s₀ t : ℝ) (u : Time)
    (extra tag : Fin 3→Fin K) (b : Bool) :
    (∑flags,∑a : GridAllocation (N+1) K (G*M),
      taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
        taggedReference
          ((physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g flags a m r R C S s₀ (2*t) u).compProd
            (physicalPrimaryReference hL g m t r R C S u
              (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
          (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag)) =
    allocatedTagLaw ((groundPathLaw (N+1) L r (2*t) ψ).compProd
      (physicalAllocationKernel m (G*M) r R C S s₀ u))
      (fun g p ↦ groupUnion g p.2) (physicalRead L extra tag b) g := by
  have hI : ∀g : Fin G,∀i : Fin (N+1),MeasurableSet
      {p : ConfigurationPath (N+1) L×GridAllocation (N+1) K (G*M) | i∈groupUnion g p.2} := by
    intro g i
    exact ((measurable_of_countable (fun a ↦ i∈groupUnion g a)).comp measurable_snd).setOf
  simp_rw [physical_branch_allocated_reference hL hK h50]
  simp_rw [←allocatedTagLaw_sum _ _ hI]
  congr 1
  exact genuine_ground_allocated_raw hL hK ψ m (G*M) r R C S s₀ (2*t) u

theorem physical_allocated_reference_le {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (R C S s₀ t : ℝ) (ht : 0≤t) (u : Time)
    (extra tag : Fin 3→Fin K) (b : Bool) :
    (∑g : Fin G,allocatedTagLaw ((groundPathLaw (N+1) L r (2*t) ψ).compProd
      (physicalAllocationKernel m (G*M) r R C S s₀ u))
      (fun g p ↦ groupUnion g p.2) (physicalRead L extra tag b) g) ≤
    (N+1) • (physicalCellPost L extra tag b ∘ₘ
      (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2)))) := by
  have hT : 0≤2*t := mul_nonneg (by norm_num) ht
  let := hψ.groundPathLaw_probability hT
  refine (sum_physical_group_tags_le hL hK m r R C S s₀ u _ _).trans ?_
  simp_rw [physicalRead,comp_comap_map,allocation_slice_law hψ (2*t) hT midpointTime]
  exact le_of_eq (all_tags_reference ψ hψ.2.1 hψ.2.2.1 (uniformBathOrder N) (physicalCellPost L extra tag b))

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

theorem physicalCellPost_le {N K : ℕ} [NeZero K] {L : Length} (hL : 1≤L.val)
    (extra tag : Fin 3→Fin K) (b : Bool) (P : Measure (Torus L×Configuration N L)) [SFinite P] :
    physicalCellPost L extra tag b ∘ₘ P≤physicalCellVolumePost L extra tag b ∘ₘ P := by
  rw [physicalCellPost,physicalCellVolumePost,←Measure.map_comp _ _ (cellObservation_measurable b),
    ←Measure.map_comp _ _ (cellObservation_measurable b)]
  apply Measure.map_mono _ (cellObservation_measurable b)
  rw [cellExtraKernel,cellExtraKernel,restrict_kernel_comp,restrict_kernel_comp,
    ←Measure.compProd_eq_comp_prod,←Measure.compProd_eq_comp_prod,
    Measure.compProd_const,Measure.compProd_const,Measure.restrict_univ]
  apply Measure.restrict_mono_measure
  exact Measure.prod_mono le_rfl (cellPathReference_midpoint_le hL extra)

theorem physical_all_references_le {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (R C S s₀ t : ℝ) (ht : 0≤t) (u : Time)
    (extra tag : Fin 3→Fin K) (b : Bool) :
    (∑g : Fin G,∑flags,∑a : GridAllocation (N+1) K (G*M),
      taggedPhysicalBathKernel (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) b ∘ₘ
        taggedReference
          ((physicalBranchLaw hL (endpointWeightedBase ψ (2*t)) g flags a m r R C S s₀ (2*t) u).compProd
            (physicalPrimaryReference hL g m t r R C S u
              (fun i : {i // i∈groupUnion g a} ↦ i.val) extra))
          (physicalTagEvent (Function.Embedding.subtype (fun i ↦ i∈groupUnion g a)) tag)) ≤
    (N+1) • (physicalCellVolumePost L extra tag b ∘ₘ
      (((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2)))) := by
  simp_rw [physical_branch_reference_sum hL hK h50]
  exact (physical_allocated_reference_le hL hK hψ m R C S s₀ t ht u extra tag b).trans
    (nsmul_le_nsmul_right (physicalCellPost_le (by linarith) extra tag b _) (N+1))

end HardSphere.Groups
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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_Affinity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
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

namespace HardSphere.Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_sqrt {f : α → ℝ} (hf : Integrable f μ) (hf0 : 0 ≤ᵐ[μ] f) :
    MemLp (fun x ↦ Real.sqrt (f x)) 2 μ := by
  refine (memLp_two_iff_integrable_sq (Real.continuous_sqrt.comp_aestronglyMeasurable hf.1)).2 ?_
  apply hf.congr
  filter_upwards [hf0] with x hx
  exact (Real.sq_sqrt hx).symm

lemma affinity_nonneg (p q : α → ℝ) : 0 ≤ affinity μ p q := by
  exact integral_nonneg fun x ↦ mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma affinity_integrable {p q : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : 0 ≤ᵐ[μ] p) (hq0 : 0 ≤ᵐ[μ] q) :
    Integrable (fun x ↦ Real.sqrt (p x) * Real.sqrt (q x)) μ := by
  exact (memLp_sqrt hp hp0).integrable_mul (memLp_sqrt hq hq0)

lemma real_rnDeriv_chain {ν P ξ : Measure α}
    [IsFiniteMeasure ν] [IsFiniteMeasure P] [IsFiniteMeasure ξ] (hνP : ν ≪ P) :
    (fun x ↦ (ν.rnDeriv P x).toReal * (P.rnDeriv ξ x).toReal) =ᵐ[ξ]
      (fun x ↦ (ν.rnDeriv ξ x).toReal) := by
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := ξ) hνP] with x hx
  exact ENNReal.toReal_mul.symm.trans (congrArg ENNReal.toReal hx)

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_AffinityNormalization
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {α : Type*} [MeasurableSpace α]
lemma measureAffinity_eq_dominated (P Q ξ : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure ξ]
    (hP : P≪ξ) (hQ : Q≪ξ) :
    measureAffinity P Q=affinity ξ (fun x ↦ (P.rnDeriv ξ x).toReal)
      (fun x ↦ (Q.rnDeriv ξ x).toReal) := by
  have hsum : P+Q≪ξ := by
    intro s hs
    simp only [Measure.add_apply,hP hs,hQ hs,add_zero]
  have hp : P≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  unfold measureAffinity affinity
  rw [←integral_toReal_rnDeriv_mul hsum]
  apply integral_congr_ae
  filter_upwards [real_rnDeriv_chain (ξ:=ξ) hp,real_rnDeriv_chain (ξ:=ξ) hq] with x hx hy
  rw [←hx,←hy,Real.sqrt_mul ENNReal.toReal_nonneg,Real.sqrt_mul ENNReal.toReal_nonneg]
  have hsq := Real.sq_sqrt (show 0≤((P+Q).rnDeriv ξ x).toReal from ENNReal.toReal_nonneg)
  nth_rw 1 [←hsq]
  ring

lemma affinity_finset_sum {ι : Type*} (s : Finset ι) (μ : Measure α)
    (p q : ι→α→ℝ) (hp : ∀i∈s,Integrable (p i) μ) (hq : ∀i∈s,Integrable (q i) μ)
    (hp0 : ∀i x,0≤p i x) (hq0 : ∀i x,0≤q i x) :
    (∑i∈s,affinity μ (p i) (q i))≤
      affinity μ (fun x ↦ ∑i∈s,p i x) (fun x ↦ ∑i∈s,q i x) := by
  unfold affinity
  rw [←integral_finsetSum s (fun i hi ↦ affinity_integrable (hp i hi) (hq i hi)
    (Eventually.of_forall (hp0 i)) (Eventually.of_forall (hq0 i)))]
  apply integral_mono
  · exact integrable_finsetSum _ (fun i hi ↦ affinity_integrable (hp i hi) (hq i hi)
      (Eventually.of_forall (hp0 i)) (Eventually.of_forall (hq0 i)))
  · exact affinity_integrable (integrable_finsetSum _ hp) (integrable_finsetSum _ hq)
      (Eventually.of_forall (fun x ↦ Finset.sum_nonneg (fun i _ ↦ hp0 i x)))
      (Eventually.of_forall (fun x ↦ Finset.sum_nonneg (fun i _ ↦ hq0 i x)))
  · intro x
    exact Real.sum_sqrt_mul_sqrt_le s (fun i ↦ hp0 i x) (fun i ↦ hq0 i x)

lemma rnDeriv_real_mono (P Q ξ : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    [IsFiniteMeasure ξ] (h : P≤Q) :
    (fun x ↦ (P.rnDeriv ξ x).toReal)≤ᵐ[ξ](fun x ↦ (Q.rnDeriv ξ x).toReal) := by
  have he := Measure.sub_add_cancel_of_le h
  have hh := Measure.rnDeriv_add (Q-P) P ξ
  rw [he] at hh
  filter_upwards [hh,Measure.rnDeriv_lt_top P ξ,Measure.rnDeriv_lt_top (Q-P) ξ] with x hx hp hq
  rw [hx,Pi.add_apply,ENNReal.toReal_add hq.ne hp.ne]
  exact le_add_of_nonneg_left ENNReal.toReal_nonneg

lemma measureAffinity_mono (P Q P' Q' : Measure α)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] [IsFiniteMeasure P'] [IsFiniteMeasure Q']
    (hP : P≤P') (hQ : Q≤Q') : measureAffinity P Q ≤ measureAffinity P' Q' := by
  have hP' : P'≪P'+Q' := Measure.AbsolutelyContinuous.rfl.add_right Q'
  have hQ' : Q'≪P'+Q' := Measure.AbsolutelyContinuous.rfl.add_right' P'
  have hp := (Measure.absolutelyContinuous_of_le hP).trans hP'
  have hq := (Measure.absolutelyContinuous_of_le hQ).trans hQ'
  rw [measureAffinity_eq_dominated P Q (P'+Q') hp hq]
  unfold measureAffinity affinity
  apply integral_mono_ae
  · exact affinity_integrable Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
  · exact affinity_integrable Measure.integrable_toReal_rnDeriv Measure.integrable_toReal_rnDeriv
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
      (Eventually.of_forall (fun _ ↦ ENNReal.toReal_nonneg))
  · filter_upwards [rnDeriv_real_mono P P' (P'+Q') hP,rnDeriv_real_mono Q Q' (P'+Q') hQ] with x hx hy
    exact mul_le_mul (Real.sqrt_le_sqrt hx) (Real.sqrt_le_sqrt hy)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma rnDeriv_real_finset_sum {ι : Type*} (s : Finset ι) (P : ι→Measure α)
    (ξ : Measure α) [∀i,IsFiniteMeasure (P i)] [IsFiniteMeasure ξ] :
    (fun x ↦ ((∑i∈s,P i).rnDeriv ξ x).toReal)=ᵐ[ξ]
      (fun x ↦ ∑i∈s,((P i).rnDeriv ξ x).toReal) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Measure.rnDeriv_zero ξ] with x hx
    simp [hx]
  | @insert i s hi hs =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Measure.rnDeriv_add (P i) (∑j∈s,P j) ξ,hs,
      Measure.rnDeriv_lt_top (P i) ξ,Measure.rnDeriv_lt_top (∑j∈s,P j) ξ] with x hx hy ha hb
    rw [hx,Pi.add_apply,ENNReal.toReal_add ha.ne hb.ne,hy]

lemma measureAffinity_finset_sum {ι : Type*} (s : Finset ι) (P Q : ι→Measure α)
    [∀i,IsFiniteMeasure (P i)] [∀i,IsFiniteMeasure (Q i)] :
    (∑i∈s,measureAffinity (P i) (Q i)) ≤ measureAffinity (∑i∈s,P i) (∑i∈s,Q i) := by
  let ξ := (∑i∈s,P i)+(∑i∈s,Q i)
  have hsP : (∑i∈s,P i)≪ξ := Measure.AbsolutelyContinuous.rfl.add_right _
  have hsQ : (∑i∈s,Q i)≪ξ := Measure.AbsolutelyContinuous.rfl.add_right' _
  have hp : ∀i∈s,P i≪ξ := fun i hi ↦
    (Measure.absolutelyContinuous_of_le (Finset.single_le_sum (fun _ _ ↦ bot_le) hi)).trans hsP
  have hq : ∀i∈s,Q i≪ξ := fun i hi ↦
    (Measure.absolutelyContinuous_of_le (Finset.single_le_sum (fun _ _ ↦ bot_le) hi)).trans hsQ
  calc
    _ = ∑i∈s,affinity ξ (fun x ↦ ((P i).rnDeriv ξ x).toReal)
        (fun x ↦ ((Q i).rnDeriv ξ x).toReal) := Finset.sum_congr rfl
      (fun i hi ↦ measureAffinity_eq_dominated _ _ _ (hp i hi) (hq i hi))
    _ ≤ affinity ξ (fun x ↦ ∑i∈s,((P i).rnDeriv ξ x).toReal)
        (fun x ↦ ∑i∈s,((Q i).rnDeriv ξ x).toReal) :=
      affinity_finset_sum s ξ _ _ (fun _ _ ↦ Measure.integrable_toReal_rnDeriv)
        (fun _ _ ↦ Measure.integrable_toReal_rnDeriv)
        (fun _ _ ↦ ENNReal.toReal_nonneg) (fun _ _ ↦ ENNReal.toReal_nonneg)
    _ = _ := by
      rw [measureAffinity_eq_dominated _ _ ξ hsP hsQ]
      unfold affinity
      apply integral_congr_ae
      filter_upwards [rnDeriv_real_finset_sum s P ξ,rnDeriv_real_finset_sum s Q ξ] with x hx hy
      rw [hx,hy]

lemma measureAffinity_smul (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (c : ℝ) (hc : 0 ≤ c) :
    measureAffinity (ENNReal.ofReal c • P) (ENNReal.ofReal c • Q)=c*measureAffinity P Q := by
  let := P.smul_finite (c:=ENNReal.ofReal c) ENNReal.ofReal_ne_top
  let := Q.smul_finite (c:=ENNReal.ofReal c) ENNReal.ofReal_ne_top
  have hp : P≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right Q
  have hq : Q≪P+Q := Measure.AbsolutelyContinuous.rfl.add_right' P
  rw [measureAffinity_eq_dominated _ _ (P+Q) (hp.smul_left _) (hq.smul_left _)]
  unfold measureAffinity affinity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_smul_left_of_ne_top P (P+Q) ENNReal.ofReal_ne_top,
    Measure.rnDeriv_smul_left_of_ne_top Q (P+Q) ENNReal.ofReal_ne_top] with x hx hy
  rw [hx,hy,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,
    ENNReal.toReal_mul,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,
    Real.sqrt_mul hc,Real.sqrt_mul hc]
  have hs := Real.sq_sqrt hc
  calc
    _ = (Real.sqrt c)^2*(Real.sqrt ((P.rnDeriv (P+Q) x).toReal)*
        Real.sqrt ((Q.rnDeriv (P+Q) x).toReal)) := by ring
    _ = _ := by rw [hs]

end HardSphere.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_CellAffinity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {α : Type*} [MeasurableSpace α]
lemma affinity_withDensity_real (μ : Measure α) [IsFiniteMeasure μ]
    (p q : α→ℝ) (hp : Integrable p μ) (hq : Integrable q μ)
    (hp0 : ∀ᵐx ∂μ,0≤p x) (hq0 : ∀ᵐx ∂μ,0≤q x) :
    measureAffinity (μ.withDensity fun x ↦ ENNReal.ofReal (p x))
      (μ.withDensity fun x ↦ ENNReal.ofReal (q x))=affinity μ p q := by
  let := isFiniteMeasure_withDensity_ofReal hp.2
  let := isFiniteMeasure_withDensity_ofReal hq.2
  rw [measureAffinity_eq_dominated _ _ μ (withDensity_absolutelyContinuous _ _) (withDensity_absolutelyContinuous _ _)]
  unfold affinity
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_withDensity₀ μ hp.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
    Measure.rnDeriv_withDensity₀ μ hq.aestronglyMeasurable.aemeasurable.ennreal_ofReal,hp0,hq0] with x hx hy hp' hq'
  rw [hx,hy,ENNReal.toReal_ofReal hp',ENNReal.toReal_ofReal hq']

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
lemma swapLast_preserving :
    MeasurePreserving (fun p : (Y×X)×X ↦ ((p.1.1,p.2),p.1.2))
      ((ν.prod μ).prod μ) ((ν.prod μ).prod μ) := by
  have h := (measurePreserving_prodAssoc ν μ μ).symm.comp
    (((MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ:=μ) (ν:=μ))).comp
      (measurePreserving_prodAssoc ν μ μ))
  exact h

lemma full_affinity_square (f : Y×X→ℝ) (hf : MemLp f 2 (ν.prod μ))
    (hf0 : ∀p,0≤f p) (V : ℝ) (hV : 0≤V) :
    measureAffinity
      (((ν.prod μ).prod μ).withDensity fun p ↦ ENNReal.ofReal (V*f p.1^2))
      (((ν.prod μ).prod μ).withDensity fun p ↦ ENNReal.ofReal (V*f (p.1.1,p.2)^2))=
      V*∫Y,(∫x,f (Y,x) ∂μ)^2 ∂ν := by
  have h₁ := hf.comp_fst μ
  have h₂ : MemLp (fun p : (Y×X)×X ↦ f (p.1.1,p.2)) 2 ((ν.prod μ).prod μ) :=
    h₁.comp_measurePreserving (swapLast_preserving μ ν)
  have hi₁ : Integrable (fun p : (Y×X)×X ↦ V*f p.1^2) ((ν.prod μ).prod μ) :=
    ((memLp_two_iff_integrable_sq h₁.aestronglyMeasurable).1 h₁).const_mul V
  have hi₂ : Integrable (fun p : (Y×X)×X ↦ V*f (p.1.1,p.2)^2) ((ν.prod μ).prod μ) :=
    ((memLp_two_iff_integrable_sq h₂.aestronglyMeasurable).1 h₂).const_mul V
  rw [affinity_withDensity_real _ _ _ hi₁ hi₂
    (Eventually.of_forall fun _ ↦ mul_nonneg hV (sq_nonneg _))
    (Eventually.of_forall fun _ ↦ mul_nonneg hV (sq_nonneg _))]
  unfold affinity
  have he : (fun p : (Y×X)×X ↦ Real.sqrt (V*f p.1^2)*Real.sqrt (V*f (p.1.1,p.2)^2))=
      (fun p ↦ V*(f p.1*f (p.1.1,p.2))) := by
    funext p
    rw [Real.sqrt_mul hV,Real.sqrt_mul hV,Real.sqrt_sq (hf0 _),Real.sqrt_sq (hf0 _)]
    have hh := Real.sq_sqrt hV
    calc
      _ = (Real.sqrt V)^2*(f p.1*f (p.1.1,p.2)) := by ring
      _ = _ := by rw [hh]
  rw [he,integral_const_mul]
  congr 1
  have hprod := h₁.integrable_mul h₂
  have hA := (measurePreserving_prodAssoc ν μ μ).symm.integral_comp
    (MeasurableEquiv.prodAssoc (α:=Y) (β:=X) (γ:=X)).symm.measurableEmbedding
    (fun p : (Y×X)×X ↦ f p.1*f (p.1.1,p.2))
  rw [←hA]
  rw [integral_prod]
  · apply integral_congr_ae
    exact Eventually.of_forall fun Y ↦ by
      simpa [sq, MeasurableEquiv.prodAssoc] using (integral_prod_mul (μ:=μ) (ν:=μ) (fun x ↦ f (Y,x)) (fun x ↦ f (Y,x)))
  · have hi : Integrable (fun p : (Y×X)×X ↦ f p.1*f (p.1.1,p.2))
        ((ν.prod (μ.prod μ)).map MeasurableEquiv.prodAssoc.symm) := by
      rw [(measurePreserving_prodAssoc ν μ μ).symm.map_eq]
      exact hprod
    apply hi.comp_measurable
    exact (measurePreserving_prodAssoc ν μ μ).symm.measurable

end HardSphere.Comparison

end

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]

lemma sum_restrict_partition (μ : Measure α) (cell : α→ι)
    (hcell : ∀i,MeasurableSet {x | cell x=i}) :
    (∑i,μ.restrict {x | cell x=i})=μ := by
  have hd : Pairwise (fun i j ↦ Disjoint {x | cell x=i} {x | cell x=j}) := by
    intro i j hij
    exact Set.disjoint_left.mpr (fun x hi hj ↦ hij (hi.symm.trans hj))
  have hu : (⋃i,{x | cell x=i})=univ := by ext x; simp
  rw [←Measure.sum_fintype,←Measure.restrict_iUnion hd hcell,hu,Measure.restrict_univ]

end HardSphere.Comparison

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PhysicalAffinity
attribute [-instance] _root_.OAI.HardSphere.Groups.physicalObservedReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.retainedTaggedPhysicalBath_markov _root_.OAI.HardSphere.Rescaling.config_haar
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

lemma measureAffinity_map_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X≃ᵐY) (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    measureAffinity (P.map e) (Q.map e)=measureAffinity P Q := by
  unfold measureAffinity affinity
  rw [←Measure.map_add _ _ e.measurable,e.measurableEmbedding.integral_map]
  apply integral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map P (P+Q),e.measurableEmbedding.rnDeriv_map Q (P+Q)] with x hx hy
  rw [hx,hy]

end HardSphere.Comparison

namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital

lemma physical_cell_posts_sum {N K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1 ≤ K) (b : Bool)
    (P : Measure (Torus L×Configuration N L)) [SFinite P] :
    (∑tag : Fin 3→Fin K,∑extra : Fin 3→Fin K,
      physicalCellVolumePost L extra tag b ∘ₘ P)=
      (P.prod volume).map (cellObservation b) := by
  simp_rw [physicalCellVolumePost,←Measure.map_comp _ _ (cellObservation_measurable b),
    cellExtraKernel_comp _ volume _ _ (centeredCell_measurable L _) (centeredCell_measurable L _)]
  simp_rw [←Measure.map_finset_sum' (cellObservation_measurable b).aemeasurable]
  congr 1
  have he (tag extra : Fin 3→Fin K) :
      {p : (Torus L×Configuration N L)×Torus L |
        p.1.1∈centeredCell L (gridCenter L tag) ∧ p.2∈centeredCell L (gridCenter L extra)}=
      {p | (gridHome hL p.1.1,gridHome hL p.2)=(tag,extra)} := by
    ext p
    simp only [Set.mem_ofPred_eq,Prod.mk.injEq,gridHome_eq_iff hL hK]
  simp_rw [he]
  rw [←Fintype.sum_prod_type (fun ij : (Fin 3→Fin K)×(Fin 3→Fin K) ↦
    (P.prod volume).restrict {p | (gridHome hL p.1.1,gridHome hL p.2)=ij})]
  apply sum_restrict_partition
  intro i
  exact (((gridHome_measurable hL).comp (measurable_fst.comp measurable_fst)).prodMk
    ((gridHome_measurable hL).comp measurable_snd)) (measurableSet_singleton i)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_PhysicalOrbitalReference
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
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma tagBathSwap_preserving (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] :
    MeasurePreserving (tagBathSwapEquiv (X:=X) (Y:=Y)) ((μ.prod ν).prod μ) ((ν.prod μ).prod μ) :=
  (Measure.measurePreserving_swap (μ:=μ) (ν:=ν)).prod (MeasurePreserving.id μ)

lemma physical_unrestricted_affinity {n : ℕ} (μ : Measure X) (ν : Measure (Fin n→X))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : (Fin n→X)×X→ℝ) (hfm : Measurable f) (hf : MemLp f 2 (ν.prod μ))
    (hf0 : ∀p,0 ≤ f p) :
    let P := ((μ.prod ν).withDensity (fun p ↦ ENNReal.ofReal (f (p.2,p.1)^2))).prod μ
    measureAffinity (P.map (cellObservation true)) (P.map (cellObservation false))=
      ∫Y,(∫x,f (Y,x) ∂μ)^2 ∂ν := by
  dsimp only
  let P := ((μ.prod ν).withDensity (fun p ↦ ENNReal.ofReal (f (p.2,p.1)^2))).prod μ
  let ξ := (ν.prod μ).prod μ
  let g₁ := fun p : ((Fin n→X)×X)×X ↦ ENNReal.ofReal (f p.1^2)
  let g₂ := fun p : ((Fin n→X)×X)×X ↦ ENNReal.ofReal (f (p.1.1,p.2)^2)
  have hg₁ : Measurable g₁ := ((hfm.comp measurable_fst).pow_const 2).ennreal_ofReal
  have hg₂ : Measurable g₂ := ((hfm.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).pow_const 2).ennreal_ofReal
  have hD : P.map tagBathSwapEquiv=ξ.withDensity g₁ := by
    dsimp only [P]
    have hρ : Measurable (fun p : X×(Fin n→X) ↦ ENNReal.ofReal (f (p.2,p.1)^2)) := by fun_prop
    rw [prod_withDensity_left hρ]
    change (((μ.prod ν).prod μ).withDensity (g₁∘tagBathSwapEquiv)).map tagBathSwapEquiv=ξ.withDensity g₁
    rw [map_density_comp _ _ tagBathSwapEquiv.measurable g₁ hg₁,(tagBathSwap_preserving μ ν).map_eq]
  have hS : (ξ.withDensity g₁).map orbitalSwapEquiv=ξ.withDensity g₂ := by
    change (ξ.withDensity (g₂∘orbitalSwapEquiv)).map orbitalSwapEquiv=ξ.withDensity g₂
    rw [map_density_comp _ _ orbitalSwapEquiv.measurable g₂ hg₂]
    change ((ξ.map (fun p ↦ ((p.1.1,p.2),p.1.2))).withDensity g₂)=_
    rw [(swapLast_preserving μ ν).map_eq]
  have he₁ : P.map (cellObservation true)=(ξ.withDensity g₁).map orbitalObservationEquiv := by
    rw [←hD,Measure.map_map orbitalObservationEquiv.measurable tagBathSwapEquiv.measurable]
    rfl
  have he₂ : P.map (cellObservation false)=(ξ.withDensity g₂).map orbitalObservationEquiv := by
    rw [←hS,←hD,Measure.map_map orbitalSwapEquiv.measurable tagBathSwapEquiv.measurable,
      Measure.map_map orbitalObservationEquiv.measurable (orbitalSwapEquiv.measurable.comp tagBathSwapEquiv.measurable)]
    rfl
  have hi₁ : Integrable (fun p : ((Fin n→X)×X)×X ↦ f p.1^2) ξ :=
    (memLp_two_iff_integrable_sq (hf.comp_fst μ).aestronglyMeasurable).1 (hf.comp_fst μ)
  have hi₂ : Integrable (fun p : ((Fin n→X)×X)×X ↦ f (p.1.1,p.2)^2) ξ := by
    have h := (hf.comp_fst μ).comp_measurePreserving (swapLast_preserving μ ν)
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).1 h
  have : IsFiniteMeasure (ξ.withDensity g₁) := isFiniteMeasure_withDensity_ofReal hi₁.2
  have : IsFiniteMeasure (ξ.withDensity g₂) := isFiniteMeasure_withDensity_ofReal hi₂.2
  change measureAffinity (P.map _) (P.map _)=_
  rw [he₁,he₂,measureAffinity_map_equiv]
  simpa only [one_mul] using full_affinity_square μ ν f hf hf0 1 (by norm_num)

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_Admissible
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalCodeObserver_markov _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalObservedReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace HardSphere.DyadicSkeleton
open HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma current_admissible_card {K : ℕ} [NeZero K] (hK : 400≤K) :
    K^6≤2000*(currentAdmissiblePairs K).card := by
  let m := K/10
  let I := Finset.Icc (K/10+1) (K/8)
  let J := Finset.range (2*m+1)
  let S : Finset (DiscreteTorus K × ℕ × ℕ × ℕ) :=
    Finset.univ ×ˢ (I ×ˢ (J ×ˢ J))
  let f : DiscreteTorus K × ℕ × ℕ × ℕ → DiscreteTorus K × DiscreteTorus K :=
    fun z ↦ (z.1,z.1+![(z.2.1:ZMod K),((z.2.2.1:ℤ)-m:ZMod K),((z.2.2.2:ℤ)-m:ZMod K)])
  have hI (n : ℕ) (hn : n∈I) : K≤10*n ∧ 8*n≤K ∧ n<K ∧ m<n := by
    have hn := Finset.mem_Icc.mp hn
    dsimp [m]
    omega
  have hJ (b : ℕ) (hb : b∈J) : b<K ∧ |(b:ℤ)-m|≤(m:ℤ) := by
    have hb := Finset.mem_range.mp hb
    dsimp [m] at *
    constructor
    · omega
    · rw [abs_le]; constructor <;> omega
  have hsub : S.image f⊆currentAdmissiblePairs K := by
    intro z hz
    obtain ⟨⟨x,n,b,c⟩,hu,rfl⟩ := Finset.mem_image.mp hz
    simp only [S,Finset.mem_product] at hu
    obtain ⟨_,hn,hb,hc⟩ := hu
    have hin := hI n hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,n,hin.1,hin.2.1,![(b:ℤ)-m,(c:ℤ)-m],?_,?_⟩
    · intro j
      fin_cases j
      · exact (hJ b hb).2.trans (by exact_mod_cast hin.2.2.2.le)
      · exact (hJ c hc).2.trans (by exact_mod_cast hin.2.2.2.le)
    · simp [f]
  have hinj : Set.InjOn f (↑S : Set _) := by
    rintro ⟨x,n,b,c⟩ hx ⟨x',n',b',c'⟩ hx' he
    have he₁ : x=x' := congrArg Prod.fst he
    subst x'
    have he₂ : ![(n:ZMod K),((b:ℤ)-m:ZMod K),((c:ℤ)-m:ZMod K)]=
        ![(n':ZMod K),((b':ℤ)-m:ZMod K),((c':ℤ)-m:ZMod K)] :=
      add_left_cancel (congrArg Prod.snd he)
    change (x,n,b,c)∈S at hx
    change (x,n',b',c')∈S at hx'
    simp only [S,Finset.mem_product] at hx hx'
    obtain ⟨_,hn,hb,hc⟩ := hx
    obtain ⟨_,hn',hb',hc'⟩ := hx'
    have hnval := congrArg (fun z : Fin 3 → ZMod K ↦ (z 0).val) he₂
    simp only [Matrix.cons_val_zero,ZMod.val_natCast_of_lt (hI n hn).2.2.1,
      ZMod.val_natCast_of_lt (hI n' hn').2.2.1] at hnval
    have hbeq : (b:ZMod K)=(b':ZMod K) := by
      have h := congrFun he₂ 1
      simpa using h
    have hceq : (c:ZMod K)=(c':ZMod K) := by
      have h := congrFun he₂ 2
      simpa using h
    have hbval := congrArg ZMod.val hbeq
    have hcval := congrArg ZMod.val hceq
    simp only [ZMod.val_natCast_of_lt (hJ b hb).1,ZMod.val_natCast_of_lt (hJ b' hb').1] at hbval
    simp only [ZMod.val_natCast_of_lt (hJ c hc).1,ZMod.val_natCast_of_lt (hJ c' hc').1] at hcval
    simp only [Prod.mk.injEq]
    exact ⟨trivial,hnval,hbval,hcval⟩
  have hcard : S.card≤(currentAdmissiblePairs K).card :=
    (Finset.card_image_iff.mpr hinj).symm.trans_le (Finset.card_le_card hsub)
  have hcardS : S.card=K^3*I.card*J.card^2 := by
    dsimp only [S]
    rw [Finset.card_product,Finset.card_product,Finset.card_product]
    simp [DiscreteTorus,mul_assoc,pow_two]
  have hcardI : K≤50*I.card := by
    dsimp [I]
    rw [Nat.card_Icc]
    omega
  have hcardJ : K≤6*J.card := by
    simp only [J,Finset.card_range,m]
    omega
  rw [hcardS] at hcard
  calc
    K^6=K^3*K*K^2 := by ring
    _ ≤ K^3*(50*I.card)*(6*J.card)^2 := Nat.mul_le_mul
      (Nat.mul_le_mul_left _ hcardI) (Nat.pow_le_pow_left hcardJ 2)
    _ = 1800*(K^3*I.card*J.card^2) := by ring
    _ ≤ 1800*(currentAdmissiblePairs K).card := Nat.mul_le_mul_left _ hcard
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

end HardSphere.DyadicSkeleton
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAffinitySum
attribute [-instance] _root_.OAI.HardSphere.Rescaling.config_haar
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
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma measureAffinity_nsmul {X : Type*} [MeasurableSpace X]
    (P Q : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure Q] (n : ℕ) :
    measureAffinity (n • P) (n • Q)=(n:ℝ)*measureAffinity P Q := by
  have h := measureAffinity_smul P Q (n:ℝ) (Nat.cast_nonneg n)
  rw [ENNReal.ofReal_natCast] at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

lemma affinity_double_sum_bound {X I J : Type*} [MeasurableSpace X] [Fintype I] [Fintype J]
    (A : I→J→Bool→Measure X) (Q : Bool→Measure X) (n : ℕ)
    [∀i j b,IsFiniteMeasure (A i j b)] [∀b,IsFiniteMeasure (Q b)]
    (h : ∀b,(∑i,∑j,A i j b)≤n • Q b) :
    (∑i,∑j,measureAffinity (A i j true) (A i j false))≤(n:ℝ)*measureAffinity (Q true) (Q false) := by
  have hb : (∑i,∑j,measureAffinity (A i j true) (A i j false))≤
      measureAffinity (∑i,∑j,A i j true) (∑i,∑j,A i j false) := by
    refine (Finset.sum_le_sum (fun i _ ↦ measureAffinity_finset_sum Finset.univ (fun j ↦ A i j true) (fun j ↦ A i j false))).trans ?_
    exact measureAffinity_finset_sum Finset.univ (fun i ↦ ∑j,A i j true) (fun i ↦ ∑j,A i j false)
  exact hb.trans ((measureAffinity_mono _ _ _ _ (h true) (h false)).trans_eq (measureAffinity_nsmul _ _ n))

lemma physical_total_posts {N K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (b : Bool)
    (P : Measure (Torus L×Configuration N L)) [SFinite P] :
    (∑ij : DiscreteTorus K×DiscreteTorus K,
      physicalCellVolumePost L (siteIndex (if b then ij.2 else ij.1))
        (siteIndex (if b then ij.1 else ij.2)) b ∘ₘ P)=
      (P.prod volume).map (cellObservation b) := by
  rw [Fintype.sum_prod_type]
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · rw [Finset.sum_comm]
    have he := physical_cell_posts_sum hL hK false P
    rw [←he]
    exact (siteIndexEquiv.sum_comp (fun tag : Fin 3→Fin K ↦
      ∑extra : DiscreteTorus K,physicalCellVolumePost L (siteIndex extra) tag false ∘ₘ P)).trans
      (Finset.sum_congr rfl (fun tag _ ↦ siteIndexEquiv.sum_comp
        (fun extra : Fin 3→Fin K ↦ physicalCellVolumePost L extra tag false ∘ₘ P)))
  · rw [←physical_cell_posts_sum hL hK true P]
    exact (siteIndexEquiv.sum_comp (fun tag : Fin 3→Fin K ↦
      ∑extra : DiscreteTorus K,physicalCellVolumePost L (siteIndex extra) tag true ∘ₘ P)).trans
      (Finset.sum_congr rfl (fun tag _ ↦ siteIndexEquiv.sum_comp
        (fun extra : Fin 3→Fin K ↦ physicalCellVolumePost L extra tag true ∘ₘ P)))

lemma physicalGroupReference_finite {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (x y : DiscreteTorus K) (g : Fin G) (b : Bool) :
    IsFiniteMeasure (physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b) := by
  let (flags : Fin (N+1)→Bool) (a : GridAllocation (N+1) K (G*M)) :=
    physicalBranchLaw_finite hL hK hψ g flags a m R C S s₀ (2*t) (by linarith) u
  unfold physicalGroupReference
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma physical_group_references_le {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (x y : DiscreteTorus K) (b : Bool) :
    (∑g : Fin G,physicalGroupReference (M:=M) (x:=x) (y:=y) hL ψ g m t r R C S s₀ u b)≤
      (N+1) • (physicalCellVolumePost L (siteIndex (if b then y else x))
        (siteIndex (if b then x else y)) b ∘ₘ
        (((volume : Measure (Torus L)).prod volume).withDensity
          (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2)))) := by
  simpa only [physicalGroupReference,physicalObservedReference,physicalTaggedReference,
    branchParticles,Function.Embedding.subtype,Function.Embedding.coeFn_mk] using
    physical_all_references_le (M:=M) (G:=G) hL hK h50 hψ m R C S s₀ t ht u
      (siteIndex (if b then y else x)) (siteIndex (if b then x else y)) b

lemma physical_reference_sum_bound {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time) (b : Bool) :
    (∑ij : DiscreteTorus K×DiscreteTorus K,∑g : Fin G,
      physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u b)≤
      (N+1) • ((((volume : Measure (Torus L)).prod volume).withDensity
        (fun p : Torus L×Configuration N L ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2))).prod volume).map (cellObservation b) := by
  let P : Measure (Torus L×Configuration N L) := (volume.prod volume).withDensity
    (fun p ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2))
  have hf := ((Lp.memLp ψ.1).comp_measurePreserving (cons_preserving (n:=N) L)).norm
  have hf' := hf.comp_measurePreserving (Measure.measurePreserving_swap (μ:=volume) (ν:=volume))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal
    ((memLp_two_iff_integrable_sq hf'.aestronglyMeasurable).1 hf').2
  change _≤(N+1) • (P.prod volume).map (cellObservation b)
  rw [←physical_total_posts hL hK b P,Finset.smul_sum]
  exact Finset.sum_le_sum (fun ij _ ↦ physical_group_references_le hL hK h50 hψ m t R C S s₀ ht u ij.1 ij.2 b)

attribute [local irreducible] physicalGroupReference physicalCellVolumePost

theorem physical_affinity_sum_bound {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time) :
    (∑ij : DiscreteTorus K×DiscreteTorus K,∑g : Fin G,
      measureAffinity (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)) ≤
      (N+1:ℝ)*(∫Y : Configuration N L,(∫x : Torus L,‖ψ.1 (Fin.cons x Y)‖)^2) := by
  classical
  let P : Measure (Torus L×Configuration N L) := (volume.prod volume).withDensity
    (fun p ↦ ENNReal.ofReal (‖ψ.1 (Fin.cons p.1 p.2)‖^2))
  let Q := fun b ↦ (P.prod volume).map (cellObservation b)
  let A := fun ij : DiscreteTorus K×DiscreteTorus K ↦ fun g : Fin G ↦ fun b ↦
    physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u b
  have hm : Measurable (fun p : Configuration N L×Torus L ↦ ‖ψ.1 (Fin.cons p.2 p.1)‖) :=
    ((Lp.stronglyMeasurable ψ.1).measurable.comp (cons_preserving (n:=N) L).measurable).norm
  have hf := ((Lp.memLp ψ.1).comp_measurePreserving (cons_preserving (n:=N) L)).norm
  have hf' := hf.comp_measurePreserving (Measure.measurePreserving_swap (μ:=volume) (ν:=volume))
  let : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal
    ((memLp_two_iff_integrable_sq hf'.aestronglyMeasurable).1 hf').2
  let (ij : DiscreteTorus K×DiscreteTorus K) (g : Fin G) (b : Bool) : IsFiniteMeasure (A ij g b) :=
    physicalGroupReference_finite hL hK hψ m t R C S s₀ ht u ij.1 ij.2 g b
  have hsall (b : Bool) : (∑ij,∑g,A ij g b)≤(N+1) • Q b :=
    physical_reference_sum_bound hL hK h50 hψ m t R C S s₀ ht u b
  have hnorm : measureAffinity (Q true) (Q false)=
      ∫Y : Configuration N L,(∫x : Torus L,‖ψ.1 (Fin.cons x Y)‖)^2 :=
    physical_unrestricted_affinity (n:=N) (volume : Measure (Torus L)) (volume : Measure (Configuration N L))
      (fun p : Configuration N L×Torus L ↦ ‖ψ.1 (Fin.cons p.2 p.1)‖) hm hf (fun _ ↦ norm_nonneg _)
  have hb := affinity_double_sum_bound A Q (N+1) hsall
  simpa only [hnorm,Nat.cast_add,Nat.cast_one] using hb

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice HardSphere.DyadicSkeleton
attribute [local instance] Classical.propDecidable

lemma pair_group_sum_lower {K G : ℕ} (hK : 400≤K) [NeZero K]
    (f : (DiscreteTorus K×DiscreteTorus K)→Fin G→ℝ) {B : ℝ} (hB : 0<B)
    (hf : ∀i g,0≤f i g)
    (hgain : ∀i∈currentAdmissiblePairs K,∀g,1/(8*B)≤f i g) :
    (K:ℝ)^6*(G:ℝ)/(16000*B)≤∑i,∑g,f i g := by
  have hc : (K:ℝ)^6≤2000*((currentAdmissiblePairs K).card:ℝ) := by
    exact_mod_cast current_admissible_card hK
  have hs : ((currentAdmissiblePairs K).card:ℝ)*(G:ℝ)/(8*B)≤
      ∑i∈currentAdmissiblePairs K,∑g,f i g := by
    calc
      _ = ∑i∈currentAdmissiblePairs K,∑g : Fin G,1/(8*B) := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ Finset.sum_le_sum (fun g _ ↦ hgain i hi g))
  refine le_trans ?_ (hs.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ ↦ Finset.sum_nonneg (fun g _ ↦ hf i g))))
  apply (div_le_div_iff₀ (by positivity : 0<16000*B) (by positivity : 0<8*B)).mpr
  have hc' := mul_le_mul_of_nonneg_right hc (by positivity : 0≤(G:ℝ))
  nlinarith

lemma modulus_numeric_gain {V D I ell M B G : ℝ}
    (hV : 0<V) (hD : 0<D) (hell : 0<ell) (hM : 0<M) (hB : 0<B)
    (hG : ell/(8*M)≤G/D) (hbound : V^2*G/(16000*B)≤(D*V)*I) :
    ell/(128000*M*B)≤I/V := by
  calc
    _ = (ell/(8*M))/(16000*B) := by field_simp; ring
    _ ≤ (G/D)/(16000*B) := div_le_div_of_nonneg_right hG (by positivity)
    _ = (V^2*G/(16000*B))/((D*V)*V) := by field_simp
    _ ≤ ((D*V)*I)/((D*V)*V) := div_le_div_of_nonneg_right hbound (by positivity)
    _ = I/V := by field_simp

theorem physical_modulus_from_gains_oai {N K M G : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hL : L.val=(K:ℝ)) (hK : 400≤K)
    {ψ : Jet (N+1) L} (hψ : IsGroundVector (N+1) L r ψ)
    (m : ℕ) (t R C S s₀ : ℝ) (ht : 0≤t) (u : Time)
    (D ell B : ℝ) (hDeq : D=(N+1:ℝ)/L.val^3) (hell : 0<ell) (hM : 0<M) (hB : 1≤B)
    (hG : ell/(8*M)≤(G:ℝ)/D)
    (hgain : ∀ij∈currentAdmissiblePairs K,∀g : Fin G,
      1/(8*B)≤ measureAffinity
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
        (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)) :
    ell/(128000*M*B)≤Phase.modulusOccupation
      (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  have h1 : 1≤K := by omega
  have h50 : 50<L.val := by rw [hL]; exact_mod_cast (show 50<K by omega)
  have hDp : 0<D := by rw [hDeq]; positivity
  let f := fun ij : DiscreteTorus K×DiscreteTorus K ↦ fun g : Fin G ↦
    measureAffinity
      (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u true)
      (physicalGroupReference (M:=M) (x:=ij.1) (y:=ij.2) hL ψ g m t r R C S s₀ u false)
  have hl := pair_group_sum_lower hK f (by linarith : 0<B)
    (fun _ _ ↦ affinity_nonneg _ _) hgain
  have hu := physical_affinity_sum_bound (M:=M) (G:=G) hL h1 h50 hψ m t R C S s₀ ht u
  have hbound : (L.val^3)^2*(G:ℝ)/(16000*B)≤
      (D*L.val^3)*(∫Y : Configuration N L,(∫x : Torus L,‖ψ.1 (Fin.cons x Y)‖)^2) := by
    have he : D*L.val^3=(N+1:ℝ) := by rw [hDeq]; field_simp
    rw [he]
    calc
      _ = (K:ℝ)^6*(G:ℝ)/(16000*B) := by rw [hL,←pow_mul]
      _ ≤ _ := hl.trans hu
  have H := modulus_numeric_gain (by positivity : 0<L.val^3) hDp hell
    (by exact_mod_cast hM) (by linarith : 0<B) hG hbound
  simpa only [Phase.modulusOccupation,Measure.real,BathSlice.volume_torus,
    ENNReal.toReal_ofReal (by positivity : 0≤L.val^3)] using H

end HardSphere.Groups
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.Groups.physical_modulus_from_gains_oai := @OAI.HardSphere.Groups.physical_modulus_from_gains_oai
