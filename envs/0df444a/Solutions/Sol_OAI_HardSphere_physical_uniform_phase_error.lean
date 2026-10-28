-- Prove2me | solution 1 for OAI.HardSphere.physical_uniform_phase_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:34:34.571236+00:00
-- url     : https://prove2.me/submissions/142e40e0-2664-4cf6-ba9c-d774b39957cb

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_BathSlice_IsGroundVector_bathLaw_ae_allowed
import Theorems.Thm_OAI_HardSphere_BathSlice_physical_close_tail
import Theorems.Thm_OAI_HardSphere_IsGroundVector_ae_killed_complexPhase

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
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_HilbertJet
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
namespace HardSphere

attribute [local instance] scalarL2_addCommMonoid scalarL2_module scalarL2_completeSpace

lemma continuous_torusDistance (L : Length) : Continuous (fun p : Torus L × Torus L ↦ torusDistance L p.1 p.2) := by
  unfold torusDistance
  fun_prop

end HardSphere

end
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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PiAC
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
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
namespace HardSphere.Measure

lemma tprod_ac {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : ∀i,Measure (X i)) [∀i,SigmaFinite (μ i)] [∀i,SigmaFinite (ν i)]
    (h : ∀i,μ i ≪ ν i) (l : List ι) : Measure.tprod l μ ≪ Measure.tprod l ν := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [Measure.tprod_cons, Measure.tprod_cons]
    exact (h i).prod ih

lemma pi_ac {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ ν : ∀i,Measure (X i)) [∀i,SigmaFinite (μ i)] [∀i,SigmaFinite (ν i)]
    (h : ∀i,μ i ≪ ν i) : Measure.pi μ ≪ Measure.pi ν := by
  classical
  let : Encodable ι := Fintype.toEncodable ι
  rw [←Measure.pi'_eq_pi μ,←Measure.pi'_eq_pi ν,Measure.pi',Measure.pi']
  simpa only [MeasurableEquiv.piMeasurableEquivTProd_symm_apply] using
    (MeasurableEquiv.piMeasurableEquivTProd (Encodable.sortedUniv_nodup ι) (Encodable.mem_sortedUniv)).symm.measurableEmbedding.absolutelyContinuous_map
      (tprod_ac μ ν h (Encodable.sortedUniv ι))

end HardSphere.Measure

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhaseMeasure
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
namespace HardSphere
open Wiener

lemma localLiftBox_preserving {N : ℕ} (L : Length) (c : LiftedConfiguration N) :
    MeasurePreserving (project N L) (volume.restrict (localLiftBox L c)) volume := by
  have hi (i : Fin N) : MeasurePreserving (fun x : Fin 3 → ℝ ↦ fun j ↦ (x j : AddCircle L.val))
      (volume.restrict (Set.univ.pi (fun j ↦ Icc (c i j-L.val/2) (c i j+L.val/2)))) volume := by
    have hp := measurePreserving_pi (fun j : Fin 3 ↦ volume.restrict (Icc (c i j-L.val/2) (c i j+L.val/2)))
      (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
      (f:=fun _ x ↦ (x:AddCircle L.val)) (fun j ↦ ?_)
    · change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _) (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
      simpa only [Measure.restrict_pi_pi] using hp
    · have hp := AddCircle.measurePreserving_mk L.val (c i j-L.val/2)
      rw [restrict_Ioc_eq_restrict_Icc,show c i j-L.val/2+L.val=c i j+L.val/2 by ring] at hp
      exact hp
  have hp := measurePreserving_pi
    (fun i ↦ volume.restrict (Set.univ.pi (fun j ↦ Icc (c i j-L.val/2) (c i j+L.val/2))))
    (fun _ : Fin N ↦ (volume : Measure (Torus L))) hi
  change MeasurePreserving (fun X : LiftedConfiguration N ↦ fun i j ↦ (X i j : AddCircle L.val)) ((Measure.pi (fun _ : Fin N ↦ (volume : Measure (Fin 3 → ℝ)))).restrict _) (Measure.pi (fun _ : Fin N ↦ (volume : Measure (Torus L))))
  simpa only [project,localLiftBox,Measure.restrict_pi_pi] using hp

lemma ball_subset_localLiftBox {N : ℕ} (L : Length) (c : LiftedConfiguration N) {r : ℝ}
    (hr : r≤L.val/2) : Metric.ball c r ⊆ localLiftBox L c := by
  intro X hX i hi j hj
  have hd : dist (X i j) (c i j) < r :=
    (dist_le_pi_dist _ _ j).trans_lt ((dist_le_pi_dist _ _ i).trans_lt hX)
  rw [Real.dist_eq,abs_lt] at hd
  constructor <;> linarith

lemma gaussianCoordinates_ac' (N : ℕ) : (volume : Measure (Direction N → ℝ)) ≪ gaussianCoordinates N :=
  Measure.pi_ac _ _ (fun _ ↦ gaussianReal_absolutelyContinuous' 0 (by norm_num))

lemma flatten_quasi (N : ℕ) : QuasiMeasurePreserving (flattenEquiv N)
    (volume : Measure (LiftedConfiguration N)) (volume : Measure (Direction N → ℝ)) := by
  let := (flattenEquiv N).isAddHaarMeasure_map (volume : Measure (LiftedConfiguration N))
  exact ⟨(flattenEquiv N).continuous.measurable,absolutelyContinuous_isAddHaarMeasure _ _⟩

lemma endpointNoise_quasi {N : ℕ} {t : ℝ} (ht : 0<t) (X : LiftedConfiguration N) :
    QuasiMeasurePreserving (fun Y : LiftedConfiguration N ↦
      fun j : Direction N ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t))
      (volume : Measure (LiftedConfiguration N)) (volume : Measure (Direction N → ℝ)) := by
  have ht' : Real.sqrt (2*t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hs := (volume : Measure (LiftedConfiguration N)).quasiMeasurePreserving_smul (inv_ne_zero ht')
  have ha := (measurePreserving_add_right (volume : Measure (LiftedConfiguration N)) (-X)).quasiMeasurePreserving
  convert (flatten_quasi N).comp (hs.comp ha) using 1
  all_goals try with_reducible_and_instances rfl
  funext Y j
  change (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)=(Real.sqrt (2*t))⁻¹*(Y j.1 j.2+-X j.1 j.2)
  ring

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhaseBridge
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener

lemma reconstructed_bridge_eq {N : ℕ} (L : Length) {t : ℝ} (ht : 0<t)
    (X Y : LiftedConfiguration N) (β : CoordinatePaths N) :
    freeTrajectory N L t
      (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β))
      (project N L X)=projectedBridgePath L t X Y β := by
  have ht' : Real.sqrt (2*t) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  ext s i j
  change (X i j:AddCircle L.val)+
    (((Real.sqrt (2*t)*((Y i j-X i j)/Real.sqrt (2*t)*(s:ℝ)+β (i,j) s)):ℝ):AddCircle L.val)=
    (((1-(s:ℝ))*X i j+(s:ℝ)*Y i j+Real.sqrt (2*t)*β (i,j) s:ℝ):AddCircle L.val)
  rw [←AddCircle.coe_add]
  congr 1
  field_simp
  ring

lemma projectedBridgePath_endpoints {N : ℕ} (L : Length) (t : ℝ) (X Y : LiftedConfiguration N) :
    ∀ᵐ β ∂coordinateBridge N, projectedBridgePath L t X Y β 0=project N L X ∧
      projectedBridgePath L t X Y β 1=project N L Y := by
  filter_upwards [coordinateBridge_endpoints N] with β hβ
  constructor <;> ext i j
  · change (((1-(0:Time).val)*X i j+(0:Time).val*Y i j+Real.sqrt (2*t)*β (i,j) 0:ℝ):AddCircle L.val)=_
    simp [(hβ (i,j)).1]
    rfl
  · change (((1-(1:Time).val)*X i j+(1:Time).val*Y i j+Real.sqrt (2*t)*β (i,j) 1:ℝ):AddCircle L.val)=_
    simp [(hβ (i,j)).2]
    rfl

lemma killed_ae_lifted_bridges {N : ℕ} (L : Length) (a : ℝ) {t : ℝ} (ht : 0<t)
    (c : LiftedConfiguration N) {P : Configuration N L → Configuration N L → Prop}
    (hP : ∀ᵐ ω ∂killedPathLaw N L a t, P (ω 0) (ω 1)) :
    ∀ᵐ X ∂volume.restrict (localLiftBox L c), ∀ᵐ Y ∂(volume : Measure (LiftedConfiguration N)),
      ∀ᵐ β ∂coordinateBridge N, projectedBridgePath L t X Y β ∈ staysAllowed N L a →
        P (project N L X) (project N L Y) := by
  have hf : ∀ᵐ ω ∂freePathLaw N L t, ω∈staysAllowed N L a → P (ω 0) (ω 1) :=
    (ae_restrict_iff' (staysAllowed_open N L a).measurableSet).mp hP
  have hfree : MeasurePreserving (fun p : CoordinatePaths N × Configuration N L ↦
      freeTrajectory N L t p.1 p.2) ((coordinateWiener N).prod volume) (freePathLaw N L t) :=
    ⟨(freeTrajectory_continuous N L t).measurable,rfl⟩
  have hswap := (measurePreserving_swap (μ:= (volume : Measure (Configuration N L))) (ν:=coordinateWiener N))
  have hp := (localLiftBox_preserving L c).prod (reconstructCoordinates_preserving N)
  have hh := (hfree.comp (hswap.comp hp)).quasiMeasurePreserving.ae hf
  have hha := ae_ae_of_ae_prod hh
  filter_upwards [hha] with X hX
  have hxg := ae_ae_of_ae_prod hX
  have hxl := hxg.filter_mono (gaussianCoordinates_ac' N).ae_le
  have hxy := (endpointNoise_quasi ht X).ae hxl
  filter_upwards [hxy] with Y hY
  filter_upwards [hY,projectedBridgePath_endpoints L t X Y] with β hβ he
  change freeTrajectory N L t (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β))
    (project N L X)∈staysAllowed N L a → P
      (freeTrajectory N L t (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β)) (project N L X) 0)
      (freeTrajectory N L t (reconstructCoordinates N ((fun j ↦ (Y j.1 j.2-X j.1 j.2)/Real.sqrt (2*t)),β)) (project N L X) 1) at hβ
  rw [reconstructed_bridge_eq L ht X Y β] at hβ
  intro hs
  simpa only [he.1,he.2] using hβ hs

lemma exists_bridge_bounded_positive (N : ℕ) : ∃ B : ℝ, 0<B ∧
    coordinateBridge N {β | ‖β‖≤B} ≠ 0 := by
  by_contra! h
  have hz : coordinateBridge N (⋃ n : ℕ, {β | ‖β‖≤(n:ℝ)+1})=0 :=
    measure_iUnion_null (fun n ↦ h ((n:ℝ)+1) (by positivity))
  have he : (⋃ n : ℕ, {β : CoordinatePaths N | ‖β‖≤(n:ℝ)+1})=univ := by
    apply eq_univ_of_forall
    intro β
    obtain ⟨n,hn⟩ := exists_nat_gt ‖β‖
    exact mem_iUnion.mpr ⟨n,by simp only [mem_ofPred_eq]; linarith⟩
  rw [he,measure_univ] at hz
  exact one_ne_zero hz

lemma liftedBridge_distance {N : ℕ} {t : ℝ} (ht : 0≤t)
    (X Y : LiftedConfiguration N) (β : CoordinatePaths N) (s : Time) :
    dist (liftedBridgePath t X Y β s) ((1-(s:ℝ)) • X+(s:ℝ) • Y) ≤
      Real.sqrt (2*t)*‖β‖ := by
  have hscale : 0 ≤ Real.sqrt (2*t) := by
    simpa only [Real.sqrt_zero] using
      Real.sqrt_le_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ht)
  apply (dist_pi_le_iff (mul_nonneg hscale (norm_nonneg β))).mpr
  intro i
  apply (dist_pi_le_iff (mul_nonneg hscale (norm_nonneg β))).mpr
  intro j
  change dist ((1-(s:ℝ))*X i j+(s:ℝ)*Y i j+Real.sqrt (2*t)*β (i,j) s)
    ((1-(s:ℝ))*X i j+(s:ℝ)*Y i j) ≤ _
  rw [Real.dist_eq,add_sub_cancel_left,abs_mul,abs_of_nonneg hscale]
  apply mul_le_mul_of_nonneg_left _ hscale
  exact (ContinuousMap.norm_coe_le_norm (β (i,j)) s).trans (norm_le_pi_norm β (i,j))

lemma projectedBridge_stays_of_bounded {N : ℕ} (L : Length) (a : ℝ)
    {c X Y : LiftedConfiguration N} {R t B : ℝ} (ht : 0≤t)
    (hball : Metric.ball c R ⊆ (project N L) ⁻¹' allowed N L a)
    (hX : X∈Metric.ball c (R/2)) (hY : Y∈Metric.ball c (R/2))
    (hsmall : Real.sqrt (2*t)*B<R/2) {β : CoordinatePaths N} (hβ : ‖β‖≤B) :
    projectedBridgePath L t X Y β ∈ staysAllowed N L a := by
  rintro _ ⟨s,rfl⟩
  apply hball
  have hz := (convex_ball c (R/2)) hX hY (sub_nonneg.mpr s.property.2) s.property.1 (sub_add_cancel 1 (s:ℝ))
  exact (dist_triangle _ ((1-(s:ℝ)) • X+(s:ℝ) • Y) c).trans_lt
    (lt_of_le_of_lt (add_le_add ((liftedBridge_distance ht X Y β s).trans
      (mul_le_mul_of_nonneg_left hβ (Real.sqrt_nonneg _))) (le_refl _)) (by
        change Real.sqrt (2*t)*B+dist ((1-(s:ℝ)) • X+(s:ℝ) • Y) c<R
        change dist ((1-(s:ℝ)) • X+(s:ℝ) • Y) c<R/2 at hz
        linarith))

lemma killed_ae_local_pairs {N : ℕ} (L : Length) (a : ℝ)
    {P : Configuration N L → Configuration N L → Prop}
    (hP : ∀t, 0<t → ∀ᵐ ω ∂killedPathLaw N L a t, P (ω 0) (ω 1))
    (c : LiftedConfiguration N) {R : ℝ} (hR : 0<R) (hL : R≤L.val)
    (hball : Metric.ball c R ⊆ (project N L) ⁻¹' allowed N L a) :
    ∀ᵐ X ∂volume.restrict (Metric.ball c (R/2)),
    ∀ᵐ Y ∂volume.restrict (Metric.ball c (R/2)), P (project N L X) (project N L Y) := by
  obtain ⟨B,hB,hpos⟩ := exists_bridge_bounded_positive N
  let t : ℝ := (R/(4*(B+1)))^2/2
  have ha : 0<R/(4*(B+1)) := div_pos hR (by positivity)
  have ht : 0<t := by dsimp [t]; positivity
  have hsqrt : Real.sqrt (2*t)=R/(4*(B+1)) := by
    rw [show 2*t=(R/(4*(B+1)))^2 by dsimp [t]; ring,Real.sqrt_sq ha.le]
  have hsmall : Real.sqrt (2*t)*B<R/2 := by
    rw [hsqrt]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0<4*(B+1))).mpr
    nlinarith
  have hh := killed_ae_lifted_bridges L a ht c (hP t ht)
  have hsub := ball_subset_localLiftBox L c (show R/2≤L.val/2 by linarith)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hh,ae_restrict_mem measurableSet_ball] with X hX hmemX
  filter_upwards [ae_restrict_of_ae hX,ae_restrict_mem measurableSet_ball] with Y hY hmemY
  obtain ⟨β,hβ,hpair⟩ := exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hY)
  exact hpair (projectedBridge_stays_of_bounded L a ht.le hball hmemX hmemY hsmall hβ)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_TorusLocalBridge
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
namespace HardSphere
open Wiener

lemma localLiftChart_preserving {N : ℕ} (L : Length) (c : LiftedConfiguration N) :
    MeasurePreserving (project N L) (volume.restrict (localLiftChart L c)) volume := by
  have hi (i : Fin N) : MeasurePreserving (fun x : Fin 3 → ℝ ↦ fun j ↦ (x j : AddCircle L.val))
      (volume.restrict (univ.pi (fun j ↦ Ioc (c i j-L.val/2) (c i j-L.val/2+L.val)))) volume := by
    have hp := measurePreserving_pi (fun j : Fin 3 ↦ volume.restrict (Ioc (c i j-L.val/2) (c i j-L.val/2+L.val)))
      (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val)))
      (f:=fun _ x ↦ (x:AddCircle L.val)) (fun j ↦ AddCircle.measurePreserving_mk L.val (c i j-L.val/2))
    change MeasurePreserving _ ((Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ))).restrict _) (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle L.val))))
    simpa only [Measure.restrict_pi_pi] using hp
  have hp := measurePreserving_pi
    (fun i ↦ volume.restrict (univ.pi (fun j ↦ Ioc (c i j-L.val/2) (c i j-L.val/2+L.val))))
    (fun _ : Fin N ↦ (volume : Measure (Torus L))) hi
  change MeasurePreserving (fun X : LiftedConfiguration N ↦ fun i j ↦ (X i j : AddCircle L.val)) ((Measure.pi (fun _ : Fin N ↦ (volume : Measure (Fin 3 → ℝ)))).restrict _) (Measure.pi (fun _ : Fin N ↦ (volume : Measure (Torus L))))
  simpa only [project,localLiftChart,Measure.restrict_pi_pi] using hp

lemma project_injOn_chart {N : ℕ} (L : Length) (c : LiftedConfiguration N) :
    Set.InjOn (project N L) (localLiftChart L c) := by
  intro X hX Y hY he
  funext i j
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (hX i (mem_univ i) j (mem_univ j))
    (hY i (mem_univ i) j (mem_univ j))).mp (congrFun (congrFun he i) j)

lemma ball_subset_localLiftChart {N : ℕ} (L : Length) (c : LiftedConfiguration N) {r : ℝ}
    (hr : r≤L.val/2) : Metric.ball c r ⊆ localLiftChart L c := by
  intro X hX i hi j hj
  have hd : dist (X i j) (c i j) < r :=
    (dist_le_pi_dist _ _ j).trans_lt ((dist_le_pi_dist _ _ i).trans_lt hX)
  rw [Real.dist_eq,abs_lt] at hd
  constructor <;> linarith

lemma isOpenMap_project (N : ℕ) (L : Length) : IsOpenMap (project N L) := by
  have hcircle : Function.Surjective (fun t : ℝ ↦ (t : AddCircle L.val)) := by
    intro x
    exact ⟨(AddCircle.equivIco L.val 0 x).val,AddCircle.coe_equivIco⟩
  have hopen : IsOpenMap (fun X : Fin 3 → ℝ ↦ fun j ↦ (X j : AddCircle L.val)) :=
    IsOpenMap.piMap (fun _ ↦ QuotientAddGroup.isOpenMap_coe) (Eventually.of_forall (fun _ ↦ hcircle))
  exact IsOpenMap.piMap (fun _ : Fin N ↦ hopen)
    (Eventually.of_forall (fun _ ↦ Function.Surjective.piMap (fun _ ↦ hcircle)))

lemma project_ball_preserving {N : ℕ} (L : Length) (c : LiftedConfiguration N) {r : ℝ}
    (hr : r≤L.val/2) : MeasurePreserving (project N L) (volume.restrict (Metric.ball c r))
      (volume.restrict ((project N L) '' Metric.ball c r)) := by
  have hsub := ball_subset_localLiftChart L c hr
  have he : (project N L) ⁻¹' ((project N L) '' Metric.ball c r) ∩ localLiftChart L c=Metric.ball c r := by
    ext X
    constructor
    · rintro ⟨⟨Y,hY,hYX⟩,hX⟩
      exact (project_injOn_chart L c (hsub hY) hX hYX) ▸ hY
    · intro hX
      exact ⟨mem_image_of_mem _ hX,hsub hX⟩
  have h := (localLiftChart_preserving L c).restrict_preimage
    ((isOpenMap_project N L) (Metric.ball c r) Metric.isOpen_ball).measurableSet
  rw [Measure.restrict_restrict (((isOpenMap_project N L) (Metric.ball c r) Metric.isOpen_ball).measurableSet.preimage (continuous_project N L).measurable),he] at h
  exact h

lemma killed_ae_torus_local_pairs {N : ℕ} (L : Length) (a : ℝ)
    {P : Configuration N L → Configuration N L → Prop}
    (hPm : MeasurableSet {p : Configuration N L×Configuration N L | P p.1 p.2})
    (hP : ∀t, 0<t → ∀ᵐ ω ∂killedPathLaw N L a t, P (ω 0) (ω 1))
    {x : Configuration N L} (hx : x∈allowed N L a) :
    ∃ U : Set (Configuration N L), IsOpen U ∧ x∈U ∧ U⊆allowed N L a ∧
      ∀ᵐ X ∂volume.restrict U, ∀ᵐ Y ∂volume.restrict U, P X Y := by
  let c := representative N L x
  have hc : c∈(project N L) ⁻¹' allowed N L a := by simpa [c] using hx
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp ((isOpen_allowed N L a).preimage (continuous_project N L)) c hc
  let S := min R L.val
  have hS : 0<S := lt_min hR L.property
  have hb : Metric.ball c S ⊆ (project N L) ⁻¹' allowed N L a :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball
  let U := (project N L) '' Metric.ball c (S/2)
  have hU : IsOpen U := (isOpenMap_project N L) _ Metric.isOpen_ball
  refine ⟨U,hU,?_,?_,?_⟩
  · exact ⟨c,Metric.mem_ball_self (by positivity),project_representative N L x⟩
  · rintro _ ⟨X,hX,rfl⟩
    exact hb ((Metric.ball_subset_ball (by linarith : S/2≤S)) hX)
  · have h := killed_ae_local_pairs L a hP c hS (min_le_right _ _) hb
    have hp := project_ball_preserving L c (show S/2≤L.val/2 from div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
    have hh : ∀ᵐ p ∂(volume.restrict U).prod (volume.restrict U), P p.1 p.2 := by
      rw [←(hp.prod hp).map_eq,ae_map_iff (hp.prod hp).measurable.aemeasurable hPm]
      exact (ae_prod_iff_ae_ae (hPm.preimage (hp.prod hp).measurable)).mpr h
    exact ae_ae_of_ae_prod hh

end HardSphere

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalAE
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace LocalAE
variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)

lemma isOpen_region (P : α → Prop) : IsOpen (region μ P) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U,hU,hx,hP⟩
  apply mem_of_superset (hU.mem_nhds hx)
  intro y hy
  exact ⟨U,hU,hy,hP⟩

lemma ae_region [SecondCountableTopology α] (P : α → Prop) :
    ∀ᵐ x ∂μ.restrict (region μ P), P x := by
  let I := {U : Set α // IsOpen U ∧ ∀ᵐ x ∂μ.restrict U,P x}
  have he : region μ P=⋃U : I,U.val := by
    ext x
    simp only [region,mem_ofPred_eq,mem_iUnion]
    constructor
    · rintro ⟨U,hU,hx,hP⟩
      exact ⟨⟨U,hU,hP⟩,hx⟩
    · rintro ⟨U,hx⟩
      exact ⟨U.val,U.property.1,hx,U.property.2⟩
  obtain ⟨T,hT,heT⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun U : I ↦ U.val) (fun U ↦ U.property.1)
  rw [he,←heT,ae_restrict_biUnion_iff _ hT]
  intro U hU
  exact U.property.2

lemma region_unique [IsOpenPosMeasure μ] {f : α → β} {z w : β} {x : α}
    (hz : x∈region μ (fun y ↦ f y=z)) (hw : x∈region μ (fun y ↦ f y=w)) : z=w := by
  obtain ⟨U,hU,hx,hz⟩ := hz
  obtain ⟨V,hV,hy,hw⟩ := hw
  have hne := (hU.inter hV).measure_ne_zero μ ⟨x,hx,hy⟩
  have hp : ∀ᵐ y ∂μ.restrict (U∩V), f y=z ∧ f y=w :=
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hz).and
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right hw)
  obtain ⟨y,hy,h1,h2⟩ := exists_mem_of_measure_ne_zero_of_ae hne hp
  exact h1.symm.trans h2

lemma connected_region [IsOpenPosMeasure μ] {f : α → β} {S : Set α}
    (hS : IsPreconnected S) (hcover : ∀x∈S, ∃z, x∈region μ (fun y ↦ f y=z))
    {x : α} (hx : x∈S) {z : β} (hz : x∈region μ (fun y ↦ f y=z)) :
    S⊆region μ (fun y ↦ f y=z) := by
  let U := region μ (fun y ↦ f y=z)
  let V := ⋃w≠z,region μ (fun y ↦ f y=w)
  have hU : IsOpen U := isOpen_region μ _
  have hV : IsOpen V := isOpen_iUnion (fun w ↦ isOpen_iUnion (fun _ ↦ isOpen_region μ _))
  have hd : Disjoint U V := by
    apply disjoint_left.mpr
    intro y hy hyv
    obtain ⟨w,hw'⟩ := mem_iUnion.mp hyv
    obtain ⟨hw,hy'⟩ := mem_iUnion.mp hw'
    exact hw (region_unique μ hy' hy)
  have hc : S⊆U∪V := by
    intro y hy
    obtain ⟨w,hw⟩ := hcover y hy
    by_cases he : w=z
    · exact Or.inl (by simpa only [U,he] using hw)
    · exact Or.inr (mem_iUnion.mpr ⟨w,mem_iUnion.mpr ⟨he,hw⟩⟩)
  exact hS.subset_left_of_subset_union hU hV hd hc ⟨x,hx,hz⟩

omit [TopologicalSpace α] in
lemma ae_local_const_of_ae_pairs {f : α → β} {U : Set α} (hU : μ U≠0)
    (h : ∀ᵐ x ∂μ.restrict U, ∀ᵐ y ∂μ.restrict U,f x=f y) :
    ∃z,∀ᵐ y ∂μ.restrict U,f y=z := by
  obtain ⟨x,hx,hp⟩ := exists_mem_of_measure_ne_zero_of_ae hU h
  exact ⟨f x,hp.mono (fun _ hy ↦ hy.symm)⟩

lemma representative_mem [Inhabited β] {f : α → β} {x : α}
    (h : ∃z,x∈region μ (fun y ↦ f y=z)) :
    x∈region μ (fun y ↦ f y=representative μ f x) := by
  simp only [representative,dite_eq_left h]
  exact Classical.choose_spec h

lemma representative_eq [Inhabited β] [IsOpenPosMeasure μ] {f : α → β} {x : α} {z : β}
    (h : x∈region μ (fun y ↦ f y=z)) : representative μ f x=z :=
  region_unique μ (representative_mem μ ⟨z,h⟩) h

lemma representative_ae [Inhabited β] [IsOpenPosMeasure μ] [SecondCountableTopology α]
    [OpensMeasurableSpace α] {f : α → β} {S : Set α} (hS : IsOpen S)
    (hcover : ∀x∈S,∃z,x∈region μ (fun y ↦ f y=z)) :
    ∀ᵐ x ∂μ.restrict S,f x=representative μ f x := by
  have hsub : S⊆region μ (fun y ↦ f y=representative μ f y) := by
    intro x hx
    obtain ⟨z,U,hU,hxU,hf⟩ := hcover x hx
    refine ⟨U∩S,hU.inter hS,⟨hxU,hx⟩,?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hf,
      ae_restrict_mem (hU.inter hS).measurableSet] with y hy hym
    exact hy.trans (representative_eq μ (show y∈region μ (fun y ↦ f y=z) from ⟨U,hU,hym.1,hf⟩)).symm
  exact ae_restrict_of_ae_restrict_of_subset hsub (ae_region μ _)

lemma representative_eq_on_connected [Inhabited β] [IsOpenPosMeasure μ]
    {f : α → β} {S : Set α} (hS : IsPreconnected S)
    (hcover : ∀x∈S,∃z,x∈region μ (fun y ↦ f y=z)) {x y : α} (hx : x∈S) (hy : y∈S) :
    representative μ f x=representative μ f y := by
  have hz := representative_mem μ (hcover x hx)
  have hzy := connected_region μ hS hcover hx hz hy
  exact (representative_eq μ hzy).symm

end LocalAE

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_Phase
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere
open Wiener

lemma complexPhase_mul_norm (z : ℂ) : complexPhase z*(‖z‖:ℂ)=z := by
  by_cases hz : z=0
  · simp [complexPhase,hz]
  · exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

lemma norm_complexPhase {z : ℂ} (hz : z≠0) : ‖complexPhase z‖=1 := by
  rw [complexPhase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr hz)

lemma measurable_complexPhase : Measurable complexPhase := by unfold complexPhase; fun_prop

end HardSphere

namespace HardSphere

lemma IsGroundVector.phase_region {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {x : Configuration N L} (hx : x∈allowed N L a) :
    ∃z, x∈LocalAE.region volume (fun y ↦ complexPhase (u.1 y)=z) := by
  have hm := measurable_complexPhase.comp (Lp.stronglyMeasurable u.1).measurable
  have hpm : MeasurableSet {p : Configuration N L×Configuration N L |
      complexPhase (u.1 p.1)=complexPhase (u.1 p.2)} :=
    measurableSet_eq_fun (hm.comp measurable_fst) (hm.comp measurable_snd)
  obtain ⟨U,hU,hxU,hsub,hp⟩ := killed_ae_torus_local_pairs L a (P:=fun X Y ↦ complexPhase (u.1 X)=complexPhase (u.1 Y)) hpm
    (fun t ht ↦ hu.ae_killed_complexPhase ht.le) hx
  obtain ⟨z,hz⟩ := LocalAE.ae_local_const_of_ae_pairs volume (hU.measure_ne_zero volume ⟨x,hxU⟩) hp
  exact ⟨z,U,hU,hxU,hz⟩

lemma IsGroundVector.ae_phaseRepresentative {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) :
    ∀ᵐ x ∂volume.restrict (allowed N L a), complexPhase (u.1 x)=groundPhaseRepresentative u x :=
  LocalAE.representative_ae volume (isOpen_allowed N L a) (fun _ hx ↦ hu.phase_region hx)

lemma IsGroundVector.phaseRepresentative_eq_on_connected {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) {S : Set (Configuration N L)} (hS : IsPreconnected S)
    (hsub : S⊆allowed N L a) {x y : Configuration N L} (hx : x∈S) (hy : y∈S) :
    groundPhaseRepresentative u x=groundPhaseRepresentative u y :=
  LocalAE.representative_eq_on_connected volume hS (fun _ hz ↦ hu.phase_region (hsub hz)) hx hy

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhaseTransfer
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
open scoped ENNReal

namespace HardSphere.Phase

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma norm_setIntegral_of_commonPhase {f : X → ℂ} {U : Set X}
    (hphase : HasCommonPhase f U ν) :
    ‖∫ x in U, f x ∂ν‖ = ∫ x in U, ‖f x‖ ∂ν := by
  obtain ⟨c, hc, heq⟩ := hphase
  rw [integral_congr_ae heq, integral_const_mul, integral_complex_ofReal, norm_mul,
    hc, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]

lemma slice_phase_loss {f : X → ℂ} (hf : Integrable f ν) {U : Set X}
    (hU : MeasurableSet U) (hphase : HasCommonPhase f U ν) :
    (∫ x, ‖f x‖ ∂ν)^2 - ‖∫ x, f x ∂ν‖^2 ≤
      4 * (∫ x, ‖f x‖ ∂ν) * (∫ x in Uᶜ, ‖f x‖ ∂ν) := by
  have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hb : 0 ≤ ∫ x in Uᶜ, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hn : ‖∫ x, f x ∂ν‖ ≤ ∫ x, ‖f x‖ ∂ν := norm_integral_le_integral_norm _
  have htri := norm_sub_le (∫ x, f x ∂ν) (∫ x in Uᶜ, f x ∂ν)
  have hdecomp := integral_add_compl hU hf
  have hdecompNorm := integral_add_compl hU hf.norm
  have hdiff : (∫ x, f x ∂ν) - (∫ x in Uᶜ, f x ∂ν) = ∫ x in U, f x ∂ν := by
    rw [← hdecomp]; abel
  rw [hdiff, norm_setIntegral_of_commonPhase hphase] at htri
  have hsmall := norm_integral_le_integral_norm (μ := ν.restrict Uᶜ) f
  have he : (∫ x, ‖f x‖ ∂ν) - ‖∫ x, f x ∂ν‖ ≤
      2 * (∫ x in Uᶜ, ‖f x‖ ∂ν) := by linarith
  have he' : (∫ x, ‖f x‖ ∂ν) + ‖∫ x, f x ∂ν‖ ≤ 2 * (∫ x, ‖f x‖ ∂ν) := by linarith
  have hprod := mul_le_mul he he' (by positivity) (by positivity :
    0 ≤ 2 * (∫ x in Uᶜ, ‖f x‖ ∂ν))
  nlinarith [hprod]

lemma integral_mul_le_sqrt (f g : X → ℝ) (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hf0 : 0 ≤ᵐ[ν] f) (hg0 : 0 ≤ᵐ[ν] g) :
    ∫ x, f x * g x ∂ν ≤ Real.sqrt (∫ x, f x ^ 2 ∂ν) *
      Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 (by simpa using hf) (by simpa using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

lemma integral_norm_sq_le [IsFiniteMeasure ν] {f : X → ℂ} (hf : MemLp f 2 ν) :
    (∫ x, ‖f x‖ ∂ν)^2 ≤ ν.real univ * ∫ x, ‖f x‖ ^ 2 ∂ν := by
  have h := integral_mul_le_sqrt (fun _ : X ↦ 1) (fun x ↦ ‖f x‖)
    (memLp_const 1) hf.norm (Eventually.of_forall fun _ ↦ zero_le_one)
    (Eventually.of_forall fun _ ↦ norm_nonneg _)
  simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one] at h
  have ha : 0 ≤ ∫ x, ‖f x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hm : 0 ≤ ∫ x, ‖f x‖^2 ∂ν := integral_nonneg fun _ ↦ sq_nonneg _
  have hs := (sq_le_sq₀ ha (by positivity)).2 h
  simpa only [mul_pow, Real.sq_sqrt (measureReal_nonneg), Real.sq_sqrt hm] using hs

end HardSphere.Phase

namespace HardSphere.Phase

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ]

lemma memLp_slices {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    ∀ᵐ y ∂μ, MemLp (fun x ↦ f (y,x)) 2 ν := by
  filter_upwards [hf.aestronglyMeasurable.prodMk_left,
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae] with y hm hi
  exact (memLp_two_iff_integrable_sq_norm hm).2 hi

lemma memLp_integral_norm {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν)) :
    MemLp (fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν) 2 μ := by
  have hm := hf.aestronglyMeasurable.norm.integral_prod_right'
  apply (memLp_two_iff_integrable_sq hm).2
  have hi := (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
  apply (hi.const_mul (ν.real univ)).mono' (hm.pow 2)
  filter_upwards [memLp_slices hf] with y hy
  change ‖(∫ x, ‖f (y,x)‖ ∂ν)^2‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact integral_norm_sq_le hy

lemma setIntegral_norm_sq_le {f : X → ℂ} (hf : MemLp f 2 ν) (A : Set X) :
    (∫ x in A, ‖f x‖ ∂ν)^2 ≤ ν.real A * ∫ x, ‖f x‖^2 ∂ν := by
  have h := integral_norm_sq_le (hf.restrict (s := A))
  simp only [Measure.real, Measure.restrict_apply_univ] at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg)
  exact integral_mono_measure Measure.restrict_le_self
    (Eventually.of_forall fun _ ↦ sq_nonneg _)
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

theorem phase_transfer {f : Y × X → ℂ} (hf : MemLp f 2 (μ.prod ν))
    (hnorm : ∫ z, ‖f z‖^2 ∂μ.prod ν = 1) (hV : 0 < ν.real univ)
    {U : Set (Y × X)} (hU : MeasurableSet U)
    (hphase : ∀ᵐ y ∂μ, HasCommonPhase (fun x ↦ f (y,x)) (Prod.mk y ⁻¹' U) ν) :
    modulusOccupation f μ ν - 4 * Real.sqrt (geometricLoss f U μ ν) ≤
      occupation f μ ν := by
  let a : Y → ℝ := fun y ↦ ∫ x, ‖f (y,x)‖ ∂ν
  let b : Y → ℝ := fun y ↦ ∫ x in Prod.mk y ⁻¹' Uᶜ, ‖f (y,x)‖ ∂ν
  let c : Y → ℝ := fun y ↦ ‖∫ x, f (y,x) ∂ν‖
  let m : Y → ℝ := fun y ↦ ∫ x, ‖f (y,x)‖^2 ∂ν
  let v : Y → ℝ := fun y ↦ ν.real (Prod.mk y ⁻¹' Uᶜ)
  let V : ℝ := ν.real univ
  have ha0 (y) : 0 ≤ a y := integral_nonneg fun _ ↦ norm_nonneg _
  have hb0 (y) : 0 ≤ b y := integral_nonneg fun _ ↦ norm_nonneg _
  have hc0 (y) : 0 ≤ c y := norm_nonneg _
  have hm0 (y) : 0 ≤ m y := integral_nonneg fun _ ↦ sq_nonneg _
  have hv0 (y) : 0 ≤ v y := measureReal_nonneg
  have hvV (y) : v y ≤ V := measureReal_mono (by simp)
  have ha : MemLp a 2 μ := memLp_integral_norm hf
  have hbmeas : AEStronglyMeasurable b μ := by
    have h := (hf.aestronglyMeasurable.norm.indicator hU.compl).integral_prod_right'
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ext y
    dsimp only [b]
    rw [← integral_indicator (hU.compl.preimage measurable_prodMk_left)]
    rfl
  have hb : MemLp b 2 μ := by
    apply ha.mono' hbmeas
    filter_upwards [memLp_slices hf] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 y)]
    exact integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (hy.integrable (by norm_num)).norm
  have hc : MemLp c 2 μ := by
    refine ha.mono' hf.aestronglyMeasurable.integral_prod_right'.norm ?_
    exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hc0 y)]
      exact norm_integral_le_integral_norm _
  have hmi : Integrable m μ :=
    (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left
  have hvmeas : Measurable v := (measurable_measure_prodMk_left hU.compl).ennreal_toReal
  have hvmi : Integrable (fun y ↦ v y * m y) μ := by
    refine (hmi.const_mul V).mono' (hvmeas.aestronglyMeasurable.mul hmi.aestronglyMeasurable) ?_
    exact Eventually.of_forall fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hv0 y) (hm0 y))]
      exact mul_le_mul_of_nonneg_right (hvV y) (hm0 y)
  have hmass : ∫ y, m y ∂μ = 1 := by
    rw [← integral_prod _ (hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
    exact hnorm
  have ha2 : ∫ y, a y ^ 2 ∂μ ≤ V := by
    calc
      _ ≤ ∫ y, V * m y ∂μ := by
        apply integral_mono_ae ha.integrable_sq (hmi.const_mul V)
        filter_upwards [memLp_slices hf] with y hy
        exact integral_norm_sq_le hy
      _ = V := by rw [integral_const_mul, hmass, mul_one]
  have hb2 : ∫ y, b y ^ 2 ∂μ ≤ ∫ y, v y * m y ∂μ := by
    apply integral_mono_ae hb.integrable_sq hvmi
    filter_upwards [memLp_slices hf] with y hy
    exact setIntegral_norm_sq_le hy _
  have hmul : ∫ y, a y * b y ∂μ ≤
      Real.sqrt V * Real.sqrt (∫ y, v y * m y ∂μ) := by
    refine (integral_mul_le_sqrt a b ha hb
      (Eventually.of_forall ha0) (Eventually.of_forall hb0)).trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt ha2) (Real.sqrt_le_sqrt hb2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hab : Integrable (fun y ↦ a y * b y) μ := ha.integrable_mul hb
  have hloss : (∫ y, a y^2 ∂μ) - (∫ y, c y^2 ∂μ) ≤
      4 * ∫ y, a y * b y ∂μ := by
    rw [← integral_sub ha.integrable_sq hc.integrable_sq, ← integral_const_mul]
    apply integral_mono_ae (ha.integrable_sq.sub hc.integrable_sq) (hab.const_mul 4)
    filter_upwards [memLp_slices hf, hphase] with y hy hp
    simpa only [a, b, c, Pi.sub_apply, preimage_compl, mul_assoc] using
      slice_phase_loss (hy.integrable (by norm_num))
        (hU.preimage measurable_prodMk_left) hp
  have hd0 : 0 ≤ ∫ y, v y * m y ∂μ := integral_nonneg fun y ↦ mul_nonneg (hv0 y) (hm0 y)
  have hroot : Real.sqrt V * Real.sqrt (∫ y, v y * m y ∂μ) =
      V * Real.sqrt ((∫ y, v y * m y ∂μ) / V) := by
    rw [Real.sqrt_div hd0, ← mul_div_assoc]
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.2 hV))).2
    calc
      _ = (Real.sqrt V * Real.sqrt V) * Real.sqrt (∫ y, v y * m y ∂μ) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hV.le]
  have h : (∫ y, a y^2 ∂μ) - (∫ y, c y^2 ∂μ) ≤
      4 * V * Real.sqrt ((∫ y, v y * m y ∂μ) / V) := by
    calc
      _ ≤ 4 * ∫ y, a y * b y ∂μ := hloss
      _ ≤ 4 * (Real.sqrt V * Real.sqrt (∫ y, v y * m y ∂μ)) := mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = _ := by rw [hroot]; ring
  dsimp only [modulusOccupation, occupation, geometricLoss]
  change (∫ y, a y^2 ∂μ) / V - 4 * Real.sqrt ((∫ y, v y * m y ∂μ) / V) ≤
    (∫ y, c y^2 ∂μ) / V
  apply (le_div_iff₀ (show 0 < V from hV)).2
  have hvne : V ≠ 0 := ne_of_gt hV
  rw [sub_mul, div_mul_cancel₀ _ hvne]
  nlinarith

end HardSphere.Phase

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Vertex
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

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

variable {A : Type*} [AddCommGroup A]

lemma coordinateRay_zero (x : Vertex) (i : Fin 3) (d : ℤ) :
    coordinateRay x i d 0=x := by ext j; simp [coordinateRay]

lemma coordinateRay_injective (x : Vertex) (i : Fin 3) (d : ℤ) (hd : d≠0) :
    Function.Injective (coordinateRay x i d) := by
  intro m n h
  have hv := congrFun h i
  simp only [coordinateRay, ite_true] at hv
  have : (m:ℤ)=(n:ℤ) := mul_left_cancel₀ hd (add_left_cancel hv)
  exact_mod_cast this

lemma coordinateRay_step (x : Vertex) (i : Fin 3) (d : ℤ) (hd : |d|=1) (n : ℕ) :
    nearestStep (coordinateRay x i d n) (coordinateRay x i d (n+1)) := by
  refine ⟨i, ?_, ?_⟩
  · simp only [coordinateRay, ite_true, Nat.cast_add, Nat.cast_one]
    have he : x i+d*(n:ℤ)-(x i+d*((n:ℤ)+1)) = -d := by ring
    rw [he, abs_neg, hd]
  · intro j hj
    simp only [coordinateRay, ite_eq_right hj]

lemma coordinateRay_reachable (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (d : ℤ) (hd : |d|=1) (hC : ∀ n, coordinateRay x i d n∉C) (n : ℕ) :
    avoidingReach C x (coordinateRay x i d n) := by
  induction n with
  | zero => rw [coordinateRay_zero]; exact Relation.ReflTransGen.refl
  | succ n ih => exact ih.tail ⟨hC n, hC (n+1), coordinateRay_step x i d hd n⟩

lemma coordinateRay_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (d : ℤ) (hd : |d|=1) (hC : ∀ n, coordinateRay x i d n∉C) : x∈exterior C := by
  have hd0 : d≠0 := by intro h; simp [h] at hd
  refine ⟨by simpa only [coordinateRay_zero] using hC 0, ?_⟩
  have hi := Set.infinite_range_of_injective (coordinateRay_injective x i d hd0)
  exact hi.mono (by
    rintro y ⟨n,rfl⟩
    exact coordinateRay_reachable C x i d hd hC n)

lemma upper_ray_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : ∀ c∈C, c i<x i) : x∈exterior C := by
  apply coordinateRay_exterior C x i 1 (by norm_num)
  intro n hn
  have h := hx _ hn
  simp only [coordinateRay, ite_true, one_mul] at h
  omega

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_StarOffsets
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
noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice
variable {A : Type*} [AddCommGroup A]

lemma lower_ray_exterior (C : Finset Vertex) (x : Vertex) (i : Fin 3)
    (hx : ∀ c∈C, x i < c i) : x∈exterior C := by
  apply coordinateRay_exterior C x i (-1) (by norm_num)
  intro n hn
  have h := hx _ hn
  simp only [coordinateRay, ite_true, neg_one_mul] at h
  omega

theorem fill_subset_coordinateBox (C : Finset Vertex) : fill C⊆coordinateBox C := by
  intro x hx i
  change x∉exterior C at hx
  constructor
  · by_contra hn
    push Not at hn
    exact hx (lower_ray_exterior C x i hn)
  · by_contra hn
    push Not at hn
    exact hx (upper_ray_exterior C x i hn)

end HardSphere.Lattice
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LiftedBadComponent
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.hilbertDomain_closed _root_.OAI.HardSphere.hilbertDomain_complete _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma liftedBadComponent_self {B : Set Vertex} {z : Vertex} (hz : z ∈ B) :
    z ∈ liftedBadComponent B z := ⟨hz, hz, .refl⟩

lemma liftedBadComponent_subset (B : Set Vertex) (z : Vertex) : liftedBadComponent B z ⊆ B :=
  fun _ h ↦ h.2.1

lemma liftedBadComponent_closed {B : Set Vertex} {z c x : Vertex}
    (hc : c ∈ liftedBadComponent B z) (hx : x ∈ B) (hcx : starStep c x) :
    x ∈ liftedBadComponent B z :=
  ⟨hc.1, hx, hc.2.2.tail ⟨hc.2.1, hx, hcx⟩⟩

lemma liftedBadComponent_connected (B : Set Vertex) (z : Vertex) :
    starConnected (liftedBadComponent B z) := by
  intro c hc x hx
  have hcx := (withinReach_symm (fun _ _ ↦ starStep_symm) hc.2.2).trans hx.2.2
  exact withinReach_invariant (fun _ hu _ hv huv ↦ liftedBadComponent_closed hu hv huv) hc hcx

lemma IsBadComponent.connected {B : Set Vertex} {C : Finset Vertex}
    (hC : IsBadComponent B C) : starConnected (↑C) := by
  obtain ⟨z, _, hz⟩ := hC
  rw [hz]
  exact liftedBadComponent_connected B z

lemma IsBadComponent.subset {B : Set Vertex} {C : Finset Vertex}
    (hC : IsBadComponent B C) : (↑C : Set Vertex) ⊆ B := by
  obtain ⟨z, _, hz⟩ := hC
  rw [hz]
  exact liftedBadComponent_subset B z

lemma IsBadComponent.closed {B : Set Vertex} {C : Finset Vertex}
    (hC : IsBadComponent B C) {c x : Vertex}
    (hc : c ∈ C) (hx : x ∈ B) (hcx : starStep c x) : x ∈ C := by
  obtain ⟨z, _, hz⟩ := hC
  change x ∈ (↑C : Set Vertex)
  rw [hz]
  exact liftedBadComponent_closed (by simpa only [← hz, Finset.mem_coe] using hc) hx hcx

lemma intervalBox_finite (x y : Vertex) : (intervalBox x y).Finite := by
  have he : intervalBox x y = Set.Icc (x ⊓ y) (x ⊔ y) := by
    ext z
    simp only [intervalBox, Set.mem_ofPred, Set.mem_Icc, Pi.le_def,
      Pi.inf_apply, Pi.sup_apply]
    exact forall_and
  rw [he]
  exact Set.finite_Icc _ _

theorem exterior_all_liftedBadComponents_reach (B : Set Vertex)
    (hfin : FiniteBadComponents B) {v w : Vertex}
    (hv : ∀ C, IsBadComponent B C → v ∈ exterior C)
    (hw : ∀ C, IsBadComponent B C → w ∈ exterior C) :
    withinReach nearestStep Bᶜ v w := by
  classical
  let Γ := intervalBox v w
  let f : {z : Vertex // z ∈ B} → Finset Vertex := fun z ↦ (hfin z z.2).toFinset
  let roots : Finset {z : Vertex // z ∈ B} :=
    ((intervalBox_finite v w).inter_of_left B).toFinset.attach.image
      (fun z ↦ ⟨z.1, (Set.Finite.mem_toFinset _).mp z.2 |>.2⟩)
  let Cs := roots.image f
  have hf (z : {z : Vertex // z ∈ B}) : IsBadComponent B (f z) :=
    ⟨z, z.2, (hfin z z.2).coe_toFinset⟩
  have hCs : ∀ C ∈ Cs, IsBadComponent B C := by
    intro C hC
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hC
    exact hf z
  have hcover : ∀ z ∈ Γ, z ∈ B → ∃ C ∈ Cs, z ∈ C := by
    intro z hzΓ hzB
    have hz : z ∈ ((intervalBox_finite v w).inter_of_left B).toFinset := by
      exact ((intervalBox_finite v w).inter_of_left B).mem_toFinset.mpr ⟨hzΓ, hzB⟩
    have hzroot : (⟨z, hzB⟩ : {z : Vertex // z ∈ B}) ∈ roots := by
      apply Finset.mem_image.mpr
      exact ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩
    refine ⟨f ⟨z, hzB⟩, Finset.mem_image.mpr ⟨⟨z, hzB⟩, hzroot, rfl⟩, ?_⟩
    exact (hfin z hzB).mem_toFinset.mpr (liftedBadComponent_self hzB)
  have hvΓ : v ∈ Γ := by intro i; exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hwΓ : w ∈ Γ := by intro i; exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hd := good_detour_reach Γ B Cs
    (fun _ h ↦ (hCs _ h).connected) (fun _ h ↦ (hCs _ h).subset)
    (fun _ h _ hc _ hx hcx ↦ (hCs _ h).closed hc hx hcx) hcover hvΓ hwΓ
    (fun _ h ↦ hv _ (hCs _ h)) (fun _ h ↦ hw _ (hCs _ h)) (intervalBox_reach v w)
  exact withinReach_mono (fun _ h ↦ h.2) hd

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma continuous_liftPoint (L : Length) : Continuous (liftPoint L) := by
  exact continuous_pi fun j ↦ continuous_quotient_mk'.comp (continuous_apply j)

lemma isCompact_microCube (L : Length) (h : ℝ) (z : Vertex) :
    IsCompact (microCube L h z) :=
  isCompact_Icc.image (continuous_liftPoint L)

lemma microCube_pathConnected (L : Length) {h : ℝ} (hh : 0 ≤ h) (z : Vertex) :
    IsPathConnected (microCube L h z) := by
  apply ((convex_Icc (𝕜 := ℝ) _ _).isPathConnected ?_).image (continuous_liftPoint L)
  refine ⟨fun j ↦ h * (z j : ℝ) - 1/2, le_rfl, ?_⟩
  intro j
  dsimp
  nlinarith

lemma goodCube_subset_slice {n : ℕ} {L : Length} {h r : ℝ} {Y : Configuration n L}
    {z : Vertex} (hz : z ∉ bad h r Y) : microCube L h z ⊆ slice r Y := by
  intro x hx hxf
  exact hz ⟨x, hx, hxf⟩

lemma retained_finiteComponents {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} {x : Torus L} (hx : x ∈ retained h r Y) :
    FiniteBadComponents (bad h r Y) := by
  by_contra hn
  exact hx (Or.inl (Or.inr hn))

lemma retained_mem_exterior {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} {x : Torus L} (hx : x ∈ retained h r Y)
    {z : Vertex} (hxz : x ∈ microCube L h z) (C : Finset Vertex)
    (hC : IsBadComponent (bad h r Y) C) : z ∈ exterior C := by
  by_contra hn
  exact hx (Or.inr ⟨C, hC, z, hn, hxz⟩)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MicroCubeCover
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma microCube_cover (L : Length) {h : ℝ} (hh : 0 < h) (x : Torus L) :
    ∃ z, x ∈ microCube L h z := by
  let y : Point := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  let z : Vertex := fun j ↦ ⌊(y j + 1/2) / h⌋
  refine ⟨z, y, ⟨?_, ?_⟩, ?_⟩
  · intro j
    have hj := (le_div_iff₀ hh).mp (Int.floor_le ((y j + 1/2) / h))
    change h * (z j : ℝ) - 1/2 ≤ y j
    dsimp [z]
    nlinarith
  · intro j
    have hj := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((y j + 1/2) / h))
    change y j ≤ h * ((z j : ℝ) + 1) - 1/2
    dsimp [z]
    nlinarith
  · ext j
    exact AddCircle.coe_equivIco

lemma lower_corner_mem {h : ℝ} (hh : 0 ≤ h) (z : Vertex) :
    (fun j ↦ h * (z j : ℝ) - 1/2) ∈ liftedCube h z := by
  refine ⟨le_rfl, ?_⟩
  intro j
  dsimp
  nlinarith

lemma step_corner_mem {h : ℝ} (hh : 0 ≤ h) (z : Vertex) (i : Fin 3) :
    (fun j ↦ h * (step z i j : ℝ) - 1/2) ∈ liftedCube h z := by
  constructor <;> intro j <;> dsimp only
  · by_cases hj : j = i
    · subst j
      rw [step_apply_same, Int.cast_add, Int.cast_one]
      nlinarith
    · rw [step_apply_ne z hj]
  · by_cases hj : j = i
    · subst j
      rw [step_apply_same, Int.cast_add, Int.cast_one]
    · rw [step_apply_ne z hj]
      nlinarith

lemma adjacent_microCubes_inter (L : Length) {h : ℝ} (hh : 0 ≤ h)
    {z w : Vertex} (hzw : nearestStep z w) :
    (microCube L h z ∩ microCube L h w).Nonempty := by
  have hf (v : Vertex) (i : Fin 3) :
      (microCube L h v ∩ microCube L h (step v i)).Nonempty := by
    let y : Point := fun j ↦ h * (step v i j : ℝ) - 1/2
    exact ⟨liftPoint L y, ⟨y, step_corner_mem hh v i, rfl⟩,
      ⟨y, lower_corner_mem hh (step v i), rfl⟩⟩
  obtain ⟨i, rfl | rfl⟩ := nearestStep_eq_step hzw
  · exact hf z i
  · simpa only [Set.inter_comm] using hf w i

lemma exterior_all_liftedBadComponents_good (B : Set Vertex) (hfin : FiniteBadComponents B)
    {z : Vertex} (hz : ∀ C, IsBadComponent B C → z ∈ exterior C) : z ∉ B := by
  intro hzB
  let C := (hfin z hzB).toFinset
  have hC : IsBadComponent B C := ⟨z, hzB, (hfin z hzB).coe_toFinset⟩
  exact (hz C hC).1 ((hfin z hzB).mem_toFinset.mpr (liftedBadComponent_self hzB))

lemma goodCubes_reach_joined {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} (hh : 0 ≤ h) {z w : Vertex}
    (hz : z ∉ bad h r Y) (hzw : withinReach nearestStep (bad h r Y)ᶜ z w)
    {x y : Torus L} (hx : x ∈ microCube L h z) (hy : y ∈ microCube L h w) :
    JoinedIn (slice r Y) x y := by
  induction hzw generalizing y with
  | refl =>
    exact ((microCube_pathConnected L hh z).joinedIn x hx y hy).mono
      (goodCube_subset_slice hz)
  | @tail w u hzw hwu ih =>
    obtain ⟨p, hpw, hpu⟩ := adjacent_microCubes_inter L hh hwu.2.2
    exact (ih hpw).trans (((microCube_pathConnected L hh u).joinedIn p hpu y hy).mono
      (goodCube_subset_slice hwu.2.1))

theorem retained_joined {n : ℕ} {L : Length} {h r : ℝ}
    {Y : Configuration n L} (hh : 0 < h) {x y : Torus L}
    (hx : x ∈ retained h r Y) (hy : y ∈ retained h r Y) :
    JoinedIn (slice r Y) x y := by
  obtain ⟨z, hxz⟩ := microCube_cover L hh x
  obtain ⟨w, hyw⟩ := microCube_cover L hh y
  have hf := retained_finiteComponents hx
  have hz := retained_mem_exterior hx hxz
  have hw := retained_mem_exterior hy hyw
  exact goodCubes_reach_joined hh.le
    (exterior_all_liftedBadComponents_good _ hf hz)
    (exterior_all_liftedBadComponents_reach _ hf hz hw) hxz hyw

end HardSphere.BathSlice

namespace HardSphere.BathSlice
open HardSphere.Lattice

attribute [local irreducible] torusDistance

lemma isClosed_bad_test {n : ℕ} (L : Length) (h r : ℝ) (z : Vertex) :
    IsClosed {Y : Configuration n L | z ∈ bad h r Y} := by
  let A : Set (Torus L × Configuration n L) :=
    {p | p.1 ∈ microCube L h z ∧ ∃ j, torusDistance L p.1 (p.2 j) ≤ r}
  have hA : IsClosed A := by
    apply IsClosed.inter ((isCompact_microCube L h z).isClosed.preimage continuous_fst)
    have he : {p : Torus L × Configuration n L | ∃ j, torusDistance L p.1 (p.2 j) ≤ r} =
        ⋃ j : Fin n, {p | torusDistance L p.1 (p.2 j) ≤ r} := by ext p; simp
    change IsClosed {p : Torus L × Configuration n L | ∃ j, torusDistance L p.1 (p.2 j) ≤ r}
    rw [he]
    apply isClosed_iUnion_of_finite
    intro j
    exact isClosed_le ((continuous_torusDistance L).comp
      (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))) continuous_const
  have he : {Y : Configuration n L | z ∈ bad h r Y} = Prod.snd '' A := by
    ext Y
    constructor
    · rintro ⟨x, hx, hxf⟩
      exact ⟨(x, Y), ⟨hx, hxf⟩, rfl⟩
    · rintro ⟨⟨x, Z⟩, hZ, he⟩
      cases he
      exact ⟨x, hZ⟩
  rw [he]
  exact isClosedMap_snd_of_compactSpace A hA

lemma measurableSet_bad_test {n : ℕ} (L : Length) (h r : ℝ) (z : Vertex) :
    MeasurableSet {Y : Configuration n L | z ∈ bad h r Y} :=
  (isClosed_bad_test L h r z).measurableSet

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BadComponent
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.configurationBorel _root_.OAI.HardSphere.configurationPathBorel _root_.OAI.HardSphere.configurationPathMeasurable _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma isBadComponent_iff (B : Set Vertex) (C : Finset Vertex) :
    IsBadComponent B C ↔ C.Nonempty ∧ (↑C : Set Vertex) ⊆ B ∧
      starConnected (↑C) ∧
      ∀ c ∈ C, ∀ x, x ∈ B → starStep c x → x ∈ C := by
  constructor
  · intro hC
    obtain ⟨z, hzB, hz⟩ := hC
    have hzC : z ∈ C := by simpa only [← hz, Finset.mem_coe] using liftedBadComponent_self hzB
    have hC : IsBadComponent B C := ⟨z, hzB, hz⟩
    exact ⟨⟨z, hzC⟩, hC.subset, hC.connected, fun _ hc _ hx hcx ↦ hC.closed hc hx hcx⟩
  · rintro ⟨⟨z, hz⟩, hsub, hconn, hclosed⟩
    refine ⟨z, hsub hz, ?_⟩
    ext w
    constructor
    · intro hw
      exact ⟨hsub hz, hsub hw, withinReach_mono hsub (hconn z hz w hw)⟩
    · intro hw
      exact withinReach_end hz
        (withinReach_invariant (fun _ hu _ hv huv ↦ hclosed _ hu _ hv huv) hz hw.2.2)

lemma finiteBadComponents_iff (B : Set Vertex) :
    FiniteBadComponents B ↔ ∀ z ∈ B, ∃ C : Finset Vertex, IsBadComponent B C ∧ z ∈ C := by
  classical
  constructor
  · intro h z hz
    exact ⟨(h z hz).toFinset, ⟨z, hz, (h z hz).coe_toFinset⟩,
      (h z hz).mem_toFinset.mpr (liftedBadComponent_self hz)⟩
  · intro h z hz
    obtain ⟨C, hC, hzC⟩ := h z hz
    apply C.finite_toSet.subset
    intro w hw
    exact withinReach_end hzC
      (withinReach_invariant (fun _ hu _ hv huv ↦ hC.closed hu hv huv) hzC hw.2.2)

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma measurable_component_test {n : ℕ} (L : Length) (h r : ℝ) (C : Finset Vertex) :
    Measurable (fun Y : Configuration n L ↦ IsBadComponent (bad h r Y) C) := by
  simp_rw [isBadComponent_iff]
  apply Measurable.and measurable_const
  apply Measurable.and
  · change Measurable (fun Y : Configuration n L ↦ ∀ z, z ∈ C → z ∈ bad h r Y)
    exact Measurable.forall fun z ↦ Measurable.imp measurable_const
      (measurableSet_setOfPred.mp (measurableSet_bad_test L h r z))
  · apply Measurable.and measurable_const
    apply Measurable.forall
    intro c
    apply Measurable.imp measurable_const
    apply Measurable.forall
    intro x
    apply Measurable.imp
    · exact measurableSet_setOfPred.mp (measurableSet_bad_test L h r x)
    · exact Measurable.imp measurable_const measurable_const

lemma measurable_finiteComponents_test {n : ℕ} (L : Length) (h r : ℝ) :
    Measurable (fun Y : Configuration n L ↦ FiniteBadComponents (bad h r Y)) := by
  simp_rw [finiteBadComponents_iff]
  apply Measurable.forall
  intro z
  apply Measurable.imp
  · exact measurableSet_setOfPred.mp (measurableSet_bad_test L h r z)
  · exact Measurable.exists fun C ↦ (measurable_component_test L h r C).and measurable_const

lemma measurable_exceptional {n : ℕ} (L : Length) (h r : ℝ) :
    Measurable (fun Y : Configuration n L ↦ exceptional h r Y) :=
  ((isOpen_allowed n L r).measurableSet.mem.not).or
    (measurable_finiteComponents_test L h r).not

theorem measurableSet_omitted_graph {n : ℕ} (L : Length) (h r : ℝ) :
    MeasurableSet {p : Configuration n L × Torus L | p.2 ∈ omitted h r p.1} := by
  apply Measurable.setOf
  apply Measurable.or ((measurable_exceptional L h r).comp measurable_fst)
  apply Measurable.exists
  intro C
  apply Measurable.and ((measurable_component_test L h r C).comp measurable_fst)
  apply Measurable.exists
  intro z
  exact Measurable.and measurable_const
    (((isCompact_microCube L h z).isClosed.measurableSet.mem).comp measurable_snd)

attribute [local irreducible] omitted

lemma measurableSet_omitted {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) :
    MeasurableSet (omitted h r Y) := by
  have hm : Measurable (fun x : Torus L ↦ (Y, x)) :=
    (measurable_const : Measurable (fun _ : Torus L ↦ Y)).prodMk measurable_id
  exact (measurableSet_omitted_graph (n := n) L h r).preimage hm

lemma measurableSet_retained {n : ℕ} {L : Length} (h r : ℝ) (Y : Configuration n L) :
    MeasurableSet (retained h r Y) := (measurableSet_omitted h r Y).compl

theorem measurable_omitted_volume {n : ℕ} (L : Length) (h r : ℝ) :
    Measurable (fun Y : Configuration n L ↦ (volume : Measure (Torus L)) (omitted h r Y)) :=
  measurable_measure_prodMk_left (measurableSet_omitted_graph L h r)

end HardSphere.BathSlice

namespace HardSphere.Lattice

theorem fill_column_meets (C : Finset Vertex) {x : Vertex} (hx : x ∈ fill C)
    (i : Fin 3) : ∃ c ∈ C, ∀ j, j ≠ i → c j = x j := by
  by_contra hn
  apply hx
  apply coordinateRay_exterior C x i 1 (by norm_num)
  intro n hc
  apply hn
  refine ⟨coordinateRay x i 1 n, hc, ?_⟩
  intro j hj
  simp [coordinateRay, hj]

end HardSphere.Lattice

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_BathPhase
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma allowed_cons {n : ℕ} {L : Length} {r : ℝ} {Y : Configuration n L} {x : Torus L}
    (hY : Y∈allowed n L r) (hx : x∈BathSlice.slice r Y) :
    Fin.cons x Y∈allowed (n+1) L r := by
  rw [allowed_iff_ne] at hY ⊢
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact (hij rfl).elim
    | succ j =>
      simpa using (lt_of_not_ge (fun h ↦ hx ⟨j,h⟩))
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      simpa [torusDistance_comm] using (lt_of_not_ge (fun h ↦ hx ⟨i,h⟩))
    | succ j => exact hY i j (fun h ↦ hij (congrArg Fin.succ h))

lemma IsGroundVector.phaseRepresentative_eq_of_joined {n : ℕ} {L : Length} {r : ℝ}
    {u : Jet n L} (hu : IsGroundVector n L r u) {x y : Configuration n L}
    (h : JoinedIn (allowed n L r) x y) :
    groundPhaseRepresentative u x=groundPhaseRepresentative u y := by
  obtain ⟨p,hp⟩ := h
  apply hu.phaseRepresentative_eq_on_connected (S:=Set.range p)
    (isPreconnected_range p.continuous) (by rintro z ⟨t,rfl⟩; exact hp t)
  · exact ⟨0,p.source⟩
  · exact ⟨1,p.target⟩

lemma IsGroundVector.retained_phaseRepresentative {n : ℕ} {L : Length} {h r : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L r u) (hh : 0<h)
    {Y : Configuration n L} {x y : Torus L}
    (hx : x∈BathSlice.retained h r Y) (hy : y∈BathSlice.retained h r Y) :
    groundPhaseRepresentative u (Fin.cons x Y)=groundPhaseRepresentative u (Fin.cons y Y) := by
  have hY : Y∈allowed n L r := by
    by_contra hn
    exact hx (Or.inl (Or.inl hn))
  have hj := BathSlice.retained_joined hh hx hy
  have hc : Continuous (fun z : Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) z Y) := by
    apply continuous_pi
    intro i
    induction i using Fin.cases <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop
  apply hu.phaseRepresentative_eq_of_joined
  exact (hj.map hc).mono (by rintro _ ⟨z,hz,rfl⟩; exact allowed_cons hY hz)

lemma commonPhase_of_ae_phase {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℂ}
    {U : Set α} {c : ℂ} (h : ∀ᵐ x ∂μ.restrict U, complexPhase (f x)=c) :
    Phase.HasCommonPhase f U μ := by
  by_cases hc : ‖c‖=1
  · refine ⟨c,hc,?_⟩
    filter_upwards [h] with x hx
    rw [←hx,complexPhase_mul_norm]
  · refine ⟨1,norm_one,?_⟩
    filter_upwards [h] with x hx
    have hz : f x=0 := by
      by_contra hn
      exact hc (hx ▸ norm_complexPhase hn)
    simp [hz]

lemma IsGroundVector.ae_retained_commonPhase {n : ℕ} {L : Length} {h r : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L r u) (hh : 0<h) :
    ∀ᵐ Y : Configuration n L ∂volume,
      Phase.HasCommonPhase (fun x ↦ u.1 (Fin.cons x Y)) (BathSlice.retained h r Y) volume := by
  have ha : ∀ᵐ X ∂volume, X∈allowed (n+1) L r →
      complexPhase (u.1 X)=groundPhaseRepresentative u X :=
    (ae_restrict_iff' (isOpen_allowed (n+1) L r).measurableSet).mp hu.ae_phaseRepresentative
  have hb := ae_ae_of_ae_prod ((cons_preserving (n:=n) L).quasiMeasurePreserving.ae ha)
  filter_upwards [hb] with Y hY
  by_cases he : (BathSlice.retained h r Y).Nonempty
  · obtain ⟨x,hx⟩ := he
    apply commonPhase_of_ae_phase volume (c:=groundPhaseRepresentative u (Fin.cons x Y))
    filter_upwards [ae_restrict_of_ae hY,ae_restrict_mem (BathSlice.measurableSet_retained h r Y)] with y hy hym
    have hYa : Y∈allowed n L r := by
      by_contra hn
      exact hx (Or.inl (Or.inl hn))
    have hys := (BathSlice.retained_joined hh hym hym).source_mem
    exact (hy (allowed_cons hYa hys)).trans (hu.retained_phaseRepresentative hh hym hx)
  · rw [not_nonempty_iff_eq_empty.mp he]
    exact ⟨1,norm_one,by simp⟩

end HardSphere

end
end

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BadGraph
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma badComponents_subset (G : SimpleGraph V) (B : Finset V) {C : Finset V}
    (hC : C∈badComponents G B) : C⊆B := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hC
  exact badComponent_subset G B x

lemma badComponents_candidate (G : SimpleGraph V) (B : Finset V) :
    badComponents G B ⊆ candidateSets G := by
  intro C hC
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hC
  simp only [candidateSets, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨x,mem_own_badComponent G B hx⟩, ?_⟩
  intro y hy z hz
  have hxy := reachable_inside_component G B ((mem_badComponent G B x y).mp hy).2
  have hxz := reachable_inside_component G B ((mem_badComponent G B x z).mp hz).2
  exact hxy.symm.trans hxz

omit [Fintype V] [DecidableEq V] in
lemma frontierHead_mem (s : ExploreState V) (h : s.2.Nonempty) :
    frontierHead s h ∈ s.2 := h.choose_spec

omit [Fintype V] in
lemma invariant_initial (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F) :
    ExploreInvariant G F r (∅,{r}) := by
  simp [ExploreInvariant,hr]

lemma invariant_step (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s) : ExploreInvariant G F r (exploreStep G F s) := by
  rcases hs with ⟨h₁,h₂,hd,hr,hclosed⟩
  by_cases h : s.2.Nonempty
  · let x := frontierHead s h
    have hx : x∈s.2 := frontierHead_mem s h
    have hxF : x∈F := h₂ hx
    have hseen : s.1∪s.2 ⊆ (insert x s.1) ∪
        ((s.2 ∪ (G.neighborFinset x ∩ F)) \ insert x s.1) := by
      intro y hy
      by_cases hyp : y∈insert x s.1
      · exact Finset.mem_union_left _ hyp
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_left _ (by
            rcases Finset.mem_union.mp hy with hy|hy
            · exact False.elim (hyp (Finset.mem_insert_of_mem hy))
            · exact hy),hyp⟩)
    simp only [exploreStep,dite_eq_left h,exploreNext]
    change ExploreInvariant G F r
      (insert x s.1, (s.2 ∪ (G.neighborFinset x ∩ F)) \ insert x s.1)
    refine ⟨Finset.insert_subset hxF h₁, ?_, (Finset.disjoint_left.mpr (fun _ hy hz ↦ (Finset.mem_sdiff.mp hz).2 hy)), hseen hr, ?_⟩
    · intro y hy
      rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hy).1 with hy|hy
      · exact h₂ hy
      · exact (Finset.mem_inter.mp hy).2
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with rfl|hy
      · by_cases hzp : z∈insert x s.1
        · exact Finset.mem_union_left _ hzp
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr
              ⟨(G.mem_neighborFinset x z).mpr hyz,hz⟩),hzp⟩)
      · exact hseen (hclosed y hy z hz hyz)
  · simpa only [exploreStep,dite_eq_right h] using
      (show ExploreInvariant G F r s from ⟨h₁,h₂,hd,hr,hclosed⟩)

lemma exploration_invariant (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F) (n : ℕ) :
    ExploreInvariant G F r (exploration G F r n) := by
  induction n with
  | zero => exact invariant_initial G F hr
  | succ n ih => exact invariant_step G F r _ ih

omit [Fintype V] in
lemma invariant_empty_frontier (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s)
    (hconn : ∀ y∈F, (badGraph G F).Reachable r y) (he : s.2=∅) : s.1=F := by
  apply Finset.Subset.antisymm hs.1
  intro y hy
  have hreach := hconn y hy
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => simpa only [he,Finset.union_empty] using hs.2.2.2.1
  | @tail y z _ hyz ih =>
      simpa only [he,Finset.union_empty] using hs.2.2.2.2 y (ih hyz.1) z hyz.2.1 hyz.2.2

lemma exploreStep_card (G : SimpleGraph V) (F : Finset V) (r : V) (s : ExploreState V)
    (hs : ExploreInvariant G F r s) (h : s.2.Nonempty) :
    (exploreStep G F s).1.card=s.1.card+1 := by
  have hx := frontierHead_mem s h
  have hn : frontierHead s h ∉ s.1 := fun hh ↦ Finset.disjoint_left.mp hs.2.2.1 hh hx
  simp only [exploreStep,dite_eq_left h,exploreNext]
  exact Finset.card_insert_of_notMem hn

lemma exploration_covers (G : SimpleGraph V) (F : Finset V) {r : V} (hr : r∈F)
    (hconn : ∀ y∈F, (badGraph G F).Reachable r y) :
    (exploration G F r F.card).1=F := by
  have hprogress (n : ℕ) : n≤(exploration G F r n).1.card ∨ (exploration G F r n).1=F := by
    induction n with
    | zero => exact Or.inl (Nat.zero_le _)
    | succ n ih =>
      have hs := exploration_invariant G F hr n
      by_cases h : (exploration G F r n).2.Nonempty
      · by_cases hc : (exploration G F r n).1=F
        · have hx := frontierHead_mem _ h
          have hp := hs.2.1 hx
          exact False.elim (Finset.disjoint_left.mp hs.2.2.1 (hc.ge hp) hx)
        · refine Or.inl ?_
          obtain hn|hn := ih
          · rw [exploration,exploreStep_card G F r _ hs h]
            omega
          · exact False.elim (hc hn)
      · apply Or.inr
        rw [exploration,exploreStep,dite_eq_right h]
        exact invariant_empty_frontier G F r _ hs hconn (Finset.not_nonempty_iff_eq_empty.mp h)
  rcases hprogress F.card with hc|hc
  · exact Finset.eq_of_subset_of_card_le (exploration_invariant G F hr F.card).1 hc
  · exact hc

lemma exploreStep_mem_possible (G : SimpleGraph V) (F : Finset V) (s : ExploreState V) :
    exploreStep G F s ∈ possibleSteps G s := by
  by_cases h : s.2.Nonempty
  · simp only [exploreStep,possibleSteps,dite_eq_left h]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_powerset.mpr (Finset.inter_subset_left),rfl⟩
  · simp only [exploreStep,possibleSteps,dite_eq_right h,Finset.mem_singleton]

lemma exploration_mem_possible (G : SimpleGraph V) (F : Finset V) (r : V) (n : ℕ) :
    exploration G F r n ∈ possibleStates G r n := by
  induction n with
  | zero => simp only [exploration,possibleStates,Finset.mem_singleton]
  | succ n ih => exact Finset.mem_biUnion.mpr ⟨_,ih,exploreStep_mem_possible G F _⟩

lemma possibleSteps_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (s : ExploreState V) :
    (possibleSteps G s).card ≤ 2^Δ := by
  by_cases h : s.2.Nonempty
  · simp only [possibleSteps,dite_eq_left h]
    calc
      _ ≤ (G.neighborFinset (frontierHead s h)).powerset.card := Finset.card_image_le
      _ = 2^(G.degree (frontierHead s h)) := by rw [Finset.card_powerset]; rfl
      _ ≤ 2^Δ := Nat.pow_le_pow_right (by omega) (hΔ _)
  · simp only [possibleSteps,dite_eq_right h,Finset.card_singleton]
    exact Nat.one_le_pow _ _ (by omega)

lemma possibleStates_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (r : V) (n : ℕ) :
    (possibleStates G r n).card ≤ (2^Δ)^n := by
  induction n with
  | zero => simp only [possibleStates,Finset.card_singleton,pow_zero,le_refl]
  | succ n ih =>
    calc
      _ ≤ ∑ s∈possibleStates G r n, (possibleSteps G s).card := Finset.card_biUnion_le
      _ ≤ ∑ _s∈possibleStates G r n, 2^Δ :=
        Finset.sum_le_sum fun s _ ↦ possibleSteps_card_le G Δ hΔ s
      _ = (possibleStates G r n).card * 2^Δ := by simp
      _ ≤ (2^Δ)^n * 2^Δ := Nat.mul_le_mul_right _ ih
      _ = (2^Δ)^(n+1) := (pow_succ _ _).symm

lemma rootedAnimals_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (r : V) (m : ℕ) :
    (rootedAnimals G r m).card ≤ (2^Δ)^m := by
  have hsub : rootedAnimals G r m ⊆ (possibleStates G r m).image Prod.fst := by
    intro F hF
    simp only [rootedAnimals,Finset.mem_filter,Finset.mem_univ,true_and] at hF
    rcases hF with ⟨hr,hm,hconn⟩
    refine Finset.mem_image.mpr ⟨exploration G F r m, exploration_mem_possible G F r m, ?_⟩
    rw [← hm]
    exact exploration_covers G F hr hconn
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans
    (possibleStates_card_le G Δ hΔ r m))

omit [Fintype V] [DecidableEq V] in
lemma badGraph_mono (G : SimpleGraph V) {S F : Finset V} (h : S⊆F) :
    badGraph G S ≤ badGraph G F := by
  intro x y hxy
  exact ⟨h hxy.1,h hxy.2.1,hxy.2.2⟩

omit [Fintype V] in
lemma internal_boundary (G : SimpleGraph V) (F S : Finset V) {r y : V}
    (hr : r∈S) (hy : y∉S) (hp : (badGraph G F).Reachable r y) :
    ∃ x∈S, ∃ z∈F, z∉S ∧ G.Adj x z := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hp
  induction hp with
  | refl => exact False.elim (hy hr)
  | @tail y z _ hyz ih =>
      by_cases h : y∈S
      · exact ⟨y,h,z,hyz.2.1,hy,hyz.2.2⟩
      · exact ih h

omit [Fintype V] in
lemma connected_insert (G : SimpleGraph V) (S : Finset V) (r : V)
    (hconn : ∀ y∈S, (badGraph G S).Reachable r y)
    {x z : V} (hx : x∈S) (hxz : G.Adj x z) :
    ∀ y∈insert z S, (badGraph G (insert z S)).Reachable r y := by
  have hmono := badGraph_mono G (Finset.subset_insert z S)
  intro y hy
  rcases Finset.mem_insert.mp hy with he|hy
  · subst y
    exact ((hconn x hx).mono hmono).trans
      (show (badGraph G (insert z S)).Adj x z from
        ⟨Finset.mem_insert_of_mem hx,Finset.mem_insert_self _ _,hxz⟩).reachable
  · exact (hconn y hy).mono hmono

lemma exists_rooted_subanimal (G : SimpleGraph V) (F : Finset V) {r : V}
    (hr : r∈F) (hconn : ∀ y∈F, (badGraph G F).Reachable r y)
    (m : ℕ) (hm : 1 ≤ m) (hmF : m ≤ F.card) :
    ∃ S⊆F, S∈rootedAnimals G r m := by
  have hex (k : ℕ) (hk : k+1≤F.card) :
      ∃ S⊆F, r∈S ∧ S.card=k+1 ∧ ∀ y∈S, (badGraph G S).Reachable r y := by
    induction k with
    | zero =>
      refine ⟨{r},Finset.singleton_subset_iff.mpr hr,Finset.mem_singleton_self _,by simp,?_⟩
      intro y hy
      have : y=r := Finset.mem_singleton.mp hy
      subst y
      exact .refl r
    | succ k ih =>
      obtain ⟨S,hSF,hrS,hcard,hSconn⟩ := ih (by omega)
      have hlt : S.card<F.card := by omega
      obtain ⟨y,hyF,hyS⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨x,hx,z,hzF,hzS,hxz⟩ := internal_boundary G F S hrS hyS (hconn y hyF)
      refine ⟨insert z S,Finset.insert_subset hzF hSF,Finset.mem_insert_of_mem hrS,
        by rw [Finset.card_insert_of_notMem hzS,hcard],connected_insert G S r hSconn hx hxz⟩
  obtain ⟨S,hS,hrS,hc,hconnS⟩ := hex (m-1) (by omega)
  refine ⟨S,hS,?_⟩
  simp only [rootedAnimals,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨hrS,by omega,hconnS⟩

end HardSphere.Lattice
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FilledRegion
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma coordinate_dist_lift_le (L : Length) (u v : ℝ) :
    dist (u : AddCircle L.val) (v : AddCircle L.val) ≤ |u - v| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

lemma card_witnessBox (h : ℝ) (c : Point) : (witnessBox h c).card = 343 := by
  unfold witnessBox
  rw [Pi.card_Icc]
  have hc (j : Fin 3) :
      (Finset.Icc (⌊(c j + 1/2) / h⌋ - 3) (⌊(c j + 1/2) / h⌋ + 3)).card = 7 := by
    rw [Int.card_Icc]
    omega
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  norm_num

lemma interval_ball_witness {h r c u : ℝ} {z : ℤ}
    (hh : 0 < h) (hr : r ≤ 2*h)
    (hul : h * z - 1/2 ≤ u) (huu : u ≤ h * ((z : ℝ)+1) - 1/2)
    (hud : |u - c| ≤ r) :
    ⌊(c + 1/2) / h⌋ - 3 ≤ z ∧ z ≤ ⌊(c + 1/2) / h⌋ + 3 := by
  have hl := (le_div_iff₀ hh).mp (Int.floor_le ((c + 1/2) / h))
  have hu := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one ((c + 1/2) / h))
  obtain ⟨hd₁, hd₂⟩ := abs_le.mp hud
  constructor
  · have he : ((⌊(c + 1/2) / h⌋ : ℤ) : ℝ) - 3 ≤ z := by nlinarith
    exact_mod_cast he
  · have he : (z : ℝ) ≤ (⌊(c + 1/2) / h⌋ : ℝ) + 3 := by nlinarith
    exact_mod_cast he

lemma ball_microCube_witness {L : Length} {J : ℕ} {h r : ℝ} (hh : 0 < h)
    (hperiod : L.val = h * J) (hr : r ≤ 2*h)
    (c : Point) {z : Vertex} {x : Torus L}
    (hx : x ∈ microCube L h z) (hd : torusDistance L x (liftPoint L c) ≤ r) :
    ∃ w ∈ witnessBox h c, torusProjection J w = torusProjection J z := by
  obtain ⟨u, hu, rfl⟩ := hx
  let k : Vertex := fun j ↦ round (L.val⁻¹ * (u j - c j))
  let w : Vertex := fun j ↦ z j - k j * (J : ℤ)
  refine ⟨w, ?_, ?_⟩
  · apply Finset.mem_Icc.mpr
    have hb (j : Fin 3) :
        ⌊(c j + 1/2) / h⌋ - 3 ≤ w j ∧ w j ≤ ⌊(c j + 1/2) / h⌋ + 3 := by
      have hdj := (CellOrbital.dist_coord_le_torusDistance L
        (liftPoint L u) (liftPoint L c) j).trans hd
      change dist (u j : AddCircle L.val) (c j : AddCircle L.val) ≤ r at hdj
      rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq] at hdj
      have hk : |(u j - (k j : ℝ) * L.val) - c j| ≤ r := by
        convert hdj using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [k]
        ring_nf
      apply interval_ball_witness hh hr (u := u j - (k j : ℝ) * L.val)
      · have hl := hu.1 j
        change h * (z j : ℝ) - 1/2 ≤ u j at hl
        dsimp [w]
        push_cast
        rw [hperiod]
        nlinarith
      · have hl := hu.2 j
        change u j ≤ h * ((z j : ℝ)+1) - 1/2 at hl
        dsimp [w]
        push_cast
        rw [hperiod]
        nlinarith
      · exact hk
    exact ⟨fun j ↦ (hb j).1, fun j ↦ (hb j).2⟩
  · ext j
    simp [torusProjection, w]

theorem ncard_ball_bad_sites_le {L : Length} {J : ℕ} {h r : ℝ} (hh : 0 < h)
    (hperiod : L.val = h * J) (hr : r ≤ 2*h) (y : Torus L) :
    (torusProjection J '' {z | ∃ x ∈ microCube L h z,
      torusDistance L x y ≤ r}).ncard ≤ 343 := by
  let c : Point := fun j ↦ (AddCircle.equivIco L.val 0 (y j)).val
  have hc : liftPoint L c = y := by ext j; exact AddCircle.coe_equivIco
  have hsub : torusProjection J '' {z | ∃ x ∈ microCube L h z,
      torusDistance L x y ≤ r} ⊆ ↑((witnessBox h c).image (torusProjection J)) := by
    rintro v ⟨z, ⟨x, hx, hd⟩, rfl⟩
    obtain ⟨w, hw, he⟩ := ball_microCube_witness hh hperiod hr c hx (by simpa [hc] using hd)
    exact Finset.mem_image.mpr ⟨w, hw, he⟩
  calc
    _ ≤ (↑((witnessBox h c).image (torusProjection J)) : Set (DiscreteTorus J)).ncard :=
      Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ((witnessBox h c).image (torusProjection J)).card := Set.ncard_coe_finset _
    _ ≤ (witnessBox h c).card := Finset.card_image_le
    _ = 343 := card_witnessBox h c

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_StarGraph
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma withinReach_star_path {D : Set Vertex} {v w : Vertex} (hv : v ∈ D)
    (h : withinReach starStep D v w) :
    ∃ p : starGraph.Walk v w, p.IsPath ∧ ∀ x ∈ p.support, x ∈ D := by
  have hr : (restrictedStarGraph D).Reachable v w :=
    (SimpleGraph.reachable_iff_reflTransGen v w).mpr h
  obtain ⟨q⟩ := hr
  let f : restrictedStarGraph D →g starGraph := ⟨id,fun {_ _} h ↦ h.2.2⟩
  have hs : ∀ {u z : Vertex} (p : (restrictedStarGraph D).Walk u z),
      u ∈ D → ∀ x ∈ p.support, x ∈ D := by
    intro u z p
    induction p with
    | nil =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact hu
    | @cons u v z huv p ih =>
      intro hu x hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact ih huv.2.1 x hx
  refine ⟨q.toPath.val.map f, SimpleGraph.Walk.IsPath.map (fun _ _ h ↦ h) q.toPath.isPath, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map] at hx
  obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
  change y = x at he
  subst x
  exact hs q.toPath.val hv y hy

lemma withinReach_star_first_entry {D A : Set Vertex} {x y : Vertex}
    (h : withinReach starStep D x y) (hxD : x ∈ D) (hx : x ∉ A) (hy : y ∈ A) :
    ∃ u v, withinReach starStep (D ∩ Aᶜ) x u ∧ u ∈ D ∧ u ∉ A ∧
      v ∈ D ∧ v ∈ A ∧ starStep u v := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hx hy).elim
  | @head z w hzw _ ih =>
    by_cases hw : w ∈ A
    · exact ⟨z,w,.refl,hxD,hx,hzw.2.1,hw,hzw.2.2⟩
    · obtain ⟨u,v,hu,huD,huA,hvD,hvA,huv⟩ := ih hzw.2.1 hw
      exact ⟨u,v,hu.head ⟨⟨hxD,hx⟩,⟨hzw.2.1,hw⟩,hzw.2.2⟩,huD,huA,hvD,hvA,huv⟩

theorem star_first_exit {D : Set Vertex} {z w : Vertex} {h d : ℝ}
    (hh : 0 < h) (hd : 0 < d) (hz : z ∈ D)
    (hp : withinReach starStep D z w) (hw : ∃ i, d ≤ h * |(w i : ℝ) - z i|) :
    ∃ v, ∃ p : starGraph.Walk z v,
      (∀ x ∈ p.support, x ∈ D ∧ ∀ i, h * |(x i : ℝ) - z i| ≤ d + h) ∧
      (∃ i, d ≤ h * |(v i : ℝ) - z i|) := by
  let A : Set Vertex := {x | ∃ i, d ≤ h * |(x i : ℝ) - z i|}
  have hzA : z ∉ A := by simpa [A] using hd
  obtain ⟨u,v,hu,_,huA,hvD,hvA,huv⟩ := withinReach_star_first_entry hp hz hzA hw
  obtain ⟨p,_,hpD⟩ := withinReach_star_path (D := D ∩ Aᶜ) ⟨hz,hzA⟩ hu
  let q : starGraph.Walk z v := p.concat huv
  refine ⟨v,q,?_,hvA⟩
  intro x hx
  have hlocal (x : Vertex) (hx : x ∉ A) (i : Fin 3) :
      h * |(x i : ℝ) - z i| < d := by
    exact lt_of_not_ge (fun hi ↦ hx ⟨i,hi⟩)
  change x ∈ (p.concat (show starGraph.Adj u v from huv)).support at hx
  rw [SimpleGraph.Walk.support_concat] at hx
  simp only [List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | he
  · exact ⟨(hpD x hx).1, fun i ↦ (hlocal x (hpD x hx).2 i).le.trans (by linarith)⟩
  · subst x
    refine ⟨hvD,fun i ↦ ?_⟩
    have hedge : |(v i : ℝ) - u i| ≤ 1 := by
      exact_mod_cast (starStep_symm huv).2 i
    calc
      h * |(v i : ℝ) - z i| ≤ h * (|(v i : ℝ) - u i| + |(u i : ℝ) - z i|) :=
        mul_le_mul_of_nonneg_left (abs_sub_le _ _ _) hh.le
      _ ≤ h * (1 + |(u i : ℝ) - z i|) := mul_le_mul_of_nonneg_left (add_le_add hedge le_rfl) hh.le
      _ ≤ d + h := by nlinarith [hlocal u huA i]

lemma star_path_span {z v : Vertex} (p : starGraph.Walk z v) (i : Fin 3) :
    |z i - v i| ≤ p.support.toFinset.card - 1 := by
  classical
  let S : Set Vertex := {x | x ∈ p.support}
  have hfin : S.Finite := p.support.finite_toSet
  let : Fintype S := hfin.fintype
  have hs : Fintype.card S = p.support.toFinset.card := by
    rw [Set.fintypeCard_eq_ncard]
    change {x | x ∈ p.support}.ncard = p.support.toFinset.card
    simpa only [List.coe_toFinset] using Set.ncard_coe_finset p.support.toFinset
  have hspan := connected_coordinate_span (starGraph.induce S)
    p.connected_induce_support.preconnected (fun x ↦ x.val) 1
    (fun x y hxy j ↦ hxy.2 j) ⟨z,p.start_mem_support⟩ ⟨v,p.end_mem_support⟩ i
  simpa only [Nat.cast_one, one_mul, hs] using hspan

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma local_projection_injective {J : ℕ} {h d : ℝ} (hh : 0 < h)
    (hwide : 2*d < h*J) (z : Vertex) :
    Set.InjOn (torusProjection J) {x | ∀ i, h * |(x i : ℝ) - z i| ≤ d} := by
  intro x hx y hy he
  ext i
  apply sub_eq_zero.mp
  apply small_multiple_zero
  · simp only [Int.cast_sub]
    exact sub_eq_zero.mpr (congrFun he i)
  · have hab : h * |(x i : ℝ) - y i| < h*J := by
      calc
        _ ≤ h * (|(x i : ℝ) - z i| + |(y i : ℝ) - z i|) := by
          apply mul_le_mul_of_nonneg_left _ hh.le
          simpa only [abs_sub_comm (z i : ℝ) (y i : ℝ)] using abs_sub_le (x i : ℝ) (z i : ℝ) (y i : ℝ)
        _ ≤ 2*d := by nlinarith [hx i, hy i]
        _ < _ := hwide
    have hc : |(x i : ℝ) - y i| < (J : ℝ) := (mul_lt_mul_iff_right₀ hh).mp hab
    exact_mod_cast hc

lemma card_witness_sites_le {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hperiod : L.val = h * J) (hr : r ≤ 2*h)
    (Y : Configuration n L) (S : Finset Vertex)
    (hinj : Set.InjOn (torusProjection J) (↑S)) (j : Fin n)
    (hw : ∀ z ∈ S, ∃ x ∈ microCube L h z, torusDistance L x (Y j) ≤ r) :
    S.card ≤ 343 := by
  have hJ : J ≠ 0 := by
    intro he
    have hp := L.property
    simp only [he, Nat.cast_zero, mul_zero] at hperiod
    linarith
  let : NeZero J := ⟨hJ⟩
  calc
    S.card = (torusProjection J '' (↑S : Set Vertex)).ncard := by
      rw [hinj.ncard_image, Set.ncard_coe_finset]
    _ ≤ (torusProjection J '' {z | ∃ x ∈ microCube L h z,
      torusDistance L x (Y j) ≤ r}).ncard :=
      Set.ncard_le_ncard (Set.image_mono hw) (Set.toFinite _)
    _ ≤ 343 := ncard_ball_bad_sites_le hh hperiod hr (Y j)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridCorner
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma torusDistance_lift_le_two {L : Length} {x y : Point} {b : ℝ} (hb : 0 ≤ b)
    (hxy : ∀ i, |x i - y i| ≤ b) :
    torusDistance L (liftPoint L x) (liftPoint L y) ≤ 2*b := by
  have hcoord (i : Fin 3) : dist ((x i : ℝ) : AddCircle L.val) (y i : AddCircle L.val) ≤ b := by
    rw [dist_eq_norm, ← AddCircle.coe_sub]
    exact (QuotientAddGroup.norm_mk_le_norm (m := x i-y i)).trans (by simpa only [Real.norm_eq_abs] using hxy i)
  unfold torusDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _i : Fin 3, b^2 := Finset.sum_le_sum fun i _ ↦
      sq_le_sq₀ dist_nonneg hb |>.mpr (hcoord i)
    _ ≤ (2*b)^2 := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num only [Nat.cast_ofNat]; nlinarith [sq_nonneg b]

lemma microCube_dist_corner {L : Length} {h d : ℝ} (hh : 0 ≤ h) (hd : 0 ≤ d)
    {z w : Vertex} (hw : ∀ i, h * |(w i : ℝ)-z i| ≤ d)
    {x : Torus L} (hx : x ∈ microCube L h w) :
    torusDistance L x (gridCorner L h z) ≤ 2*(d+h) := by
  obtain ⟨u,hu,rfl⟩ := hx
  apply torusDistance_lift_le_two (add_nonneg hd hh)
  intro i
  have hab : |h*((w i : ℝ)-z i)| ≤ d := by
    simpa only [abs_mul, abs_of_nonneg hh] using hw i
  have hl := hu.1 i
  have hr := hu.2 i
  change h*(w i : ℝ)-1/2 ≤ u i at hl
  change u i ≤ h*((w i : ℝ)+1)-1/2 at hr
  obtain ⟨ha,hb⟩ := abs_le.mp hab
  apply abs_le.mpr
  constructor <;> nlinarith

lemma microCube_dist_adjacent {L : Length} {h : ℝ} (hh : 0 ≤ h)
    {z w : Vertex} (hzw : starStep z w) {x y : Torus L}
    (hx : x ∈ microCube L h z) (hy : y ∈ microCube L h w) :
    torusDistance L x y ≤ 4*h := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  have hc := torusDistance_lift_le_two (L := L) (x := u) (y := v) (b := 2*h) (by positivity)
  rw [show 4*h = 2*(2*h) by ring]
  apply hc
  intro i
  have he : |(z i : ℝ)-w i| ≤ 1 := by exact_mod_cast hzw.2 i
  have hmul := mul_le_mul_of_nonneg_left he hh
  have hab : |h*((z i : ℝ)-w i)| ≤ h := by
    simpa only [abs_mul, abs_of_nonneg hh, mul_one] using hmul
  obtain ⟨ha,hb⟩ := abs_le.mp hab
  have huz := hu.1 i
  have huz' := hu.2 i
  have hvw := hv.1 i
  have hvw' := hv.2 i
  dsimp [liftedCube] at huz huz' hvw hvw'
  apply abs_le.mpr
  constructor <;> nlinarith

lemma adjacent_witnesses_close {n : ℕ} {L : Length} {h r : ℝ} (hh : 0 ≤ h) (hr : h ≤ r)
    (Y : Configuration n L) {z w : Vertex} (hzw : starStep z w) {i j : Fin n}
    (hi : ∃ x ∈ microCube L h z, torusDistance L x (Y i) ≤ r)
    (hj : ∃ y ∈ microCube L h w, torusDistance L y (Y j) ≤ r) :
    torusDistance L (Y i) (Y j) ≤ 6*r := by
  obtain ⟨x,hx,hxi⟩ := hi
  obtain ⟨y,hy,hyj⟩ := hj
  have hc := microCube_dist_adjacent hh hzw hx hy
  have ht := torusDistance_triangle' L (Y i) x (Y j)
  have ht' := torusDistance_triangle' L x y (Y j)
  rw [torusDistance_comm L (Y i) x] at ht
  linarith

end HardSphere.BathSlice

namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk

lemma label_boundary {α β : Type*} {G : SimpleGraph α} {u v : α} (p : G.Walk u v)
    (f : α → β) {a : β} (hu : f u = a) (hv : f v ≠ a) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ f x = a ∧ f y ≠ a := by
  induction p with
  | nil => exact (hv hu).elim
  | @cons u v w huv p ih =>
    by_cases he : f v = a
    · obtain ⟨x,hx,y,hy,hxy,hfx,hfy⟩ := ih he hv
      exact ⟨x,by simp [hx],y,by simp [hy],hxy,hfx,hfy⟩
    · exact ⟨u,by simp,v,by simp [p.start_mem_support],huv,hu,he⟩

lemma each_label_has_boundary {α β : Type*} [DecidableEq α] [DecidableEq β]
    {G : SimpleGraph α} {u v : α} (p : G.Walk u v) (f : α → β)
    (hc : 1 < (p.support.toFinset.image f).card) {a : β}
    (ha : a ∈ p.support.toFinset.image f) :
    ∃ x ∈ p.support, ∃ y ∈ p.support, G.Adj x y ∧ f x = a ∧ f y ≠ a := by
  obtain ⟨x,hx,hxa⟩ := Finset.mem_image.mp ha
  obtain ⟨b,hb,c,hc',hbc⟩ := Finset.one_lt_card.mp hc
  have hd : ∃ d ∈ p.support.toFinset.image f, d ≠ a := by
    by_cases he : b = a
    · exact ⟨c,hc',by simpa [he] using Ne.symm hbc⟩
    · exact ⟨b,hb,he⟩
  obtain ⟨d,hd,hda⟩ := hd
  obtain ⟨y,hy,hyd⟩ := Finset.mem_image.mp hd
  have hx' : x ∈ p.support := List.mem_toFinset.mp hx
  have hy' : y ∈ p.support := List.mem_toFinset.mp hy
  obtain ⟨q⟩ := p.connected_induce_support.preconnected ⟨x,hx'⟩ ⟨y,hy'⟩
  obtain ⟨s,_,t,_,hst,hsa,hta⟩ := _root_.OAI.SimpleGraph.Walk.label_boundary q
    (fun z ↦ f z.val) hxa (by simpa [hyd] using hda)
  exact ⟨s.val,s.property,t.val,t.property,hst,hsa,hta⟩

end SimpleGraph.Walk

namespace HardSphere.BathSlice
open HardSphere.Lattice

theorem first_exit_witnesses {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhr : h ≤ r) (hrh : r ≤ 2*h) (hr : r ≤ 1/4096)
    (hperiod : L.val = h * J) (hL : 10 < L.val)
    (Y : Configuration n L) {z w : Vertex}
    (hz : z ∈ bad h r Y) (hp : withinReach starStep (bad h r Y) z w)
    (hw : ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i|) :
    ∃ A : Finset (Fin n),
      (1:ℝ)/1372 ≤ r * A.card ∧
      (∀ i ∈ A, torusDistance L (Y i) (gridCorner L h z) ≤ 1) ∧
      (∀ i ∈ A, ∃ j ∈ A, j ≠ i ∧ torusDistance L (Y i) (Y j) ≤ 6*r) := by
  classical
  obtain ⟨v,p,hlocal,ih,hspan⟩ := star_first_exit hh (by norm_num : (0:ℝ)<1/4) hz hp hw
  let S := p.support.toFinset
  have hS : ∀ x ∈ S, x ∈ bad h r Y := fun x hx ↦ (hlocal x (List.mem_toFinset.mp hx)).1
  obtain ⟨x0,hx0,j0,hj0⟩ := hz
  have hex (x : Vertex) : ∃ j : Fin n, x ∈ S →
      ∃ u ∈ microCube L h x, torusDistance L u (Y j) ≤ r := by
    by_cases hx : x ∈ S
    · obtain ⟨u,hu,j,hj⟩ := hS x hx
      exact ⟨j,fun _ ↦ ⟨u,hu,hj⟩⟩
    · exact ⟨j0,fun h ↦ (hx h).elim⟩
  choose f hf using hex
  let A := S.image f
  have hinj : Set.InjOn (torusProjection J) (↑S : Set Vertex) := by
    apply (local_projection_injective hh (d := (1:ℝ)/4+h) (z := z) ?_).mono
    · intro x hx
      exact (hlocal x (List.mem_toFinset.mp hx)).2
    · linarith
  have hcount : S.card ≤ 343*A.card := by
    apply Finset.card_le_mul_card_image S 343
    intro j _
    apply card_witness_sites_le hh hperiod hrh Y _ (hinj.mono (Finset.filter_subset _ _)) j
    intro x hx
    obtain ⟨hxS,hfx⟩ := Finset.mem_filter.mp hx
    simpa only [hfx] using hf x hxS
  have hpSpan : |(v ih : ℝ)-z ih| ≤ (S.card : ℝ)-1 := by
    have he := star_path_span p ih
    rw [abs_sub_comm] at he
    exact_mod_cast he
  have hcR : (S.card : ℝ) ≤ 343*(A.card : ℝ) := by exact_mod_cast hcount
  have hlarge : (1:ℝ)/1372 ≤ r*A.card := by
    have ht := mul_le_mul_of_nonneg_left hpSpan hh.le
    have hcount' := mul_le_mul_of_nonneg_left hcR hh.le
    have hhr' := mul_le_mul_of_nonneg_right hhr (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
    nlinarith
  have htwo : 1 < A.card := by
    by_contra hn
    have hc : (A.card : ℝ) ≤ 1 := by exact_mod_cast (show A.card ≤ 1 by omega)
    have h0 : 0 ≤ r := hh.le.trans hhr
    have ht := mul_le_mul_of_nonneg_left hc h0
    nlinarith
  refine ⟨A,hlarge,?_,?_⟩
  · intro i hi
    obtain ⟨x,hx,hxi⟩ := Finset.mem_image.mp hi
    obtain ⟨u,hu,huf⟩ := hf x hx
    rw [hxi] at huf
    have hd := microCube_dist_corner hh.le (show (0:ℝ)≤1/4+h by positivity)
      (hlocal x (List.mem_toFinset.mp hx)).2 hu
    have ht := torusDistance_triangle' L (Y i) u (gridCorner L h z)
    rw [torusDistance_comm L (Y i) u] at ht
    linarith
  · intro i hi
    obtain ⟨x,hx,y,hy,hxy,hfi,hfj⟩ := _root_.OAI.SimpleGraph.Walk.each_label_has_boundary p f htwo hi
    refine ⟨f y,Finset.mem_image.mpr ⟨y,List.mem_toFinset.mpr hy,rfl⟩,hfj,?_⟩
    rw [← hfi]
    exact adjacent_witnesses_close hh.le hhr Y hxy (hf x (List.mem_toFinset.mpr hx))
      (hf y (List.mem_toFinset.mpr hy))

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmallComponent
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma small_fill_coordinate {h : ℝ} (hh : 0 ≤ h) {C : Finset Vertex}
    (hC : SmallComponent h C) {z c : Vertex} (hz : z ∈ fill C) (hc : c ∈ C)
    (i : Fin 3) : h * |(z i : ℝ) - c i| ≤ 1 := by
  obtain ⟨⟨u, hu, huz⟩, ⟨v, hv, hzv⟩⟩ := fill_subset_coordinateBox C hz i
  have hu' : (u i : ℝ) ≤ z i := by exact_mod_cast huz
  have hv' : (z i : ℝ) ≤ v i := by exact_mod_cast hzv
  have huc := hC u hu c hc i
  have hvc := hC v hv c hc i
  have huv := le_abs_self ((u i : ℝ) - c i)
  have hcu := neg_abs_le ((u i : ℝ) - c i)
  have hvv := le_abs_self ((v i : ℝ) - c i)
  rw [show h * |(z i : ℝ) - c i| = |h * ((z i : ℝ) - c i)| by
    rw [abs_mul, abs_of_nonneg hh], abs_le]
  have hm₁ := mul_le_mul_of_nonneg_left hu' hh
  have hm₂ := mul_le_mul_of_nonneg_left hv' hh
  have hm₃ := mul_le_mul_of_nonneg_left hcu hh
  have hm₄ := mul_le_mul_of_nonneg_left hvv hh
  constructor <;> nlinarith

lemma small_fill_subset_columns {L : Length} {h : ℝ} (hh : 0 ≤ h)
    {C : Finset Vertex} (hC : SmallComponent h C) :
    filledRegion L h C ⊆ ⋃ c ∈ C, microColumn L h c := by
  intro x hx
  obtain ⟨z, hz, hx⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨c, hc, hcol⟩ := fill_column_meets C hz 0
  refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
  obtain ⟨u, hu, rfl⟩ := hx
  intro j _
  apply (coordinate_dist_lift_le L (u j) (h * (c j : ℝ) + h/2 - 1/2)).trans
  have hl := hu.1 j
  have hr := hu.2 j
  change h * (z j : ℝ) - 1/2 ≤ u j at hl
  change u j ≤ h * ((z j : ℝ)+1) - 1/2 at hr
  by_cases hj : j = 0
  · subst j
    simp only [ite_true]
    have hb := small_fill_coordinate hh hC hz hc 0
    have hb' : |h * ((z 0 : ℝ) - c 0)| ≤ 1 := by
      simpa only [abs_mul, abs_of_nonneg hh] using hb
    obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb'
    apply abs_le.mpr
    constructor <;> nlinarith
  · simp only [ite_eq_right hj]
    have he := hcol j hj
    rw [← he] at hl hr
    apply abs_le.mpr
    constructor <;> nlinarith

lemma volume_microColumn_le (L : Length) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (z : Vertex) :
    (volume : Measure (Torus L)) (microColumn L h z) ≤ ENNReal.ofReal (3*h^2) := by
  unfold microColumn
  rw [volume_pi_pi]
  simp only [AddCircle.volume_closedBall]
  have hb (j : Fin 3) : ENNReal.ofReal (min L.val
      (2 * (if j = 0 then 1 + h/2 else h/2))) ≤
      (if j = 0 then ENNReal.ofReal 3 else ENNReal.ofReal h) := by
    split_ifs with hj
    · apply ENNReal.ofReal_le_ofReal
      exact (min_le_right _ _).trans (by linarith)
    · apply ENNReal.ofReal_le_ofReal
      exact (min_le_right _ _).trans (by linarith)
  calc
    _ ≤ ∏ j : Fin 3, (if j = 0 then ENNReal.ofReal 3 else ENNReal.ofReal h) :=
      Finset.prod_le_prod' fun j _ ↦ hb j
    _ = ENNReal.ofReal (3*h^2) := by
      simp [Fin.prod_univ_succ, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
        ENNReal.ofReal_mul hh, pow_two]

lemma microColumn_eq_of_projection {L : Length} {J : ℕ} {h : ℝ}
    (hperiod : L.val = h * J) {w z : Vertex}
    (he : torusProjection J w = torusProjection J z) :
    microColumn L h w = microColumn L h z := by
  have hc (j : Fin 3) :
      ((h * (w j : ℝ) + h/2 - 1/2 : ℝ) : AddCircle L.val) =
      ((h * (z j : ℝ) + h/2 - 1/2 : ℝ) : AddCircle L.val) := by
    have hj := congrFun he j
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w j) (z j) J).mp hj
    have hkr : (z j : ℝ) - w j = (J : ℝ) * k := by exact_mod_cast hk
    have hr : h * (z j : ℝ) + h/2 - 1/2 =
        (h * (w j : ℝ) + h/2 - 1/2) + (k : ℝ) * L.val := by
      rw [hperiod]
      linear_combination h * hkr
    rw [hr, AddCircle.coe_add]
    have hk0 : (((k : ℝ) * L.val : ℝ) : AddCircle L.val) = 0 := by
      rw [← zsmul_eq_mul, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero]
    rw [hk0, add_zero]
  simp only [microColumn, hc]

lemma card_bathWitnessCover_le {n : ℕ} {L : Length} (h : ℝ) (Y : Configuration n L) :
    (bathWitnessCover h Y).card ≤ 343 * n := by
  apply Finset.card_biUnion_le.trans
  simp only [card_witnessBox, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  omega

lemma bad_has_bathWitness {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ} (hh : 0 < h)
    (hperiod : L.val = h * J) (hr : r ≤ 2*h) (Y : Configuration n L)
    {z : Vertex} (hz : z ∈ bad h r Y) :
    ∃ w ∈ bathWitnessCover h Y, torusProjection J w = torusProjection J z := by
  obtain ⟨x, hx, i, hi⟩ := hz
  let c : Point := fun j ↦ (AddCircle.equivIco L.val 0 (Y i j)).val
  have hc : liftPoint L c = Y i := by ext j; exact AddCircle.coe_equivIco
  obtain ⟨w, hw, he⟩ := ball_microCube_witness hh hperiod hr c hx (by simpa [hc] using hi)
  exact ⟨w, Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩, he⟩

theorem volume_smallFills_le {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1) (hperiod : L.val = h * J) (hr : r ≤ 2*h)
    (Y : Configuration n L) :
    (volume : Measure (Torus L)) (smallFills h r Y) ≤ ENNReal.ofReal (1029*h^2*n) := by
  have hsub : smallFills h r Y ⊆ ⋃ w ∈ bathWitnessCover h Y, microColumn L h w := by
    rintro x ⟨C, hC, hs, hx⟩
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (small_fill_subset_columns hh.le hs hx)
    obtain ⟨w, hw, he⟩ := bad_has_bathWitness hh hperiod hr Y (hC.subset hc)
    refine Set.mem_iUnion₂.mpr ⟨w, hw, ?_⟩
    rwa [microColumn_eq_of_projection hperiod he]
  calc
    _ ≤ volume (⋃ w ∈ bathWitnessCover h Y, microColumn L h w) := measure_mono hsub
    _ ≤ ∑ w ∈ bathWitnessCover h Y, volume (microColumn L h w) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ bathWitnessCover h Y, ENNReal.ofReal (3*h^2) :=
      Finset.sum_le_sum fun w _ ↦ volume_microColumn_le L hh.le hh1 w
    _ = ENNReal.ofReal (((bathWitnessCover h Y).card : ℝ) * (3*h^2)) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hc : ((bathWitnessCover h Y).card : ℝ) ≤ 343*n := by
        exact_mod_cast card_bathWitnessCover_le h Y
      nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg h)]

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_FiniteScaledBox
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.Lattice

lemma finite_scaled_box {h d : ℝ} (hh : 0 < h) (z : Vertex) :
    {w : Vertex | ∀ i, h * |(w i : ℝ)-z i| ≤ d}.Finite := by
  let M : ℤ := ⌈d/h⌉
  apply (Set.finite_Icc (fun i ↦ z i-M) (fun i ↦ z i+M)).subset
  intro w hw
  constructor
  · intro i
    have ht : |(w i : ℝ)-z i| ≤ (M : ℝ) :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hw i) |>.trans (Int.le_ceil _)
    have ht' := (abs_le.mp ht).1
    exact_mod_cast (show (z i : ℝ)-(M : ℝ) ≤ w i by linarith)
  · intro i
    have ht : |(w i : ℝ)-z i| ≤ (M : ℝ) :=
      (le_div_iff₀ hh).mpr (by simpa only [mul_comm] using hw i) |>.trans (Int.le_ceil _)
    have ht' := (abs_le.mp ht).2
    exact_mod_cast (show (w i : ℝ) ≤ z i+(M : ℝ) by linarith)

lemma infinite_component_has_exit {B : Set Vertex} {z : Vertex} {h : ℝ}
    (hh : 0 < h) (hinf : ¬ (liftedBadComponent B z).Finite) :
    ∃ w, withinReach starStep B z w ∧ ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
  by_contra hn
  push Not at hn
  apply hinf
  apply (finite_scaled_box (d := (1:ℝ)/4) hh z).subset
  intro w hw i
  exact (hn w hw.2.2 i).le
end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_MicroPeriod
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma not_small_has_exit {B : Set Vertex} {C : Finset Vertex} {z : Vertex} {h : ℝ}
    (hh : 0 < h) (hC : IsBadComponent B C) (hz : z ∈ C) (hlarge : ¬ SmallComponent h C) :
    ∃ w, withinReach starStep B z w ∧ ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
  classical
  have hex : ∃ w ∈ C, ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
    by_contra hn
    push Not at hn
    apply hlarge
    intro u hu v hv i
    have hu' := hn u hu i
    have hv' := hn v hv i
    have ht := abs_sub_le (u i : ℝ) (z i) (v i)
    rw [abs_sub_comm (z i : ℝ) (v i)] at ht
    have hm := mul_le_mul_of_nonneg_left ht hh.le
    nlinarith
  obtain ⟨w,hw,i,hi⟩ := hex
  exact ⟨w,withinReach_mono hC.subset (hC.connected z hz w hw),i,hi⟩

theorem large_component_witnesses {n : ℕ} {L : Length} {J : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhr : h ≤ r) (hrh : r ≤ 2*h) (hr : r ≤ 1/4096)
    (hperiod : L.val = h * J) (hL : 10 < L.val)
    (Y : Configuration n L) {z : Vertex} (hz : z ∈ bad h r Y)
    (hlarge : ¬ (liftedBadComponent (bad h r Y) z).Finite ∨
      ∃ C, IsBadComponent (bad h r Y) C ∧ z ∈ C ∧ ¬ SmallComponent h C) :
    ∃ A : Finset (Fin n),
      (1:ℝ)/1372 ≤ r * A.card ∧
      (∀ i ∈ A, torusDistance L (Y i) (gridCorner L h z) ≤ 1) ∧
      (∀ i ∈ A, ∃ j ∈ A, j ≠ i ∧ torusDistance L (Y i) (Y j) ≤ 6*r) := by
  have hex : ∃ w, withinReach starStep (bad h r Y) z w ∧
      ∃ i, (1:ℝ)/4 ≤ h * |(w i : ℝ)-z i| := by
    rcases hlarge with hinf | ⟨C,hC,hzC,hClarge⟩
    · exact infinite_component_has_exit hh hinf
    · exact not_small_has_exit hh hC hzC hClarge
  obtain ⟨w,hp,hw⟩ := hex
  exact first_exit_witnesses hh hhr hrh hr hperiod hL Y hz hp hw

lemma microPeriod_pos {r : ℝ} (hr : 0 < r) : 0 < microPeriod r := by
  exact Nat.ceil_pos.mpr (by positivity)

lemma microMesh_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    0 < microMesh r ∧ microMesh r ≤ r ∧ r ≤ 2*microMesh r := by
  have hq : (0:ℝ) < microPeriod r := by exact_mod_cast microPeriod_pos hr
  have hceil : 1/r ≤ (microPeriod r : ℝ) := Nat.le_ceil _
  have hceil' : (microPeriod r : ℝ) < 1/r + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hcr := (div_le_iff₀ hr).mp hceil
  have hcr' := (lt_div_iff₀ hr).mp (show (microPeriod r : ℝ)-1 < 1/r by linarith)
  refine ⟨one_div_pos.mpr hq,?_,?_⟩
  · exact (div_le_iff₀ hq).mpr (by nlinarith)
  · change r ≤ 2*(1/(microPeriod r : ℝ))
    rw [← div_eq_mul_one_div]
    exact (le_div_iff₀ hq).mpr (by nlinarith)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AnimalFamily
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma animalFamily_card_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (m : ℕ) :
    (animalFamily G m).card ≤ Fintype.card V * (2^Δ)^m := by
  calc
    _ ≤ ∑ r : V, (rootedAnimals G r m).card := Finset.card_biUnion_le
    _ ≤ ∑ _r : V, (2^Δ)^m := Finset.sum_le_sum fun r _ ↦ rootedAnimals_card_le G Δ hΔ r m
    _ = _ := by simp

lemma mem_animalFamily_card (G : SimpleGraph V) (m : ℕ) {F : Finset V}
    (hF : F∈animalFamily G m) : F.card=m := by
  obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hF
  exact (Finset.mem_filter.mp hr).2.2.1

lemma largeBadComponent_contains_animal (G : SimpleGraph V) (B : Finset V)
    (m : ℕ) (hm : 1 ≤ m) (hB : LargeBadComponent G B m) :
    ∃ F∈animalFamily G m, F⊆B := by
  obtain ⟨C,hC,hmC⟩ := hB
  have hc := badComponents_candidate G B hC
  simp only [candidateSets,Finset.mem_filter,Finset.mem_univ,true_and] at hc
  obtain ⟨r,hr⟩ := hc.1
  obtain ⟨F,hFC,hF⟩ := exists_rooted_subanimal G C hr (hc.2 r hr) m hm hmC
  exact ⟨F,Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ r,hF⟩,
    hFC.trans (badComponents_subset G B hC)⟩

end HardSphere.Lattice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma gridCorner_dist_parent {L : Length} {q : ℕ} (hq : 0 < q) (z : Vertex) :
    torusDistance L (gridCorner L (1/(q:ℝ)) z) (coarseCenter L (parent q z)) ≤ 2 := by
  change torusDistance L (liftPoint L _) (liftPoint L _) ≤ 2
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have he (i : Fin 3) : (z i : ℝ) = (q:ℝ)*(parent q z i : ℝ)+((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod (z i) q).symm
  have hlo (i : Fin 3) : (0:ℝ) ≤ ((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg (z i) hqz.ne'
  have hhi (i : Fin 3) : ((z i % (q:ℤ) : ℤ) : ℝ) < q := by
    exact_mod_cast Int.emod_lt_of_pos (z i) hqz
  have hbound (i : Fin 3) : |1/(q:ℝ)*(z i : ℝ)-1/2 - ((parent q z i : ℝ)+1/2)| ≤ 1 := by
    apply abs_le.mpr
    have hmul : (q:ℝ)*(1/(q:ℝ)*(z i : ℝ)- (parent q z i : ℝ)) = ((z i % (q:ℤ) : ℤ) : ℝ) := by
      rw [mul_sub]; field_simp; nlinarith [he i]
    constructor <;> nlinarith [hlo i,hhi i]
  simpa only [mul_one] using torusDistance_lift_le_two (by norm_num : (0:ℝ)≤1) hbound

lemma witnesses_pairClose {m : ℕ} {L : Length} {r s : ℝ} {Y : Configuration m L}
    {z : Vertex} {q : ℕ} (hq : 0 < q) (hrs : 6*r ≤ s) {A : Finset (Fin m)}
    (hnear : ∀ i ∈ A, torusDistance L (Y i) (gridCorner L (1/(q:ℝ)) z) ≤ 1)
    (hpartner : ∀ i ∈ A, ∃ j ∈ A, j ≠ i ∧ torusDistance L (Y i) (Y j) ≤ 6*r) :
    A ⊆ pairCloseLabels L s (coarseCenter L (parent q z)) Y := by
  classical
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i,?_,?_⟩
  · have hc := gridCorner_dist_parent (L := L) hq z
    have ht := torusDistance_triangle' L (Y i) (gridCorner L (1/(q:ℝ)) z)
      (coarseCenter L (parent q z))
    have hn := hnear i hi
    linarith
  · obtain ⟨j,_,hji,hj⟩ := hpartner i hi
    exact ⟨j,hji,hj.trans hrs⟩

lemma pairClose_card_mono {m n : ℕ} (L : Length) (s : ℝ) (v : Torus L)
    (e : Fin m ↪ Fin n) (X : Configuration n L) :
    (pairCloseLabels L s v (fun i ↦ X (e i))).card ≤ (pairCloseLabels L s v X).card := by
  classical
  have hs : (pairCloseLabels L s v (fun i ↦ X (e i))).map e ⊆ pairCloseLabels L s v X := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨_,hv,k,hkj,hk⟩ := Finset.mem_filter.mp hj
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,hv,e k,fun he ↦ hkj (e.injective he),hk⟩
  simpa only [Finset.card_map] using Finset.card_le_card hs

theorem large_component_forces_close {m n K : ℕ} {L : Length} {r s D θ : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hrs : 6*r ≤ s) (hθ : θ*D ≤ 1/(1372*r))
    (e : Fin m ↪ Fin n) (X : Configuration n L) {z : Vertex}
    (hz : z ∈ bad (microMesh r) r (fun i ↦ X (e i)))
    (hlarge : ¬ (liftedBadComponent (bad (microMesh r) r (fun i ↦ X (e i))) z).Finite ∨
      ∃ C, IsBadComponent (bad (microMesh r) r (fun i ↦ X (e i))) C ∧ z ∈ C ∧
        ¬ SmallComponent (microMesh r) C) :
    θ*D ≤ ((pairCloseLabels L s (coarseCenter L (parent (microPeriod r) z)) X).card:ℝ) := by
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨hh,hhr,hrh⟩ := microMesh_bounds hr hr1
  have hq : (microPeriod r : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast microPeriod_pos hr)
  have hperiod : L.val = microMesh r * ((K*microPeriod r : ℕ) : ℝ) := by
    rw [hLK,Nat.cast_mul,microMesh]; field_simp
  obtain ⟨A,hA,hnear,hpartner⟩ := large_component_witnesses hh hhr hrh hrsmall
    hperiod hL (fun i ↦ X (e i)) hz hlarge
  have hsub := witnesses_pairClose (microPeriod_pos hr) hrs hnear hpartner
  have hcard : (A.card:ℝ) ≤ ((pairCloseLabels L s
      (coarseCenter L (parent (microPeriod r) z)) X).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (pairClose_card_mono L s _ e X)
  apply hθ.trans
  have hmul := mul_le_mul_of_nonneg_left hcard hr.le
  apply (div_le_iff₀ (by positivity : (0:ℝ)<1372*r)).mpr
  nlinarith

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ParentStep
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
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
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma parent_step {q : ℕ} (hq : 0 < q) {z w : Vertex} (hzw : starStep z w) :
    parent q z = parent q w ∨ rangeStep 1 (parent q z) (parent q w) := by
  by_cases he : parent q z = parent q w
  · exact Or.inl he
  right
  refine ⟨he,fun i ↦ ?_⟩
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have hb := abs_le.mp (hzw.2 i)
  have hu : z i ≤ w i+q := by omega
  have hv : w i ≤ z i+q := by omega
  have hdu := Int.ediv_le_ediv hqz hu
  have hdv := Int.ediv_le_ediv hqz hv
  rw [Int.add_ediv_of_dvd_right (dvd_refl (q:ℤ)), Int.ediv_self hqz.ne'] at hdu hdv
  exact abs_le.mpr ⟨by change -(1:ℤ) ≤ z i/(q:ℤ)-w i/(q:ℤ); omega,
    by change z i/(q:ℤ)-w i/(q:ℤ) ≤ (1:ℤ); omega⟩

lemma parent_fiber_finite {q : ℕ} (hq : 0 < q) (v : Vertex) :
    {z | parent q z=v}.Finite := by
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  apply (Set.finite_Icc (fun i ↦ (q:ℤ)*v i) (fun i ↦ (q:ℤ)*v i+q)).subset
  intro z hz
  constructor <;> intro i
  · change (q:ℤ)*v i ≤ z i
    have he := Int.mul_ediv_add_emod (z i) q
    have hi : z i/(q:ℤ)=v i := congrFun hz i
    have hn := Int.emod_nonneg (z i) hqz.ne'
    rw [hi] at he
    omega
  · change z i ≤ (q:ℤ)*v i+q
    have he := Int.mul_ediv_add_emod (z i) q
    have hi : z i/(q:ℤ)=v i := congrFun hz i
    have hn := Int.emod_lt_of_pos (z i) hqz
    rw [hi] at he
    omega

lemma parent_preimage_finite {q : ℕ} (hq : 0 < q) (C : Finset Vertex) :
    ((parent q) ⁻¹' (↑C : Set Vertex)).Finite := by
  have hf : (⋃ v ∈ (↑C : Set Vertex), {z | parent q z=v}).Finite :=
    C.finite_toSet.biUnion (fun v _ ↦ parent_fiber_finite hq v)
  apply hf.subset
  intro z hz
  exact Set.mem_iUnion.mpr ⟨parent q z,Set.mem_iUnion.mpr ⟨hz,rfl⟩⟩

lemma parent_reach {q : ℕ} (hq : 0 < q) {D E : Set Vertex}
    (hDE : ∀ z ∈ D, parent q z ∈ E) {z w : Vertex}
    (hp : withinReach starStep D z w) :
    withinReach (rangeStep 1) E (parent q z) (parent q w) := by
  induction hp with
  | refl => exact .refl
  | @tail u v _ huv ih =>
    rcases parent_step hq huv.2.2 with he | he
    · simpa only [←he] using ih
    · exact ih.tail ⟨hDE u huv.1,hDE v huv.2.1,he⟩

lemma parent_projection_reachable {q K : ℕ} (hq : 0 < q) (hK : 2 < K)
    {D : Set Vertex} {B : Finset (DiscreteTorus K)}
    (hDB : ∀ z ∈ D, torusProjection K (parent q z) ∈ B) {z w : Vertex}
    (hp : withinReach starStep D z w) :
    (badGraph (torusRangeGraph K 1) B).Reachable
      (torusProjection K (parent q z)) (torusProjection K (parent q w)) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hp with
  | refl => exact .refl
  | @tail u v _ huv ih =>
    rcases parent_step hq huv.2.2 with he | he
    · simpa only [←he] using ih
    · exact ih.tail ⟨hDB u huv.1,hDB v huv.2.1,
        rangeStep_projection (by simpa only [mul_one] using hK) he⟩
end HardSphere.BathSlice

namespace HardSphere.BathSlice
open HardSphere.Lattice

theorem parent_component_lift {q K : ℕ} [NeZero K] (hq : 0 < q) (hK : 2 < K)
    {D : Set Vertex} (hD : starConnected D) {z : Vertex} (hz : z ∈ D)
    (B : Finset (DiscreteTorus K)) (hDB : ∀ w ∈ D, torusProjection K (parent q w) ∈ B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))).card < K) :
    ∃ C : Finset Vertex,
      (∀ w ∈ D, parent q w ∈ C) ∧
      Set.BijOn (torusProjection K) (↑C)
        (↑(badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z)))) ∧
      (∀ u∈C, ∀ v∈C, ∀ i, |u i-v i| ≤
        ((badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))).card:ℤ)-1) := by
  classical
  let S := badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))
  have hmem : ∀ w ∈ D, torusProjection K (parent q w) ∈ S := by
    intro w hw
    apply (mem_badComponent _ _ _ _).mpr
    exact ⟨hDB w hw,parent_projection_reachable hq hK hDB (hD z hz w hw)⟩
  obtain ⟨C,hC,hbij,hspan⟩ := small_periodic_lifts (a := 1)
    (by simpa only [mul_one] using hK) S (by simpa only [one_mul] using hsmall)
    (badComponent_preconnected _ _ _) (parent q z) (hmem z hz)
  refine ⟨C,?_,hbij,?_⟩
  · intro w hw
    change parent q w ∈ (↑C : Set Vertex)
    rw [hC]
    exact ⟨hmem w hw,parent_reach hq (fun u hu ↦ hmem u hu) (hD z hz w hw)⟩
  · simpa only [Nat.cast_one,one_mul] using hspan

theorem finite_of_parent_component_small {q K : ℕ} [NeZero K] (hq : 0 < q) (hK : 2 < K)
    {D : Set Vertex} (hD : starConnected D) {z : Vertex} (hz : z ∈ D)
    (B : Finset (DiscreteTorus K)) (hDB : ∀ w ∈ D, torusProjection K (parent q w) ∈ B)
    (hsmall : (badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))).card < K) :
    D.Finite := by
  obtain ⟨C,hC,_,_⟩ := parent_component_lift hq hK hD hz B hDB hsmall
  exact (parent_preimage_finite hq C).subset hC

end HardSphere.BathSlice

namespace HardSphere.Lattice
lemma liftedBadComponent_eq_of_mem {B : Set Vertex} {z w : Vertex}
    (hw : w ∈ liftedBadComponent B z) : liftedBadComponent B w = liftedBadComponent B z := by
  ext v
  constructor
  · intro hv
    exact ⟨hw.1,hv.2.1,hw.2.2.trans hv.2.2⟩
  · intro hv
    exact ⟨hw.2.1,hv.2.1,(withinReach_symm (fun _ _ ↦ starStep_symm) hw.2.2).trans hv.2.2⟩

lemma own_badComponent_card_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : Finset V) {M : ℕ} (he : ¬LargeBadComponent G B M)
    {v : V} (hv : v ∈ B) : (badComponent G B v).card < M := by
  apply lt_of_not_ge
  intro h
  exact he ⟨_,Finset.mem_image.mpr ⟨v,hv,rfl⟩,h⟩
end HardSphere.Lattice

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LargeParentMarked
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

theorem finite_components_of_no_large {n q K M : ℕ} [NeZero K] {L : Length} {h r : ℝ}
    (hq : 0 < q) (hK : 2 < K) (hMK : M ≤ K) (Y : Configuration n L)
    (B : Finset (DiscreteTorus K)) (hmark : LargeParentMarked q h r Y B)
    (he : ¬LargeBadComponent (torusRangeGraph K 1) B M) :
    FiniteBadComponents (bad h r Y) := by
  intro z hz
  by_contra hinf
  let D := liftedBadComponent (bad h r Y) z
  have hzD : z ∈ D := liftedBadComponent_self hz
  have hDB : ∀ w ∈ D, torusProjection K (parent q w) ∈ B := by
    intro w hw
    apply hmark w hw.2.1 (Or.inl ?_)
    rw [liftedBadComponent_eq_of_mem hw]
    exact hinf
  exact hinf (finite_of_parent_component_small hq hK
    (liftedBadComponent_connected _ _) hzD B hDB
    ((own_badComponent_card_lt _ B he (hDB z hzD)).trans_le hMK))

theorem large_finite_parent_lift {n q K M : ℕ} [NeZero K] {L : Length} {h r : ℝ}
    (hq : 0 < q) (hK : 2 < K) (hMK : M ≤ K) (Y : Configuration n L)
    (B : Finset (DiscreteTorus K)) (hmark : LargeParentMarked q h r Y B)
    (he : ¬LargeBadComponent (torusRangeGraph K 1) B M)
    {C : Finset Vertex} (hC : IsBadComponent (bad h r Y) C)
    (hlarge : ¬SmallComponent h C) {z : Vertex} (hz : z ∈ C) :
    let S := badComponent (torusRangeGraph K 1) B (torusProjection K (parent q z))
    1 ≤ S.card ∧ S ∈ rootedAnimals (torusRangeGraph K 1)
      (torusProjection K (parent q z)) S.card ∧ S ⊆ B ∧
      ∀ w ∈ C, ∀ i, |parent q w i-parent q z i| ≤ (S.card:ℤ)-1 := by
  classical
  let v := torusProjection K (parent q z)
  let S := badComponent (torusRangeGraph K 1) B v
  have hDB : ∀ w ∈ C, torusProjection K (parent q w) ∈ B :=
    fun w hw ↦ hmark w (hC.subset hw) (Or.inr ⟨C,hC,hw,hlarge⟩)
  have hv : v ∈ B := hDB z hz
  have hvS : v ∈ S := mem_own_badComponent _ B hv
  have hc : 1 ≤ S.card := Finset.one_le_card.mpr ⟨v,hvS⟩
  obtain ⟨T,hT,_,hspan⟩ := parent_component_lift hq hK hC.connected hz B hDB
    ((own_badComponent_card_lt _ B he hv).trans_le hMK)
  refine ⟨hc,?_,badComponent_subset _ B v,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hvS,rfl,?_⟩
    intro w hw
    exact reachable_inside_component _ B ((mem_badComponent _ B v w).mp hw).2
  · intro w hw i
    exact hspan _ (hT w hw) _ (hT z hz) i

lemma volume_rootBox_le (L : Length) (v : Vertex) {R : ℝ} (hR : 0 ≤ R) :
    (volume : Measure (Torus L)) (rootBox L v R) ≤ ENNReal.ofReal ((2*R)^3) := by
  unfold rootBox
  rw [volume_pi_pi]
  simp only [AddCircle.volume_closedBall]
  calc
    _ ≤ ∏ _i : Fin 3, ENNReal.ofReal (2*R) := by
      exact Finset.prod_le_prod' fun _ _ ↦ ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = _ := by simp [ENNReal.ofReal_pow (by positivity : 0 ≤ 2*R)]

lemma scaled_parent_bounds {q : ℕ} (hq : 0 < q) (z : Vertex) (i : Fin 3) :
    (parent q z i : ℝ) ≤ 1/(q:ℝ)*(z i : ℝ) ∧
    1/(q:ℝ)*((z i : ℝ)+1) ≤ (parent q z i : ℝ)+1 := by
  have hqr : (0:ℝ)<q := by exact_mod_cast hq
  have hqz : (0:ℤ)<q := by exact_mod_cast hq
  have he : (z i : ℝ) = (q:ℝ)*(parent q z i : ℝ)+((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod (z i) q).symm
  have hlo : (0:ℝ) ≤ ((z i % (q:ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.emod_nonneg (z i) hqz.ne'
  have hhi : ((z i % (q:ℤ) : ℤ) : ℝ)+1 ≤ q := by
    exact_mod_cast (show z i % (q:ℤ)+1 ≤ q by have := Int.emod_lt_of_pos (z i) hqz; omega)
  constructor
  · rw [one_div,←div_eq_inv_mul]
    apply (le_div_iff₀ hqr).mpr
    nlinarith
  · rw [one_div,←div_eq_inv_mul]
    apply (div_le_iff₀ hqr).mpr
    nlinarith

lemma filledRegion_subset_rootBox {L : Length} {q : ℕ} (hq : 0 < q)
    (C : Finset Vertex) (v : Vertex) {m : ℕ}
    (hspan : ∀ w ∈ C, ∀ i, |parent q w i-v i| ≤ (m:ℤ)) :
    filledRegion L (1/(q:ℝ)) C ⊆ rootBox L v (m+1) := by
  intro x hx
  obtain ⟨z,hz,ux,hux,rfl⟩ := Set.mem_iUnion₂.mp hx
  intro i _
  apply (coordinate_dist_lift_le L (ux i) ((v i : ℝ)+1/2)).trans
  apply abs_le.mpr
  obtain ⟨⟨cl,hcl,hclz⟩,⟨cu,hcu,hzcu⟩⟩ := fill_subset_coordinateBox C hz i
  have hbl := (scaled_parent_bounds hq cl i).1
  have hbu := (scaled_parent_bounds hq cu i).2
  have hsl : - (m:ℝ) ≤ (parent q cl i : ℝ)-(v i : ℝ) := by
    exact_mod_cast (abs_le.mp (hspan cl hcl i)).1
  have hsu : (parent q cu i : ℝ)-(v i : ℝ) ≤ (m:ℝ) := by
    exact_mod_cast (abs_le.mp (hspan cu hcu i)).2
  have hclz' : (cl i : ℝ) ≤ z i := by exact_mod_cast hclz
  have hzcu' : (z i : ℝ) ≤ cu i := by exact_mod_cast hzcu
  have hlo := hux.1 i
  have hhi := hux.2 i
  have hqnn : 0 ≤ 1/(q:ℝ) := by positivity
  constructor <;> dsimp [Point,liftedCube] at * <;> nlinarith

lemma coarseCenter_eq_of_projection {L : Length} {K : ℕ}
    (hLK : L.val=(K:ℝ)) {w z : Vertex}
    (he : torusProjection K w = torusProjection K z) :
    coarseCenter L w = coarseCenter L z := by
  ext j
  change (((w j : ℝ)+1/2 : ℝ) : AddCircle L.val) =
    (((z j : ℝ)+1/2 : ℝ) : AddCircle L.val)
  obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (w j) (z j) K).mp (congrFun he j)
  have hkr : (z j : ℝ)-(w j : ℝ)=(K:ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hr : (z j : ℝ)+1/2=((w j : ℝ)+1/2)+(k:ℝ)*L.val := by
    rw [hLK]; linarith
  rw [hr]
  have hz : (((k:ℝ)*L.val:ℝ) : AddCircle L.val)=0 := by
    rw [←zsmul_eq_mul,AddCircle.coe_zsmul,AddCircle.coe_period,smul_zero]
  simp only [AddCircle.coe_add,hz,add_zero]

lemma rootBox_eq_of_projection {L : Length} {K : ℕ}
    (hLK : L.val=(K:ℝ)) {w z : Vertex}
    (he : torusProjection K w = torusProjection K z) (R : ℝ) :
    rootBox L w R = rootBox L z R := by
  have hc := coarseCenter_eq_of_projection hLK he
  change (Set.univ.pi fun i ↦ Metric.closedBall (coarseCenter L w i) R) =
    (Set.univ.pi fun i ↦ Metric.closedBall (coarseCenter L z i) R)
  rw [hc]

lemma siteRep_projection {K : ℕ} [NeZero K] (v : DiscreteTorus K) :
    torusProjection K (siteRep v)=v := by
  ext i
  change (((v i).val:ℤ):ZMod K)=v i
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

theorem actual_large_parent_marked {m n K : ℕ} [NeZero K] {L : Length} {r s D θ : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hrs : 6*r ≤ s) (hθ : θ*D ≤ 1/(1372*r))
    (e : Fin m ↪ Fin n) (X : Configuration n L) :
    LargeParentMarked (microPeriod r) (microMesh r) r (fun i ↦ X (e i))
      (closeSet (K := K) L s (θ*D) X) := by
  intro z hz hlarge
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have hc : siteCenter L (torusProjection K (parent (microPeriod r) z)) =
      coarseCenter L (parent (microPeriod r) z) :=
    coarseCenter_eq_of_projection hLK (siteRep_projection _)
  rw [hc]
  exact large_component_forces_close hr hrsmall hL hLK hrs hθ e X hz hlarge

theorem omitted_subset_small_and_boxes {n q K M : ℕ} [NeZero K] {L : Length} {r : ℝ}
    (hq : 0 < q) (hK : 2 < K) (hLK : L.val=(K:ℝ)) (hMK : M ≤ K)
    (Y : Configuration n L) (hY : Y ∈ allowed n L r)
    (B : Finset (DiscreteTorus K)) (hmark : LargeParentMarked q (1/(q:ℝ)) r Y B)
    (he : ¬LargeBadComponent (torusRangeGraph K 1) B M) :
    omitted (1/(q:ℝ)) r Y ⊆ smallFills (1/(q:ℝ)) r Y ∪ largeBoxUnion L B := by
  intro x hx
  rcases hx with hex | ⟨C,hC,z,hz,hxz⟩
  · exact (hex.elim (fun h ↦ h hY) (fun h ↦ h
      (finite_components_of_no_large hq hK hMK Y B hmark he))).elim
  by_cases hsmall : SmallComponent (1/(q:ℝ)) C
  · exact Or.inl ⟨C,hC,hsmall,Set.mem_iUnion₂.mpr ⟨z,hz,hxz⟩⟩
  right
  obtain ⟨w,hw,_⟩ := fill_column_meets C hz 0
  let v := torusProjection K (parent q w)
  let S := badComponent (torusRangeGraph K 1) B v
  obtain ⟨hSpos,hSan,hSB,hspan⟩ := large_finite_parent_lift hq hK hMK Y B hmark he hC hsmall hw
  change 1 ≤ S.card at hSpos
  change S ∈ rootedAnimals (torusRangeGraph K 1) v S.card at hSan
  change S ⊆ B at hSB
  change ∀ u ∈ C, ∀ i, |parent q u i-parent q w i| ≤ (S.card:ℤ)-1 at hspan
  have hxbox : x ∈ rootBox L (parent q w) ((S.card:ℝ)+1) := by
    apply filledRegion_subset_rootBox hq C (parent q w) (m := S.card)
      (fun u hu i ↦ (hspan u hu i).trans (by omega))
    exact Set.mem_iUnion₂.mpr ⟨z,hz,hxz⟩
  have hrad : ((S.card-1:ℕ):ℝ)+2=(S.card:ℝ)+1 := by
    rw [Nat.cast_sub hSpos]; push_cast; ring
  change x ∈ ⋃ m : ℕ, ⋃ v : DiscreteTorus K, ⋃ S ∈ rootedAnimals (torusRangeGraph K 1) v (m+1),
    ⋃ (_ : S ⊆ B), rootBox L (siteRep v) ((m:ℝ)+2)
  refine Set.mem_iUnion.mpr ⟨S.card-1,Set.mem_iUnion.mpr ⟨v,
    Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨?_,Set.mem_iUnion.mpr ⟨hSB,?_⟩⟩⟩⟩⟩
  · simpa only [Nat.sub_add_cancel hSpos] using hSan
  · rw [hrad,rootBox_eq_of_projection hLK (siteRep_projection v)]
    exact hxbox

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_TorusNear
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice

lemma torusOffsets_card (R : ℕ) : (torusOffsets R).card=(2*R+1)^3 := by
  have hcard : (Finset.Icc (-(R:ℤ)) R).card=2*R+1 := by rw [Int.card_Icc]; omega
  simp only [torusOffsets,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma torusNear_mem_image {K R : ℕ} (x y : DiscreteTorus K) :
    torusNear K R x y ↔ y∈(torusOffsets R).image (fun d ↦ x+torusProjection K d) := by
  constructor
  · rintro ⟨d,hd,he⟩
    refine Finset.mem_image.mpr ⟨d,?_,?_⟩
    · simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd
    · ext i; exact (he i).symm
  · intro hy
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨d,?_,fun i ↦ rfl⟩
    simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd

lemma torusNear_ball_card {K : ℕ} [NeZero K] (R : ℕ) (x : DiscreteTorus K) :
    (Finset.univ.filter (torusNear K R x)).card≤(2*R+1)^3 := by
  have he : Finset.univ.filter (torusNear K R x)=(torusOffsets R).image (fun d ↦ x+torusProjection K d) := by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,torusNear_mem_image]
  rw [he]
  exact Finset.card_image_le.trans (torusOffsets_card R).le

lemma torusRange_degree {K : ℕ} [NeZero K] (a : ℕ) (x : DiscreteTorus K) :
    (torusRangeGraph K a).degree x≤(2*a+1)^3 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  apply (Finset.card_le_card (t := Finset.univ.filter (torusNear K a x)) ?_).trans (torusNear_ball_card a x)
  intro y hy
  have hxy : (torusRangeGraph K a).Adj x y := by simpa using hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy.2⟩

open MeasureTheory
variable {W V : Type*} [MeasurableSpace W] [Fintype V] [DecidableEq V]

theorem largeBadComponent_measure (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (μ : Measure W) (B : W → Finset V) (p : ℝ≥0∞)
    (hbad : ∀ A : Finset V, μ {ω | A⊆B ω} ≤ p^A.card) (m : ℕ) (hm : 1 ≤ m) :
    μ {ω | LargeBadComponent G (B ω) m} ≤
      (Fintype.card V : ℝ≥0∞) * (((2^Δ:ℕ):ℝ≥0∞)*p)^m := by
  classical
  have hsub : {ω | LargeBadComponent G (B ω) m} ⊆
      ⋃ A∈animalFamily G m, {ω | A⊆B ω} := by
    intro ω hω
    obtain ⟨A,hA,hAB⟩ := largeBadComponent_contains_animal G (B ω) m hm hω
    exact Set.mem_iUnion₂.mpr ⟨A,hA,hAB⟩
  calc
    _ ≤ μ (⋃ A∈animalFamily G m, {ω | A⊆B ω}) := measure_mono hsub
    _ ≤ ∑ A∈animalFamily G m, μ {ω | A⊆B ω} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _A∈animalFamily G m, p^m := by
      apply Finset.sum_le_sum
      intro A hA
      simpa only [mem_animalFamily_card G m hA] using hbad A
    _ = ((animalFamily G m).card:ℝ≥0∞)*p^m := by simp
    _ ≤ ((Fintype.card V*(2^Δ)^m:ℕ):ℝ≥0∞)*p^m := by
      apply mul_le_mul' _ le_rfl
      exact_mod_cast animalFamily_card_le G Δ hΔ m
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow,mul_pow]; ring

lemma measurable_animalCost (G : SimpleGraph V) (B : W → Finset V)
    (hB : Measurable B) (w : ℕ → ℝ≥0∞) : Measurable (fun ω ↦ animalCost G (B ω) w) := by
  apply Measurable.tsum
  intro m
  apply Finset.measurable_sum
  intro v _
  apply Finset.measurable_sum
  intro A _
  apply Measurable.ite _ measurable_const measurable_const
  have hm : MeasurableSet {C : Finset V | A⊆C} := (Set.to_countable _).measurableSet
  exact hm.preimage hB

theorem animalCost_mean_le (G : SimpleGraph V) (Δ : ℕ)
    (hΔ : ∀ x, G.degree x≤Δ) (μ : Measure W) (B : W → Finset V)
    (hB : Measurable B) (p : ℝ≥0∞)
    (hbad : ∀ A : Finset V, μ {ω | A⊆B ω} ≤ p^A.card) (w : ℕ → ℝ≥0∞) :
    (∫⁻ ω, animalCost G (B ω) w ∂μ) ≤
      (Fintype.card V:ℝ≥0∞) * ∑' m : ℕ, w (m+1) * (((2^Δ:ℕ):ℝ≥0∞)*p)^(m+1) := by
  classical
  have hm (A : Finset V) : MeasurableSet {ω | A⊆B ω} :=
    (Set.to_countable {C : Finset V | A⊆C}).measurableSet.preimage hB
  have hi (A : Finset V) (t : ℝ≥0∞) : Measurable (fun ω ↦ if A⊆B ω then t else 0) :=
    Measurable.ite (hm A) measurable_const measurable_const
  unfold animalCost
  rw [lintegral_tsum (fun m ↦ (Finset.measurable_sum _ fun v _ ↦
    Finset.measurable_sum _ fun A _ ↦ hi A _).aemeasurable)]
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro m
  rw [lintegral_finsetSum _ (fun v _ ↦ Finset.measurable_sum _ fun A _ ↦ hi A _)]
  calc
    _ ≤ ∑ _v : V, (((2^Δ:ℕ):ℝ≥0∞)^(m+1)) * (w (m+1)*p^(m+1)) := by
      apply Finset.sum_le_sum
      intro v _
      rw [lintegral_finsetSum _ (fun A _ ↦ hi A _)]
      calc
        _ ≤ ∑ _A∈rootedAnimals G v (m+1), w (m+1)*p^(m+1) := by
          apply Finset.sum_le_sum
          intro A hA
          have hc : A.card=m+1 := (Finset.mem_filter.mp hA).2.2.1
          have heq : (fun ω ↦ if A⊆B ω then w (m+1) else 0) =
              {ω | A⊆B ω}.indicator (fun _ ↦ w (m+1)) := by
            ext ω
            simp only [Set.indicator_apply, Set.mem_ofPred_eq]
          rw [heq,lintegral_indicator_const (hm A)]
          exact mul_le_mul' le_rfl (by simpa only [hc] using hbad A)
        _ = ((rootedAnimals G v (m+1)).card:ℝ≥0∞)*(w (m+1)*p^(m+1)) := by simp
        _ ≤ _ := by
          apply mul_le_mul' _ le_rfl
          exact_mod_cast rootedAnimals_card_le G Δ hΔ v (m+1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_pow]; ring

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BoxWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma volume_largeBoxUnion_le {K : ℕ} [NeZero K] (L : Length) (B : Finset (DiscreteTorus K)) :
    (volume : Measure (Torus L)) (largeBoxUnion L B) ≤ animalCost (torusRangeGraph K 1) B boxWeight := by
  classical
  unfold largeBoxUnion animalCost
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro m
  apply (measure_iUnion_le _).trans
  rw [tsum_fintype]
  apply Finset.sum_le_sum
  intro v _
  apply (measure_biUnion_finset_le _ _).trans
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A⊆B
  · simp only [hA,Set.iUnion_true,ite_true]
    simpa only [boxWeight,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      volume_rootBox_le L (siteRep v) (by positivity : (0:ℝ)≤(m:ℝ)+2)
  · simp only [hA,Set.iUnion_of_empty,measure_empty,ite_false,le_refl]

attribute [local irreducible] torusDistance

lemma pairCloseLabels_measurable {m : ℕ} (L : Length) (s : ℝ) (v : Torus L) :
    Measurable (fun Y : Configuration m L ↦ ((pairCloseLabels L s v Y).card:ℝ)) := by
  classical
  simp only [pairCloseLabels,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.measurable_sum
  intro i _
  have hd : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) v) :=
    (continuous_torusDistance L).comp
      ((continuous_apply i).prodMk (continuous_const : Continuous (fun _ : Configuration m L ↦ v)))
  have hp : MeasurableSet {Y : Configuration m L | ∃ j, j≠i ∧ torusDistance L (Y i) (Y j)≤ s} := by
    simp only [Set.ofPred_exists]
    apply MeasurableSet.iUnion
    intro j
    have hc : Continuous (fun Y : Configuration m L ↦ torusDistance L (Y i) (Y j)) :=
      (continuous_torusDistance L).comp ((show Continuous (fun Y : Configuration m L ↦ Y i) from continuous_apply i).prodMk
        (show Continuous (fun Y : Configuration m L ↦ Y j) from continuous_apply j))
    by_cases hji : j≠i
    · convert measurableSet_le hc.measurable (show Measurable (fun _ : Configuration m L ↦ s) from measurable_const) using 1
      all_goals try with_reducible_and_instances rfl
      ext Y
      exact and_iff_right hji
    · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Configuration m L))) using 1
      all_goals try with_reducible_and_instances rfl
      ext Y
      exact iff_false_intro (fun h ↦ hji h.1)
  exact Measurable.ite ((measurableSet_le hd.measurable measurable_const).inter hp)
    measurable_const measurable_const

lemma measurable_closeSet {n K : ℕ} [NeZero K] (L : Length) (s T : ℝ) :
    Measurable (closeSet (n := n) (K := K) L s T) := by
  classical
  apply measurable_finset_iff.mpr
  intro v
  simp only [closeSet,Finset.mem_filter,Finset.mem_univ,true_and]
  apply measurableSet_setOfPred.mp
  exact measurableSet_le measurable_const (pairCloseLabels_measurable L s (siteCenter L v))

lemma microperiod_length {K : ℕ} {L : Length} {r : ℝ} (hr : 0 < r)
    (hLK : L.val=(K:ℝ)) : L.val = microMesh r * ((microPeriod r*K : ℕ):ℝ) := by
  have hq : (microPeriod r : ℝ) ≠ 0 := by exact_mod_cast (microPeriod_pos hr).ne'
  rw [hLK,microMesh,Nat.cast_mul]
  field_simp

theorem omitted_volume_le {n K M : ℕ} [NeZero K] {L : Length} {r s T : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hMK : M ≤ K) (hrs : 6*r ≤ s) (hT : T ≤ 1/(1372*r))
    (Y : Configuration n L) (hY : Y ∈ allowed n L r) :
    (volume : Measure (Torus L)) (omitted (microMesh r) r Y) ≤
      ENNReal.ofReal (1029*r^2*n) +
      animalCost (torusRangeGraph K 1) (closeSet L s T Y) boxWeight +
      (if LargeBadComponent (torusRangeGraph K 1) (closeSet L s T Y) M then
        ENNReal.ofReal (L.val^3) else 0) := by
  classical
  have hmesh := microMesh_bounds hr (by linarith : r ≤ 1)
  have hmark : LargeParentMarked (microPeriod r) (microMesh r) r Y (closeSet (K := K) L s T Y) := by
    simpa only [mul_one,Function.Embedding.refl_apply] using actual_large_parent_marked (K := K) (D := 1) (θ := T)
      hr hrsmall hL hLK hrs (by simpa using hT) (Function.Embedding.refl _) Y
  by_cases he : LargeBadComponent (torusRangeGraph K 1) (closeSet L s T Y) M
  · simp only [he,ite_true]
    calc
      _ ≤ (volume : Measure (Torus L)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal (L.val^3) := volume_torus L
      _ ≤ _ := le_add_self
  · simp only [he,ite_false,add_zero]
    have hK : 2 < K := by rw [hLK] at hL; exact_mod_cast (show (2:ℝ)<K by linarith)
    have hsub := omitted_subset_small_and_boxes (microPeriod_pos hr) hK hLK hMK Y hY
      (closeSet L s T Y) hmark he
    apply (measure_mono hsub).trans
    apply (measure_union_le _ _).trans
    apply add_le_add
    · apply (volume_smallFills_le hmesh.1 (hmesh.2.1.trans (by linarith))
        (microperiod_length hr hLK) hmesh.2.2 Y).trans
      apply ENNReal.ofReal_le_ofReal
      have hsq : (microMesh r)^2 ≤ r^2 := sq_le_sq₀ hmesh.1.le hr.le |>.mpr hmesh.2.1
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (Nat.cast_nonneg n)
    · exact volume_largeBoxUnion_le L _

end HardSphere.BathSlice

namespace HardSphere.BathSlice
open HardSphere.Lattice

lemma boxWeight_le (m : ℕ) : boxWeight (m+1) ≤ 64*(8:ℝ≥0∞)^m := by
  have hnat : m+2 ≤ 2^(m+1) := by have := (Nat.lt_two_pow_self (n := m+1)); omega
  have hbound : 8*(m+2)^3 ≤ 64*8^m := by
    calc
      _ ≤ 8*(2^(m+1))^3 := by gcongr
      _ = 64*8^m := by rw [←pow_mul,Nat.mul_comm (m+1) 3,pow_mul]; norm_num; rw [pow_succ]; ring
  have heq : boxWeight (m+1) = ((8*(m+2)^3:ℕ):ℝ≥0∞) := by
    unfold boxWeight
    norm_cast
    ring
  rw [heq]
  exact_mod_cast hbound

lemma box_series_le {q : ℝ≥0∞} (hq : 8*q ≤ (2:ℝ≥0∞)⁻¹) :
    (∑' m : ℕ, boxWeight (m+1)*q^(m+1)) ≤ 128*q := by
  calc
    _ ≤ ∑' m : ℕ, (64*q)*((2:ℝ≥0∞)⁻¹)^m := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc
        _ ≤ (64*8^m)*q^(m+1) := mul_le_mul' (boxWeight_le m) le_rfl
        _ = (64*q)*(8*q)^m := by rw [mul_pow,pow_succ]; ring
        _ ≤ _ := mul_le_mul' le_rfl (pow_le_pow_left' hq m)
    _ = (64*q)*2 := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
    _ = _ := by ring

theorem omitted_mean_le {n K M : ℕ} [NeZero K] {L : Length} {r s T : ℝ}
    (hr : 0 < r) (hrsmall : r ≤ 1/4096) (hL : 10 < L.val) (hLK : L.val=(K:ℝ))
    (hMK : M ≤ K) (hM : 1 ≤ M) (hrs : 6*r ≤ s) (hT : T ≤ 1/(1372*r))
    (μ : Measure (Configuration n L)) [IsProbabilityMeasure μ]
    (hallowed : ∀ᵐ Y ∂μ, Y ∈ allowed n L r) (p : ℝ≥0∞)
    (hbad : ∀ A : Finset (DiscreteTorus K), μ {Y | A ⊆ closeSet L s T Y} ≤ p^A.card)
    (hp : 8*((2^27:ℕ):ℝ≥0∞)*p ≤ (2:ℝ≥0∞)⁻¹) :
    (∫⁻ Y, (volume : Measure (Torus L)) (omitted (microMesh r) r Y) ∂μ) ≤
      ENNReal.ofReal (1029*r^2*n) +
      (K:ℝ≥0∞)^3*(128*(((2^27:ℕ):ℝ≥0∞)*p)) +
      ENNReal.ofReal (L.val^3)*(K:ℝ≥0∞)^3*(((2^27:ℕ):ℝ≥0∞)*p)^M := by
  classical
  let B := closeSet (n := n) (K := K) L s T
  let E := {Y : Configuration n L | LargeBadComponent (torusRangeGraph K 1) (B Y) M}
  have hB : Measurable B := measurable_closeSet L s T
  have hE : MeasurableSet E := by
    exact (Set.to_countable {C : Finset (DiscreteTorus K) |
      LargeBadComponent (torusRangeGraph K 1) C M}).measurableSet.preimage hB
  have hdegree (v : DiscreteTorus K) : (torusRangeGraph K 1).degree v ≤ 27 := by
    simpa using torusRange_degree 1 v
  have hcard : Fintype.card (DiscreteTorus K) = K^3 := by
    simp only [DiscreteTorus,Fintype.card_fun,ZMod.card,Fintype.card_fin]
  have hcost := animalCost_mean_le (torusRangeGraph K 1) 27 hdegree μ B hB p hbad boxWeight
  rw [hcard,Nat.cast_pow] at hcost
  have hprob := largeBadComponent_measure (torusRangeGraph K 1) 27 hdegree μ B p hbad M hM
  rw [hcard,Nat.cast_pow] at hprob
  have hi : (fun Y ↦ if Y∈E then ENNReal.ofReal (L.val^3) else 0) =
      E.indicator (fun _ ↦ ENNReal.ofReal (L.val^3)) := by
    ext Y
    simp only [Set.indicator_apply]
  calc
    _ ≤ ∫⁻ Y, ENNReal.ofReal (1029*r^2*n) + animalCost (torusRangeGraph K 1) (B Y) boxWeight +
        (if Y∈E then ENNReal.ofReal (L.val^3) else 0) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hallowed] with Y hY
      exact omitted_volume_le hr hrsmall hL hLK hMK hrs hT Y hY
    _ = ENNReal.ofReal (1029*r^2*n) + (∫⁻ Y, animalCost (torusRangeGraph K 1) (B Y) boxWeight ∂μ) +
        ENNReal.ofReal (L.val^3)*μ E := by
      have hm : Measurable (fun Y ↦ ENNReal.ofReal (1029*r^2*n) +
          animalCost (torusRangeGraph K 1) (B Y) boxWeight) :=
        measurable_const.add (measurable_animalCost _ B hB _)
      rw [lintegral_add_left hm,
        lintegral_add_left measurable_const,hi,lintegral_indicator_const hE,lintegral_const]
      simp only [measure_univ,mul_one]
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add_right
        exact hcost.trans (mul_le_mul' le_rfl (box_series_le (by simpa only [mul_assoc] using hp)))
      · exact (mul_le_mul' le_rfl hprob).trans_eq (by ring)

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SmoothSiteWeight
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma groundPositionLaw_integral {n : ℕ} {L : Length} (u : Jet n L) (f : Configuration n L → ℝ) :
    (∫ X, f X ∂groundPositionLaw n L u)=∫ X, f X*‖u.1 X‖^2 := by
  rw [groundPositionLaw,integral_withDensity_eq_integral_toReal_smul
    (((Lp.stronglyMeasurable u.1).measurable.norm.pow_const 2).ennreal_ofReal)
    (Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,mul_comm]

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
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhysicalPhase
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
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

lemma cons_measurableEmbedding {n : ℕ} (L : Length) :
    MeasurableEmbedding (fun p : Configuration n L × Torus L ↦ Fin.cons (α:=fun _ ↦ Torus L) p.2 p.1) := by
  have h := ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) ↦ Torus L) 0).symm.measurableEmbedding).comp
    (MeasurableEquiv.prodComm : Configuration n L × Torus L ≃ᵐ Torus L × Configuration n L).measurableEmbedding
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext pair
  change Fin.cons pair.2 pair.1 = Fin.insertNth (α:=fun _ : Fin (n+1) ↦ Torus L) 0 pair.2 pair.1
  exact (Fin.insertNth_zero' _ _).symm

lemma ground_bath_integral {n : ℕ} {L : Length} {u : Jet (n+1) L} (hu : ‖u.1‖=1)
    (F : Configuration n L → ℝ) (hF : Measurable F) {B : ℝ} (hB : ∀Y,|F Y|≤B) :
    (∫Y,F Y*(∫x,‖u.1 (Fin.cons x Y)‖^2)) =
      ∫Y,F Y ∂(groundPositionLaw (n+1) L u).map (fun X ↦ fun i : Fin n ↦ X i.succ) := by
  let μ := groundPositionLaw (n+1) L u
  let := groundPositionLaw_probability u hu
  have hm : Measurable (fun X : Configuration (n+1) L ↦ fun i : Fin n ↦ X i.succ) := by fun_prop
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable,groundPositionLaw_integral]
  let f : Configuration n L × Torus L → ℝ := fun p ↦ F p.1*‖u.1 (Fin.cons p.2 p.1)‖^2
  have hf : Integrable f (volume.prod volume) := by
    have hu' := (Lp.memLp u.1).comp_measurePreserving (cons_preserving (n:=n) L)
    apply ((hu'.integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul B).mono'
    · exact (hF.comp measurable_fst).aestronglyMeasurable.mul (hu'.aestronglyMeasurable.norm.pow 2)
    · exact Eventually.of_forall fun p ↦ by
        change ‖F p.1*‖u.1 (Fin.cons p.2 p.1)‖^2‖ ≤ B*‖u.1 (Fin.cons p.2 p.1)‖^2
        simp only [Real.norm_eq_abs,abs_mul,abs_sq]
        exact mul_le_mul_of_nonneg_right (hB _) (sq_nonneg _)
  calc
    _ = ∫p,f p ∂volume.prod volume := by rw [integral_prod _ hf]; simp only [f,integral_const_mul]
    _ = _ := by
      have he := (cons_preserving (n:=n) L).integral_comp (cons_measurableEmbedding (n:=n) L)
        (fun X ↦ F (fun i : Fin n ↦ X i.succ)*‖u.1 X‖^2)
      simpa only [Fin.cons_succ] using he

lemma ground_physical_phase_transfer {n : ℕ} {L : Length} {r h : ℝ}
    {u : Jet (n+1) L} (hu : IsGroundVector (n+1) L r u) (hh : 0<h) :
    Phase.modulusOccupation (fun p : Configuration n L × Torus L ↦ u.1 (Fin.cons p.2 p.1)) volume volume -
      4*Real.sqrt ((∫Y,(volume : Measure (Torus L)).real (BathSlice.omitted h r Y)
        ∂(groundPositionLaw (n+1) L u).map (fun X ↦ fun i : Fin n ↦ X i.succ))/L.val^3) ≤
    Phase.occupation (fun p : Configuration n L × Torus L ↦ u.1 (Fin.cons p.2 p.1)) volume volume := by
  have hLp := L.property
  let f : Configuration n L × Torus L → ℂ := fun p ↦ u.1 (Fin.cons p.2 p.1)
  have hf : MemLp f 2 (volume.prod volume) :=
    (Lp.memLp u.1).comp_measurePreserving (cons_preserving (n:=n) L)
  have hn : ∫p,‖f p‖^2 ∂volume.prod volume=1 := by
    rw [(cons_preserving (n:=n) L).integral_comp (cons_measurableEmbedding (n:=n) L)
      (fun X ↦ ‖u.1 X‖^2),←scalar_norm_sq_integral,hu.2.2.1]
    norm_num
  have hV : (volume : Measure (Torus L)).real univ=L.val^3 := by
    rw [Measure.real,BathSlice.volume_torus,ENNReal.toReal_ofReal (by positivity)]
  have hU : MeasurableSet {p : Configuration n L × Torus L | p.2∈BathSlice.retained h r p.1} :=
    (BathSlice.measurableSet_omitted_graph L h r).compl
  have ht := Phase.phase_transfer hf hn (by rw [hV]; positivity) hU (hu.ae_retained_commonPhase hh)
  have hl : Phase.geometricLoss f {p | p.2∈BathSlice.retained h r p.1} volume volume =
      (∫Y,(volume : Measure (Torus L)).real (BathSlice.omitted h r Y)
        ∂(groundPositionLaw (n+1) L u).map (fun X ↦ fun i : Fin n ↦ X i.succ))/L.val^3 := by
    unfold Phase.geometricLoss
    simp only [hV]
    congr 1
    convert ground_bath_integral hu.2.2.1 (fun Y ↦ (volume : Measure (Torus L)).real (BathSlice.omitted h r Y))
      (BathSlice.measurable_omitted_volume L h r).ennreal_toReal (B:=L.val^3) (fun Y ↦ by
        rw [abs_of_nonneg measureReal_nonneg,←hV]
        exact measureReal_mono (subset_univ _)) using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    exact Eventually.of_forall fun Y ↦ by
      have he : Prod.mk Y ⁻¹' {p : Configuration n L × Torus L | p.2∈BathSlice.retained h r p.1}ᶜ = BathSlice.omitted h r Y := by
        ext x
        simp [BathSlice.retained]
      dsimp only
      rw [he]
  simpa only [hl] using ht

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SiteCube
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open MeasureTheory Set Filter HardSphere.Lattice

theorem physical_omitted_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K M : ℕ) [NeZero K] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
      α/D≤1/4096 → 6*(α/D)≤ spatialCloseScale D b → θ*D≤1/(1372*(α/D)) →
    ∀ (g : Jet n L), HardSphere.IsGroundVector n L (α/D) g →
    ∀ (m : ℕ) (e : Fin m ↪ Fin n), 1≤M → M≤K →
    let p := ENNReal.ofReal (((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))
    8*((2^27:ℕ):ℝ≥0∞)*p≤(2:ℝ≥0∞)⁻¹ →
      (∫⁻ Y, (volume : Measure (Torus L)) (omitted (microMesh (α/D)) (α/D) Y)
        ∂(groundPositionLaw n L g).map (fun X i ↦ X (e i))) ≤
      ENNReal.ofReal (1029*(α/D)^2*m) +
      (K:ℝ≥0∞)^3*(128*(((2^27:ℕ):ℝ≥0∞)*p)) +
      ENNReal.ofReal (L.val^3)*(K:ℝ≥0∞)^3*(((2^27:ℕ):ℝ≥0∞)*p)^M := by
  obtain ⟨Q,hQ,htail⟩ := physical_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K M _ L hL D α hL100 hDeq hD hα hαmax hrsmall hrs hT g hg m e hM hMK p hp
  have hDp : 0<D := lt_of_lt_of_le (by norm_num) (hD₀.trans hD)
  have hαp : 0<α := lt_of_lt_of_le (by norm_num) hα
  let := groundPositionLaw_probability g hg.2.2.1
  have hm : Measurable (fun X : Configuration n L ↦ (fun i ↦ X (e i))) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  let : IsProbabilityMeasure ((groundPositionLaw n L g).map (fun X i ↦ X (e i))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  exact omitted_mean_le (div_pos hαp hDp) hrsmall (by linarith) hL hMK hM hrs hT _
    (IsGroundVector.bathLaw_ae_allowed hg e) p
    (hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg m e) hp

end HardSphere.BathSlice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalUniformModulus
attribute [-instance] _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
open BathSlice
attribute [local instance] Classical.propDecidable

lemma omitted_integral_real {n : ℕ} {L : Length} (h r : ℝ) (μ : Measure (Configuration n L))
    {C : ℝ} (hC : 0≤C) (hbound : (∫⁻Y,(volume : Measure (Torus L)) (omitted h r Y) ∂μ)≤ENNReal.ofReal C) :
    (∫Y,(volume : Measure (Torus L)).real (omitted h r Y) ∂μ)≤C := by
  have hm := measurable_omitted_volume (n:=n) L h r
  have hf : (∫⁻Y,(volume : Measure (Torus L)) (omitted h r Y) ∂μ)≠⊤ :=
    ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top)
  have he := integral_toReal hm.aemeasurable (ae_lt_top hm hf)
  change (∫Y,((volume : Measure (Torus L)) (omitted h r Y)).toReal ∂μ)≤C
  rw [he]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal hC)

theorem physical_geometry_error : ∃Q : ℕ,0<Q ∧ ∀θ : ℝ,0<θ →
    ∃b H : ℝ,0<b ∧ b≤1/4 ∧ 0<H ∧
      Tendsto (fun D : ℝ ↦ ((H/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀A : ℝ,∃D₀ : ℝ,1≤D₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀_hL : L.val=(K:ℝ),
      100≤L.val → ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤A →
      α/D≤1/4096 → 6*(α/D)≤ spatialCloseScale D b → θ*D≤1/(1372*(α/D)) →
    ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    let p := ((H/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))
    8*(2^27:ℝ)*p≤1/2 →
    (∫Y,(volume : Measure (Torus L)).real (omitted (microMesh (α/D)) (α/D) Y)
      ∂(groundPositionLaw (N+1) L ψ).map (fun X ↦ fun i : Fin N ↦ X i.succ))/L.val^3 ≤
      1029*α^2/D+128*(2^27:ℝ)*p+(K:ℝ)^3*((2^27:ℝ)*p)^K := by
  obtain ⟨Q,hQ,htail⟩ := physical_omitted_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,H,hb,hb1,hH,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,H,hb,hb1,hH,hlim,?_⟩
  intro A
  obtain ⟨D₀,hD₀,hfin⟩ := hfin A
  refine ⟨D₀,hD₀,?_⟩
  intro N K instK L hL h100 D α hDeq hD hα hαA hrs hsep hθD ψ hψ p hp
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one (hD₀.trans hD)
  have hαp : 0<α := lt_of_lt_of_le zero_lt_one hα
  have hp0 : 0≤p := Real.rpow_nonneg (by positivity) _
  have h1 : 1≤K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  let e : Fin N ↪ Fin (N+1) := ⟨Fin.succ,Fin.succ_injective N⟩
  have hpE : 8*((2^27:ℕ):ℝ≥0∞)*ENNReal.ofReal p≤(2:ℝ≥0∞)⁻¹ := by
    have hh := ENNReal.ofReal_le_ofReal hp
    simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤8*2^27),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤8),ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
      ENNReal.ofReal_one,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),one_div,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hh := hfin (N+1) K K L hL D α h100 (by simpa only [Nat.cast_add,Nat.cast_one] using hDeq) hD hα hαA hrs hsep hθD ψ hψ N e h1 le_rfl hpE
  let C := 1029*(α/D)^2*N+(K:ℝ)^3*(128*((2^27:ℝ)*p))+L.val^3*(K:ℝ)^3*((2^27:ℝ)*p)^K
  have hC : 0≤C := by dsimp only [C]; positivity
  have hh' : (∫⁻ Y,(volume : Measure (Torus L)) (omitted (microMesh (α/D)) (α/D) Y)
      ∂(groundPositionLaw (N+1) L ψ).map (fun X ↦ fun i : Fin N ↦ X i.succ))≤ENNReal.ofReal C := by
    dsimp only [C]
    rw [ENNReal.ofReal_add (by positivity) (by positivity),ENNReal.ofReal_add (by positivity) (by positivity)]
    simp only [ENNReal.ofReal_mul (by positivity : (0:ℝ)≤(K:ℝ)^3),
      ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤128),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤2^27),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤L.val^3*(K:ℝ)^3),
      ENNReal.ofReal_mul (by positivity : (0:ℝ)≤L.val^3),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤K),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2),
      ENNReal.ofReal_pow (by positivity : (0:ℝ)≤2^27*p),
      ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
    simpa only [Nat.cast_pow,Nat.cast_ofNat,p,e,Function.Embedding.coeFn_mk] using hh
  have hreal := omitted_integral_real (microMesh (α/D)) (α/D) _ hC hh'
  refine (div_le_div_of_nonneg_right hreal (by positivity)).trans ?_
  have hn : (N:ℝ)≤D*L.val^3 := by rw [hDeq]; field_simp; norm_num
  have hfirst : 1029*(α/D)^2*(N:ℝ)/L.val^3≤1029*α^2/D := by
    apply (div_le_iff₀ (by positivity : 0<L.val^3)).mpr
    apply le_trans (mul_le_mul_of_nonneg_left hn (by positivity))
    field_simp
    ring_nf
    exact le_rfl
  dsimp only [C]
  rw [add_div,add_div]
  have htwo : (K:ℝ)^3*(128*((2^27:ℝ)*p))/L.val^3=128*(2^27:ℝ)*p := by rw [hL]; field_simp
  have hthree : L.val^3*(K:ℝ)^3*((2^27:ℝ)*p)^K/L.val^3=(K:ℝ)^3*((2^27:ℝ)*p)^K := by field_simp
  rw [htwo,hthree]
  linarith

end HardSphere
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_PhysicalPhaseWindow
attribute [-instance] _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
open BathSlice
attribute [local instance] Classical.propDecidable

lemma geometry_scale_eventually {A b : ℝ} (hA : 0<A) (hb : 0<b) :
    ∀ᶠ D : ℝ in atTop,∀α : ℝ,0<α → α≤2*A →
      α/D≤1/4096 ∧ 6*(α/D)≤ spatialCloseScale D b ∧
      (1/(2744*A))*D≤1/(1372*(α/D)) := by
  have hr := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/3)).eventually (eventually_ge_atTop (12*A/b))
  filter_upwards [eventually_ge_atTop (max 1 (8192*A)),hr] with D hD hr
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hD)
  have hbD : 12*A≤b*D^(2/3:ℝ) := by
    have hh := (div_le_iff₀ hb).mp hr
    nlinarith
  have h8192 : 8192*A≤D := (le_max_right _ _).trans hD
  intro α hα hαA
  refine ⟨(div_le_iff₀ hDp).mpr (by nlinarith),?_,?_⟩
  · rw [←mul_div_assoc]
    apply (div_le_iff₀ hDp).mpr
    have he : (spatialCloseScale D b)*D=b*D^(2/3:ℝ) := by
      unfold spatialCloseScale
      rw [mul_assoc]
      conv_lhs => arg 2; arg 2; rw [←Real.rpow_one D]
      rw [←Real.rpow_add hDp]
      norm_num
    rw [he]
    nlinarith
  · have hh : (1372*(α/D))>0 := by positivity
    apply (le_div_iff₀ hh).mpr
    have he : 1/(2744*A)*D*(1372*(α/D))=α/(2*A) := by field_simp; ring
    rw [he]
    exact (div_le_one (by positivity : 0<2*A)).mpr hαA

theorem physical_uniform_phase_error_oai {A c : ℝ} (hA : 2≤A) (hc : 0 < c) :
    ∃D₀ : ℝ,1≤D₀ ∧ ∃K₀ : ℕ,100≤K₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀_hL : L.val=(K:ℝ),K₀≤K →
    ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    Phase.modulusOccupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume-c/2≤
      Phase.occupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  have hAp : 0<A := by linarith
  obtain ⟨Q,hQ,htail⟩ := physical_geometry_error
  let θ := 1/(2744*A)
  have hθ : 0<θ := by dsimp only [θ]; positivity
  obtain ⟨b,H,hb,hb1,hH,hlim,hfin⟩ := htail θ hθ
  let p := fun D : ℝ ↦ ((H/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))
  obtain ⟨Ds,hDs,hfin⟩ := hfin (2*A)
  have herror : Tendsto (fun D : ℝ ↦ 1029*(2*A)^2/D+128*(2^27:ℝ)*p D) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x:=1029*(2*A)^2)).div_atTop (tendsto_id (α:=ℝ))).add (hlim.const_mul (128*(2^27:ℝ)))
    simpa only [mul_zero,add_zero,p,id_eq] using hh
  have hlarge := (geometry_scale_eventually hAp hb).and
    ((herror.eventually (gt_mem_nhds (by positivity : (0:ℝ) < c^2/128))).and
      (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/(16*2^27)))))
  obtain ⟨De,hDe⟩ := eventually_atTop.mp hlarge
  have hKlim := tendsto_pow_const_mul_const_pow_of_lt_one 3 (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  obtain ⟨Ke,hKe⟩ := eventually_atTop.mp (hKlim.eventually (gt_mem_nhds (by positivity : (0:ℝ) < c^2/128)))
  refine ⟨max Ds De,hDs.trans (le_max_left _ _),max 100 Ke,le_max_left _ _,?_⟩
  intro N K instK L hL hK D α hDeq hD hαlo hαhi ψ hψ
  have hDsD := (le_max_left Ds De).trans hD
  have hDp : 0<D := lt_of_lt_of_le zero_lt_one (hDs.trans hDsD)
  have hα : 1≤α := by linarith
  have hp : 0≤p D := Real.rpow_nonneg (by positivity) _
  obtain ⟨hscale,herr,hpD⟩ := hDe D ((le_max_right Ds De).trans hD)
  obtain ⟨hr,hsep,hθD⟩ := hscale α (by linarith) hαhi
  have h100 : 100≤L.val := by rw [hL]; exact_mod_cast (le_max_left 100 Ke).trans hK
  have hnum : 8*(2^27:ℝ)*p D≤1/2 := by linarith
  have hgeom := hfin hL h100 D α hDeq hDsD hα hαhi hr hsep hθD ψ hψ hnum
  let loss := (∫Y,(volume : Measure (Torus L)).real (omitted (microMesh (α/D)) (α/D) Y)
      ∂(groundPositionLaw (N+1) L ψ).map (fun X ↦ fun i : Fin N ↦ X i.succ))/L.val^3
  have hfirst : 1029*α^2/D≤1029*(2*A)^2/D := by gcongr
  have hlast : (K:ℝ)^3*((2^27:ℝ)*p D)^K≤(K:ℝ)^3*(1/2:ℝ)^K := by
    gcongr
    linarith
  have hKerr := hKe K ((le_max_right 100 Ke).trans hK)
  have hloss : loss ≤ c^2/64 := by change loss≤_ at hgeom; linarith
  have hsqrt : Real.sqrt loss ≤ c/8 := by
    apply (Real.sqrt_le_left (by positivity : 0 ≤ c/8)).mpr
    nlinarith
  have hphase := ground_physical_phase_transfer hψ ((microMesh_bounds (by positivity : 0<α/D) (by linarith : α/D≤1)).1)
  dsimp only [loss] at hsqrt
  linarith

end HardSphere
end
end

end OAI
end

theorem solution : type_of% @OAI.HardSphere.physical_uniform_phase_error_oai := @OAI.HardSphere.physical_uniform_phase_error_oai
