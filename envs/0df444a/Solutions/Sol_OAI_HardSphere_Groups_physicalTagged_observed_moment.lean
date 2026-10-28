-- Prove2me | solution 1 for OAI.HardSphere.Groups.physicalTagged_observed_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:16:57.832319+00:00
-- url     : https://prove2.me/submissions/312cbe88-ecb2-4071-b9e5-57051d0d80a7

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_Groups_physicalPairedRoute_marginals
import Theorems.Thm_OAI_HardSphere_Groups_physicalPairedRoute_midpoint
import Theorems.Thm_OAI_HardSphere_Groups_physicalRouteAux_nonempty
import Theorems.Thm_OAI_HardSphere_Groups_physical_first_likelihood_moment
import Theorems.Thm_OAI_HardSphere_Groups_physical_second_likelihood_moment

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalCheck
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison

variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

variable {C : Type*} [Fintype C] (checks : C → LocalCheck X)

lemma measurableSet_retainedEvent (s : Finset ι) : MeasurableSet (retainedEvent checks s) := by
  classical
  have heq : retainedEvent checks s =
      ⋂ c, if (checks c).support ⊆ s then {x | (checks c).pass x} else Set.univ := by
    ext x
    simp [retainedEvent]
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact (checks c).measurable_pass
  · exact MeasurableSet.univ

lemma measurable_checkWeight (s : Finset ι) : Measurable (checkWeight checks s) :=
  measurable_const.indicator (measurableSet_retainedEvent checks s)

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_le_one (s : Finset ι) (x : ∀ i, X i) : checkWeight checks s x ≤ 1 := by
  classical
  simp only [checkWeight, Set.indicator_apply]
  split_ifs <;> simp

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_depends (s : Finset ι) {x y : ∀ i, X i}
    (hxy : ∀ i ∈ s, x i = y i) : checkWeight checks s x = checkWeight checks s y := by
  classical
  have h : x ∈ retainedEvent checks s ↔ y ∈ retainedEvent checks s := by
    apply forall_congr'
    intro c
    apply imp_congr_right
    intro hc
    exact (checks c).depends x y fun i hi ↦ hxy i (hc hi)
  simp only [checkWeight, Set.indicator_apply, h]

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_antitone {s t : Finset ι} (hst : s ⊆ t) :
    checkWeight checks t ≤ checkWeight checks s := by
  classical
  intro x
  by_cases ht : x ∈ retainedEvent checks t
  · have hs : x ∈ retainedEvent checks s := fun c hc ↦ ht c (hc.trans hst)
    simp [checkWeight, ht, hs]
  · simp [checkWeight, ht]

end HardSphere.Comparison

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

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PairFiber
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
variable {I E : Type*} [Fintype I] [MeasurableSpace E]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]
attribute [local instance] Classical.propDecidable

lemma pairEvent_measurable (C : ∀i j,X i→X j→Prop)
    (hC : ∀i j,MeasurableSet {z : X i×X j | C i j z.1 z.2}) :
    MeasurableSet (pairEvent C) := by
  simp only [pairEvent,ofPred_forall]
  exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun (_ : i≠j) ↦ (hC i j).preimage ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

end HardSphere.Comparison

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

private lemma lintegral_fin_prod {n : ℕ} {β : Fin n → Type*}
    [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, β i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  induction n with
  | zero => simp [Measure.pi_of_empty μ]
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove μ 0).symm
      (MeasurableEquiv.piFinSuccAbove β 0)
    rw [← hp.lintegral_comp (f := fun x ↦ ∏ i, f i (x i)) (Finset.measurable_prod _ fun i _ ↦
      (hf i).comp (measurable_pi_apply i))]
    have heq : (fun z ↦ ∏ i, f i ((MeasurableEquiv.piFinSuccAbove β 0).symm z i)) =
        (fun z ↦ f 0 z.1 * ∏ j, f ((0 : Fin (n+1)).succAbove j) (z.2 j)) := by
      funext z
      rw [Fin.prod_univ_succAbove _ 0]
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Equiv.coe_fn_mk, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [heq]
    have hm : Measurable (fun z : ∀ j : Fin n, β ((0 : Fin (n+1)).succAbove j) ↦
        ∏ j, f ((0 : Fin (n+1)).succAbove j) (z j)) :=
      Finset.measurable_prod _ fun i _ ↦
        (hf ((0 : Fin (n+1)).succAbove i)).comp (measurable_pi_apply i)
    rw [lintegral_prod_mul (hf 0).aemeasurable hm.aemeasurable]
    rw [ih _ _ (fun i ↦ hf ((0 : Fin (n+1)).succAbove i))]
    exact (Fin.prod_univ_succAbove (fun i ↦ ∫⁻ x, f i x ∂μ i) 0).symm

lemma lintegral_finite_prod {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (μ : ∀ i, Measure (β i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, β i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂μ i := by
  classical
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp (f := fun x ↦ ∏ i, f i (x i))
    (Finset.measurable_prod _ fun i _ ↦ (hf i).comp (measurable_pi_apply i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i ↦ hf (e i))

section CoordinateKernels
variable {ι : Type*} [Fintype ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

lemma coordinateKernel_apply (x : ∀ i, X i) :
    coordinateKernel κ x = Measure.pi (fun i ↦ κ i (x i)) := by
  simp only [coordinateKernel, finiteKernelPi_apply, Kernel.comap_apply]

lemma pi_compProd (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)] :
    Measure.map (fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i))
      ((Measure.pi μ).compProd (coordinateKernel κ)) =
    Measure.pi (fun i ↦ (μ i).compProd (κ i)) := by
  classical
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i)) := by
    fun_prop
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs),
    Measure.compProd_apply (hm (MeasurableSet.univ_pi hs))]
  have heq (x : ∀ i, X i) : (Prod.mk x ⁻¹'
      ((fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i)) ⁻¹' Set.pi Set.univ s)) =
      Set.pi Set.univ (fun i ↦ Prod.mk (x i) ⁻¹' s i) := by
    ext z
    simp
  simp_rw [heq, coordinateKernel_apply, Measure.pi_pi]
  rw [lintegral_finite_prod _ _ (fun i ↦ Kernel.measurable_kernel_prodMk_left (hs i))]
  congr 1
  funext i
  exact (Measure.compProd_apply (hs i)).symm

lemma lintegral_pi_compProd (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    {f : (∀ i, X i × Z i) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂Measure.pi (fun i ↦ (μ i).compProd (κ i))) =
    ∫⁻ x, ∫⁻ z, f (fun i ↦ (x i,z i)) ∂Measure.pi (fun i ↦ κ i (x i)) ∂Measure.pi μ := by
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i, Z i) ↦ fun i ↦ (p.1 i, p.2 i)) := by
    fun_prop
  rw [← pi_compProd κ μ, lintegral_map hf hm]
  rw [Measure.lintegral_compProd (f := fun p : (∀ i, X i) × (∀ i, Z i) ↦ f (fun i ↦ (p.1 i, p.2 i)))
    (hf.comp hm)]
  simp only [coordinateKernel_apply]

end CoordinateKernels
end HardSphere.Comparison

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AuxiliaryChecks
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory

variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

lemma measurable_conditionalDensity (s o : Finset ι) (z : ∀ i, Z i) :
    Measurable (fun x ↦ conditionalDensity checks κ s o x z) := by
  let κ' (i : s) : Kernel (∀ j, X j) (Z i) :=
    (κ i).comap (fun x ↦ x i) (measurable_pi_apply (i : ι))
  let η := finiteKernelPi κ'
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i : s, Z i) ↦
      checkWeight checks (s ∪ o) (fun i ↦ (p.1 i, Function.updateFinset z s p.2 i))) := by
    apply (measurable_checkWeight checks (s ∪ o)).comp
    exact Measurable.of_eval fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp ((measurable_updateFinset (x := z) (s := s)).comp
          measurable_snd))
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  simpa only [η, finiteKernelPi_apply, κ', Kernel.comap_apply,
    conditionalDensity, lmarginal] using h

end HardSphere.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RestrictedMeasure
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {X : Type*} [MeasurableSpace X]

lemma subtypeConditional_map (P : Measure X) {S : Set X} (hS : MeasurableSet S) :
    (subtypeConditional P S).map (Subtype.val:S→X)=(P S)⁻¹ • P.restrict S := by
  rw [subtypeConditional,Measure.map_smul, map_comap_subtype_coe hS]

end HardSphere.Comparison

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
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff Comparison

lemma referenceOn_map (t : ℝ) (y z : Point) {S : Set C(Time,Point)} (hS : MeasurableSet S) :
    (referenceOn t y z S).map Subtype.val=individualReference t y z S :=
  subtypeConditional_map _ hS

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ConditionTransport
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

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalReference
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
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener Bridge GaussianPacking Comparison CellOrbital
attribute [local instance] Classical.propDecidable

lemma physicalMutual_measurable {I : Type*} [Fintype I] {L : Length} (r : ℝ) :
    MeasurableSet (physicalMutual (I:=I) (L:=L) r) :=
  pairEvent_measurable _ (fun _ _ ↦ (jointCollision_closed (L:=L) r).measurableSet.compl)

end HardSphere.Groups

end
end

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

lemma torusNear_refl (K R : ℕ) (x : DiscreteTorus K) : torusNear K R x x := by
  exact ⟨0,fun i ↦ by simp,fun i ↦ by simp⟩

lemma torusNear_symm {K R : ℕ} {x y : DiscreteTorus K} (h : torusNear K R x y) :
    torusNear K R y x := by
  obtain ⟨d,hd,he⟩ := h
  refine ⟨-d,fun i ↦ by simpa using hd i,fun i ↦ ?_⟩
  simp only [Pi.neg_apply,Int.cast_neg,he i]
  abel

open MeasureTheory

end HardSphere.Lattice

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
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_PartialPhysicalLaw
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
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
variable {I E : Type*} [DecidableEq I] [Fintype E]
  {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (checks : E → LocalCheck V)
  (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]

lemma insertionFiberEvent_measurable (s o : Finset I) :
    MeasurableSet (insertionFiberEvent checks s o) :=
  (measurableSet_retainedEvent checks (s∪o)).preimage measurable_updateFinset'

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ConditionalLikelihood
attribute [-instance] _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory
section NormalizerFacts
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)
omit [Fintype C] in
lemma partialNormalizer_le_one {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (s o : Finset ι) (x : ∀ i, X i) : partialNormalizer checks μ s o x ≤ 1 := by
  calc
    _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂Measure.pi (fun i : s ↦ μ i) :=
      lintegral_mono fun _ ↦ checkWeight_le_one checks _ _
    _ = 1 := by simp

lemma measurable_partialNormalizer {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (s o : Finset ι) : Measurable (partialNormalizer checks μ s o) :=
  (measurable_checkWeight checks (s ∪ o)).lmarginal μ

end NormalizerFacts

section CancellationEstimate
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {R C D : Type*} [Fintype R] [Fintype C] [Fintype D]
  (reference : R → LocalCheck X)
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

lemma measurable_conditionalLikelihood (s o : Finset ι) (z : ∀ i, Z i) :
    Measurable (fun x ↦ conditionalLikelihood reference checks μ κ s o x z) := by
  apply Measurable.mul
  · apply Measurable.div (measurable_partialNormalizer reference s o)
    exact (measurable_partialNormalizer checks s o).comp
      (Measurable.of_eval fun i ↦ (measurable_pi_apply i).prodMk measurable_const)
  · exact measurable_conditionalDensity checks κ s o z

end CancellationEstimate

section LikelihoodIdentity
variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {R C : Type*} [Fintype R] [Fintype C]
  (reference : R → LocalCheck X) (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

omit [Fintype R] [∀ i, IsProbabilityMeasure (μ i)] in
lemma partialNormalizer_updateFinset (s o : Finset ι) (x : ∀ i, X i) (u : ∀ i : s, X i) :
    partialNormalizer reference μ s o (Function.updateFinset x s u) =
      partialNormalizer reference μ s o x := by
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset, hi]

omit [Fintype R] [Fintype C] [∀ i, IsFiniteKernel (κ i)] in

lemma conditionalDensity_reference_support (s o : Finset ι)
    (hincl : ∀ (x : ∀ i, X i) (z : ∀ i, Z i),
      checkWeight checks (s ∪ o) (fun i ↦ (x i,z i)) ≤ checkWeight reference (s ∪ o) x)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    checkWeight reference (s ∪ o) x * conditionalDensity checks κ s o x z =
      conditionalDensity checks κ s o x z := by
  classical
  by_cases hx : x ∈ retainedEvent reference (s ∪ o)
  · simp [checkWeight, hx]
  · have hz : conditionalDensity checks κ s o x z = 0 := by
      apply le_antisymm _ zero_le
      calc
        _ ≤ lmarginal (fun i ↦ κ i (x i)) s (fun _ ↦ checkWeight reference (s ∪ o) x) z :=
          lmarginal_mono (hincl x) z
        _ = 0 := by simp [lmarginal, checkWeight, hx]
    simp [hz]

end LikelihoodIdentity

end HardSphere.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ExactFiberLikelihood
attribute [-instance] _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
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
variable {I : Type*} [DecidableEq I] {X Z : I → Type*}
  [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]
  {E R : Type*} [Fintype E] [Fintype R]
  (checks : E → LocalCheck (fun i ↦ X i×Z i))
  (reference : R → LocalCheck X)
  (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
  (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]

lemma conditionalDensity_weighted (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i)
    (F : (∀i,X i) → ℝ≥0∞) (hF : Measurable F) :
    lmarginal μ s (fun y ↦ F y * conditionalDensity checks κ s o y z) x =
      lmarginal (fun i ↦ (μ i).compProd (κ i)) s
        (fun v ↦ F (fun i ↦ (v i).1)*checkWeight checks (s∪o) v) (fun i ↦ (x i,z i)) := by
  let f (p : ∀i : s,X i×Z i) :=
    F (Function.updateFinset x s (fun i ↦ (p i).1))*
      checkWeight checks (s∪o) (Function.updateFinset (fun i ↦ (x i,z i)) s p)
  have hf : Measurable f := by
    apply Measurable.mul
    · apply hF.comp
      exact measurable_updateFinset.comp (Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i)))
    · exact (measurable_checkWeight checks (s∪o)).comp measurable_updateFinset
  have he (p : ∀i : s,X i×Z i) :
      (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)=
        Function.updateFinset x s (fun i ↦ (p i).1) := by
    funext i
    by_cases hi : i∈s <;> simp [Function.updateFinset,hi]
  change (∫⁻y,F (Function.updateFinset x s y)*conditionalDensity checks κ s o (Function.updateFinset x s y) z
    ∂Measure.pi (fun i : s ↦ μ i))= _
  change _=∫⁻p,F (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)*
    checkWeight checks (s∪o) (Function.updateFinset (fun i ↦ (x i,z i)) s p)
    ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i))
  simp_rw [he]
  rw [show (fun p ↦ F (Function.updateFinset x s (fun i ↦ (p i).1))*
    checkWeight checks (s∪o) (Function.updateFinset (fun i ↦ (x i,z i)) s p))=f from rfl,
    lintegral_pi_compProd (fun i : s ↦ κ i) (fun i : s ↦ μ i) hf]
  apply lintegral_congr
  intro y
  change F (Function.updateFinset x s y)*
    (∫⁻u,checkWeight checks (s∪o)
      (fun i ↦ (Function.updateFinset x s y i,Function.updateFinset z s u i))
      ∂Measure.pi (fun i : s ↦ κ i (Function.updateFinset x s y i)))=_
  have hμ : (fun i : s ↦ κ i (Function.updateFinset x s y i))=(fun i : s ↦ κ i (y i)) := by
    funext i
    simp [Function.updateFinset,i.property]
  rw [hμ,←lintegral_const_mul _ (by
    exact (measurable_checkWeight checks (s∪o)).comp
      (Measurable.of_eval (fun i ↦ measurable_const.prodMk
        ((measurable_pi_apply i).comp measurable_updateFinset))))]
  apply lintegral_congr
  intro u
  have hp : (fun i ↦ (Function.updateFinset x s y i,Function.updateFinset z s u i))=
      Function.updateFinset (fun i ↦ (x i,z i)) s (fun i ↦ (y i,u i)) := by
    funext i
    by_cases hi : i∈s <;> simp [Function.updateFinset,hi]
  simp only [f,hp]

omit [Fintype E] [Fintype R] [∀i,IsProbabilityMeasure (μ i)] [∀i,IsFiniteKernel (κ i)] in
lemma conditionalLikelihood_update (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i) (y : ∀i : s,X i) :
    conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s y) z=
      (partialNormalizer reference μ s o x /
        partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i)))*
      conditionalDensity checks κ s o (Function.updateFinset x s y) z := by
  unfold conditionalLikelihood
  rw [partialNormalizer_updateFinset]
  congr 2
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset,hi]

lemma fiber_lintegral {V : I → Type*} [∀i,MeasurableSpace (V i)]
    {C : Type*} [Fintype C] (c : C → LocalCheck V) (ν : ∀i,Measure (V i))
    (s o : Finset I) (v : ∀i,V i) (f : (∀i : s,V i) → ℝ≥0∞) :
    (∫⁻p,f p ∂conditionedMeasure (Measure.pi (fun i : s ↦ ν i))
      {p | Function.updateFinset v s p∈retainedEvent c (s∪o)})=
    (partialNormalizer c ν s o v)⁻¹ *
      ∫⁻p,f p*checkWeight c (s∪o) (Function.updateFinset v s p)
        ∂Measure.pi (fun i : s ↦ ν i) := by
  let A : Set (∀i : s,V i) := {p | Function.updateFinset v s p∈retainedEvent c (s∪o)}
  have hA : MeasurableSet A := (measurableSet_retainedEvent c (s∪o)).preimage measurable_updateFinset
  have hmass : (Measure.pi (fun i : s ↦ ν i)) A=partialNormalizer c ν s o v := by
    change _=∫⁻p,A.indicator (fun _ ↦ (1:ℝ≥0∞)) p ∂Measure.pi (fun i : s ↦ ν i)
    rw [lintegral_indicator_const hA,one_mul]
  change (∫⁻p,f p ∂conditionedMeasure _ A)=_
  rw [conditionedMeasure,lintegral_smul_measure,hmass]
  change _⁻¹ *(∫⁻p in A,f p ∂Measure.pi (fun i : s ↦ ν i))=_
  rw [←lintegral_indicator hA]
  congr 1
  apply lintegral_congr
  intro p
  by_cases hp : p∈A
  · simp only [Set.indicator_of_mem hp]
    change f p=f p*A.indicator (fun _ ↦ (1:ℝ≥0∞)) p
    rw [Set.indicator_of_mem hp,mul_one]
  · simp only [Set.indicator_of_notMem hp]
    change 0=f p*A.indicator (fun _ ↦ (1:ℝ≥0∞)) p
    rw [Set.indicator_of_notMem hp,mul_zero]

lemma proposalFiber_primary (s o : Finset I) (x : ∀i,X i) (z : ∀i,Z i)
    (hZ : 0<partialNormalizer reference μ s o x)
    (hincl : ∀(y : ∀i,X i)(u : ∀i,Z i),
      checkWeight checks (s∪o) (fun i ↦ (y i,u i)) ≤ checkWeight reference (s∪o) y) :
    (proposalFiber checks μ κ s o x z).map (fun p i ↦ (p i).1)=
      (referenceFiber reference μ s o x).withDensity
        (fun y ↦ conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s y) z) := by
  let Z₀ := partialNormalizer reference μ s o x
  let Y₀ := partialNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s o (fun i ↦ (x i,z i))
  have hZT : Z₀≠⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (partialNormalizer_le_one reference s o x)
  have hZm : Z₀⁻¹*Z₀=1 := ENNReal.inv_mul_cancel (ne_of_gt hZ) hZT
  apply Measure.ext_of_lintegral
  intro f hf
  let F (y : ∀i,X i) := f (fun i : s ↦ y i)
  have hF : Measurable F := hf.comp (Measurable.of_eval (fun i ↦ measurable_pi_apply (i:I)))
  have hu (p : ∀i : s,X i) : F (Function.updateFinset x s p)=f p := by
    dsimp only [F]
    congr 1
    funext i
    simp [Function.updateFinset,i.property]
  have hm : Measurable (fun y : ∀i:s,X i ↦ conditionalLikelihood reference checks μ κ s o
      (Function.updateFinset x s y) z) :=
    (measurable_conditionalLikelihood reference checks μ κ s o z).comp
      (measurable_updateFinset (x:=x) (s:=s))
  have hproj : Measurable (fun p : ∀i:s,X i×Z i ↦ fun i ↦ (p i).1) :=
    Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i))
  rw [lintegral_map hf hproj,
    lintegral_withDensity_eq_lintegral_mul _ hm hf]
  simp only [Pi.mul_apply]
  rw [proposalFiber,referenceFiber]
  rw [fiber_lintegral checks (fun i ↦ (μ i).compProd (κ i)) s o
      (fun i ↦ (x i,z i)) (fun p ↦ f (fun i ↦ (p i).1)),
    fiber_lintegral reference μ s o x
      (fun p ↦ conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s p) z*f p)]
  have hw := conditionalDensity_weighted checks μ κ s o x z F hF
  have he : (∫⁻p,f (fun i ↦ (p i).1)*checkWeight checks (s∪o)
      (Function.updateFinset (fun i ↦ (x i,z i)) s p)
      ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))=
      lmarginal μ s (fun y ↦ F y*conditionalDensity checks κ s o y z) x := by
    rw [hw]
    apply lintegral_congr
    intro p
    congr 1
    change f (fun i ↦ (p i).1)=f (fun i : s ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)
    congr 1
    funext i
    simp [Function.updateFinset,i.property]
  rw [he]
  have hp (p : ∀i : s,X i) :
      (conditionalLikelihood reference checks μ κ s o (Function.updateFinset x s p) z*f p)*
        checkWeight reference (s∪o) (Function.updateFinset x s p)=
      (Z₀/Y₀)*(F (Function.updateFinset x s p)*
        conditionalDensity checks κ s o (Function.updateFinset x s p) z) := by
    rw [conditionalLikelihood_update checks reference μ κ,hu]
    have hh := conditionalDensity_reference_support reference checks κ s o hincl
      (Function.updateFinset x s p) z
    calc
      _ = (Z₀/Y₀)*(f p*(checkWeight reference (s∪o) (Function.updateFinset x s p)*
        conditionalDensity checks κ s o (Function.updateFinset x s p) z)) := by ac_rfl
      _ = _ := by rw [hh]
  simp only [hp]
  have hprod : Measurable (fun p : ∀i:s,X i ↦
      F (Function.updateFinset x s p)*conditionalDensity checks κ s o (Function.updateFinset x s p) z) :=
    (hF.mul (measurable_conditionalDensity checks κ s o z)).comp
      (measurable_updateFinset (x:=x) (s:=s))
  rw [lintegral_const_mul _ hprod]
  change Y₀⁻¹ * _ = Z₀⁻¹ *((Z₀/Y₀)*_)
  rw [ENNReal.div_eq_inv_mul]
  calc
    _ = (Z₀⁻¹*Z₀)*(Y₀⁻¹*lmarginal μ s (fun y ↦ F y*conditionalDensity checks κ s o y z) x) := by rw [hZm,one_mul]
    _ = _ := by ac_rfl

end HardSphere.Comparison

end
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

lemma integrated_primary_density (ξ : Measure W) [SFinite ξ]
    (κ : Kernel W A) (η : Kernel W B) [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (f : A→B) (hf : Measurable f) (L : W×B→ℝ≥0∞) (hL : Measurable L)
    (h : ∀ᵐw ∂ξ,(κ w).map f=(η w).withDensity (fun b ↦ L (w,b))) :
    (ξ.compProd κ).map (fun p ↦ (p.1,f p.2))=(ξ.compProd η).withDensity L := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hm : Measurable (fun p : W×A ↦ (p.1,f p.2)) := measurable_fst.prodMk (hf.comp measurable_snd)
  rw [lintegral_map hF hm,Measure.lintegral_compProd (show Measurable (fun p : W×A ↦ F (p.1,f p.2)) from hF.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ hL hF,
    Measure.lintegral_compProd (hL.mul hF)]
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  rw [←lintegral_map (show Measurable (fun b : B ↦ F (w,b)) from hF.comp measurable_prodMk_left) hf,hw,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun b : B ↦ L (w,b)) from hL.comp measurable_prodMk_left)
      (show Measurable (fun b : B ↦ F (w,b)) from hF.comp measurable_prodMk_left)]
  rfl

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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_LocalMoment
attribute [-instance] _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
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
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma local_mean_integrates (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] (U : Finset I) (F : (∀i,X i)→ℝ≥0∞)
    (hF : Measurable F) (A : ℝ≥0∞) (hA : A≠⊤)
    (hlocal : ∀x,x∈retainedEvent checks (Finset.univ\U) →
      lmarginal μ U (fun y ↦ checkWeight checks Finset.univ y*F y) x /
        lmarginal μ U (checkWeight checks Finset.univ) x≤A) :
    (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))≤A := by
  let w := checkWeight checks Finset.univ
  have hw : Measurable w := measurable_checkWeight checks _
  have hraw : (∫⁻x,w x*F x ∂Measure.pi μ)≤A*∫⁻x,w x ∂Measure.pi μ := by
    rw [←lintegral_const_mul _ hw]
    apply lintegral_le_of_lmarginal_le U (f:=fun y ↦ w y*F y) (g:=fun y ↦ A*w y) (hw.mul hF) (measurable_const.mul hw)
    intro x
    have hden : lmarginal μ U w x≠⊤ := by
      have hd : lmarginal μ U w x≤1 := by
        calc
          _≤lmarginal μ U (fun _ ↦ 1) x := lmarginal_mono (checkWeight_le_one checks _) x
          _=1 := by simp [lmarginal]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hd
    by_cases hx : x∈retainedEvent checks (Finset.univ\U)
    · have h := (ENNReal.div_le_iff_le_mul (Or.inr hA) (Or.inl hden)).mp (hlocal x hx)
      change _≤∫⁻u,A*w (Function.updateFinset x U u) ∂Measure.pi (fun i:U ↦ μ i)
      rw [lintegral_const_mul _ (show Measurable (fun u : ∀i:U,X i ↦ w (Function.updateFinset x U u)) from hw.comp measurable_updateFinset)]
      exact h
    · have hz : lmarginal μ U (fun y ↦ w y*F y) x=0 := by
        unfold lmarginal
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro u
        dsimp only
        have hout : checkWeight checks (Finset.univ\U) (Function.updateFinset x U u)=0 := by
          rw [checkWeight_depends checks (Finset.univ\U) (x:=Function.updateFinset x U u) (y:=x)
            (fun i hi ↦ by simp [Function.updateFinset,(Finset.mem_sdiff.mp hi).2])]
          exact Set.indicator_of_notMem hx _
        have hfull : w (Function.updateFinset x U u)=0 := le_antisymm
          ((checkWeight_antitone checks (Finset.subset_univ (Finset.univ\U)) _).trans_eq hout) bot_le
        simp only [hfull,zero_mul,Pi.zero_apply]
      rw [hz]
      exact bot_le
  let Z := (Measure.pi μ) (retainedEvent checks Finset.univ)
  have hZ : (∫⁻x,w x ∂Measure.pi μ)=Z := by
    exact (lintegral_indicator_const (measurableSet_retainedEvent checks _) (1:ℝ≥0∞)).trans (one_mul _)
  have hint : (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))=
      Z⁻¹*∫⁻x,w x*F x ∂Measure.pi μ := by
    rw [conditionedMeasure,lintegral_smul_measure,←lintegral_indicator (measurableSet_retainedEvent checks _)]
    congr 1
    apply lintegral_congr
    intro x
    by_cases hx : x∈retainedEvent checks Finset.univ <;> simp [w,checkWeight,hx]
  rw [hint]
  calc
    _≤Z⁻¹*(A*Z) := mul_le_mul' (le_refl _) (hraw.trans_eq (congrArg (A*·) hZ))
    _≤A := by
      by_cases hz : Z=0
      · simp [hz]
      · have ht : Z≠⊤ := measure_ne_top _ _
        calc
          _=A*(Z⁻¹*Z) := by ac_rfl
          _≤A := by rw [ENNReal.inv_mul_cancel hz ht,mul_one]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ReferenceResample
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

variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma lmarginal_updateFinset (μ : ∀i,Measure (X i)) (s : Finset I)
    (f : (∀i,X i)→ℝ≥0∞) (x : ∀i,X i) (u : ∀i:s,X i) :
    lmarginal μ s f (Function.updateFinset x s u)=lmarginal μ s f x := by
  apply lmarginal_congr
  intro i hi
  simp [Function.updateFinset,hi]

lemma reference_resample (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] (s : Finset I) :
    (insertedLaw checks μ s (Finset.univ\s)
      (conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))).map
      (fun p ↦ Function.updateFinset p.1 s p.2)=
      conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ) := by
  let w := checkWeight checks Finset.univ
  have hw : Measurable w := measurable_checkWeight checks _
  have hs : s∪(Finset.univ\s)=Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ s)
  let Z := (Measure.pi μ) (retainedEvent checks Finset.univ)
  have integral_ref (F : (∀i,X i)→ℝ≥0∞) :
      (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))=
        Z⁻¹*∫⁻x,w x*F x ∂Measure.pi μ := by
    rw [conditionedMeasure,lintegral_smul_measure,←lintegral_indicator (measurableSet_retainedEvent checks _)]
    congr 1
    apply lintegral_congr
    intro x
    by_cases hx : x∈retainedEvent checks Finset.univ <;> simp [w,checkWeight,hx]
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF measurable_updateFinset',insertedLaw,
    Measure.lintegral_compProd (show Measurable (fun p : (∀i,X i)×(∀i:s,X i) ↦ F (Function.updateFinset p.1 s p.2)) from hF.comp (measurable_updateFinset' (s:=s)))]
  have hkernel (x : ∀i,X i) :
      (∫⁻u,F (Function.updateFinset x s u) ∂fiberNormalize
        (Kernel.const _ (Measure.pi fun i:s ↦ μ i))
        (insertionFiberEvent checks s (Finset.univ\s)) x)=
      (lmarginal μ s w x)⁻¹*lmarginal μ s (fun y ↦ w y*F y) x := by
    have he : fiberNormalize (Kernel.const _ (Measure.pi fun i:s ↦ μ i))
        (insertionFiberEvent checks s (Finset.univ\s)) x=
      referenceFiber checks μ s (Finset.univ\s) x := by
      change (fiberRestrict _ _ x univ)⁻¹ • fiberRestrict _ _ x=_
      rw [fiberRestrict_apply _ (insertionFiberEvent_measurable checks s (Finset.univ\s))]
      simp only [Kernel.const_apply,Measure.restrict_apply_univ,referenceFiber,conditionedMeasure]
      rfl
    rw [he,referenceFiber,fiber_lintegral]
    simp only [hs,partialNormalizer]
    congr 1
    apply lintegral_congr
    intro u
    exact mul_comm _ _
  simp_rw [hkernel]
  rw [integral_ref,integral_ref]
  congr 1
  have hA : Measurable (lmarginal μ s w) := hw.lmarginal μ
  have hB : Measurable (lmarginal μ s (fun y ↦ w y*F y)) := (hw.mul hF).lmarginal μ
  apply lintegral_eq_of_lmarginal_eq s (hw.mul (hA.inv.mul hB)) (hw.mul hF)
  funext x
  change lmarginal μ s (fun y ↦ w y*((lmarginal μ s w y)⁻¹*lmarginal μ s (fun z ↦ w z*F z) y)) x = lmarginal μ s (fun y ↦ w y*F y) x
  have hfin : lmarginal μ s w x≠⊤ := by
    apply ne_top_of_le_ne_top ENNReal.one_ne_top
    exact (lmarginal_mono (checkWeight_le_one checks _) x).trans_eq (by simp [lmarginal])
  have he : (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)*
      ((lmarginal μ s w (Function.updateFinset x s u))⁻¹*
        lmarginal μ s (fun y ↦ w y*F y) (Function.updateFinset x s u)))=
      (fun u ↦ w (Function.updateFinset x s u)*((lmarginal μ s w x)⁻¹*
        lmarginal μ s (fun y ↦ w y*F y) x)) := by
    funext u
    simp only [lmarginal_updateFinset]
  change (∫⁻u,w (Function.updateFinset x s u)*
      ((lmarginal μ s w (Function.updateFinset x s u))⁻¹*
        lmarginal μ s (fun y ↦ w y*F y) (Function.updateFinset x s u))
      ∂Measure.pi (fun i:s ↦ μ i))=_
  rw [he,lintegral_mul_const _ ((show Measurable (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)) from hw.comp (measurable_updateFinset (s:=s) (x:=x))))]
  change lmarginal μ s w x*((lmarginal μ s w x)⁻¹*lmarginal μ s (fun y ↦ w y*F y) x)=_
  by_cases hz : lmarginal μ s w x=0
  · have hwz : ∀ᵐu ∂Measure.pi (fun i:s ↦ μ i), w (Function.updateFinset x s u)=0 :=
      (lintegral_eq_zero_iff' ((show Measurable (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)) from hw.comp (measurable_updateFinset (s:=s) (x:=x)))).aemeasurable).mp hz
    have hb : lmarginal μ s (fun y ↦ w y*F y) x=0 :=
      lintegral_eq_zero_of_ae_eq_zero (hwz.mono fun u hu ↦ by simp [hu])
    rw [hz,hb,mul_zero,mul_zero]
  · rw [←mul_assoc,ENNReal.mul_inv_cancel hz hfin,one_mul]

lemma reference_fiber_positive (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] (s : Finset I) :
    ∀ᵐx ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ),
      0<partialNormalizer checks μ s (Finset.univ\s) x := by
  let w := checkWeight checks Finset.univ
  have hw : Measurable w := measurable_checkWeight checks _
  let A : Set (∀i,X i) := {x | lmarginal μ s w x=0}
  have hA : MeasurableSet A := measurableSet_eq_fun (hw.lmarginal μ) measurable_const
  let F : (∀i,X i)→ℝ≥0∞ := A.indicator (fun _ ↦ 1)
  have hF : Measurable F := measurable_const.indicator hA
  have he (x : ∀i,X i) (u : ∀i:s,X i) : F (Function.updateFinset x s u)=F x := by
    simp only [F,A,indicator_apply,mem_ofPred_eq,lmarginal_updateFinset]
  have hbound := local_mean_integrates checks μ s F hF 0 (by norm_num) (by
    intro x hx
    have hnum : lmarginal μ s (fun y ↦ w y*F y) x=0 := by
      change (∫⁻u,w (Function.updateFinset x s u)*F (Function.updateFinset x s u)
        ∂Measure.pi (fun i:s ↦ μ i))=0
      simp_rw [he]
      rw [lintegral_mul_const _ ((show Measurable (fun u : ∀i:s,X i ↦ w (Function.updateFinset x s u)) from hw.comp (measurable_updateFinset (s:=s) (x:=x))))]
      change lmarginal μ s w x*F x=0
      by_cases ha : x∈A
      · rw [show lmarginal μ s w x=0 from ha,zero_mul]
      · rw [show F x=0 from indicator_of_notMem ha _,mul_zero]
    change lmarginal μ s (fun y ↦ w y*F y) x/lmarginal μ s w x≤0
    rw [hnum,ENNReal.zero_div])
  have hz : (conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ)) A=0 := by
    have h : (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ))=0 :=
      le_antisymm hbound bot_le
    simpa only [F,lintegral_indicator_const hA,one_mul] using h
  have hae : ∀ᵐx ∂conditionedMeasure (Measure.pi μ) (retainedEvent checks Finset.univ),x∉A := by
    exact measure_eq_zero_iff_ae_notMem.mp hz
  filter_upwards [hae] with x hx
  have hs : s∪(Finset.univ\s)=Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ s)
  simpa only [partialNormalizer,checkNormalizer,hs,pos_iff_ne_zero] using (show lmarginal μ s w x≠0 from hx)

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I C R : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype R]
  {X Z : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]

omit [Fintype I] in
lemma measurable_proposalEvent (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (s o : Finset I) (z : ∀i,Z i) : MeasurableSet (proposalEvent checks s o z) := by
  apply (measurableSet_retainedEvent checks (s∪o)).preimage
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈s
  · simpa only [Function.updateFinset,dite_eq_left hi,Function.comp_def] using
      (measurable_pi_apply (⟨i,hi⟩:s)).comp (measurable_snd : Measurable (Prod.snd : (∀i,X i)×(∀i:s,X i×Z i)→_))
  · simpa only [Function.updateFinset,dite_eq_right hi,Function.comp_def] using
      (((measurable_pi_apply i).comp (measurable_fst : Measurable (Prod.fst : (∀i,X i)×(∀i:s,X i×Z i)→_))).prodMk measurable_const)

omit [Fintype I] in
lemma proposalKernel_apply (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) (x : ∀i,X i) :
    proposalKernel checks μ κ s o z x=proposalFiber checks μ κ s o x z := by
  change (fiberRestrict _ _ x univ)⁻¹ • fiberRestrict _ _ x=_
  rw [fiberRestrict_apply _ (measurable_proposalEvent checks s o z)]
  simp only [Kernel.const_apply,Measure.restrict_apply_univ,proposalFiber,conditionedMeasure]
  rfl

lemma full_primary_law (reference : R→LocalCheck X)
    (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s : Finset I) (z : ∀i,Z i)
    (hincl : ∀(y : ∀i,X i)(u : ∀i,Z i),
      checkWeight checks Finset.univ (fun i ↦ (y i,u i)) ≤ checkWeight reference Finset.univ y) :
    ((conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ)).compProd
      (proposalKernel checks μ κ s (Finset.univ\s) z)).map
      (fun p ↦ Function.updateFinset p.1 s (fun i ↦ (p.2 i).1))=
    (conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ)).withDensity
      (fun x ↦ conditionalLikelihood reference checks μ κ s (Finset.univ\s) x z) := by
  let ξ := conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ)
  let η := fiberNormalize (Kernel.const _ (Measure.pi fun i:s ↦ μ i))
    (insertionFiberEvent reference s (Finset.univ\s))
  let π : (∀i:s,X i×Z i)→(∀i:s,X i) := fun p i ↦ (p i).1
  have hπ : Measurable π := Measurable.of_eval (fun i ↦ measurable_fst.comp (measurable_pi_apply i))
  let upd : (∀i,X i)×(∀i:s,X i)→(∀i,X i) := fun p ↦ Function.updateFinset p.1 s p.2
  have hu : Measurable upd := measurable_updateFinset'
  let L : (∀i,X i)→ℝ≥0∞ := fun x ↦ conditionalLikelihood reference checks μ κ s (Finset.univ\s) x z
  have hL : Measurable L := measurable_conditionalLikelihood reference checks μ κ s _ z
  have he : (ξ.compProd (proposalKernel checks μ κ s (Finset.univ\s) z)).map
      (fun p ↦ (p.1,π p.2))=(ξ.compProd η).withDensity (L∘upd) := by
    apply integrated_primary_density ξ _ η π hπ (L∘upd) (hL.comp hu)
    filter_upwards [reference_fiber_positive reference μ s] with x hx
    rw [proposalKernel_apply]
    have heq : η x=referenceFiber reference μ s (Finset.univ\s) x := by
      change (fiberRestrict _ _ x univ)⁻¹ • fiberRestrict _ _ x=_
      rw [fiberRestrict_apply _ (insertionFiberEvent_measurable reference s (Finset.univ\s))]
      simp only [Kernel.const_apply,Measure.restrict_apply_univ,referenceFiber,conditionedMeasure]
      rfl
    rw [heq]
    apply proposalFiber_primary checks reference μ κ s _ x z hx
    simpa only [Finset.union_sdiff_of_subset (Finset.subset_univ s)] using hincl
  have he' := congrArg (fun ν ↦ ν.map upd) he
  rw [Measure.map_map hu (show Measurable (fun p : (∀i,X i)×(∀i:s,X i×Z i) ↦ (p.1,π p.2)) from measurable_fst.prodMk (hπ.comp measurable_snd)),map_density_comp _ upd hu L hL] at he'
  change _=((insertedLaw reference μ s (Finset.univ\s) ξ).map upd).withDensity L at he'
  rw [reference_resample reference μ s] at he'
  exact he'

end HardSphere.Comparison

end
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

lemma datumIndividualReference_apply {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S t : ℝ) (u : Time) (i : Fin N)
    (d : PhysicalDatum N K M G L) :
    datumIndividualReference hL g m r R C S t u i d=
      individualReference t (datumStart hL d i) (datumEnd hL d i)
        (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u i) :=
  parameterIndividualReference_apply ..

end HardSphere.Groups

end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_AddedSites
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace HardSphere.Lattice
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
lemma mem_encounterSet (e : V → V → Prop) (P Q : Finset V) (x y : V) :
    (x,y)∈encounterSet e P Q ↔ x∈P ∧ y∈Q ∧ e x y := by
  simp only [encounterSet,Finset.mem_filter,Finset.mem_product]
  tauto

end HardSphere.Lattice

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteGeometry
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar
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

lemma nearest_project_distance {L : Length} {x y : Vertex} (h : nearestStep x y) :
    torusDistance L (projectPoint L (fun k ↦ (x k:ℝ)))
      (projectPoint L (fun k ↦ (y k:ℝ)))≤1 := by
  obtain ⟨j,hj,hh⟩ := h
  have hc (i : Fin 3) : dist (((x i:ℝ):AddCircle L.val)) ((y i:ℝ):AddCircle L.val)≤
      if i=j then (1:ℝ) else 0 := by
    rw [dist_eq_norm,←AddCircle.coe_sub]
    refine (QuotientAddGroup.norm_mk_le_norm (m:=(x i:ℝ)-(y i:ℝ))).trans ?_
    rw [Real.norm_eq_abs]
    by_cases hi : i=j
    · subst i
      simp only
      exact_mod_cast le_of_eq hj
    · simp only [ite_eq_right hi,hh i hi,sub_self,abs_zero,le_refl]
  unfold torusDistance
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by norm_num,?_⟩
  calc
    _ ≤ ∑ i : Fin 3,(if i=j then (1:ℝ) else 0)^2 := Finset.sum_le_sum fun i _ ↦
      (sq_le_sq₀ dist_nonneg (by split_ifs <;> norm_num)).mpr (hc i)
    _ = 1^2 := by simp

lemma adjacent_center_distance {K : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) {x y : DiscreteTorus K} (h : (torusNearestGraph K).Adj x y) :
    torusDistance L (gridCenter L (siteIndex x)) (gridCenter L (siteIndex y))≤1 := by
  obtain ⟨_,v,w,hv,hw,hn⟩ := h
  subst x y
  change torusDistance L (projectPoint L (anchorPoint (siteIndex (torusProjection K v))))
    (projectPoint L (anchorPoint (siteIndex (torusProjection K w))))≤1
  rw [siteIndex_project_lift hL,siteIndex_project_lift hL]
  exact nearest_project_distance hn

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RoutePartition
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {I V : Type*} [DecidableEq I]
omit [DecidableEq I] in
lemma mem_nearSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) (i : I) :
    i∈nearSlots e c s t ↔ i∈s ∧ ∃j∈t,e (c i) (c j) := by simp [nearSlots]
omit [DecidableEq I] in
lemma nearSlots_card [DecidableEq V] (e : V→V→Prop) (c : I→V) (s t : Finset I)
    (hi : Set.InjOn c (s:Set I)) :
    (nearSlots e c s t).card≤(encounterSet e (s.image c) (t.image c)).card := by
  have hsub : (nearSlots e c s t).image c⊆
      (encounterSet e (s.image c) (t.image c)).image Prod.fst := by
    intro v hv
    obtain ⟨i,hi',rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨his,j,hjt,he⟩ := (mem_nearSlots e c s t i).mp hi'
    exact Finset.mem_image.mpr ⟨(c i,c j),(mem_encounterSet e _ _ _ _).mpr
      ⟨Finset.mem_image.mpr ⟨i,his,rfl⟩,Finset.mem_image.mpr ⟨j,hjt,rfl⟩,he⟩,rfl⟩
  have hin : Set.InjOn c (nearSlots e c s t:Set I) := hi.mono (Finset.filter_subset _ _)
  rw [←Finset.card_image_of_injOn hin]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end HardSphere.Comparison

end
end

section
noncomputable section
namespace HardSphere.Comparison
variable {J : Type*}

lemma routePermutation_label {d : ℕ} (labels : Fin d↪J) (i : Fin d) :
    routePermutation labels (some (labels i))=routeEmbedding labels i.succ := by
  rw [←routeEmbedding_castSucc labels i]
  change (finRotate (d+1)).viaEmbedding (routeEmbedding labels) _=_
  rw [Equiv.Perm.viaEmbedding_apply]
  congr 1
  exact finRotate_of_lt i.isLt

lemma routePermutation_star (d : ℕ) (labels : Fin (d+1)↪J) :
    routePermutation labels none=some (labels 0) := by
  rw [←routeEmbedding_last labels]
  change (finRotate (d+1+1)).viaEmbedding (routeEmbedding labels) _=_
  rw [Equiv.Perm.viaEmbedding_apply,finRotate_last]
  exact routeEmbedding_castSucc labels 0

lemma routePermutation_lastLabel (d : ℕ) (labels : Fin (d+1)↪J) :
    routePermutation labels (some (labels (Fin.last d)))=none := by
  rw [routePermutation_label]
  exact routeEmbedding_last labels

lemma routeSlots_exact {d : ℕ} [DecidableEq J] (labels : Fin d↪J) :
    routeSlots labels=insert none (Finset.univ.image (fun i ↦ some (labels i))) := by
  ext x
  simp only [routeSlots,Finset.mem_map,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_image]
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<d
    · exact Or.inr ⟨⟨i.val,hi⟩,by change _=(if h : i.val<d then _ else _);rw [dite_eq_left hi]⟩
    · exact Or.inl (by change (if h : i.val<d then _ else _)=_;rw [dite_eq_right hi])
  · rintro (rfl|⟨i,rfl⟩)
    · exact ⟨Fin.last d,routeEmbedding_last labels⟩
    · exact ⟨i.castSucc,routeEmbedding_castSucc labels i⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SparseChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Wiener
attribute [local irreducible] torusDistance

lemma confined_far_avoid {L : Length} (v w : Torus L) (f g : ConfigurationPath 1 L)
    (hf : Confined v f) (hg : Confined w g) (hfar : 21<torusDistance L v w)
    {r : ℝ} (hr : r≤1) : ∀s : Time,r<torusDistance L (f s 0) (g s 0) := by
  intro s
  have h₁ := torusDistance_triangle' L v (f s 0) w
  have h₂ := torusDistance_triangle' L (f s 0) (g s 0) w
  rw [torusDistance_comm L v (f s 0)] at h₁
  have hh := hf s
  have hh' := hg s
  linarith

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSparse
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]

omit [Fintype J] [DecidableEq J] in
lemma physicalSparseChecks_complete (r : ℝ) (hr : r≤1)
    (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (hconf : ∀j,∀f : allowed j,Confined (anchor j) (projectCurve L f.val))
    (owner : Bool → J → I) (path : ∀b j,V (owner b j) → allowed j)
    (hpath : ∀b j,Measurable (path b j)) (x : ∀i,V i)
    (hx : x∈retainedEvent (physicalSparseChecks r anchor allowed owner path hpath) Finset.univ) :
    ∀b j k,j≠k → ¬TrialCollision r (projectCurve L (path b k (x (owner b k))).val)
      (path b j (x (owner b j))).val := by
  intro b j k hjk
  by_cases hn : torusDistance L (anchor j) (anchor k)≤21
  · exact hx (b,⟨(j,k),hjk,hn⟩) (Finset.subset_univ _)
  · rintro ⟨s,hs⟩
    exact (not_le_of_gt (confined_far_avoid (anchor j) (anchor k)
      (projectCurve L (path b j (x (owner b j))).val)
      (projectCurve L (path b k (x (owner b k))).val)
      (hconf _ _) (hconf _ _) (lt_of_not_ge hn) hr s)) hs

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [DecidableEq I] in
lemma fiberEquiv_pi {i j : I} (h : i=j) (x : ∀i,X i) : fiberEquiv h (x i)=x j := by
  subst j
  rfl

variable (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_primary (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))
    (u : Finset I) (p : ∀i,X i×X (σ.symm i))
    (hp : p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) u) :
    (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) u := by
  intro e he
  exact hp (false,e.2) he

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_unselected (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (j : J) (hj : label j∉S)
    (p : ∀i,X i×X (σ.symm i)) :
    routePath σ S hfix allowed label get true j (p (routeOwner σ label true j))=
      get j (p (label j)).1 := by
  simp only [routePath,dite_eq_right hj]
  exact congrArg (get j) (fiberEquiv_pi (hfix (label j) hj) (fun i ↦ (p i).1))

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ReversePair
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma partialReversePairs_selected (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (p : ∀i,X i×X (σ.symm i)) (j : I) (hj : j∈s) :
    partialReversePairs σ s hf p j=
      (fiberEquiv (σ.symm_apply_apply j) (p (σ j)).2,(p (σ j)).1) := by
  change partialReverseFactor σ s hf j (p (σ j))=_
  simp only [partialReverseFactor,dite_eq_left hj,reverseFactor]
  rfl
omit [Fintype I] in
lemma partialReversePairs_outside_fst (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (p : ∀i,X i×X (σ.symm i)) (j : I) (hj : j∉s) :
    (partialReversePairs σ s hf p j).1=(p j).1 := by
  change (partialReverseFactor σ s hf j (p (σ j))).1=_
  simp only [partialReverseFactor,dite_eq_right hj]
  change fiberEquiv (hf j hj) (p (σ j)).1=(p j).1
  exact fiberEquiv_pi (hf j hj) (fun i ↦ (p i).1)

variable {J : Type*} [Fintype J] [DecidableEq J]
omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma partialReverse_primary_path (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j)
    (p : ∀i,X i×X (σ.symm i)) (j : J) :
    get j (partialReversePairs σ s hf p (label j)).1=
      routePath σ s hf allowed label get true j (p (routeOwner σ label true j)) := by
  by_cases hj : label j∈s
  · rw [partialReversePairs_selected σ s hf p _ hj]
    simp only [routePath,dite_eq_left hj]
    rfl
  · rw [partialReversePairs_outside_fst σ s hf p _ hj,
      routePath_unselected σ s hf allowed label get j hj]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma partialReverse_secondary_path (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j)
    (p : ∀i,X i×X (σ.symm i)) (j : J) :
    routePath σ.symm s (reverse_fix σ s hf) allowed label get true j
      (partialReversePairs σ s hf p (routeOwner σ.symm label true j))=get j (p (label j)).1 := by
  by_cases hj : label j∈s
  · have hj' : σ.symm (label j)∈s :=
      (move_mem_iff σ.symm s (reverse_fix σ s hf) _).mpr hj
    simp only [routePath,dite_eq_left hj]
    change get j (fiberEquiv (σ.apply_symm_apply (label j))
      (partialReversePairs σ s hf p (σ.symm (label j))).2)=get j (p (label j)).1
    rw [partialReversePairs_selected σ s hf p _ hj']
    exact congrArg (get j) (fiberEquiv_pi (σ.apply_symm_apply (label j)) (fun i ↦ (p i).1))
  · rw [routePath_unselected σ.symm s (reverse_fix σ s hf) allowed label get j hj,
      partialReversePairs_outside_fst σ s hf p _ hj]

omit [Fintype J] [DecidableEq J] in
lemma partialReverse_checks {L : Length} (σ : Equiv.Perm I) (s : Finset I)
    (hf : ∀i,i∉s→σ i=i) (r : ℝ) (anchor : J→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j)) :
    (partialReversePairs σ s hf)⁻¹'
      retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ=
    retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ := by
  ext p
  constructor
  · intro hp e _
    rcases e with ⟨b,e⟩
    cases b
    · have hh := hp (true,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.2
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.2))).val)
        (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.1
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.1))).val at hh
      rw [partialReverse_secondary_path,partialReverse_secondary_path] at hh
      exact hh
    · have hh := hp (false,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hf p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hf p (label e.val.1)).1).val at hh
      rw [partialReverse_primary_path σ s hf allowed label get p e.val.2,
        partialReverse_primary_path σ s hf allowed label get p e.val.1] at hh
      exact hh
  · intro hp e _
    rcases e with ⟨b,e⟩
    cases b
    · change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hf p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hf p (label e.val.1)).1).val
      rw [partialReverse_primary_path σ s hf allowed label get p e.val.2,
        partialReverse_primary_path σ s hf allowed label get p e.val.1]
      exact hp (true,e) (Finset.subset_univ _)
    · change ¬TrialCollision r
        (projectCurve L (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.2
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.2))).val)
        (routePath σ.symm s (reverse_fix σ s hf) allowed label get true e.val.1
          (partialReversePairs σ s hf p (routeOwner σ.symm label true e.val.1))).val
      rw [partialReverse_secondary_path,partialReverse_secondary_path]
      exact hp (false,e) (Finset.subset_univ _)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_SelectedReverse
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.conditioned_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*}
  [∀i,MeasurableSpace (X i)]

omit [Fintype I] in
lemma reverseSelected_product (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (μ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (Measure.pi μ).map (reverseSelected σ s hf)=
      Measure.pi (fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j)) := by
  let e := MeasurableEquiv.piCongrLeft (fun i:s ↦ X i×X (σ.symm i)) (selectedPerm σ s hf)
  have h₁ : MeasurePreserving e.symm (Measure.pi μ)
      (Measure.pi fun j:s ↦ μ (selectedPerm σ s hf j)) :=
    MeasurePreserving.symm e (measurePreserving_piCongrLeft μ (selectedPerm σ s hf))
  have : ∀j:s, IsFiniteMeasure ((μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j)) := by
    intro j
    let : IsFiniteMeasure (μ (selectedPerm σ s hf j)) := (inferInstance : ∀i,IsFiniteMeasure (μ i)) _
    constructor
    rw [Measure.map_apply (reverseFactor (X:=X) σ j).measurable MeasurableSet.univ]
    simpa only [Set.preimage_univ] using (measure_lt_top (μ (selectedPerm σ s hf j)) Set.univ)
  have h₂ : MeasurePreserving (MeasurableEquiv.piCongrRight (fun j:s ↦ reverseFactor (X:=X) σ j))
      (Measure.pi fun j:s ↦ μ (selectedPerm σ s hf j))
      (Measure.pi fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j)) :=
    measurePreserving_pi (fun j:s ↦ μ (selectedPerm σ s hf j))
      (fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j))
      (fun j : s ↦ ⟨(reverseFactor (X:=X) σ j).measurable,rfl⟩)
  exact (h₂.comp h₁).map_eq

omit [Fintype I] in
lemma partialReverse_update (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (b : ∀i,X i×X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    partialReversePairs σ s hf (Function.updateFinset b s p)=
      Function.updateFinset (partialReversePairs σ s hf b) s (reverseSelected σ s hf p) := by
  funext j
  by_cases hj : j∈s
  · rw [partialReversePairs_selected σ s hf _ j hj]
    have hj' : σ j∈s := (move_mem_iff σ s hf j).mpr hj
    simp only [Function.updateFinset,dite_eq_left hj,dite_eq_left hj']
    rfl
  · have hj' : σ j∉s := fun h ↦ hj ((move_mem_iff σ s hf j).mp h)
    simp only [Function.updateFinset,dite_eq_right hj]
    change partialReverseFactor σ s hf j (Function.updateFinset b s p (σ j))=_
    simp only [Function.updateFinset,dite_eq_right hj']
    rfl

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma selected_physical_conditioned_reverse {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (b : ∀i,X i×X (σ.symm i))
    (μ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (conditionedMeasure (Measure.pi μ) {p | Function.updateFinset b s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ}).map
      (reverseSelected σ s hf)=
    conditionedMeasure (Measure.pi fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j))
      {p | Function.updateFinset (partialReversePairs σ s hf b) s p∈
        retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ} := by
  let A : Set (∀j:s,X j×X (σ j)) := {p | Function.updateFinset (partialReversePairs σ s hf b) s p∈
        retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ}
  have hA : MeasurableSet A := (measurableSet_retainedEvent _ _).preimage
    measurable_updateFinset
  have he : (reverseSelected σ s hf)⁻¹' A={p | Function.updateFinset b s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ} := by
    ext p
    simp only [Set.mem_preimage,A,Set.mem_ofPred_eq]
    rw [←partialReverse_update σ s hf b p]
    exact Set.ext_iff.mp (partialReverse_checks σ s hf r anchor allowed label get hg)
      (Function.updateFinset b s p)
  rw [←he,conditioned_map_preimage _ _ (reverseSelected σ s hf).measurable hA,
    reverseSelected_product]

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_update_base (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (allowed : J→Set C(Time,Point)) (label : J→I) (get : ∀j,X (label j)→allowed j)
    (b b' : ∀i,X i×X (σ.symm i)) (he : ∀i,i∉s→(b i).1=(b' i).1)
    (p : ∀i:s,X i×X (σ.symm i)) (c : Bool) (j : J) :
    routePath σ s hf allowed label get c j (Function.updateFinset b s p (routeOwner σ label c j))=
    routePath σ s hf allowed label get c j (Function.updateFinset b' s p (routeOwner σ label c j)) := by
  cases c
  · change get j (Function.updateFinset b s p (label j)).1=get j (Function.updateFinset b' s p (label j)).1
    by_cases hj : label j∈s
    · simp only [Function.updateFinset,dite_eq_left hj]
    · simpa only [Function.updateFinset,dite_eq_right hj] using congrArg (get j) (he _ hj)
  · by_cases hj : label j∈s
    · have hh : σ (label j)∈s := (move_mem_iff σ s hf _).mpr hj
      change routePath σ s hf allowed label get true j (Function.updateFinset b s p (σ (label j))) =
        routePath σ s hf allowed label get true j (Function.updateFinset b' s p (σ (label j)))
      simp only [Function.updateFinset,dite_eq_left hh]
    · rw [routePath_unselected σ s hf allowed label get j hj,
        routePath_unselected σ s hf allowed label get j hj]
      simpa only [Function.updateFinset,dite_eq_right hj] using congrArg (get j) (he _ hj)

omit [Fintype J] [DecidableEq J] in
lemma route_fill_event_congr {L : Length} (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (b b' : ∀i,X i×X (σ.symm i)) (he : ∀i,i∉s→(b i).1=(b' i).1) :
    {p | Function.updateFinset b s p∈retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ}=
    {p | Function.updateFinset b' s p∈retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ} := by
  ext p
  change (∀e, _ → _) ↔ (∀e, _ → _)
  apply forall_congr'
  intro e
  apply imp_congr_right
  intro _he'
  change (¬TrialCollision r
    (projectCurve L (routePath σ s hf allowed label get e.1 e.2.val.2
      (Function.updateFinset b s p (routeOwner σ label e.1 e.2.val.2))).val)
    (routePath σ s hf allowed label get e.1 e.2.val.1
      (Function.updateFinset b s p (routeOwner σ label e.1 e.2.val.1))).val) ↔ _
  rw [routePath_update_base σ s hf allowed label get b b' he,
    routePath_update_base σ s hf allowed label get b b' he]
  rfl

lemma selected_reverse_same_outside {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i))
    (μ : ∀i:s,Measure (X i×X (σ.symm i))) [∀i,IsFiniteMeasure (μ i)] :
    (conditionedMeasure (Measure.pi μ) {p | Function.updateFinset (fun i ↦ (x i,z i)) s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) Finset.univ}).map
      (reverseSelected σ s hf)=
    conditionedMeasure (Measure.pi fun j:s ↦ (μ (selectedPerm σ s hf j)).map (reverseFactor (X:=X) σ j))
      {p | Function.updateFinset (fun i ↦ (x i,w i)) s p∈
        retainedEvent (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) Finset.univ} := by
  rw [selected_physical_conditioned_reverse σ s hf r anchor allowed label get hg]
  congr 1
  apply route_fill_event_congr σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg
  intro i hi
  exact partialReversePairs_outside_fst σ s hf (fun i ↦ (x i,z i)) i hi

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteFrozen
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]
  (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
  (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
  (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_primary_weight (u : Finset I) (p : ∀i,X i×X (σ.symm i)) :
    checkWeight (routeChecks σ S hfix r anchor allowed label get hg) u p≤
      checkWeight (primaryChecks r anchor allowed label get hg) u (fun i ↦ (p i).1) := by
  by_cases hp : p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) u
  · rw [checkWeight,Set.indicator_of_mem hp,checkWeight,
      Set.indicator_of_mem (routeChecks_primary σ S hfix r anchor allowed label get hg u p hp)]
  · rw [checkWeight,Set.indicator_of_notMem hp]
    exact bot_le

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma proposalKernel_reverse {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) :
    (proposalKernel (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z).map
      (reverseSelected σ s hf)=
    proposalKernel (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg)
      ν η s (Finset.univ\s) w := by
  ext x B hB
  rw [Kernel.map_apply _ (reverseSelected σ s hf).measurable x,
    proposalKernel_apply,proposalKernel_apply]
  change ((conditionedMeasure (Measure.pi fun i:s ↦ (μ i).compProd (κ i))
    {p | Function.updateFinset (fun i ↦ (x i,z i)) s p∈
      retainedEvent (routeChecks σ s hf r anchor allowed label get hg) (s∪(Finset.univ\s))}).map
      (reverseSelected σ s hf)) B=_
  simp only [Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rw [selected_reverse_same_outside σ s hf r anchor allowed label get hg x z w]
  simp_rw [show ∀j:s,((μ ((selectedPerm σ s hf) j)).compProd (κ ((selectedPerm σ s hf) j))).map
      (reverseFactor (X:=X) σ j)=(ν j).compProd (η j) from he]
  simp only [proposalFiber, Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rfl

lemma full_paired_reverse {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i))
    (ξ : Measure (∀i,X i)) [SFinite ξ] :
    (ξ.compProd (proposalKernel (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z)).map
      (Prod.map id (reverseSelected σ s hf))=
    ξ.compProd (proposalKernel (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg)
      ν η s (Finset.univ\s) w) := by
  rw [←Measure.compProd_map (reverseSelected σ s hf).measurable,
    proposalKernel_reverse σ s hf r anchor allowed label get hg μ ν κ η he z w]

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_ExtraReference
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
open scoped ENNReal
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma lintegral_ignore_coordinate (μ ν : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (F : (∀i,X i)→ℝ≥0∞) (hF : Measurable F)
    (hignore : ∀x y,F (Function.update x j y)=F x) :
    (∫⁻x,F x ∂Measure.pi μ)=∫⁻x,F x ∂Measure.pi ν := by
  let x₀ : ∀i,X i := fun i ↦ Classical.choice (nonempty_of_isProbabilityMeasure (μ i))
  rw [lintegral_eq_lmarginal_univ (μ:=μ) x₀,lintegral_eq_lmarginal_univ (μ:=ν) x₀,
    lmarginal_erase' (μ:=μ) F hF (Finset.mem_univ j),lmarginal_erase' (μ:=ν) F hF (Finset.mem_univ j)]
  simp_rw [hignore,lintegral_const,measure_univ,mul_one]
  unfold lmarginal
  congr 2
  funext i
  exact he i (Finset.mem_erase.mp i.property).1

lemma conditioned_lintegral_ignore (μ ν : ∀i,Measure (X i))
    [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (A : Set (∀i,X i)) (hA : MeasurableSet A)
    (hAi : ∀x y,Function.update x j y∈A↔x∈A)
    (F : (∀i,X i)→ℝ≥0∞) (hF : Measurable F)
    (hFi : ∀x y,F (Function.update x j y)=F x) :
    (∫⁻x,F x ∂conditionedMeasure (Measure.pi μ) A)=
      ∫⁻x,F x ∂conditionedMeasure (Measure.pi ν) A := by
  have hw (x : ∀i,X i) (y : X j) :
      A.indicator (fun _ ↦ (1:ℝ≥0∞)) (Function.update x j y)=A.indicator (fun _ ↦ 1) x := by
    by_cases hx : x∈A
    · rw [indicator_of_mem ((hAi x y).mpr hx),indicator_of_mem hx]
    · rw [indicator_of_notMem ((hAi x y).not.mpr hx),indicator_of_notMem hx]
  have hm : (Measure.pi μ) A=(Measure.pi ν) A := by
    have hh := lintegral_ignore_coordinate μ ν j he _ (measurable_const.indicator hA) hw
    simpa only [lintegral_indicator_const hA,one_mul] using hh
  rw [conditionedMeasure,conditionedMeasure,lintegral_smul_measure,lintegral_smul_measure,hm]
  congr 1
  rw [←lintegral_indicator hA,←lintegral_indicator hA]
  apply lintegral_ignore_coordinate μ ν j he _ (hF.indicator hA)
  intro x y
  by_cases hx : x∈A
  · rw [indicator_of_mem ((hAi x y).mpr hx),indicator_of_mem hx,hFi]
  · rw [indicator_of_notMem ((hAi x y).not.mpr hx),indicator_of_notMem hx]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ActualOutside
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]
omit [Fintype I] [Fintype C] in
lemma retainedEvent_ignore (checks : C→LocalCheck X) (j : I)
    (hj : ∀c,j∉(checks c).support) (s : Finset I) (x : ∀i,X i) (y : X j) :
    Function.update x j y∈retainedEvent checks s ↔ x∈retainedEvent checks s := by
  have he (c : C) : (checks c).pass (Function.update x j y) ↔ (checks c).pass x := by
    apply (checks c).depends
    intro i hi
    exact Function.update_of_ne (show i≠j from fun h ↦ hj c (h ▸ hi)) y x
  simp only [retainedEvent,Set.mem_ofPred_eq,he]
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I→Type*} [∀i,MeasurableSpace (X i)]
omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma primaryChecks_ignore_star (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (s : Finset I) (x : ∀i,X i) (y : X star) :
    Function.update x star y∈retainedEvent (primaryChecks r anchor allowed label get hg) s ↔
      x∈retainedEvent (primaryChecks r anchor allowed label get hg) s := by
  apply retainedEvent_ignore
  intro c
  simp only [primaryChecks,physicalSparseChecks,factorPathCheck,dependentCheck,
    Finset.mem_insert,Finset.mem_singleton,not_or]
  exact ⟨(hstar _).symm,(hstar _).symm⟩

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] [DecidableEq I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma conditioned_kernel_ignore {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (j : I) (he : ∀i,i≠j→μ i=ν i)
    (A : Set (∀i,X i)) (hA : MeasurableSet A) (hAi : ∀x y,Function.update x j y∈A↔x∈A)
    (κ : Kernel (∀i,X i) Y) [IsSFiniteKernel κ]
    (hi : ∀x y,κ (Function.update x j y)=κ x)
    (f : (∀i,X i)×Y→Z) (hf : Measurable f)
    (hfi : ∀x y p,f (Function.update x j y,p)=f (x,p)) :
    ((conditionedMeasure (Measure.pi μ) A).compProd κ).map f=
      ((conditionedMeasure (Measure.pi ν) A).compProd κ).map f := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hf,lintegral_map hF hf]
  change (∫⁻a,(F∘f) a ∂(conditionedMeasure (Measure.pi μ) A).compProd κ)=
    ∫⁻a,(F∘f) a ∂(conditionedMeasure (Measure.pi ν) A).compProd κ
  rw [Measure.lintegral_compProd (hF.comp hf),Measure.lintegral_compProd (hF.comp hf)]
  apply conditioned_lintegral_ignore μ ν j he A hA hAi _
    (hF.comp hf).lintegral_kernel_prod_right'
  intro x y
  rw [hi]
  apply lintegral_congr
  intro p
  exact congrArg F (hfi x y p)

variable {C : Type*} [Fintype C] {Z : I→Type*} [∀i,MeasurableSpace (Z i)]
omit [Fintype I] in
lemma proposalKernel_ignore_selected (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (s o : Finset I) (z : ∀i,Z i) (j : I) (hj : j∈s) (x : ∀i,X i) (y : X j) :
    proposalKernel checks μ κ s o z (Function.update x j y)=proposalKernel checks μ κ s o z x := by
  rw [proposalKernel_apply,proposalKernel_apply]
  unfold proposalFiber
  congr 1
  ext p
  suffices hh : Function.updateFinset (fun i ↦ (Function.update x j y i,z i)) s p=
      Function.updateFinset (fun i ↦ (x i,z i)) s p by
    change _∈retainedEvent checks (s∪o) ↔ _∈retainedEvent checks (s∪o)
    rw [hh]
  funext i
  by_cases his : i∈s
  · simp [Function.updateFinset,his]
  · simp only [Function.updateFinset,dite_eq_right his]
    rw [Function.update_of_ne (show i≠j from fun h ↦ his (h.symm ▸ hj))]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_ActualReverse
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma actual_reverse_trimmed {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (P Q : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (P i)] [∀i,IsProbabilityMeasure (Q i)]
    (hPQ : ∀i,i≠star→P i=Q i)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) :
    ((conditionedMeasure (Measure.pi P) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).compProd
      (proposalKernel (routeChecks σ s hf r anchor allowed label get hg) μ κ s (Finset.univ\s) z)).map
      (fun p ↦ ((fun i : {i // i∉s} ↦ p.1 i),reverseSelected σ s hf p.2))=
    ((conditionedMeasure (Measure.pi Q) (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).compProd
      (proposalKernel (routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg) ν η s (Finset.univ\s) w)).map
      (fun p ↦ ((fun i : {i // i∉s} ↦ p.1 i),p.2)) := by
  let A := retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ
  let π : ((∀i,X i)×(∀i:s,X i×X (σ i)))→((∀i:{i // i∉s},X i)×(∀i:s,X i×X (σ i))) :=
    fun p ↦ ((fun i ↦ p.1 i),p.2)
  have hπ : Measurable π := by fun_prop
  have hh := congrArg (fun M ↦ M.map π)
    (full_paired_reverse σ s hf r anchor allowed label get hg μ ν κ η he z w
      (conditionedMeasure (Measure.pi P) A))
  rw [Measure.map_map hπ (measurable_id.prodMap (reverseSelected σ s hf).measurable)] at hh
  apply hh.trans
  apply conditioned_kernel_ignore P Q star hPQ A (measurableSet_retainedEvent _ _)
    (primaryChecks_ignore_star r anchor allowed label get hg star hstar Finset.univ)
    _ (proposalKernel_ignore_selected _ ν η s (Finset.univ\s) w star hs) π hπ
  intro x y p
  change ((fun i : {i // i∉s} ↦ (Function.update x star y) i),p) = ((fun i : {i // i∉s} ↦ x i),p)
  congr 1
  funext i
  exact Function.update_of_ne (show (i:I)≠star from fun h ↦ i.property (h.symm ▸ hs)) y x

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Comparison Wiener GaussianPacking
variable {I : Type*} [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

omit [Fintype I] in
lemma rebuildPrimary_measurable (s : Finset I) : Measurable (rebuildPrimary (X:=X) (Y:=Y) s) := by
  apply Measurable.of_eval
  intro i
  by_cases hi : i∈s
  · simpa only [rebuildPrimary,dite_eq_left hi,Function.comp_def] using
      measurable_fst.comp ((measurable_pi_apply (⟨i,hi⟩:s)).comp measurable_snd)
  · simpa only [rebuildPrimary,dite_eq_right hi,Function.comp_def] using
      (measurable_pi_apply (⟨i,hi⟩:{i // i∉s})).comp measurable_fst

omit [Fintype I] [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)] in
lemma rebuildPrimary_trim (s : Finset I) (x : ∀i,X i) (p : ∀i:s,X i×Y i) :
    rebuildPrimary s ((fun i ↦ x i),p)=Function.updateFinset x s (fun i ↦ (p i).1) := by
  funext i
  by_cases hi : i∈s <;> simp [rebuildPrimary,Function.updateFinset,hi]

variable {J : Type*} [Fintype J] [DecidableEq J]

lemma actual_two_primary_laws {L : Length}
    (σ : Equiv.Perm I) (s : Finset I) (hf : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (heq : ∀i,i≠star→μ i=ν i)
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) :
    let R := primaryChecks r anchor allowed label get hg
    let C := routeChecks σ s hf r anchor allowed label get hg
    let C' := routeChecks σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg
    let P := conditionedMeasure (Measure.pi μ) (retainedEvent R Finset.univ)
    let Q := conditionedMeasure (Measure.pi ν) (retainedEvent R Finset.univ)
    let T := P.compProd (proposalKernel C μ κ s (Finset.univ\s) z)
    T.map (fun p ↦ Function.updateFinset p.1 s (fun i ↦ (p.2 i).1))=
      P.withDensity (fun x ↦ conditionalLikelihood R C μ κ s (Finset.univ\s) x z) ∧
    T.map (fun p ↦ Function.updateFinset p.1 s (fun i ↦ (reverseSelected σ s hf p.2 i).1))=
      Q.withDensity (fun x ↦ conditionalLikelihood R C' ν η s (Finset.univ\s) x w) := by
  dsimp only
  refine ⟨full_primary_law _ _ μ κ s z (fun y u ↦ routeChecks_primary_weight σ s hf r anchor allowed label get hg Finset.univ (fun i ↦ (y i,u i))),?_⟩
  have h := congrArg (fun M ↦ M.map (rebuildPrimary (X:=X) (Y:=fun i ↦ X (σ i)) s))
    (actual_reverse_trimmed σ s hf r anchor allowed label get hg star hstar hs μ ν heq μ ν κ η he z w)
  rw [Measure.map_map (rebuildPrimary_measurable s) (show Measurable (fun p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) ↦ ((fun i:{i // i∉s} ↦ p.1 i), reverseSelected σ s hf p.2)) from
      (Measurable.of_eval (fun i ↦ (measurable_pi_apply i.val).comp measurable_fst)).prodMk ((reverseSelected σ s hf).measurable.comp measurable_snd)),
    Measure.map_map (rebuildPrimary_measurable s) (show Measurable (fun p : (∀i,X i)×(∀i:s,X i×X (σ i)) ↦ ((fun i:{i // i∉s} ↦ p.1 i), p.2)) from by fun_prop)] at h
  simp only [Function.comp_def,rebuildPrimary_trim] at h
  rw [h]
  exact full_primary_law _ _ ν η s w
    (fun y u ↦ routeChecks_primary_weight σ.symm s (reverse_fix σ s hf) r anchor allowed label get hg Finset.univ (fun i ↦ (y i,u i)))

end HardSphere.Bridge

end
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

lemma fiberNormalize_apply_measure {E X : Type*} [MeasurableSpace E] [MeasurableSpace X]
    (κ : Kernel E X) [IsSFiniteKernel κ] (A : Set (E×X)) (hA : MeasurableSet A) (e : E) :
    fiberNormalize κ A e=conditionedMeasure (κ e) (Prod.mk e ⁻¹' A) := by
  change (fiberRestrict _ _ e univ)⁻¹ • fiberRestrict _ _ e=_
  rw [fiberRestrict_apply _ hA]
  simp only [Measure.restrict_apply_univ,conditionedMeasure]
  rfl

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

omit [Fintype I] in
lemma ambientRefreshEvent_measurable (s : Finset I) (σ : Equiv.Perm I)
    (hf : ∀i,i∉s→σ i=i) (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) :
    MeasurableSet (ambientRefreshEvent s σ hf A) := by
  exact (hA.preimage (measurable_fst.fst.prodMk ((ambientFirst_measurable s σ).comp
    (measurable_fst.snd.prodMk measurable_snd)))).inter
    (hA.preimage (measurable_fst.fst.prodMk ((ambientSecond_measurable s σ hf).comp
      (measurable_fst.snd.prodMk measurable_snd))))

omit [Fintype I] in
lemma ambientRefreshKernel_apply (s : Finset I) (σ : Equiv.Perm I) (hf : ∀i,i∉s→σ i=i)
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (hA : MeasurableSet A) (e : E) (x : ∀i,X i) :
    ambientRefreshKernel s σ hf ρ A (e,x)=
      conditionedMeasure (Measure.pi fun i ↦ ρ i e)
        {p | (e,ambientFirst s σ (x,p))∈A ∧ (e,ambientSecond s σ hf (x,p))∈A} := by
  rw [ambientRefreshKernel,fiberNormalize_apply_measure _ _ (ambientRefreshEvent_measurable s σ hf A hA),
    Kernel.comap_apply,finiteKernelPi_apply]
  rfl

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SharedTransport
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
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

omit [Fintype I] [DecidableEq I] in
lemma routeConfigMap_measurable (f : ∀i,X i→Y i) (hf : ∀i,Measurable (f i)) :
    Measurable (routeConfigMap f) :=
  Measurable.of_eval fun i ↦ (hf i).comp (measurable_pi_apply i)

omit [Fintype I] in
lemma ambientSharedKernel_apply_measure (s : Finset I) (σ : Equiv.Perm I)
    (hσ : ∀i,i∉s→σ i=i) (ξ : Kernel E (∀i,X i)) [IsFiniteKernel ξ]
    (ρ : ∀i:s,Kernel E (X i×X (σ.symm i))) [∀i,IsFiniteKernel (ρ i)]
    (A : Set (E×(∀i,X i))) (e : E) :
    ambientSharedKernel s σ hσ ξ ρ A e=(ξ e).compProd
      ((ambientRefreshKernel s σ hσ ρ A).comap (Prod.mk e) measurable_prodMk_left) := by
  ext C hC
  rw [ambientSharedKernel,Kernel.compProd_apply hC,Measure.compProd_apply hC]
  rfl

end HardSphere.Comparison
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

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotAllowed_measurable {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : Option J) :
    MeasurableSet (physicalSlotAllowed hL g m r R C S u particle d i) := by
  cases i with
  | none => exact MeasurableSet.univ
  | some i => exact (datumPermitted_measurable hL g m r R C S u (particle i)).preimage measurable_prodMk_left

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotOn_map {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J) :
    (physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val=
      physicalSlotReference hL g m t r R C S u particle v i d := by
  cases i with
  | none =>
    change (subtypeConditional (cellPathReference v) (univ : Set C(Time,Point))).map
      Subtype.val=cellPathReference v
    rw [subtypeConditional_map _ MeasurableSet.univ,measure_univ,inv_one,
      one_smul,Measure.restrict_univ]
  | some i =>
    change (referenceOn t (datumStart hL d (particle i)) (datumEnd hL d (particle i))
      (Prod.mk d ⁻¹' datumPermitted hL g m r R C S u (particle i))).map Subtype.val=
      datumIndividualReference hL g m r R C S t u (particle i) d
    rw [referenceOn_map _ _ _ ((datumPermitted_measurable hL g m r R C S u (particle i)).preimage
      measurable_prodMk_left),datumIndividualReference_apply]

instance physicalSlotOn_finite {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J) :
    IsFiniteMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have hm := physicalSlotOn_map hL g m t r R C S u particle v d i
  have : IsFiniteMeasure ((physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val) := by
    rw [hm]; infer_instance
  exact Measure.isFiniteMeasure_of_map measurable_subtype_coe.aemeasurable

omit [Fintype J] [DecidableEq J] in
lemma physicalSlotOn_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) (i : Option J)
    [IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u particle v i d)] :
    IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have : IsProbabilityMeasure ((physicalSlotOn hL g m t r R C S u particle v d i).map Subtype.val) := by
    rw [physicalSlotOn_map]; infer_instance
  exact Measure.isProbabilityMeasure_of_map (Subtype.val : _ → _)

omit [Fintype J] [DecidableEq J] in
lemma physicalAllowed_confined {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : J)
    (f : physicalSlotAllowed hL g m r R C S u particle d (some i)) :
    Confined (projectPoint L (anchorPoint (datumHome hL d (particle i)))) (projectCurve L f.val) :=
  fun s ↦ (f.property.2.1 s).2

lemma physicalAllowed_checks {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (hr : r≤1) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) :
    (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ⁻¹'
      physicalSlotMutual (L:=L) r=
    retainedEvent (primaryChecks r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j))
      some (fun _ f ↦ f) (fun _ ↦ measurable_id)) Finset.univ := by
  ext x
  constructor
  · intro hx e he
    exact hx e.2.val.1 e.2.val.2 e.2.property.1
  · intro hx
    let allowed := physicalSlotAllowed hL g m r R C S u particle d
    let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
    have hconf : ∀j,∀f : allowed (some j),Confined (anchor j) (projectCurve L f.val) :=
      physicalAllowed_confined hL g m r R C S u particle d
    have hh := physicalSparseChecks_complete (I:=Option J) (V:=fun i ↦ allowed i)
      r hr anchor (fun j ↦ allowed (some j)) hconf
      (fun _ ↦ some) (fun _ _ f ↦ f) (fun _ _ ↦ measurable_id) x hx
    exact hh false

lemma physicalPrimary_on_map {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (hr : r≤1) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    (conditionedMeasure (Measure.pi (physicalSlotOn hL g m t r R C S u particle v d))
      (retainedEvent (primaryChecks r (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
        (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j))
        some (fun _ f ↦ f) (fun _ ↦ measurable_id)) Finset.univ)).map
      (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_)))=
      physicalPrimaryReference hL g m t r R C S u particle v d := by
  rw [←physicalAllowed_checks hL g m r R C S hr u particle d,
    physicalPrimaryReference_apply]
  exact (conditioned_pi_map (physicalSlotOn hL g m t r R C S u particle v d)
    (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))
    (fun _ ↦ measurable_subtype_coe) (physicalSlotMutual_measurable r)).trans
    (by simp only [physicalSlotOn_map])

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupported
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
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

instance physicalSlotAllowed_borel {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (i : Option J) :
    StandardBorelSpace (physicalSlotAllowed hL g m r R C S u particle d i) :=
  (physicalSlotAllowed_measurable hL g m r R C S u particle d i).standardBorel

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SharedIdentities
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
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
open HardSphere.Bridge HardSphere.Wiener HardSphere.GaussianPacking
attribute [local instance] Classical.propDecidable
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [DecidableEq I]
  {X Y : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Y i)]

variable {J : Type*} [Fintype J] [DecidableEq J] {L : HardSphere.Length}

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma ambientFirst_updated (s : Finset I) (σ : Equiv.Perm I)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    (fun i ↦ (Function.updateFinset (fun i ↦ (x i,z i)) s p i).1)=
      ambientFirst s σ (x,p) := by
  funext i
  by_cases hi : i∈s
  · simp only [ambientFirst,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientFirst,Function.updateFinset,dite_eq_right hi]

omit [Fintype I] in
lemma ambientSecond_updated (s : Finset I) (σ : Equiv.Perm I) (hσ : ∀i,i∉s→σ i=i)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (p : ∀i:s,X i×X (σ.symm i)) :
    (fun i ↦ (partialReversePairs σ s hσ (Function.updateFinset (fun i ↦ (x i,z i)) s p) i).1)=
      ambientSecond s σ hσ (x,p) := by
  rw [partialReverse_update]
  funext i
  by_cases hi : i∈s
  · simp only [ambientSecond,Function.updateFinset,dite_eq_left hi]
  · simp only [ambientSecond,Function.updateFinset,dite_eq_right hi,
      partialReversePairs_outside_fst σ s hσ _ i hi]

omit [Fintype J] [DecidableEq J] in
lemma routeChecks_both (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (p : ∀i,X i×X (σ.symm i)) :
    p∈retainedEvent (routeChecks σ s hσ r anchor allowed label get hg) Finset.univ ↔
      (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      (fun i ↦ (partialReversePairs σ s hσ p i).1)∈
        retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ := by
  constructor
  · intro hp
    refine ⟨routeChecks_primary σ s hσ r anchor allowed label get hg _ p hp,?_⟩
    intro e _
    rcases e with ⟨b,e⟩
    change ¬TrialCollision r
      (projectCurve L (get e.val.2 (partialReversePairs σ s hσ p (label e.val.2)).1).val)
      (get e.val.1 (partialReversePairs σ s hσ p (label e.val.1)).1).val
    rw [partialReverse_primary_path σ s hσ allowed label get p e.val.2,
      partialReverse_primary_path σ s hσ allowed label get p e.val.1]
    exact hp (true,e) (Finset.subset_univ _)
  · rintro ⟨hp,hq⟩ ⟨b,e⟩ _
    cases b
    · exact hp (false,e) (Finset.subset_univ _)
    · have h := hq (false,e) (Finset.subset_univ _)
      change ¬TrialCollision r
        (projectCurve L (get e.val.2 (partialReversePairs σ s hσ p (label e.val.2)).1).val)
        (get e.val.1 (partialReversePairs σ s hσ p (label e.val.1)).1).val at h
      rw [partialReverse_primary_path σ s hσ allowed label get p e.val.2,
      partialReverse_primary_path σ s hσ allowed label get p e.val.1] at h
      exact h

omit [Fintype J] [DecidableEq J] in
lemma ambient_proposalEvent (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (z : ∀i,X (σ.symm i)) :
    {p : (∀i,X i)×(∀i:s,X i×X (σ.symm i)) |
      ambientFirst s σ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ ∧
      ambientSecond s σ hσ p∈retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ} =
    proposalEvent (routeChecks σ s hσ r anchor allowed label get hg) s (Finset.univ\s) z := by
  ext p
  simp only [proposalEvent,mem_ofPred_eq,Finset.union_sdiff_of_subset (Finset.subset_univ s)]
  rw [routeChecks_both,ambientFirst_updated,ambientSecond_updated]

lemma ambientRefresh_constant (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (z : ∀i,X (σ.symm i)) (e : E) (x : ∀i,X i) :
    ambientRefreshKernel s σ hσ (fun i ↦ Kernel.const E ((μ i).compProd (κ i)))
      (Prod.snd ⁻¹' retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ) (e,x)=
    proposalKernel (routeChecks σ s hσ r anchor allowed label get hg) μ κ s (Finset.univ\s) z x := by
  rw [ambientRefreshKernel_apply _ _ _ _ _
      ((measurableSet_retainedEvent _ _).preimage measurable_snd),proposalKernel_apply]
  simp only [Kernel.const_apply]
  have he := congrArg (fun A ↦ Prod.mk x ⁻¹' A)
    (ambient_proposalEvent σ s hσ r anchor allowed label get hg z)
  change conditionedMeasure _ _=conditionedMeasure _ _
  congr 1

lemma ambient_two_primary_laws (σ : Equiv.Perm I) (s : Finset I) (hσ : ∀i,i∉s→σ i=i)
    (r : ℝ) (anchor : J→HardSphere.Torus L) (allowed : J→Set C(Time,Point))
    (label : J→I) (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (star : I) (hstar : ∀j,label j≠star) (hs : star∈s)
    (μ ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)] [∀i,IsProbabilityMeasure (ν i)]
    (heq : ∀i,i≠star→μ i=ν i)
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (σ i))) [∀i,IsFiniteKernel (η i)]
    (he : ∀j:s,((μ (σ j)).compProd (κ (σ j))).map (reverseFactor (X:=X) σ j)=
        (ν j).compProd (η j))
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (σ i)) (e : E) :
    let R := primaryChecks r anchor allowed label get hg
    let C := routeChecks σ s hσ r anchor allowed label get hg
    let C' := routeChecks σ.symm s (reverse_fix σ s hσ) r anchor allowed label get hg
    let P := conditionedMeasure (Measure.pi μ) (retainedEvent R Finset.univ)
    let Q := conditionedMeasure (Measure.pi ν) (retainedEvent R Finset.univ)
    let T := ambientSharedKernel s σ hσ (Kernel.const E P)
      (fun i ↦ Kernel.const E ((μ i).compProd (κ i))) (Prod.snd ⁻¹' retainedEvent R Finset.univ) e
    T.map (ambientFirst s σ)=
      P.withDensity (fun x ↦ conditionalLikelihood R C μ κ s (Finset.univ\s) x z) ∧
    T.map (ambientSecond s σ hσ)=
      Q.withDensity (fun x ↦ conditionalLikelihood R C' ν η s (Finset.univ\s) x w) := by
  dsimp only
  rw [ambientSharedKernel_apply_measure,Kernel.const_apply]
  have hk : (ambientRefreshKernel s σ hσ
      (fun i : s ↦ Kernel.const E ((μ i).compProd (κ i)))
      (Prod.snd ⁻¹' retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ)).comap
        (Prod.mk e) measurable_prodMk_left=
      proposalKernel (routeChecks σ s hσ r anchor allowed label get hg) μ κ s (Finset.univ\s) z := by
    ext x A hA
    exact congrArg (fun m ↦ m A) (ambientRefresh_constant σ s hσ r anchor allowed label get hg μ κ z e x)
  rw [hk]
  exact actual_two_primary_laws σ s hσ r anchor allowed label get hg star hstar hs μ ν heq κ η he z w

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalPairedRoute
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLikelihood
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma physicalOn_probability {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (i : Option J) : IsProbabilityMeasure (physicalSlotOn hL g m t r R C S u particle v d i) := by
  have : IsProbabilityMeasure (physicalSlotReference hL g m t r R C S u particle v i d) := by
    cases i with
    | none => exact inferInstanceAs (IsProbabilityMeasure (cellPathReference v))
    | some i => exact hp i
  exact physicalSlotOn_probability hL g m t r R C S u particle v d i

theorem physical_two_likelihoods {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (κ : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i)))
    [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (physicalSlotAllowed hL g m r R C S u particle d i)
      (physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)))
    [∀i,IsFiniteKernel (η i)]
    (he : ∀i:routeSlots labels,
      (physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d i).compProd (κ i)=
        physicalSelectedOn hL g m t r R C S u particle labels v steps d i)
    (hr : ∀i:routeSlots labels,
      ((physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d (routePermutation labels i)).compProd
        (κ (routePermutation labels i))).map (reverseFactor (X:=fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i)
          (routePermutation labels) i)=
      (physicalSlotOn hL g m t r R C S u particle (v 0) d i).compProd (η i))
    (z : ∀i,physicalSlotAllowed hL g m r R C S u particle d ((routePermutation labels).symm i))
    (w : ∀i,physicalSlotAllowed hL g m r R C S u particle d (routePermutation labels i)) :
    let σ := routePermutation labels
    let s := routeSlots labels
    let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
    let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let R₀ := physicalOnChecks hL g m r R C S u particle d
    let C₀ := routeChecks σ s (routePermutation_fixed labels) r anchor allowed some (fun _ f ↦ f) (fun _ ↦ measurable_id)
    let C₁ := routeChecks σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) r anchor allowed some (fun _ f ↦ f) (fun _ ↦ measurable_id)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    let T := physicalSharedOn hL g m t r R C S u particle labels v steps d
    T.map (ambientFirst s σ)=
      (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d).withDensity
        (fun x ↦ conditionalLikelihood R₀ C₀ μ κ s (Finset.univ\s) x z) ∧
    T.map (ambientSecond s σ (routePermutation_fixed labels))=
      (physicalOnPrimary hL g m t r R C S u particle (v 0) d).withDensity
        (fun x ↦ conditionalLikelihood R₀ C₁ ν η s (Finset.univ\s) x w) := by
  dsimp only
  let X : Option J → Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let σ := routePermutation labels
  let s := routeSlots labels
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have : ∀i,IsProbabilityMeasure (ν i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have heq : ∀i,i≠none→μ i=ν i := by
    intro i hi
    cases i with
    | none => exact (hi rfl).elim
    | some i => rfl
  have hs : none∈s := by
    exact Finset.mem_map.mpr ⟨Fin.last (n+1),Finset.mem_univ _,routeEmbedding_last labels⟩
  have h := ambient_two_primary_laws (X:=X) σ s (routePermutation_fixed labels) r
    (fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j))))
    (fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)) some (fun _ f ↦ f) (fun _ ↦ measurable_id)
    none (fun _ ↦ Option.some_ne_none _) hs μ ν heq κ η hr z w ()
  have hρ : (fun i:s ↦ Kernel.const Unit ((μ i).compProd (κ i)))=
      (fun i:s ↦ Kernel.const Unit (physicalSelectedOn hL g m t r R C S u particle labels v steps d i)) := by
    funext i
    rw [he i]
  dsimp only at h
  simp only [hρ] at h
  exact h

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteAuxiliary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)

attribute [instance] PhysicalRouteAux.forward_finite PhysicalRouteAux.backward_finite

variable {hL g m t r R C S u particle labels v steps d}

lemma PhysicalRouteAux.laws (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    (physicalSharedOn hL g m t r R C S u particle labels v steps d).map
      (ambientFirst (routeSlots labels) (routePermutation labels))=
      (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d).withDensity A.firstDensity ∧
    (physicalSharedOn hL g m t r R C S u particle labels v steps d).map
      (ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels))=
      (physicalOnPrimary hL g m t r R C S u particle (v 0) d).withDensity A.secondDensity := by
  exact physical_two_likelihoods hL g m t r R C S u particle labels v steps d hp
    A.forward A.backward A.selected (fun i ↦ A.reverse i) A.firstSeed A.secondSeed

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_RouteRN
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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

lemma piSubtype_measurableEmbedding {I : Type*} [Countable I]
    {X : I→Type*} [∀i,MeasurableSpace (X i)] (A : ∀i,Set (X i))
    (hA : ∀i,MeasurableSet (A i)) :
    MeasurableEmbedding (fun z : ∀i,A i ↦ fun i ↦ (z i).val) := by
  let f : (∀i,A i)→∀i,X i := fun z i ↦ (z i).val
  have hr : range f={z | ∀i,z i∈A i} := by
    ext z
    constructor
    · rintro ⟨w,rfl⟩ i
      exact (w i).property
    · intro hz
      exact ⟨fun i ↦ ⟨z i,hz i⟩,rfl⟩
  let g : range f→∀i,A i := fun z i ↦ ⟨z.val i,by
    exact ((Set.ext_iff.mp hr z.val).mp z.property) i⟩
  apply MeasurableEmbedding.of_measurable_inverse_on_range
    (g:=g) (Measurable.of_eval fun i ↦ measurable_subtype_coe.comp (measurable_pi_apply i))
  · rw [hr]
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i ↦ (hA i).preimage (measurable_pi_apply i)
  · exact Measurable.of_eval fun i ↦ ((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk
  · intro z
    rfl

lemma mapped_likelihood_cross {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P μ ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f g : X→ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    (hμ : μ=P.withDensity f) (hν : ν=P.withDensity g)
    (e : X→Y) (he : MeasurableEmbedding e) :
    (∫⁻y,(μ.map e).rnDeriv (P.map e) y*(ν.map e).rnDeriv (P.map e) y ∂P.map e)=
      ∫⁻x,f x*g x ∂P := by
  rw [he.lintegral_map]
  apply lintegral_congr_ae
  have hf' : (fun x ↦ (μ.map e).rnDeriv (P.map e) (e x))=ᵐ[P] f := by
    refine (he.rnDeriv_map μ P).trans ?_
    rw [hμ]
    exact Measure.rnDeriv_withDensity P hf
  have hg' : (fun x ↦ (ν.map e).rnDeriv (P.map e) (e x))=ᵐ[P] g := by
    refine (he.rnDeriv_map ν P).trans ?_
    rw [hν]
    exact Measure.rnDeriv_withDensity P hg
  exact hf'.mul hg'

end HardSphere.Comparison
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]
omit [DecidableEq J] in
lemma physicalConfig_embedding {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) :
    MeasurableEmbedding (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) :=
  piSubtype_measurableEmbedding _ (physicalSlotAllowed_measurable hL g m r R C S u particle d)

variable {N K M G n : ℕ} {L : Length} {hL : L.val=(K:ℝ)} {g : Fin G}
  {m : ℕ} {t r R C S : ℝ} {u : Time} {particle : J↪Fin N}
  {labels : Fin (n+1)↪J} {v : Fin (n+2)→Fin 3→Fin K} {steps : Fin (n+1)→Fin 7}
  {d : PhysicalDatum N K M G L}
lemma PhysicalRouteAux.firstDensity_measurable
    (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    Measurable A.firstDensity := by
  have := physicalOn_probability hL g m t r R C S u particle (v (Fin.last (n+1))) d hp
  exact measurable_conditionalLikelihood _ _ _ _ _ _ _
lemma PhysicalRouteAux.secondDensity_measurable
    (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    Measurable A.secondDensity := by
  have := physicalOn_probability hL g m t r R C S u particle (v 0) d hp
  have : ∀i,IsFiniteKernel (A.backward i) := A.backward_finite
  exact measurable_conditionalLikelihood _ _ _ _ _ _ _

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAmbientRN
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
  (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
  (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K)
  (steps : Fin (n+1)→Fin 7)
  (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
  (d : PhysicalDatum N K M G L)
  (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
  (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)

include ht hr hc hhome haccess

lemma physicalPairedRoute_densities
    (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.fst=
      ((physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d).withDensity A.firstDensity).map
        (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ∧
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.snd=
      ((physicalOnPrimary hL g m t r R C S u particle (v 0) d).withDensity A.secondDensity).map
        (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) := by
  have H := physicalPairedRoute_marginals hL g m t r R C S ht hr u particle labels v steps hc d hhome haccess
  rw [(A.laws hp).1] at H
  rw [(A.laws hp).2] at H
  exact H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
variable {J : Type*} [Fintype J] [DecidableEq J]

variable {N K M G n l : ℕ} {L : Length} (hL : L.val=(K:ℝ))
  (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
  (particle : J↪Fin N)
  (f : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K) (steps : Fin (n+1)→Fin 7)
  (f' : Fin (l+1)↪J) (v' : Fin (l+2)→Fin 3→Fin K) (steps' : Fin (l+1)→Fin 7)
  (d : PhysicalDatum N K M G L)
  (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
  (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
  (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
  (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
  (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
  (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
  (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
  (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
  (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
include ht hr hc hc' hh hh' ha ha' hp

lemma physical_first_RN_cross (he : v' (Fin.last (l+1))=v (Fin.last (n+1))) :
    let P := physicalPrimaryReference hL g m t r R C S u particle (v (Fin.last (n+1))) d
    (∫⁻z,((physicalPairedRoute hL g m t r R C S u particle f v steps d).map Prod.fst).rnDeriv P z *
      ((physicalPairedRoute hL g m t r R C S u particle f' v' steps' d).map Prod.fst).rnDeriv P z ∂P)=
    ∫⁻z,A.firstDensity z*B.firstDensity z
      ∂physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d := by
  dsimp only
  rw [(physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f v steps hc d hh ha).1,
    (physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f' v' steps' hc' d hh' ha').1,
    ←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
  apply mapped_likelihood_cross
    (physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d) _ _
    A.firstDensity B.firstDensity (A.firstDensity_measurable hp) (B.firstDensity_measurable hp)
    (A.laws hp).1 _ _ (physicalConfig_embedding hL g m r R C S u particle d)
  simpa only [he] using (B.laws hp).1

lemma physical_second_RN_cross (he : v' 0=v 0) :
    let P := physicalPrimaryReference hL g m t r R C S u particle (v 0) d
    (∫⁻z,((physicalPairedRoute hL g m t r R C S u particle f v steps d).map Prod.snd).rnDeriv P z *
      ((physicalPairedRoute hL g m t r R C S u particle f' v' steps' d).map Prod.snd).rnDeriv P z ∂P)=
    ∫⁻z,A.secondDensity z*B.secondDensity z
      ∂physicalOnPrimary hL g m t r R C S u particle (v 0) d := by
  dsimp only
  rw [(physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f v steps hc d hh ha).2,
    (physicalPairedRoute_marginals hL g m t r R C S ht hr u particle f' v' steps' hc' d hh' ha').2,
    ←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
  apply mapped_likelihood_cross
    (physicalOnPrimary hL g m t r R C S u particle (v 0) d) _ _
    A.secondDensity B.secondDensity (A.secondDensity_measurable hp) (B.secondDensity_measurable hp)
    (A.laws hp).2 _ _ (physicalConfig_embedding hL g m r R C S u particle d)
  simpa only [he] using (B.laws hp).2

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLabelLaw
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar
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

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma uniformLabels_supported (s : Finset J) : ∀ᵐ i ∂uniformLabels s,i∈paddedLabels s := by
  rw [ae_iff]
  change uniformLabels s ((↑(paddedLabels s) : Set (Option J))ᶜ)=0
  unfold uniformLabels
  rw [PMF.toMeasure_uniformOfFinset_apply _ _ (Set.to_countable _).measurableSet]
  simp

instance physicalLabels_markov {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N) :
    IsMarkovKernel (physicalLabels (M:=M) hL g m t r R C S u particle) := by
  constructor
  intro d
  rw [physicalLabels,finiteKernelPi_apply]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalLabels_supported {N K M G : ℕ} [NeZero K] {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) :
    ∀ᵐ z ∂physicalLabels hL g m t r R C S u particle d,
      ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d) := by
  rw [physicalLabels,finiteKernelPi_apply]
  apply ae_all_iff.mpr
  intro v
  exact (measurePreserving_eval (fun v ↦ physicalLabelAt hL g m t r R C S u particle v d) v).quasiMeasurePreserving.ae
    (uniformLabels_supported _)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PathSlots
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}

lemma routeEmbedding_anchor (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc)
    (i : Fin (p.val.length+1)) :
    extendedAnchor anchor y (routeEmbedding (departureEmbedding p anchor pick hpick) i)=
      pathVertexEmbedding p i := by
  by_cases hi : i.val<p.val.length
  · have he : i=(⟨i.val,hi⟩ : Fin p.val.length).castSucc := Fin.ext rfl
    rw [he,routeEmbedding_castSucc]
    exact hpick ⟨i.val,hi⟩
  · have he : i=Fin.last p.val.length := Fin.ext (by simp only [Fin.val_last];omega)
    rw [he,routeEmbedding_last,pathVertex_last]
    rfl

lemma routeSlots_anchor_injective (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    Set.InjOn (extendedAnchor anchor y) (routeSlots (departureEmbedding p anchor pick hpick):Set (Option J)) := by
  intro a ha b hb hab
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hb
  rw [routeEmbedding_anchor,routeEmbedding_anchor] at hab
  exact congrArg _ ((pathVertexEmbedding p).injective hab)

lemma routeSlots_sites (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    (routeSlots (departureEmbedding p anchor pick hpick)).image (extendedAnchor anchor y)=p.val.support.toFinset := by
  ext v
  constructor
  · intro hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ha
    rw [routeEmbedding_anchor]
    exact List.mem_toFinset.mpr (p.val.getVert_mem_support i.val)
  · intro hv
    obtain ⟨n,hn,hle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp hv)
    refine Finset.mem_image.mpr ⟨routeEmbedding (departureEmbedding p anchor pick hpick) ⟨n,by omega⟩,
      Finset.mem_map.mpr ⟨⟨n,by omega⟩,Finset.mem_univ _,rfl⟩,?_⟩
    rw [routeEmbedding_anchor]
    exact hn

lemma simple_nearSlots_bound (R : ℕ) (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f : Fin p.val.length→J) (g : Fin q.val.length→J)
    (hf : ∀i,anchor (f i)=pathVertexEmbedding p i.castSucc)
    (hg : ∀i,anchor (g i)=pathVertexEmbedding q i.castSucc) :
    (nearSlots (torusNear K R) (extendedAnchor anchor y)
      (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))).card≤
      simpleEncounter R p q := by
  have h := nearSlots_card (torusNear K R) (extendedAnchor anchor y)
    (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))
    (routeSlots_anchor_injective p anchor f hf)
  rw [routeSlots_sites,routeSlots_sites] at h
  exact h

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_SlotMultiplicity
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {I V : Type*} [DecidableEq V]
lemma nearSlots_card_of_fiber (e : V→V→Prop) (c : I→V) (s t : Finset I)
    (B : ℕ) (hB : ∀v,(s.filter (fun i ↦ c i=v)).card≤B) :
    (nearSlots e c s t).card≤B*(encounterSet e (s.image c) (t.image c)).card := by
  have hm : (nearSlots e c s t).image c⊆
      (encounterSet e (s.image c) (t.image c)).image Prod.fst := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨his,j,hjt,hij⟩ := (mem_nearSlots e c s t i).mp hi
    exact Finset.mem_image.mpr ⟨(c i,c j),(mem_encounterSet e _ _ _ _).mpr
      ⟨Finset.mem_image.mpr ⟨i,his,rfl⟩,Finset.mem_image.mpr ⟨j,hjt,rfl⟩,hij⟩,rfl⟩
  have hc : ((nearSlots e c s t).image c).card≤(encounterSet e (s.image c) (t.image c)).card :=
    (Finset.card_le_card hm).trans Finset.card_image_le
  calc
    _=∑v∈(nearSlots e c s t).image c,((nearSlots e c s t).filter (fun i ↦ c i=v)).card :=
      Finset.card_eq_sum_card_image c _
    _≤∑_v∈(nearSlots e c s t).image c,B := by
      apply Finset.sum_le_sum
      intro v _
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans (hB v)
    _=((nearSlots e c s t).image c).card*B := by simp
    _≤B*(encounterSet e (s.image c) (t.image c)).card := by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right B hc

variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}
lemma departure_anchor_injective (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    Set.InjOn anchor (Set.range pick) := by
  rintro a ⟨i,rfl⟩ b ⟨j,rfl⟩ hab
  rw [hpick i,hpick j] at hab
  have h := (pathVertexEmbedding p).injective hab
  have he : i=j := Fin.ext (congrArg (fun k : Fin (p.val.length+1) ↦ k.val) h)
  exact congrArg pick he

lemma routeSlots_start_fiber (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) (v : DiscreteTorus K) :
    ((routeSlots (departureEmbedding p anchor pick hpick)).filter
      (fun i ↦ extendedAnchor anchor x i=v)).card≤2 := by
  let s := (routeSlots (departureEmbedding p anchor pick hpick)).filter
      (fun i ↦ extendedAnchor anchor x i=v)
  have hone : (s.erase none).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hna := Finset.mem_erase.mp ha
    have hnb := Finset.mem_erase.mp hb
    obtain ⟨a,rfl⟩ := Option.ne_none_iff_exists'.mp hna.1
    obtain ⟨b,rfl⟩ := Option.ne_none_iff_exists'.mp hnb.1
    have has := Finset.mem_filter.mp hna.2
    have hbs := Finset.mem_filter.mp hnb.2
    rw [routeSlots_exact] at has hbs
    have hai : a∈Set.range pick := by
      rcases Finset.mem_insert.mp has.1 with h|h
      · contradiction
      · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
        exact ⟨i,Option.some.inj he⟩
    have hbi : b∈Set.range pick := by
      rcases Finset.mem_insert.mp hbs.1 with h|h
      · contradiction
      · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
        exact ⟨i,Option.some.inj he⟩
    exact congrArg some (departure_anchor_injective p anchor pick hpick hai hbi (has.2.trans hbs.2.symm))
  have hcard : s.card≤(s.erase none).card+1 := by
    have hin : s⊆insert none (s.erase none) := by intro a ha;by_cases h:a=none <;> simp_all
    exact (Finset.card_le_card hin).trans (Finset.card_insert_le _ _)
  exact hcard.trans (by omega)

end HardSphere.Comparison

end
end

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open HardSphere.Lattice
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*}
lemma routeSlots_start_sites (p : SimplePath x y) (anchor : J→DiscreteTorus K)
    (pick : Fin p.val.length→J)
    (hpick : ∀i,anchor (pick i)=pathVertexEmbedding p i.castSucc) :
    (routeSlots (departureEmbedding p anchor pick hpick)).image (extendedAnchor anchor x)⊆p.val.support.toFinset := by
  intro v hv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  rw [routeSlots_exact] at ha
  rcases Finset.mem_insert.mp ha with rfl|ha
  · exact List.mem_toFinset.mpr p.val.start_mem_support
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    change anchor (pick i)∈_
    rw [hpick i]
    exact List.mem_toFinset.mpr (p.val.getVert_mem_support i.val)

lemma second_primary_nearSlots_bound (R : ℕ) (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f : Fin p.val.length→J) (g : Fin q.val.length→J)
    (hf : ∀i,anchor (f i)=pathVertexEmbedding p i.castSucc)
    (hg : ∀i,anchor (g i)=pathVertexEmbedding q i.castSucc) :
    (nearSlots (torusNear K R) (extendedAnchor anchor x)
      (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))).card≤
      2*simpleEncounter R p q := by
  have h := nearSlots_card_of_fiber (torusNear K R) (extendedAnchor anchor x)
    (routeSlots (departureEmbedding p anchor f hf)) (routeSlots (departureEmbedding q anchor g hg))
    2 (routeSlots_start_fiber p anchor f hf)
  apply h.trans
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro v hv
  obtain ⟨ha,hb,he⟩ := (mem_encounterSet _ _ _ _ _).mp hv
  exact (mem_encounterSet _ _ _ _ _).mpr
    ⟨routeSlots_start_sites p anchor f hf ha,routeSlots_start_sites q anchor g hg hb,he⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Paths_SimpleRouteGeometry
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotAllowed_borel _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K} {J : Type*}

lemma simpleRouteVertices_zero (p : SimplePath x y) (n : ℕ) :
    simpleRouteVertices p n 0=siteIndex x := by simp [simpleRouteVertices]
lemma simpleRouteVertices_last (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) :
    simpleRouteVertices p n (Fin.last (n+1))=siteIndex y := by
  simp only [simpleRouteVertices,Fin.val_last,hn,SimpleGraph.Walk.getVert_length]

lemma simpleRouteVertices_distance {L : Length} (hL : L.val=(K:ℝ))
    (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) :
    ∀i:Fin (n+1),torusDistance L (gridCenter L (simpleRouteVertices p n i.castSucc))
      (gridCenter L (simpleRouteVertices p n i.succ))≤1 :=
  fun i ↦ adjacent_center_distance hL (simpleRouteVertices_adjacent p n hn i)

lemma simpleRouteSteps_period {L : Length} (hL : L.val=(K:ℝ))
    (p : SimplePath x y) (n : ℕ) (hn : n+1=p.val.length) :
    ∀ i : Fin (n+1), projectPoint L (routeCellPeriod (simpleRouteVertices p n i.succ)
      (simpleRouteVertices p n i.castSucc) (simpleRouteSteps hL p n hn i))=0 :=
  fun i ↦ (adjacent_routeCellPeriod hL (simpleRouteVertices_adjacent p n hn i)).choose_spec

lemma gridSite_slotCenter {home : J→Fin 3→Fin K} (w : DiscreteTorus K) :
    (fun i ↦ gridSite (slotCenter home (siteIndex w) i))=
      extendedAnchor (fun j ↦ gridSite (home j)) w := by
  funext i
  cases i with
  | none => exact indexSite_siteIndex w
  | some j => rfl

lemma routeSlots_reparam {d e : ℕ} (f : Fin d↪J) (h : e=d) :
    routeSlots ((finCongr h).toEmbedding.trans f)=routeSlots f := by
  subst e
  rfl

lemma simpleRouteSlots {n : ℕ} (p : SimplePath x y) (hn : n+1=p.val.length)
    (home : J→Fin 3→Fin K) (f : Fin (n+1)↪J)
    (hf : ∀i,home (f i)=simpleRouteVertices p n i.castSucc) :
    ∃ pick : Fin p.val.length→J, ∃ H : ∀i,gridSite (home (pick i))=pathVertexEmbedding p i.castSucc,
      routeSlots f=routeSlots (departureEmbedding p (fun j ↦ gridSite (home j)) pick H) := by
  let pick : Fin p.val.length→J := fun i ↦ f (Fin.cast hn.symm i)
  have hp : ∀i,gridSite (home (pick i))=pathVertexEmbedding p i.castSucc := by
    intro i
    dsimp only [pick]
    rw [hf]
    exact indexSite_siteIndex _
  refine ⟨pick,hp,?_⟩
  have he : departureEmbedding p (fun j ↦ gridSite (home j)) pick hp=
      (finCongr hn.symm).toEmbedding.trans f := by ext i; rfl
  rw [he,routeSlots_reparam]

lemma simpleRoute_near_first {n l : ℕ} (p q : SimplePath x y)
    (hn : n+1=p.val.length) (hl : l+1=q.val.length)
    (home : J→Fin 3→Fin K) (f : Fin (n+1)↪J) (g : Fin (l+1)↪J)
    (hf : ∀i,home (f i)=simpleRouteVertices p n i.castSucc)
    (hg : ∀i,home (g i)=simpleRouteVertices q l i.castSucc) (R : ℕ) :
    (nearSlots (torusNear K R) (fun i ↦ gridSite (slotCenter home (siteIndex y) i))
      (routeSlots f) (routeSlots g)).card≤ simpleEncounter R p q := by
  obtain ⟨pick,hpick,hp⟩ := simpleRouteSlots p hn home f hf
  obtain ⟨choose,hchoose,hq⟩ := simpleRouteSlots q hl home g hg
  rw [gridSite_slotCenter,hp,hq]
  exact simple_nearSlots_bound R p q _ pick choose hpick hchoose

lemma simpleRoute_near_second {n l : ℕ} (p q : SimplePath x y)
    (hn : n+1=p.val.length) (hl : l+1=q.val.length)
    (home : J→Fin 3→Fin K) (f : Fin (n+1)↪J) (g : Fin (l+1)↪J)
    (hf : ∀i,home (f i)=simpleRouteVertices p n i.castSucc)
    (hg : ∀i,home (g i)=simpleRouteVertices q l i.castSucc) (R : ℕ) :
    (nearSlots (torusNear K R) (fun i ↦ gridSite (slotCenter home (siteIndex x) i))
      (routeSlots f) (routeSlots g)).card≤2*simpleEncounter R p q := by
  obtain ⟨pick,hpick,hp⟩ := simpleRouteSlots p hn home f hf
  obtain ⟨choose,hchoose,hq⟩ := simpleRouteSlots q hl home g hg
  rw [gridSite_slotCenter,hp,hq]
  exact second_primary_nearSlots_bound R p q _ pick choose hpick hchoose

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

omit [NeZero K] [Fintype J] [DecidableEq J] in
lemma fieldLabels_spec (p : SimplePath x y) (z : DiscreteTorus K→Option J) (h : RouteFieldValid p z) :
    ∀i,z (pathVertexEmbedding p i.castSucc)=some (fieldLabels p z h i) := h.choose_spec

omit [DecidableEq J] in
lemma branchAccessible_home {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) (d : PhysicalDatum N K M G L) (j : J)
    (hj : j∈branchAccessible hL g m t r R C S u particle v d) :
    datumHome hL d (particle j)=siteIndex v ∧ datumAccessible hL g m t r R C S u (particle j) d := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).2).2

lemma routeFieldValid_of_supported {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) :
    RouteFieldValid p z := by
  have he : ∀i : Fin p.val.length,∃j : J,
      j∈branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d ∧
      z (pathVertexEmbedding p i.castSucc)=some j := by
    intro i
    have hh := hz (pathVertexEmbedding p i.castSucc)
    rw [paddedLabels,ite_eq_left (ha i)] at hh
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hh
    exact ⟨j,hj,he.symm⟩
  choose f hf hfe using he
  have hhome : ∀i,gridSite (datumHome hL d (particle (f i)))=pathVertexEmbedding p i.castSucc := by
    intro i
    rw [(branchAccessible_home hL g m t r R C S u particle _ d _ (hf i)).1]
    exact indexSite_siteIndex _
  exact ⟨departureEmbedding p (fun j ↦ gridSite (datumHome hL d (particle j))) f hhome,hfe⟩

lemma fieldLabels_physical {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (h : RouteFieldValid p z) :
    ∀i,datumHome hL d (particle (fieldLabels p z h i))=siteIndex (pathVertexEmbedding p i.castSucc) ∧
      datumAccessible hL g m t r R C S u (particle (fieldLabels p z h i)) d := by
  intro i
  apply branchAccessible_home hL g m t r R C S u particle _ d _
  have hh := hz (pathVertexEmbedding p i.castSucc)
  rw [paddedLabels,ite_eq_left (ha i),fieldLabels_spec p z h] at hh
  simpa using hh

lemma fieldRouteLabels_physical {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) (hxy : x≠y) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (h : RouteFieldValid p z) :
    ∀i,datumHome hL d (particle (fieldRouteLabels hxy p z h i))=
      simpleRouteVertices p (p.val.length-1) i.castSucc ∧
      datumAccessible hL g m t r R C S u (particle (fieldRouteLabels hxy p z h i)) d := by
  intro i
  exact fieldLabels_physical hL g m t r R C S u particle d p z hz ha h (Fin.cast (simpleRouteLength_eq hxy p) i)

end HardSphere.Groups
end
end

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
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_LabelMoment
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
open scoped BigOperators ENNReal
namespace HardSphere.Comparison
variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]
lemma uniform_match_integral (G : ℝ) (x : A) :
    (∫y, (if x=y then G else 1) ∂(PMF.uniformOfFintype A).toMeasure)=
      1+(G-1)/(Fintype.card A:ℝ) := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [←Finset.mul_sum]
  have h : (∑y:A,if x=y then G else (1:ℝ))=G+((Fintype.card A:ℝ)-1) := by
    have he (y : A) : (if x=y then G else (1:ℝ))=1+(if x=y then G-1 else 0) := by
      by_cases hxy : x=y <;> simp [hxy]
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_ite_eq]
    simp
    ring
  rw [h]
  have hn : (Fintype.card A:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring
lemma uniform_pair_match_integral (G : ℝ) :
    (∫p:A×A, (if p.1=p.2 then G else 1)
      ∂((PMF.uniformOfFintype A).toMeasure.prod (PMF.uniformOfFintype A).toMeasure))=
      1+(G-1)/(Fintype.card A:ℝ) := by
  rw [integral_prod _ (by exact Integrable.of_finite)]
  simp only [uniform_match_integral]
  simp

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_PartialLabelMoment
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
open scoped BigOperators ENNReal
namespace HardSphere.Comparison
lemma partial_match_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι→Type*} [∀i,DecidableEq (A i)] (S : Finset ι) (G : ℝ) (p : ∀i,A i×A i) :
    (∏i,if i∈S then (if (p i).1=(p i).2 then G else 1) else 1)=
      G^(S.filter (fun i ↦ (p i).1=(p i).2)).card := by
  have he (i : ι) : (if i∈S then (if (p i).1=(p i).2 then G else 1) else 1)=
      if i∈S ∧ (p i).1=(p i).2 then G else 1 := by
    by_cases hi : i∈S <;> simp [hi]
  simp_rw [he]
  rw [Finset.prod_ite]
  have hs : (Finset.univ.filter (fun i:ι ↦ i∈S ∧ (p i).1=(p i).2))=
      S.filter (fun i ↦ (p i).1=(p i).2) := by ext i; simp
  simp only [Finset.prod_const, one_pow, mul_one, hs]

lemma partial_label_match_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι→Type*) [∀i,Fintype (A i)] [∀i,Nonempty (A i)] [∀i,DecidableEq (A i)]
    [∀i,MeasurableSpace (A i)] [∀i,MeasurableSingletonClass (A i)]
    (S : Finset ι) (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hcard : ∀i∈S,M≤2*(Fintype.card (A i):ℝ)) :
    (∫p:∀i,A i×A i,G^(S.filter (fun i ↦ (p i).1=(p i).2)).card
      ∂Measure.pi (fun i ↦ (PMF.uniformOfFintype (A i)).toMeasure.prod
        (PMF.uniformOfFintype (A i)).toMeasure))≤
      Real.exp ((2*(G-1)/M)*(S.card:ℝ)) := by
  simp_rw [←partial_match_eq_pow S G]
  rw [integral_fintype_prod_eq_prod (fun (i:ι) (p:A i×A i) ↦
    if i∈S then (if p.1=p.2 then G else 1) else 1)]
  have hi (i : ι) : (∫p:A i×A i, (if i∈S then (if p.1=p.2 then G else 1) else 1)
      ∂((PMF.uniformOfFintype (A i)).toMeasure.prod (PMF.uniformOfFintype (A i)).toMeasure))=
      if i∈S then 1+(G-1)/(Fintype.card (A i):ℝ) else 1 := by
    by_cases h : i∈S
    · simp only [h,ite_true,uniform_pair_match_integral]
    · simp [h]
  simp_rw [hi]
  calc
    _ ≤ ∏i:ι,Real.exp (if i∈S then 2*(G-1)/M else 0) := by
      apply Finset.prod_le_prod
      · intro i _
        by_cases h : i∈S
        · simp only [h,ite_true]
          have := div_nonneg (sub_nonneg.mpr hG) (Nat.cast_nonneg (Fintype.card (A i)))
          linarith
        · simp [h]
      · intro i _
        by_cases h : i∈S
        · simp only [h,ite_true]
          have hn : (0:ℝ)<Fintype.card (A i) := by exact_mod_cast Fintype.card_pos
          have hd : (G-1)/(Fintype.card (A i):ℝ)≤2*(G-1)/M := by
            apply (div_le_div_iff₀ hn hM).mpr
            nlinarith [hcard i h]
          linarith [Real.add_one_le_exp (2*(G-1)/M)]
        · simp [h]
    _ = _ := by
      rw [←Real.exp_sum]
      congr 1
      rw [←Finset.sum_filter]
      simp [mul_comm]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RouteMatches
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalCodedRoute_finite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalLabels_markov _root_.OAI.HardSphere.Groups.physicalMixedRoutes_finite _root_.OAI.HardSphere.Groups.physicalRouteFamily_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped Classical
namespace HardSphere.Comparison
open _root_.OAI.HardSphere.Lattice MeasureTheory ProbabilityTheory
variable {K : ℕ} {x y : DiscreteTorus K} {J : Type*} [DecidableEq J]

lemma routeSlots_inter_card {d e : ℕ} (f : Fin d↪J) (g : Fin e↪J) :
    (routeSlots f∩routeSlots g).card=1+((Finset.univ.image f)∩(Finset.univ.image g)).card := by
  have he : routeSlots f∩routeSlots g=insert none
      ((((Finset.univ.image f)∩(Finset.univ.image g))).image some) := by
    ext j
    cases j <;> simp [routeSlots_exact]
  rw [he,Finset.card_insert_of_notMem (by simp)]
  rw [Finset.card_image_of_injective _ (Option.some_injective _),Nat.add_comm]

lemma matched_labels_bound (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (f g : DiscreteTorus K→J)
    (hf : ∀v∈departureSites p,anchor (f v)=v)
    (hg : ∀v∈departureSites q,anchor (g v)=v) :
    ((Finset.univ.image (fun i : Fin p.val.length ↦ f (pathVertexEmbedding p i.castSucc)))∩
      (Finset.univ.image (fun i : Fin q.val.length ↦ g (pathVertexEmbedding q i.castSucc)))).card≤
      (matchingSites p q f g).card := by
  let s := (Finset.univ.image (fun i : Fin p.val.length ↦ f (pathVertexEmbedding p i.castSucc)))∩
      (Finset.univ.image (fun i : Fin q.val.length ↦ g (pathVertexEmbedding q i.castSucc)))
  have hip (i : Fin p.val.length) : pathVertexEmbedding p i.castSucc∈departureSites p :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hiq (i : Fin q.val.length) : pathVertexEmbedding q i.castSucc∈departureSites q :=
    Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hin : Set.InjOn anchor (s : Set J) := by
    intro a ha b hb hab
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hb).1
    rw [hf _ (hip i),hf _ (hip j)] at hab
    exact congrArg f hab
  rw [←Finset.card_image_of_injOn hin]
  apply Finset.card_le_card
  intro v hv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).1
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (Finset.mem_inter.mp ha).2
  have hia : anchor a=pathVertexEmbedding p i.castSucc := by rw [←hi,hf _ (hip i)]
  have hja : anchor a=pathVertexEmbedding q j.castSucc := by rw [←hj,hg _ (hiq j)]
  refine Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hia.symm ▸ hip i,hja.symm ▸ hiq j⟩,?_⟩
  calc
    f (anchor a) = a := by rw [hia,hi]
    _ = g (anchor a) := by rw [hja,hj]

end HardSphere.Comparison

end
end

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

lemma shared_departures_le_encounters (R : ℕ) (p q : SimplePath x y) :
    (departureSites p∩departureSites q).card ≤ simpleEncounter R p q := by
  let s := departureSites p∩departureSites q
  have hi : Function.Injective (fun v : DiscreteTorus K ↦ (v,v)) := by
    intro a b h;exact congrArg Prod.fst h
  have hs : s.image (fun v ↦ (v,v))⊆encounterSet (torusNear K R)
      p.val.support.toFinset q.val.support.toFinset := by
    intro v hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    refine (mem_encounterSet _ _ _ _ _).mpr ⟨departureSites_subset p (Finset.mem_inter.mp ha).1,
      departureSites_subset q (Finset.mem_inter.mp ha).2,?_⟩
    exact torusNear_refl K R a
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hi] at hc
  exact hc

lemma route_label_integral [NeZero K] (p q : SimplePath x y) (anchor : J→DiscreteTorus K)
    (A : DiscreteTorus K→Type*) [∀v,Fintype (A v)] [∀v,Nonempty (A v)]
    [∀v,DecidableEq (A v)] [∀v,MeasurableSpace (A v)] [∀v,MeasurableSingletonClass (A v)]
    (decode : ∀v,A v→J)
    (hd : ∀v∈departureSites p∩departureSites q,Function.Injective (decode v))
    (ha : ∀v∈departureSites p∪departureSites q,∀a,anchor (decode v a)=v)
    (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hm : ∀v∈departureSites p∩departureSites q,M≤2*(Fintype.card (A v):ℝ)) :
    (∫z:∀v,A v×A v,
      G^(1+(((Finset.univ.image (fun i : Fin p.val.length ↦
        decode (pathVertexEmbedding p i.castSucc) (z (pathVertexEmbedding p i.castSucc)).1))∩
        (Finset.univ.image (fun i : Fin q.val.length ↦
        decode (pathVertexEmbedding q i.castSucc) (z (pathVertexEmbedding q i.castSucc)).2)))).card)
      ∂Measure.pi (fun v ↦ (PMF.uniformOfFintype (A v)).toMeasure.prod
        (PMF.uniformOfFintype (A v)).toMeasure))≤
      G*Real.exp ((2*(G-1)/M)*((departureSites p∩departureSites q).card:ℝ)) := by
  let μ := Measure.pi (fun v ↦ (PMF.uniformOfFintype (A v)).toMeasure.prod
        (PMF.uniformOfFintype (A v)).toMeasure)
  have hdec (z : ∀v,A v×A v) : matchingSites p q (fun v ↦ decode v (z v).1)
      (fun v ↦ decode v (z v).2)=
      (departureSites p∩departureSites q).filter (fun v ↦ (z v).1=(z v).2) := by
    ext v
    simp only [matchingSites,Finset.mem_filter]
    constructor
    · exact fun h ↦ ⟨h.1,hd v h.1 h.2⟩
    · exact fun h ↦ ⟨h.1,congrArg (decode v) h.2⟩
  have hbound (z : ∀v,A v×A v) := matched_labels_bound p q anchor
    (fun v ↦ decode v (z v).1) (fun v ↦ decode v (z v).2)
    (fun v hv ↦ ha v (Finset.mem_union_left _ hv) _) (fun v hv ↦ ha v (Finset.mem_union_right _ hv) _)
  calc
    _ ≤ ∫z:∀v,A v×A v,
        G*G^((departureSites p∩departureSites q).filter (fun v ↦ (z v).1=(z v).2)).card ∂μ := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro z
      dsimp only
      rw [←pow_succ']
      apply pow_le_pow_right₀ hG
      rw [Nat.add_comm]
      exact Nat.succ_le_succ (by simpa only [hdec z] using hbound z)
    _ = G*(∫z:∀v,A v×A v,
        G^((departureSites p∩departureSites q).filter (fun v ↦ (z v).1=(z v).2)).card ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (partial_label_match_moment A _ G M hG hM hm) (by linarith)

end HardSphere.Comparison

end
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

lemma physicalRouteLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) :
    Measurable (fun z : (PhysicalDatum N K M G L×PhysicalRouteCode x y J)×(Option J→C(Time,Point)) ↦ physicalRouteLikelihood (M:=M) hL g m t r R C S u particle hxy b z.1 z.2) :=
  Kernel.measurable_rnDeriv _ _
lemma physicalRouteLikelihood_measure {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (d : PhysicalDatum N K M G L) (c : PhysicalRouteCode x y J) :
    physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,c)=ᵐ[
      physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d]
      ((physicalCodedRoute hL g m t r R C S u particle hxy c d).map
        (if b then Prod.fst else Prod.snd)).rnDeriv
      (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d) := by
  have hb : Measurable (if b then (Prod.fst : (Option J→C(Time,Point))×(Option J→C(Time,Point))→_) else Prod.snd) := by
    cases b
    · exact measurable_snd
    · exact measurable_fst
  have H := Kernel.rnDeriv_eq_rnDeriv_measure
    (κ:=physicalRouteView (M:=M) hL g m t r R C S u particle hxy b)
    (η:=physicalFamilyReference hL g m t r R C S u particle b) (a:=(d,c))
  simpa only [physicalRouteLikelihood,physicalRouteView,physicalFamilyReference,
    Kernel.comap_apply,Kernel.map_apply _ hb,physicalRouteFamily,Kernel.coe_mk] using H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable

lemma uniformFinset_subtype {J : Type*} [Fintype J] [DecidableEq J]
    [MeasurableSpace J] [MeasurableSingletonClass J] (s : Finset J) (hs : s.Nonempty) :
    have : Nonempty s := hs.to_subtype
    ((PMF.uniformOfFintype s).toMeasure).map (Subtype.val : s→J)=
      (PMF.uniformOfFinset s hs).toMeasure := by
  apply Measure.ext_of_singleton
  intro j
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton j),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  by_cases hj : j∈s
  · have he : (Subtype.val : s→J) ⁻¹' {j}={⟨j,hj⟩} := by ext a; simp [Subtype.ext_iff]
    rw [he,PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp only [PMF.uniformOfFintype_apply,PMF.uniformOfFinset_apply,hj,ite_true,Fintype.card_coe]
  · have he : (Subtype.val : s→J) ⁻¹' {j}=∅ := by
      ext a
      simp only [mem_preimage,mem_singleton_iff,mem_empty_iff_false,iff_false]
      intro h
      exact hj (h ▸ a.property)
    rw [he,measure_empty]
    simp only [PMF.uniformOfFinset_apply,hj,ite_false]

lemma paddedLabels_card {J : Type*} [DecidableEq J] (s : Finset J) (hs : s.Nonempty) :
    (paddedLabels s).card=s.card := by
  rw [paddedLabels,ite_eq_left hs,Finset.card_image_of_injective _ (Option.some_injective _)]

lemma label_pair_transport {V J : Type*} [Fintype V] [Fintype J] [DecidableEq J]
    [MeasurableSpace J] [MeasurableSingletonClass J] (s : V→Finset J) :
    let A := fun v ↦ paddedLabels (s v)
    have : ∀v,Nonempty (A v) := fun v ↦ (paddedLabels_nonempty (s v)).to_subtype
    MeasurePreserving (fun z : ∀v,A v×A v ↦ (fun v ↦ (z v).1.val,fun v ↦ (z v).2.val))
      (Measure.pi fun v ↦ (PMF.uniformOfFintype (A v)).toMeasure.prod
        (PMF.uniformOfFintype (A v)).toMeasure)
      ((Measure.pi fun v ↦ uniformLabels (s v)).prod (Measure.pi fun v ↦ uniformLabels (s v))) := by
  dsimp only
  let A := fun v ↦ paddedLabels (s v)
  have : ∀v,Nonempty (A v) := fun v ↦ (paddedLabels_nonempty (s v)).to_subtype
  have hp (v : V) : MeasurePreserving (Subtype.val : A v→Option J)
      (PMF.uniformOfFintype (A v)).toMeasure (uniformLabels (s v)) :=
    ⟨measurable_subtype_coe,uniformFinset_subtype (A v) (paddedLabels_nonempty (s v))⟩
  exact (measurePreserving_arrowProdEquivProdArrow (Option J) (Option J) V
      (fun v ↦ uniformLabels (s v)) (fun v ↦ uniformLabels (s v))).comp
    (measurePreserving_pi _ _ (fun v ↦ (hp v).prod (hp v)))

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma padded_label_overlap (p q : SimplePath x y) (s : DiscreteTorus K→Finset J)
    (home : J→DiscreteTorus K)
    (hn : ∀v∈departureSites p∪departureSites q,(s v).Nonempty)
    (hh : ∀v∈departureSites p∪departureSites q,∀j∈s v,home j=v)
    (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hm : ∀v∈departureSites p∩departureSites q,M≤2*((s v).card:ℝ)) :
    (∫z : (DiscreteTorus K→Option J)×(DiscreteTorus K→Option J),
      G^(1+(fieldLabelImage p z.1∩fieldLabelImage q z.2).card)
      ∂(Measure.pi (fun v ↦ uniformLabels (s v))).prod (Measure.pi (fun v ↦ uniformLabels (s v))))≤
      G*Real.exp ((2*(G-1)/M)*((departureSites p∩departureSites q).card:ℝ)) := by
  let A := fun v ↦ paddedLabels (s v)
  have : ∀v,Nonempty (A v) := fun v ↦ (paddedLabels_nonempty (s v)).to_subtype
  have ha : ∀v∈departureSites p∪departureSites q,∀a : A v,
      a.val.elim x home=v := by
    intro v hv a
    have h := a.property
    change a.val∈paddedLabels (s v) at h
    rw [paddedLabels,ite_eq_left (hn v hv)] at h
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp h
    rw [←he]
    exact hh v hv j hj
  have hc : ∀v∈departureSites p∩departureSites q,M≤2*(Fintype.card (A v):ℝ) := by
    intro v hv
    rw [Fintype.card_coe]
    change M≤2*((paddedLabels (s v)).card:ℝ)
    rw [paddedLabels_card _ (hn v (Finset.mem_union_left _ (Finset.mem_inter.mp hv).1))]
    exact hm v hv
  have H := route_label_integral p q (fun o : Option J ↦ o.elim x home) (fun v ↦ (A v : Type _)) (fun _ a ↦ a.val)
    (fun _ _ ↦ Subtype.val_injective) ha G M hG hM hc
  have hmap := (label_pair_transport s).map_eq
  rw [←hmap,integral_map (label_pair_transport s).measurable.aemeasurable
    ((measurable_of_countable _ : Measurable (fun z : (DiscreteTorus K→Option J)×(DiscreteTorus K→Option J) ↦
      G^(1+(fieldLabelImage p z.1∩fieldLabelImage q z.2).card))).aestronglyMeasurable)]
  exact H

omit [NeZero K] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma fieldLabelImage_eq (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : RouteFieldValid p z) :
    fieldLabelImage p z=(Finset.univ.image (fieldLabels p z hz)).image some := by
  simp only [fieldLabelImage,fieldLabels_spec p z hz,Finset.image_image,Function.comp_def]

omit [NeZero K] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma fieldRoute_overlap (hxy : x≠y) (p q : SimplePath x y)
    (z w : DiscreteTorus K→Option J) (hz : RouteFieldValid p z) (hw : RouteFieldValid q w) :
    (routeSlots (fieldRouteLabels hxy p z hz)∩routeSlots (fieldRouteLabels hxy q w hw)).card=
      1+(fieldLabelImage p z∩fieldLabelImage q w).card := by
  rw [fieldRouteLabels,fieldRouteLabels,routeSlots_reparam,routeSlots_reparam,
    routeSlots_inter_card,fieldLabelImage_eq p z hz,fieldLabelImage_eq q w hw,
    ←Finset.image_inter _ _ (Option.some_injective J),
    Finset.card_image_of_injective _ (Option.some_injective J)]

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalCodedMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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

omit [NeZero K] in
lemma simpleEncounter_comm (R : ℕ) (p q : SimplePath x y) :
    simpleEncounter R p q=simpleEncounter R q p := by
  unfold simpleEncounter
  apply Finset.card_bij (fun z _ ↦ z.swap)
  · intro z hz
    obtain ⟨hp,hq,hn⟩ := (mem_encounterSet _ _ _ _ _).mp hz
    exact (mem_encounterSet _ _ _ _ _).mpr ⟨hq,hp,torusNear_symm hn⟩
  · intro z _ w _ he
    exact Prod.swap_injective he
  · intro z hz
    obtain ⟨hp,hq,hn⟩ := (mem_encounterSet _ _ _ _ _).mp hz
    exact ⟨z.swap,(mem_encounterSet _ _ _ _ _).mpr ⟨hq,hp,torusNear_symm hn⟩,rfl⟩

theorem physicalCoded_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p p' : SimplePath x y) (z z' : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (hz' : ∀v,z' v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (ha' : ∀i : Fin p'.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p' i.castSucc) d).Nonempty)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) (b : Bool) :
    (∫⁻w,physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)) w *
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p',z')) w
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)≤
      (routeDensityBound t)^(1+(fieldLabelImage p z∩fieldLabelImage p' z').card)*
        (a⁻¹)^(8*simpleEncounter 30 p p') := by
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  have hv' := routeFieldValid_of_supported hL g m t r R C S u particle d p' z' hz' ha'
  let f := fieldRouteLabels hxy p z hv
  let f' := fieldRouteLabels hxy p' z' hv'
  let v := simpleRouteVertices p (p.val.length-1)
  let v' := simpleRouteVertices p' (p'.val.length-1)
  let steps := simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p)
  let steps' := simpleRouteSteps hL p' _ (simpleRouteLength_eq hxy p')
  have hc := simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)
  have hc' := simpleRouteSteps_period hL p' _ (simpleRouteLength_eq hxy p')
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  have hh' := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p' z' hz' ha' hv'
  let A := Classical.choice (physicalRouteAux_nonempty hL g m t r R C S u particle f v steps d ht hc
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2) hp)
  let B := Classical.choice (physicalRouteAux_nonempty hL g m t r R C S u particle f' v' steps' d ht hc'
    (fun i ↦ (hh' i).1) (fun i ↦ (hh' i).2) hp)
  have hn := simpleRouteVertices_distance hL p _ (simpleRouteLength_eq hxy p)
  have hn' := simpleRouteVertices_distance hL p' _ (simpleRouteLength_eq hxy p')
  have ha1 : 1≤a⁻¹ := ENNReal.one_le_inv.mpr ((le_add_right le_rfl).trans hsmall)
  have hover : (routeSlots f∩routeSlots f').card=1+(fieldLabelImage p z∩fieldLabelImage p' z').card :=
    fieldRoute_overlap hxy p p' z z' hv hv'
  have he0 : v 0=siteIndex x := simpleRouteVertices_zero p _
  have he0' : v' 0=siteIndex x := simpleRouteVertices_zero p' _
  have he1 : v (Fin.last (p.val.length-1+1))=siteIndex y := simpleRouteVertices_last p _ (simpleRouteLength_eq hxy p)
  have he1' : v' (Fin.last (p'.val.length-1+1))=siteIndex y := simpleRouteVertices_last p' _ (simpleRouteLength_eq hxy p')
  have HL := lintegral_congr_ae ((physicalRouteLikelihood_measure hL g m t r R C S u particle hxy b d (p,z)).mul
    (physicalRouteLikelihood_measure hL g m t r R C S u particle hxy b d (p',z')))
  simp only [Pi.mul_apply] at HL
  rw [HL]
  simp only [physicalCodedRoute,dite_eq_left hv,dite_eq_left hv']
  cases b with
  | true =>
    simp only [ite_true]
    have H := physical_first_likelihood_moment hL g m t r R C S ht u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2)
      hn hn' (he1'.trans he1.symm) hm hp q a ha0 hq hsmall
    have Hrn := physical_first_RN_cross hL g m t r R C S ht hr u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2) hp (he1'.trans he1.symm)
    rw [he1] at Hrn H
    rw [Hrn]
    apply H.trans
    rw [div_eq_mul_inv,ENNReal.inv_pow,hover]
    apply mul_le_mul' le_rfl
    apply pow_le_pow_right₀ ha1
    have h1 := simpleRoute_near_first p p' (simpleRouteLength_eq hxy p) (simpleRouteLength_eq hxy p')
      (fun j ↦ datumHome hL d (particle j)) f f' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) 30
    have h2 := simpleRoute_near_first p' p (simpleRouteLength_eq hxy p') (simpleRouteLength_eq hxy p)
      (fun j ↦ datumHome hL d (particle j)) f' f (fun i ↦ (hh' i).1) (fun i ↦ (hh i).1) 30
    rw [simpleEncounter_comm 30 p' p] at h2
    omega
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    have H := physical_second_likelihood_moment hL g m t r R C S ht u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2)
      hn hn' (he0'.trans he0.symm) hm hp q a ha0 hq hsmall
    have Hrn := physical_second_RN_cross hL g m t r R C S ht hr u particle f v steps f' v' steps' d A B
      hc hc' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) (fun i ↦ (hh i).2) (fun i ↦ (hh' i).2) hp (he0'.trans he0.symm)
    rw [he0] at Hrn H
    rw [Hrn]
    apply H.trans
    rw [div_eq_mul_inv,ENNReal.inv_pow,hover]
    apply mul_le_mul' le_rfl
    apply pow_le_pow_right₀ ha1
    have h1 := simpleRoute_near_second p p' (simpleRouteLength_eq hxy p) (simpleRouteLength_eq hxy p')
      (fun j ↦ datumHome hL d (particle j)) f f' (fun i ↦ (hh i).1) (fun i ↦ (hh' i).1) 30
    have h2 := simpleRoute_near_second p' p (simpleRouteLength_eq hxy p') (simpleRouteLength_eq hxy p)
      (fun j ↦ datumHome hL d (particle j)) f' f (fun i ↦ (hh' i).1) (fun i ↦ (hh i).1) 30
    rw [simpleEncounter_comm 30 p' p] at h2
    omega

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physicalCoded_density {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (b : Bool) :
    (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d).withDensity
      (physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z))) =
    (physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d).map
      (if b then Prod.fst else Prod.snd) := by
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  let f := fieldRouteLabels hxy p z hv
  let v := simpleRouteVertices p (p.val.length-1)
  let steps := simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p)
  have hc := simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  let A := Classical.choice (physicalRouteAux_nonempty hL g m t r R C S u particle f v steps d ht hc
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2) hp)
  have hd := physicalPairedRoute_densities hL g m t r R C S ht hr u particle f v steps hc d
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2) A hp
  rw [withDensity_congr_ae (physicalRouteLikelihood_measure hL g m t r R C S u particle hxy b d (p,z))]
  have : IsFiniteMeasure (physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d) :=
    IsFiniteKernel.isFiniteMeasure (κ:=physicalCodedRoute hL g m t r R C S u particle hxy (p,z)) d
  have : IsFiniteMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d) :=
    IsFiniteKernel.isFiniteMeasure (κ:=physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x))) d
  have : IsFiniteMeasure ((physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d).map
      (if b then Prod.fst else Prod.snd)) := Measure.isFiniteMeasure_map _ _
  have := Measure.haveLebesgueDecomposition_of_sigmaFinite
    (μ:=(physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d).map (if b then Prod.fst else Prod.snd))
    (ν:=physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)
  apply Measure.withDensity_rnDeriv_eq
  simp only [physicalCodedRoute,dite_eq_left hv]
  have hf : Measurable (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) :=
    routeConfigMap_measurable _ (fun _ ↦ measurable_subtype_coe)
  cases b with
  | true =>
    simp only [ite_true]
    rw [hd.1,←simpleRouteVertices_last p _ (simpleRouteLength_eq hxy p),
      ←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
    exact (withDensity_absolutelyContinuous _ _).map hf
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    rw [hd.2,←simpleRouteVertices_zero p _,←physicalPrimary_on_map hL g m t r R C S hr u particle _ d]
    exact (withDensity_absolutelyContinuous _ _).map hf

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_LabelEncounterAverage
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
open Comparison HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma padded_label_encounter (p q : SimplePath x y) (s : DiscreteTorus K→Finset J)
    (home : J→DiscreteTorus K)
    (hn : ∀v∈departureSites p∪departureSites q,(s v).Nonempty)
    (hh : ∀v∈departureSites p∪departureSites q,∀j∈s v,home j=v)
    (G M : ℝ) (hG : 1≤G) (hM : 0<M)
    (hm : ∀v∈departureSites p∩departureSites q,M≤2*((s v).card:ℝ)) (R : ℕ) :
    (∫⁻z,∫⁻w,(ENNReal.ofReal G)^(1+(fieldLabelImage p z∩fieldLabelImage q w).card)
      ∂Measure.pi (fun v ↦ uniformLabels (s v)) ∂Measure.pi (fun v ↦ uniformLabels (s v)))≤
      ENNReal.ofReal (G*Real.exp ((2*(G-1)/M)*(simpleEncounter R p q:ℝ))) := by
  have G0 : 0≤G := by linarith
  rw [←lintegral_prod (fun z : (DiscreteTorus K→Option J)×(DiscreteTorus K→Option J) ↦
    (ENNReal.ofReal G)^(1+(fieldLabelImage p z.1∩fieldLabelImage q z.2).card))
    (measurable_of_countable _).aemeasurable]
  simp_rw [←ENNReal.ofReal_pow G0]
  rw [←ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (ae_of_all _ (fun _ ↦ pow_nonneg G0 _))]
  apply ENNReal.ofReal_le_ofReal
  apply (padded_label_overlap p q s home hn hh G M hG hM hm).trans
  apply mul_le_mul_of_nonneg_left _ G0
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast shared_departures_le_encounters R p q
  · positivity

lemma encounter_absorb (G M κ δ : ℝ) (hG : 1≤G) (_hM : 0<M) (hδ : 0<δ)
    (hκ : 2*(G-1)/M-8*Real.log δ≤κ) (n : ℕ) :
    ENNReal.ofReal (G*Real.exp ((2*(G-1)/M)*(n:ℝ))) *
        (ENNReal.ofReal δ)⁻¹^(8*n) ≤ ENNReal.ofReal (G*Real.exp (κ*(n:ℝ))) := by
  have G0 : 0≤G := by linarith
  have he : (δ⁻¹)^(8*n)=Real.exp ((-8*Real.log δ)*(n:ℝ)) := by
    have H := Real.exp_nat_mul (-Real.log δ) (8*n)
    rw [Real.exp_neg,Real.exp_log hδ] at H
    exact H.symm.trans (congrArg Real.exp (by push_cast; ring))
  rw [←ENNReal.ofReal_inv_of_pos hδ,←ENNReal.ofReal_pow (inv_nonneg.mpr hδ.le),
    ←ENNReal.ofReal_mul (mul_nonneg G0 (Real.exp_nonneg _)),he]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ G0
  apply Real.exp_le_exp.mpr
  nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem physicalLabel_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (p p' : SimplePath x y) (hM : 0<M)
    (hsupply : ∀v∈departureSites p∪departureSites p',
      (M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ))
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q : ℝ≥0∞) (δ B κ : ℝ) (hδ : 0<δ) (hB : 1≤B) (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) (b : Bool) :
    (∫⁻z,∫⁻z',∫⁻w,physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)) w *
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p',z')) w
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d
      ∂physicalLabels hL g m t r R C S u particle d
      ∂physicalLabels hL g m t r R C S u particle d)≤
      ENNReal.ofReal (B*Real.exp (κ*(simpleEncounter 30 p p':ℝ))) := by
  let s := fun v ↦ branchAccessible hL g m t r R C S u particle v d
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hn : ∀v∈departureSites p∪departureSites p',(s v).Nonempty := by
    intro v hv
    apply Finset.card_pos.mp
    have H := hsupply v hv
    have : (0:ℝ)<(s v).card := by dsimp [s]; linarith
    exact_mod_cast this
  have hhome : ∀v∈departureSites p∪departureSites p',∀j∈s v,
      indexSite (datumHome hL d (particle j))=v := by
    intro v _ j hj
    rw [(branchAccessible_home hL g m t r R C S u particle v d j hj).1]
    exact indexSite_siteIndex v
  have ha : ∀i : Fin p.val.length,(s (pathVertexEmbedding p i.castSucc)).Nonempty := by
    intro i
    exact hn _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have ha' : ∀i : Fin p'.val.length,(s (pathVertexEmbedding p' i.castSucc)).Nonempty := by
    intro i
    exact hn _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have Hav := padded_label_encounter p p' s (fun j ↦ indexSite (datumHome hL d (particle j)))
    hn hhome B M hB hM' (fun v hv ↦ hsupply v (Finset.mem_union_left _ (Finset.mem_inter.mp hv).1)) 30
  have hlabels : physicalLabels hL g m t r R C S u particle d=Measure.pi (fun v ↦ uniformLabels (s v)) := by
    rw [physicalLabels, finiteKernelPi_apply]
    rfl
  calc
    _ ≤ ∫⁻z,∫⁻z',(ENNReal.ofReal B)^(1+(fieldLabelImage p z∩fieldLabelImage p' z').card)*
      (ENNReal.ofReal δ)⁻¹^(8*simpleEncounter 30 p p')
      ∂physicalLabels hL g m t r R C S u particle d
      ∂physicalLabels hL g m t r R C S u particle d := by
      apply lintegral_mono_ae
      filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
      apply lintegral_mono_ae
      filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z' hz'
      apply (physicalCoded_moment hL g m t r R C S ht hr u particle d hxy p p' z z' hz hz'
        ha ha' hm hp q (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) hq hsmall b).trans
      exact mul_le_mul' (pow_le_pow_left' hBt _) le_rfl
    _ = (∫⁻z,∫⁻z',(ENNReal.ofReal B)^(1+(fieldLabelImage p z∩fieldLabelImage p' z').card)
        ∂physicalLabels hL g m t r R C S u particle d
        ∂physicalLabels hL g m t r R C S u particle d) *
        (ENNReal.ofReal δ)⁻¹^(8*simpleEncounter 30 p p') := by
      simp_rw [lintegral_mul_const _ (measurable_of_countable _)]
    _ ≤ ENNReal.ofReal (B*Real.exp ((2*(B-1)/M)*(simpleEncounter 30 p p':ℝ))) *
        (ENNReal.ofReal δ)⁻¹^(8*simpleEncounter 30 p p') := by
      apply mul_le_mul' _ le_rfl
      rwa [hlabels]
    _ ≤ _ := encounter_absorb B M κ δ hB hM' hδ hκ _

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
variable {Q X : Type*} [MeasurableSpace Q] [MeasurableSpace X]

lemma mixed_likelihood_square (σ : Measure Q) (P : Measure X) [SFinite σ] [SFinite P]
    (L : Q×X→ℝ≥0∞) (hL : Measurable L) :
    (∫⁻x,(∫⁻q,L (q,x) ∂σ)^2 ∂P)=
      ∫⁻q,∫⁻q',∫⁻x,L (q,x)*L (q',x) ∂P ∂σ ∂σ := by
  have hslice (x : X) : Measurable (fun q ↦ L (q,x)) := hL.comp measurable_prodMk_right
  have hs (x : X) : (∫⁻q,L (q,x) ∂σ)^2=
      ∫⁻q,∫⁻q',L (q,x)*L (q',x) ∂σ ∂σ := by
    simp_rw [lintegral_const_mul _ (hslice x)]
    rw [lintegral_mul_const _ (hslice x),pow_two]
  simp_rw [hs]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro q
    exact lintegral_lintegral_swap
      (show Measurable (Function.uncurry (fun x q' ↦ L (q,x)*L (q',x))) from
        ((hL.comp measurable_prodMk_left).comp measurable_fst).mul
          (hL.comp (measurable_snd.prodMk measurable_fst))).aemeasurable
  · apply Measurable.aemeasurable
    change Measurable (fun p : X×Q ↦ ∫⁻q',L (p.2,p.1)*L (q',p.1) ∂σ)
    exact (show Measurable (fun p : (X×Q)×Q ↦ L (p.1.2,p.1.1)*L (p.2,p.1.1)) from
      (hL.comp (measurable_fst.snd.prodMk measurable_fst.fst)).mul
        (hL.comp (measurable_snd.prodMk measurable_fst.fst))).lintegral_prod_right'

lemma tag_likelihood_square {I : Type*} [Fintype I] (P : Measure X)
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    (∑i,∫⁻x,(f i x)^2 ∂P)≤∫⁻x,(∑i,f i x)^2 ∂P := by
  rw [←lintegral_finsetSum _ (fun i _ ↦ (hf i).pow_const 2)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [pow_two,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [pow_two]
  exact mul_le_mul' (le_refl _) ((show f i x ≤ ∑j,f j x from Finset.single_le_sum (f:=fun j ↦ f j x) (fun j _ ↦ bot_le) (Finset.mem_univ i)))

end HardSphere.Comparison

end
end

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

lemma observed_kernel_second_moment (P ν : Measure X) [IsFiniteMeasure P] [IsFiniteMeasure ν]
    (hac : ν≪P) (κ : Kernel X Y) [IsMarkovKernel κ]
    (hi : Integrable (fun x ↦ (ν.rnDeriv P x).toReal^2) P) :
    Integrable (fun y ↦ (((ν.compProd κ).map Prod.snd).rnDeriv
      ((P.compProd κ).map Prod.snd) y).toReal^2) ((P.compProd κ).map Prod.snd) ∧
    (∫y,(((ν.compProd κ).map Prod.snd).rnDeriv
      ((P.compProd κ).map Prod.snd) y).toReal^2 ∂(P.compProd κ).map Prod.snd)≤
      ∫x,(ν.rnDeriv P x).toReal^2 ∂P := by
  have hf : (P.compProd κ).map Prod.fst=P := Measure.fst_compProd P κ
  have hm : Measurable (fun x ↦ (ν.rnDeriv P x).toReal^2) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.pow_const _
  have hi' : Integrable (fun p : X×Y ↦ (ν.rnDeriv P p.1).toReal^2) (P.compProd κ) := by
    apply (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hf]
  have he : (fun p : X×Y ↦ ((ν.compProd κ).rnDeriv (P.compProd κ) p).toReal^2)=ᵐ[P.compProd κ]
      (fun p ↦ (ν.rnDeriv P p.1).toReal^2) :=
    (rnDeriv_measure_compProd_left ν P κ).fun_comp (fun t : ℝ≥0∞ ↦ t.toReal^2)
  have h := observed_second_moment (P.compProd κ) (ν.compProd κ) (hac.compProd_left κ)
    Prod.snd measurable_snd (hi'.congr he.symm)
  refine ⟨h.1,h.2.trans_eq ?_⟩
  rw [integral_congr_ae he,←integral_map measurable_fst.aemeasurable hm.aestronglyMeasurable,hf]

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalAverageMoment
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalAverageLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    [IsSFiniteKernel ν] :
    Measurable (fun z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) ↦
      physicalAverageLikelihood hL g m t r R C S u particle hxy b ν z.1 z.2) := by
  exact ((physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b).comp
    ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).lintegral_kernel_prod_right'
      (κ:=(ν.prod (physicalLabels hL g m t r R C S u particle)).comap Prod.fst measurable_fst)

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalAverageLikelihood_square {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y))
    [IsMarkovKernel ν] (d : PhysicalDatum N K M G L) :
    (∫⁻w,(physicalAverageLikelihood hL g m t r R C S u particle hxy b ν d w)^2
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)=
    ∫⁻p,∫⁻p',∫⁻z,∫⁻z',∫⁻w,
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)) w *
      physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p',z')) w
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d
      ∂physicalLabels hL g m t r R C S u particle d
      ∂physicalLabels hL g m t r R C S u particle d ∂ν d ∂ν d := by
  unfold physicalAverageLikelihood
  rw [mixed_likelihood_square _ _ (fun cw : PhysicalRouteCode x y J×(Option J→C(Time,Point)) ↦
    physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,cw.1) cw.2)
    ((physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))]
  simp_rw [Kernel.prod_apply,lintegral_prod _ (measurable_of_countable _).aemeasurable]
  apply lintegral_congr
  intro p
  exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable

theorem physicalAverage_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (d : PhysicalDatum N K M G L) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (hM : 0<M)
    (hsupply : ∀ᵐp ∂ν d,∀v∈departureSites p,
      (M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ))
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q : ℝ≥0∞) (δ B κ : ℝ) (hδ : 0<δ) (hB : 1≤B) (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hq : ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) (b : Bool) :
    (∫⁻w,(physicalAverageLikelihood hL g m t r R C S u particle hxy b ν d w)^2
      ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)≤
      ENNReal.ofReal B*(∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d) := by
  rw [physicalAverageLikelihood_square]
  simp_rw [←lintegral_const_mul _ (measurable_of_countable _),←ENNReal.ofReal_mul (zero_le_one.trans hB)]
  apply lintegral_mono_ae
  filter_upwards [hsupply] with p hpSupply
  apply lintegral_mono_ae
  filter_upwards [hsupply] with p' hpSupply'
  apply physicalLabel_moment hL g m t r R C S ht hr u particle d hxy p p' hM _ hm hp q δ B κ hδ hB hBt hκ hq hsmall b
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · exact hpSupply v h
  · exact hpSupply' v h

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
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalGoodLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (b : Bool) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsSFiniteKernel ν]
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E) :
    Measurable (physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E) :=
  (physicalAverageLikelihood_measurable hL g m t r R C S u particle hxy b ν).ite
    (hE.preimage measurable_fst) measurable_const

theorem physicalGoodLikelihood_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin N) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum N K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum N K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath)
    (b : Bool) :
    (∫⁻z,(physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E z)^2
      ∂μ ⊗ₘ physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)))≤
      ENNReal.ofReal B*ENNReal.ofReal Cpath := by
  rw [Measure.lintegral_compProd ((physicalGoodLikelihood_measurable hL g m t r R C S u particle hxy b ν E hE).pow_const 2)]
  have hind (d : PhysicalDatum N K M G L) :
      (∫⁻w,(physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E (d,w))^2
        ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d)=
      E.indicator (fun d ↦ ∫⁻w,(physicalAverageLikelihood hL g m t r R C S u particle hxy b ν d w)^2
        ∂physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d) d := by
    by_cases hd : d∈E <;> simp [physicalGoodLikelihood,hd]
  simp_rw [hind]
  rw [lintegral_indicator hE]
  calc
    _ ≤ ∫⁻d in E,ENNReal.ofReal B*(∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdata] with d hd
      exact physicalAverage_moment hL g m t r R C S ht hr u particle d hxy ν hM hd.1 hd.2.1 hd.2.2.1
        q δ B κ hδ hB hBt hκ hd.2.2.2 hsmall b
    _ = ENNReal.ofReal B*(∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ) := by
      rw [lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := mul_le_mul' le_rfl henc

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

omit [DecidableEq J] in
lemma physicalPrimary_extra {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (v : Fin 3→Fin K) (d : PhysicalDatum N K M G L) :
    ∀ᵐw ∂physicalPrimaryReference hL g m t r R C S u particle v d,
      physicalFullMidpoint particle (d,w) none∈centeredCell L (gridCenter L v) := by
  have hL1 : 1≤L.val := by rw [hL]; exact_mod_cast NeZero.pos K
  have hextra := (Measure.quasiMeasurePreserving_eval
    (fun i ↦ physicalSlotReference hL g m t r R C S u particle v i d) none).ae (cellPathReference_support hL1 v)
  rw [physicalPrimaryReference_apply,conditionedMeasure]
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_of_ae hextra] with w hw
  change fillGroup particle _ _ (optionParticle particle none)∈_
  rw [fillGroup_selected]
  exact hw

omit [NeZero K] [DecidableEq J] in
lemma physicalTagEvent_measurable {N M G : ℕ} {L : Length} (particle : J↪Fin N)
    (v : Fin 3→Fin K) (i : Fin N) : MeasurableSet (physicalTagEvent (M:=M) (G:=G) (L:=L) particle v i) :=
  .inter (show MeasurableSet {z : PhysicalDatum N K M G L×(Option J→C(Time,Point)) | i∈Set.range particle} from by
    by_cases h : i∈Set.range particle <;> simp [h]) ((centeredCell_measurable L _).preimage
    ((measurable_pi_apply (some i)).comp (physicalFullMidpoint_measurable particle)))

theorem physicalCodedRoute_tag_support {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (d : PhysicalDatum (N+1) K M G L) (hxy : x≠y)
    (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) (b : Bool) :
    ∀ᵐw ∂physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d,
      (d,if b then w.1 else w.2)∈physicalTagEvent particle (siteIndex (if b then x else y))
        (physicalCodeTag particle hxy b (p,z)) := by
  have he (b : Bool) : ∀ᵐw ∂physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d,
      physicalFullMidpoint particle (d,if b then w.1 else w.2) none∈
        centeredCell L (gridCenter L (siteIndex (if b then y else x))) := by
    have hd := physicalCoded_density hL g m t r R C S ht hr u particle d hxy p z hz ha hp b
    have h := (withDensity_absolutelyContinuous _ (physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,(p,z)))).ae_le (physicalPrimary_extra hL g m t r R C S u particle (siteIndex (if b then y else x)) d)
    rw [hd] at h
    have hf : Measurable (if b then (Prod.fst : ((Option J→C(Time,Point))×(Option J→C(Time,Point)))→_) else Prod.snd) := by cases b <;> simp <;> fun_prop
    have hm : Measurable (fun w : Option J→C(Time,Point) ↦ physicalFullMidpoint particle (d,w) none) :=
      (measurable_pi_apply none).comp ((physicalFullMidpoint_measurable particle).comp measurable_prodMk_left)
    have h' := (ae_map_iff hf.aemeasurable ((centeredCell_measurable L _).preimage hm)).mp h
    cases b <;> simpa using h'
  have hv := routeFieldValid_of_supported hL g m t r R C S u particle d p z hz ha
  have hh := fieldRouteLabels_physical hL g m t r R C S u particle d hxy p z hz ha hv
  have hmid := physicalPairedRoute_midpoint hL g m t r R C S ht u particle
    (fieldRouteLabels hxy p z hv) (simpleRouteVertices p (p.val.length-1))
    (simpleRouteSteps hL p _ (simpleRouteLength_eq hxy p))
    (simpleRouteSteps_period hL p _ (simpleRouteLength_eq hxy p)) d
    (fun i ↦ (hh i).1) (fun i ↦ (hh i).2)
  have hmid' : ∀ᵐw ∂physicalCodedRoute hL g m t r R C S u particle hxy (p,z) d,
      ∀i,physicalFullMidpoint particle (d,w.2) i=physicalFullMidpoint particle (d,w.1)
        (routePermutation ((fieldRouteLabels hxy p z hv).trans particle) i) := by
    simpa only [physicalCodedRoute,dite_eq_left hv] using hmid
  filter_upwards [he true,he false,hmid'] with w h1 h2 hm
  cases b with
  | true =>
    simp only [physicalTagEvent,mem_ofPred_eq,physicalCodeTag,dite_eq_left hv,ite_true]
    refine ⟨⟨_,rfl⟩,?_⟩
    have H := hm none
    rw [routePermutation_star] at H
    simp only [Function.Embedding.trans_apply] at H
    change physicalFullMidpoint particle (d,w.1) (some (particle (fieldRouteLabels hxy p z hv 0)))∈_
    rw [←H]
    exact h2
  | false =>
    simp only [physicalTagEvent,mem_ofPred_eq,physicalCodeTag,dite_eq_left hv,Bool.false_eq_true,ite_false]
    refine ⟨⟨_,rfl⟩,?_⟩
    have H := hm (some (particle (fieldRouteLabels hxy p z hv (Fin.last (p.val.length-1)))))
    change physicalFullMidpoint particle (d,w.2) (some (((fieldRouteLabels hxy p z hv).trans particle) (Fin.last (p.val.length-1)))) = physicalFullMidpoint particle (d,w.1) (routePermutation ((fieldRouteLabels hxy p z hv).trans particle) (some (((fieldRouteLabels hxy p z hv).trans particle) (Fin.last (p.val.length-1))))) at H
    rw [routePermutation_lastLabel] at H
    simp only [Function.Embedding.trans_apply] at H
    rw [H]
    exact h1

end HardSphere.Groups
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
lemma taggedFunction_measurable (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    Measurable (fun p : I×X ↦ f p.1 p.2) :=
  measurable_from_prod_countable_right hf

lemma tagged_density_square (P : Measure X) [SFinite P] (E : I→Set X)
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) :
    (∫⁻p,(f p.1 p.2)^2 ∂taggedReference P E)≤∫⁻x,(∑i,f i x)^2 ∂P := by
  apply (lintegral_mono' Measure.restrict_le_self (le_refl _)).trans
  rw [lintegral_prod _ (taggedFunction_measurable (fun i x ↦ (f i x)^2) (fun i ↦ (hf i).pow_const 2)).aemeasurable]
  rw [lintegral_count,tsum_fintype]
  exact tag_likelihood_square P f hf

lemma tagged_density_moment (P : Measure X) [IsFiniteMeasure P] (E : I→Set X)
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i)) (C : ℝ) (hC : 0≤C)
    (hbound : (∫⁻x,(∑i,f i x)^2 ∂P)≤ENNReal.ofReal C) :
    Integrable (fun p ↦ (f p.1 p.2).toReal^2) (taggedReference P E) ∧
      (∫p,(f p.1 p.2).toReal^2 ∂taggedReference P E)≤C := by
  let R := taggedReference P E
  let F : I×X→ℝ≥0∞ := fun p ↦ (f p.1 p.2)^2
  have hF : Measurable F := (taggedFunction_measurable f hf).pow_const 2
  have hb : (∫⁻p,F p ∂ R)≤ENNReal.ofReal C := (tagged_density_square P E f hf).trans hbound
  have hfin : (∫⁻p,F p ∂ R)≠⊤ := ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)
  have haef := ae_lt_top hF hfin
  have hi := integrable_toReal_of_lintegral_ne_top hF.aemeasurable hfin
  constructor
  · simpa only [F,ENNReal.toReal_pow] using hi
  · have he := integral_toReal hF.aemeasurable haef
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    rw [ENNReal.toReal_ofReal hC] at hh
    calc
      _ = (∫⁻p,F p ∂ R).toReal := by simpa only [F,ENNReal.toReal_pow] using he
      _ ≤ C := hh

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {Q X I : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma tagLikelihood_measurable (σ : Measure Q) [SFinite σ] (tag : Q→I)
    (ht : Measurable tag) (L : Q×X→ℝ≥0∞) (hL : Measurable L) (i : I) :
    Measurable (tagLikelihood σ tag L i) := by
  apply Measurable.lintegral_prod_left
  exact hL.ite (measurableSet_eq_fun (ht.comp measurable_fst) measurable_const) measurable_const

lemma sum_tagLikelihood (σ : Measure Q) (tag : Q→I) (ht : Measurable tag)
    (L : Q×X→ℝ≥0∞) (hL : Measurable L) (x : X) :
    (∑i,tagLikelihood σ tag L i x)=∫⁻q,L (q,x) ∂σ := by
  classical
  simp only [tagLikelihood]
  rw [←lintegral_finsetSum]
  · apply lintegral_congr
    intro q
    simp
  · intro i _
    exact (hL.comp measurable_prodMk_right).ite (measurableSet_eq_fun ht measurable_const) measurable_const

lemma tagged_mixture_density (σ : Measure Q) (P : Measure X) [SFinite σ] [SFinite P]
    (tag : Q→I) (ht : Measurable tag) (L : Q×X→ℝ≥0∞) (hL : Measurable L) :
    ((σ.prod P).withDensity L).map (fun p ↦ (tag p.1,p.2))=
      (Measure.count.prod P).withDensity (fun p ↦ tagLikelihood σ tag L p.1 p.2) := by
  classical
  let T : Q×X→I×X := fun p ↦ (tag p.1,p.2)
  have hm : Measurable T := (ht.comp measurable_fst).prodMk measurable_snd
  have hl : Measurable (fun p : I×X ↦ tagLikelihood σ tag L p.1 p.2) :=
    taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hm]
  change (∫⁻a,(F∘T) a ∂(σ.prod P).withDensity L)=_
  rw [lintegral_withDensity_eq_lintegral_mul _ hL (hF.comp hm),
    lintegral_withDensity_eq_lintegral_mul _ hl hF]
  rw [lintegral_prod _ (hl.mul hF).aemeasurable,lintegral_count,tsum_fintype]
  have hi (i : I) : (∫⁻x,tagLikelihood σ tag L i x*F (i,x) ∂P)=
      ∫⁻q,∫⁻x,(if tag q=i then L (q,x) else 0)*F (i,x) ∂P ∂σ := by
    unfold tagLikelihood
    have he (x : X) : (∫⁻q,if tag q=i then L (q,x) else 0 ∂σ)*F (i,x)=
        ∫⁻q,(if tag q=i then L (q,x) else 0)*F (i,x) ∂σ :=
      (lintegral_mul_const _ ((hL.comp measurable_prodMk_right).ite
        (measurableSet_eq_fun ht measurable_const) measurable_const)).symm
    simp_rw [he]
    apply lintegral_lintegral_swap
    exact (((hL.comp measurable_swap).ite
      (measurableSet_eq_fun (ht.comp measurable_snd) measurable_const) measurable_const).mul
      ((hF.comp measurable_prodMk_left).comp measurable_fst)).aemeasurable
  simp only [Pi.mul_apply,Function.comp_apply]
  simp_rw [hi]
  rw [←lintegral_finsetSum]
  · rw [lintegral_prod _ (show Measurable (fun p : Q×X ↦ L p*F (T p)) from hL.mul (hF.comp hm)).aemeasurable]
    apply lintegral_congr
    intro q
    rw [←lintegral_finsetSum]
    · apply lintegral_congr
      intro x
      simp [T]
    · intro i _
      exact (((hL.comp measurable_prodMk_left).ite (by measurability) measurable_const).mul
        (hF.comp measurable_prodMk_left))
  · intro i _
    exact (((hL.ite (measurableSet_eq_fun (ht.comp measurable_fst) measurable_const) measurable_const).mul
      ((hF.comp measurable_prodMk_left).comp measurable_snd))).lintegral_prod_right

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_TaggedObserved
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
variable {Q X I Y : Type*} [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Y]
attribute [local instance] Classical.propDecidable

lemma finite_density_of_square {Z : Type*} [MeasurableSpace Z]
    (P : Measure Z) [IsFiniteMeasure P] (f : Z→ℝ≥0∞) (_hf : Measurable f)
    (hf2 : (∫⁻x,(f x)^2 ∂ P)≠⊤) : IsFiniteMeasure (P.withDensity f) := by
  apply isFiniteMeasure_withDensity
  have hp (x : Z) : f x≤1+(f x)^2 := by
    by_cases h : f x≤1
    · exact h.trans (le_add_right le_rfl)
    · have h' : 1≤f x := le_of_not_ge h
      calc
        f x = f x*1 := (mul_one _).symm
        _ ≤ f x*f x := mul_le_mul' le_rfl h'
        _ ≤ 1+(f x)^2 := by rw [pow_two]; exact le_add_left le_rfl
  apply ne_of_lt ((lintegral_mono hp).trans_lt _)
  rw [lintegral_add_left measurable_const,lintegral_const]
  exact ENNReal.add_lt_top.mpr ⟨by simp [measure_lt_top],lt_top_iff_ne_top.mpr hf2⟩

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ConditionalTagDensity
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
attribute [local instance] Classical.propDecidable
variable {D Q X I : Type*} [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

lemma conditionalTagLikelihood_measurable (σ : Kernel D Q) [IsSFiniteKernel σ]
    (tag : Q→I) (ht : Measurable tag) (L : (D×Q)×X→ℝ≥0∞) (hL : Measurable L)
    (E : Set D) (hE : MeasurableSet E) (i : I) :
    Measurable (conditionalTagLikelihood σ tag L E i) := by
  apply Measurable.ite (hE.preimage measurable_fst) _ measurable_const
  exact (((hL.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).ite
    (measurableSet_eq_fun (ht.comp measurable_snd) measurable_const) measurable_const)).lintegral_kernel_prod_right'
      (κ:=σ.comap Prod.fst measurable_fst)

lemma conditionalTagLikelihood_sum (σ : Kernel D Q) (tag : Q→I) (ht : Measurable tag)
    (L : (D×Q)×X→ℝ≥0∞) (hL : Measurable L) (E : Set D) (z : D×X) :
    (∑i,conditionalTagLikelihood σ tag L E i z)=
      if z.1∈E then ∫⁻q,L ((z.1,q),z.2) ∂σ z.1 else 0 := by
  by_cases hz : z.1∈E
  · simp only [conditionalTagLikelihood,ite_eq_left hz]
    exact sum_tagLikelihood (σ z.1) tag ht _
      (hL.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) z.2
  · simp [conditionalTagLikelihood,hz]

lemma tagLikelihood_lintegral (σ : Measure Q) [SFinite σ] (P : Measure X) [SFinite P]
    (tag : Q→I) (ht : Measurable tag) (L : Q×X→ℝ≥0∞) (hL : Measurable L)
    (F : I×X→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻q,∫⁻x,L (q,x)*F (tag q,x) ∂P ∂σ)=
      ∑i,∫⁻x,tagLikelihood σ tag L i x*F (i,x) ∂P := by
  have H := congrArg (fun η : Measure (I×X) ↦ ∫⁻z,F z ∂η)
    (tagged_mixture_density σ P tag ht L hL)
  have hm : Measurable (fun p : Q×X ↦ (tag p.1,p.2)) := (ht.comp measurable_fst).prodMk measurable_snd
  rw [lintegral_map hF hm,
    lintegral_withDensity_eq_lintegral_mul _ hL
      (show Measurable (fun a : Q×X ↦ F (tag a.1,a.2)) from hF.comp hm),
    lintegral_withDensity_eq_lintegral_mul _
      (taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)) hF] at H
  rw [lintegral_prod _ ((taggedFunction_measurable _ (tagLikelihood_measurable σ tag ht L hL)).mul hF).aemeasurable,
    lintegral_count,tsum_fintype] at H
  simp only [Pi.mul_apply] at H
  rw [lintegral_prod _ (show Measurable (fun a : Q×X ↦ L a*F (tag a.1,a.2)) from hL.mul (hF.comp hm)).aemeasurable] at H
  exact H

theorem conditionalTagged_density (μ : Measure D) [SFinite μ]
    (σ : Kernel D Q) [IsSFiniteKernel σ] (P : Kernel D X) [IsSFiniteKernel P]
    (χ : Kernel (D×Q) X) [IsSFiniteKernel χ]
    (tag : Q→I) (ht : Measurable tag) (L : (D×Q)×X→ℝ≥0∞) (hL : Measurable L)
    (E : Set D) (hE : MeasurableSet E)
    (hd : ∀ᵐd ∂μ.restrict E,∀ᵐq ∂σ d,χ (d,q)=(P d).withDensity (fun x ↦ L ((d,q),x))) :
    (((μ.restrict E).compProd (σ⊗ₖχ)).map (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))))=
      (Measure.count.prod (μ.compProd P)).withDensity (fun z ↦ conditionalTagLikelihood σ tag L E z.1 z.2) := by
  let T : D×(Q×X)→I×(D×X) := fun z ↦ (tag z.2.1,(z.1,z.2.2))
  have hT : Measurable T := (ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd)
  have hf := taggedFunction_measurable _ (conditionalTagLikelihood_measurable σ tag ht L hL E hE)
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hT,
    lintegral_withDensity_eq_lintegral_mul _ hf hF,
    lintegral_prod _ (hf.mul hF).aemeasurable,lintegral_count,tsum_fintype,
    Measure.lintegral_compProd (show Measurable (fun a ↦ F (T a)) from hF.comp hT)]
  have hleft : (∫⁻d in E,∫⁻z,F (tag z.1,(d,z.2)) ∂(σ⊗ₖχ) d ∂μ)=
      ∫⁻d in E,∫⁻q,∫⁻x,L ((d,q),x)*F (tag q,(d,x)) ∂P d ∂σ d ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hd] with d hd'
    rw [Kernel.lintegral_compProd σ χ d (show Measurable (fun z : Q×X ↦ F (tag z.1,(d,z.2))) from hF.comp ((ht.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)))]
    apply lintegral_congr_ae
    filter_upwards [hd'] with q hq
    rw [hq,lintegral_withDensity_eq_lintegral_mul _ (show Measurable (fun x ↦ L ((d,q),x)) from hL.comp measurable_prodMk_left)
      (show Measurable (fun x ↦ F (tag q,(d,x))) from hF.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))]
    rfl
  change (∫⁻d in E,∫⁻z,F (tag z.1,(d,z.2)) ∂(σ⊗ₖχ) d ∂μ)=_
  rw [hleft]
  have hright (i : I) :
      (∫⁻z,conditionalTagLikelihood σ tag L E i z*F (i,z) ∂μ.compProd P)=
        ∫⁻d in E,∫⁻x,tagLikelihood (σ d) tag (fun qx ↦ L ((d,qx.1),qx.2)) i x*F (i,(d,x)) ∂P d ∂μ := by
    rw [Measure.lintegral_compProd (show Measurable (fun z : D×X ↦ conditionalTagLikelihood σ tag L E i z*F (i,z)) from
      (conditionalTagLikelihood_measurable σ tag ht L hL E hE i).mul (hF.comp measurable_prodMk_left))]
    rw [←lintegral_indicator hE]
    apply lintegral_congr
    intro d
    by_cases hd : d∈E <;> simp [conditionalTagLikelihood,hd,tagLikelihood]
  change _ = ∑i,∫⁻z,conditionalTagLikelihood σ tag L E i z*F (i,z) ∂μ.compProd P
  simp_rw [hright]
  rw [←lintegral_finsetSum]
  · apply lintegral_congr
    intro d
    exact tagLikelihood_lintegral (σ d) (P d) tag ht _
      (hL.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) _
      (hF.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  · intro i _
    have hm : Measurable (fun z : D×X ↦
        tagLikelihood (σ z.1) tag (fun qx ↦ L ((z.1,qx.1),qx.2)) i z.2) := by
      exact (((hL.comp ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)).ite
        (measurableSet_eq_fun (ht.comp measurable_snd) measurable_const) measurable_const)).lintegral_kernel_prod_right'
          (κ:=σ.comap Prod.fst measurable_fst)
    exact (hm.mul (hF.comp measurable_prodMk_left)).lintegral_kernel_prod_right

end HardSphere.Comparison
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {D Q X I Y : Type*} [MeasurableSpace D] [MeasurableSpace Q] [MeasurableSpace X]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace Y]

lemma tagged_density_of_ae_support (P : Measure X) (ν : Measure (I×X))
    (S : I→Set X) (hS : ∀i,MeasurableSet (S i)) (f : I→X→ℝ≥0∞)
    (hd : ν=(Measure.count.prod P).withDensity (fun p ↦ f p.1 p.2))
    (hs : ∀ᵐp ∂ν,p.2∈S p.1) :
    ν=(taggedReference P S).withDensity (fun p ↦ f p.1 p.2) := by
  rw [taggedReference,←restrict_withDensity (taggedEvent_measurable S hS),←hd]
  exact (Measure.restrict_eq_self_of_ae_mem hs).symm

lemma conditionalTagged_support (μ : Measure D) [SFinite μ]
    (σ : Kernel D Q) [IsSFiniteKernel σ] (χ : Kernel (D×Q) X) [IsSFiniteKernel χ]
    (tag : Q→I) (ht : Measurable tag) (E : Set D)
    (S : I→Set (D×X)) (hS : ∀i,MeasurableSet (S i))
    (hs : ∀ᵐd ∂μ.restrict E,∀ᵐq ∂σ d,∀ᵐw ∂χ (d,q),(d,w)∈S (tag q)) :
    ∀ᵐp ∂(((μ.restrict E).compProd (σ⊗ₖχ)).map (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2)))),p.2∈S p.1 := by
  have hm : Measurable (fun z : D×(Q×X) ↦ (tag z.2.1,(z.1,z.2.2))) :=
    (ht.comp measurable_snd.fst).prodMk (measurable_fst.prodMk measurable_snd.snd)
  rw [ae_map_iff hm.aemeasurable (taggedEvent_measurable S hS)]
  apply Measure.ae_compProd_of_ae_ae ((taggedEvent_measurable S hS).preimage hm)
  filter_upwards [hs] with d hd
  exact Kernel.ae_compProd_of_ae_ae ((taggedEvent_measurable S hS).preimage
    ((ht.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))) hd

theorem tagged_observed_of_density (P : Measure X) [IsFiniteMeasure P]
    (ν : Measure (I×X)) (S : I→Set X) (hS : ∀i,MeasurableSet (S i))
    (f : I→X→ℝ≥0∞) (hf : ∀i,Measurable (f i))
    (hd : ν=(Measure.count.prod P).withDensity (fun p ↦ f p.1 p.2))
    (hs : ∀ᵐp ∂ν,p.2∈S p.1) (κ : Kernel (I×X) Y) [IsMarkovKernel κ]
    (C : ℝ) (hC : 0≤C) (hb : (∫⁻x,(∑i,f i x)^2 ∂P)≤ENNReal.ofReal C) :
    Integrable (fun y ↦ (((ν.compProd κ).map Prod.snd).rnDeriv
      (((taggedReference P S).compProd κ).map Prod.snd) y).toReal^2)
        (((taggedReference P S).compProd κ).map Prod.snd) ∧
    (∫y,(((ν.compProd κ).map Prod.snd).rnDeriv
      (((taggedReference P S).compProd κ).map Prod.snd) y).toReal^2
        ∂((taggedReference P S).compProd κ).map Prod.snd)≤C := by
  have he := tagged_density_of_ae_support P ν S hS f hd hs
  rw [he]
  let R := taggedReference P S
  let F : I×X→ℝ≥0∞ := fun p ↦ f p.1 p.2
  have hF : Measurable F := taggedFunction_measurable f hf
  let _ : IsFiniteMeasure R := by dsimp [R,taggedReference]; infer_instance
  have hm := tagged_density_moment P S f hf C hC hb
  have hsq : (∫⁻p,(F p)^2 ∂ R)≤ENNReal.ofReal C := (tagged_density_square P S f hf).trans hb
  let _ : IsFiniteMeasure (R.withDensity F) :=
    finite_density_of_square R F hF (ne_of_lt (hsq.trans_lt ENNReal.ofReal_lt_top))
  have hae : (fun p ↦ ((R.withDensity F).rnDeriv R p).toReal^2)=ᵐ[R]
      (fun p ↦ (F p).toReal^2) :=
    (Measure.rnDeriv_withDensity R hF).fun_comp (fun x : ℝ≥0∞ ↦ x.toReal^2)
  have h := observed_kernel_second_moment R (R.withDensity F)
    (withDensity_absolutelyContinuous _ _) κ (hm.1.congr hae.symm)
  refine ⟨h.1,h.2.trans ?_⟩
  rw [integral_congr_ae hae]
  exact hm.2

end HardSphere.Comparison
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalTaggedDensity
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalTagLikelihood_measurable {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsSFiniteKernel ν]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E) (i : Fin (N+1)) :
    Measurable (physicalTagLikelihood hL g m t r R C S u particle hxy b ν E i) :=
  conditionalTagLikelihood_measurable _ _ (measurable_of_countable _) _
    (physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b) E hE i

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma physicalTagLikelihood_sum {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin (N+1))
    (hxy : x≠y) (b : Bool)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y))
    (E : Set (PhysicalDatum (N+1) K M G L))
    (z : PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point))) :
    (∑i,physicalTagLikelihood hL g m t r R C S u particle hxy b ν E i z)=
      physicalGoodLikelihood hL g m t r R C S u particle hxy b ν E z := by
  exact conditionalTagLikelihood_sum _ _ (measurable_of_countable _) _
    (physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b) E z

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalTaggedMixture_density_support {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)))
    (b : Bool) :
    physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E =
      (Measure.count.prod (μ.compProd (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x))))).withDensity
        (fun z ↦ physicalTagLikelihood hL g m t r R C S u particle hxy b ν E z.1 z.2) ∧
    (∀ᵐz ∂physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E,
      z.2∈physicalTagEvent particle (siteIndex (if b then x else y)) z.1) := by
  have hb : Measurable (if b then (Prod.fst : ((Option J→C(Time,Point))×(Option J→C(Time,Point)))→_) else Prod.snd) := by
    cases b <;> simp <;> fun_prop
  have hd : ∀ᵐd ∂μ.restrict E,∀ᵐc ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d,
      physicalRouteView hL g m t r R C S u particle hxy b (d,c)=
        (physicalPrimaryReference hL g m t r R C S u particle (siteIndex (if b then y else x)) d).withDensity
          (physicalRouteLikelihood hL g m t r R C S u particle hxy b (d,c)) := by
    filter_upwards [hdata] with d hd
    rw [Kernel.prod_apply]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
    filter_upwards [hd.1] with p hp
    filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
    simpa only [physicalRouteView,Kernel.map_apply _ hb,physicalRouteFamily,Kernel.coe_mk] using
      (physicalCoded_density hL g m t r R C S ht hr u particle d hxy p z hz hp hd.2 b).symm
  constructor
  · exact conditionalTagged_density μ _ _ _ _ (measurable_of_countable _) _
      (physicalRouteLikelihood_measurable hL g m t r R C S u particle hxy b) E hE hd
  · apply conditionalTagged_support μ _ _ _ (measurable_of_countable _) E _
      (physicalTagEvent_measurable particle (siteIndex (if b then x else y)))
    filter_upwards [hdata] with d hd
    rw [Kernel.prod_apply]
    apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
    filter_upwards [hd.1] with p hp
    filter_upwards [physicalLabels_supported hL g m t r R C S u particle d] with z hz
    simp only [physicalRouteView,Kernel.map_apply _ hb,physicalRouteFamily,Kernel.coe_mk]
    rw [ae_map_iff hb.aemeasurable ((physicalTagEvent_measurable particle _ _).preimage measurable_prodMk_left)]
    have H := physicalCodedRoute_tag_support hL g m t r R C S ht hr u particle d hxy p z hz hp hd.2 b
    cases b <;> simpa using H

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem physicalTagged_observed_moment_oai {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath)
    (b : Bool) {Y : Type*} [MeasurableSpace Y]
    (obs : Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))) Y)
    [IsMarkovKernel obs] :
    Integrable (fun z ↦ ((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2)
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) ∧
    (∫z,((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2
      ∂((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd)≤B*Cpath := by
  have ha : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) := by
    filter_upwards [hdata] with d hd
    refine ⟨?_,hd.2.2.1⟩
    filter_upwards [hd.1] with p hp
    intro i
    apply Finset.card_pos.mp
    have H := hp _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    have hM' : (0:ℝ)<M := by exact_mod_cast hM
    have H' : (0:ℝ)<(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).card := by linarith
    exact_mod_cast H'
  have hd := physicalTaggedMixture_density_support hL g m t r R C S ht hr u particle hxy ν μ E hE ha b
  apply tagged_observed_of_density _ _ _ (physicalTagEvent_measurable particle _)
    _ (physicalTagLikelihood_measurable hL g m t r R C S u particle hxy b ν E hE)
    hd.1 hd.2 obs (B*Cpath) (mul_nonneg (le_trans zero_le_one hB) hCpath)
  simp_rw [physicalTagLikelihood_sum]
  rw [ENNReal.ofReal_mul (le_trans zero_le_one hB)]
  exact physicalGoodLikelihood_moment hL g m t r R C S ht hr u particle hxy ν μ E hE
    hM q δ B κ Cpath hδ hB hBt hκ hsmall hdata henc b

end HardSphere.Groups
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HardSphere.Groups.physicalTagged_observed_moment_oai.{u_1, u_2} := @OAI.HardSphere.Groups.physicalTagged_observed_moment_oai.{u_1, u_2}
