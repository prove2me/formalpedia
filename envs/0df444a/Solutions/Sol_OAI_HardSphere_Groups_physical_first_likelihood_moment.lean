-- Prove2me | solution 1 for OAI.HardSphere.Groups.physical_first_likelihood_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T20:18:33.457679+00:00
-- url     : https://prove2.me/submissions/39a230db-1ccd-4a29-9636-c99b633e3a09

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002
import Theorems.Thm_OAI_HardSphere_Groups_PhysicalRouteAux_path_bounds

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
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_BridgeReference
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
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

lemma densityLower_pos {b : ℝ} (hb : 0<b) (C : ℝ) : 0<densityLower b C := by
  unfold densityLower
  exact mul_pos (pow_pos (Real.sqrt_pos.mpr (div_pos hb Real.pi_pos)) _) (Real.exp_pos _)

end HardSphere.GaussianPacking

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_LocalReference
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
open scoped ENNReal NNReal Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison

lemma midpointLower_pos {t : ℝ} (ht : 0<t) (C : ℝ) : 0 < midpointLower t C :=
  ENNReal.ofReal_pos.mpr (densityLower_pos (by positivity) C)

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

lemma measurableSet_insertionEvent (s : Finset ι) (i : ι) :
    MeasurableSet (insertionEvent checks s i) := by
  classical
  have heq : insertionEvent checks s i =
      ⋂ c, if (checks c).support ⊆ insert i s ∧ ¬ (checks c).support ⊆ s then
        {x | (checks c).pass x} else Set.univ := by
    ext x
    simp [insertionEvent, and_imp]
  rw [heq]
  apply MeasurableSet.iInter
  intro c
  split_ifs
  · exact (checks c).measurable_pass
  · exact MeasurableSet.univ

omit [Fintype C] in
lemma retainedEvent_insert (s : Finset ι) (i : ι) :
    retainedEvent checks (insert i s) =
      retainedEvent checks s ∩ insertionEvent checks s i := by
  classical
  ext x
  constructor
  · intro h
    exact ⟨fun c hc ↦ h c (hc.trans (Finset.subset_insert _ _)), fun c hc _ ↦ h c hc⟩
  · rintro ⟨hs, hi⟩ c hc
    by_cases hold : (checks c).support ⊆ s
    · exact hs c hold
    · exact hi c hc hold

omit [Fintype C] in
lemma retainedEvent_update {s : Finset ι} {i : ι} (hi : i ∉ s)
    (x : ∀ j, X j) (y : X i) :
    Function.update x i y ∈ retainedEvent checks s ↔ x ∈ retainedEvent checks s := by
  apply forall_congr'
  intro c
  apply imp_congr_right
  intro hc
  apply (checks c).depends
  intro j hj
  exact Function.update_of_ne (ne_of_mem_of_not_mem (hc hj) hi) y x

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

omit [Fintype C] in
lemma checkNormalizer_const {μ : ∀ i, Measure (X i)} (s : Finset ι)
    (x y : ∀ i, X i) : checkNormalizer checks μ s x = checkNormalizer checks μ s y := by
  apply lintegral_congr
  intro z
  apply checkWeight_depends
  intro i hi
  simp [Function.updateFinset, hi]

omit [Fintype C] in
lemma checkNormalizer_le_one {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset ι) (x : ∀ i, X i) : checkNormalizer checks μ s x ≤ 1 := by
  calc
    checkNormalizer checks μ s x ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂Measure.pi (fun i : s ↦ μ i) :=
      lintegral_mono fun _ ↦ checkWeight_le_one checks _ _
    _ = 1 := by simp

omit [DecidableEq ι] [Fintype C] in
lemma checkWeight_antitone {s t : Finset ι} (hst : s ⊆ t) :
    checkWeight checks t ≤ checkWeight checks s := by
  classical
  intro x
  by_cases ht : x ∈ retainedEvent checks t
  · have hs : x ∈ retainedEvent checks s := fun c hc ↦ ht c (hc.trans hst)
    simp [checkWeight, ht, hs]
  · simp [checkWeight, ht]

omit [Fintype C] in
lemma checkWeight_union {s t : Finset ι} (hsep : SeparatedChecks checks s t)
    (x : ∀ i, X i) :
    checkWeight checks (s ∪ t) x = checkWeight checks s x * checkWeight checks t x := by
  classical
  have hevent : x ∈ retainedEvent checks (s ∪ t) ↔
      x ∈ retainedEvent checks s ∧ x ∈ retainedEvent checks t := by
    constructor
    · intro h
      exact ⟨fun c hc ↦ h c (hc.trans Finset.subset_union_left),
        fun c hc ↦ h c (hc.trans Finset.subset_union_right)⟩
    · rintro ⟨hs, ht⟩ c hc
      exact (hsep c hc).elim (hs c) (ht c)
  simp only [checkWeight, Set.indicator_apply, hevent]
  split_ifs <;> simp_all

lemma checkNormalizer_union_eq_mul {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s t : Finset ι} (hst : Disjoint s t) (hsep : SeparatedChecks checks s t)
    (x : ∀ i, X i) :
    checkNormalizer checks μ (s ∪ t) x =
      checkNormalizer checks μ s x * checkNormalizer checks μ t x := by
  have hin : ∀ y, lmarginal μ t
      (fun y ↦ checkWeight checks s y * checkWeight checks t y) y =
      checkWeight checks s y * checkNormalizer checks μ t y := by
    intro y
    simp only [lmarginal, checkNormalizer]
    have hu : ∀ z : ∀ i : t, X i,
        checkWeight checks s (Function.updateFinset y t z) = checkWeight checks s y := by
      intro z
      apply checkWeight_depends
      intro i hi
      have hit : i ∉ t := Finset.disjoint_left.mp hst hi
      simp [Function.updateFinset, hit]
    simp_rw [hu]
    exact lintegral_const_mul _ ((measurable_checkWeight checks t).comp
      (measurable_updateFinset (x := y) (s := t)))
  rw [checkNormalizer, show checkWeight checks (s ∪ t) =
    (fun y ↦ checkWeight checks s y * checkWeight checks t y) from
      funext (checkWeight_union checks hsep)]
  rw [lmarginal_union μ (fun y ↦ checkWeight checks s y * checkWeight checks t y)
    ((measurable_checkWeight checks s).mul (measurable_checkWeight checks t)) hst]
  simp_rw [show lmarginal μ t (fun y ↦ checkWeight checks s y * checkWeight checks t y) =
    (fun y ↦ checkWeight checks s y * checkNormalizer checks μ t y) from funext hin]
  simp only [lmarginal]
  simp_rw [checkNormalizer_const checks t _ x]
  exact lintegral_mul_const _ ((measurable_checkWeight checks s).comp
    (measurable_updateFinset (x := x) (s := s)))

omit [Fintype C] in
lemma lmarginal_eq_const_of_depends {μ : ∀ i, Measure (X i)}
    {s : Finset ι} {f : (∀ i, X i) → ℝ≥0∞}
    (hf : DependsOn f (s : Set ι)) (x y : ∀ i, X i) :
    lmarginal μ s f x = lmarginal μ s f y := by
  apply lintegral_congr
  intro z
  apply hf
  intro i hi
  change i ∈ s at hi
  simp [Function.updateFinset, hi]

omit [Fintype C] in
lemma lmarginal_mul_disjoint {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s t : Finset ι} (hst : Disjoint s t) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfs : DependsOn f (s : Set ι)) (hgt : DependsOn g (t : Set ι))
    (x : ∀ i, X i) :
    lmarginal μ (s ∪ t) (fun y ↦ f y * g y) x =
      lmarginal μ s f x * lmarginal μ t g x := by
  have hin : ∀ y, lmarginal μ t (fun y ↦ f y * g y) y =
      f y * lmarginal μ t g y := by
    intro y
    simp only [lmarginal]
    have hu : ∀ z : ∀ i : t, X i, f (Function.updateFinset y t z) = f y := by
      intro z
      apply hfs
      intro i hi
      have hit : i ∉ t := Finset.disjoint_left.mp hst hi
      simp [Function.updateFinset, hit]
    simp_rw [hu]
    exact lintegral_const_mul _ (hg.comp (measurable_updateFinset (x := y) (s := t)))
  rw [lmarginal_union μ (fun y ↦ f y * g y) (hf.mul hg) hst]
  simp_rw [show lmarginal μ t (fun y ↦ f y * g y) =
    (fun y ↦ f y * lmarginal μ t g y) from funext hin]
  change (∫⁻ y, f (Function.updateFinset x s y) *
    lmarginal μ t g (Function.updateFinset x s y)
    ∂Measure.pi (fun i : s ↦ μ i)) = _
  simp_rw [lmarginal_eq_const_of_depends hgt _ x]
  exact lintegral_mul_const _ (hf.comp (measurable_updateFinset (x := x) (s := s)))

omit [Fintype C] in
lemma lmarginal_prod_coordinates {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (g : ∀ i, X i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (s : Finset ι) (x : ∀ i, X i) :
    lmarginal μ s (fun y ↦ ∏ i ∈ s, g i (y i)) x =
      ∏ i ∈ s, ∫⁻ y, g i y ∂μ i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm (s : Finset ι) : Measurable (fun y : ∀ i, X i ↦ ∏ i ∈ s, g i (y i)) :=
      Finset.measurable_prod s fun i _ ↦ (hg i).comp (measurable_pi_apply i)
    have hs : DependsOn (fun y : ∀ i, X i ↦ ∏ i ∈ s, g i (y i)) (s : Set ι) := by
      intro y z hyz
      exact Finset.prod_congr rfl fun i hi ↦ congrArg (g i) (hyz i hi)
    have hu : (insert i s : Finset ι) = {i} ∪ s := by simp
    simp only [Finset.prod_insert hi]
    rw [hu, lmarginal_mul_disjoint (μ := μ)
      (f := fun y ↦ g i (y i)) (g := fun y ↦ ∏ i ∈ s, g i (y i))
      (Finset.disjoint_singleton_left.mpr hi)
      ((hg i).comp (measurable_pi_apply i)) (hm s)
      (by intro y z hyz; exact congrArg (g i) (hyz i (by simp))) hs x]
    rw [ih, lmarginal_singleton]
    simp

lemma checkNormalizer_delete_le {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s t : Finset ι} (hst : Disjoint s t) (x : ∀ i, X i) :
    checkNormalizer checks μ (s ∪ t) x ≤
      checkNormalizer checks μ s x * ∏ i ∈ t, μ i Set.univ := by
  calc
    checkNormalizer checks μ (s ∪ t) x ≤ lmarginal μ (s ∪ t) (checkWeight checks s) x :=
      lmarginal_mono (checkWeight_antitone checks Finset.subset_union_left) x
    _ = checkNormalizer checks μ s x * ∏ i ∈ t, μ i Set.univ := by
      rw [lmarginal_union' μ _ (measurable_checkWeight checks s) hst]
      change (∫⁻ y, checkNormalizer checks μ s (Function.updateFinset x t y)
        ∂Measure.pi (fun i : t ↦ μ i)) = _
      simp_rw [checkNormalizer_const checks s _ x]
      rw [lintegral_const]
      rw [Measure.pi_univ]
      exact congrArg (checkNormalizer checks μ s x * ·)
        (Finset.prod_coe_sort t (fun i ↦ μ i Set.univ))

end HardSphere.Comparison

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

section AuxiliaryMarginals
variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

omit [DecidableEq ι] [Fintype C] in
lemma auxiliary_checkWeight (s : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) :
    checkWeight (auxiliaryChecks checks x) s z =
      checkWeight checks s (fun i ↦ (x i,z i)) := rfl

lemma auxiliaryDensity_delete_le {s t : Finset ι} (hst : Disjoint s t)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    auxiliaryDensity checks κ (s ∪ t) x z ≤
      auxiliaryDensity checks κ s x z * ∏ i ∈ t, κ i (x i) Set.univ :=
  checkNormalizer_delete_le (auxiliaryChecks checks x) hst z

omit [Fintype C] [∀ i, IsFiniteKernel (κ i)] in
lemma auxiliaryDensity_depends (s : Finset ι) (z : ∀ i, Z i) :
    DependsOn (fun x ↦ auxiliaryDensity checks κ s x z) (s : Set ι) := by
  intro x y hxy
  have hμ : (fun i : s ↦ κ i (x i)) = (fun i : s ↦ κ i (y i)) := by
    funext i
    rw [hxy i i.property]
  change (∫⁻ u, checkWeight (auxiliaryChecks checks x) s
    (Function.updateFinset z s u) ∂Measure.pi (fun i : s ↦ κ i (x i))) = _
  rw [hμ]
  apply lintegral_congr
  intro u
  simp only [auxiliary_checkWeight]
  apply checkWeight_depends
  intro i hi
  exact Prod.ext (hxy i hi) rfl

lemma measurable_auxiliaryDensity (s : Finset ι) (z : ∀ i, Z i) :
    Measurable (fun x ↦ auxiliaryDensity checks κ s x z) := by
  let κ' (i : s) : Kernel (∀ j, X j) (Z i) :=
    (κ i).comap (fun x ↦ x i) (measurable_pi_apply (i : ι))
  let η := finiteKernelPi κ'
  have hm : Measurable (fun p : (∀ i, X i) × (∀ i : s, Z i) ↦
      checkWeight checks s (fun i ↦ (p.1 i, Function.updateFinset z s p.2 i))) := by
    apply (measurable_checkWeight checks s).comp
    exact Measurable.of_eval fun i ↦
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp ((measurable_updateFinset (x := z) (s := s)).comp
          measurable_snd))
  have h := hm.lintegral_kernel_prod_right' (κ := η)
  simpa only [η, finiteKernelPi_apply, κ', Kernel.comap_apply,
    auxiliaryDensity, checkNormalizer, lmarginal, auxiliary_checkWeight] using h

lemma auxiliaryDensity_integral (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)]
    (s : Finset ι) (x : ∀ i, X i) (z : ∀ i, Z i) :
    lmarginal μ s (fun y ↦ auxiliaryDensity checks κ s y z) x =
      checkNormalizer checks (fun i ↦ (μ i).compProd (κ i)) s (fun i ↦ (x i,z i)) := by
  let f (p : ∀ i : s, X i × Z i) :=
    checkWeight checks s (Function.updateFinset (fun i ↦ (x i,z i)) s p)
  have hf : Measurable f := (measurable_checkWeight checks s).comp measurable_updateFinset
  have hh := lintegral_pi_compProd (fun i : s ↦ κ i) (fun i : s ↦ μ i) hf
  change (∫⁻ y, auxiliaryDensity checks κ s (Function.updateFinset x s y) z
    ∂Measure.pi (fun i : s ↦ μ i)) = (∫⁻ p, f p ∂Measure.pi (fun i : s ↦ (μ i).compProd (κ i)))
  rw [hh]
  apply lintegral_congr
  intro y
  change (∫⁻ u, checkWeight (auxiliaryChecks checks (Function.updateFinset x s y)) s
    (Function.updateFinset z s u)
    ∂Measure.pi (fun i : s ↦ κ i (Function.updateFinset x s y i))) = _
  have hμ : (fun i : s ↦ κ i (Function.updateFinset x s y i)) = (fun i : s ↦ κ i (y i)) := by
    funext i
    simp [Function.updateFinset, i.property]
  rw [hμ]
  apply lintegral_congr
  intro u
  rw [auxiliary_checkWeight]
  apply checkWeight_depends
  intro i hi
  simp [Function.updateFinset, hi]

end AuxiliaryMarginals

section OverlapProducts
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)]

omit [DecidableEq ι] in
lemma measurable_densityProduct (s : Finset ι) (g : ∀ i, X i → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) : Measurable (densityProduct s g) :=
  Finset.measurable_prod s fun i _ ↦ (hg i).comp (measurable_pi_apply i)

omit [DecidableEq ι] [∀ i, MeasurableSpace (X i)] in
lemma densityProduct_depends (s : Finset ι) (g : ∀ i, X i → ℝ≥0∞) :
    DependsOn (densityProduct s g) (s : Set ι) := by
  intro x y hxy
  exact Finset.prod_congr rfl fun i hi ↦ congrArg (g i) (hxy i hi)

omit [∀ i, MeasurableSpace (X i)] in
lemma densityProduct_union (s t : Finset ι) (g h : ∀ i, X i → ℝ≥0∞)
    (x : ∀ i, X i) :
    densityProduct s g x * densityProduct t h x =
      ∏ i ∈ s ∪ t, (if i ∈ s then g i (x i) else 1) *
        (if i ∈ t then h i (x i) else 1) := by
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    simp only [Finset.filter_mem_eq_inter, Finset.union_inter_cancel_left, densityProduct]
  · rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
    simp only [Finset.filter_mem_eq_inter, Finset.union_inter_cancel_right, densityProduct]

lemma lmarginal_overlap_products {μ : ∀ i, Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] (s t : Finset ι)
    (g h : ∀ i, X i → ℝ≥0∞) (hg : ∀ i, Measurable (g i))
    (hh : ∀ i, Measurable (h i)) {G : ℝ≥0∞}
    (hgb : ∀ i x, g i x ≤ G)
    (hgm : ∀ i, ∫⁻ x, g i x ∂μ i = 1)
    (hhm : ∀ i, ∫⁻ x, h i x ∂μ i = 1) (x : ∀ i, X i) :
    lmarginal μ (s ∪ t) (fun y ↦ densityProduct s g y * densityProduct t h y) x ≤
      G ^ (s ∩ t).card := by
  let f (i : ι) (y : X i) :=
    (if i ∈ s then g i y else 1) * (if i ∈ t then h i y else 1)
  have hf : ∀ i, Measurable (f i) := by
    intro i
    dsimp [f]
    split_ifs <;> fun_prop
  rw [show (fun y ↦ densityProduct s g y * densityProduct t h y) =
      (fun y ↦ ∏ i ∈ s ∪ t, f i (y i)) from funext (densityProduct_union s t g h)]
  rw [lmarginal_prod_coordinates f hf]
  have hi (i : ι) : (∫⁻ y, f i y ∂μ i) ≤ if i ∈ s ∩ t then G else 1 := by
    by_cases his : i ∈ s <;> by_cases hit : i ∈ t
    · simp only [f, his, hit, ite_true, Finset.mem_inter, and_self]
      calc
        (∫⁻ y, g i y * h i y ∂μ i) ≤ ∫⁻ y, G * h i y ∂μ i :=
          lintegral_mono fun y ↦ mul_le_mul_left (hgb i y) _
        _ = G := by rw [lintegral_const_mul _ (hh i), hhm, mul_one]
    all_goals simp [f, his, hit, hgm, hhm]
  calc
    (∏ i ∈ s ∪ t, ∫⁻ y, f i y ∂μ i) ≤
        ∏ i ∈ s ∪ t, if i ∈ s ∩ t then G else 1 :=
      Finset.prod_le_prod' fun i _ ↦ hi i
    _ = G ^ (s ∩ t).card := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one]
      have heq : (s ∪ t).filter (fun i ↦ i ∈ s ∩ t) = s ∩ t := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
        tauto
      rw [heq, Finset.prod_const]

omit [∀ i, MeasurableSpace (X i)] in
lemma dependsOn_mul_union {s t : Finset ι} {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : DependsOn f (s : Set ι)) (hg : DependsOn g (t : Set ι)) :
    DependsOn (fun x ↦ f x * g x) ((s ∪ t : Finset ι) : Set ι) := by
  intro x y hxy
  change f x * g x = f y * g y
  rw [hf (fun i hi ↦ hxy i (Finset.mem_union_left t hi)),
    hg (fun i hi ↦ hxy i (Finset.mem_union_right s hi))]

end OverlapProducts

section KernelOverlap
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {C D : Type*} [Fintype C] [Fintype D]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

lemma auxiliaryDensity_overlap_bound
    {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (fs ft cs ct : Finset ι)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs ∪ ft) (cs ∪ ct))
    {G : ℝ≥0∞}
    (hκb : ∀ i x, κ i x Set.univ ≤ G)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hηm : ∀ i, ∫⁻ x, η i x Set.univ ∂μ i = 1)
    (x : ∀ i, X i) (z : ∀ i, Z i) (w : ∀ i, W i) :
    lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct))
      (fun y ↦ auxiliaryDensity checks κ (fs ∪ cs) y z *
        auxiliaryDensity other η (ft ∪ ct) y w) x ≤
      (checkNormalizer checks (fun i ↦ (μ i).compProd (κ i)) fs (fun i ↦ (x i,z i)) *
       checkNormalizer other (fun i ↦ (μ i).compProd (η i)) ft (fun i ↦ (x i,w i))) *
       G ^ (cs ∩ ct).card := by
  let g (i : ι) (y : X i) := κ i y Set.univ
  let h (i : ι) (y : X i) := η i y Set.univ
  have hg : ∀ i, Measurable (g i) := fun i ↦ (κ i).measurable_coe MeasurableSet.univ
  have hh : ∀ i, Measurable (h i) := fun i ↦ (η i).measurable_coe MeasurableSet.univ
  have hfs : Disjoint fs cs := hfn.mono Finset.subset_union_left Finset.subset_union_left
  have hft : Disjoint ft ct := hfn.mono Finset.subset_union_right Finset.subset_union_right
  let F (y : ∀ i, X i) := auxiliaryDensity checks κ fs y z
  let H (y : ∀ i, X i) := auxiliaryDensity other η ft y w
  let P (y : ∀ i, X i) := densityProduct cs g y * densityProduct ct h y
  have hF : Measurable F := measurable_auxiliaryDensity checks κ fs z
  have hH : Measurable H := measurable_auxiliaryDensity other η ft w
  have hP : Measurable P := (measurable_densityProduct cs g hg).mul
    (measurable_densityProduct ct h hh)
  have hFd : DependsOn F (fs : Set ι) := auxiliaryDensity_depends checks κ fs z
  have hHd : DependsOn H (ft : Set ι) := auxiliaryDensity_depends other η ft w
  have hPd : DependsOn P ((cs ∪ ct : Finset ι) : Set ι) :=
    dependsOn_mul_union (densityProduct_depends cs g) (densityProduct_depends ct h)
  calc
    _ ≤ lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct)) (fun y ↦ (F y * H y) * P y) x := by
      apply lmarginal_mono _ x
      intro y
      calc
        _ ≤ (F y * densityProduct cs g y) * (H y * densityProduct ct h y) :=
          mul_le_mul' (auxiliaryDensity_delete_le checks κ hfs y z)
            (auxiliaryDensity_delete_le other η hft y w)
        _ = _ := by dsimp [P]; ac_rfl
    _ = (lmarginal μ fs F x * lmarginal μ ft H x) * lmarginal μ (cs ∪ ct) P x := by
      rw [lmarginal_mul_disjoint (f := fun y ↦ F y * H y) (g := P) hfn
        (hF.mul hH) hP (dependsOn_mul_union hFd hHd) hPd,
        lmarginal_mul_disjoint (f := F) (g := H) hff hF hH hFd hHd]
    _ ≤ (lmarginal μ fs F x * lmarginal μ ft H x) * G ^ (cs ∩ ct).card :=
      mul_le_mul_right (lmarginal_overlap_products cs ct g h hg hh hκb hκm hηm x) _
    _ = _ := by rw [auxiliaryDensity_integral, auxiliaryDensity_integral]

end KernelOverlap

section ConditionalNormalizers
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)

omit [Fintype C] in
lemma insertion_integral_lower_on {μ : ∀ i, Measure (X i)} {a : ℝ≥0∞}
    {r : Finset ι} (hcompat : UniformInsertionOn checks μ a r)
    {s : Finset ι} {i : ι} (hir : i ∈ r) (hi : i ∉ s) (x : ∀ i, X i) :
    a * checkWeight checks s x ≤
      ∫⁻ y, checkWeight checks (insert i s) (Function.update x i y) ∂μ i := by
  classical
  by_cases hx : x ∈ retainedEvent checks s
  · have heq : (fun y ↦ checkWeight checks (insert i s) (Function.update x i y)) =
        fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞))
          (Function.update x i y) := by
      funext y
      have hu := (retainedEvent_update checks hi x y).2 hx
      simp [checkWeight, retainedEvent_insert, Set.indicator_apply, hu]
    rw [heq]
    simpa [checkWeight, hx] using hcompat i hir s hi x
  · simp [checkWeight, hx]

lemma partialNormalizer_insert_lower {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {a : ℝ≥0∞} {r : Finset ι}
    (hcompat : UniformInsertionOn checks μ a r) {s o : Finset ι} {i : ι}
    (hir : i ∈ r) (hi : i ∉ s ∪ o) (x : ∀ i, X i) :
    a * partialNormalizer checks μ s o x ≤
      partialNormalizer checks μ (insert i s) o x := by
  have his : i ∉ s := fun h ↦ hi (Finset.mem_union_left o h)
  rw [partialNormalizer, partialNormalizer, Finset.insert_union,
    lmarginal_insert' _ (measurable_checkWeight checks _) his]
  calc
    a * lmarginal μ s (checkWeight checks (s ∪ o)) x =
        lmarginal μ s (fun x ↦ a * checkWeight checks (s ∪ o) x) x := by
      dsimp [lmarginal]
      exact (lintegral_const_mul a ((measurable_checkWeight checks (s ∪ o)).comp
        (measurable_updateFinset (x := x) (s := s)))).symm
    _ ≤ _ := lmarginal_mono (insertion_integral_lower_on checks hcompat hir hi) x

lemma partialNormalizer_union_lower {μ : ∀ i, Measure (X i)}
    [∀ i, SigmaFinite (μ i)] {a : ℝ≥0∞} {r : Finset ι}
    (hcompat : UniformInsertionOn checks μ a r)
    (s t o : Finset ι) (htr : t ⊆ r) (hto : Disjoint (s ∪ o) t)
    (x : ∀ i, X i) :
    a ^ t.card * partialNormalizer checks μ s o x ≤
      partialNormalizer checks μ (s ∪ t) o x := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hit ih =>
    have hino : i ∉ s ∪ o := (Finset.disjoint_insert_right.mp hto).1
    have hto' := (Finset.disjoint_insert_right.mp hto).2
    have hiu : i ∉ (s ∪ t) ∪ o := by
      simp only [Finset.mem_union, not_or] at hino ⊢
      exact ⟨⟨hino.1, hit⟩, hino.2⟩
    calc
      a ^ (insert i t).card * partialNormalizer checks μ s o x =
          a * (a ^ t.card * partialNormalizer checks μ s o x) := by
        rw [Finset.card_insert_of_notMem hit, pow_succ]
        ac_rfl
      _ ≤ a * partialNormalizer checks μ (s ∪ t) o x :=
        mul_le_mul_right (ih ((Finset.subset_insert _ _).trans htr) hto') a
      _ ≤ partialNormalizer checks μ (insert i (s ∪ t)) o x :=
        partialNormalizer_insert_lower checks hcompat (htr (Finset.mem_insert_self _ _)) hiu x
      _ = _ := by rw [Finset.union_insert]

lemma partialNormalizer_pos {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (ha : 0 < a) {s o : Finset ι}
    (hcompat : UniformInsertionOn checks μ a s) (hso : Disjoint s o)
    (x : ∀ i, X i) (hx : x ∈ retainedEvent checks o) :
    0 < partialNormalizer checks μ s o x := by
  have h := partialNormalizer_union_lower checks hcompat ∅ s o (Finset.Subset.refl s)
    (by simpa using hso.symm) x
  simp only [partialNormalizer, Finset.empty_union, lmarginal_empty, checkWeight,
    Set.indicator_of_mem hx, mul_one] at h
  exact lt_of_lt_of_le (by positivity) h

lemma partialNormalizer_far_eq {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {s o : Finset ι} (hso : Disjoint s o) (hsep : SeparatedChecks checks s o)
    (x : ∀ i, X i) :
    partialNormalizer checks μ s o x = checkNormalizer checks μ s x * checkWeight checks o x := by
  rw [partialNormalizer]
  have heq : checkWeight checks (s ∪ o) = fun y ↦ checkWeight checks s y * checkWeight checks o y :=
    funext (checkWeight_union checks hsep)
  rw [heq]
  change (∫⁻ y, checkWeight checks s (Function.updateFinset x s y) *
    checkWeight checks o (Function.updateFinset x s y) ∂Measure.pi (fun i : s ↦ μ i)) = _
  have hu : ∀ y : ∀ i : s, X i,
      checkWeight checks o (Function.updateFinset x s y) = checkWeight checks o x := by
    intro y
    apply checkWeight_depends
    intro i hi
    have his : i ∉ s := Finset.disjoint_right.mp hso hi
    simp [Function.updateFinset, his]
  simp_rw [hu]
  exact lintegral_mul_const _ ((measurable_checkWeight checks s).comp
    (measurable_updateFinset (x := x) (s := s)))

lemma partialNormalizer_le_far {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    {s t o : Finset ι} (hst : Disjoint s t) (x : ∀ i, X i) :
    partialNormalizer checks μ (s ∪ t) o x ≤ checkNormalizer checks μ s x := by
  calc
    _ ≤ lmarginal μ (s ∪ t) (checkWeight checks s) x :=
      lmarginal_mono (checkWeight_antitone checks
        (Finset.subset_union_left.trans Finset.subset_union_left)) x
    _ = _ := by
      rw [lmarginal_union' μ _ (measurable_checkWeight checks s) hst]
      change (∫⁻ y, checkNormalizer checks μ s (Function.updateFinset x t y)
        ∂Measure.pi (fun i : t ↦ μ i)) = _
      simp_rw [checkNormalizer_const checks s _ x]
      simp

end ConditionalNormalizers

variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {C : Type*} [Fintype C]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

omit [Fintype C] [∀ i, IsFiniteKernel (κ i)] in
lemma conditionalDensity_le_auxiliaryDensity (s o : Finset ι)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    conditionalDensity checks κ s o x z ≤ auxiliaryDensity checks κ s x z :=
  lmarginal_mono (fun v ↦ checkWeight_antitone checks Finset.subset_union_left
    (fun i ↦ (x i,v i))) z

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
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_Insertion
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
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {ι C : Type*} [Fintype ι] [Fintype C] [DecidableEq ι]
  {X : ι → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype ι] in
lemma uniformInsertionOn_of_check_failures (checks : C → LocalCheck X)
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (p : ι → C → ℝ≥0∞) (a : ℝ≥0∞) (r : Finset ι)
    (hfail : ∀i∈r, ∀c, i∈(checks c).support → ∀x : ∀j,X j,
      μ i {y | ¬(checks c).pass (Function.update x i y)} ≤ p i c)
    (htotal : ∀i∈r,a+(∑c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),p i c) ≤ 1) :
    UniformInsertionOn checks μ a r := by
  classical
  intro i hir s hi x
  let B : Set (X i) := {y | Function.update x i y ∈ insertionEvent checks s i}
  have hm : Measurable (fun y : X i ↦ Function.update x i y) := by
    fun_prop
  have hB : MeasurableSet B := (measurableSet_insertionEvent checks s i).preimage hm
  have hsub : Bᶜ ⊆ ⋃c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),
      {y | ¬(checks c).pass (Function.update x i y)} := by
    intro y hy
    classical
    simp only [B,Set.mem_compl_iff,Set.mem_ofPred_eq,insertionEvent] at hy
    push Not at hy
    rcases hy with ⟨c,hc,hcs,hp⟩
    have hci : i∈(checks c).support := by
      by_contra hn
      apply hcs
      intro j hj
      have h := hc hj
      rcases Finset.mem_insert.mp h with he|hs
      · subst j; contradiction
      · exact hs
    exact mem_iUnion.2 ⟨c,mem_iUnion.2 ⟨by simp [hci],hp⟩⟩
  have hb : μ i Bᶜ ≤ ∑c∈Finset.univ.filter (fun c ↦ i∈(checks c).support),p i c := by
    apply (measure_mono hsub).trans
    apply (measure_biUnion_finset_le _ _).trans
    exact Finset.sum_le_sum fun c hc ↦ hfail i hir c (Finset.mem_filter.mp hc).2 x
  have hadd : a+μ i Bᶜ ≤ μ i B+μ i Bᶜ := by
    rw [measure_add_measure_compl hB]
    exact (add_le_add_right hb a).trans (by simpa using htotal i hir)
  have ha : a≤μ i B := (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).mp hadd
  have he : (fun y ↦ (insertionEvent checks s i).indicator (fun _ ↦ (1 : ℝ≥0∞)) (Function.update x i y))=
      B.indicator (fun _ ↦ (1 : ℝ≥0∞)) := by funext y; simp [B,Set.indicator_apply]
  rw [he,lintegral_indicator hB]
  simpa using ha

end HardSphere.Comparison

end
end

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridAlignment
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open Classical
namespace HardSphere.Groups
open CellOrbital BathSlice HardSphere.Lattice ShiftVisits

lemma gridSite_injective {K : ℕ} [NeZero K] : Function.Injective (gridSite (K:=K)) := by
  intro v w h
  funext j
  apply Fin.ext
  have hh := congrArg (fun f : DiscreteTorus K ↦ (f j).val) h
  simpa only [gridSite,ZMod.val_natCast_of_lt (v j).isLt,ZMod.val_natCast_of_lt (w j).isLt] using hh

end HardSphere.Groups

end
end

section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open HardSphere.Lattice HardSphere.FreeVisits HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

lemma card_rangePackingBox (c : Fin 3→ℝ) : (rangePackingBox c).card=49^3 := by
  unfold rangePackingBox
  rw [Pi.card_Icc]
  have h (j : Fin 3) : (Finset.Icc (⌊c j⌋-24) (⌊c j⌋+24)).card=49 := by rw [Int.card_Icc]; omega
  simp only [h,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma grid_packing_witness {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (c : Fin 3→ℝ) (v : Fin 3→Fin K)
    (hv : ∀j,dist (gridCenter L v j) ((c j:ℝ):AddCircle L.val)≤23) :
    ∃z∈rangePackingBox c,torusProjection K z=gridSite v := by
  let k : Vertex := fun j ↦ round (L.val⁻¹*((v j).val-c j))
  let z : Vertex := fun j ↦ ((v j).val:ℤ)-k j*(K:ℤ)
  refine ⟨z,?_,?_⟩
  · apply Finset.mem_Icc.mpr
    have hz (j : Fin 3) : ⌊c j⌋-24≤z j ∧ z j≤⌊c j⌋+24 := by
      have hd := hv j
      change dist (((v j).val:ℝ):AddCircle L.val) ((c j:ℝ):AddCircle L.val)≤23 at hd
      rw [dist_eq_norm,←AddCircle.coe_sub,AddCircle.norm_eq] at hd
      have hd' : |(z j:ℝ)-c j|≤23 := by
        convert hd using 1
        all_goals try with_reducible_and_instances rfl
        dsimp [z,k]
        push_cast
        rw [hL]
        ring_nf
      have hl := Int.floor_le (c j)
      have hu := Int.lt_floor_add_one (c j)
      obtain ⟨h₁,h₂⟩ := abs_le.mp hd'
      constructor <;> (apply (Int.cast_le (R:=ℝ)).mp; push_cast; linarith)
    exact ⟨fun j ↦ (hz j).1,fun j ↦ (hz j).2⟩
  · ext j
    simp [torusProjection,z,gridSite]

lemma card_near_grid_le {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (x : Torus L) (A : Finset (Fin 3→Fin K))
    (hA : ∀v∈A,torusDistance L (gridCenter L v) x≤23) : A.card≤49^3 := by
  let c : Fin 3→ℝ := fun j ↦ (AddCircle.equivIco L.val 0 (x j)).val
  have hc (j : Fin 3) : ((c j:ℝ):AddCircle L.val)=x j := AddCircle.coe_equivIco
  have hsub : A.image gridSite⊆(rangePackingBox c).image (torusProjection K) := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z,hz,he⟩ := grid_packing_witness L hL c w (fun j ↦ by
      rw [hc]
      exact (dist_coord_le_torusDistance L (gridCenter L w) x j).trans (hA w hw))
    exact Finset.mem_image.mpr ⟨z,hz,he⟩
  have hh : (A.image gridSite).card≤49^3 :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (card_rangePackingBox c).le)
  rwa [Finset.card_image_of_injective A gridSite_injective] at hh

lemma card_near_labels {I : Type*} [Fintype I] {K : ℕ} [NeZero K]
    (L : Length) (hL : L.val=(K:ℝ)) (anchor : I→Fin 3→Fin K) (M : ℕ)
    (hm : ∀v,(Finset.univ.filter (fun i : I ↦ anchor i=v)).card≤M) (x : Torus L) :
    (Finset.univ.filter (fun i : I ↦ torusDistance L (gridCenter L (anchor i)) x≤23)).card≤49^3*M := by
  let A : Finset (Fin 3→Fin K) := Finset.univ.filter (fun v ↦ torusDistance L (gridCenter L v) x≤23)
  let S : Finset I := Finset.univ.filter (fun i ↦ torusDistance L (gridCenter L (anchor i)) x≤23)
  have hs : ∀i∈S,anchor i∈A := by intro i hi; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hs
  change S.card≤_
  rw [hcard]
  calc
    _ ≤ ∑_v∈A,M := Finset.sum_le_sum (fun v _ ↦ (Finset.card_le_card (by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩)).trans (hm v))
    _ = A.card*M := by simp
    _ ≤ 49^3*M := Nat.mul_le_mul_right _ (card_near_grid_le L hL x A (fun v hv ↦ (Finset.mem_filter.mp hv).2))

end HardSphere.Groups

end
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

lemma measurable_partialNormalizer {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    (s o : Finset ι) : Measurable (partialNormalizer checks μ s o) :=
  (measurable_checkWeight checks (s ∪ o)).lmarginal μ

omit [Fintype C] in
lemma UniformInsertionOn.mono {μ : ∀ i, Measure (X i)} {a : ℝ≥0∞}
    {s t : Finset ι} (h : UniformInsertionOn checks μ a t) (hst : s ⊆ t) :
    UniformInsertionOn checks μ a s := fun i hi ↦ h i (hst hi)

lemma checkNormalizer_pos_on {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} (ha : 0 < a) (s : Finset ι)
    (hcompat : UniformInsertionOn checks μ a s) (x : ∀ i, X i) :
    0 < checkNormalizer checks μ s x := by
  have hp := partialNormalizer_pos checks ha hcompat (Finset.disjoint_empty_right s) x
    (show x ∈ retainedEvent checks ∅ from fun c hc ↦
      False.elim ((checks c).nonempty.ne_empty (Finset.subset_empty.mp hc)))
  simpa only [partialNormalizer, checkNormalizer, Finset.union_empty] using hp

lemma checkNormalizer_union_lower_on {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} {t : Finset ι} (hcompat : UniformInsertionOn checks μ a t)
    (s : Finset ι) (hst : Disjoint s t) (x : ∀ i, X i) :
    a ^ t.card * checkNormalizer checks μ s x ≤ checkNormalizer checks μ (s ∪ t) x := by
  have h := partialNormalizer_union_lower checks hcompat s t ∅ (Finset.Subset.refl t)
    (by simpa using hst) x
  simpa only [partialNormalizer, checkNormalizer, Finset.union_empty] using h

end NormalizerFacts

lemma isProbabilityMeasure_compProd_of_mass {X Z : Type*} [MeasurableSpace X]
    [MeasurableSpace Z] (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X Z) [IsFiniteKernel κ] (hm : ∫⁻ x, κ x Set.univ ∂μ = 1) :
    IsProbabilityMeasure (μ.compProd κ) where
  measure_univ := by simpa only [Measure.compProd_apply MeasurableSet.univ,
    Set.preimage_univ] using hm

section ConditionalOverlap
variable {ι : Type*} [DecidableEq ι] {X Z W : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  [∀ i, MeasurableSpace (W i)]
  {C D : Type*} [Fintype C] [Fintype D]
  (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (other : D → LocalCheck (fun i ↦ X i × W i))
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]
  (η : ∀ i, Kernel (X i) (W i)) [∀ i, IsFiniteKernel (η i)]

lemma conditionalDensity_overlap_bound
    {μ : ∀ i, Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
    (fs ft cs ct os ot : Finset ι)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs ∪ ft) (cs ∪ ct))
    {G : ℝ≥0∞}
    (hκb : ∀ i x, κ i x Set.univ ≤ G)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hηm : ∀ i, ∫⁻ x, η i x Set.univ ∂μ i = 1)
    (x : ∀ i, X i) (z : ∀ i, Z i) (w : ∀ i, W i) :
    lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct))
      (fun y ↦ conditionalDensity checks κ (fs ∪ cs) os y z *
        conditionalDensity other η (ft ∪ ct) ot y w) x ≤
      (checkNormalizer checks (fun i ↦ (μ i).compProd (κ i)) fs (fun i ↦ (x i,z i)) *
       checkNormalizer other (fun i ↦ (μ i).compProd (η i)) ft (fun i ↦ (x i,w i))) *
       G ^ (cs ∩ ct).card := by
  apply le_trans (lmarginal_mono (fun y ↦
    mul_le_mul' (conditionalDensity_le_auxiliaryDensity checks κ _ _ y z)
      (conditionalDensity_le_auxiliaryDensity other η _ _ y w)) x)
  exact auxiliaryDensity_overlap_bound checks other κ η fs ft cs ct hff hfn hκb hκm hηm x z w

end ConditionalOverlap

lemma finite_normalizer_cancellation {p q zs zt ys yt : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpT : p ≠ ⊤) (hq0 : q ≠ 0) (hqT : q ≠ ⊤)
    (hzs0 : zs ≠ 0) (hzsT : zs ≠ ⊤) (hzt0 : zt ≠ 0) (hztT : zt ≠ ⊤)
    (hys0 : ys ≠ 0) (hysT : ys ≠ ⊤) (hyt0 : yt ≠ 0) (hytT : yt ≠ ⊤)
    (b : ℝ≥0∞) :
    ((zs / (p * ys)) * (zt / (q * yt)) * ((ys * yt) * b)) /
        ((p * q) * (zs * zt)) = b / ((p * q) ^ 2) := by
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  have hpqT : p * q ≠ ⊤ := ENNReal.mul_ne_top hpT hqT
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hp0) (Or.inl hpT),
    ENNReal.mul_inv (Or.inl hq0) (Or.inl hqT),
    ENNReal.mul_inv (Or.inl hpq0) (Or.inl hpqT),
    ENNReal.mul_inv (Or.inl hzs0) (Or.inl hzsT), ENNReal.inv_pow]
  calc
    _ = (zs * zs⁻¹) * (zt * zt⁻¹) * (ys * ys⁻¹) * (yt * yt⁻¹) *
      (b * (p⁻¹ * q⁻¹) ^ 2) := by simp only [pow_two]; ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hzs0 hzsT,
      ENNReal.mul_inv_cancel hzt0 hztT, ENNReal.mul_inv_cancel hys0 hysT,
      ENNReal.mul_inv_cancel hyt0 hytT]; simp

section ConditionalLower
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {C : Type*} [Fintype C]
  (checks : C → LocalCheck X)

lemma partialNormalizer_ge_far {μ : ∀ i, Measure (X i)} [∀ i, SigmaFinite (μ i)]
    {a : ℝ≥0∞} {s t o : Finset ι}
    (hcompat : UniformInsertionOn checks μ a (s ∪ t))
    (hto : Disjoint (s ∪ o) t) (hso : Disjoint s o)
    (hsep : SeparatedChecks checks s o) (x : ∀ i, X i)
    (hx : x ∈ retainedEvent checks o) :
    a ^ t.card * checkNormalizer checks μ s x ≤
      partialNormalizer checks μ (s ∪ t) o x := by
  have h := partialNormalizer_union_lower checks hcompat s t o Finset.subset_union_right hto x
  rwa [partialNormalizer_far_eq checks hso hsep x, checkWeight,
    Set.indicator_of_mem hx, mul_one] at h

end ConditionalLower

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

theorem conditional_cancellation
    (fs ft cs ct os ot : Finset ι)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs ∪ ft) (cs ∪ ct))
    (hos : Disjoint (fs ∪ cs) os) (hot : Disjoint (ft ∪ ct) ot)
    (hosU : (fs ∪ cs) ∪ os = (fs ∪ ft) ∪ (cs ∪ ct))
    (hotU : (ft ∪ ct) ∪ ot = (fs ∪ ft) ∪ (cs ∪ ct))
    {a G : ℝ≥0∞} (ha : 0 < a) (ha1 : a ≤ 1)
    (hκb : ∀ i x, κ i x Set.univ ≤ G)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hηm : ∀ i, ∫⁻ x, η i x Set.univ ∂μ i = 1)
    (hRef : UniformInsertionOn reference μ a ((fs ∪ ft) ∪ (cs ∪ ct)))
    (hS : UniformInsertionOn checks (fun i ↦ (μ i).compProd (κ i)) a (fs ∪ cs))
    (hT : UniformInsertionOn other (fun i ↦ (μ i).compProd (η i)) a (ft ∪ ct))
    (hsepRef : SeparatedChecks reference fs ft)
    (hsepS : SeparatedChecks checks fs os) (hsepT : SeparatedChecks other ft ot)
    (hOutsideS : ∀ (x : ∀ i, X i) (z : ∀ i, Z i), x ∈ retainedEvent reference os →
      (fun i ↦ (x i,z i)) ∈ retainedEvent checks os)
    (hOutsideT : ∀ (x : ∀ i, X i) (w : ∀ i, W i), x ∈ retainedEvent reference ot →
      (fun i ↦ (x i,w i)) ∈ retainedEvent other ot)
    (x : ∀ i, X i) (z : ∀ i, Z i) (w : ∀ i, W i) :
    lmarginal μ ((fs ∪ ft) ∪ (cs ∪ ct))
      (fun y ↦ checkWeight reference ((fs ∪ ft) ∪ (cs ∪ ct)) y *
        conditionalLikelihood reference checks μ κ (fs ∪ cs) os y z *
        conditionalLikelihood reference other μ η (ft ∪ ct) ot y w) x /
      checkNormalizer reference μ ((fs ∪ ft) ∪ (cs ∪ ct)) x ≤
      G ^ (cs ∩ ct).card / a ^ (2 * (cs.card + ct.card)) := by
  let U := (fs ∪ ft) ∪ (cs ∪ ct)
  let ν i := (μ i).compProd (κ i)
  let ξ i := (μ i).compProd (η i)
  have : ∀ i, IsProbabilityMeasure (ν i) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (κ i) (hκm i)
  have : ∀ i, IsProbabilityMeasure (ξ i) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (η i) (hηm i)
  let zs := checkNormalizer reference μ fs x
  let zt := checkNormalizer reference μ ft x
  let ys := checkNormalizer checks ν fs (fun i ↦ (x i,z i))
  let yt := checkNormalizer other ξ ft (fun i ↦ (x i,w i))
  have hfsU : fs ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hftU : ft ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hNearU : cs ∪ ct ⊆ U := Finset.subset_union_right
  have hzs : 0 < zs := checkNormalizer_pos_on reference ha fs
    (UniformInsertionOn.mono reference hRef hfsU) x
  have hzt : 0 < zt := checkNormalizer_pos_on reference ha ft
    (UniformInsertionOn.mono reference hRef hftU) x
  have hys : 0 < ys := checkNormalizer_pos_on checks ha fs
    (UniformInsertionOn.mono checks hS Finset.subset_union_left) _
  have hyt : 0 < yt := checkNormalizer_pos_on other ha ft
    (UniformInsertionOn.mono other hT Finset.subset_union_left) _
  have hzsT : zs ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one reference fs x)
  have hztT : zt ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one reference ft x)
  have hysT : ys ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one checks fs _)
  have hytT : yt ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one other ft _)
  have haT : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top ha1
  have hZU : a ^ (cs.card + ct.card) * (zs * zt) ≤ checkNormalizer reference μ U x := by
    calc
      _ ≤ a ^ (cs ∪ ct).card * (zs * zt) :=
        mul_le_mul_left (pow_le_pow_right_of_le_one' ha1 (Finset.card_union_le cs ct)) _
      _ = a ^ (cs ∪ ct).card * checkNormalizer reference μ (fs ∪ ft) x := by
        rw [checkNormalizer_union_eq_mul reference hff hsepRef]
      _ ≤ _ := checkNormalizer_union_lower_on reference
        (UniformInsertionOn.mono reference hRef hNearU) (fs ∪ ft) hfn x
  have hfs : Disjoint fs cs := hfn.mono Finset.subset_union_left Finset.subset_union_left
  have hft : Disjoint ft ct := hfn.mono Finset.subset_union_right Finset.subset_union_right
  have hfsos : Disjoint fs os := hos.mono_left Finset.subset_union_left
  have hftot : Disjoint ft ot := hot.mono_left Finset.subset_union_left
  have hfcso : Disjoint (fs ∪ os) cs := Finset.disjoint_union_left.mpr
    ⟨hfs, (hos.mono_left Finset.subset_union_right).symm⟩
  have hftcto : Disjoint (ft ∪ ot) ct := Finset.disjoint_union_left.mpr
    ⟨hft, (hot.mono_left Finset.subset_union_right).symm⟩
  let rs := zs / (a ^ cs.card * ys)
  let rt := zt / (a ^ ct.card * yt)
  have hratioS (y : ∀ i, X i) (hy : y ∈ retainedEvent reference U) :
      partialNormalizer reference μ (fs ∪ cs) os y /
        partialNormalizer checks ν (fs ∪ cs) os (fun i ↦ (y i,z i)) ≤ rs := by
    have hyo : y ∈ retainedEvent reference os := fun c hc ↦ hy c
      (hc.trans (by change os ⊆ (fs ∪ ft) ∪ (cs ∪ ct); rw [← hosU]; exact Finset.subset_union_right))
    have hl := partialNormalizer_ge_far checks hS hfcso hfsos hsepS
      (fun i ↦ (y i,z i)) (hOutsideS y z hyo)
    rw [checkNormalizer_const checks fs _ (fun i ↦ (x i,z i))] at hl
    have hu := partialNormalizer_le_far reference (μ := μ) (o := os) hfs y
    rw [checkNormalizer_const reference fs y x] at hu
    exact ENNReal.div_le_div hu hl
  have hratioT (y : ∀ i, X i) (hy : y ∈ retainedEvent reference U) :
      partialNormalizer reference μ (ft ∪ ct) ot y /
        partialNormalizer other ξ (ft ∪ ct) ot (fun i ↦ (y i,w i)) ≤ rt := by
    have hyo : y ∈ retainedEvent reference ot := fun c hc ↦ hy c
      (hc.trans (by change ot ⊆ (fs ∪ ft) ∪ (cs ∪ ct); rw [← hotU]; exact Finset.subset_union_right))
    have hl := partialNormalizer_ge_far other hT hftcto hftot hsepT
      (fun i ↦ (y i,w i)) (hOutsideT y w hyo)
    rw [checkNormalizer_const other ft _ (fun i ↦ (x i,w i))] at hl
    have hu := partialNormalizer_le_far reference (μ := μ) (o := ot) hft y
    rw [checkNormalizer_const reference ft y x] at hu
    exact ENNReal.div_le_div hu hl
  let H (y : ∀ i, X i) := conditionalDensity checks κ (fs ∪ cs) os y z *
    conditionalDensity other η (ft ∪ ct) ot y w
  have hH : Measurable H := (measurable_conditionalDensity checks κ _ _ z).mul
    (measurable_conditionalDensity other η _ _ w)
  have hpoint (y : ∀ i, X i) :
      checkWeight reference U y * conditionalLikelihood reference checks μ κ (fs ∪ cs) os y z *
        conditionalLikelihood reference other μ η (ft ∪ ct) ot y w ≤ (rs * rt) * H y := by
    classical
    by_cases hy : y ∈ retainedEvent reference U
    · simp only [checkWeight, Set.indicator_of_mem hy, one_mul, conditionalLikelihood]
      calc
        _ ≤ (rs * conditionalDensity checks κ (fs ∪ cs) os y z) *
            (rt * conditionalDensity other η (ft ∪ ct) ot y w) :=
          mul_le_mul' (mul_le_mul_left (hratioS y hy) _) (mul_le_mul_left (hratioT y hy) _)
        _ = _ := by dsimp [H]; ac_rfl
    · simp [checkWeight, hy]
  have hIntegral : lmarginal μ U
      (fun y ↦ checkWeight reference U y *
        conditionalLikelihood reference checks μ κ (fs ∪ cs) os y z *
        conditionalLikelihood reference other μ η (ft ∪ ct) ot y w) x ≤
      (rs * rt) * ((ys * yt) * G ^ (cs ∩ ct).card) := by
    calc
      _ ≤ lmarginal μ U (fun y ↦ (rs * rt) * H y) x := lmarginal_mono hpoint x
      _ = (rs * rt) * lmarginal μ U H x :=
        lintegral_const_mul _ (hH.comp (measurable_updateFinset (x := x) (s := U)))
      _ ≤ _ := mul_le_mul_right
        (conditionalDensity_overlap_bound checks other κ η fs ft cs ct os ot hff hfn
          hκb hκm hηm x z w) _
  calc
    _ ≤ ((rs * rt) * ((ys * yt) * G ^ (cs ∩ ct).card)) /
        (a ^ (cs.card + ct.card) * (zs * zt)) := ENNReal.div_le_div hIntegral hZU
    _ = G ^ (cs ∩ ct).card / ((a ^ cs.card * a ^ ct.card) ^ 2) := by
      rw [pow_add]
      exact finite_normalizer_cancellation (ne_of_gt (ENNReal.pow_pos ha _))
        (ENNReal.pow_ne_top haT) (ne_of_gt (ENNReal.pow_pos ha _)) (ENNReal.pow_ne_top haT)
        (ne_of_gt hzs) hzsT (ne_of_gt hzt) hztT (ne_of_gt hys) hysT (ne_of_gt hyt) hytT _
    _ = _ := by rw [← pow_add, ← pow_mul, Nat.mul_comm 2]

end CancellationEstimate

end HardSphere.Comparison
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FrozenChecks
attribute [-instance] _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
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
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_update (U : Finset I) (x y : ∀i,X i) {i : I} (hi : i∈U) (v : X i) :
    freezeOutside U x (Function.update y i v)=Function.update (freezeOutside U x y) i v := by
  funext j
  by_cases hj : j=i
  · subst j;simp [freezeOutside,hi]
  · simp [freezeOutside,Function.update_of_ne hj]

omit [Fintype C]
lemma frozen_support_subset (checks : C → LocalCheck X) (U t : Finset I) (c : C) :
    (checks c).support ⊆ t∪(Finset.univ \ U) ↔ (checks c).support∩U ⊆t := by
  constructor
  · intro h i hi
    rcases Finset.mem_union.mp (h (Finset.mem_inter.mp hi).1) with ht|ho
    · exact ht
    · exact False.elim ((Finset.mem_sdiff.mp ho).2 (Finset.mem_inter.mp hi).2)
  · intro h i hi
    by_cases hu : i∈U
    · exact Finset.mem_union_left _ (h (Finset.mem_inter.mpr ⟨hi,hu⟩))
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩)

lemma frozen_retained (checks : C → LocalCheck X) (U t : Finset I) (x y : ∀i,X i)
    (hx : x∈retainedEvent checks (Finset.univ \ U)) :
    y∈retainedEvent (frozenChecks checks U x) t ↔
      freezeOutside U x y∈retainedEvent checks (t∪(Finset.univ \ U)) := by
  constructor
  · intro hy c hc
    by_cases he : ((checks c).support∩U).Nonempty
    · exact hy ⟨c,he⟩ ((frozen_support_subset checks U t c).mp hc)
    · have hout : (checks c).support⊆Finset.univ \ U := by
        intro i hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
        intro hu
        exact he ⟨i,Finset.mem_inter.mpr ⟨hi,hu⟩⟩
      apply ((checks c).depends x (freezeOutside U x y) ?_).mp (hx c hout)
      intro i hi
      simp only [freezeOutside,ite_eq_right (Finset.mem_sdiff.mp (hout hi)).2]
  · intro hy c hc
    exact hy c.val ((frozen_support_subset checks U t c.val).mpr hc)

lemma frozen_checkWeight (checks : C → LocalCheck X) (U t : Finset I) (x y : ∀i,X i)
    (hx : x∈retainedEvent checks (Finset.univ \ U)) :
    checkWeight (frozenChecks checks U x) t y=
      checkWeight checks (t∪(Finset.univ \ U)) (freezeOutside U x y) := by
  classical
  simp only [checkWeight,Set.indicator_apply,frozen_retained checks U t x y hx]

lemma frozen_insertion (checks : C → LocalCheck X) (U s : Finset I) (x y : ∀i,X i) (i : I) :
    freezeOutside U x y∈insertionEvent checks (s∪(Finset.univ \ U)) i →
      y∈insertionEvent (frozenChecks checks U x) s i := by
  intro hy c hc hcs
  apply hy c.val
  · rw [←Finset.insert_union]
    exact (frozen_support_subset checks U (insert i s) c.val).mpr hc
  · intro hs
    exact hcs ((frozen_support_subset checks U s c.val).mp hs)

lemma frozen_uniformInsertion (checks : C → LocalCheck X) (U : Finset I) (x : ∀i,X i)
    (μ : ∀i,Measure (X i)) {a : ℝ≥0∞}
    (h : UniformInsertionOn checks μ a U) :
    UniformInsertionOn (frozenChecks checks U x) μ a U := by
  intro i hi s his y
  have hin : i∉s∪(Finset.univ \ U) := by simp [Finset.mem_union,his,hi]
  apply (h i hi (s∪(Finset.univ \ U)) hin (freezeOutside U x y)).trans
  apply lintegral_mono
  intro v
  dsimp only
  rw [←freezeOutside_update U x y hi v]
  by_cases hp : freezeOutside U x (Function.update y i v)∈insertionEvent checks (s∪(Finset.univ \ U)) i
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (frozen_insertion checks U s x (Function.update y i v) i hp)]
  · rw [Set.indicator_of_notMem hp]
    exact bot_le

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

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_update_self (U : Finset I) (x : ∀i,X i) (u : ∀i:U,X i) :
    freezeOutside U x (Function.updateFinset x U u)=Function.updateFinset x U u := by
  funext i
  by_cases hi : i∈U <;> simp [freezeOutside,Function.updateFinset,hi]

omit [Fintype C] in
lemma frozen_local_mean (checks : C→LocalCheck X) (μ : ∀i,Measure (X i))
    (U : Finset I) (x : ∀i,X i) (hx : x∈retainedEvent checks (Finset.univ\U))
    (F : (∀i,X i)→ℝ≥0∞) :
    lmarginal μ U (fun y ↦ checkWeight (frozenChecks checks U x) U y*F (freezeOutside U x y)) x /
      checkNormalizer (frozenChecks checks U x) μ U x=
    lmarginal μ U (fun y ↦ checkWeight checks Finset.univ y*F y) x /
      lmarginal μ U (checkWeight checks Finset.univ) x := by
  have hU : U∪(Finset.univ\U)=Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  unfold checkNormalizer lmarginal
  congr 1 <;> apply lintegral_congr <;> intro u <;> (try dsimp only) <;>
    rw [frozen_checkWeight checks U U _ _ hx,hU,freezeOutside_update_self]

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridNear
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set
namespace HardSphere.Groups
open HardSphere.Lattice HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable
lemma grid_near_of_distance {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (v w : Fin 3→Fin K) (h : torusDistance L (gridCenter L v) (gridCenter L w)≤23) :
    torusNear K 24 (gridSite w) (gridSite v) := by
  obtain ⟨z,hz,he⟩ := grid_packing_witness L hL (fun j ↦ ((w j).val:ℝ)) v
    (fun j ↦ (dist_coord_le_torusDistance L (gridCenter L v) (gridCenter L w) j).trans h)
  refine ⟨fun j ↦ z j-(w j).val,?_,?_⟩
  · intro j
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hz
    have hl' := hl j
    have hu' := hu j
    simp only [Int.floor_natCast] at hl' hu'
    change |z j-(w j).val|≤24
    exact abs_le.mpr ⟨by omega,by omega⟩
  · intro j
    have hj := congrFun he j
    dsimp [torusProjection,gridSite] at hj ⊢
    push_cast
    rw [←hj]
    ring
lemma distance_far_of_grid_far {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    {R : ℕ} (hR : 24≤R) (v w : Fin 3→Fin K)
    (h : ¬torusNear K R (gridSite v) (gridSite w)) :
    23<torusDistance L (gridCenter L v) (gridCenter L w) := by
  by_contra hn
  apply h
  exact torusNear_mono hR (torusNear_symm (grid_near_of_distance L hL v w (le_of_not_gt hn)))

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_RoutePartition
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
lemma mem_farSlots (e : V→V→Prop) (c : I→V) (s t : Finset I) (i : I) :
    i∈farSlots e c s t ↔ i∈s ∧ ∀j∈t,¬e (c i) (c j) := by
  simp [farSlots,nearSlots];tauto
lemma far_union_near (e : V→V→Prop) (c : I→V) (s t : Finset I) :
    farSlots e c s t∪nearSlots e c s t=s := by
  ext i
  simp [farSlots,nearSlots];tauto
lemma far_near_disjoint (e : V→V→Prop) (c : I→V) (s t : Finset I) :
    Disjoint (farSlots e c s t) (nearSlots e c s t) := Finset.sdiff_disjoint
lemma far_other_disjoint (e : V→V→Prop) (hrefl : ∀v,e v v) (c : I→V) (s t : Finset I) :
    Disjoint (farSlots e c s t) t := by
  apply Finset.disjoint_left.mpr
  intro i hi hit
  exact ((mem_farSlots e c s t i).mp hi).2 i hit (hrefl _)
lemma far_partition_disjoint (e : V→V→Prop) (hrefl : ∀v,e v v) (c : I→V) (s t : Finset I) :
    Disjoint (farSlots e c s t) (farSlots e c t s) ∧
    Disjoint (farSlots e c s t∪farSlots e c t s) (nearSlots e c s t∪nearSlots e c t s) := by
  have hst := far_other_disjoint e hrefl c s t
  have hts := far_other_disjoint e hrefl c t s
  have ns : nearSlots e c s t⊆s := Finset.filter_subset _ _
  have nt : nearSlots e c t s⊆t := Finset.filter_subset _ _
  have ft : farSlots e c t s⊆t := Finset.sdiff_subset
  refine ⟨hst.mono_right ft,?_⟩
  exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_right.mpr
    ⟨far_near_disjoint e c s t,hst.mono_right nt⟩,
    Finset.disjoint_union_right.mpr ⟨hts.mono_right ns,far_near_disjoint e c t s⟩⟩
lemma route_partition_union (e : V→V→Prop) (c : I→V) (s t : Finset I) :
    (farSlots e c s t∪farSlots e c t s)∪(nearSlots e c s t∪nearSlots e c t s)=s∪t := by
  rw [Finset.union_union_union_comm,far_union_near,far_union_near]
lemma commonSlots_near (e : V→V→Prop) (hrefl : ∀v,e v v) (c : I→V) (s t : Finset I) :
    nearSlots e c s t∩nearSlots e c t s=s∩t := by
  ext i
  simp only [Finset.mem_inter,mem_nearSlots]
  constructor
  · exact fun h ↦ ⟨h.1.1,h.2.1⟩
  · exact fun h ↦ ⟨⟨h.1,i,h.2,hrefl _⟩,⟨h.2,i,h.1,hrefl _⟩⟩

lemma physical_far_slots {K : ℕ} [NeZero K] (L : HardSphere.Length) (hL : L.val=(K:ℝ))
    (c : I→Fin 3→Fin K) (s t : Finset I) (i j : I)
    (hi : i∈farSlots (torusNear K 30) (fun i ↦ HardSphere.Groups.gridSite (c i)) s t)
    (hj : j∈t) :
    23<HardSphere.torusDistance L (HardSphere.CellOrbital.gridCenter L (c i)) (HardSphere.CellOrbital.gridCenter L (c j)) := by
  exact HardSphere.Groups.distance_far_of_grid_far L hL (by norm_num) _ _
    (((mem_farSlots _ _ _ _ _).mp hi).2 j hj)

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
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_DependentChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
variable {I E P : Type*} [Fintype I] [DecidableEq I] [Fintype E] [MeasurableSpace P]
  {V : I→Type*} [∀i,MeasurableSpace (V i)]
  (avoid : P→P→Prop) (hm : MeasurableSet {p : P×P | avoid p.1 p.2})
  (left right : E→I) (hdiff : ∀e,left e≠right e)
  (getL : (e:E)→V (left e)→P) (getR : (e:E)→V (right e)→P)
  (hL : ∀e,Measurable (getL e)) (hR : ∀e,Measurable (getR e))

include hdiff in
omit [Fintype I] in
lemma dependent_insertion (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (p : I→E→ℝ≥0∞) (a : ℝ≥0∞) (U : Finset I)
    (hleft : ∀e,left e∈U→∀g : V (right e),μ (left e) {f | ¬avoid (getL e f) (getR e g)}≤p (left e) e)
    (hright : ∀e,right e∈U→∀f : V (left e),μ (right e) {g | ¬avoid (getL e f) (getR e g)}≤p (right e) e)
    (htotal : ∀i∈U,a+(∑e∈Finset.univ.filter
      (fun e ↦ i∈(dependentCheck avoid hm left right getL getR hL hR e).support),p i e)≤1) :
    UniformInsertionOn (dependentCheck avoid hm left right getL getR hL hR) μ a U := by
  apply uniformInsertionOn_of_check_failures _ μ p a U _ htotal
  intro i hi e he x
  have hie : i=left e ∨ i=right e := by simpa [dependentCheck] using he
  rcases hie with hh|hh
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e).symm] using hleft e hi (x (right e))
  · subst i
    simpa only [dependentCheck,Function.update_self,Function.update_of_ne (hdiff e)] using hright e hi (x (left e))

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
attribute [local instance] Classical.propDecidable
variable {I E B : Type*} [Fintype I] [DecidableEq I] [Fintype E]
  [Fintype B] [DecidableEq B]

omit [Fintype I] in
lemma card_incident_edge_le (left right : E → I) (color : E → B)
    (hinj : Function.Injective (fun e ↦ (color e,(left e,right e))))
    (i : I) (T : Finset I)
    (hnear : ∀e,left e=i → right e∈T)
    (hnear' : ∀e,right e=i → left e∈T) :
    (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).card ≤ Fintype.card B*(2*T.card) := by
  classical
  let Q := (({i}:Finset I) ×ˢ T)∪(T ×ˢ {i})
  have hs : (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).image
      (fun e ↦ (color e,(left e,right e)))⊆(Finset.univ : Finset B) ×ˢ Q := by
    intro p hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases (Finset.mem_filter.mp he).2 with hh|hh
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨Finset.mem_singleton.mpr hh,hnear e hh⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨hnear' e hh,Finset.mem_singleton.mpr hh⟩)
  have hq : Q.card ≤ 2*T.card := by
    apply (Finset.card_union_le _ _).trans
    simp only [Finset.card_product,Finset.card_singleton,one_mul,mul_one]
    omega
  have hcard := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ hinj,Finset.card_product,Finset.card_univ] at hcard
  exact hcard.trans (Nat.mul_le_mul_left _ hq)

end HardSphere.Comparison
namespace HardSphere.Groups
open Comparison HardSphere.CellOrbital
attribute [local instance] Classical.propDecidable

lemma physical_incident_degree {I E B : Type*} [Fintype I] [DecidableEq I] [Fintype E]
    [Fintype B] [DecidableEq B] {K : ℕ} [NeZero K] (L : Length) (hL : L.val=(K:ℝ))
    (anchor : I → Fin 3 → Fin K) (M : ℕ)
    (hm : ∀v,(Finset.univ.filter (fun i : I ↦ anchor i=v)).card ≤ M)
    (left right : E → I) (color : E → B)
    (hinj : Function.Injective (fun e ↦ (color e,(left e,right e))))
    (hnear : ∀e,torusDistance L (gridCenter L (anchor (left e))) (gridCenter L (anchor (right e))) ≤ 23)
    (i : I) :
    (Finset.univ.filter (fun e ↦ left e=i ∨ right e=i)).card ≤ Fintype.card B*(2*(49^3*M)) := by
  let T := Finset.univ.filter (fun j : I ↦ torusDistance L (gridCenter L (anchor j)) (gridCenter L (anchor i)) ≤ 23)
  have hcard := card_incident_edge_le left right color hinj i T (by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa only [he,torusDistance_comm L (gridCenter L (anchor i))] using hnear e) (by
    intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [he] using hnear e⟩)
  exact hcard.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_near_labels L hL anchor M hm _)))

end HardSphere.Groups

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalFactorChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.instFintypeFrozenCheckIndex _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators Topology
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison CellOrbital Groups
attribute [local instance] Classical.propDecidable

lemma normalized_marginal_collision {X : Type*} [MeasurableSpace X]
    {L : Length} {S : Set C(Time,Point)} (μ : Measure X) (P : Measure S)
    (f : X → S) (hf : Measurable f) {G q : ℝ≥0∞} (hdom : μ.map f ≤ G • P)
    (r : ℝ) (g : C(Time,Point))
    (hq : P {u | TrialCollision (L:=L) r (projectCurve L g) u.val} ≤ q) :
    μ {x | TrialCollision (L:=L) r (projectCurve L g) (f x).val} ≤ G*q := by
  have hm : MeasurableSet {u : S | TrialCollision (L:=L) r (projectCurve L g) u.val} :=
    (trialCollision_closed r (projectCurve L g)).measurableSet.preimage measurable_subtype_coe
  have h := hdom {u | TrialCollision (L:=L) r (projectCurve L g) u.val}
  rw [Measure.map_apply hf hm,Measure.smul_apply,smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl hq)

variable {I J E : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype E]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]
  (allowed : J → Set C(Time,Point))
  (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
  (color : E → Bool) (labelL labelR : E → J) (hdiff : ∀e,labelL e ≠ labelR e)
  (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))

omit [Fintype I] [Fintype J] in
include howner hdiff in
lemma factorPath_insertion (r : ℝ) (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (D : ℕ) (U : Finset I)
    (hdom : ∀b j,owner b j∈U → (μ (owner b j)).map (path b j) ≤ G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision (L:=L) r (projectCurve L g.val) f.val} ≤ q)
    (hdegree : ∀i∈U,(Finset.univ.filter (fun e ↦ owner (color e) (labelL e)=i ∨ owner (color e) (labelR e)=i)).card ≤ D)
    (hsmall : a+(D:ℝ≥0∞)*(G*q) ≤ 1) :
    UniformInsertionOn (factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r) μ a U := by
  apply dependent_insertion _ _ _ _ (fun e ↦ fun h ↦ hdiff e (howner (color e) h))
    _ _ _ _ μ (fun _ _ ↦ G*q) a U
  · intro e he g
    simpa only [not_not] using normalized_marginal_collision (μ _) (P _) _ (hpath _ _)
      (hdom _ _ he) r (path (color e) (labelR e) g).val (hq _ _ (hdiff e) _)
  · intro e he f
    have h := normalized_marginal_collision (μ _) (P _) _ (hpath _ _)
      (hdom _ _ he) r (path (color e) (labelL e) f).val (hq _ _ (hdiff e).symm _)
    have hh : {g | ¬¬TrialCollision (L:=L) r (projectCurve L (path (color e) (labelR e) g).val)
        (path (color e) (labelL e) f).val}=
      {g | TrialCollision (L:=L) r (projectCurve L (path (color e) (labelL e) f).val)
        (path (color e) (labelR e) g).val} := by
      ext g
      simp only [mem_ofPred_eq,not_not]
      exact physicalPairCheck_symmetric r _ _
    rw [hh]
    exact h
  · intro i hi
    have hd := hdegree i hi
    have he : (Finset.univ.filter (fun e ↦ i∈(factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r e).support))=
        Finset.univ.filter (fun e ↦ owner (color e) (labelL e)=i ∨ owner (color e) (labelR e)=i) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton]
      exact or_congr eq_comm eq_comm
    change a+(∑_e∈Finset.univ.filter (fun e ↦ i∈(factorPathCheck (L:=L) allowed owner color labelL labelR path hpath r e).support),G*q) ≤ 1
    rw [he,Finset.sum_const, nsmul_eq_mul]
    exact (add_le_add le_rfl (mul_le_mul' (by exact_mod_cast hd) le_rfl)).trans hsmall

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SparseChecks
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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

lemma incident_centers_close {I : Type*} {L : Length} (anchor center : I→Torus L)
    (owner : I→I) (hcenter : ∀i,torusDistance L (anchor i) (center (owner i))≤1)
    (i j : I) (hij : torusDistance L (anchor i) (anchor j)≤21) :
    torusDistance L (center (owner i)) (center (owner j))≤23 := by
  have h₁ := torusDistance_triangle' L (center (owner i)) (anchor i) (center (owner j))
  have h₂ := torusDistance_triangle' L (anchor i) (anchor j) (center (owner j))
  rw [torusDistance_comm L (center (owner i)) (anchor i)] at h₁
  linarith [hcenter i,hcenter j]

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

lemma physicalSparseChecks_degree {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (anchor : J → Torus L) (center : I → Fin 3 → Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
    (hcenter : ∀b j,torusDistance L (anchor j) (gridCenter L (center (owner b j)))≤1)
    (i : I) :
    (Finset.univ.filter (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.1=i ∨ owner e.1 e.2.val.2=i)).card≤4*(49^3*M) := by
  have hinj : Function.Injective (fun e : physicalEdges anchor ↦
      (e.1,(owner e.1 e.2.val.1,owner e.1 e.2.val.2))) := by
    rintro ⟨b,⟨⟨j,k⟩,h⟩⟩ ⟨b',⟨⟨j',k'⟩,h'⟩⟩ he
    have hb : b=b' := congrArg Prod.fst he
    subst b'
    have hj : j=j' := howner b (congrArg (fun p ↦ p.2.1) he)
    have hk : k=k' := howner b (congrArg (fun p ↦ p.2.2) he)
    subst j';subst k';rfl
  have hn : ∀e : physicalEdges anchor,
      torusDistance L (gridCenter L (center (owner e.1 e.2.val.1)))
        (gridCenter L (center (owner e.1 e.2.val.2)))≤23 := by
    intro e
    exact incident_centers_close anchor (fun j ↦ gridCenter L (center (owner e.1 j))) id
      (hcenter e.1) e.2.val.1 e.2.val.2 e.2.property.2
  have hd := physical_incident_degree L hL center M hm
    (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.1)
    (fun e : physicalEdges anchor ↦ owner e.1 e.2.val.2) Prod.fst hinj hn i
  simp only [Fintype.card_bool] at hd
  omega

lemma physicalSparseChecks_insertion {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J → Torus L) (center : I → Fin 3 → Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (allowed : J → Set C(Time,Point))
    (owner : Bool → J → I) (howner : ∀b,Function.Injective (owner b))
    (hcenter : ∀b j,torusDistance L (anchor j) (gridCenter L (center (owner b j)))≤1)
    (path : ∀b j,V (owner b j) → allowed j) (hpath : ∀b j,Measurable (path b j))
    (μ : ∀i,Measure (V i)) [∀i,IsProbabilityMeasure (μ i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (U : Finset I)
    (hdom : ∀b j,owner b j∈U → (μ (owner b j)).map (path b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) :
    UniformInsertionOn (physicalSparseChecks r anchor allowed owner path hpath) μ a U := by
  have hd : ∀i∈U,(Finset.univ.filter (fun e : physicalEdges anchor ↦
      owner e.1 e.2.val.1=i ∨ owner e.1 e.2.val.2=i)).card≤4*(49^3*M) := by
    intro i _
    exact physicalSparseChecks_degree hL anchor center M hm owner howner hcenter i
  exact factorPath_insertion (L:=L) allowed owner howner
    (fun e : physicalEdges anchor ↦ e.1)
    (fun e : physicalEdges anchor ↦ e.2.val.1)
    (fun e : physicalEdges anchor ↦ e.2.val.2)
    (fun e : physicalEdges anchor ↦ e.2.property.1) path hpath r μ P G q a
    (4*(49^3*M)) U hdom hq hd hsmall

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
omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
lemma routeOwner_injective (label : J → I) (hlabel : Function.Injective label) (b : Bool) :
    Function.Injective (routeOwner σ label b) := by
  cases b
  · exact hlabel
  · exact σ.injective.comp hlabel

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routePath_unselected (allowed : J → Set C(Time,Point)) (label : J → I)
    (get : ∀j,X (label j) → allowed j) (j : J) (hj : label j∉S)
    (p : ∀i,X i×X (σ.symm i)) :
    routePath σ S hfix allowed label get true j (p (routeOwner σ label true j))=
      get j (p (label j)).1 := by
  simp only [routePath,dite_eq_right hj]
  exact congrArg (get j) (fiberEquiv_pi (hfix (label j) hj) (fun i ↦ (p i).1))

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma routeChecks_outside (r : ℝ) (anchor : J → Torus L) (allowed : J → Set C(Time,Point))
    (label : J → I) (get : ∀j,X (label j) → allowed j) (hg : ∀j,Measurable (get j))
    (o : Finset I) (hso : Disjoint S o) (p : ∀i,X i×X (σ.symm i))
    (hp : (fun i ↦ (p i).1)∈retainedEvent (primaryChecks r anchor allowed label get hg) o) :
    p∈retainedEvent (routeChecks σ S hfix r anchor allowed label get hg) o := by
  intro e he
  rcases e with ⟨b,⟨⟨j,k⟩,hjk,hnear⟩⟩
  cases b
  · exact hp (false,⟨(j,k),hjk,hnear⟩) he
  · have hj : label j∉S := by
      intro hs
      exact Finset.disjoint_left.mp hso ((move_mem_iff σ S hfix (label j)).mpr hs)
        (he (by simp [routeChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner]))
    have hk : label k∉S := by
      intro hs
      exact Finset.disjoint_left.mp hso ((move_mem_iff σ S hfix (label k)).mpr hs)
        (he (by simp [routeChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner]))
    have he' : (primaryChecks r anchor allowed label get hg (false,⟨(j,k),hjk,hnear⟩)).support⊆o := by
      simpa [routeChecks,primaryChecks,physicalSparseChecks,factorPathCheck,dependentCheck,routeOwner,
        hfix (label j) hj,hfix (label k) hk] using he
    have hh := hp (false,⟨(j,k),hjk,hnear⟩) he'
    change ¬TrialCollision r (projectCurve L (routePath σ S hfix allowed label get true k
      (p (routeOwner σ label true k))).val) (routePath σ S hfix allowed label get true j
      (p (routeOwner σ label true j))).val
    rw [routePath_unselected σ S hfix allowed label get j hj,
      routePath_unselected σ S hfix allowed label get k hk]
    exact hh

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

omit [Fintype J] [DecidableEq J] in
lemma routeChecks_frozen_outside (U o : Finset I) (hSU : S⊆U) (hSo : Disjoint S o)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg) (Finset.univ\U))
    (y : ∀i,X i) (u : ∀i,X (σ.symm i))
    (hy : y∈retainedEvent (frozenChecks (primaryChecks r anchor allowed label get hg) U x) o) :
    (fun i ↦ (y i,u i))∈retainedEvent (frozenChecks (routeChecks σ S hfix r anchor allowed label get hg)
      U (fun i ↦ (x i,z i))) o := by
  have hSc : Disjoint S (Finset.univ\U) := Finset.disjoint_left.mpr (fun i hi hic ↦
    (Finset.mem_sdiff.mp hic).2 (hSU hi))
  have hz := routeChecks_outside σ S hfix r anchor allowed label get hg (Finset.univ\U) hSc
    (fun i ↦ (x i,z i)) hx
  apply (frozen_retained _ U o _ _ hz).mpr
  have hyo := (frozen_retained _ U o _ _ hx).mp hy
  apply routeChecks_outside σ S hfix r anchor allowed label get hg (o∪(Finset.univ\U))
    (Finset.disjoint_union_right.mpr ⟨hSo,hSc⟩)
  convert hyo using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  by_cases hi : i∈U <;> simp only [freezeOutside,hi,ite_true,ite_false]

end HardSphere.Bridge

end
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

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalSupported
attribute [-instance] _root_.OAI.HardSphere.Groups.labelOptionSpace
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

lemma routeDensityBound_ne_top {t : ℝ} (ht : 0<t) : routeDensityBound t≠⊤ := by
  have ha : (ENNReal.ofReal (9/10:ℝ))≠0 := by positivity
  have hb : (ENNReal.ofReal (49/50:ℝ))≠0 := by positivity
  have hc := (midpointLower_pos ht 13).ne'
  simp only [routeDensityBound,ne_eq,max_eq_top]
  exact not_or.mpr ⟨by norm_num,ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ha)
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hb) (ENNReal.inv_ne_top.mpr hc))⟩

lemma one_le_routeDensityBound (t : ℝ) : 1 ≤ routeDensityBound t :=
  le_trans (by norm_num) (le_max_left _ _)

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

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_RouteCenters
attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Comparison CellOrbital
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [Fintype J] [DecidableEq J] in
lemma routeEmbedding_center {K n : ℕ} (home : J→Fin 3→Fin K)
    (labels : Fin n↪J) (v : Fin (n+1)→Fin 3→Fin K)
    (hh : ∀i,home (labels i)=v i.castSucc) (i : Fin (n+1)) :
    slotCenter home (v (Fin.last n)) (routeEmbedding labels i)=v i := by
  by_cases hi : i.val<n
  · have he : i=(⟨i.val,hi⟩ : Fin n).castSucc := Fin.ext rfl
    rw [he,routeEmbedding_castSucc]
    exact hh _
  · have he : i=Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [he,routeEmbedding_last]
    rfl

omit [Fintype J] [DecidableEq J] in
lemma route_two_center_bounds {K n : ℕ} {L : Length}
    (home : J→Fin 3→Fin K) (labels : Fin (n+1)↪J)
    (v : Fin (n+2)→Fin 3→Fin K)
    (hh : ∀i,home (labels i)=v i.castSucc)
    (ha : ∀i : Fin (n+1),torusDistance L (gridCenter L (v i.castSucc))
      (gridCenter L (v i.succ))≤1) :
    (∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v (Fin.last (n+1))) (routePermutation labels (some j))))≤1) ∧
    (∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v 0) ((routePermutation labels).symm (some j))))≤1) := by
  have hf : ∀j,torusDistance L (gridCenter L (home j))
      (gridCenter L (slotCenter home (v (Fin.last (n+1))) (routePermutation labels (some j))))≤1 := by
    intro j
    by_cases hj : ∃i,labels i=j
    · obtain ⟨i,rfl⟩ := hj
      rw [routePermutation_label,routeEmbedding_center home labels v hh,hh i]
      exact ha i
    · have hnot : some j∉routeSlots labels := by
        rw [routeSlots_exact]
        simp only [Finset.mem_insert,Option.some_ne_none,Finset.mem_image,Finset.mem_univ,
          true_and,false_or,not_exists]
        intro i hi
        exact hj ⟨i,Option.some.inj hi⟩
      rw [routePermutation_fixed labels _ hnot]
      change torusDistance L (gridCenter L (home j)) (gridCenter L (home j))≤1
      simp [torusDistance]
  refine ⟨hf,?_⟩
  intro j
  cases he : (routePermutation labels).symm (some j) with
  | none =>
    have hj : j=labels 0 := by
      have hh' := congrArg (routePermutation labels) he
      rw [Equiv.apply_symm_apply,routePermutation_star] at hh'
      exact Option.some.inj hh'
    rw [hj,hh 0]
    change torusDistance L (gridCenter L (v 0)) (gridCenter L (v 0))≤1
    simp [torusDistance]
  | some k =>
    have hek : routePermutation labels (some k)=some j := by
      rw [←he,Equiv.apply_symm_apply]
    have hk := hf k
    rw [hek] at hk
    change torusDistance L (gridCenter L (home j)) (gridCenter L (home k))≤1
    change torusDistance L (gridCenter L (home k)) (gridCenter L (home j))≤1 at hk
    rw [torusDistance_comm]
    exact hk

lemma slotCenter_fiber {K : ℕ} (home : J→Fin 3→Fin K) (v : Fin 3→Fin K)
    (M : ℕ) (hm : ∀w,(Finset.univ.filter (fun j ↦ home j=w)).card≤M) (w : Fin 3→Fin K) :
    (Finset.univ.filter (fun i ↦ slotCenter home v i=w)).card≤M+1 := by
  have hs : Finset.univ.filter (fun i ↦ slotCenter home v i=w) ⊆
      insert none ((Finset.univ.filter (fun j ↦ home j=w)).image some) := by
    intro i hi
    cases i with
    | none => exact Finset.mem_insert_self _ _
    | some j =>
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩,rfl⟩)
  exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right (Finset.card_image_le.trans (hm w)) 1))

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_SeparatedPhysical
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasurePointMidpointNoise _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [Fintype C] in
lemma separated_of_no_crossing (checks : C → LocalCheck X) (s t : Finset I)
    (h : ∀c,∀i∈(checks c).support,∀j∈(checks c).support,i∈s → j∈t → False) :
    SeparatedChecks checks s t := by
  intro c hc
  by_cases hs : (checks c).support⊆s
  · exact Or.inl hs
  · right
    obtain ⟨j,hj,hjs⟩ := Finset.not_subset.mp hs
    have hjt := (Finset.mem_union.mp (hc hj)).resolve_left hjs
    intro i hi
    exact (Finset.mem_union.mp (hc hi)).resolve_left (fun his ↦ h c i hi j hj his hjt)

omit [Fintype I] [Fintype C] in
lemma frozen_separated_of_no_crossing (checks : C → LocalCheck X) (U s t : Finset I)
    (x : ∀i,X i)
    (h : ∀c,∀i∈(checks c).support,∀j∈(checks c).support,i∈s → j∈t → False) :
    SeparatedChecks (frozenChecks checks U x) s t := by
  apply separated_of_no_crossing
  intro c i hi j hj his hjt
  exact h c.val i (Finset.mem_inter.mp hi).1 j (Finset.mem_inter.mp hj).1 his hjt
end HardSphere.Comparison
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {V : I → Type*} [∀i,MeasurableSpace (V i)]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma physical_support_near (r : ℝ) (anchor : J → Torus L) (center : I → Torus L)
    (allowed : J → Set C(Time,Point)) (owner : Bool → J → I)
    (hc : ∀b j,torusDistance L (anchor j) (center (owner b j))≤1)
    (path : ∀b j,V (owner b j)→allowed j) (hm : ∀b j,Measurable (path b j))
    (e : physicalEdges anchor) (i j : I)
    (hi : i∈(physicalSparseChecks r anchor allowed owner path hm e).support)
    (hj : j∈(physicalSparseChecks r anchor allowed owner path hm e).support) :
    torusDistance L (center i) (center j)≤23 := by
  have hbound := incident_centers_close anchor (fun k ↦ center (owner e.1 k)) id
    (hc e.1) e.2.val.1 e.2.val.2 e.2.property.2
  have hie : i=owner e.1 e.2.val.1 ∨ i=owner e.1 e.2.val.2 := by
    simpa only [physicalSparseChecks,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton] using hi
  have hje : j=owner e.1 e.2.val.1 ∨ j=owner e.1 e.2.val.2 := by
    simpa only [physicalSparseChecks,factorPathCheck,dependentCheck,Finset.mem_insert,Finset.mem_singleton] using hj
  rcases hie with rfl|rfl <;> rcases hje with rfl|rfl
  · simp [torusDistance]
  · exact hbound
  · simpa only [id_eq,torusDistance_comm L (center (owner e.1 e.2.val.2))] using hbound
  · simp [torusDistance]

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma physical_frozen_separated (r : ℝ) (anchor : J → Torus L) (center : I → Torus L)
    (allowed : J → Set C(Time,Point)) (owner : Bool → J → I)
    (hc : ∀b j,torusDistance L (anchor j) (center (owner b j))≤1)
    (path : ∀b j,V (owner b j)→allowed j) (hm : ∀b j,Measurable (path b j))
    (U s t : Finset I) (x : ∀i,V i)
    (hfar : ∀i∈s,∀j∈t,23<torusDistance L (center i) (center j)) :
    SeparatedChecks (frozenChecks (physicalSparseChecks r anchor allowed owner path hm) U x) s t := by
  apply frozen_separated_of_no_crossing
  intro e i hi j hj his hjt
  exact (not_le_of_gt (hfar i his j hjt)) (physical_support_near r anchor center allowed owner hc path hm e i j hi hj)

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_FirstCoordinate
attribute [-instance] _root_.OAI.HardSphere.Comparison.proposalKernel_finite _root_.OAI.HardSphere.Groups.labelOptionSpace
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
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]
  {X : I → Type*} [∀i,MeasurableSpace (X i)]
omit [Fintype C] in
lemma frozen_uniformInsertion_on (checks : C → LocalCheck X) (U S : Finset I)
    (hSU : S⊆U) (x : ∀i,X i) (μ : ∀i,Measure (X i)) {a : ℝ≥0∞}
    (h : UniformInsertionOn checks μ a S) :
    UniformInsertionOn (frozenChecks checks U x) μ a S := by
  intro i hi s his y
  have hin : i∉s∪(Finset.univ\U) := by simp [Finset.mem_union,his,hSU hi]
  apply (h i hi (s∪(Finset.univ\U)) hin (freezeOutside U x y)).trans
  apply lintegral_mono
  intro v
  dsimp only
  rw [←freezeOutside_update U x y (hSU hi) v]
  by_cases hp : freezeOutside U x (Function.update y i v)∈insertionEvent checks (s∪(Finset.univ\U)) i
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (frozen_insertion checks U s x (Function.update y i v) i hp)]
  · rw [Set.indicator_of_notMem hp]
    exact bot_le
end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteInsertion
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]
lemma route_insertion {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (center : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ center i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
    (hc : ∀b j,torusDistance L (anchor j) (gridCenter L (center (routeOwner σ label b j)))≤1)
    (ν : ∀i,Measure (X i×X (σ.symm i))) [∀i,IsProbabilityMeasure (ν i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞)
    (hdom : ∀b j,routeOwner σ label b j∈S → (ν (routeOwner σ label b j)).map
      (routePath σ S hfix allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) :
    UniformInsertionOn (routeChecks σ S hfix r anchor allowed label get hg) ν a S := by
  unfold routeChecks
  exact physicalSparseChecks_insertion (V:=fun i ↦ X i×X (σ.symm i)) hL r anchor center M hm allowed (routeOwner σ label)
    (routeOwner_injective σ label hl) hc (routePath σ S hfix allowed label get)
    (routePath_measurable σ S hfix allowed label get hg) ν P G q a S hdom hq hsmall

omit [Fintype I] [Fintype J] [DecidableEq J] in
lemma route_frozen_separated (r : ℝ) (anchor : J→Torus L) (center : I→Torus L)
    (allowed : J→Set C(Time,Point)) (label : J→I)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ : Equiv.Perm I) (S : Finset I) (hfix : ∀i,i∉S → σ i=i)
    (hc : ∀b j,torusDistance L (anchor j) (center (routeOwner σ label b j))≤1)
    (U s t : Finset I) (x : ∀i,X i×X (σ.symm i))
    (hfar : ∀i∈s,∀j∈t,23<torusDistance L (center i) (center j)) :
    SeparatedChecks (frozenChecks (routeChecks σ S hfix r anchor allowed label get hg) U x) s t := by
  unfold routeChecks
  exact physical_frozen_separated (V:=fun i ↦ X i×X (σ.symm i)) r anchor center allowed (routeOwner σ label) hc
    (routePath σ S hfix allowed label get) (routePath_measurable σ S hfix allowed label get hg) U s t x hfar

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

theorem physical_route_cancellation {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (cent : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ cent i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ τ : Equiv.Perm I) (fs ft cs ct os ot : Finset I)
    (hσ : ∀i,i∉fs∪cs → σ i=i) (hτ : ∀i,i∉ft∪ct → τ i=i)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs∪ft) (cs∪ct))
    (hos : Disjoint (fs∪cs) os) (hot : Disjoint (ft∪ct) ot)
    (hosU : (fs∪cs)∪os=(fs∪ft)∪(cs∪ct))
    (hotU : (ft∪ct)∪ot=(fs∪ft)∪(cs∪ct))
    (hc0 : ∀j,torusDistance L (anchor j) (gridCenter L (cent (label j)))≤1)
    (hcσ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (σ (label j))))≤1)
    (hcτ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (τ (label j))))≤1)
    (hfar0 : ∀i∈fs,∀j∈ft,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (hfarσ : ∀i∈fs,∀j∈os,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (hfarτ : ∀i∈ft,∀j∈ot,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (τ.symm i))) [∀i,IsFiniteKernel (η i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (ha : 0<a) (ha1 : a≤1)
    (hκb : ∀i x,κ i x Set.univ≤G)
    (hκm : ∀i,∫⁻x,κ i x Set.univ ∂μ i=1)
    (hηm : ∀i,∫⁻x,η i x Set.univ ∂μ i=1)
    (hdom0 : ∀j,label j∈(fs∪ft)∪(cs∪ct) → (μ (label j)).map (get j)≤G • P j)
    (hdomσ : ∀b j,routeOwner σ label b j∈fs∪cs →
      ((μ (routeOwner σ label b j)).compProd (κ (routeOwner σ label b j))).map
        (routePath σ (fs∪cs) hσ allowed label get b j)≤G • P j)
    (hdomτ : ∀b j,routeOwner τ label b j∈ft∪ct →
      ((μ (routeOwner τ label b j)).compProd (η (routeOwner τ label b j))).map
        (routePath τ (ft∪ct) hτ allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1)
    (x : ∀i,X i) (z : ∀i,X (σ.symm i)) (w : ∀i,X (τ.symm i))
    (hx : x∈retainedEvent (primaryChecks r anchor allowed label get hg)
      (Finset.univ\((fs∪ft)∪(cs∪ct)))) :
    let U := (fs∪ft)∪(cs∪ct)
    let Ref := frozenChecks (primaryChecks r anchor allowed label get hg) U x
    let ChS := frozenChecks (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg) U (fun i ↦ (x i,z i))
    let ChT := frozenChecks (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg) U (fun i ↦ (x i,w i))
    lmarginal μ U (fun y ↦ checkWeight Ref U y *
      conditionalLikelihood Ref ChS μ κ (fs∪cs) os y z *
      conditionalLikelihood Ref ChT μ η (ft∪ct) ot y w) x /
      checkNormalizer Ref μ U x≤G^(cs∩ct).card/a^(2*(cs.card+ct.card)) := by
  let U := (fs∪ft)∪(cs∪ct)
  have hsU : fs∪cs⊆U := by change fs∪cs⊆(fs∪ft)∪(cs∪ct);rw [←hosU];exact Finset.subset_union_left
  have htU : ft∪ct⊆U := by change ft∪ct⊆(fs∪ft)∪(cs∪ct);rw [←hotU];exact Finset.subset_union_left
  have hcS : ∀b j,torusDistance L (anchor j) (gridCenter L (cent (routeOwner σ label b j)))≤1 := by
    intro b j;cases b;exact hc0 j;exact hcσ j
  have hcT : ∀b j,torusDistance L (anchor j) (gridCenter L (cent (routeOwner τ label b j)))≤1 := by
    intro b j;cases b;exact hc0 j;exact hcτ j
  let hprobκ : ∀i,IsProbabilityMeasure ((μ i).compProd (κ i)) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (κ i) (hκm i)
  let hprobη : ∀i,IsProbabilityMeasure ((μ i).compProd (η i)) :=
    fun i ↦ isProbabilityMeasure_compProd_of_mass (μ i) (η i) (hηm i)
  have hRef' : UniformInsertionOn (primaryChecks r anchor allowed label get hg) μ a U :=
    physicalSparseChecks_insertion (V:=X) hL r anchor cent M hm allowed (fun _ ↦ label)
      (fun _ ↦ hl) (fun _ ↦ hc0) (fun _ ↦ get) (fun _ ↦ hg) μ P G q a U
      (fun _ ↦ hdom0) hq hsmall
  have hS' : UniformInsertionOn (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg)
      (fun i ↦ (μ i).compProd (κ i)) a (fs∪cs) :=
    route_insertion hL r anchor cent M hm allowed label hl get hg σ (fs∪cs) hσ hcS _ P G q a hdomσ hq hsmall
  have hT' : UniformInsertionOn (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg)
      (fun i ↦ (μ i).compProd (η i)) a (ft∪ct) :=
    route_insertion hL r anchor cent M hm allowed label hl get hg τ (ft∪ct) hτ hcT _ P G q a hdomτ hq hsmall
  apply conditional_cancellation _ _ _ μ κ η fs ft cs ct os ot hff hfn hos hot hosU hotU
    ha ha1 hκb hκm hηm
  · exact frozen_uniformInsertion _ U x μ hRef'
  · exact frozen_uniformInsertion_on _ U (fs∪cs) hsU _ _ hS'
  · exact frozen_uniformInsertion_on _ U (ft∪ct) htU _ _ hT'
  · exact physical_frozen_separated (V:=X) r anchor (fun i ↦ gridCenter L (cent i)) allowed
      (fun _ ↦ label) (fun _ ↦ hc0) (fun _ ↦ get) (fun _ ↦ hg) U fs ft x hfar0
  · exact route_frozen_separated r anchor (fun i ↦ gridCenter L (cent i)) allowed label get hg σ (fs∪cs) hσ hcS U fs os _ hfarσ
  · exact route_frozen_separated r anchor (fun i ↦ gridCenter L (cent i)) allowed label get hg τ (ft∪ct) hτ hcT U ft ot _ hfarτ
  · exact fun y u hy ↦ routeChecks_frozen_outside σ (fs∪cs) hσ r anchor allowed label get hg
      U os hsU hos x z hx y u hy
  · exact fun y u hy ↦ routeChecks_frozen_outside τ (ft∪ct) hτ r anchor allowed label get hg
      U ot htU hot x w hx y u hy

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteMarginals
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
attribute [local instance] Classical.propDecidable

omit [Fintype J] in
lemma route_selected_accessible {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (labels : Fin n↪J) (d : PhysicalDatum N K M G L)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (j : J) (h : some j∈routeSlots labels) :
    datumAccessible hL g m t r R C S u (particle j) d := by
  rw [routeSlots_exact] at h
  rcases Finset.mem_insert.mp h with h|h
  · contradiction
  · obtain ⟨i,_,he⟩ := Finset.mem_image.mp h
    rw [←Option.some.inj he]
    exact ha i

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_PhysicalCollisionReference
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
attribute [local instance] Classical.propDecidable
variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in
lemma physicalCollisionReference_eq {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J)
    (ha : datumAccessible hL g m t r R C S u (particle j) d) (v : Fin 3→Fin K) :
    physicalCollisionReference hL g m t r R C S u particle d j=
      physicalSlotOn hL g m t r R C S u particle v d (some j) := by
  change (if datumAccessible hL g m t r R C S u (particle j) d then _ else _) = _
  rw [ite_eq_left ha]
  rfl

omit [DecidableEq J] in
lemma physical_primary_domination {N K M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J→Fin N) (d : PhysicalDatum N K M G L) (j : J)
    (ha : datumAccessible hL g m t r R C S u (particle j) d) (v : Fin 3→Fin K) :
    (physicalSlotOn hL g m t r R C S u particle v d (some j)).map (fun f ↦ f)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j := by
  rw [Measure.map_id',physicalCollisionReference_eq hL g m t r R C S u particle d j ha v]
  intro A
  rw [Measure.smul_apply]
  exact le_trans (le_of_eq (one_mul _).symm) (mul_le_mul_left (one_le_routeDensityBound t) _)

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteMass
attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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

omit [Fintype J] [DecidableEq J] in
lemma physical_owner_centers {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (particle : J→Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (d : PhysicalDatum N K M G L)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (hneigh : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1) :
    ∀b j,torusDistance L (projectPoint L (anchorPoint (datumHome hL d (particle j))))
      (gridCenter L (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))
        (routeOwner (routePermutation labels) some b j)))≤1 := by
  intro b j
  cases b
  · change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  · exact (route_two_center_bounds (fun j ↦ datumHome hL d (particle j)) labels v hhome hneigh).1 j

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_FrozenLikelihood
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
  {X : I → Type*} [∀i,MeasurableSpace (X i)]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_updateFinset (U s : Finset I) (hs : s⊆U) (x y : ∀i,X i) (v : ∀i:s,X i) :
    freezeOutside U x (Function.updateFinset y s v)=Function.updateFinset (freezeOutside U x y) s v := by
  funext i
  by_cases hi : i∈s
  · simp [freezeOutside,Function.updateFinset,hi,hs hi]
  · simp [freezeOutside,Function.updateFinset,hi]

omit [Fintype C] in
lemma frozen_partialNormalizer (checks : C → LocalCheck X) (μ : ∀i,Measure (X i))
    (U s o : Finset I) (hs : s⊆U) (x y : ∀i,X i)
    (hx : x∈retainedEvent checks (Finset.univ\U)) :
    partialNormalizer (frozenChecks checks U x) μ s o y=
      partialNormalizer checks μ s (o∪(Finset.univ\U)) (freezeOutside U x y) := by
  apply lintegral_congr
  intro v
  rw [frozen_checkWeight checks U (s∪o) x _ hx,freezeOutside_updateFinset U s hs]
  simp only [Finset.union_assoc]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_pair {Z : I → Type*} (U : Finset I) (x y : ∀i,X i) (z u : ∀i,Z i) :
    freezeOutside U (fun i ↦ (x i,z i)) (fun i ↦ (y i,u i))=
      fun i ↦ (freezeOutside U x y i,freezeOutside U z u i) := by
  funext i
  by_cases hi : i∈U <;> simp [freezeOutside,hi]

omit [Fintype C] in
lemma frozen_conditionalDensity {Z : I → Type*} [∀i,MeasurableSpace (Z i)]
    (checks : C → LocalCheck (fun i ↦ X i×Z i))
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (U s o : Finset I) (hs : s⊆U) (x y : ∀i,X i) (z u : ∀i,Z i)
    (hx : (fun i ↦ (x i,z i))∈retainedEvent checks (Finset.univ\U)) :
    conditionalDensity (frozenChecks checks U (fun i ↦ (x i,z i))) κ s o y u=
      conditionalDensity checks κ s (o∪(Finset.univ\U)) (freezeOutside U x y) (freezeOutside U z u) := by
  unfold conditionalDensity lmarginal
  have hκ : (fun i:s ↦ κ i (freezeOutside U x y i))=(fun i:s ↦ κ i (y i)) := by
    funext i;simp only [freezeOutside,ite_eq_left (hs i.property)]
  rw [hκ]
  apply lintegral_congr
  intro v
  dsimp only
  rw [frozen_checkWeight checks U (s∪o) _ _ hx,freezeOutside_pair,freezeOutside_updateFinset U s hs]
  simp only [Finset.union_assoc]

omit [Fintype C] in
lemma frozen_conditionalLikelihood {Z : I → Type*} [∀i,MeasurableSpace (Z i)]
    {R : Type*} [Fintype R] (reference : R → LocalCheck X)
    (checks : C → LocalCheck (fun i ↦ X i×Z i))
    (μ : ∀i,Measure (X i)) (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (U s o : Finset I) (hs : s⊆U) (x y : ∀i,X i) (z u : ∀i,Z i)
    (hx : x∈retainedEvent reference (Finset.univ\U))
    (hz : (fun i ↦ (x i,z i))∈retainedEvent checks (Finset.univ\U)) :
    conditionalLikelihood (frozenChecks reference U x) (frozenChecks checks U (fun i ↦ (x i,z i))) μ κ s o y u=
      conditionalLikelihood reference checks μ κ s (o∪(Finset.univ\U)) (freezeOutside U x y) (freezeOutside U z u) := by
  unfold conditionalLikelihood
  rw [frozen_partialNormalizer reference μ U s o hs x y hx,
    frozen_partialNormalizer checks _ U s o hs _ _ hz,
    freezeOutside_pair,
    frozen_conditionalDensity checks κ U s o hs x y z u hz]

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
variable {I R C D : Type*} [Fintype I] [DecidableEq I] [Fintype R] [Fintype C] [Fintype D]
  {X Z W : I→Type*} [∀i,MeasurableSpace (X i)] [∀i,MeasurableSpace (Z i)]
  [∀i,MeasurableSpace (W i)]

omit [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma freezeOutside_self (U : Finset I) (x : ∀i,X i) : freezeOutside U x x=x := by
  funext i
  by_cases hi : i∈U <;> simp [freezeOutside,hi]

lemma local_complement (s o U : Finset I) (hso : Disjoint s o) (hU : s∪o=U) :
    o∪(Finset.univ\U)=Finset.univ\s := by
  ext i
  have hd := Finset.disjoint_left.mp hso
  simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  rw [←hU]
  simp only [Finset.mem_union]
  constructor
  · rintro (ho|hnot)
    · exact fun hs ↦ hd hs ho
    · exact fun hs ↦ hnot (Or.inl hs)
  · intro hs
    by_cases ho : i∈o
    · exact Or.inl ho
    · exact Or.inr (not_or.mpr ⟨hs,ho⟩)

theorem frozen_pair_mean_integrates
    (reference : R→LocalCheck X) (checks : C→LocalCheck (fun i ↦ X i×Z i))
    (other : D→LocalCheck (fun i ↦ X i×W i))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (Z i)) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (W i)) [∀i,IsFiniteKernel (η i)]
    (s t os ot U : Finset I) (hs : s⊆U) (ht : t⊆U)
    (hso : Disjoint s os) (hto : Disjoint t ot) (hsU : s∪os=U) (htU : t∪ot=U)
    (z : ∀i,Z i) (w : ∀i,W i)
    (hS : ∀x,x∈retainedEvent reference (Finset.univ\U) →
      (fun i ↦ (x i,z i))∈retainedEvent checks (Finset.univ\U))
    (hT : ∀x,x∈retainedEvent reference (Finset.univ\U) →
      (fun i ↦ (x i,w i))∈retainedEvent other (Finset.univ\U))
    (A : ℝ≥0∞) (hA : A≠⊤)
    (hlocal : ∀x,x∈retainedEvent reference (Finset.univ\U) →
      let Ref := frozenChecks reference U x
      let ChS := frozenChecks checks U (fun i ↦ (x i,z i))
      let ChT := frozenChecks other U (fun i ↦ (x i,w i))
      lmarginal μ U (fun y ↦ checkWeight Ref U y *
        conditionalLikelihood Ref ChS μ κ s os y z *
        conditionalLikelihood Ref ChT μ η t ot y w) x /
        checkNormalizer Ref μ U x≤A) :
    (∫⁻x,conditionalLikelihood reference checks μ κ s (Finset.univ\s) x z *
      conditionalLikelihood reference other μ η t (Finset.univ\t) x w
      ∂conditionedMeasure (Measure.pi μ) (retainedEvent reference Finset.univ))≤A := by
  apply local_mean_integrates reference μ U _
    ((measurable_conditionalLikelihood reference checks μ κ _ _ z).mul
      (measurable_conditionalLikelihood reference other μ η _ _ w)) A hA
  intro x hx
  rw [←frozen_local_mean reference μ U x hx]
  have h := hlocal x hx
  dsimp only at h
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  apply congrArg (fun f ↦ lmarginal μ U f x)
  funext y
  rw [frozen_conditionalLikelihood reference checks μ κ U s os hs x y z z hx (hS x hx),
    frozen_conditionalLikelihood reference other μ η U t ot ht x y w w hx (hT x hx),
    freezeOutside_self,freezeOutside_self,local_complement s os U hso hsU,
    local_complement t ot U hto htU]
  exact (mul_assoc _ _ _).symm

end HardSphere.Comparison

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PhysicalSecondMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
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
open Wiener GaussianPacking Comparison Groups CellOrbital
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I → Type*} [∀i,MeasurableSpace (X i)]

theorem physical_route_second_moment {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (cent : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ cent i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ τ : Equiv.Perm I) (fs ft cs ct os ot : Finset I)
    (hσ : ∀i,i∉fs∪cs → σ i=i) (hτ : ∀i,i∉ft∪ct → τ i=i)
    (hff : Disjoint fs ft) (hfn : Disjoint (fs∪ft) (cs∪ct))
    (hos : Disjoint (fs∪cs) os) (hot : Disjoint (ft∪ct) ot)
    (hosU : (fs∪cs)∪os=(fs∪ft)∪(cs∪ct))
    (hotU : (ft∪ct)∪ot=(fs∪ft)∪(cs∪ct))
    (hc0 : ∀j,torusDistance L (anchor j) (gridCenter L (cent (label j)))≤1)
    (hcσ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (σ (label j))))≤1)
    (hcτ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (τ (label j))))≤1)
    (hfar0 : ∀i∈fs,∀j∈ft,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (hfarσ : ∀i∈fs,∀j∈os,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (hfarτ : ∀i∈ft,∀j∈ot,23<torusDistance L (gridCenter L (cent i)) (gridCenter L (cent j)))
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (τ.symm i))) [∀i,IsFiniteKernel (η i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (ha : 0<a) (ha1 : a≤1)
    (hκb : ∀i x,κ i x Set.univ≤G)
    (hκm : ∀i,∫⁻x,κ i x Set.univ ∂μ i=1)
    (hηm : ∀i,∫⁻x,η i x Set.univ ∂μ i=1)
    (hdom0 : ∀j,label j∈(fs∪ft)∪(cs∪ct) → (μ (label j)).map (get j)≤G • P j)
    (hdomσ : ∀b j,routeOwner σ label b j∈fs∪cs →
      ((μ (routeOwner σ label b j)).compProd (κ (routeOwner σ label b j))).map
        (routePath σ (fs∪cs) hσ allowed label get b j)≤G • P j)
    (hdomτ : ∀b j,routeOwner τ label b j∈ft∪ct →
      ((μ (routeOwner τ label b j)).compProd (η (routeOwner τ label b j))).map
        (routePath τ (ft∪ct) hτ allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k → ∀g : allowed k,P j {f | TrialCollision r (projectCurve L g.val) f.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1)
    (hG : G≠⊤) (z : ∀i,X (σ.symm i)) (w : ∀i,X (τ.symm i)) :
    (∫⁻x,conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg) μ κ
      (fs∪cs) (Finset.univ\(fs∪cs)) x z *
      conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg) μ η
      (ft∪ct) (Finset.univ\(ft∪ct)) x w
      ∂conditionedMeasure (Measure.pi μ)
        (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))≤
      G^(cs∩ct).card/a^(2*(cs.card+ct.card)) := by
  let U := (fs∪ft)∪(cs∪ct)
  have hsU : fs∪cs⊆U := by rw [show U=(fs∪cs)∪os from hosU.symm];exact Finset.subset_union_left
  have htU : ft∪ct⊆U := by rw [show U=(ft∪ct)∪ot from hotU.symm];exact Finset.subset_union_left
  have hsC : Disjoint (fs∪cs) (Finset.univ\U) := Finset.disjoint_left.mpr
    (fun i hi hic ↦ (Finset.mem_sdiff.mp hic).2 (hsU hi))
  have htC : Disjoint (ft∪ct) (Finset.univ\U) := Finset.disjoint_left.mpr
    (fun i hi hic ↦ (Finset.mem_sdiff.mp hic).2 (htU hi))
  apply frozen_pair_mean_integrates
    (primaryChecks r anchor allowed label get hg)
    (routeChecks σ (fs∪cs) hσ r anchor allowed label get hg)
    (routeChecks τ (ft∪ct) hτ r anchor allowed label get hg)
    μ κ η (fs∪cs) (ft∪ct) os ot U hsU htU hos hot hosU hotU z w
  · intro x hx
    exact routeChecks_outside σ (fs∪cs) hσ r anchor allowed label get hg _ hsC
      (fun i ↦ (x i,z i)) hx
  · intro x hx
    exact routeChecks_outside τ (ft∪ct) hτ r anchor allowed label get hg _ htC
      (fun i ↦ (x i,w i)) hx
  · exact ENNReal.div_ne_top (ENNReal.pow_ne_top hG)
      (pow_ne_zero _ (ne_of_gt ha))
  · intro x hx
    exact physical_route_cancellation hL r anchor cent M hm allowed label hl get hg
      σ τ fs ft cs ct os ot hσ hτ hff hfn hos hot hosU hotU hc0 hcσ hcτ
      hfar0 hfarσ hfarτ μ κ η P G q a ha ha1 hκb hκm hηm hdom0 hdomσ hdomτ
      hq hsmall x z w hx

end HardSphere.Bridge

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_RouteSecondMoment
attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Comparison.parameterTargetKernel_finite _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotOn_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Bridge
open Wiener GaussianPacking Comparison Groups CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {L : Length} {X : I→Type*} [∀i,MeasurableSpace (X i)]

theorem physical_route_encounter_moment {K : ℕ} [NeZero K] (hL : L.val=(K:ℝ))
    (r : ℝ) (anchor : J→Torus L) (cent : I→Fin 3→Fin K)
    (M : ℕ) (hm : ∀v,(Finset.univ.filter (fun i : I ↦ cent i=v)).card≤M)
    (allowed : J→Set C(Time,Point)) (label : J→I) (hl : Function.Injective label)
    (get : ∀j,X (label j)→allowed j) (hg : ∀j,Measurable (get j))
    (σ τ : Equiv.Perm I) (s t : Finset I)
    (hσ : ∀i,i∉s→σ i=i) (hτ : ∀i,i∉t→τ i=i)
    (hc0 : ∀j,torusDistance L (anchor j) (gridCenter L (cent (label j)))≤1)
    (hcσ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (σ (label j))))≤1)
    (hcτ : ∀j,torusDistance L (anchor j) (gridCenter L (cent (τ (label j))))≤1)
    (μ : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (μ i)]
    (κ : ∀i,Kernel (X i) (X (σ.symm i))) [∀i,IsFiniteKernel (κ i)]
    (η : ∀i,Kernel (X i) (X (τ.symm i))) [∀i,IsFiniteKernel (η i)]
    (P : ∀j,Measure (allowed j)) (G q a : ℝ≥0∞) (ha : 0<a) (ha1 : a≤1)
    (hκb : ∀i x,κ i x univ≤G)
    (hκm : ∀i,∫⁻x,κ i x univ ∂μ i=1)
    (hηm : ∀i,∫⁻x,η i x univ ∂μ i=1)
    (hdom0 : ∀j,label j∈s∪t→(μ (label j)).map (get j)≤G • P j)
    (hdomσ : ∀b j,routeOwner σ label b j∈s→
      ((μ (routeOwner σ label b j)).compProd (κ (routeOwner σ label b j))).map
        (routePath σ s hσ allowed label get b j)≤G • P j)
    (hdomτ : ∀b j,routeOwner τ label b j∈t→
      ((μ (routeOwner τ label b j)).compProd (η (routeOwner τ label b j))).map
        (routePath τ t hτ allowed label get b j)≤G • P j)
    (hq : ∀j k,j≠k→∀f:allowed k,P j {p | TrialCollision r (projectCurve L f.val) p.val}≤q)
    (hsmall : a+(4*(49^3*M):ℕ)*(G*q)≤1) (hG : G≠⊤)
    (z : ∀i,X (σ.symm i)) (w : ∀i,X (τ.symm i)) :
    let ns := nearSlots (torusNear K 30) (fun i ↦ Groups.gridSite (cent i)) s t
    let nt := nearSlots (torusNear K 30) (fun i ↦ Groups.gridSite (cent i)) t s
    (∫⁻x,conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks σ s hσ r anchor allowed label get hg) μ κ s (Finset.univ\s) x z *
      conditionalLikelihood (primaryChecks r anchor allowed label get hg)
      (routeChecks τ t hτ r anchor allowed label get hg) μ η t (Finset.univ\t) x w
      ∂conditionedMeasure (Measure.pi μ)
        (retainedEvent (primaryChecks r anchor allowed label get hg) Finset.univ))≤
      G^(s∩t).card/a^(2*(ns.card+nt.card)) := by
  dsimp only
  let e := torusNear K 30
  let c := fun i ↦ Groups.gridSite (cent i)
  let fs := farSlots e c s t
  let ft := farSlots e c t s
  let cs := nearSlots e c s t
  let ct := nearSlots e c t s
  have he : ∀v,e v v := fun v ↦ torusNear_refl K 30 v
  have hs : fs∪cs=s := far_union_near e c s t
  have ht : ft∪ct=t := far_union_near e c t s
  have hU : (fs∪ft)∪(cs∪ct)=s∪t := route_partition_union e c s t
  have hS : ∀i,i∉fs∪cs→σ i=i := by simpa only [hs] using hσ
  have hT : ∀i,i∉ft∪ct→τ i=i := by simpa only [ht] using hτ
  have hdis := far_partition_disjoint e he c s t
  have pathS : routePath σ (fs∪cs) hS allowed label get = routePath σ s hσ allowed label get := by
    congr 1
  have pathT : routePath τ (ft∪ct) hT allowed label get = routePath τ t hτ allowed label get := by
    congr 1
  have checksS : routeChecks σ (fs∪cs) hS r anchor allowed label get hg = routeChecks σ s hσ r anchor allowed label get hg := by
    congr 1
  have checksT : routeChecks τ (ft∪ct) hT r anchor allowed label get hg = routeChecks τ t hτ r anchor allowed label get hg := by
    congr 1
  have hh := physical_route_second_moment hL r anchor cent M hm allowed label hl get hg
    σ τ fs ft cs ct (t\s) (s\t) hS hT hdis.1 hdis.2
    (by rw [hs]; exact Finset.disjoint_left.mpr (fun i hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi))
    (by rw [ht]; exact Finset.disjoint_left.mpr (fun i hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi))
    (by rw [hs,hU]; ext i; simp)
    (by rw [ht,hU]; ext i; simp; tauto)
    hc0 hcσ hcτ
    (fun i hi j hj ↦ physical_far_slots L hL cent s t i j hi (Finset.sdiff_subset hj))
    (fun i hi j hj ↦ physical_far_slots L hL cent s t i j hi (Finset.mem_sdiff.mp hj).1)
    (fun i hi j hj ↦ physical_far_slots L hL cent t s i j hi (Finset.mem_sdiff.mp hj).1)
    μ κ η P G q a ha ha1 hκb hκm hηm
    (by simpa only [hU] using hdom0)
    (by simpa only [hs,pathS] using hdomσ) (by simpa only [ht,pathT] using hdomτ)
    hq hsmall hG z w
  simpa only [hs,ht,checksS,checksT,show cs∩ct=s∩t from commonSlots_near e he c s t] using hh

end HardSphere.Bridge
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalRouteAuxiliary
attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar
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

attribute [instance] PhysicalRouteAux.forward_finite PhysicalRouteAux.backward_finite

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
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physical_first_likelihood_moment_oai {N K M G n l : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N)
    (f : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K)) (steps : Fin (n+1)→Fin 7)
    (f' : Fin (l+1)↪J) (v' : Fin (l+2)→(Fin 3→Fin K)) (steps' : Fin (l+1)→Fin 7)
    (d : PhysicalDatum N K M G L)
    (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
    (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
    (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
    (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
    (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
    (hn : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hn' : ∀k : Fin (l+1),torusDistance L (gridCenter L (v' k.castSucc)) (gridCenter L (v' k.succ))≤1)
    (hend : v' (Fin.last (l+1))=v (Fin.last (n+1)))
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀p : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p' | TrialCollision r (projectCurve L p.val) p'.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    let c := fun i ↦ gridSite (slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1))) i)
    let ns := nearSlots (torusNear K 30) c (routeSlots f) (routeSlots f')
    let nt := nearSlots (torusNear K 30) c (routeSlots f') (routeSlots f)
    (∫⁻x,A.firstDensity x*B.firstDensity x
      ∂physicalOnPrimary hL g m t r R C S u particle (v (Fin.last (n+1))) d)≤
      (routeDensityBound t)^(routeSlots f∩routeSlots f').card/a^(2*(ns.card+nt.card)) := by
  let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
  let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
  let anchor := fun j ↦ projectPoint L (anchorPoint (datumHome hL d (particle j)))
  let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
  let center := slotCenter (fun j ↦ datumHome hL d (particle j)) (v (Fin.last (n+1)))
  have : ∀i,IsProbabilityMeasure (μ i) := physicalOn_probability hL g m t r R C S u particle _ d hp
  have hdom : ∀j,some j∈routeSlots f∪routeSlots f'→(μ (some j)).map (fun p ↦ p)≤
      routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j := by
    intro j hj
    apply physical_primary_domination
    rcases Finset.mem_union.mp hj with hj|hj
    · exact route_selected_accessible hL g m t r R C S u particle f d ha j hj
    · exact route_selected_accessible hL g m t r R C S u particle f' d ha' j hj
  have h0 : ∀j,torusDistance L (anchor j) (gridCenter L (center (some j)))≤1 := by
    intro j
    change torusDistance L (gridCenter L (datumHome hL d (particle j)))
      (gridCenter L (datumHome hL d (particle j)))≤1
    simp [torusDistance]
  have hB := (B.path_bounds ht hc' hh' ha').1
  have hmB := B.forward_mass
  have hcB := physical_owner_centers hL particle f' v' d hh' hn' true
  simp only [hend] at hB hmB hcB
  have H := physical_route_encounter_moment (X:=X) hL r anchor center (M+1)
    (slotCenter_fiber _ _ M hm) allowed some (Option.some_injective _) (fun _ p ↦ p) (fun _ ↦ measurable_id)
    (routePermutation f) (routePermutation f') (routeSlots f) (routeSlots f')
    (routePermutation_fixed f) (routePermutation_fixed f') h0
    (physical_owner_centers hL particle f v d hh hn true) hcB μ A.forward B.forward
    (physicalCollisionReference hL g m t r R C S u particle d) (routeDensityBound t) q a ha0
    ((le_add_right le_rfl).trans hsmall) A.forward_bound A.forward_mass hmB hdom
    (A.path_bounds ht hc hh ha).1 hB hq hsmall (routeDensityBound_ne_top ht) A.firstSeed B.firstSeed
  simpa only [PhysicalRouteAux.firstDensity,hend,physicalOnPrimary,physicalOnChecks,X,μ,anchor,allowed,center] using H

end HardSphere.Groups
end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.HardSphere.Groups.physical_first_likelihood_moment_oai.{u_1} := @OAI.HardSphere.Groups.physical_first_likelihood_moment_oai.{u_1}
