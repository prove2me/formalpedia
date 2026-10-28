-- Prove2me | solution 1 for OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:29:41.472991+00:00
-- url     : https://prove2.me/submissions/6b6408ce-e0bd-4dc8-9ebe-12d316bf76cb

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]

variable {E : Type*}

lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id

lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_BlockExposure
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E B : Type*}

lemma measurable_block_of_dependsOn {A : Type*} [MeasurableSpace A]
    {f : Set E → A} (hf : Measurable f) (S : Set E) (hdep : DependsOn f S) :
    @Measurable (Set E) A (blockSigma S) inferInstance f := by
  have hm := hf.comp (measurable_forceOn_block Sᶜ (∅ : Set E))
  rw [compl_compl] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext ω
  apply hdep
  intro e he
  simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he),
    Set.mem_empty_iff_false]
  rfl

lemma lintegral_indicator_fresh (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hdep : DependsOn (fun ω => ω ∈ A) S)
    (g : Set E → ℝ≥0∞) (hg : Measurable g) (hgdep : DependsOn g Sᶜ) :
    (∫⁻ ω, A.indicator g ω ∂law q) = law q A * ∫⁻ ω, g ω ∂law q := by
  have hAb : MeasurableSet[blockSigma S] A := by
    have hm := hA.preimage (measurable_forceOn_block Sᶜ (∅ : Set E))
    rw [compl_compl] at hm
    convert hm using 1
    all_goals try with_reducible_and_instances rfl
    ext ω
    apply Iff.of_eq
    apply hdep
    intro e he
    simp only [forceOn, Set.mem_compl_iff, ite_eq_right (not_not.mpr he)]
    rfl
  have hgb := measurable_block_of_dependsOn hg Sᶜ hgdep
  have hi := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (blockSigma_le S) (blockSigma_le Sᶜ)
    (independent_blocks q S)
    ((measurable_const : @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance
      (fun _ => 1)).indicator hAb) hgb
  have heq : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω * g ω) = A.indicator g := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Set.indicator, hω]
  have hone := lintegral_indicator_const (μ := law q) hA (1 : ℝ≥0∞)
  simp only [one_mul] at hone
  rw [heq, hone] at hi
  exact hi

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open ClusterDeletion FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E)

lemma eraseVertices_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => G.eraseVertices ω U) (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext e
  change (ω e ∧ e ∉ G.incidentEdges U) ↔ (ω' e ∧ e ∉ G.incidentEdges U)
  by_cases he : e ∈ G.incidentEdges U
  · simp [he]
  · rw [(hω e he).to_iff]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ComponentSelf
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

end CriticalPercolation.ClusterDeletion

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_ClusterExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exactCluster_dependsOn (x : V) (S : Set V) :
    DependsOn (fun ω : Set E => G.cluster ω x = S) (G.incidentEdges S) := by
  intro ω η hω
  apply propext
  have hforward (ω η : Set E) (hωη : ∀ e ∈ G.incidentEdges S, e ∈ ω ↔ e ∈ η)
      (hS : G.cluster ω x = S) : G.cluster η x = S := by
    have hr : ClusterDeletion.roots (G.openGraph ω) {x} = S := by
      simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hS
    have hr' := G.roots_eq_of_incident hr hωη
    simpa only [ClusterDeletion.roots_singleton, ClusterDeletion.component, cluster] using hr'
  exact ⟨hforward ω η (fun e he => (hω e he).to_iff),
    hforward η ω (fun e he => (hω e he).symm.to_iff)⟩

lemma measurable_eraseVertices (S : Set V) : Measurable (fun ω => G.eraseVertices ω S) := by
  refine (@measurable_pi_iff (Set E) E (fun _ => Prop)
    inferInstance (fun _ => inferInstance) _).mpr ?_
  intro e
  exact (measurable_set_mem e).and measurable_const

lemma measurableSet_exactCluster [Countable V] [Countable E] (x : V) (S : Set V) :
    MeasurableSet {ω | G.cluster ω x = S} := by
  have heq : {ω | G.cluster ω x = S} =
      ⋂ y : V, {ω | (G.openGraph ω).Reachable x y ↔ y ∈ S} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact Set.ext_iff
  rw [heq]
  exact MeasurableSet.iInter fun y => ((G.measurable_reachable x y).iff measurable_const).setOf

theorem exactCluster_exterior_factor [Countable V] [Countable E]
    (p : unitInterval) (x : V) (S : Set V) (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, ({ω | G.cluster ω x = S} : Set (Set E)).indicator
      (fun ω => F (G.eraseVertices ω S)) ω ∂G.law p) =
        G.law p {ω | G.cluster ω x = S} *
          ∫⁻ η, F (G.eraseVertices η S) ∂G.law p := by
  unfold law
  rw [← BernoulliProduct.law_const]
  apply BernoulliProduct.lintegral_indicator_fresh (fun _ => p) (G.incidentEdges S)
    _ (G.measurableSet_exactCluster x S) (G.exactCluster_dependsOn x S)
    _ (hF.comp (G.measurable_eraseVertices S))
  intro ω η hωη
  exact congrArg F (G.eraseVertices_dependsOn S hωη)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteEnergy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma law_coordinate (q : E → unitInterval) (e : E) (b : Prop) :
    law q {ω : Set E | (e ∈ ω) = b} = bitMeasure (q e) {b} := by
  rw [law_eq_infinitePi]
  have h := congrArg (fun μ : Measure Prop => μ {b})
    (Measure.infinitePi_map_eval (fun e => bitMeasure (q e)) e)
  rw [Measure.map_apply (measurable_pi_apply e) (MeasurableSet.singleton b)] at h
  exact h

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BernoulliSingleton
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma force_singleton_inter (q : E → unitInterval) (e : E) (σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    law q (A ∩ {ω : Set E | (e∈ω)=(e∈σ)}) =
      bitMeasure (q e) {e∈σ} * law q (forceOn {e} σ ⁻¹' A) := by
  let C := {ω : Set E | (e∈ω)=(e∈σ)}
  let B := forceOn {e} σ ⁻¹' A
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e∈σ},MeasurableSet.singleton _,rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e≤blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (measurable_forceOn_block {e} σ)
  have hmul := ((independent_blocks q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have heq : A∩C = C∩B := by
    ext ω
    have hf (hω : ω∈C) : forceOn {e} σ ω=ω := by
      ext f
      by_cases he : f=e
      · subst f
        simpa only [mem_forceOn,Set.mem_singleton_iff,if_true] using Iff.of_eq hω.symm
      · simp only [mem_forceOn,Set.mem_singleton_iff,ite_eq_right he]
    constructor
    · rintro ⟨ha,hc⟩
      exact ⟨hc,by change forceOn {e} σ ω∈A; rwa [hf hc]⟩
    · rintro ⟨hc,hb⟩
      exact ⟨by change forceOn {e} σ ω∈A at hb; rwa [hf hc] at hb,hc⟩
  change law q (A∩C)=_
  rw [heq,hmul]
  change law q {ω : Set E | (e∈ω)=(e∈σ)} * _ = _
  rw [law_coordinate]

lemma law_singleton_decomposition (q : E → unitInterval) (e : E) :
    law q = bitMeasure (q e) {True} • (law q).map (forceOn {e} Set.univ) +
      bitMeasure (q e) {False} • (law q).map (forceOn {e} ∅) := by
  ext A hA
  rw [Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    Measure.map_apply (measurable_forceOn _ _) hA,
    Measure.map_apply (measurable_forceOn _ _) hA]
  simp only [smul_eq_mul]
  have ht := force_singleton_inter q e Set.univ A hA
  have hf := force_singleton_inter q e ∅ A hA
  simp only [Set.mem_univ,Set.mem_empty_iff_false] at ht hf
  rw [←ht,←hf]
  have he : {ω : Set E | (e∈ω)=False} = {ω : Set E | (e∈ω)=True}ᶜ := by
    ext ω
    simp
  rw [he,←Set.sdiff_eq]
  exact (measure_inter_add_sdiff A (measurableSet_eq_fun (measurable_set_mem e) measurable_const)).symm

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_EdgeClosing
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma force_closed_after_singleton (e : E) (σ ω : Set E) :
    forceOn {e} ∅ (forceOn {e} σ ω) = forceOn {e} ∅ ω := by
  ext f
  by_cases hf : f = e <;> simp [hf]

lemma lintegral_singleton_decomposition (q : E → unitInterval) (e : E)
    (f : Set E → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂law q) =
      bitMeasure (q e) {True} * (∫⁻ ω, f (forceOn {e} Set.univ ω) ∂law q) +
      bitMeasure (q e) {False} * (∫⁻ ω, f (forceOn {e} ∅ ω) ∂law q) := by
  conv_lhs => rw [law_singleton_decomposition q e]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_map hf (measurable_forceOn _ _), lintegral_map hf (measurable_forceOn _ _)]
  rfl

lemma lintegral_open_closed_observable (q : E → unitInterval) (e : E)
    (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∈ ω then F (forceOn {e} ∅ ω) else 0 ∂law q) =
      bitMeasure (q e) {True} * ∫⁻ ω, F (forceOn {e} ∅ ω) ∂law q := by
  have hm : Measurable (fun ω => if e ∈ ω then F (forceOn {e} ∅ ω) else 0) :=
    (hF.comp (measurable_forceOn _ _)).ite (measurable_set_mem e).setOf measurable_const
  rw [lintegral_singleton_decomposition q e _ hm]
  simp only [mem_forceOn, Set.mem_singleton, if_true, Set.mem_univ,
    Set.mem_empty_iff_false, if_false, force_closed_after_singleton,
    lintegral_zero, mul_zero, add_zero]

lemma lintegral_closed_observable (q : E → unitInterval) (e : E)
    (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∉ ω then F ω else 0 ∂law q) =
      bitMeasure (q e) {False} * ∫⁻ ω, F (forceOn {e} ∅ ω) ∂law q := by
  have hm : Measurable (fun ω => if e ∉ ω then F ω else 0) :=
    hF.ite (measurable_set_mem e).setOf.compl measurable_const
  rw [lintegral_singleton_decomposition q e _ hm]
  simp only [mem_forceOn, Set.mem_singleton, if_true, Set.mem_univ,
    Set.mem_empty_iff_false, not_true_eq_false, not_false_eq_true,
    if_false, if_true, lintegral_zero, mul_zero, zero_add]

theorem lintegral_edge_closing (q : E → unitInterval) (e : E)
    (he : (q e : ℝ) < 1) (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∈ ω then F (forceOn {e} ∅ ω) else 0 ∂law q) =
      (ENNReal.ofReal (q e : ℝ) / ENNReal.ofReal (1 - (q e : ℝ))) *
        (∫⁻ ω, if e ∉ ω then F ω else 0 ∂law q) := by
  have hbit (b : Prop) : bitMeasure (q e) {b} = ENNReal.ofReal (bitWeight (q e) b) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    congr 1
    exact bitMeasure_real_singleton (q e) b
  have hne : ENNReal.ofReal (1 - (q e : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr he)).ne'
  rw [lintegral_open_closed_observable q e F hF, lintegral_closed_observable q e F hF,
    hbit True, hbit False]
  simp only [bitWeight, if_true, if_false]
  rw [← mul_assoc, ENNReal.div_mul_cancel hne ENNReal.ofReal_ne_top]

end CriticalPercolation.BernoulliProduct

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_FiniteClusterSums
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem lintegral_eq_sum_finite_clusters (p : unitInterval) (x : V)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) (F : Set V → ℝ≥0∞) :
    (∫⁻ ω, F (G.cluster ω x) ∂G.law p) =
      ∑' S : Finset V, G.law p {ω | G.cluster ω x = (S : Set V)} * F (S : Set V) := by
  have heq : (fun ω => F (G.cluster ω x)) =ᵐ[G.law p]
      (fun ω => ∑' S : Finset V, if G.cluster ω x = (S : Set V) then F (S : Set V) else 0) := by
    filter_upwards [hfin] with ω hω
    rw [tsum_eq_single hω.toFinset (fun S hS => by
      apply ite_eq_right
      intro hc
      exact hS (Finset.coe_injective (hc.symm.trans hω.coe_toFinset.symm)))]
    rw [ite_eq_left hω.coe_toFinset.symm, hω.coe_toFinset]
  rw [lintegral_congr_ae heq,lintegral_tsum]
  · apply tsum_congr
    intro S
    simpa only [Set.indicator,Set.mem_ofPred_eq,mul_comm] using
      lintegral_indicator_const (G.measurableSet_exactCluster x (S : Set V)) (F (S : Set V))
  · intro S
    exact (measurable_const.ite (G.measurableSet_exactCluster x (S : Set V))
      measurable_const).aemeasurable

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedGhost
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

lemma ghostKernel_le_product (h x : ℝ) : ghostKernel h x ≤ h * x := by
  have he := Real.add_one_le_exp (-h * x)
  dsimp [ghostKernel]
  linarith

lemma ghostKernel_scaled_derivative_le (h x : ℝ) :
    h * (x * Real.exp (-h * x)) ≤ ghostKernel h x := by
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (h * x))
    (Real.exp_pos (-h * x)).le
  have heq : Real.exp (h * x) * Real.exp (-h * x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [heq] at he
  dsimp [ghostKernel]
  nlinarith

lemma hasDerivAt_ghostKernel (h x : ℝ) :
    HasDerivAt (fun r => ghostKernel r x) (x * Real.exp (-h * x)) h := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r * x))
      (-x * Real.exp (-h * x)) h := by
    convert (((hasDerivAt_id h).neg.mul_const x).exp) using 1
    all_goals first | rfl | (funext r; rfl) | (dsimp; ring)
  convert (hasDerivAt_const h (1 : ℝ)).sub he using 1
  all_goals first | rfl | ring

lemma ghostKernel_le_threeQuarter {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    ghostKernel h x ≤ (h * x) ^ (3 / 4 : ℝ) := by
  by_cases hu : h * x ≤ 1
  · exact (ghostKernel_le_product h x).trans
      (Real.self_le_rpow_of_le_one (mul_nonneg hh hx) hu (by norm_num))
  · exact (ghostKernel_le_one h x).trans
      (Real.one_le_rpow (le_of_not_ge hu) (by norm_num))

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ)

lemma measurable_ghostKernel (hX : Measurable X) (h : ℝ) :
    Measurable (fun ω => ghostKernel h (X ω)) :=
  measurable_const.sub ((measurable_const.mul hX).exp)

lemma integrable_ghostKernel (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 ≤ h) : Integrable (fun ω => ghostKernel h (X ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_ghostKernel X hX h).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ghostKernel_nonneg hh (hX0 ω))]
    exact ghostKernel_le_one _ _

theorem hasDerivAt_ghostMagnetization (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 < h) :
    Integrable (fun ω => X ω * Real.exp (-h * X ω)) μ ∧
      HasDerivAt (ghostMagnetization μ X) (ghostMagnetizationDerivative μ X h) h := by
  have hhalf : 0 < h / 2 := by positivity
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioi (h / 2)) (bound := fun _ => 2 / h)
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun r => (measurable_ghostKernel X hX r).aestronglyMeasurable)
    (integrable_ghostKernel μ X hX hX0 hh.le)
    (hX.mul ((measurable_const.mul hX).exp)).aestronglyMeasurable
  · exact ae_of_all _ fun ω r hr => by
      have hder0 : 0 ≤ X ω * Real.exp (-r * X ω) :=
        mul_nonneg (hX0 ω) (Real.exp_pos _).le
      have hprod : r * (X ω * Real.exp (-r * X ω)) ≤ 1 :=
        (ghostKernel_scaled_derivative_le r (X ω)).trans (ghostKernel_le_one _ _)
      change h / 2 < r at hr
      rw [Real.norm_eq_abs, abs_of_nonneg hder0]
      apply (le_div_iff₀ hh).mpr
      nlinarith
  · exact integrable_const _
  · exact ae_of_all _ fun ω r _ => hasDerivAt_ghostKernel r (X ω)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TwoGhost
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Percolation.BenjaminiSchramm

lemma one_sub_exp_le_single_add_two_ghost {u : ℝ} (hu : 0 ≤ u) :
    1 - Real.exp (-u) ≤ u * Real.exp (-u) + 2 * (1 - Real.exp (-(u / 2))) ^ 2 := by
  let F (r : ℝ) := Real.exp r - 4 * Real.exp (r / 2) + 3 + r
  have hF (r : ℝ) : HasDerivAt F (Real.exp r - 2 * Real.exp (r / 2) + 1) r := by
    have hh : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (r / 2) / 2) r := by
      convert (Real.hasDerivAt_exp (r / 2)).comp (h := fun s : ℝ => s / 2) r
        ((hasDerivAt_id r).div_const 2) using 1
      all_goals first | rfl | (funext s; rfl) | ring
    convert (((Real.hasDerivAt_exp r).sub (hh.const_mul 4)).add_const 3).add
      (hasDerivAt_id r) using 1
    all_goals first | rfl | (funext s; rfl) | ring
  have hmono : Monotone F := by
    apply monotone_of_deriv_nonneg (fun r => (hF r).differentiableAt)
    intro r
    rw [(hF r).deriv]
    have he : Real.exp (r / 2) ^ 2 = Real.exp r := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    nlinarith [sq_nonneg (Real.exp (r / 2) - 1)]
  have hnonneg : 0 ≤ F u := by
    have hm := hmono hu
    norm_num [F] at hm ⊢
    exact hm
  have hp := mul_nonneg (Real.exp_pos (-u)).le hnonneg
  have h1 : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (-u) * Real.exp (u / 2) = Real.exp (-(u / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  dsimp [F] at hp
  nlinarith

lemma ghostKernel_le_derivative_add_two_ghost {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    ghostKernel h x ≤ h * (x * Real.exp (-h * x)) + 2 * ghostKernel (h / 2) x ^ 2 := by
  have he := one_sub_exp_le_single_add_two_ghost (mul_nonneg hh hx)
  have hhalf : -(h / 2) * x = -(h * x / 2) := by ring
  dsimp [ghostKernel]
  rw [hhalf]
  simpa only [neg_mul, mul_assoc] using he

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ)

lemma integrable_ghostKernel_sq (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 ≤ h) : Integrable (fun ω => ghostKernel h (X ω) ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_ghostKernel X hX h).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [ghostKernel_nonneg hh (hX0 ω), ghostKernel_le_one h (X ω)]

theorem ghostMagnetization_le_derivative_add_two_ghost
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) {h : ℝ} (hh : 0 < h) :
    ghostMagnetization μ X h ≤ h * ghostMagnetizationDerivative μ X h +
      2 * ∫ ω, ghostKernel (h / 2) (X ω) ^ 2 ∂μ := by
  calc
    _ ≤ ∫ ω, h * (X ω * Real.exp (-h * X ω)) +
        2 * ghostKernel (h / 2) (X ω) ^ 2 ∂μ := by
      apply integral_mono (integrable_ghostKernel μ X hX hX0 hh.le)
        (((hasDerivAt_ghostMagnetization μ X hX hX0 hh).1.const_mul h).add
          ((integrable_ghostKernel_sq μ X hX hX0 (by positivity : 0 ≤ h / 2)).const_mul 2))
      intro ω
      exact ghostKernel_le_derivative_add_two_ghost hh.le (hX0 ω)
    _ = _ := by
      rw [integral_add ((hasDerivAt_ghostMagnetization μ X hX hX0 hh).1.const_mul h)
        ((integrable_ghostKernel_sq μ X hX hX0 (by positivity : 0 ≤ h / 2)).const_mul 2),
        integral_const_mul, integral_const_mul]
      rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostField
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ghostRate_closed_probability (h x : ℝ≥0) :
    CriticalPercolation.BernoulliProduct.bitMeasure (ghostRate h x) {False} =
      ENNReal.ofReal (Real.exp (-(h : ℝ) * x)) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  change ENNReal.ofReal
    ((CriticalPercolation.BernoulliProduct.bitMeasure (ghostRate h x)).real {False}) = _
  rw [CriticalPercolation.BernoulliProduct.bitMeasure_real_singleton]
  simp [CriticalPercolation.BernoulliProduct.bitWeight, ghostRate, ghostKernel]

theorem ghostFieldLaw_avoid_finset {V : Type*} (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    ghostFieldLaw h w {m | Disjoint (S : Set V) m} =
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) := by
  unfold ghostFieldLaw
  have hm : MeasurableSet {m : Set V | Disjoint (S : Set V) m} := by
    rw [show {m : Set V | Disjoint (S : Set V) m} = ⋂ v ∈ S, {m | v ∉ m} from by
      ext m
      simp [Set.disjoint_left]]
    exact S.measurableSet_biInter fun v _ => (measurable_set_mem v).setOf.compl
  rw [CriticalPercolation.BernoulliProduct.law,
    Measure.map_apply MeasurableEquiv.setOfPred.measurable hm]
  have he : MeasurableEquiv.setOfPred ⁻¹' {m : Set V | Disjoint (S : Set V) m} =
      ((S : Set V).pi (fun _ => {False}) : Set (V → Prop)) := by
    ext f
    change Disjoint (S : Set V) {v | f v} ↔ ∀ v ∈ (S : Set V), f v = False
    constructor
    · intro hd v hv
      exact propext (iff_false_intro fun hf => Set.disjoint_left.mp hd hv hf)
    · intro hd
      apply Set.disjoint_left.mpr
      intro v hv hf
      change f v at hf
      rw [hd v hv] at hf
      exact hf
  rw [he]
  erw [Measure.infinitePi_pi
    (μ := fun v : V => CriticalPercolation.BernoulliProduct.bitMeasure (ghostRate h (w v)))
    (s := S) (t := fun _ : V => ({False} : Set Prop)) (fun _ _ => MeasurableSet.of_discrete)]
  simp_rw [ghostRate_closed_probability]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  exact (Finset.mul_sum S _ _).symm

lemma measurableSet_ghostHits {V : Type*} [Countable V] (S : Set V) :
    MeasurableSet (ghostHits S) :=
  (Measurable.exists fun v => measurable_const.and (measurable_set_mem v)).setOf

lemma ghostHits_compl {V : Type*} (S : Set V) : (ghostHits S)ᶜ = {m | Disjoint S m} := by
  ext m
  simp [ghostHits, Set.disjoint_left]

theorem ghostFieldLaw_real_hit_finset {V : Type*} [Countable V]
    (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    (ghostFieldLaw h w).real (ghostHits (S : Set V)) =
      ghostKernel h (∑ v ∈ S, (w v : ℝ)) := by
  have he := probReal_compl_eq_one_sub (μ := ghostFieldLaw h w)
    (measurableSet_ghostHits (S : Set V))
  rw [ghostHits_compl, measureReal_def, ghostFieldLaw_avoid_finset,
    ENNReal.toReal_ofReal (Real.exp_pos _).le] at he
  dsimp [ghostKernel]
  linarith

theorem twoGhostFieldLaw_real_hit_finset {V : Type*} [Countable V]
    (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    ((ghostFieldLaw h w).prod (ghostFieldLaw h w)).real
      (ghostHits (S : Set V) ×ˢ ghostHits (S : Set V)) =
        ghostKernel h (∑ v ∈ S, (w v : ℝ)) ^ 2 := by
  rw [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
  change (ghostFieldLaw h w).real (ghostHits (S : Set V)) *
    (ghostFieldLaw h w).real (ghostHits (S : Set V)) = _
  rw [ghostFieldLaw_real_hit_finset, sq]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostAvoidance
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace Percolation.BenjaminiSchramm
variable {V : Type*}

lemma ghost_avoidance_exterior_factor (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V)
    (F : Set V → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ m, ({m | Disjoint (S : Set V) m} : Set (Set V)).indicator
      (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m)) m
      ∂ghostFieldLaw h w) =
        ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) *
          ∫⁻ m, F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m)
            ∂ghostFieldLaw h w := by
  let A := {m : Set V | Disjoint (S : Set V) m}
  have hA : MeasurableSet A := by
    rw [show A = ⋂ v ∈ S, {m | v ∉ m} from by ext m; simp [A,Set.disjoint_left]]
    exact S.measurableSet_biInter fun v _ => (measurable_set_mem v).setOf.compl
  have hd : DependsOn (fun m => m ∈ A) (S : Set V) := by
    intro m n hmn
    apply propext
    simp only [A, Set.disjoint_left]
    exact ⟨fun hm v hv hn => hm hv ((hmn v hv).to_iff.mpr hn),
      fun hn v hv hm => hn hv ((hmn v hv).to_iff.mp hm)⟩
  have hforce : DependsOn
      (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m))
      (S : Set V)ᶜ := by
    intro m n hmn
    apply congrArg F
    unfold CriticalPercolation.BernoulliProduct.forceOn
    funext v
    by_cases hv : v ∈ (S : Set V)
    · simp only [ite_eq_left hv]
    · simp only [ite_eq_right hv]
      exact hmn v hv
  have he := CriticalPercolation.BernoulliProduct.lintegral_indicator_fresh
    (fun v => ghostRate h (w v)) (S : Set V) A hA hd
    (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m))
    (hF.comp (CriticalPercolation.BernoulliProduct.measurable_forceOn _ _)) hforce
  change _ = ghostFieldLaw h w A * _ at he
  rw [ghostFieldLaw_avoid_finset] at he
  exact he

lemma ghost_avoidance_upper (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V)
    (F : Set V → ℝ≥0∞) (hF : Measurable F) (hmono : Monotone F) :
    (∫⁻ m, if Disjoint (S : Set V) m then F m else 0 ∂ghostFieldLaw h w) ≤
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) *
        ∫⁻ m, F m ∂ghostFieldLaw h w := by
  have heq (m : Set V) (hm : Disjoint (S : Set V) m) :
      CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m = m := by
    ext v
    by_cases hv : v ∈ (S : Set V)
    · have hvm : v ∉ m := fun h => Set.disjoint_left.mp hm hv h
      simp [CriticalPercolation.BernoulliProduct.mem_forceOn,hv,hvm]
    · simp [CriticalPercolation.BernoulliProduct.mem_forceOn,hv]
  calc
    _ = ∫⁻ m, ({m | Disjoint (S : Set V) m} : Set (Set V)).indicator
        (fun m => F (CriticalPercolation.BernoulliProduct.forceOn (S : Set V) ∅ m)) m
        ∂ghostFieldLaw h w := by
      apply lintegral_congr
      intro m
      by_cases hm : Disjoint (S : Set V) m <;> simp [Set.indicator,hm,heq m]
    _ = _ := ghost_avoidance_exterior_factor h w S F hF
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro m
      apply hmono
      intro v hv
      by_cases hvS : v ∈ (S : Set V)
      · simp [CriticalPercolation.BernoulliProduct.mem_forceOn,hvS] at hv
      · simpa [CriticalPercolation.BernoulliProduct.mem_forceOn,hvS] using hv

theorem two_ghost_avoidance_upper (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V)
    (F : Set V × Set V → ℝ≥0∞) (hF : Measurable F)
    (hmono : ∀ m m', m ⊆ m' → ∀ n n', n ⊆ n' → F (m,n) ≤ F (m',n')) :
    (∫⁻ m, ∫⁻ n, if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n
      then F (m,n) else 0 ∂ghostFieldLaw h w ∂ghostFieldLaw h w) ≤
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) ^ 2 *
        ∫⁻ m, ∫⁻ n, F (m,n) ∂ghostFieldLaw h w ∂ghostFieldLaw h w := by
  let c := ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ)))
  let H := fun m => ∫⁻ n, F (m,n) ∂ghostFieldLaw h w
  have hH : Measurable H := hF.lintegral_prod_right'
  have hHm : Monotone H := by
    intro m m' hmm
    exact lintegral_mono fun n => hmono m m' hmm n n le_rfl
  calc
    _ ≤ ∫⁻ m, if Disjoint (S : Set V) m then c * H m else 0 ∂ghostFieldLaw h w := by
      apply lintegral_mono
      intro m
      by_cases hm : Disjoint (S : Set V) m
      · simp only [hm, true_and, if_true]
        exact ghost_avoidance_upper h w S (fun n => F (m,n))
          (hF.comp (measurable_const.prodMk measurable_id))
          (fun n n' hnn => hmono m m le_rfl n n' hnn)
      · simp only [hm, false_and, if_false, lintegral_zero, le_refl]
    _ = c * ∫⁻ m, if Disjoint (S : Set V) m then H m else 0 ∂ghostFieldLaw h w := by
      have heq (m : Set V) : (if Disjoint (S : Set V) m then c * H m else 0) =
          c * (if Disjoint (S : Set V) m then H m else 0) := by split_ifs <;> simp
      simp_rw [heq]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ c * (c * ∫⁻ m, H m ∂ghostFieldLaw h w) :=
      mul_le_mul' le_rfl (ghost_avoidance_upper h w S H hH hHm)
    _ = _ := by rw [← mul_assoc, sq]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Kernel_Bounds
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel domination, monotone couplings and endpoint bounds. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Coupling

theorem measurable_threshold (p : unitInterval) :
    Measurable (fun t : unitInterval => t ≤ p) :=
  measurableSet_setOfPred.mp measurableSet_Iic

 
theorem map_threshold (p : unitInterval) :
    (volume : Measure unitInterval).map (fun t => t ≤ p) =
      unitInterval.toNNReal p • Measure.dirac True +
      unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False := by
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Iic p) = _
    rw [unitInterval.volume_Iic, ← unitInterval.coe_toNNReal p,
      ENNReal.ofReal_coe_nnreal]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [Measure.map_apply (measurable_threshold p), Set.preimage]
    change volume (Set.Ioi p) = _
    rw [unitInterval.volume_Ioi, ← unitInterval.coe_symm_eq,
      ← unitInterval.coe_toNNReal (unitInterval.symm p), ENNReal.ofReal_coe_nnreal]


end Coupling

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_ProductMeasure_Association
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Association, disjoint witnesses and the BK inequality. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Restriction

theorem measurable_set_restrict (s : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
  measurable_setOfPred.comp (Measurable.of_eval
    (fun e => (measurable_pi_apply e.val).comp MeasurableEquiv.setOfPred.symm.measurable))

 
theorem law_map_restrict (p : unitInterval) (s : Set E) :
    (law p : Measure (Set E)).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) = law p := by
  have hm := measurable_set_restrict s
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map hm measurable_setOfPred]
  have he : (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ∘
      (fun f : E → Prop => {e | f e}) =
      (fun f : s → Prop => {e | f e}) ∘ s.domRestrict := rfl
  rw [he, ← Measure.map_map measurable_setOfPred (by fun_prop),
    Measure.infinitePi_map_restrict', setBernoulli_eq_map]
  simp only [Set.mem_univ]

end Restriction

section WitnessAssociation
attribute [local instance] Classical.propDecidable
open Filter Topology


 theorem edgeExhaustion_mono [Encodable E] :
    Monotone (edgeExhaustion : ℕ → Finset E) := by
  intro m n h e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range] at he ⊢
  exact he.trans_le h

private theorem subset_edgeExhaustion [Encodable E] (s : Finset E) :
    ∃ n, s ⊆ edgeExhaustion n := by
  refine ⟨s.sup Encodable.encode + 1, ?_⟩
  intro e he
  simp only [edgeExhaustion, Finset.mem_preimage, Finset.mem_range]
  exact Nat.lt_succ_of_le (Finset.le_sup he)

 theorem witness_eq_union [Encodable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hf : FiniteWitness A) :
    A = ⋃ n, {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · intro hω
    obtain ⟨s, hs, hsa⟩ := hf ω hω
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact ⟨n, hA (fun _ he => ⟨hs he, hn he⟩) hsa⟩
  · rintro ⟨n, hn⟩
    exact hA Set.inter_subset_left hn



end WitnessAssociation

section ClusterEvents
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : MeasurableSet A := by
  let := Encodable.ofCountable E
  rw [witness_eq_union A hA hfA]
  apply MeasurableSet.iUnion
  intro n
  let s := edgeExhaustion (E := E) n
  have he : {ω : Set E | ω ∩ (s : Set E) ∈ A} =
      (fun ω => (Subtype.val ⁻¹' ω : Set (s : Set E))) ⁻¹'
        {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set (s : Set E)) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  change MeasurableSet {ω : Set E | ω ∩ (s : Set E) ∈ A}
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict _)

theorem finiteWitness_conn (G : BondGraph V E) (x y : V) :
    FiniteWitness {ω | Conn G ω x y} := by
  intro ω h
  induction h with
  | refl => exact ⟨∅, by simp, by simp⟩
  | @tail b c hab hbc ih =>
    obtain ⟨s, hs, hconn⟩ := ih
    obtain ⟨e, he, hGe⟩ := hbc
    refine ⟨insert e s, ?_, ?_⟩
    · simpa only [Finset.coe_insert] using Set.insert_subset he hs
    · exact (conn_mono G (by simp) hconn).tail ⟨e, by simp, hGe⟩

end ClusterEvents

section DisjointWitness
attribute [local instance] Classical.propDecidable


theorem disjointOccurrence_upper (A B : Set (Set E)) : IsUpperSet (DisjointOccurrence A B) := by
  rintro ω η h ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs.trans h, ht.trans h, hd, ha, hb⟩

theorem finiteWitness_disjointOccurrence (A B : Set (Set E)) :
    FiniteWitness (DisjointOccurrence A B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  refine ⟨s ∪ t, ?_, s, t, ?_, ?_, hd, ha, hb⟩
  · simpa only [Finset.coe_union] using Set.union_subset hs ht
  · simp
  · simp

theorem disjointOccurrence_mono {A A' B B' : Set (Set E)}
    (hA : A ⊆ A') (hB : B ⊆ B') : DisjointOccurrence A B ⊆ DisjointOccurrence A' B' := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs, ht, hd, hA ha, hB hb⟩


theorem openSection_upper {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    IsUpperSet (openSection A e) :=
  fun _ _ h hω => hA (Set.insert_subset_insert h) hω

theorem subset_openSection {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    A ⊆ openSection A e := fun ω hω => hA (Set.subset_insert e ω) hω

 
theorem openSection_disjointOccurrence (A B : Set (Set E)) (_hA : IsUpperSet A)
    (hB : IsUpperSet B) (e : E) :
    openSection (DisjointOccurrence A B) e ⊆
      DisjointOccurrence (openSection A e) B ∪ DisjointOccurrence A (openSection B e) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  by_cases he : e ∈ s
  · left
    have het : e ∉ t := fun h => Finset.disjoint_left.mp hd he h
    refine ⟨s.erase e, t, ?_, ?_, Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hd, ?_, hb⟩
    · intro z hz
      exact (hs (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · intro z hz
      rcases ht hz with rfl | hz'
      · exact (het hz).elim
      · exact hz'
    · change insert e (↑(s.erase e) : Set E) ∈ A
      simpa only [← Finset.coe_insert, Finset.insert_erase he] using ha
  · right
    refine ⟨s, t.erase e, ?_, ?_, Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd, ha, ?_⟩
    · intro z hz
      rcases hs hz with rfl | hz'
      · exact (he hz).elim
      · exact hz'
    · intro z hz
      exact (ht (Finset.mem_of_mem_erase hz)).resolve_left (Finset.ne_of_mem_erase hz)
    · apply hB ?_ hb
      intro z hz
      by_cases hze : z = e
      · exact Or.inl hze
      · exact Or.inr (Finset.mem_erase.mpr ⟨hze, hz⟩)



theorem finiteProbability_mono (p : unitInterval) (s : Finset E)
    {A B : Set (Set E)} (h : A ⊆ B) : finiteProbability p s A ≤ finiteProbability p s B := by
  apply Finset.sum_le_sum
  intro t _
  split_ifs with ha hb hb
  · exact le_rfl
  · exact (hb (h ha)).elim
  · exact mul_nonneg (pow_nonneg p.2.1 _) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  · exact le_rfl

theorem finiteProbability_union_add_inter (p : unitInterval) (s : Finset E)
    (A B : Set (Set E)) :
    finiteProbability p s (A ∪ B) + finiteProbability p s (A ∩ B) =
      finiteProbability p s A + finiteProbability p s B := by
  simp only [finiteProbability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ha : (t : Set E) ∈ A <;> by_cases hb : (t : Set E) ∈ B <;> simp [ha, hb]

theorem finiteProbability_insert (p : unitInterval) (s : Finset E) (e : E) (he : e ∉ s)
    (A : Set (Set E)) :
    finiteProbability p (insert e s) A =
      (1 - p : ℝ) * finiteProbability p s A + (p : ℝ) * finiteProbability p s (openSection A e) := by
  have hd : Disjoint s.powerset (s.powerset.image (insert e)) := by
    apply Finset.disjoint_left.mpr
    intro t ht himg
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp himg
    exact he ((Finset.mem_powerset.mp ht) (by simp))
  have hinj : Set.InjOn (insert e) (↑s.powerset : Set (Finset E)) := by
    intro t ht r hr h
    have ht' : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    have hr' : e ∉ r := fun h => he (Finset.mem_powerset.mp hr h)
    have hh := congrArg (fun t : Finset E => t.erase e) h
    simpa [ht', hr'] using hh
  simp only [finiteProbability, Finset.powerset_insert, Finset.sum_union hd,
    Finset.sum_image hinj, Finset.mul_sum, Finset.card_insert_of_notMem he]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    have hcard := Finset.card_le_card (Finset.mem_powerset.mp ht)
    have hexp : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
    rw [hexp, pow_succ]
    split_ifs <;> simp_all [mul_comm, mul_left_comm]
  · apply Finset.sum_congr rfl
    intro t ht
    have het : e ∉ t := fun h => he (Finset.mem_powerset.mp ht h)
    simp only [Finset.card_insert_of_notMem het, Nat.add_sub_add_right, pow_succ,
      Finset.coe_insert, openSection, Set.mem_ofPred_eq]
    split_ifs <;> simp_all [mul_assoc, mul_comm]

end DisjointWitness

section FiniteBK
attribute [local instance] Classical.propDecidable



theorem finiteProbability_disjointOccurrence_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) (s : Finset E) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) :
    finiteProbability p s (DisjointOccurrence A B) ≤
      finiteProbability p s A * finiteProbability p s B := by
  induction s using Finset.induction_on generalizing A B with
  | empty =>
    simp only [finiteProbability_empty, empty_mem_disjointOccurrence]
    by_cases ha : (∅ : Set E) ∈ A <;> by_cases hb : (∅ : Set E) ∈ B <;> simp [ha, hb]
  | @insert e s he ih =>
    let A1 := openSection A e
    let B1 := openSection B e
    let D00 := DisjointOccurrence A B
    let D10 := DisjointOccurrence A1 B
    let D01 := DisjointOccurrence A B1
    have hD : D00 ⊆ D10 ∩ D01 := by
      intro ω hω
      exact ⟨disjointOccurrence_mono (subset_openSection hA e) (Set.Subset.refl _) hω,
        disjointOccurrence_mono (Set.Subset.refl _) (subset_openSection hB e) hω⟩
    have hsec : finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s D10 + finiteProbability p s D01 - finiteProbability p s D00 := by
      have h1 := finiteProbability_mono p s (openSection_disjointOccurrence A B hA hB e)
      have h2 := finiteProbability_mono p s hD
      have h3 := finiteProbability_union_add_inter p s D10 D01
      change finiteProbability p s (openSection D00 e) ≤
        finiteProbability p s (D10 ∪ D01) at h1
      linarith
    have h00 := ih A B hA hB
    have h10 := ih A1 B (openSection_upper hA e) hB
    have h01 := ih A B1 hA (openSection_upper hB e)
    have ha := finiteProbability_mono p s (subset_openSection hA e)
    have hb := finiteProbability_mono p s (subset_openSection hB e)
    have hcoef : 0 ≤ 1 - 2 * (p : ℝ) := by linarith
    have hdif : 0 ≤ ((p : ℝ) ^ 2) *
        (finiteProbability p s A1 - finiteProbability p s A) *
        (finiteProbability p s B1 - finiteProbability p s B) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr ha)) (sub_nonneg.mpr hb)
    rw [finiteProbability_insert p s e he, finiteProbability_insert p s e he,
      finiteProbability_insert p s e he]
    have hm := mul_le_mul_of_nonneg_left hsec p.2.1
    have hm00 := mul_le_mul_of_nonneg_left h00 hcoef
    have hm10 := mul_le_mul_of_nonneg_left h10 p.2.1
    have hm01 := mul_le_mul_of_nonneg_left h01 p.2.1
    change (1 - (p : ℝ)) * finiteProbability p s D00 +
      (p : ℝ) * finiteProbability p s (openSection D00 e) ≤
      ((1 - (p : ℝ)) * finiteProbability p s A + (p : ℝ) * finiteProbability p s A1) *
      ((1 - (p : ℝ)) * finiteProbability p s B + (p : ℝ) * finiteProbability p s B1)
    nlinarith

end FiniteBK

section BKMeasure
attribute [local instance] Classical.propDecidable
open Filter Topology

 
theorem finiteProbability_univ [Fintype E] (p : unitInterval) (A : Set (Set E)) :
    finiteProbability p Finset.univ A = (law p).real A := by
  have he : (law p).real A = ∑ ω : Set E, if ω ∈ A then (law p).real {ω} else 0 := by
    have h := integral_fintype (μ := law p) (f := A.indicator (fun _ => (1 : ℝ)))
      Integrable.of_finite
    rw [integral_indicator_const (1 : ℝ) (.of_discrete : MeasurableSet A)] at h
    simpa [smul_eq_mul, mul_ite, Set.indicator_apply] using h
  rw [he, finiteProbability]
  apply Finset.sum_bij (fun (t : Finset E) _ => (t : Set E))
  · simp
  · intro a _ b _ h
    exact Finset.coe_injective h
  · intro ω _
    exact ⟨ω.toFinset, by simp, by simp⟩
  · intro t _
    rw [law, setBernoulli_real_singleton p (Set.subset_univ _) Set.finite_univ]
    simp [Set.ncard_sdiff' (Set.subset_univ _) Set.finite_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]

theorem disjointOccurrence_image {F : Type*} (f : F ↪ E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B =
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    let s' := s.preimage f f.injective.injOn
    let t' := t.preimage f f.injective.injOn
    have hs' : (s' : Set F) = f ⁻¹' (s : Set E) := by simp [s']
    have ht' : (t' : Set F) = f ⁻¹' (t : Set E) := by simp [t']
    have hsI : f '' (s' : Set F) = (s : Set E) := by
      rw [hs', Set.image_preimage_eq_of_subset]
      exact hs.trans (Set.image_subset_range _ _)
    have htI : f '' (t' : Set F) = (t : Set E) := by
      rw [ht', Set.image_preimage_eq_of_subset]
      exact ht.trans (Set.image_subset_range _ _)
    refine ⟨s', t', ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs']
      exact (Set.preimage_mono hs).trans (by rw [Set.preimage_image_eq _ f.injective])
    · rw [ht']
      exact (Set.preimage_mono ht).trans (by rw [Set.preimage_image_eq _ f.injective])
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      exact Finset.disjoint_left.mp hd (by simpa [s'] using hx) (by simpa [t'] using hy)
    · change f '' (s' : Set F) ∈ A
      rwa [hsI]
    · change f '' (t' : Set F) ∈ B
      rwa [htI]
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    refine ⟨s.map f, t.map f, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.coe_map] using Set.image_mono hs
    · simpa only [Finset.coe_map] using Set.image_mono ht
    · exact (Finset.disjoint_map f).mpr hd
    · simpa only [Finset.coe_map, Set.mem_preimage] using ha
    · simpa only [Finset.coe_map, Set.mem_preimage] using hb

theorem bk_finite_half [Fintype E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  simpa only [finiteProbability_univ] using
    finiteProbability_disjointOccurrence_le_half p hp Finset.univ A B hA hB

theorem bk_restricted_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) (s : Finset E) :
    (law p).real {ω | ω ∩ (s : Set E) ∈ DisjointOccurrence A B} ≤
      (law p).real {ω | ω ∩ (s : Set E) ∈ A} *
      (law p).real {ω | ω ∩ (s : Set E) ∈ B} := by
  let f : (s : Set E) ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
  have hreal (C : Set (Set E)) :
      (law p).real {ω | ω ∩ (s : Set E) ∈ C} =
        (law p).real {η : Set (s : Set E) | f '' η ∈ C} := by
    rw [← law_map_restrict p (s : Set E)]
    simp only [Measure.real]
    rw [Measure.map_apply (measurable_set_restrict _) MeasurableSet.of_discrete]
    congr 2
    ext ω
    change ω ∩ (s : Set E) ∈ C ↔ f '' (Subtype.val ⁻¹' ω) ∈ C
    have he : f '' (Subtype.val ⁻¹' ω) = ω ∩ (s : Set E) := by
      ext e
      simp [f, and_comm]
    rw [he]
  rw [hreal, hreal, hreal]
  have hh := bk_finite_half p hp ((fun ω => f '' ω) ⁻¹' A)
    ((fun ω => f '' ω) ⁻¹' B)
    (fun _ _ h hω => hA (Set.image_mono h) hω)
    (fun _ _ h hω => hB (Set.image_mono h) hω)
  rw [← disjointOccurrence_image] at hh
  exact hh

 
theorem bk_finiteWitness_half [Countable E] (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  let := Encodable.ofCountable E
  have hlim (C : Set (Set E)) (hC : IsUpperSet C) (hfC : FiniteWitness C) :
      Tendsto (fun n => (law p).real {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C})
        atTop (𝓝 ((law p).real C)) := by
    have hm : Monotone (fun n => {ω : Set E | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ C}) := by
      intro m n h ω hω
      exact hC (Set.inter_subset_inter_right _ (edgeExhaustion_mono h)) hω
    have h := tendsto_measure_iUnion_atTop (μ := law p) hm
    rw [← witness_eq_union C hC hfC] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  apply le_of_tendsto_of_tendsto
    (hlim _ (disjointOccurrence_upper A B) (finiteWitness_disjointOccurrence A B))
    ((hlim A hA hfA).mul (hlim B hB hfB))
  exact Filter.Eventually.of_forall fun n => bk_restricted_half p hp A B hA hB (edgeExhaustion n)

end BKMeasure

section ORLift
attribute [local instance] Classical.propDecidable

instance bitLaw_isProbabilityMeasure (q : unitInterval) : IsProbabilityMeasure (bitLaw q) := by
  rw [bitLaw, ← map_threshold q]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

 
theorem map_nonempty (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set F)).map Set.Nonempty = bitLaw (orParameter q (Fintype.card F)) := by
  let μ := (law q : Measure (Set F)).map Set.Nonempty
  have hm : Measurable (Set.Nonempty : Set F → Prop) := .of_discrete
  have : IsProbabilityMeasure μ := by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hfalse : μ.real {False} = (1 - (q : ℝ)) ^ Fintype.card F := by
    change ((law q).map Set.Nonempty).real {False} = _
    simp only [Measure.real, Measure.map_apply hm (measurableSet_singleton _)]
    have he : Set.Nonempty ⁻¹' ({False} : Set Prop) = ({∅} : Set (Set F)) := by
      ext ω
      simp [Set.not_nonempty_iff_eq_empty]
    rw [he]
    change (law q).real {∅} = _
    rw [law, setBernoulli_real_singleton q (Set.empty_subset _) Set.finite_univ]
    simp [Set.ncard_univ, Nat.card_eq_fintype_card]
  have htrue : μ.real {True} = 1 - (1 - (q : ℝ)) ^ Fintype.card F := by
    have he : ({True} : Set Prop) = ({False} : Set Prop)ᶜ := by ext b; simp
    rw [he, measureReal_compl (measurableSet_singleton _), probReal_univ, hfalse]
  apply Measure.ext_of_singleton
  intro b
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real {b} = (bitLaw (orParameter q (Fintype.card F))).real {b}
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    rw [htrue]
    simp [bitLaw, Measure.real, orParameter]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    rw [hfalse]
    simp [bitLaw, Measure.real, orParameter]

 
theorem finite_image_lift {F : Type*} (f : F → E) {ω : Set F} (s : Finset E)
    (hs : (s : Set E) ⊆ f '' ω) :
    ∃ t : Finset F, (t : Set F) ⊆ ω ∧ f '' (t : Set F) = (s : Set E) := by
  have hex : ∃ t ⊆ f '' ω, t.Finite ∧ t = (s : Set E) :=
    ⟨s, hs, s.finite_toSet, rfl⟩
  obtain ⟨t, ht, htf, hti⟩ := Set.exists_subset_image_finite_and.mp hex
  exact ⟨htf.toFinset, by simpa using ht, by simpa using hti⟩

theorem finiteWitness_image_preimage {F : Type*} (f : F → E) (A : Set (Set E))
    (hA : FiniteWitness A) : FiniteWitness ((fun ω => f '' ω) ⁻¹' A) := by
  intro ω hω
  obtain ⟨s, hs, ha⟩ := hA (f '' ω) hω
  obtain ⟨t, ht, htI⟩ := finite_image_lift f s hs
  exact ⟨t, ht, by simpa only [Set.mem_preimage, htI] using ha⟩

theorem image_preimage_disjointOccurrence {F : Type*} (f : F → E) (A B : Set (Set E)) :
    (fun ω => f '' ω) ⁻¹' DisjointOccurrence A B ⊆
      DisjointOccurrence ((fun ω => f '' ω) ⁻¹' A) ((fun ω => f '' ω) ⁻¹' B) := by
  rintro ω ⟨s, t, hs, ht, hd, ha, hb⟩
  obtain ⟨s', hs', hsI⟩ := finite_image_lift f s hs
  obtain ⟨t', ht', htI⟩ := finite_image_lift f t ht
  refine ⟨s', t', hs', ht', ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    have hxs : f x ∈ (s : Set E) := hsI ▸ Set.mem_image_of_mem f hx
    have hxt : f x ∈ (t : Set E) := htI ▸ Set.mem_image_of_mem f hy
    exact Finset.disjoint_left.mp hd hxs hxt
  · simpa only [Set.mem_preimage, hsI] using ha
  · simpa only [Set.mem_preimage, htI] using hb

end ORLift

section ORLaw
attribute [local instance] Classical.propDecidable

theorem map_exists_bitLaw (q : unitInterval) (F : Type*) [Fintype F] :
    (Measure.infinitePi (fun _ : F => bitLaw q)).map (fun f : F → Prop => ∃ j, f j) =
      bitLaw (orParameter q (Fintype.card F)) := by
  have h := map_nonempty q F
  unfold law at h
  rw [setBernoulli_eq_map, Measure.map_map (Measurable.of_discrete) measurable_setOfPred] at h
  simpa only [Set.mem_univ, Function.comp_def, Set.Nonempty, Set.mem_ofPred_eq,
    bernoulliMeasure_def, bitLaw] using h

theorem measurable_image_fst (F : Type*) [Fintype F] :
    Measurable (fun ω : Set (E × F) => Prod.fst '' ω) := by
  have hm : Measurable (fun ω : Set (E × F) => fun e => ∃ j : F, (e,j) ∈ ω) := by
    apply Measurable.of_eval
    intro e
    apply measurableSet_setOfPred.mp
    have he : {ω : Set (E × F) | ∃ j : F, (e,j) ∈ ω} =
        ⋃ j : F, {ω : Set (E × F) | (e,j) ∈ ω} := by ext ω; simp
    rw [he]
    exact MeasurableSet.iUnion fun j => measurableSet_setOfPred.mpr
      ((measurable_pi_apply (e,j)).comp MeasurableEquiv.setOfPred.symm.measurable)
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) =
      (fun f : E → Prop => {e | f e}) ∘ (fun ω e => ∃ j : F, (e,j) ∈ ω) := by
    funext ω
    ext e
    simp [Prod.exists]
  rw [he]
  exact measurable_setOfPred.comp hm

 
theorem law_map_image_fst (q : unitInterval) (F : Type*) [Fintype F] :
    (law q : Measure (Set (E × F))).map (fun ω => Prod.fst '' ω) =
      law (orParameter q (Fintype.card F)) := by
  let c := MeasurableEquiv.curry E F Prop
  let b := fun f : E → F → Prop => fun e => ∃ j, f e j
  have hb : Measurable b := Measurable.of_eval
    (fun e => (Measurable.of_discrete : Measurable (fun f : F → Prop => ∃j, f j)).comp
      (measurable_pi_apply e))
  unfold law
  rw [setBernoulli_eq_map, Measure.map_map (measurable_image_fst F) measurable_setOfPred]
  simp only [Set.mem_univ]
  have he : (fun ω : Set (E × F) => Prod.fst '' ω) ∘ (fun f => {e | f e}) =
      (fun f : E → Prop => {e | f e}) ∘ b ∘ c := by
    funext f
    ext e
    simp [b, c, Function.comp_def, Prod.exists]
  rw [he, ← Measure.map_map measurable_setOfPred (hb.comp c.measurable),
    ← Measure.map_map hb c.measurable]
  change ((Measure.infinitePi (fun _ : E × F => bitLaw q)).map c |>.map b |>.map
    (fun f : E → Prop => {e | f e})) = _
  rw [Measure.infinitePi_map_curry (fun (_ : E) (_ : F) => bitLaw q)]
  dsimp only [b]
  rw [Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  rw [map_exists_bitLaw q F]
  rw [setBernoulli_eq_map]
  rfl

 
theorem exists_orParameter (p : unitInterval) (hp : p < 1) :
    ∃ m : ℕ, ∃ q : unitInterval, (q : ℝ) ≤ 1 / 2 ∧ orParameter q m = p := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show 0 < 1 - (p : ℝ) by exact sub_pos.mpr hp)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let f := fun x : ℝ => 1 - (1-x)^m
  have hf : Continuous f := by fun_prop
  have h0 : f 0 = 0 := by simp [f]
  have hp' : (p : ℝ) ∈ Set.Icc (f 0) (f (1/2)) := by
    rw [h0]
    refine ⟨p.2.1, ?_⟩
    dsimp [f]
    norm_num at hm ⊢
    linarith
  obtain ⟨q, hq, hqp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1/2)
    hf.continuousOn hp'
  refine ⟨m, ⟨q, hq.1, hq.2.trans (by norm_num)⟩, hq.2, ?_⟩
  apply Subtype.ext
  exact hqp

end ORLaw

section BK
attribute [local instance] Classical.propDecidable

theorem disjointOccurrence_subset_inter (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) : DisjointOccurrence A B ⊆ A ∩ B := by
  rintro ω ⟨s,t,hs,ht,_,ha,hb⟩
  exact ⟨hA hs ha, hB ht hb⟩

 

theorem bk [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (law p).real (DisjointOccurrence A B) ≤ (law p).real A * (law p).real B := by
  by_cases hp : p = 1
  · subst p
    by_cases hu : Set.univ ∈ DisjointOccurrence A B
    · have ha := (disjointOccurrence_subset_inter A B hA hB hu).1
      have hb := (disjointOccurrence_subset_inter A B hA hB hu).2
      simp [law, Measure.real, hu, ha, hb]
    · simp [law, Measure.real, hu]
      positivity
  · have hp' : p < 1 := lt_of_le_of_ne p.2.2 hp
    obtain ⟨m, q, hq, hqp⟩ := exists_orParameter p hp'
    let f : E × Fin m → E := Prod.fst
    let A' := (fun ω => f '' ω) ⁻¹' A
    let B' := (fun ω => f '' ω) ⁻¹' B
    have hreal (C : Set (Set E)) (hC : MeasurableSet C) :
        (law p).real C = (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' C) := by
      have hh := law_map_image_fst (E := E) q (Fin m)
      simp only [Fintype.card_fin, hqp] at hh
      rw [← hh]
      simp only [Measure.real, Measure.map_apply (measurable_image_fst (Fin m)) hC]
      rfl
    calc
      (law p).real (DisjointOccurrence A B) =
          (law q).real ((fun ω : Set (E × Fin m) => f '' ω) ⁻¹' DisjointOccurrence A B) :=
        hreal _ (measurableSet_finiteWitness _ (disjointOccurrence_upper A B)
          (finiteWitness_disjointOccurrence A B))
      _ ≤ (law q).real (DisjointOccurrence A' B') :=
        measureReal_mono (image_preimage_disjointOccurrence f A B)
      _ ≤ (law q).real A' * (law q).real B' := bk_finiteWitness_half q hq A' B'
        (fun _ _ h hω => hA (Set.image_mono h) hω)
        (fun _ _ h hω => hB (Set.image_mono h) hω)
        (finiteWitness_image_preimage f A hfA) (finiteWitness_image_preimage f B hfB)
      _ = (law p).real A * (law p).real B := by
        rw [hreal A (measurableSet_finiteWitness A hA hfA),
          hreal B (measurableSet_finiteWitness B hB hfB)]

end BK

end Percolation

end OAI
end

section
-- module Solutions.OAIQ078_BS.UnimodularPercolation_Clusters_KernelMoments
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Kernel Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ThreeArmProbability
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem bk_ennreal [Countable E] (p : unitInterval) (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B) (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    law p (DisjointOccurrence A B) ≤ law p A * law p B := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact bk p A B hA hB hfA hfB



end ThreeArmProbability
end Percolation


end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostBondBK
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V E T : Type*} (G : BondGraph V E) (x : V) (vertex : T → V)

lemma finiteGhostConnection_upper (m : Set T) : IsUpperSet (finiteGhostConnection G x vertex m) := by
  rintro ω η hωη ⟨i,hi,hc⟩
  exact ⟨i,hi,conn_mono G hωη hc⟩

lemma finiteGhostConnection_finiteWitness (m : Set T) :
    FiniteWitness (finiteGhostConnection G x vertex m) := by
  rintro ω ⟨i,hi,hc⟩
  obtain ⟨s,hs,hconn⟩ := finiteWitness_conn G x (vertex i) ω hc
  exact ⟨s,hs,i,hi,hconn⟩

lemma measurable_finiteGhostConnection_measure [Countable V] [Countable T] [Countable E]
    (p : unitInterval) : Measurable (fun m => law p (finiteGhostConnection G x vertex m)) := by
  have hm : MeasurableSet {z : Set T × Set E | ∃ i ∈ z.1, Conn G z.2 x (vertex i)} := by
    have heq : {z : Set T × Set E | ∃ i ∈ z.1, Conn G z.2 x (vertex i)} =
        ⋃ i : T, {z : Set T × Set E | i ∈ z.1} ∩ {z | Conn G z.2 x (vertex i)} := by
      ext z
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun i =>
      (((measurable_set_mem i).comp measurable_fst).setOf).inter
        ((measurableSet_conn G x (vertex i)).preimage measurable_snd)
  exact measurable_measure_prodMk_left (ν := law p) hm

theorem averaged_ghostConnection_bk [Countable V] [Countable T] [Countable E]
    (p : unitInterval) (ν : Measure (Set T)) :
    (∫⁻ m, ∫⁻ n, law p (DisjointOccurrence (finiteGhostConnection G x vertex m)
      (finiteGhostConnection G x vertex n)) ∂ν ∂ν) ≤
        (∫⁻ m, law p (finiteGhostConnection G x vertex m) ∂ν) ^ 2 := by
  have hm := measurable_finiteGhostConnection_measure G x vertex p
  calc
    _ ≤ ∫⁻ m, ∫⁻ n, law p (finiteGhostConnection G x vertex m) *
        law p (finiteGhostConnection G x vertex n) ∂ν ∂ν := by
      apply lintegral_mono
      intro m
      apply lintegral_mono
      intro n
      exact bk_ennreal p _ _
        (finiteGhostConnection_upper G x vertex m) (finiteGhostConnection_upper G x vertex n)
        (finiteGhostConnection_finiteWitness G x vertex m)
        (finiteGhostConnection_finiteWitness G x vertex n)
    _ = _ := by
      simp_rw [lintegral_const_mul _ hm]
      rw [lintegral_mul_const _ hm, sq]

lemma measurableSet_ghostDisjointOccurrence [Countable T] [Countable E] :
    MeasurableSet {z : (Set T × Set T) × Set E |
      z.2 ∈ DisjointOccurrence (finiteGhostConnection G x vertex z.1.1)
        (finiteGhostConnection G x vertex z.1.2)} := by
  have hsub (s : Finset E) :
      Measurable (fun z : (Set T × Set T) × Set E => (s : Set E) ⊆ z.2) := by
    exact Measurable.forall fun e =>
      measurable_const.imp ((measurable_set_mem e).comp measurable_snd)
  have hc (s : Finset E) (j : Fin 2) :
      Measurable (fun z : (Set T × Set T) × Set E =>
        ∃ i ∈ (if j = 0 then z.1.1 else z.1.2), Conn G (s : Set E) x (vertex i)) := by
    apply Measurable.exists
    intro i
    by_cases hj : j = 0
    · simpa only [ite_eq_left hj, Function.comp_def] using
        (((measurable_set_mem i).comp (measurable_fst.comp measurable_fst)).and
          (measurable_const : Measurable (fun _ : (Set T × Set T) × Set E =>
            Conn G (s : Set E) x (vertex i))))
    · simpa only [ite_eq_right hj, Function.comp_def] using
        (((measurable_set_mem i).comp (measurable_snd.comp measurable_fst)).and
          (measurable_const : Measurable (fun _ : (Set T × Set T) × Set E =>
            Conn G (s : Set E) x (vertex i))))
  exact (Measurable.exists fun s : Finset E => Measurable.exists fun t : Finset E =>
    (hsub s).and ((hsub t).and (measurable_const.and ((hc s 0).and (hc t 1))))).setOf

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_image_equiv (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact Measurable.of_eval (fun index => measurable_set_mem (e.symm index))

lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (measurable_image_equiv e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm

lemma Aut.vertexBall_ncard (φ : G.Aut) (o : V) (n : ℕ) :
    (G.vertexBall (φ.vertex o) n).ncard = (G.vertexBall o n).ncard := by
  rw [← Aut.vertexBall_image G φ,Set.ncard_image_of_injective _ φ.vertex.injective]

lemma Aut.incident_singleton_image (φ : G.Aut) (v : V) :
    φ.edge '' G.incidentEdges {v} = G.incidentEdges {φ.vertex v} := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,incidentEdges,
    Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]

lemma uniform_incident_bound (hquasi : G.QuasiTransitive) :
    ∃ D : ℕ, 1≤D ∧ ∀ v, (G.incidentEdges {v}).ncard ≤ D := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  let D := 1 + ∑ v ∈ hS.toFinset, (G.incidentEdges {v}).ncard
  refine ⟨D,by dsimp [D]; omega,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [← Aut.incident_singleton_image G φ,Set.ncard_image_of_injective _ φ.edge.injective]
  exact (Finset.single_le_sum (f := fun v => (G.incidentEdges {v}).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)).trans (Nat.le_add_left _ _)

lemma uniform_ball_bound (hquasi : G.QuasiTransitive) (n : ℕ) :
    ∃ M : ℕ, ∀ v, (G.vertexBall v n).ncard ≤ M := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  refine ⟨∑ v ∈ hS.toFinset, (G.vertexBall v n).ncard,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [Aut.vertexBall_ncard G φ]
  exact Finset.single_le_sum (f := fun v => (G.vertexBall v n).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RelativeModular
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace Subgroup
open scoped _root_.Subgroup
variable {Γ : Type*} [Group Γ]

lemma relativeMass_self (A : Subgroup Γ) : relativeMass A A = 1 := by
  simp [relativeMass]

end Subgroup
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_GraphModular
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularRatio_self (x : V) : G.modularRatio x x = 1 := by
  rw [modularRatio_eq_relativeMass,Subgroup.relativeMass_self]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterMass
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_ne_top (o x : V) : G.stabilizerWeight o x ≠ ∞ :=
  ENNReal.ofReal_ne_top

lemma stabilizerWeight_pos (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : 0 < G.stabilizerWeight o x :=
  ENNReal.ofReal_pos.mpr (G.modularRatio_pos hc hl x o)

@[simp] lemma stabilizerWeight_self (o : V) : G.stabilizerWeight o o = 1 := by
  simp [stabilizerWeight,modularRatio_self]

lemma stabilizerWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight o x =
      G.stabilizerWeight o a * G.stabilizerWeight a x := by
  unfold stabilizerWeight
  rw [←ENNReal.ofReal_mul (G.modularRatio_pos hc hl a o).le]
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedMassTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma suborbitCard_mul_modularRatio (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (x y : V) :
    (G.suborbitCard y x : ℝ) * G.modularRatio x y = G.suborbitCard x y := by
  unfold modularRatio
  have hn : (G.suborbitCard y x : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl y x))
  field_simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_TiltedTransportENNReal
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
namespace OrbitRepresentatives
variable (R : G.OrbitRepresentatives)

lemma enn_fiber_sum_root (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y)
    (x : {x // x∈R.roots}) (y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  let := (G.stabilizerOrbit_finite hc hl x y).fintype
  rw [← (fiberEquiv G R x y).symm.tsum_eq]
  have hv (z : G.stabilizerOrbit x y) :
      ennRow G R F ((fiberEquiv G R x y).symm z) = F x y := by
    change F x z = F x y
    obtain ⟨φ,hx,hy⟩ := G.mem_stabilizerOrbit.mp z.property
    have hh := hF φ x y
    rwa [hx,hy] at hh
  simp only [hv,tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : Fintype.card (G.stabilizerOrbit x y) = G.suborbitCard x y := by
    rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
    rfl
  rw [hcard]

lemma enn_fiber_sum (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) (x y : V) :
    (∑' p : (pairMap G R) ⁻¹' {G.pairOrbit x y}, ennRow G R F p) =
      (G.suborbitCard x y : ℝ≥0∞) * F x y := by
  obtain ⟨u,hu,φ,rfl⟩ := R.cover x
  let v := φ.vertex.symm y
  have hy : φ.vertex v = y := φ.vertex.apply_symm_apply y
  have hq : G.pairOrbit (φ.vertex u) y = G.pairOrbit u v := by
    rw [←hy,Aut.pairOrbit]
  rw [hq,enn_fiber_sum_root G R hc hl F hF ⟨u,hu⟩ v]
  change (G.suborbitCard u v : ℝ≥0∞) * F u v = _
  rw [←hy,Aut.suborbitCard,hF]

lemma tsum_ennRow (F : V → V → ℝ≥0∞) :
    (∑' p, ennRow G R F p) = ∑ x ∈ R.roots, ∑' y, F x y := by
  change (∑' p : {x // x∈R.roots} × V, F p.1 p.2) = _
  rw [ENNReal.tsum_prod (f := fun (x : {x // x∈R.roots}) y => F x y)]
  simp only [tsum_fintype]
  exact Finset.sum_coe_sort R.roots (fun x => ∑' y, F x y)

lemma tilted_massTransport_ennreal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : V → V → ℝ≥0∞)
    (hF : ∀ (φ : G.Aut) x y, F (φ.vertex x) (φ.vertex y) = F x y) :
    (∑ x ∈ R.roots, ∑' y, F x y) =
      ∑ y ∈ R.roots, ∑' x, F x y * G.stabilizerWeight y x := by
  let F' := fun x y => F y x * G.stabilizerWeight x y
  have hF' (φ : G.Aut) (x y : V) : F' (φ.vertex x) (φ.vertex y) = F' x y := by
    simp only [F',hF,Aut.stabilizerWeight]
  have heq : (∑' p, ennRow G R F p) = (∑' p, ennRow G R F' p) := by
    calc
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {q}, ennRow G R F p :=
        (ENNReal.tsum_fiberwise _ _).symm
      _ = ∑' q : G.PairOrbit, ∑' p : (pairMap G R) ⁻¹' {G.swapPairOrbit q},
          ennRow G R F' p := by
        apply tsum_congr
        intro q
        induction q using Quotient.inductionOn' with
        | h p =>
          change (∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.1 p.2}, ennRow G R F z) =
            ∑' z : (pairMap G R) ⁻¹' {G.pairOrbit p.2 p.1}, ennRow G R F' z
          rw [enn_fiber_sum G R hc hl F hF,enn_fiber_sum G R hc hl F' hF']
          have hbal : (G.suborbitCard p.2 p.1 : ℝ≥0∞) * G.stabilizerWeight p.2 p.1 =
              (G.suborbitCard p.1 p.2 : ℝ≥0∞) := by
            unfold stabilizerWeight
            rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg _),
              G.suborbitCard_mul_modularRatio hc hl,ENNReal.ofReal_natCast]
          simp only [F']
          rw [mul_left_comm, hbal, mul_comm]
      _ = ∑' p, ennRow G R F' p :=
        (G.swapPairOrbit.tsum_eq _).trans (ENNReal.tsum_fiberwise _ _)
  rw [tsum_ennRow G R F,tsum_ennRow G R F'] at heq
  exact heq

end OrbitRepresentatives
end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_RandomTiltedTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] (G : BondGraph V E)

omit [Countable V] in
lemma expected_enn_transport_aut (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ ω, F ω (φ.vertex x) (φ.vertex y) ∂G.law p) = ∫⁻ ω, F ω x y ∂G.law p := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [lintegral_map (hm _ _) (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [ha]

lemma OrbitRepresentatives.random_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y) :
    (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) =
      ∑ y ∈ R.roots, ∫⁻ ω, ∑' x, F ω x y * G.stabilizerWeight y x ∂G.law p := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _ (G.expected_enn_transport_aut p F hm ha)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularClusterCount
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_mul_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    G.stabilizerWeight x y*G.stabilizerWeight y x=1 := by
  rw [←G.stabilizerWeight_change_base hc hl x y x,G.stabilizerWeight_self]

lemma stabilizerWeight_inv (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    (G.stabilizerWeight x y)⁻¹=G.stabilizerWeight y x := by
  apply (ENNReal.mul_left_inj (G.stabilizerWeight_pos hc hl x y).ne' (G.stabilizerWeight_ne_top x y)).mp
  rw [ENNReal.inv_mul_cancel (G.stabilizerWeight_pos hc hl x y).ne' (G.stabilizerWeight_ne_top x y),
    G.stabilizerWeight_mul_reverse hc hl]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_TiltedGhostSusceptibility
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph

variable {V E : Type*} (G : BondGraph V E)

lemma measurable_quarterTiltedMass [Countable V] [Countable E] (x : V) :
    Measurable (fun ω => G.quarterTiltedMass ω x) := by
  apply Measurable.tsum
  intro y
  exact measurable_const.ite (G.measurable_reachable x y).setOf measurable_const

lemma quarterTiltedMass_aut (φ : G.Aut) (ω : Set E) (x : V) :
    G.quarterTiltedMass (φ.edge '' ω) (φ.vertex x) = G.quarterTiltedMass ω x := by
  unfold quarterTiltedMass
  rw [← φ.vertex.tsum_eq]
  apply tsum_congr
  intro y
  rw [Aut.stabilizerWeight]
  congr 1
  exact propext (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω))

lemma quarterTiltedMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (hxy : (G.openGraph ω).Reachable x y) :
    G.quarterTiltedMass ω y =
      G.stabilizerWeight y x ^ (1 / 4 : ℝ) * G.quarterTiltedMass ω x := by
  unfold quarterTiltedMass
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro z
  have hr : (G.openGraph ω).Reachable y z ↔ (G.openGraph ω).Reachable x z :=
    ⟨fun h => hxy.trans h,fun h => hxy.symm.trans h⟩
  rw [hr]
  split_ifs
  · rw [G.stabilizerWeight_change_base hc hl y x z, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  · simp

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostCluster
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm

variable {V E : Type*} (G : BondGraph V E)

lemma coe_quarterGhostWeight (x y : V) :
    (G.quarterGhostWeight x y : ℝ≥0∞) = G.stabilizerWeight x y ^ (1 / 4 : ℝ) := by
  exact ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (G.stabilizerWeight_ne_top x y))

lemma quarterGhostWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x v y : V) : G.quarterGhostWeight x y =
      G.quarterGhostWeight x v * G.quarterGhostWeight v y := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_mul, G.coe_quarterGhostWeight, G.coe_quarterGhostWeight,
    G.coe_quarterGhostWeight, G.stabilizerWeight_change_base hc hl x v y,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

lemma quarterGhostField_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (h : ℝ≥0) (x v : V) :
    ghostFieldLaw h (G.quarterGhostWeight x) =
      ghostFieldLaw (h * G.quarterGhostWeight x v) (G.quarterGhostWeight v) := by
  unfold ghostFieldLaw
  congr 1
  funext y
  apply Subtype.ext
  simp only [ghostRate, ghostKernel, NNReal.coe_mul, G.quarterGhostWeight_change_base hc hl x v y]
  congr 2
  ring

lemma quarterTiltedMass_finite_sum {ω : Set E} {x : V} (hfin : (G.cluster ω x).Finite) :
    G.quarterTiltedMass ω x =
      ∑ y ∈ hfin.toFinset, (G.quarterGhostWeight x y : ℝ≥0∞) := by
  unfold quarterTiltedMass
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · apply Finset.sum_congr rfl
    intro y hy
    have hr : (G.openGraph ω).Reachable x y := hfin.mem_toFinset.mp hy
    rw [ite_eq_left hr, G.coe_quarterGhostWeight]
  · intro y hy
    exact ite_eq_right (fun hr => hy (hfin.mem_toFinset.mpr hr))

lemma quarterTiltedMass_toReal_finite_sum {ω : Set E} {x : V}
    (hfin : (G.cluster ω x).Finite) :
    (G.quarterTiltedMass ω x).toReal =
      ∑ y ∈ hfin.toFinset, (G.quarterGhostWeight x y : ℝ) := by
  rw [G.quarterTiltedMass_finite_sum hfin, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro y _
    exact ENNReal.coe_toReal _
  · intro y _
    exact ENNReal.coe_ne_top

lemma ghost_hit_cluster_joint_measurable [Countable V] [Countable E] (x : V) :
    MeasurableSet {z : Set E × Set V | ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2} := by
  exact (Measurable.exists fun y =>
    ((G.measurable_reachable x y).comp measurable_fst).and
      ((measurable_set_mem y).comp measurable_snd)).setOf

theorem quarterGhostField_hit_cluster [Countable V] (h : ℝ≥0) {ω : Set E} {x : V}
    (hfin : (G.cluster ω x).Finite) :
    (ghostFieldLaw h (G.quarterGhostWeight x)).real (ghostHits (G.cluster ω x)) =
      ghostKernel h (G.quarterTiltedMass ω x).toReal := by
  rw [G.quarterTiltedMass_toReal_finite_sum hfin]
  convert ghostFieldLaw_real_hit_finset h (G.quarterGhostWeight x) hfin.toFinset using 1
  all_goals try with_reducible_and_instances rfl
  rw [hfin.coe_toFinset]

theorem quarterTwoGhostField_hit_cluster [Countable V] (h : ℝ≥0) {ω : Set E} {x : V}
    (hfin : (G.cluster ω x).Finite) :
    ((ghostFieldLaw h (G.quarterGhostWeight x)).prod
      (ghostFieldLaw h (G.quarterGhostWeight x))).real
      (ghostHits (G.cluster ω x) ×ˢ ghostHits (G.cluster ω x)) =
        ghostKernel h (G.quarterTiltedMass ω x).toReal ^ 2 := by
  rw [G.quarterTiltedMass_toReal_finite_sum hfin]
  convert twoGhostFieldLaw_real_hit_finset h (G.quarterGhostWeight x) hfin.toFinset using 1
  all_goals try with_reducible_and_instances rfl
  rw [hfin.coe_toFinset]

theorem quarterGhostConnection_average [Countable V] [Countable E]
    (p : unitInterval) (x : V) (h : ℝ≥0)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    (∫⁻ m, G.law p {ω | ∃ y ∈ m, (G.openGraph ω).Reachable x y}
      ∂ghostFieldLaw h (G.quarterGhostWeight x)) =
        ENNReal.ofReal (G.quarterGhostMagnetization p x h) := by
  let ν := ghostFieldLaw h (G.quarterGhostWeight x)
  let A := {z : Set E × Set V | ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2}
  have hm : MeasurableSet A := G.ghost_hit_cluster_joint_measurable x
  have he := (Measure.prod_apply (μ := G.law p) (ν := ν) hm).symm.trans
    (Measure.prod_apply_symm (μ := G.law p) (ν := ν) hm)
  have hswap : (∫⁻ m, G.law p {ω | ∃ y ∈ m, (G.openGraph ω).Reachable x y} ∂ν) =
      ∫⁻ ω, ν (ghostHits (G.cluster ω x)) ∂G.law p := by
    convert he.symm using 1
    · apply lintegral_congr
      intro m
      congr 1
      ext ω
      simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
      exact exists_congr (fun y => and_comm)
    · rfl
  rw [hswap]
  have hprob : (fun ω => ν (ghostHits (G.cluster ω x))) =ᵐ[G.law p]
      (fun ω => ENNReal.ofReal (ghostKernel h (G.quarterTiltedMass ω x).toReal)) := by
    filter_upwards [hfin] with ω hω
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact congrArg ENNReal.ofReal (G.quarterGhostField_hit_cluster h hω)
  rw [lintegral_congr_ae hprob]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_ghostKernel (G.law p) _ (G.measurable_quarterTiltedMass x).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) h.2)
    (ae_of_all _ fun _ => ghostKernel_nonneg h.2 ENNReal.toReal_nonneg)).symm

theorem quarterGhostConnection_change_base [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (x v : V) (h : ℝ≥0)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω v).Finite) :
    (∫⁻ m, G.law p {ω | ∃ y ∈ m, (G.openGraph ω).Reachable v y}
      ∂ghostFieldLaw h (G.quarterGhostWeight x)) =
        ENNReal.ofReal (G.quarterGhostMagnetization p v (h * G.quarterGhostWeight x v)) := by
  rw [G.quarterGhostField_change_base hc hl h x v]
  exact G.quarterGhostConnection_average p v _ hfin

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostTiltedTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma measurable_ghostAvoid (h : ℝ) : Measurable (ghostAvoid h) := by
  exact measurable_const.ite (measurableSet_eq_fun measurable_id measurable_const)
    ((measurable_const.mul measurable_id.ennreal_toReal).exp.ennreal_ofReal)

lemma ghostAvoid_antitone {h : ℝ} (hh : 0 ≤ h) : Antitone (ghostAvoid h) := by
  intro m n hmn
  by_cases hn : n = ⊤
  · simp [ghostAvoid, hn]
  · have hm : m ≠ ⊤ := ne_top_of_le_ne_top hn hmn
    rw [ghostAvoid, ite_eq_right hn, ghostAvoid, ite_eq_right hm]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (ENNReal.toReal_mono hn hmn) (neg_nonpos.mpr hh)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm

variable {V E : Type*} (G : BondGraph V E)

lemma measurable_ghostHighTransport [Countable V] [Countable E]
    (h : ℝ) (x y : V) : Measurable (fun ω => G.ghostHighTransport h ω x y) := by
  exact (((measurable_ghostAvoid h).comp (G.measurable_quarterTiltedMass x)).mul_const _).ite
    ((G.measurable_reachable x y).and measurable_const).setOf measurable_const

lemma ghostHighTransport_aut (h : ℝ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.ghostHighTransport h (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.ghostHighTransport h ω x y := by
  unfold ghostHighTransport
  rw [Aut.stabilizerWeight, G.quarterTiltedMass_aut]
  congr 1
  exact propext (and_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)) Iff.rfl)

lemma ghostHighTransport_incoming_le
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {h : ℝ} (hh : 0 ≤ h) (ω : Set E) (y : V) :
    (∑' x, G.ghostHighTransport h ω x y * G.stabilizerWeight y x) ≤
      ghostAvoid h (G.quarterTiltedMass ω y) * G.quarterTiltedMass ω y := by
  rw [quarterTiltedMass, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  unfold ghostHighTransport
  by_cases hr : (G.openGraph ω).Reachable x y
  · have hr' := hr.symm
    simp only [hr, hr', true_and, ↓reduceIte]
    by_cases hw : 1 < G.stabilizerWeight x y
    · rw [ite_eq_left hw]
      have hmass : G.quarterTiltedMass ω y ≤ G.quarterTiltedMass ω x := by
        rw [G.quarterTiltedMass_change_base hc hl ω hr']
        calc
          _ = 1 * G.quarterTiltedMass ω y := (one_mul _).symm
          _ ≤ _ := mul_le_mul' (ENNReal.one_le_rpow hw.le (by norm_num)) le_rfl
      have ha := ghostAvoid_antitone hh hmass
      have hrev : G.stabilizerWeight y x ≤ 1 := by
        rw [← G.stabilizerWeight_inv hc hl x y]
        exact ENNReal.inv_le_one.mpr hw.le
      have hp : G.stabilizerWeight x y ^ (3 / 8 : ℝ) * G.stabilizerWeight y x ≤
          G.stabilizerWeight y x ^ (1 / 4 : ℝ) := by
        rw [← G.stabilizerWeight_inv hc hl y x, ENNReal.inv_rpow, ← ENNReal.rpow_neg]
        nth_rw 2 [← ENNReal.rpow_one (G.stabilizerWeight y x)]
        rw [← ENNReal.rpow_add _ _ (G.stabilizerWeight_pos hc hl y x).ne'
          (G.stabilizerWeight_ne_top y x)]
        exact ENNReal.rpow_le_rpow_of_exponent_ge hrev (by norm_num)
      calc
        _ = ghostAvoid h (G.quarterTiltedMass ω x) *
            (G.stabilizerWeight x y ^ (3 / 8 : ℝ) * G.stabilizerWeight y x) := by ac_rfl
        _ ≤ _ := mul_le_mul' ha hp
    · simp [hw]
  · have hr' : ¬ (G.openGraph ω).Reachable y x := fun h => hr h.symm
    simp [hr,hr']

theorem ghostHighTransport_expected_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, ∑' y, G.ghostHighTransport h ω x y ∂G.law p) ≤
      ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p := by
  rw [OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
    (G.ghostHighTransport h) (G.measurable_ghostHighTransport h) (G.ghostHighTransport_aut h)]
  apply Finset.sum_le_sum
  intro y _
  exact lintegral_mono fun ω => G.ghostHighTransport_incoming_le hc hl hh ω y

lemma ghostWeightedCount_le (h : ℝ) (ω : Set E) (x : V) :
    G.ghostWeightedCount h ω x ≤
      ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x +
        ∑' y, G.ghostHighTransport h ω x y := by
  rw [quarterTiltedMass, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro y
  unfold ghostHighTransport
  by_cases hr : (G.openGraph ω).Reachable x y
  · simp only [hr, true_and, ↓reduceIte]
    by_cases hw : 1 < G.stabilizerWeight x y
    · rw [ite_eq_left hw]
      exact le_add_left le_rfl
    · rw [ite_eq_right hw, add_zero]
      exact mul_le_mul' le_rfl
        (ENNReal.rpow_le_rpow_of_exponent_ge (le_of_not_gt hw) (by norm_num))
  · simp [hr]

theorem expected_ghostWeightedCount_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ ω, G.ghostWeightedCount h ω x ∂G.law p) ≤
      2 * ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p := by
  calc
    _ ≤ ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x +
          ∑' y, G.ghostHighTransport h ω x y ∂G.law p := by
      apply Finset.sum_le_sum
      intro x _
      exact lintegral_mono fun ω => G.ghostWeightedCount_le h ω x
    _ = (∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p) +
        ∑ x ∈ (G.orbitRepresentatives hq).roots,
          ∫⁻ ω, ∑' y, G.ghostHighTransport h ω x y ∂G.law p := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact lintegral_add_left
        (((measurable_ghostAvoid h).comp (G.measurable_quarterTiltedMass x)).mul
          (G.measurable_quarterTiltedMass x)) _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add le_rfl (G.ghostHighTransport_expected_le hc hl hq p hh)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostDerivative
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma ghostAvoid_mul_mass (h : ℝ) (m : ℝ≥0∞) :
    ghostAvoid h m * m = ENNReal.ofReal (m.toReal * Real.exp (-h * m.toReal)) := by
  by_cases hm : m = ⊤
  · simp [ghostAvoid,hm]
  · rw [ghostAvoid,ite_eq_right hm,← ENNReal.ofReal_toReal hm,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    ring

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma lintegral_ghostAvoid_mass_eq_derivative (p : unitInterval) (x : V)
    {h : ℝ} (hh : 0 < h) :
    (∫⁻ ω, ghostAvoid h (G.quarterTiltedMass ω x) * G.quarterTiltedMass ω x ∂G.law p) =
      ENNReal.ofReal (G.quarterGhostDerivative p x h) := by
  unfold quarterGhostDerivative ghostMagnetizationDerivative
  have hI := (hasDerivAt_ghostMagnetization (G.law p)
    (fun ω => (G.quarterTiltedMass ω x).toReal)
    (G.measurable_quarterTiltedMass x).ennreal_toReal (fun _ => ENNReal.toReal_nonneg) hh).1
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (ae_of_all _ fun ω => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)]
  exact lintegral_congr (fun ω => ghostAvoid_mul_mass h (G.quarterTiltedMass ω x))

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostDoubleConnection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem quarterTwoGhostConnection_average (p : unitInterval) (x : V) (h : ℝ≥0)
    (hfin : ∀ᵐ ω ∂G.law p, (G.cluster ω x).Finite) :
    (∫⁻ m, ∫⁻ n, G.law p {ω |
      (∃ y ∈ m, (G.openGraph ω).Reachable x y) ∧
      (∃ y ∈ n, (G.openGraph ω).Reachable x y)}
      ∂ghostFieldLaw h (G.quarterGhostWeight x)
      ∂ghostFieldLaw h (G.quarterGhostWeight x)) =
      ENNReal.ofReal (∫ ω, ghostKernel h (G.quarterTiltedMass ω x).toReal ^ 2 ∂G.law p) := by
  let ν := ghostFieldLaw h (G.quarterGhostWeight x)
  let A := {z : Set E × (Set V × Set V) |
    (∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.1) ∧
    (∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.2)}
  have hm : MeasurableSet A := by
    have h₁ : Measurable (fun z : Set E × (Set V × Set V) =>
        ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.1) :=
      Measurable.exists fun y => ((G.measurable_reachable x y).comp measurable_fst).and
        ((measurable_set_mem y).comp (measurable_fst.comp measurable_snd))
    have h₂ : Measurable (fun z : Set E × (Set V × Set V) =>
        ∃ y, (G.openGraph z.1).Reachable x y ∧ y ∈ z.2.2) :=
      Measurable.exists fun y => ((G.measurable_reachable x y).comp measurable_fst).and
        ((measurable_set_mem y).comp (measurable_snd.comp measurable_snd))
    exact (h₁.and h₂).setOf
  have hswap := (Measure.prod_apply (μ := G.law p) (ν := ν.prod ν) hm).symm.trans
    (Measure.prod_apply_symm (μ := G.law p) (ν := ν.prod ν) hm)
  have hmeas : Measurable (fun z : Set V × Set V => G.law p ((fun ω : Set E => (ω,z)) ⁻¹' A)) :=
    measurable_measure_prodMk_right hm
  have hmeas' : Measurable (fun z : Set V × Set V => G.law p {ω |
      (∃ y ∈ z.1, (G.openGraph ω).Reachable x y) ∧
      (∃ y ∈ z.2, (G.openGraph ω).Reachable x y)}) := by
    convert hmeas using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    congr 1
    ext ω
    simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
    exact and_congr (exists_congr fun y => and_comm) (exists_congr fun y => and_comm)
  have he : (∫⁻ m, ∫⁻ n, G.law p {ω |
      (∃ y ∈ m, (G.openGraph ω).Reachable x y) ∧
      (∃ y ∈ n, (G.openGraph ω).Reachable x y)} ∂ν ∂ν) =
      ∫⁻ ω, (ν.prod ν) (ghostHits (G.cluster ω x) ×ˢ ghostHits (G.cluster ω x)) ∂G.law p := by
    rw [← lintegral_prod _ hmeas'.aemeasurable]
    convert hswap.symm using 1
    · apply lintegral_congr
      intro z
      congr 1
      ext ω
      simp only [A, Set.mem_preimage, Set.mem_ofPred_eq]
      exact and_congr (exists_congr fun y => and_comm) (exists_congr fun y => and_comm)
    · rfl
  rw [he]
  have hprob : (fun ω => (ν.prod ν) (ghostHits (G.cluster ω x) ×ˢ ghostHits (G.cluster ω x)))
      =ᵐ[G.law p] (fun ω => ENNReal.ofReal (ghostKernel h (G.quarterTiltedMass ω x).toReal ^ 2)) := by
    filter_upwards [hfin] with ω hω
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact congrArg ENNReal.ofReal (G.quarterTwoGhostField_hit_cluster h hω)
  rw [lintegral_congr_ae hprob]
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_ghostKernel_sq (G.law p) _ (G.measurable_quarterTiltedMass x).ennreal_toReal
      (fun _ => ENNReal.toReal_nonneg) h.2)
    (ae_of_all _ fun _ => sq_nonneg _)).symm

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostMomentBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma quarterThreeQuarterMoment_aut (p : unitInterval) (φ : G.Aut) (x : V) :
    G.quarterThreeQuarterMoment p (φ.vertex x) = G.quarterThreeQuarterMoment p x := by
  unfold quarterThreeQuarterMoment
  conv_lhs => rw [← G.law_map_aut p φ]
  have hm : Measurable (fun ω => G.quarterTiltedMass ω (φ.vertex x) ^ (3 / 4 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp (G.measurable_quarterTiltedMass _)
  rw [lintegral_map hm (BernoulliProduct.measurable_image_equiv φ.edge)]
  simp only [G.quarterTiltedMass_aut]

theorem uniform_quarterGhost_moment_bound (hq : G.QuasiTransitive) (p : unitInterval)
    (hfin : ∀ x ∈ (G.orbitRepresentatives hq).roots,
      G.quarterThreeQuarterMoment p x < ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ x h, 0 ≤ h →
      G.quarterGhostMagnetization p x h ≤ K * h ^ (3 / 4 : ℝ) := by
  let C := ∑ x ∈ (G.orbitRepresentatives hq).roots, G.quarterThreeQuarterMoment p x
  have hC : C < ⊤ := ENNReal.sum_lt_top.mpr hfin
  have hxC (x : V) : G.quarterThreeQuarterMoment p x ≤ C := by
    obtain ⟨y,hy,φ,rfl⟩ := (G.orbitRepresentatives hq).cover x
    rw [G.quarterThreeQuarterMoment_aut]
    exact Finset.single_le_sum (fun _ _ => bot_le) hy
  refine ⟨C.toReal + 1,by positivity,?_⟩
  intro x h hh
  have hxfin := lt_of_le_of_lt (hxC x) hC
  have hpow : Measurable (fun ω => G.quarterTiltedMass ω x ^ (3 / 4 : ℝ)) :=
    ENNReal.continuous_rpow_const.measurable.comp (G.measurable_quarterTiltedMass x)
  have hXi : Integrable (fun ω => (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ))
      (G.law p) := by
    simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top hpow.aemeasurable hxfin.ne
  have hI : (∫ ω, (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ) ∂G.law p) ≤ C.toReal := by
    have he := integral_toReal hpow.aemeasurable (ae_lt_top hpow hxfin.ne)
    calc
      _ = ∫ ω, (G.quarterTiltedMass ω x ^ (3 / 4 : ℝ)).toReal ∂G.law p :=
        integral_congr_ae (ae_of_all _ fun ω => ENNReal.toReal_rpow _ _)
      _ = (G.quarterThreeQuarterMoment p x).toReal := he
      _ ≤ C.toReal := ENNReal.toReal_mono hC.ne (hxC x)
  calc
    _ ≤ ∫ ω, h ^ (3 / 4 : ℝ) * (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ)
        ∂G.law p := by
      apply integral_mono
        (integrable_ghostKernel (G.law p) _ (G.measurable_quarterTiltedMass x).ennreal_toReal
          (fun _ => ENNReal.toReal_nonneg) hh) (hXi.const_mul _)
      intro ω
      exact (ghostKernel_le_threeQuarter hh ENNReal.toReal_nonneg).trans_eq
        (Real.mul_rpow hh ENNReal.toReal_nonneg)
    _ = h ^ (3 / 4 : ℝ) * ∫ ω, (G.quarterTiltedMass ω x).toReal ^ (3 / 4 : ℝ)
        ∂G.law p := integral_const_mul _ _
    _ ≤ _ := by
      have hp : 0 ≤ h ^ (3 / 4 : ℝ) := Real.rpow_nonneg hh _
      nlinarith

omit [Countable V] [Countable E] in
lemma quarterGhost_square_bound {p : unitInterval} {K : ℝ}
    (hbound : ∀ x h, 0 ≤ h → G.quarterGhostMagnetization p x h ≤ K * h ^ (3 / 4 : ℝ))
    (x : V) {h : ℝ} (hh : 0 ≤ h) :
    G.quarterGhostMagnetization p x h ^ 2 ≤ K ^ 2 * h ^ (3 / 2 : ℝ) := by
  have hnonneg : 0 ≤ G.quarterGhostMagnetization p x h :=
    integral_nonneg (fun _ => ghostKernel_nonneg hh ENNReal.toReal_nonneg)
  have hpow : (h ^ (3 / 4 : ℝ)) ^ 2 = h ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_mul_natCast hh]
    norm_num
  calc
    _ ≤ (K * h ^ (3 / 4 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hnonneg (hbound x h hh) 2
    _ = _ := by rw [mul_pow,hpow]

omit [Countable V] [Countable E] in
lemma quarterGhostWeight_threeHalf (x v : V) :
    (G.quarterGhostWeight x v : ℝ) ^ (3 / 2 : ℝ) =
      (G.stabilizerWeight x v ^ (3 / 8 : ℝ)).toReal := by
  rw [← ENNReal.coe_toReal (G.quarterGhostWeight x v), G.coe_quarterGhostWeight,
    ENNReal.toReal_rpow, ← ENNReal.rpow_mul]
  norm_num

omit [Countable V] [Countable E] in
lemma rebased_quarterGhost_square_bound {p : unitInterval} {K : ℝ}
    (hbound : ∀ x h, 0 ≤ h → G.quarterGhostMagnetization p x h ≤ K * h ^ (3 / 4 : ℝ))
    (x v : V) {h : ℝ} (hh : 0 ≤ h) :
    G.quarterGhostMagnetization p v (h * G.quarterGhostWeight x v) ^ 2 ≤
      K ^ 2 * h ^ (3 / 2 : ℝ) * (G.stabilizerWeight x v ^ (3 / 8 : ℝ)).toReal := by
  have hb := G.quarterGhost_square_bound hbound v (mul_nonneg hh (G.quarterGhostWeight x v).2)
  rw [Real.mul_rpow hh (G.quarterGhostWeight x v).2] at hb
  erw [G.quarterGhostWeight_threeHalf, ← mul_assoc] at hb
  exact hb

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostFan
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V : Type*} {H : SimpleGraph V}

lemma GhostFan.symm {A B : Set V} {x : V} (h : GhostFan H A B x) : GhostFan H B A x := by
  obtain ⟨a,ha,b,hb,p,q,hpq⟩ := h
  exact ⟨b,hb,a,ha,q,p,hpq.symm⟩

lemma walk_edges_disjoint_of_single_support_intersection
    {u v a b z : V} (p : H.Walk u v) (q : H.Walk a b)
    (h : ∀ x ∈ p.support, x ∈ q.support → x = z) : p.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e hp hq
  obtain ⟨⟨c,d⟩,he⟩ := Quot.exists_rep e
  rw [← he] at hp hq
  have hc := h c (p.fst_mem_support_of_mem_edges hp) (q.fst_mem_support_of_mem_edges hq)
  have hd := h d (p.snd_mem_support_of_mem_edges hp) (q.snd_mem_support_of_mem_edges hq)
  exact (p.adj_of_mem_edges hp).ne (hc.trans hd.symm)

lemma ghostFan_of_trail_support {A B : Set V} {a b x : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : H.Walk a b) (hp : p.IsTrail) (hx : x ∈ p.support) :
    GhostFan H A B x := by
  refine ⟨a,ha,b,hb,(p.takeUntil x hx).reverse,p.dropUntil x hx,?_⟩
  simpa only [SimpleGraph.Walk.edges_reverse, List.disjoint_reverse_left] using
    hp.disjoint_edges_takeUntil_dropUntil hx

lemma ghostFan_of_first_arm_support {A B : Set V} {w a b x : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : H.Walk w a) (q : H.Walk w b)
    (hp : p.IsTrail) (hq : q.IsTrail) (hpq : p.edges.Disjoint q.edges) (hx : x ∈ p.support) :
    GhostFan H A B x := by
  apply ghostFan_of_trail_support ha hb (p.reverse.append q)
  · exact (SimpleGraph.Walk.isTrail_append _ _).mpr
      ⟨hp.reverse,hq,by simpa using hpq⟩
  · exact SimpleGraph.Walk.support_subset_support_append_left _ _ (by simpa using hx)

lemma ghostFan_of_arm_avoiding_prefix {A B : Set V} {u w a b v : V}
    (ha : a ∈ A) (hb : b ∈ B) (p : H.Walk w a) (q : H.Walk w b)
    (hpq : p.edges.Disjoint q.edges) (huw : H.Adj u w)
    (hu : u ∉ p.support) (r : H.Walk u v) (hv : v ∈ p.support)
    (hrq : r.edges.Disjoint q.edges)
    (hre : s(u,w) ∉ r.edges) : GhostFan H A B u := by
  refine ⟨a,ha,b,hb,r.append (p.dropUntil v hv),SimpleGraph.Walk.cons huw q,?_⟩
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons]
  apply List.disjoint_left.mpr
  intro e he he'
  rcases List.mem_append.mp he with her | hep
  · rcases List.mem_cons.mp he' with he' | heq
    · exact hre (he' ▸ her)
    · exact List.disjoint_left.mp hrq her heq
  · have hep' := p.edges_dropUntil_subset_edges hv hep
    rcases List.mem_cons.mp he' with he' | heq
    · exact hu (p.fst_mem_support_of_mem_edges (he' ▸ hep'))
    · exact List.disjoint_left.mp hpq hep' heq

lemma GhostFan.of_alternate_walk {A B : Set V} {u w : V}
    (h : GhostFan H A B w) (huw : H.Adj u w)
    (r : H.Walk u w) (hre : s(u,w) ∉ r.edges) : GhostFan H A B u := by
  classical
  obtain ⟨a,ha,b,hb,p₀,q₀,hpq₀⟩ := h
  let p : H.Walk w a := p₀.toPath
  let q : H.Walk w b := q₀.toPath
  have hp : p.IsTrail := p₀.toPath.property.isTrail
  have hq : q.IsTrail := q₀.toPath.property.isTrail
  have hpq : p.edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hpq₀
      (p₀.edges_toPath_subset_edges hep) (q₀.edges_toPath_subset_edges heq)
  by_cases hu : u ∈ p.support
  · exact ghostFan_of_first_arm_support ha hb p q hp hq hpq hu
  by_cases hu' : u ∈ q.support
  · exact (ghostFan_of_first_arm_support hb ha q p hq hp hpq.symm hu').symm
  let S := p.support.toFinset ∪ q.support.toFinset
  have hwS : w ∈ S := Finset.mem_union_left _ (List.mem_toFinset.mpr p.start_mem_support)
  obtain ⟨v,hv,hvr,hfirst⟩ := r.exists_mem_support_forall_mem_support_imp_eq S
    ⟨w,Finset.mem_filter.mpr ⟨hwS,r.end_mem_support⟩⟩
  let r' := r.takeUntil v hvr
  have hrp : r'.edges.Disjoint p.edges := by
    apply walk_edges_disjoint_of_single_support_intersection r' p
    intro x hxr hxp
    exact hfirst x (Finset.mem_union_left _ (List.mem_toFinset.mpr hxp)) hxr
  have hrq : r'.edges.Disjoint q.edges := by
    apply walk_edges_disjoint_of_single_support_intersection r' q
    intro x hxr hxq
    exact hfirst x (Finset.mem_union_right _ (List.mem_toFinset.mpr hxq)) hxr
  have hre' : s(u,w) ∉ r'.edges := fun he => hre (r.edges_takeUntil_subset_edges hvr he)
  rcases Finset.mem_union.mp hv with hvp | hvq
  · exact ghostFan_of_arm_avoiding_prefix ha hb p q hpq huw hu r'
      (List.mem_toFinset.mp hvp) hrq hre'
  · exact (ghostFan_of_arm_avoiding_prefix hb ha q p hpq.symm huw hu' r'
      (List.mem_toFinset.mp hvq) hrp hre').symm

lemma GhostFan.of_not_isBridge {A B : Set V} {u w : V}
    (h : GhostFan H A B w) (huw : H.Adj u w) (he : ¬H.IsBridge s(u,w)) :
    GhostFan H A B u := by
  obtain ⟨r,hr⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp
    (not_not.mp (SimpleGraph.isBridge_iff.not.mp he))
  exact h.of_alternate_walk huw r hr

lemma exists_bridge_to_ghostFan {A B : Set V} {x w : V}
    (r : H.Walk x w) (hw : GhostFan H A B w) (hx : ¬GhostFan H A B x) :
    ∃ u v, H.Adj u v ∧ H.IsBridge s(u,v) ∧
      (H.deleteEdges {s(u,v)}).Reachable x u ∧ GhostFan H A B v ∧ ¬GhostFan H A B u := by
  induction r with
  | nil => exact (hx hw).elim
  | @cons x y w hxy r ih =>
    by_cases hy : GhostFan H A B y
    · have he : H.IsBridge s(x,y) := by
        by_contra hn
        exact hx (hy.of_not_isBridge hxy hn)
      exact ⟨x,y,hxy,he,SimpleGraph.Reachable.refl x,hy,hx⟩
    · obtain ⟨u,v,huv,he,hreach,hv,hu⟩ := ih hw hy
      have hne : s(x,y) ≠ s(u,v) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨hxu,hyv⟩ | ⟨hxv,hyu⟩
        · exact hy (hyv ▸ hv)
        · exact hx (hxv ▸ hv)
      have hxy' : (H.deleteEdges {s(u,v)}).Adj x y := by
        exact SimpleGraph.deleteEdges_adj.mpr ⟨hxy,by simpa using hne⟩
      exact ⟨u,v,huv,he,hxy'.reachable.trans hreach,hv,hu⟩

lemma walk_edges_disjoint_of_bridge {u v a b : V} (he : H.IsBridge s(u,v))
    (p : H.Walk u a) (q : H.Walk v b)
    (hp : s(u,v) ∉ p.edges) (hq : s(u,v) ∉ q.edges) : p.edges.Disjoint q.edges := by
  apply List.disjoint_left.mpr
  intro e hep heq
  obtain ⟨⟨c,d⟩,he'⟩ := Quot.exists_rep e
  rw [← he'] at hep heq
  have hc := p.fst_mem_support_of_mem_edges hep
  have hc' := q.fst_mem_support_of_mem_edges heq
  let r := (p.takeUntil c hc).append (q.takeUntil c hc').reverse
  have hr : s(u,v) ∉ r.edges := by
    simp only [r, SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_reverse,
      List.mem_append, List.mem_reverse, not_or]
    exact ⟨fun h => hp (p.edges_takeUntil_subset_edges hc h),
      fun h => hq (q.edges_takeUntil_subset_edges hc' h)⟩
  exact hr (SimpleGraph.isBridge_iff_forall_walk_mem_edges.mp he r)

lemma bridge_to_ghostFan_avoids_marks {A B : Set V} {u v : V}
    (huv : H.Adj u v) (he : H.IsBridge s(u,v))
    (hv : GhostFan H A B v) (hu : ¬GhostFan H A B u) :
    (∀ a ∈ A, ¬(H.deleteEdges {s(u,v)}).Reachable u a) ∧
    (∀ b ∈ B, ¬(H.deleteEdges {s(u,v)}).Reachable u b) := by
  classical
  suffices h : ∀ (C D : Set V), GhostFan H C D v → ¬GhostFan H C D u →
      ∀ a ∈ C, ¬(H.deleteEdges {s(u,v)}).Reachable u a by
    exact ⟨h A B hv hu,h B A hv.symm (fun hf => hu hf.symm)⟩
  intro C D hv hu a ha hreach
  obtain ⟨a₀,ha₀,b,hb,p₀,q₀,hpq₀⟩ := hv
  let p : H.Walk v a₀ := p₀.toPath
  let q : H.Walk v b := q₀.toPath
  have hpq : p.edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hpq₀
      (p₀.edges_toPath_subset_edges hep) (q₀.edges_toPath_subset_edges heq)
  have huq : u ∉ q.support := by
    intro h
    exact hu (ghostFan_of_first_arm_support hb ha₀ q p
      q₀.toPath.property.isTrail p₀.toPath.property.isTrail hpq.symm h).symm
  have hqe : s(u,v) ∉ q.edges := fun h => huq (q.fst_mem_support_of_mem_edges h)
  obtain ⟨r,hr⟩ := SimpleGraph.reachable_deleteEdges_iff_exists_walk.mp hreach
  have hrq := walk_edges_disjoint_of_bridge he r q hr hqe
  apply hu
  refine ⟨a,ha,b,hb,r,SimpleGraph.Walk.cons huv q,?_⟩
  rw [SimpleGraph.Walk.edges_cons]
  apply List.disjoint_left.mpr
  intro e her heq
  rcases List.mem_cons.mp heq with heq | heq
  · exact hr (heq ▸ her)
  · exact List.disjoint_left.mp hrq her heq

lemma ghostFan_delete_bridge {A B : Set V} {u v : V}
    (hv : GhostFan H A B v) (hu : ¬GhostFan H A B u) :
    GhostFan (H.deleteEdges {s(u,v)}) A B v := by
  classical
  obtain ⟨a,ha,b,hb,p₀,q₀,hpq₀⟩ := hv
  let p : H.Walk v a := p₀.toPath
  let q : H.Walk v b := q₀.toPath
  have hpq : p.edges.Disjoint q.edges := by
    apply List.disjoint_left.mpr
    intro e hep heq
    exact List.disjoint_left.mp hpq₀
      (p₀.edges_toPath_subset_edges hep) (q₀.edges_toPath_subset_edges heq)
  have hup : u ∉ p.support := by
    intro h
    exact hu (ghostFan_of_first_arm_support ha hb p q
      p₀.toPath.property.isTrail q₀.toPath.property.isTrail hpq h)
  have huq : u ∉ q.support := by
    intro h
    exact hu (ghostFan_of_first_arm_support hb ha q p
      q₀.toPath.property.isTrail p₀.toPath.property.isTrail hpq.symm h).symm
  have hpe : s(u,v) ∉ p.edges := fun h => hup (p.fst_mem_support_of_mem_edges h)
  have hqe : s(u,v) ∉ q.edges := fun h => huq (q.fst_mem_support_of_mem_edges h)
  refine ⟨a,ha,b,hb,p.toDeleteEdge s(u,v) hpe,q.toDeleteEdge s(u,v) hqe,?_⟩
  simpa using hpq

lemma two_connections_fan_or_bridge {A B : Set V} {x : V}
    (hA : ∃ a ∈ A, H.Reachable x a) (hB : ∃ b ∈ B, H.Reachable x b) :
    GhostFan H A B x ∨ ∃ u v, H.Adj u v ∧ H.IsBridge s(u,v) ∧
      (H.deleteEdges {s(u,v)}).Reachable x u ∧
      (∀ a ∈ A, ¬(H.deleteEdges {s(u,v)}).Reachable x a) ∧
      (∀ b ∈ B, ¬(H.deleteEdges {s(u,v)}).Reachable x b) ∧
      GhostFan (H.deleteEdges {s(u,v)}) A B v := by
  classical
  by_cases hx : GhostFan H A B x
  · exact Or.inl hx
  right
  obtain ⟨a,ha,⟨p⟩⟩ := hA
  obtain ⟨b,hb,⟨q⟩⟩ := hB
  have haFan : GhostFan H A B a :=
    ⟨a,ha,b,hb,SimpleGraph.Walk.nil,p.reverse.append q,by simp⟩
  obtain ⟨u,v,huv,he,hxu,hv,hu⟩ := exists_bridge_to_ghostFan p haFan hx
  obtain ⟨hA,hB⟩ := bridge_to_ghostFan_avoids_marks huv he hv hu
  exact ⟨u,v,huv,he,hxu,
    fun a ha hxa => hA a ha (hxu.symm.trans hxa),
    fun b hb hxb => hB b hb (hxu.symm.trans hxb),ghostFan_delete_bridge hv hu⟩

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostFanBK
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm

variable {V E T : Type*} (G : BondGraph V E) (x : V) (vertex : T → V)

lemma ghostFan_mem_disjointOccurrence {ω : Set E} {m n : Set T}
    (h : GhostFan (openSimpleGraph G ω) (vertex '' m) (vertex '' n) x) :
    ω ∈ DisjointOccurrence (finiteGhostConnection G x vertex m)
      (finiteGhostConnection G x vertex n) := by
  obtain ⟨a,⟨i,hi,rfl⟩,b,⟨j,hj,rfl⟩,p,q,hpq⟩ := h
  obtain ⟨s,hs,hse,hso⟩ := walk_lift_bonds G ω p
  obtain ⟨t,ht,hte,hto⟩ := walk_lift_bonds G ω q
  refine ⟨s.toFinset,t.toFinset,?_,?_,?_,?_,?_⟩
  · intro e he
    exact hso e (List.mem_toFinset.mp he)
  · intro e he
    exact hto e (List.mem_toFinset.mp he)
  · apply Finset.disjoint_left.mpr
    intro e hes het
    exact List.disjoint_left.mp hpq
      (hse ▸ List.mem_map_of_mem (List.mem_toFinset.mp hes))
      (hte ▸ List.mem_map_of_mem (List.mem_toFinset.mp het))
  · exact ⟨i,hi,hs.conn (fun e he => List.mem_toFinset.mpr he)⟩
  · exact ⟨j,hj,ht.conn (fun e he => List.mem_toFinset.mpr he)⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalBound
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma finiteGhostConnection_mono_marks (G : BondGraph V E) (x : V)
    {m n : Set V} (hmn : m ⊆ n) :
    finiteGhostConnection G x id m ⊆ finiteGhostConnection G x id n := by
  rintro ω ⟨v,hv,hconn⟩
  exact ⟨v,hmn hv,hconn⟩

theorem ghost_avoidance_bk (G : BondGraph V E) (p : unitInterval) (x : V)
    (h : ℝ≥0) (w : V → ℝ≥0) (S : Finset V) :
    (∫⁻ m, ∫⁻ n, if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n then
      law p (DisjointOccurrence (finiteGhostConnection G x id m)
        (finiteGhostConnection G x id n)) else 0 ∂ghostFieldLaw h w ∂ghostFieldLaw h w) ≤
      ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ v ∈ S, (w v : ℝ))) ^ 2 *
        (∫⁻ m, law p (finiteGhostConnection G x id m) ∂ghostFieldLaw h w) ^ 2 := by
  let F := fun z : Set V × Set V => law p
    (DisjointOccurrence (finiteGhostConnection G x id z.1) (finiteGhostConnection G x id z.2))
  have hF : Measurable F := measurable_measure_prodMk_left (ν := law p)
    (measurableSet_ghostDisjointOccurrence G x id)
  have hmono : ∀ m m', m ⊆ m' → ∀ n n', n ⊆ n' → F (m,n) ≤ F (m',n') := by
    intro m m' hmm n n' hnn
    exact measure_mono (disjointOccurrence_mono
      (finiteGhostConnection_mono_marks G x hmm) (finiteGhostConnection_mono_marks G x hnn))
  exact (two_ghost_avoidance_upper h w S F hF hmono).trans
    (mul_le_mul' le_rfl (averaged_ghostConnection_bk G x id p (ghostFieldLaw h w)))

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalGeometry
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma openSimpleGraph_delete_singleton (hG : Function.Injective G) (ω : Set E) (e : E) :
    openSimpleGraph G (ω \ {e}) = (openSimpleGraph G ω).deleteEdges {G e} := by
  ext u v
  rw [SimpleGraph.deleteEdges_adj]
  change (u ≠ v ∧ ∃ f ∈ ω \ {e}, G f = s(u,v)) ↔
    (u ≠ v ∧ ∃ f ∈ ω, G f = s(u,v)) ∧ s(u,v) ∉ ({G e} : Set (Sym2 V))
  constructor
  · rintro ⟨hne,f,⟨hfw,hfe⟩,hf⟩
    exact ⟨⟨hne,f,hfw,hf⟩,fun heq => hfe (hG (hf.trans heq))⟩
  · rintro ⟨⟨hne,f,hfw,hf⟩,hfe⟩
    refine ⟨hne,f,⟨hfw,?_⟩,hf⟩
    intro he
    exact hfe (by simpa only [Set.mem_singleton_iff] using (hf.symm.trans (congrArg G he)))

lemma two_ghost_connections_or_pivotal (hG : Function.Injective G) (ω : Set E)
    (m n : Set V) (x : V)
    (hm : ω ∈ finiteGhostConnection G x id m) (hn : ω ∈ finiteGhostConnection G x id n) :
    ω ∈ DisjointOccurrence (finiteGhostConnection G x id m) (finiteGhostConnection G x id n) ∨
      ∃ e u v, GhostBridgePivotal G ω m n x e u v := by
  obtain ⟨a,ha,hxa⟩ := hm
  obtain ⟨b,hb,hxb⟩ := hn
  have hm' : ∃ a ∈ m, (openSimpleGraph G ω).Reachable x a :=
    ⟨a,ha,(conn_iff_reachable G ω x a).mp hxa⟩
  have hn' : ∃ b ∈ n, (openSimpleGraph G ω).Reachable x b :=
    ⟨b,hb,(conn_iff_reachable G ω x b).mp hxb⟩
  rcases two_connections_fan_or_bridge hm' hn' with hfan | ⟨u,v,huv,he,hxu,hA,hB,hfan⟩
  · exact Or.inl (ghostFan_mem_disjointOccurrence G x id (by simpa using hfan))
  right
  obtain ⟨_,e,heω,hGe⟩ := huv
  have hdel : (openSimpleGraph G ω).deleteEdges {s(u,v)} = openSimpleGraph G (ω \ {e}) := by
    rw [← hGe]
    exact (openSimpleGraph_delete_singleton G hG ω e).symm
  have hnot : ¬(openSimpleGraph G (ω \ {e})).Reachable x v := by
    intro hxv
    exact (SimpleGraph.isBridge_iff.mp he) (hxu.symm.trans (hdel.symm ▸ hxv))
  rw [hdel] at hxu hA hB hfan
  refine ⟨e,u,v,heω,hGe,(conn_iff_reachable G _ x u).mpr hxu,
    fun h => hnot ((conn_iff_reachable G _ x v).mp h),?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro y hy hym
    exact hA y hym ((conn_iff_reachable G _ x y).mp hy)
  · apply Set.disjoint_left.mpr
    intro y hy hyn
    exact hB y hyn ((conn_iff_reachable G _ x y).mp hy)
  · exact ghostFan_mem_disjointOccurrence G v id (by simpa using hfan)

lemma measurableSet_ghostBridgePivotal [Countable V] [Countable E]
    (x : V) (e : E) (u v : V) :
    MeasurableSet {z : (Set V × Set V) × Set E |
      GhostBridgePivotal G z.2 z.1.1 z.1.2 x e u v} := by
  have hdel : Measurable (fun ω : Set E => ω \ {e}) :=
    measurable_set_iff.mpr fun f => (measurable_set_mem f).and measurable_const
  have hc (y : V) : Measurable (fun z : (Set V × Set V) × Set E =>
      Conn G (z.2 \ {e}) x y) :=
    (measurableSet_conn G x y).mem.comp (hdel.comp measurable_snd)
  have hm : Measurable (fun z : (Set V × Set V) × Set E =>
      Disjoint (cluster G (z.2 \ {e}) x) z.1.1) := by
    have h := Measurable.forall fun y => (hc y).imp
      (((measurable_set_mem y).comp (measurable_fst.comp measurable_fst)).not)
    simpa only [Set.disjoint_left,cluster,Set.mem_ofPred_eq, Function.comp_def] using h
  have hn : Measurable (fun z : (Set V × Set V) × Set E =>
      Disjoint (cluster G (z.2 \ {e}) x) z.1.2) := by
    have h := Measurable.forall fun y => (hc y).imp
      (((measurable_set_mem y).comp (measurable_snd.comp measurable_fst)).not)
    simpa only [Set.disjoint_left,cluster,Set.mem_ofPred_eq, Function.comp_def] using h
  have hdo := (measurableSet_ghostDisjointOccurrence G v id).preimage
    (measurable_fst.prodMk (hdel.comp measurable_snd))
  exact (((measurable_set_mem e).comp measurable_snd).and
    (measurable_const.and ((hc u).and ((hc v).not.and (hm.and (hn.and hdo.mem)))))).setOf

lemma conn_exterior_witness {ω s : Set E} (x v y : V) (hs : s ⊆ ω)
    (hv : ¬Conn G ω x v) (hvy : Conn G s v y) :
    Conn G (s ∩ internalEdges G (cluster G ω x)ᶜ) v y := by
  have hout (a : V) (ha : Conn G s v a) : a ∉ cluster G ω x := by
    intro hxa
    exact hv (hxa.trans (conn_symm G ω (conn_mono G hs ha)))
  induction hvy with
  | refl => exact conn_refl G _ v
  | @tail a b hva hab ih =>
    obtain ⟨e,he,hGe⟩ := hab
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G _ e a b hGe).mpr
      ⟨hout a hva,hout b (hva.tail ⟨e,he,hGe⟩)⟩⟩,hGe⟩

lemma ghostDisjointOccurrence_exterior {ω : Set E} (x v : V) (m n : Set V)
    (hv : ¬Conn G ω x v)
    (h : ω ∈ DisjointOccurrence (finiteGhostConnection G v id m)
      (finiteGhostConnection G v id n)) :
    (ω ∩ internalEdges G (cluster G ω x)ᶜ) ∈
      DisjointOccurrence (finiteGhostConnection G v id m) (finiteGhostConnection G v id n) := by
  let I := internalEdges G (cluster G ω x)ᶜ
  obtain ⟨s,t,hs,ht,hst,⟨a,ha,hva⟩,⟨b,hb,hvb⟩⟩ := h
  let s' := s.filter (fun e => e ∈ I)
  let t' := t.filter (fun e => e ∈ I)
  have hs' : (s' : Set E) = (s : Set E) ∩ I := by ext e; simp [s']
  have ht' : (t' : Set E) = (t : Set E) ∩ I := by ext e; simp [t']
  refine ⟨s',t',?_,?_,?_,?_,?_⟩
  · rw [hs']
    exact Set.inter_subset_inter_left _ hs
  · rw [ht']
    exact Set.inter_subset_inter_left _ ht
  · exact hst.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  · refine ⟨a,ha,?_⟩
    rw [hs']
    exact conn_exterior_witness G x v a hs hv hva
  · refine ⟨b,hb,?_⟩
    rw [ht']
    exact conn_exterior_witness G x v b ht hv hvb

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PhaseInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}

theorem criticalModel_openGraph (G : BondGraph V E) (ω : Set E) :
    (criticalModel G).openGraph ω = openSimpleGraph G ω := by
  ext x y
  simp only [CriticalPercolation.BondGraph.openGraph, SimpleGraph.fromEdgeSet_adj,
    Set.mem_image, openSimpleGraph, criticalModel]
  tauto

theorem criticalModel_cluster (G : BondGraph V E) (ω : Set E) (x : V) :
    (criticalModel G).cluster ω x = cluster G ω x := by
  ext y
  simp only [CriticalPercolation.BondGraph.cluster, criticalModel_openGraph,
    Set.mem_ofPred_eq, cluster]
  exact (conn_iff_reachable G ω x y).symm

end Percolation.BenjaminiSchramm

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_PivotalExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exactCluster_boundary_closed {ω : Set E} {x u v : V} {S : Set V} {e : E}
    (hends : G.ends e = s(u,v)) (hu : u ∈ S) (hv : v ∉ S)
    (hS : G.cluster ω x = S) : e ∉ ω := by
  intro he
  have huv : u ≠ v := fun huv => hv (huv ▸ hu)
  have hadj : (G.openGraph ω).Adj u v :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,hends⟩,huv⟩
  have hxu : (G.openGraph ω).Reachable x u := by
    change u ∈ G.cluster ω x
    rwa [hS]
  exact hv (hS ▸ (hxu.trans hadj.reachable))

theorem closed_cluster_pivotal_factor [Countable V] [Countable E]
    (p : unitInterval) (hp : (p : ℝ) < 1) (x : V) (S : Set V) (e : E)
    (u v : V) (hends : G.ends e = s(u,v)) (hu : u ∈ S) (hv : v ∉ S)
    (F : Set E → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, if e ∈ ω then
      ({η | G.cluster η x = S} : Set (Set E)).indicator
        (fun η => F (G.eraseVertices η S)) (BernoulliProduct.forceOn {e} ∅ ω)
      else 0 ∂G.law p) =
        (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
          G.law p {ω | G.cluster ω x = S} *
            ∫⁻ η, F (G.eraseVertices η S) ∂G.law p := by
  let f : Set E → ℝ≥0∞ := ({η | G.cluster η x = S} : Set (Set E)).indicator
    (fun η => F (G.eraseVertices η S))
  have hf : Measurable f := (hF.comp (G.measurable_eraseVertices S)).indicator
    (G.measurableSet_exactCluster x S)
  have heq : (fun ω => if e ∉ ω then f ω else 0) = f := by
    funext ω
    by_cases hS : G.cluster ω x = S
    · rw [ite_eq_left (G.exactCluster_boundary_closed hends hu hv hS)]
    · simp only [f, Set.indicator, Set.mem_ofPred_eq, ite_eq_right hS, ite_self]
  have hclose := BernoulliProduct.lintegral_edge_closing (fun _ : E => p) e hp f hf
  rw [heq] at hclose
  have hlaw : BernoulliProduct.law (fun _ : E => p) = G.law p :=
    BernoulliProduct.law_const p
  rw [hlaw] at hclose
  change (∫⁻ ω, if e ∈ ω then f (BernoulliProduct.forceOn {e} ∅ ω) else 0 ∂G.law p) = _
  rw [hclose]
  change _ * (∫⁻ ω, ({ω | G.cluster ω x = S} : Set (Set E)).indicator
    (fun ω => F (G.eraseVertices ω S)) ω ∂G.law p) = _
  rw [G.exactCluster_exterior_factor p x S F hF, mul_assoc]

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma criticalModel_eraseVertices (ω : Set E) (S : Set V) :
    (criticalModel G).eraseVertices ω S = ω ∩ internalEdges G Sᶜ := by
  ext e
  simp only [CriticalPercolation.BondGraph.eraseVertices,
    CriticalPercolation.BondGraph.incidentEdges, criticalModel, Set.mem_sdiff,
    Set.mem_inter_iff, internalEdges, Set.mem_ofPred_eq, Set.mem_compl_iff,
    not_exists, not_and]
  constructor
  · rintro ⟨he,h⟩
    exact ⟨he,fun y hy hS => h y hS hy⟩
  · rintro ⟨he,h⟩
    exact ⟨he,fun y hS hy => h y hy hS⟩

omit [Countable V] [Countable E] in
lemma force_closed_eq_sdiff (ω : Set E) (e : E) :
    CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω = ω \ {e} := by
  ext f
  by_cases hf : f = e <;> simp [hf]

lemma measurableSet_ghostBridge_fixed_cluster (S : Set V) (x : V) (e : E) (u v : V)
    (m n : Set V) :
    MeasurableSet {ω | GhostBridgePivotal G ω m n x e u v ∧
      cluster G (ω \ {e}) x = S} := by
  have hdel : Measurable (fun ω : Set E => ω \ {e}) :=
    measurable_set_iff.mpr fun f => (measurable_set_mem f).and measurable_const
  have hp := (measurableSet_ghostBridgePivotal G x e u v).preimage
    (show Measurable (fun ω : Set E => ((m,n),ω)) from
      measurable_const.prodMk measurable_id)
  have hc := ((criticalModel G).measurableSet_exactCluster x S).preimage hdel
  simpa only [Set.preimage_ofPred_eq, Set.mem_ofPred_eq, criticalModel_cluster] using (hp.mem.and hc.mem).setOf

theorem ghostBridge_fixed_cluster_measure_le (p : unitInterval) (hp : (p : ℝ) < 1)
    (S : Set V) (x : V) (e : E) (u v : V) (hends : G e = s(u,v))
    (hu : u ∈ S) (hv : v ∉ S) (m n : Set V) :
    law p {ω | GhostBridgePivotal G ω m n x e u v ∧ cluster G (ω \ {e}) x = S} ≤
      (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
        law p {ω | cluster G ω x = S} *
          (if Disjoint S m ∧ Disjoint S n then
            law p (DisjointOccurrence (finiteGhostConnection G v id m)
              (finiteGhostConnection G v id n)) else 0) := by
  let D := DisjointOccurrence (finiteGhostConnection G v id m) (finiteGhostConnection G v id n)
  have hD : MeasurableSet D := (measurableSet_ghostDisjointOccurrence G v id).preimage
    (show Measurable (fun ω : Set E => ((m,n),ω)) from
      measurable_const.prodMk measurable_id)
  let F := D.indicator (fun _ : Set E => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hD
  by_cases havoid : Disjoint S m ∧ Disjoint S n
  · rw [ite_eq_left havoid]
    have hpoint (ω : Set E) :
        ({ω | GhostBridgePivotal G ω m n x e u v ∧ cluster G (ω \ {e}) x = S} : Set (Set E)).indicator
          (fun _ => (1 : ℝ≥0∞)) ω ≤
        if e ∈ ω then ({η | (criticalModel G).cluster η x = S} : Set (Set E)).indicator
          (fun η => F ((criticalModel G).eraseVertices η S))
          (CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω) else 0 := by
      by_cases hω : GhostBridgePivotal G ω m n x e u v ∧ cluster G (ω \ {e}) x = S
      · have horig := hω
        obtain ⟨⟨he,_,_,hnot,_,_,hdo⟩,hcl⟩ := hω
        have hd := ghostDisjointOccurrence_exterior G x v m n hnot hdo
        rw [hcl] at hd
        have hcl' : (criticalModel G).cluster
            (CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω) x = S := by
          rw [force_closed_eq_sdiff, criticalModel_cluster, hcl]
        have hd' : (criticalModel G).eraseVertices
            (CriticalPercolation.BernoulliProduct.forceOn {e} ∅ ω) S ∈ D := by
          rw [force_closed_eq_sdiff, criticalModel_eraseVertices G]
          exact hd
        simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_left horig, ite_eq_left he,
          ite_eq_left hcl', F, ite_eq_left hd', le_refl]
      · simp only [Set.indicator, Set.mem_ofPred_eq, ite_eq_right hω]
        exact bot_le
    calc
      _ = ∫⁻ ω, ({ω | GhostBridgePivotal G ω m n x e u v ∧
          cluster G (ω \ {e}) x = S} : Set (Set E)).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂law p := by
        exact (lintegral_indicator_one (measurableSet_ghostBridge_fixed_cluster G S x e u v m n)).symm
      _ ≤ _ := lintegral_mono hpoint
      _ = _ := (criticalModel G).closed_cluster_pivotal_factor p hp x S e u v hends hu hv F hF
      _ ≤ _ := by
        simp only [criticalModel_cluster]
        apply mul_le_mul' le_rfl
        calc
          _ ≤ ∫⁻ η, F η ∂(criticalModel G).law p := by
            apply lintegral_mono
            intro η
            by_cases he : (criticalModel G).eraseVertices η S ∈ D
            · have he' : η ∈ D := (disjointOccurrence_upper _ _)
                (fun _ h => h.1) he
              simp only [F, Set.indicator, ite_eq_left he, ite_eq_left he', le_refl]
            · simp only [F, Set.indicator, ite_eq_right he]
              exact bot_le
          _ = _ := lintegral_indicator_one hD
  · have he : {ω | GhostBridgePivotal G ω m n x e u v ∧
        cluster G (ω \ {e}) x = S} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨h,hcl⟩
      exact havoid (by simpa only [← hcl] using ⟨h.2.2.2.2.1,h.2.2.2.2.2.1⟩)
    simp only [he,measure_empty,ite_eq_right havoid,mul_zero,le_refl]

theorem averaged_ghostBridge_fixed_cluster_le (p : unitInterval) (hp : (p : ℝ) < 1)
    (S : Finset V) (x : V) (e : E) (u v : V) (hends : G e = s(u,v))
    (hu : u ∈ S) (hv : v ∉ S) (h : ℝ≥0) (w : V → ℝ≥0) :
    (∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
      cluster G (ω \ {e}) x = (S : Set V)} ∂ghostFieldLaw h w ∂ghostFieldLaw h w) ≤
      (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        (ENNReal.ofReal (Real.exp (-(h : ℝ) * ∑ y ∈ S, (w y : ℝ)))) ^ 2 *
        (∫⁻ m, law p (finiteGhostConnection G v id m) ∂ghostFieldLaw h w) ^ 2 := by
  let C := (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
    law p {ω | cluster G ω x = (S : Set V)}
  have hC : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · rw [div_eq_mul_inv]
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp)).ne'
    · exact measure_ne_top _ _
  calc
    _ ≤ ∫⁻ m, ∫⁻ n, C * (if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n then
        law p (DisjointOccurrence (finiteGhostConnection G v id m)
          (finiteGhostConnection G v id n)) else 0) ∂ghostFieldLaw h w ∂ghostFieldLaw h w := by
      apply lintegral_mono
      intro m
      apply lintegral_mono
      intro n
      exact ghostBridge_fixed_cluster_measure_le G p hp S x e u v hends hu hv m n
    _ = C * (∫⁻ m, ∫⁻ n, if Disjoint (S : Set V) m ∧ Disjoint (S : Set V) n then
        law p (DisjointOccurrence (finiteGhostConnection G v id m)
          (finiteGhostConnection G v id n)) else 0 ∂ghostFieldLaw h w ∂ghostFieldLaw h w) := by
      simp_rw [lintegral_const_mul' C _ hC]
    _ ≤ _ := by
      simpa only [C, mul_assoc] using mul_le_mul' (le_refl C)
        (ghost_avoidance_bk G p v h w S)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalWeight
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma criticalModel_finiteGhostConnection (x : V) (m : Set V) :
    finiteGhostConnection G x id m =
      {ω | ∃ y ∈ m, ((criticalModel G).openGraph ω).Reachable x y} := by
  ext ω
  simp only [finiteGhostConnection, Set.mem_ofPred_eq, criticalModel_openGraph]
  exact exists_congr fun y => and_congr_right fun _ => conn_iff_reachable G ω x y

omit [Countable V] [Countable E] in
lemma ghostAvoid_finite_sum (h : ℝ) (w : V → ℝ≥0) (S : Finset V) :
    ghostAvoid h (∑ y ∈ S, (w y : ℝ≥0∞)) =
      ENNReal.ofReal (Real.exp (-h * ∑ y ∈ S, (w y : ℝ))) := by
  have hfin : (∑ y ∈ S, (w y : ℝ≥0∞)) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.coe_lt_top).ne
  rw [ghostAvoid,ite_eq_right hfin,ENNReal.toReal_sum (fun _ _ => ENNReal.coe_ne_top)]
  simp only [ENNReal.coe_toReal]

omit [Countable V] [Countable E] in
lemma exp_avoidance_sq (h : ℝ) (w : V → ℝ≥0) (S : Finset V) :
    ENNReal.ofReal (Real.exp (-h * ∑ y ∈ S, (w y : ℝ))) ^ 2 =
      ghostAvoid (2*h) (∑ y ∈ S, (w y : ℝ≥0∞)) := by
  rw [ghostAvoid_finite_sum, pow_two, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add]
  congr 2
  ring

theorem averaged_ghostBridge_quarter_weight_le
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K * h ^ (3/4 : ℝ))
    (S : Finset V) (x : V) (e : E) (u v : V) (hends : G e = s(u,v))
    (hu : u ∈ S) (hv : v ∉ S) (h : ℝ≥0) :
    (∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
      cluster G (ω \ {e}) x = (S : Set V)}
      ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)
      ∂ghostFieldLaw h ((criticalModel G).quarterGhostWeight x)) ≤
      (ENNReal.ofReal (p : ℝ) / ENNReal.ofReal (1 - (p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
        (ENNReal.ofReal (K^2 * (h : ℝ)^(3/2 : ℝ)) *
          (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ)) := by
  let H := criticalModel G
  have hf : ∀ᵐ ω ∂H.law p, (H.cluster ω v).Finite := by
    rw [show H.law p = (law p : Measure (Set E)) from rfl]
    simpa only [H,criticalModel_cluster] using hfin v
  have haverage : (∫⁻ m, law p (finiteGhostConnection G v id m)
      ∂ghostFieldLaw h (H.quarterGhostWeight x)) =
        ENNReal.ofReal (H.quarterGhostMagnetization p v (h * H.quarterGhostWeight x v)) := by
    simp_rw [criticalModel_finiteGhostConnection G]
    exact H.quarterGhostConnection_change_base hc hl p x v h hf
  have hsquare : ENNReal.ofReal (H.quarterGhostMagnetization p v
        (h * H.quarterGhostWeight x v)) ^ 2 ≤
      ENNReal.ofReal (K^2 * (h : ℝ)^(3/2 : ℝ)) * H.stabilizerWeight x v ^ (3/8 : ℝ) := by
    have hnonneg : 0 ≤ H.quarterGhostMagnetization p v (h * H.quarterGhostWeight x v) :=
      integral_nonneg fun _ => ghostKernel_nonneg (by positivity) ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_pow hnonneg]
    have hb := ENNReal.ofReal_le_ofReal (H.rebased_quarterGhost_square_bound hbound x v h.2)
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg K) (Real.rpow_nonneg h.2 _)),
      ENNReal.ofReal_toReal
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (H.stabilizerWeight_ne_top x v))] at hb
    exact hb
  have hb := averaged_ghostBridge_fixed_cluster_le G p hp S x e u v hends hu hv h
    (H.quarterGhostWeight x)
  rw [exp_avoidance_sq, haverage] at hb
  exact hb.trans (mul_le_mul' le_rfl hsquare)

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma incidence_stabilizerOrbit_subset_ball (v w : V) (n : ℕ) (hw : w∈G.vertexBall v n) :
    G.stabilizerOrbit v w ⊆ G.vertexBall v n := by
  intro z hz
  obtain ⟨φ,hv,hwz⟩ := G.mem_stabilizerOrbit.mp hz
  have h := (Aut.vertexBall_mem G φ v w n).mpr hw
  simpa only [hv,hwz] using h

lemma stabilizerWeight_le_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) {v w : V}
    (_hw : w∈G.vertexBall v 1) (hv : v∈G.vertexBall w 1) :
    G.stabilizerWeight v w ≤ K := by
  unfold stabilizerWeight modularRatio
  apply ENNReal.ofReal_le_of_le_toReal
  simp only [ENNReal.toReal_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl v w))).mpr
  have hnum : G.suborbitCard w v ≤ K :=
    (Set.ncard_le_ncard (G.incidence_stabilizerOrbit_subset_ball w v 1 hv)
      (G.vertexBall_finite hl w 1)).trans (hK w)
  have hden : (1:ℝ)≤G.suborbitCard v w := by exact_mod_cast G.suborbitCard_pos hc hl v w
  exact (Nat.cast_le.mpr hnum).trans (by nlinarith [show (0:ℝ)≤K by positivity])

lemma common_bond_ball_one {v w : V} {e : E} (hv : v∈G.ends e) (hw : w∈G.ends e) :
    w∈G.vertexBall v 1 := by
  by_cases he : v=w
  · subst w
    exact G.mem_vertexBall_self v 1
  · apply G.vertexBall_step (G.mem_vertexBall_self v 0)
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_,he⟩
    refine ⟨e,Set.mem_univ e,?_⟩
    exact (Sym2.mem_and_mem_iff he).mp ⟨hv,hw⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_WeightedGhostIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ghostBondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o v : V) (e : E) : G.ghostBondWeight o e =
      G.stabilizerWeight o v ^ (3 / 8 : ℝ) * G.ghostBondWeight v e := by
  unfold ghostBondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [G.stabilizerWeight_change_base hc hl o v y,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]

lemma ghostBondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (o v : V) (e : E)
    (hv : v ∈ G.ends e) :
    G.ghostBondWeight o e ≤ (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ)) *
      G.stabilizerWeight o v ^ (3 / 8 : ℝ) := by
  rw [G.ghostBondWeight_change_base hc hl o v e]
  have hsum : G.ghostBondWeight v e ≤ 2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ) := by
    calc
      _ ≤ ∑ y ∈ (G.ends e).toFinset, (K : ℝ≥0∞) ^ (3 / 8 : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        have hy' := Sym2.mem_toFinset.mp hy
        exact ENNReal.rpow_le_rpow
          (G.stabilizerWeight_le_ball_bound hc hl K hK
            (G.common_bond_ball_one hv hy') (G.common_bond_ball_one hy' hv)) (by norm_num)
      _ = (G.ends e).toFinset.card * (K : ℝ≥0∞) ^ (3 / 8 : ℝ) := by
        simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        exact_mod_cast (show (G.ends e).toFinset.card ≤ 2 by
          rw [Sym2.card_toFinset]; split_ifs <;> omega)
  exact (mul_le_mul' le_rfl hsum).trans_eq (mul_comm _ _)

lemma weighted_ghost_incidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) (o : V) (S : Set V) :
    (∑' e, if e ∈ G.incidentEdges S then G.ghostBondWeight o e else 0) ≤
      ((D : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ))) * G.threeEighthMass o S := by
  let B := (2 : ℝ≥0∞) * (K : ℝ≥0∞) ^ (3 / 8 : ℝ)
  calc
    _ ≤ ∑' e : E, ∑' v : V, if v ∈ S ∧ v ∈ G.ends e then G.ghostBondWeight o e else 0 := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e ∈ G.incidentEdges S
      · rw [ite_eq_left he]
        obtain ⟨v,hv,hve⟩ := he
        simpa only [ite_eq_left (show v ∈ S ∧ v ∈ G.ends e from ⟨hv,hve⟩)] using
          ENNReal.le_tsum v (f := fun v => if v ∈ S ∧ v ∈ G.ends e then G.ghostBondWeight o e else 0)
      · rw [ite_eq_right he]
        exact bot_le
    _ = ∑' v : V, ∑' e : E, if v ∈ S ∧ v ∈ G.ends e then G.ghostBondWeight o e else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' v : V, if v ∈ S then (D : ℝ≥0∞) * B * G.stabilizerWeight o v ^ (3 / 8 : ℝ) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v ∈ S
      · simp only [hv,true_and,if_true]
        have hf : (G.incidentEdges {v}).Finite := by simpa [incidentEdges] using hl v
        have hm (e : E) : e ∈ G.incidentEdges {v} ↔ v ∈ G.ends e := by simp [incidentEdges]
        rw [tsum_eq_sum (s := hf.toFinset) (fun e he => by
          simp only [hf.mem_toFinset,hm] at he
          exact ite_eq_right he)]
        calc
          _ ≤ ∑ e ∈ hf.toFinset, B * G.stabilizerWeight o v ^ (3 / 8 : ℝ) := by
            apply Finset.sum_le_sum
            intro e he
            rw [ite_eq_left ((hm e).mp (hf.mem_toFinset.mp he))]
            exact G.ghostBondWeight_le_at_end hc hl K hK o v e
              ((hm e).mp (hf.mem_toFinset.mp he))
          _ = ((G.incidentEdges {v}).ncard : ℝ≥0∞) *
              (B * G.stabilizerWeight o v ^ (3 / 8 : ℝ)) := by
            simp only [Finset.sum_const,nsmul_eq_mul,← Set.ncard_eq_toFinset_card _ hf]
          _ ≤ (D : ℝ≥0∞) * (B * G.stabilizerWeight o v ^ (3 / 8 : ℝ)) := by
            apply mul_le_mul' _ le_rfl
            exact_mod_cast hD v
          _ = _ := (mul_assoc _ _ _).symm
      · simp only [hv,false_and,if_false,tsum_zero,le_refl]
    _ = _ := by
      unfold threeEighthMass
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp [B]

lemma ghostWeightedCount_eq (h : ℝ) (ω : Set E) (x : V) :
    G.ghostWeightedCount h ω x =
      Percolation.BenjaminiSchramm.ghostAvoid h (G.quarterTiltedMass ω x) *
        G.threeEighthMass x (G.cluster ω x) := by
  unfold ghostWeightedCount threeEighthMass
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro v
  split_ifs <;> simp_all [cluster]

theorem expected_ghost_boundary_weight_le [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) {h : ℝ} (hh : 0 ≤ h)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hK : ∀ v, (G.vertexBall v 1).ncard ≤ K) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots, ∫⁻ ω,
      Percolation.BenjaminiSchramm.ghostAvoid h (G.quarterTiltedMass ω x) *
        (∑' e, if e ∈ G.incidentEdges (G.cluster ω x) then G.ghostBondWeight x e else 0)
      ∂G.law p) ≤
      ((D : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ))) *
        (2 * ∑ x ∈ (G.orbitRepresentatives hq).roots, ∫⁻ ω,
          Percolation.BenjaminiSchramm.ghostAvoid h (G.quarterTiltedMass ω x) *
            G.quarterTiltedMass ω x ∂G.law p) := by
  let B := (D : ℝ≥0∞) * (2 * (K : ℝ≥0∞) ^ (3 / 8 : ℝ))
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top (by norm_num)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.coe_ne_top))
  calc
    _ ≤ ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, B * G.ghostWeightedCount h ω x ∂G.law p := by
      apply Finset.sum_le_sum
      intro x _
      apply lintegral_mono
      intro ω
      dsimp only
      rw [G.ghostWeightedCount_eq]
      exact (mul_le_mul' le_rfl
        (G.weighted_ghost_incidence_le hc hl D K hD hK x (G.cluster ω x))).trans_eq
          (by dsimp [B]; ac_rfl)
    _ = B * ∑ x ∈ (G.orbitRepresentatives hq).roots,
        ∫⁻ ω, G.ghostWeightedCount h ω x ∂G.law p := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      exact lintegral_const_mul' _ _ hB
    _ ≤ _ := mul_le_mul' le_rfl (G.expected_ghostWeightedCount_le hc hl hq p hh)

end CriticalPercolation.BondGraph

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalIncidence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

lemma oriented_pivotal_weight_le (S : Set V) (e : E) (w : V → ℝ≥0∞) :
    (∑' u : V, ∑' v : V,
      if G e = s(u,v) ∧ u ∈ S ∧ v ∉ S then w v else 0) ≤
      if e ∈ (criticalModel G).incidentEdges S then 2 * ∑ v ∈ (G e).toFinset, w v else 0 := by
  let B := (G e).toFinset
  by_cases he : e ∈ (criticalModel G).incidentEdges S
  · rw [ite_eq_left he]
    rw [tsum_eq_sum (s := B) (fun u hu => by
      apply ENNReal.tsum_eq_zero.mpr
      intro v
      apply ite_eq_right
      intro h
      exact hu (Sym2.mem_toFinset.mpr (by rw [h.1]; simp)))]
    have hrow (u : V) :
        (∑' v : V, if G e = s(u,v) ∧ u ∈ S ∧ v ∉ S then w v else 0) ≤ ∑ v ∈ B, w v := by
      rw [tsum_eq_sum (s := B) (fun v hv => by
        apply ite_eq_right
        intro h
        exact hv (Sym2.mem_toFinset.mpr (by rw [h.1]; simp)))]
      apply Finset.sum_le_sum
      intro v _
      split_ifs <;> simp
    calc
      _ ≤ ∑ _u ∈ B, ∑ v ∈ B, w v := Finset.sum_le_sum fun u _ => hrow u
      _ = (B.card : ℝ≥0∞) * ∑ v ∈ B, w v := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := by
        apply mul_le_mul' _ le_rfl
        exact_mod_cast (show B.card ≤ 2 by
          dsimp [B]
          rw [Sym2.card_toFinset]
          split_ifs <;> omega)
  · rw [ite_eq_right he]
    apply le_of_eq
    apply ENNReal.tsum_eq_zero.mpr
    intro u
    apply ENNReal.tsum_eq_zero.mpr
    intro v
    apply ite_eq_right
    intro h
    exact he ⟨u,h.2.1,by change u ∈ G e; rw [h.1]; simp⟩

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalUnion
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem twoGhostConnection_le_fan_add_pivotal_sum (hG : Function.Injective G)
    (p : unitInterval) (x : V) (m n : Set V)
    (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    law p (finiteGhostConnection G x id m ∩ finiteGhostConnection G x id n) ≤
      law p (DisjointOccurrence (finiteGhostConnection G x id m)
        (finiteGhostConnection G x id n)) +
      ∑' e : E, ∑' u : V, ∑' v : V, ∑' S : Finset V,
        law p {ω | GhostBridgePivotal G ω m n x e u v ∧
          cluster G (ω \ {e}) x = (S : Set V)} := by
  let D := DisjointOccurrence (finiteGhostConnection G x id m) (finiteGhostConnection G x id n)
  let A := fun e u v (S : Finset V) => {ω | GhostBridgePivotal G ω m n x e u v ∧
    cluster G (ω \ {e}) x = (S : Set V)}
  have hsub : ((finiteGhostConnection G x id m ∩ finiteGhostConnection G x id n : Set (Set E)))
      ≤ᵐ[law p] (D ∪ ⋃ e, ⋃ u, ⋃ v, ⋃ S, A e u v S : Set (Set E)) := by
    filter_upwards [hfin] with ω hω hm
    rcases two_ghost_connections_or_pivotal G hG ω m n x hm.1 hm.2 with hd | ⟨e,u,v,hp⟩
    · exact Or.inl hd
    · have hf : (cluster G (ω \ {e}) x).Finite :=
        hω.subset (fun _ h => conn_mono G Set.sdiff_subset h)
      apply Or.inr
      exact Set.mem_iUnion.mpr ⟨e,Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨v,
        Set.mem_iUnion.mpr ⟨hf.toFinset,hp,hf.coe_toFinset.symm⟩⟩⟩⟩
  calc
    _ ≤ law p (D ∪ ⋃ e, ⋃ u, ⋃ v, ⋃ S, A e u v S) := measure_mono_ae hsub
    _ ≤ law p D + law p (⋃ e, ⋃ u, ⋃ v, ⋃ S, A e u v S) := measure_union_le _ _
    _ ≤ law p D + ∑' e, law p (⋃ u, ⋃ v, ⋃ S, A e u v S) :=
      add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ law p D + ∑' e, ∑' u, law p (⋃ v, ⋃ S, A e u v S) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum fun e : E => measure_iUnion_le _)
    _ ≤ law p D + ∑' e, ∑' u, ∑' v, law p (⋃ S, A e u v S) :=
      add_le_add le_rfl (ENNReal.tsum_le_tsum fun e : E =>
        ENNReal.tsum_le_tsum fun u : V => measure_iUnion_le _)
    _ ≤ _ := add_le_add le_rfl (ENNReal.tsum_le_tsum fun e : E =>
      ENNReal.tsum_le_tsum fun u : V => ENNReal.tsum_le_tsum fun v : V =>
        measure_iUnion_le (fun S : Finset V => A e u v S))

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

theorem lintegral_twice_tsum {A I : Type*} [MeasurableSpace A] [Countable I]
    (ν : Measure A) [SFinite ν] (F : I → A × A → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) :
    (∫⁻ m, ∫⁻ n, ∑' i, F i (m,n) ∂ν ∂ν) =
      ∑' i, ∫⁻ m, ∫⁻ n, F i (m,n) ∂ν ∂ν := by
  calc
    _ = ∫⁻ z, ∑' i, F i z ∂ν.prod ν :=
      (lintegral_prod _ (Measurable.tsum hF).aemeasurable).symm
    _ = ∑' i, ∫⁻ z, F i z ∂ν.prod ν := lintegral_tsum (fun i => (hF i).aemeasurable)
    _ = _ := tsum_congr fun i => lintegral_prod _ (hF i).aemeasurable

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_ghostBridge_cluster_fields (p : unitInterval) (x : V)
    (e : E) (u v : V) (S : Finset V) :
    Measurable (fun z : Set V × Set V => law p {ω |
      GhostBridgePivotal G ω z.1 z.2 x e u v ∧ cluster G (ω \ {e}) x = (S : Set V)}) := by
  have hdel : Measurable (fun ω : Set E => ω \ {e}) :=
    measurable_set_iff.mpr fun f => (measurable_set_mem f).and measurable_const
  have hm := (measurableSet_ghostBridgePivotal G x e u v).inter
    ((((criticalModel G).measurableSet_exactCluster x (S : Set V)).preimage hdel).preimage measurable_snd)
  convert measurable_measure_prodMk_left (ν := law p) hm using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  congr 1
  ext ω
  simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,criticalModel_cluster]

theorem averaged_twoGhost_le_fan_add_pivotal_sum (hG : Function.Injective G)
    (p : unitInterval) (x : V) (hfin : ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (ν : Measure (Set V)) [SFinite ν] :
    (∫⁻ m, ∫⁻ n, law p (finiteGhostConnection G x id m ∩ finiteGhostConnection G x id n) ∂ν ∂ν) ≤
      (∫⁻ m, law p (finiteGhostConnection G x id m) ∂ν)^2 +
      ∑' e : E, ∑' u : V, ∑' v : V, ∑' S : Finset V,
        ∫⁻ m, ∫⁻ n, law p {ω | GhostBridgePivotal G ω m n x e u v ∧
          cluster G (ω \ {e}) x = (S : Set V)} ∂ν ∂ν := by
  let F := fun e u v (S : Finset V) (z : Set V × Set V) => law p {ω |
    GhostBridgePivotal G ω z.1 z.2 x e u v ∧ cluster G (ω \ {e}) x = (S : Set V)}
  let D := fun z : Set V × Set V => law p
    (DisjointOccurrence (finiteGhostConnection G x id z.1) (finiteGhostConnection G x id z.2))
  have hF (e : E) (u v : V) (S : Finset V) : Measurable (F e u v S) :=
    measurable_ghostBridge_cluster_fields G p x e u v S
  have hD : Measurable D := measurable_measure_prodMk_left (ν := law p)
    (measurableSet_ghostDisjointOccurrence G x id)
  have hsum : (∫⁻ m, ∫⁻ n, ∑' e, ∑' u, ∑' v, ∑' S, F e u v S (m,n) ∂ν ∂ν) =
      ∑' e, ∑' u, ∑' v, ∑' S, ∫⁻ m, ∫⁻ n, F e u v S (m,n) ∂ν ∂ν := by
    rw [lintegral_twice_tsum ν _ (fun e => Measurable.tsum fun u => Measurable.tsum fun v => Measurable.tsum (hF e u v))]
    apply tsum_congr
    intro e
    rw [lintegral_twice_tsum ν _ (fun u => Measurable.tsum fun v => Measurable.tsum (hF e u v))]
    apply tsum_congr
    intro u
    rw [lintegral_twice_tsum ν _ (fun v => Measurable.tsum (hF e u v))]
    apply tsum_congr
    intro v
    exact lintegral_twice_tsum ν _ (hF e u v)
  calc
    _ ≤ ∫⁻ m, ∫⁻ n, D (m,n) + ∑' e, ∑' u, ∑' v, ∑' S, F e u v S (m,n) ∂ν ∂ν := by
      apply lintegral_mono
      intro m
      apply lintegral_mono
      intro n
      exact twoGhostConnection_le_fan_add_pivotal_sum G hG p x m n hfin
    _ = (∫⁻ m, ∫⁻ n, D (m,n) ∂ν ∂ν) +
        ∫⁻ m, ∫⁻ n, ∑' e, ∑' u, ∑' v, ∑' S, F e u v S (m,n) ∂ν ∂ν := by
      have hM : Measurable (fun z => ∑' e, ∑' u, ∑' v, ∑' S, F e u v S z) :=
        Measurable.tsum fun e => Measurable.tsum fun u => Measurable.tsum fun v => Measurable.tsum (hF e u v)
      have hDM : Measurable (fun z => D z + ∑' e, ∑' u, ∑' v, ∑' S, F e u v S z) := hD.add hM
      rw [←lintegral_prod _ hDM.aemeasurable,lintegral_add_left hD _,
        lintegral_prod _ hD.aemeasurable,lintegral_prod _ hM.aemeasurable]
    _ ≤ _ := by
      rw [hsum]
      exact add_le_add (averaged_ghostConnection_bk G x id p ν) le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostPivotalBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem averagedQuarterBridge_oriented_le
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (S : Finset V) (x : V) (e : E) (u v : V) (h : ℝ≥0) :
    averagedQuarterBridge G p x h e u v S ≤
      ((ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      (if G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V) then
        (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ) else 0) := by
  by_cases hor : G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V)
  · rw [ite_eq_left hor]
    exact (averaged_ghostBridge_quarter_weight_le G hc hl p hp hfin K hbound S x e u v
      hor.1 hor.2.1 hor.2.2 h).trans_eq (by simp only [mul_assoc])
  · rw [ite_eq_right hor,mul_zero]
    have hempty (m n : Set V) : {ω | GhostBridgePivotal G ω m n x e u v ∧
        cluster G (ω \ {e}) x = (S : Set V)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hpiv,hcl⟩
      apply hor
      refine ⟨hpiv.2.1,?_,?_⟩
      · have hu : u ∈ cluster G (ω \ {e}) x := hpiv.2.2.1
        rw [hcl] at hu
        exact hu
      · intro hv
        have hv' : v ∈ cluster G (ω \ {e}) x := by rw [hcl]; exact hv
        exact hpiv.2.2.2.1 hv'
    simp only [averagedQuarterBridge,hempty,measure_empty,lintegral_zero,le_refl]

theorem averagedQuarterBridge_cluster_sum_le
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (S : Finset V) (x : V) (h : ℝ≥0) :
    (∑' e, ∑' u, ∑' v, averagedQuarterBridge G p x h e u v S) ≤
      ((ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))) *
        law p {ω | cluster G ω x = (S : Set V)} *
        ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      (2 * ∑' e, if e ∈ (criticalModel G).incidentEdges (S : Set V) then
        (criticalModel G).ghostBondWeight x e else 0) := by
  let C := (ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))) *
    law p {ω | cluster G ω x = (S : Set V)} *
    ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, ((criticalModel G).quarterGhostWeight x y : ℝ≥0∞)) *
    ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))
  calc
    _ ≤ ∑' e, ∑' u, ∑' v, C * (if G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V) then
        (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ) else 0) := by
      apply ENNReal.tsum_le_tsum
      intro e
      apply ENNReal.tsum_le_tsum
      intro u
      exact ENNReal.tsum_le_tsum fun v =>
        averagedQuarterBridge_oriented_le G hc hl p hp hfin K hbound S x e u v h
    _ = C * ∑' e, ∑' u, ∑' v, if G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V) then
        (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ) else 0 := by
      simp_rw [ENNReal.tsum_mul_left]
    _ ≤ C * ∑' e, if e ∈ (criticalModel G).incidentEdges (S : Set V) then
        2*(criticalModel G).ghostBondWeight x e else 0 := by
      apply mul_le_mul' le_rfl
      apply ENNReal.tsum_le_tsum
      intro e
      have he := oriented_pivotal_weight_le G (S : Set V) e
        (fun v => (criticalModel G).stabilizerWeight x v ^ (3/8 : ℝ))
      convert he using 1
      · apply tsum_congr
        intro u
        apply tsum_congr
        intro v
        by_cases hor : G e = s(u,v) ∧ u ∈ (S : Set V) ∧ v ∉ (S : Set V)
        · simp only [ite_eq_left hor]
        · simp only [ite_eq_right hor]
      · rfl
    _ = _ := by
      congr 1
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro e
      split_ifs <;> simp

theorem averagedQuarterBridge_sum_le_boundary
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (x : V) (h : ℝ≥0) :
    (∑' e, ∑' u, ∑' v, ∑' S, averagedQuarterBridge G p x h e u v S) ≤
      (2*(ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ)))*
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      ∫⁻ ω, ghostAvoid (2*(h : ℝ)) ((criticalModel G).quarterTiltedMass ω x) *
        (∑' e, if e ∈ (criticalModel G).incidentEdges (cluster G ω x) then
          (criticalModel G).ghostBondWeight x e else 0) ∂law p := by
  let H := criticalModel G
  let R := ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))
  let Q := ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))
  let F := fun S : Set V => ghostAvoid (2*(h : ℝ))
    (∑' y, if y ∈ S then (H.quarterGhostWeight x y : ℝ≥0∞) else 0) *
      (∑' e, if e ∈ H.incidentEdges S then H.ghostBondWeight x e else 0)
  have hF (S : Finset V) : F (S : Set V) =
      ghostAvoid (2*(h : ℝ)) (∑ y ∈ S, (H.quarterGhostWeight x y : ℝ≥0∞)) *
        (∑' e, if e ∈ H.incidentEdges (S : Set V) then H.ghostBondWeight x e else 0) := by
    dsimp only [F]
    apply congrArg (fun m => ghostAvoid (2*(h : ℝ)) m *
      (∑' e, if e ∈ H.incidentEdges (S : Set V) then H.ghostBondWeight x e else 0))
    calc
      _ = ∑' y, if y ∈ S then (H.quarterGhostWeight x y : ℝ≥0∞) else 0 := by
        apply tsum_congr
        intro y
        by_cases hy : y ∈ S
        · simp only [Finset.mem_coe,ite_eq_left hy]
        · simp only [Finset.mem_coe,ite_eq_right hy]
      _ = ∑ y ∈ S, (H.quarterGhostWeight x y : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun y hy => ite_eq_right hy)]
        apply Finset.sum_congr rfl
        intro y hy
        exact ite_eq_left hy
  have hI : (∫⁻ ω, F (cluster G ω x) ∂law p) =
      ∫⁻ ω, ghostAvoid (2*(h : ℝ)) (H.quarterTiltedMass ω x) *
        (∑' e, if e ∈ H.incidentEdges (cluster G ω x) then H.ghostBondWeight x e else 0) ∂law p := by
    apply lintegral_congr
    intro ω
    dsimp only [F]
    congr 2
    unfold CriticalPercolation.BondGraph.quarterTiltedMass
    apply tsum_congr
    intro y
    rw [H.coe_quarterGhostWeight]
    congr 1
    rw [show H.openGraph ω = openSimpleGraph G ω from criticalModel_openGraph G ω]
    exact propext (conn_iff_reachable G ω x y)
  calc
    _ = ∑' e, ∑' u, ∑' S, ∑' v, averagedQuarterBridge G p x h e u v S :=
      tsum_congr fun e => tsum_congr fun u => ENNReal.tsum_comm
    _ = ∑' e, ∑' S, ∑' u, ∑' v, averagedQuarterBridge G p x h e u v S :=
      tsum_congr fun e => ENNReal.tsum_comm
    _ = ∑' S, ∑' e, ∑' u, ∑' v, averagedQuarterBridge G p x h e u v S := ENNReal.tsum_comm
    _ ≤ ∑' S : Finset V, (2*R*Q) * (law p {ω | cluster G ω x = (S : Set V)} * F (S : Set V)) := by
      apply ENNReal.tsum_le_tsum
      intro S
      exact (averagedQuarterBridge_cluster_sum_le G hc hl p hp hfin K hbound S x h).trans_eq (by rw [hF]; dsimp [R,Q,H]; ac_rfl)
    _ = (2*R*Q) * ∫⁻ ω, F (cluster G ω x) ∂law p := by
      rw [ENNReal.tsum_mul_left]
      congr 1
      have hf : ∀ᵐ ω ∂(criticalModel G).law p, ((criticalModel G).cluster ω x).Finite := by
        change ∀ᵐ ω ∂law p, ((criticalModel G).cluster ω x).Finite
        simpa only [criticalModel_cluster] using hfin x
      have hh := ((criticalModel G).lintegral_eq_sum_finite_clusters p x hf F).symm
      change (∑' S : Finset V, law p {ω | (criticalModel G).cluster ω x = (S : Set V)}*F (S : Set V)) =
        ∫⁻ ω, F ((criticalModel G).cluster ω x) ∂law p at hh
      simpa only [criticalModel_cluster] using hh
    _ = _ := by rw [hI]

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostDifferentialAssembly
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem quarter_twoGhost_le_square_add_boundary
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (x : V) (h : ℝ≥0) :
    ENNReal.ofReal (∫ ω, ghostKernel h ((criticalModel G).quarterTiltedMass ω x).toReal ^ 2 ∂law p) ≤
      ENNReal.ofReal ((criticalModel G).quarterGhostMagnetization p x h)^2 +
      (2*(ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ)))*
        ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
      ∫⁻ ω, ghostAvoid (2*(h : ℝ)) ((criticalModel G).quarterTiltedMass ω x) *
        (∑' e, if e ∈ (criticalModel G).incidentEdges (cluster G ω x) then
          (criticalModel G).ghostBondWeight x e else 0) ∂law p := by
  let H := criticalModel G
  have hf : ∀ᵐ ω ∂H.law p, (H.cluster ω x).Finite := by
    change ∀ᵐ ω ∂law p, (H.cluster ω x).Finite
    simpa only [H,criticalModel_cluster] using hfin x
  have hb := averaged_twoGhost_le_fan_add_pivotal_sum G hinj p x (hfin x)
    (ghostFieldLaw h (H.quarterGhostWeight x))
  have htwo := H.quarterTwoGhostConnection_average p x h hf
  have hone := H.quarterGhostConnection_average p x h hf
  change (∫⁻ m, ∫⁻ n, law p
      ({ω | ∃ y ∈ m, (H.openGraph ω).Reachable x y} ∩
        {ω | ∃ y ∈ n, (H.openGraph ω).Reachable x y})
      ∂ghostFieldLaw h (H.quarterGhostWeight x) ∂ghostFieldLaw h (H.quarterGhostWeight x)) =
    ENNReal.ofReal (∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) at htwo
  change (∫⁻ m, law p {ω | ∃ y ∈ m, (H.openGraph ω).Reachable x y}
      ∂ghostFieldLaw h (H.quarterGhostWeight x)) = ENNReal.ofReal (H.quarterGhostMagnetization p x h) at hone
  simp_rw [criticalModel_finiteGhostConnection G] at hb
  rw [htwo,hone] at hb
  exact hb.trans (add_le_add le_rfl
    (averagedQuarterBridge_sum_le_boundary G hc hl p hp hfin K hbound x h))

theorem root_twoGhost_bound
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (hq : (criticalModel G).QuasiTransitive)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (K : ℝ) (hbound : ∀ x h, 0 ≤ h →
      (criticalModel G).quarterGhostMagnetization p x h ≤ K*h^(3/4 : ℝ))
    (D B : ℕ) (hD : ∀ v, ((criticalModel G).incidentEdges {v}).ncard ≤ D)
    (hB : ∀ v, ((criticalModel G).vertexBall v 1).ncard ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ h : ℝ≥0, 0 < h →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        ∫ ω, ghostKernel h ((criticalModel G).quarterTiltedMass ω x).toReal ^ 2 ∂law p) ≤
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x h)^2 +
      A*(h : ℝ)^(3/2 : ℝ) *
        (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
          (criticalModel G).quarterGhostDerivative p x (2*h)) := by
  let H := criticalModel G
  let O := (H.orbitRepresentatives hq).roots
  let R := ENNReal.ofReal (p : ℝ)/ENNReal.ofReal (1-(p : ℝ))
  let J : ℝ≥0∞ := (2*R*ENNReal.ofReal (K^2)) * ((D : ℝ≥0∞)*(2*(B : ℝ≥0∞)^(3/8 : ℝ))) * 2
  have hR : R ≠ ⊤ := by
    dsimp [R]
    apply ENNReal.div_ne_top ENNReal.ofReal_ne_top
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp)).ne'
  have hJ : J ≠ ⊤ := by
    dsimp [J]
    finiteness
  refine ⟨J.toReal,ENNReal.toReal_nonneg,?_⟩
  intro h hh
  have hh0 : (0 : ℝ) < h := hh
  have h2 : (0 : ℝ) < 2*h := by positivity
  let M := ∑ x ∈ O, H.quarterGhostMagnetization p x h
  let Derv := ∑ x ∈ O, H.quarterGhostDerivative p x (2*h)
  have hM (x : V) : 0 ≤ H.quarterGhostMagnetization p x h :=
    integral_nonneg fun _ => ghostKernel_nonneg h.2 ENNReal.toReal_nonneg
  have hDerv (x : V) : 0 ≤ H.quarterGhostDerivative p x (2*h) :=
    integral_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hpow : ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ)) =
      ENNReal.ofReal (K^2) * ENNReal.ofReal ((h : ℝ)^(3/2 : ℝ)) :=
    ENNReal.ofReal_mul (sq_nonneg K)
  have htransport := H.expected_ghost_boundary_weight_le hc hl hq p (by positivity : (0 : ℝ) ≤ 2*h)
    D B hD hB
  have hderiv : (∑ x ∈ O, ∫⁻ ω, ghostAvoid (2*(h : ℝ)) (H.quarterTiltedMass ω x)*H.quarterTiltedMass ω x ∂H.law p) =
      ENNReal.ofReal Derv := by
    simp_rw [H.lintegral_ghostAvoid_mass_eq_derivative p _ h2]
    exact (ENNReal.ofReal_sum_of_nonneg (fun x _ => hDerv x)).symm
  have hsq : (∑ x ∈ O, ENNReal.ofReal (H.quarterGhostMagnetization p x h)^2) ≤ ENNReal.ofReal (M^2) := by
    simp_rw [←ENNReal.ofReal_pow (hM _)]
    rw [←ENNReal.ofReal_sum_of_nonneg (fun x _ => sq_nonneg (H.quarterGhostMagnetization p x h))]
    exact ENNReal.ofReal_le_ofReal (Finset.sum_sq_le_sq_sum_of_nonneg (fun x _ => hM x))
  have hfinal : (∑ x ∈ O, ENNReal.ofReal (∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p)) ≤
      ENNReal.ofReal (M^2) + J*ENNReal.ofReal ((h : ℝ)^(3/2 : ℝ))*ENNReal.ofReal Derv := by
    calc
      _ ≤ (∑ x ∈ O, ENNReal.ofReal (H.quarterGhostMagnetization p x h)^2) +
          (2*R*ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
            ∑ x ∈ O, ∫⁻ ω, ghostAvoid (2*(h : ℝ)) (H.quarterTiltedMass ω x)*
              (∑' e, if e ∈ H.incidentEdges (cluster G ω x) then H.ghostBondWeight x e else 0) ∂law p := by
        rw [Finset.mul_sum,←Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun x _ => quarter_twoGhost_le_square_add_boundary G hinj hc hl p hp hfin K hbound x h
      _ ≤ ENNReal.ofReal (M^2) + (2*R*ENNReal.ofReal (K^2*(h : ℝ)^(3/2 : ℝ))) *
          (((D : ℝ≥0∞)*(2*(B : ℝ≥0∞)^(3/8 : ℝ)))*(2*ENNReal.ofReal Derv)) := by
        apply add_le_add hsq
        apply mul_le_mul' le_rfl
        have htrans := htransport
        change (∑ x ∈ O, ∫⁻ ω, ghostAvoid (2*(h:ℝ)) (H.quarterTiltedMass ω x)*
            (∑' e, if e ∈ H.incidentEdges (H.cluster ω x) then H.ghostBondWeight x e else 0) ∂law p) ≤ _ at htrans
        rw [hderiv] at htrans
        simpa only [H,criticalModel_cluster] using htrans
      _ = _ := by rw [hpow]; dsimp [J]; ac_rfl
  have hreal := ENNReal.toReal_mono (by finiteness) hfinal
  rw [ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_ofReal (sq_nonneg M),ENNReal.toReal_mul,ENNReal.toReal_mul] at hreal
  have hpnonneg : 0 ≤ (h : ℝ)^(3/2 : ℝ) := Real.rpow_nonneg h.2 _
  have hdnonneg : 0 ≤ Derv := Finset.sum_nonneg (fun x _ => hDerv x)
  rw [ENNReal.toReal_ofReal hpnonneg,ENNReal.toReal_ofReal hdnonneg] at hreal
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _))] using hreal

end Percolation.BenjaminiSchramm

end

end OAI
end

section
-- module Solutions.OAIQ078_BS.BenjaminiSchramm_GhostMomentDischarge
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal NNReal BigOperators

namespace Percolation.BenjaminiSchramm

lemma ghostKernel_mono_field {h k x : ℝ} (hhk : h ≤ k) (hx : 0 ≤ x) :
    ghostKernel h x ≤ ghostKernel k x := by
  unfold ghostKernel
  apply sub_le_sub_left
  exact Real.exp_le_exp.mpr (by nlinarith)

lemma ghostMagnetization_le_derivative_add_twoGhost_same
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 < h) :
    ghostMagnetization μ X h ≤ h*ghostMagnetizationDerivative μ X h +
      2*∫ ω, ghostKernel h (X ω)^2 ∂μ := by
  apply (ghostMagnetization_le_derivative_add_two_ghost μ X hX hX0 hh).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  apply integral_mono
    (integrable_ghostKernel_sq μ X hX hX0 (by positivity : 0 ≤ h/2))
    (integrable_ghostKernel_sq μ X hX hX0 hh.le)
  intro ω
  exact pow_le_pow_left₀ (ghostKernel_nonneg (by positivity) (hX0 ω))
    (ghostKernel_mono_field (by linarith) (hX0 ω)) 2

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem root_quarterGhost_differential_bs_oai
    (hinj : Function.Injective G)
    (hc : (criticalModel G).fullGraph.Connected) (hl : LocallyFinite G)
    (hq : (criticalModel G).QuasiTransitive)
    (p : unitInterval) (hp : (p : ℝ) < 1)
    (hfin : ∀ v, ∀ᵐ ω ∂law p, (cluster G ω v).Finite)
    (hmoment : ∀ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
      (criticalModel G).quarterThreeQuarterMoment p x < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x (t^4)) ≤
      C*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostMagnetization p x (t^4))^2 +
      t^4*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostDerivative p x (t^4)) +
      C*t^6*(∑ x ∈ ((criticalModel G).orbitRepresentatives hq).roots,
        (criticalModel G).quarterGhostDerivative p x (t^4)) := by
  let H := criticalModel G
  let O := (H.orbitRepresentatives hq).roots
  obtain ⟨K,_,hK⟩ := H.uniform_quarterGhost_moment_bound hq p hmoment
  obtain ⟨D,_,hD⟩ := H.uniform_incident_bound hq
  obtain ⟨B,hB⟩ := H.uniform_ball_bound hq 1
  obtain ⟨A,hA,hbound⟩ := root_twoGhost_bound G hinj hc hl hq p hp hfin K hK D B hD hB
  let C := max 2 (2*A)
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCA : 2*A ≤ C := le_max_right _ _
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht _
  let h : ℝ≥0 := ⟨t^4,by positivity⟩
  have hh : (0 : ℝ) < h := by change 0 < t^4; exact pow_pos ht 4
  let M := ∑ x ∈ O, H.quarterGhostMagnetization p x (t^4)
  let Derv := ∑ x ∈ O, H.quarterGhostDerivative p x (t^4)
  have hDnonneg (x : V) : 0 ≤ H.quarterGhostDerivative p x (t^4) :=
    integral_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hDerv : 0 ≤ Derv := Finset.sum_nonneg fun x _ => hDnonneg x
  have hdouble : (∑ x ∈ O, H.quarterGhostDerivative p x (2*h)) ≤ Derv := by
    apply Finset.sum_le_sum
    intro x _
    unfold CriticalPercolation.BondGraph.quarterGhostDerivative ghostMagnetizationDerivative
    apply integral_mono
      (hasDerivAt_ghostMagnetization (H.law p) _ (H.measurable_quarterTiltedMass x).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg) (by positivity : (0 : ℝ) < 2*h)).1
      (hasDerivAt_ghostMagnetization (H.law p) _ (H.measurable_quarterTiltedMass x).ennreal_toReal
        (fun _ => ENNReal.toReal_nonneg) (by positivity : (0 : ℝ) < t^4)).1
    intro ω
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    apply Real.exp_le_exp.mpr
    change -(2*t^4)*(H.quarterTiltedMass ω x).toReal ≤ -(t^4)*(H.quarterTiltedMass ω x).toReal
    exact mul_le_mul_of_nonneg_right (by nlinarith [pow_nonneg ht.le 4]) ENNReal.toReal_nonneg
  have hpow : (h : ℝ)^(3/2 : ℝ) = t^6 := by
    change (t^4)^(3/2 : ℝ) = t^6
    rw [←Real.rpow_natCast_mul ht.le]
    norm_num
  have hsq := hbound h hh
  rw [hpow] at hsq
  have herror := mul_le_mul_of_nonneg_left hdouble (by positivity : 0 ≤ A*t^6)
  have hbase : M ≤ t^4*Derv + 2*(∑ x ∈ O,
      ∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) := by
    calc
      _ ≤ ∑ x ∈ O, (t^4*H.quarterGhostDerivative p x (t^4) +
          2*∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) := by
        apply Finset.sum_le_sum
        intro x _
        exact ghostMagnetization_le_derivative_add_twoGhost_same (H.law p)
          (fun ω => (H.quarterTiltedMass ω x).toReal) (H.measurable_quarterTiltedMass x).ennreal_toReal
          (fun _ => ENNReal.toReal_nonneg) (by positivity)
      _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
  have h1 : 2*M^2 ≤ C*M^2 := mul_le_mul_of_nonneg_right hC2 (sq_nonneg M)
  have h2 : 2*A*t^6*Derv ≤ C*t^6*Derv :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCA (by positivity)) hDerv
  change M ≤ C*M^2+t^4*Derv+C*t^6*Derv
  change (∑ x ∈ O, ∫ ω, ghostKernel h (H.quarterTiltedMass ω x).toReal^2 ∂law p) ≤
    M^2+A*t^6*(∑ x ∈ O, H.quarterGhostDerivative p x (2*h)) at hsq
  change A*t^6*(∑ x ∈ O, H.quarterGhostDerivative p x (2*h)) ≤ A*t^6*Derv at herror
  nlinarith

end Percolation.BenjaminiSchramm

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs_oai.{u_1, u_2} := @OAI.Percolation.BenjaminiSchramm.root_quarterGhost_differential_bs_oai.{u_1, u_2}
