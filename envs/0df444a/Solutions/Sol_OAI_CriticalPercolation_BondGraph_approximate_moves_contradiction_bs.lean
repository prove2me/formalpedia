-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:44:02.054315+00:00
-- url     : https://prove2.me/submissions/4b032162-4121-4cae-a23a-0d705ad55966

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_coordinate_pinned_corridor_failure_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_original_root_corridor_miss_bs

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProductConditioning
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_forceOn_joint (S : Set E) :
    Measurable (fun z : Set E × Set E => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    inferInstance (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · simpa only [forceOn,ite_eq_left he,Function.comp_def] using (measurable_set_mem e).comp measurable_fst
  · simpa only [forceOn,ite_eq_right he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd

lemma forceOn_resample_law (q : E → unitInterval) (S : Set E) :
    ((law q).prod (law q)).map (fun z : Set E × Set E => forceOn S z.1 z.2)=law q := by
  let f : Set E → Set E := forceOn Sᶜ ∅
  let g : Set E → Set E := forceOn S ∅
  have hf : Measurable f := measurable_forceOn _ _
  have hg : Measurable g := measurable_forceOn _ _
  have hfb : @Measurable (Set E) (Set E) (blockSigma S) inferInstance f := by
    have hh := measurable_forceOn_block Sᶜ (∅ : Set E)
    rw [compl_compl] at hh
    exact hh
  have hgb : @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance g :=
    measurable_forceOn_block S ∅
  have hi : IndepFun f g (law q) :=
    indep_of_indep_of_le (independent_blocks q S) hfb.comap_le hgb.comap_le
  have hm := hi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hp := congrArg (Measure.map (fun z : Set E × Set E => forceOn S z.1 z.2)) hm
  rw [Measure.map_prod_map _ _ hf hg,Measure.map_map (measurable_forceOn_joint S)
    (hf.prodMk hg),Measure.map_map (measurable_forceOn_joint S) (hf.prodMap hg)] at hp
  have he1 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ (fun ω => (f ω,g ω))=id := by
    funext ω
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  have he2 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ Prod.map f g=
      (fun z : Set E × Set E => forceOn S z.1 z.2) := by
    funext z
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  rw [he1,he2,Measure.map_id] at hp
  exact hp.symm

lemma forceOn_map_law (q : E → unitInterval) (S σ : Set E) :
    (law q).map (forceOn S σ)=law (pinnedParameters q S σ) := by
  simp only [law_eq_infinitePi]
  have hm (e : E) : Measurable (fun b : Prop => if e∈S then e∈σ else b) := .of_discrete
  have h := Measure.infinitePi_map_pi (fun e => bitMeasure (q e)) hm
  change (Measure.infinitePi (fun e => bitMeasure (q e))).map
    (fun (ω : E → Prop) e => if e∈S then e∈σ else ω e)=
    Measure.infinitePi (fun e => bitMeasure (pinnedParameters q S σ e))
  rw [h]
  congr 1
  funext e
  by_cases he : e∈S
  · simp only [ite_eq_left he,Measure.map_const,measure_univ,one_smul]
    by_cases hs : e∈σ <;> simp [pinnedParameters,he,hs,bitMeasure]
  · simp [pinnedParameters,he]

lemma blockProbability_le_one (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (σ : Set E) : blockProbability q S A σ≤1 := prob_le_one

lemma lintegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫⁻ σ, blockProbability q S A σ ∂law q)=law q A := by
  simp_rw [blockProbability_eq_lintegral q S A hA]
  have hm : Measurable (fun z : Set E × Set E =>
      A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    (measurable_const.indicator hA).comp (measurable_forceOn_joint S)
  rw [← lintegral_prod _ hm.aemeasurable]
  have hi : Measurable (A.indicator (1 : Set E → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_map hi (measurable_forceOn_joint S),
    forceOn_resample_law,lintegral_indicator_one hA]

lemma blockSigma_eq_comap (S : Set E) :
    blockSigma S=MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      Set.instMeasurableSpace := by
  change (⨆ e∈S, MeasurableSpace.comap (fun σ : Set E => e∈σ) inferInstance)=
    MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      (⨆ e : S, MeasurableSpace.comap (fun σ : Set S => e∈σ) inferInstance)
  rw [MeasurableSpace.comap_iSup,iSup_subtype']
  congr 1
  funext e
  rw [MeasurableSpace.comap_comp]
  rfl

lemma block_event_forceOn (S : Set E) (B : Set (Set E))
    (hB : MeasurableSet[blockSigma S] B) (σ ω : Set E) :
    forceOn S σ ω∈B ↔ σ∈B := by
  rw [blockSigma_eq_comap] at hB
  obtain ⟨C,hC,rfl⟩ := hB
  have he : (Subtype.val ⁻¹' forceOn S σ ω : Set S)=Subtype.val ⁻¹' σ := by
    ext e
    simp only [mem_preimage,mem_forceOn,ite_eq_left e.property]
  change (Subtype.val ⁻¹' forceOn S σ ω)∈C ↔ (Subtype.val ⁻¹' σ)∈C
  rw [he]

lemma blockProbability_inter_block (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hB : MeasurableSet[blockSigma S] B) (σ : Set E) :
    blockProbability q S (A∩B) σ=B.indicator (blockProbability q S A) σ := by
  unfold blockProbability
  by_cases hσ : σ∈B
  · rw [Set.indicator_of_mem hσ]
    congr 1
    ext ω
    simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,and_true]
  · rw [Set.indicator_of_notMem hσ]
    have he : forceOn S σ ⁻¹' (A∩B)=∅ := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,
        and_false,Set.mem_empty_iff_false]
    rw [he,measure_empty]

lemma setLIntegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet[blockSigma S] B) :
    (∫⁻ σ in B, blockProbability q S A σ ∂law q)=law q (A∩B) := by
  have hmB := (blockSigma_le S) _ hB
  rw [← lintegral_indicator hmB]
  simp_rw [← blockProbability_inter_block q S A B hB]
  exact lintegral_blockProbability q S (A∩B) (hA.inter hmB)

lemma forceOn_absorb (S T σ τ : Set E) (hST : S⊆T) :
    forceOn T τ ∘ forceOn S σ=forceOn T τ := by
  funext ω
  ext e
  change (e∈forceOn T τ (forceOn S σ ω)) ↔ e∈forceOn T τ ω
  by_cases heT : e∈T
  · simp only [mem_forceOn,ite_eq_left heT]
  · have heS : e∉S := fun he => heT (hST he)
    simp only [mem_forceOn,ite_eq_right heT,ite_eq_right heS]

lemma blockProbability_pin_smaller (q : E → unitInterval) (S T σ : Set E)
    (hST : S⊆T) (A : Set (Set E)) (hA : MeasurableSet A) (τ : Set E) :
    blockProbability (pinnedParameters q S σ) T A τ=blockProbability q T A τ := by
  unfold blockProbability
  rw [← forceOn_map_law q S σ,Measure.map_apply (measurable_forceOn S σ)
    (hA.preimage (measurable_forceOn T τ)),← Set.preimage_comp,forceOn_absorb S T σ τ hST]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshTrial
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma integrable_blockProbability_real (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    Integrable (fun σ => (blockProbability q S A σ).toReal) (law q) := by
  have hm := (measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl
  apply (integrable_const (1:ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with σ
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (by simp) (blockProbability_le_one q S A σ)

lemma integral_blockProbability_real (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ σ, (blockProbability q S A σ).toReal ∂law q)=(law q).real A := by
  have hm := (measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl
  rw [integral_toReal hm.aemeasurable (ae_of_all _ (fun σ =>
    (blockProbability_le_one q S A σ).trans_lt ENNReal.one_lt_top)),
    lintegral_blockProbability q S A hA]
  rfl

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)

theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)

theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc

lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma hitEvent_mono_edges (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ConditionalGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma seedHitEvent_upper (B T : Set V) : IsUpperSet (G.seedHitEvent B T) := by
  intro ω τ hωτ hω
  obtain ⟨b,hb,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨b,hb,G.hitEvent_mono_edges b T hωτ hω⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_PredictionFailure
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma prediction_persists (q : E → unitInterval) (S T U σ τ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma U] A)
    (hST : S∩U=T∩U) (hstates : ∀ e∈S∩U, (e∈σ ↔ e∈τ)) :
    blockProbability q S A σ=blockProbability q T A τ := by
  unfold blockProbability
  congr 1
  ext ω
  have hrestrict : U∩forceOn S σ ω=U∩forceOn T τ ω := by
    ext e
    by_cases he : e∈U
    · have heST : e∈S ↔ e∈T := by
        have hh := Set.ext_iff.mp hST e
        simpa only [Set.mem_inter_iff,he,and_true] using hh
      by_cases heS : e∈S
      · have heT := heST.mp heS
        simp only [Set.mem_inter_iff,he,true_and,mem_forceOn,ite_eq_left heS,ite_eq_left heT]
        exact hstates e ⟨heS,he⟩
      · have heT : e∉T := fun h => heS (heST.mpr h)
        simp only [Set.mem_inter_iff,he,true_and,mem_forceOn,ite_eq_right heS,ite_eq_right heT]
    · simp only [Set.mem_inter_iff,he,false_and]
  have hforce : forceOn U (forceOn S σ ω) (forceOn T τ ω)=forceOn T τ ω := by
    ext e
    by_cases he : e∈U
    · have hh := Set.ext_iff.mp hrestrict e
      simpa only [Set.mem_inter_iff,he,true_and,mem_forceOn,if_true,ite_eq_left he] using hh
    · simp only [mem_forceOn,ite_eq_right he]
  have hh := block_event_forceOn U A hA (forceOn S σ ω) (forceOn T τ ω)
  rw [hforce] at hh
  exact hh.symm

lemma blockProbability_real_compl (q : E → unitInterval) (S σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (blockProbability q S Aᶜ σ).toReal=1-(blockProbability q S A σ).toReal := by
  change (law q).real ((forceOn S σ ⁻¹' A)ᶜ)=1-(law q).real (forceOn S σ ⁻¹' A)
  exact probReal_compl_eq_one_sub (hA.preimage (measurable_forceOn S σ))

lemma integral_known_prediction_defect (q : E → unitInterval) (S : Set E)
    (A C : Set (Set E)) (hA : MeasurableSet[blockSigma S] A) (hC : MeasurableSet C) :
    (∫ σ, A.indicator (fun σ => 1-(blockProbability q S C σ).toReal) σ ∂law q)=
      (law q).real (A\C) := by
  have he : (fun σ => A.indicator (fun σ => 1-(blockProbability q S C σ).toReal) σ)=
      (fun σ => (blockProbability q S (Cᶜ∩A) σ).toReal) := by
    funext σ
    rw [blockProbability_inter_block q S Cᶜ A hA]
    by_cases hσ : σ∈A
    · simp only [Set.indicator_of_mem hσ,blockProbability_real_compl q S σ C hC]
    · simp only [Set.indicator_of_notMem hσ,ENNReal.toReal_zero]
  rw [he,integral_blockProbability_real q S (Cᶜ∩A) (hC.compl.inter ((blockSigma_le S) _ hA))]
  congr 1
  exact Set.inter_comm _ _

lemma bad_prediction_bound (q : E → unitInterval) (S : Set E)
    (A C : Set (Set E)) (hA : MeasurableSet[blockSigma S] A) (hC : MeasurableSet C)
    (δ : ℝ) (hδ : 0<δ) :
    (law q).real (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})≤
      (law q).real (A\C)/δ := by
  let g := fun σ => (blockProbability q S C σ).toReal
  let B := A∩{σ : Set E | g σ<1-δ}
  have hg : Measurable g :=
    ((measurable_blockProbability q S C hC).mono (blockSigma_le S) le_rfl).ennreal_toReal
  have hma := (blockSigma_le S) _ hA
  have hmb : MeasurableSet B := hma.inter (measurableSet_lt hg measurable_const)
  have hgi : Integrable g (law q) := integrable_blockProbability_real q S C hC
  have hdef : Integrable (A.indicator (fun σ => 1-g σ)) (law q) :=
    ((integrable_const 1).sub hgi).indicator hma
  have hl : Integrable (fun σ => δ*B.indicator (1 : Set E → ℝ) σ) (law q) :=
    ((integrable_const 1).indicator hmb).const_mul δ
  have hi := integral_mono hl hdef (fun σ => by
    by_cases hσ : σ∈B
    · rw [Set.indicator_of_mem hσ,Set.indicator_of_mem hσ.1]
      dsimp only [Pi.one_apply]
      have hh := hσ.2
      dsimp only [Set.mem_ofPred_eq] at hh
      linarith
    · rw [Set.indicator_of_notMem hσ,mul_zero]
      by_cases hσA : σ∈A
      · rw [Set.indicator_of_mem hσA]
        exact sub_nonneg.mpr (ENNReal.toReal_mono (by simp) (blockProbability_le_one q S C σ))
      · rw [Set.indicator_of_notMem hσA])
  rw [integral_const_mul,integral_indicator_one hmb] at hi
  have he := integral_known_prediction_defect q S A C hA hC
  change (∫ σ, A.indicator (fun σ => 1-g σ) σ ∂law q)=(law q).real (A\C) at he
  rw [he] at hi
  exact (le_div_iff₀ hδ).mpr (by nlinarith [hi])

theorem two_prediction_failure (q : E → unitInterval) (S : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma S] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ) (hin : 1-δ≤(law q).real A)
    (hCfail : (law q).real (A\C)≤a) (hDfail : (law q).real (A\D)≤a) :
    (law q).real (Aᶜ ∪
      (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ}) ∪
      (A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ}))≤δ+2*a/δ := by
  have hma := (blockSigma_le S) _ hA
  have hcomp : (law q).real Aᶜ≤δ := by rw [probReal_compl_eq_one_sub hma]; linarith
  have hc := (bad_prediction_bound q S A C hA hC δ hδ).trans
    (div_le_div_of_nonneg_right hCfail hδ.le)
  have hd := (bad_prediction_bound q S A D hA hD δ hδ).trans
    (div_le_div_of_nonneg_right hDfail hδ.le)
  have h1 := measureReal_union_le (μ := law q) (s₁ := Aᶜ)
    (s₂ := A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})
  have h2 := measureReal_union_le (μ := law q)
    (s₁ := Aᶜ∪(A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ}))
    (s₂ := A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ})
  calc
    _ ≤ _ := h2
    _ ≤ (law q).real Aᶜ+(law q).real
        (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})+
        (law q).real (A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ}) :=
      add_le_add h1 le_rfl
    _ ≤ δ+a/δ+a/δ := add_le_add (add_le_add hcomp hc) hd
    _ = δ+2*a/δ := by ring

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_RestrictedSeed
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma restrictedSeed_mono (A T : Set V) {S U : Set E} (h : S⊆U) :
    G.restrictedSeed A T S⊆G.restrictedSeed A T U := by
  intro ω hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_right _ h) hω

lemma seed_prediction_persists [Countable V] [Countable E]
    (q : E → unitInterval) (A T : Set V) (I F D σ : Set E)
    (hIF : I⊆F) (hfresh : F∩D⊆I) :
    blockProbability q I (G.restrictedSeed A T (I∪D)) σ ≤
      blockProbability q F (G.restrictedSeed A T (F∪D)) σ := by
  have hrestrict : I∩(I∪D)=F∩(I∪D) := by
    ext e
    constructor <;> intro h
    · exact ⟨hIF h.1,h.2⟩
    · rcases h.2 with hi|hd
      · exact ⟨hi,Or.inl hi⟩
      · exact ⟨hfresh ⟨h.1,hd⟩,Or.inr hd⟩
  rw [prediction_persists q I F (I∪D) σ σ _
    (G.measurableSet_restrictedSeed A T (I∪D)) hrestrict (fun _ _ => Iff.rfl)]
  apply measure_mono
  intro ω hω
  exact G.restrictedSeed_mono A T (Set.union_subset_union_left D hIF) hω

lemma restrictedSeed_self (A T : Set V) (h : (A∩T).Nonempty) (S : Set E) :
    G.restrictedSeed A T S=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  obtain ⟨v,hvA,hvT⟩ := h
  exact Set.mem_iUnion₂.mpr ⟨v,hvA,v,SimpleGraph.Reachable.refl _,hvT⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AdaptiveReveal
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BernoulliProduct

namespace RevealPartition
variable {E I : Type*} [Fintype I] (P : RevealPartition E I)

lemma cell_measurable (i : I) : MeasurableSet (P.cell i) :=
  (blockSigma_le (P.block i)) _ (P.measurable i)

lemma historySigma_le : P.historySigma ≤ (inferInstance : MeasurableSpace (Set E)) := by
  intro A hA
  have he : A=⋃ i, A∩P.cell i := by rw [← Set.inter_iUnion,P.cover,Set.inter_univ]
  rw [he]
  exact MeasurableSet.iUnion (fun i => (blockSigma_le (P.block i)) _ (hA i))

lemma probability_on_cell (q : E → unitInterval) (A : Set (Set E))
    {σ : Set E} {i : I} (hi : σ∈P.cell i) :
    P.probability q A σ=blockProbability q (P.block i) A σ := by
  rw [probability,Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    exact hji (P.cell_unique hj hi)
  · simp

theorem setLIntegral_probability (q : E → unitInterval) (A B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet[P.historySigma] B) :
    (∫⁻ σ in B, P.probability q A σ ∂law q)=law q (A∩B) := by
  have hmB := P.historySigma_le _ hB
  have hf (i : I) : Measurable ((P.cell i).indicator (blockProbability q (P.block i) A)) :=
    ((measurable_blockProbability q (P.block i) A hA).mono (blockSigma_le _) le_rfl).indicator
      (P.cell_measurable i)
  change (∫⁻ σ in B, ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ ∂law q)=_
  rw [lintegral_finsetSum _ (fun i _ => hf i)]
  have he (i : I) :
      (∫⁻ σ in B, (P.cell i).indicator (blockProbability q (P.block i) A) σ ∂law q)=
      law q (A∩(B∩P.cell i)) := by
    rw [lintegral_indicator (P.cell_measurable i),Measure.restrict_restrict
      (P.cell_measurable i),Set.inter_comm (P.cell i) B]
    exact setLIntegral_blockProbability q (P.block i) A (B∩P.cell i) hA (hB i)
  simp_rw [he]
  have hd : Pairwise (Disjoint on (fun i => A∩(B∩P.cell i))) := by
    intro i j hij
    exact (P.disjoint hij).mono (fun _ h => h.2.2) (fun _ h => h.2.2)
  rw [← tsum_fintype (L := .unconditional _),← measure_iUnion hd (fun i => hA.inter (hmB.inter (P.cell_measurable i)))]
  congr 1
  rw [← Set.inter_iUnion,← Set.inter_iUnion,P.cover,Set.inter_univ]

lemma measureReal_inter_le (q : E → unitInterval) (A B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet[P.historySigma] B)
    (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ σ∈B, P.probability q A σ≤ENNReal.ofReal ε) :
    (law q).real (B∩A)≤ε*(law q).real B := by
  have hh : law q (A∩B)≤ENNReal.ofReal ε*law q B := by
    rw [← P.setLIntegral_probability q A B hA hB]
    calc
      (∫⁻ σ in B, P.probability q A σ ∂law q) ≤
          ∫⁻ _ in B, ENNReal.ofReal ε ∂law q :=
        setLIntegral_mono' (P.historySigma_le _ hB) hb
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)) hh
  simpa only [Set.inter_comm A B,ENNReal.toReal_mul,ENNReal.toReal_ofReal hε,
    Measure.real] using ht

end RevealPartition
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_DecisionHistory
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct

namespace DecisionRule
variable {E S : Type*} (D : DecisionRule E S)

lemma partition_block (n : ℕ) (w : DecisionCode n) :
    (D.partition n).block w=D.block (D.state n w) :=
  (D.partitionWithBlock n).property w

lemma partition_cell_succ (n : ℕ) (w : DecisionCode n) (b : Bool) :
    (D.partition (n+1)).cell (w,b)=(D.partition n).cell w∩
      {ω | (if ω∈D.accept n (D.state n w) then true else false)=b} := rfl

lemma historySigma_step (n : ℕ) : (D.partition n).historySigma ≤ (D.partition (n+1)).historySigma := by
  intro A hA w
  rcases w with ⟨w,b⟩
  change MeasurableSet[blockSigma (D.further n (D.state n w))]
    (A ∩ ((D.partition n).cell w ∩
      {ω | (if ω∈D.accept n (D.state n w) then true else false)=b}))
  rw [← Set.inter_assoc]
  have hmono : blockSigma (D.block (D.state n w)) ≤ blockSigma (D.further n (D.state n w)) :=
    iSup₂_mono' (fun e he => ⟨e,D.contained n (D.state n w) he,le_rfl⟩)
  refine (hmono _ ?_).inter ?_
  · rw [← D.partition_block n w]
    exact hA w
  · have hm : @Measurable (Set E) Bool (blockSigma (D.further n (D.state n w))) inferInstance
        (fun ω => if ω∈D.accept n (D.state n w) then true else false) :=
      Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const
    exact hm (MeasurableSet.singleton b)

lemma historySigma_mono : Monotone (fun n => (D.partition n).historySigma) :=
  monotone_nat_of_le_succ D.historySigma_step

lemma failure_on_cell (n : ℕ) {w : DecisionCode n} {ω : Set E}
    (hw : ω∈(D.partition n).cell w) :
    ω∈D.failure n ↔ D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w) := by
  constructor
  · intro h
    obtain ⟨v,hv,hf⟩ := Set.mem_iUnion.mp h
    have he := (D.partition n).cell_unique hv hw
    change D.active n (D.state n v) ∧ ω∉D.accept n (D.state n v) at hf
    simpa only [he] using hf
  · intro h
    exact Set.mem_iUnion.mpr ⟨w,hw,h⟩

lemma failure_measurable (n : ℕ) : MeasurableSet (D.failure n) := by
  apply MeasurableSet.iUnion
  intro w
  exact ((D.partition n).cell_measurable w).inter
    ((MeasurableSet.const _).inter ((blockSigma_le _) _ (D.measurable n (D.state n w))).compl)

lemma failure_history_measurable (n : ℕ) :
    MeasurableSet[(D.partition (n+1)).historySigma] (D.failure n) := by
  intro w
  rcases w with ⟨w,b⟩
  have he : D.failure n∩(D.partition (n+1)).cell (w,b)=
      {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}∩
        (D.partition (n+1)).cell (w,b) := by
    ext ω
    constructor <;> intro h
    · exact ⟨(D.failure_on_cell n (by rw [D.partition_cell_succ] at h; exact h.2.1)).mp h.1,h.2⟩
    · exact ⟨(D.failure_on_cell n (by rw [D.partition_cell_succ] at h; exact h.2.1)).mpr h.1,h.2⟩
  rw [he]
  apply MeasurableSet.inter _ ((D.partition (n+1)).measurable (w,b))
  change MeasurableSet[blockSigma (D.further n (D.state n w))] _
  exact (MeasurableSet.const _).inter (D.measurable n (D.state n w)).compl

lemma failure_probability_on_cell (q : E → unitInterval) (n : ℕ)
    {w : DecisionCode n} {σ : Set E} (hw : σ∈(D.partition n).cell w) :
    blockProbability q ((D.partition n).block w) (D.failure n) σ=
      blockProbability q (D.block (D.state n w))
        {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)} σ := by
  rw [← D.partition_block n w]
  unfold blockProbability
  congr 1
  ext ω
  apply D.failure_on_cell
  exact (block_event_forceOn _ _ ((D.partition n).measurable w) σ ω).mpr hw

theorem conditional_failure_bound (q : E → unitInterval) (B : Set (Set E))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ n w σ, σ∈(D.partition n).cell w → σ∈B →
      (blockProbability q (D.block (D.state n w))
        {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)} σ).toReal ≤ ε) :
    ∀ n A, MeasurableSet[(D.partition n).historySigma] A → A⊆B →
      (law q).real (A∩D.failure n) ≤ ε*(law q).real A := by
  intro n A hmA hAB
  apply (D.partition n).measureReal_inter_le q (D.failure n) A (D.failure_measurable n) hmA ε hε
  intro σ hσ
  obtain ⟨w,hw⟩ := (D.partition n).exists_cell σ
  rw [(D.partition n).probability_on_cell q (D.failure n) hw,D.failure_probability_on_cell q n hw]
  exact (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt (blockProbability_le_one _ _ _ _) ENNReal.one_lt_top))
    ENNReal.ofReal_ne_top).mp (by rw [ENNReal.toReal_ofReal hε]; exact hlocal n w σ hw (hAB hσ))

lemma codeOf_mem (n : ℕ) (ω : Set E) : ω∈(D.partition n).cell (D.codeOf n ω) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,rfl⟩

end DecisionRule
end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorSeparation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.Corridor

lemma int_eq_of_close (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<1) : a=b := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<1 := by exact_mod_cast h2
  omega

lemma int_endpoint_interval (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<2) :
    b=a ∨ b=a+1 := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<2 := by exact_mod_cast h2
  omega

lemma box_disjoint (j h : ℝ) (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (box j h v) (box j h w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  rw [abs_le] at hx1 hx2 hy1 hy2
  apply hv
  apply Prod.ext
  · apply int_eq_of_close <;> linarith
  · apply int_eq_of_close <;> linarith

lemma box_tube_endpoint (j h : ℝ) (hs : j+h<1) (hj : j<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈tube h e) :
    v=source e ∨ v=target e := by
  obtain ⟨a,b⟩ := v
  obtain ⟨⟨c,d⟩,s⟩ := e
  obtain ⟨hx1,hx2⟩ := hx
  rw [abs_le] at hx1 hx2
  cases s with
  | true =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
    rw [abs_le] at hy
    have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
    subst d
    have ha : a=c ∨ a=c+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases ha with rfl|rfl <;> simp [source,target]
  | false =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
    rw [abs_le] at hy
    have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
    subst c
    have hb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases hb with rfl|rfl <;> simp [source,target]

lemma tubes_opposite (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) {x : Point} (hx : x∈tube h ((a,b),true))
    (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have hac : c=a ∨ c=a+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  have hdb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  refine ⟨(c,b),?_,?_,?_⟩
  · rcases hac with rfl|rfl <;> simp [endpoints,source,target]
  · rcases hdb with rfl|rfl <;> simp [endpoints,source,target]
  · constructor <;> rw [abs_le] <;> constructor <;> dsimp <;> linarith

lemma tubes_parallel_true (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),true)) (hy : x∈tube h ((c,d),true)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),true) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
  rw [abs_le] at hx hy
  have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
  subst d
  have ha : a≠c := by intro h; subst c; exact hne rfl
  have hab : a=c+1 ∨ c=a+1 := by
    have h1 : a ≤ c+1 := by exact_mod_cast (show (a : ℝ) ≤ c+1 by linarith)
    have h2 : c≤a+1 := by exact_mod_cast (show (c : ℝ)≤a+1 by linarith)
    omega
  rcases hab with rfl|rfl
  · refine ⟨(c+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma tubes_parallel_false (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),false)) (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),false) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(2*(a : ℝ)-x.1)|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
  subst c
  have hb : b≠d := by intro h; subst d; exact hne rfl
  have hbd : b=d+1 ∨ d=b+1 := by
    have h1 : b≤d+1 := by exact_mod_cast (show (b : ℝ)≤d+1 by linarith)
    have h2 : d≤b+1 := by exact_mod_cast (show (d : ℝ)≤b+1 by linarith)
    omega
  rcases hbd with rfl|rfl
  · refine ⟨(a,d+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a,b+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith

lemma distinct_tubes_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈tube h e) (hy : x∈tube h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  obtain ⟨⟨c,d⟩,t⟩ := f
  cases s <;> cases t
  · exact tubes_parallel_false j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,false)) he)) hx hy
  · obtain ⟨v,hv,hv',hb⟩ := tubes_opposite j h hh hhj hh1 c d a b hy hx
    exact ⟨v,hv',hv,hb⟩
  · exact tubes_opposite j h hh hhj hh1 a b c d hx hy
  · exact tubes_parallel_true j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,true)) he)) hx hy

lemma box_domain_endpoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈domain j h e) :
    v∈endpoints e := by
  rcases hy with (hy|hy)|hy
  · have he : v=source e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · have he : v=target e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · exact (box_tube_endpoint j h (by linarith) (by linarith) hx hy)

theorem distinct_domains_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈domain j h e) (hy : x∈domain j h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  rcases hx with (hx|hx)|hx
  · exact ⟨source e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · exact ⟨target e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · rcases hy with (hy|hy)|hy
    · exact ⟨source f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact ⟨target f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact distinct_tubes_intersection j h hh hhj (by linarith) hne hx hy

lemma nonincident_domains_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (he : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (domain j h e) (domain j h f) := by
  have hne : e≠f := by
    intro hh
    subst f
    exact Set.disjoint_left.mp he (show source e∈endpoints e by simp [endpoints])
      (by simp [endpoints])
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v,hv,hv',_⟩ := distinct_domains_intersection j h hh hhj hs hne hx hy
  exact Set.disjoint_left.mp he hv hv'

lemma nonendpoint_domain_box_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) : Disjoint (box j h v) (domain j h e) := by
  exact Set.disjoint_left.mpr fun _ hx hy => hv (box_domain_endpoint j h hh hhj hs hx hy)

end CriticalPercolation.Corridor
end
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_OpenTrialBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorGraph
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma coordinate_ball_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    {v w : V} {n : ℕ} (hw : w∈G.vertexBall v n) : |f w-f v|≤n*ρ := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hw
    subst w
    simp
  | succ n ih =>
    rcases hw with hw|hw
    · exact (ih hw).trans (by push_cast; nlinarith)
    · obtain ⟨u,hu,huw⟩ := Set.mem_iUnion₂.mp hw
      calc
        |f w-f v| ≤ |f w-f u|+|f u-f v| := abs_sub_le _ _ _
        _ ≤ ρ+n*ρ := add_le_add (hf huw.symm) (ih hu)
        _ = _ := by push_cast; ring

end CriticalPercolation.BondGraph
namespace CriticalPercolation.Corridor
open BondGraph

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

lemma graph_boxes_disjoint (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (graphBox ξ j h v) (graphBox ξ j h w) :=
  (box_disjoint j h hs hv).preimage ξ

lemma graph_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (graphDomain ξ j h e) (graphDomain ξ j h f) :=
  (nonincident_domains_disjoint j h hh hhj hs hef).preimage ξ

lemma edge_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (corridorEdges G ξ j h e) (corridorEdges G ξ j h f) :=
  G.inducedEdges_disjoint (graph_nonincident_disjoint ξ j h hh hhj hs hef)

lemma edge_box_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) :
    Disjoint (boxEdges G ξ j h v) (corridorEdges G ξ j h e) :=
  G.inducedEdges_disjoint
    ((nonendpoint_domain_box_disjoint j h hh hhj hs hv).preimage ξ)

lemma history_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} (he : ∀ f∈H, Disjoint (endpoints f) (endpoints e)) :
    Disjoint (⋃ f∈H, corridorEdges G ξ j h f) (corridorEdges G ξ j h e) := by
  apply Set.disjoint_left.mpr
  intro b hb he'
  obtain ⟨f,hf,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.disjoint_left.mp (edge_nonincident_disjoint G ξ j h hh hhj hs (he f hf)) hb he'

lemma history_intersection_subset (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} {v : Site}
    (he : e∉H) (hH : ∀ f∈H, endpoints f∩endpoints e⊆{v}) :
    (⋃ f∈H, corridorEdges G ξ j h f)∩corridorEdges G ξ j h e⊆boxEdges G ξ j h v := by
  intro b hb
  obtain ⟨f,hf,hbf⟩ := Set.mem_iUnion₂.mp hb.1
  have hne : f≠e := fun h => he (h ▸ hf)
  intro w hw
  obtain ⟨u,hu,hu',hwu⟩ := distinct_domains_intersection j h hh hhj hs hne
    (hbf w hw) (hb.2 w hw)
  have huv : u=v := hH f hf ⟨hu,hu'⟩
  rwa [huv] at hwu

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SpecifiedFailures
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
open scoped Classical ENNReal

namespace CriticalPercolation

theorem specified_failures_with_initialization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B₀ : Set Ω) (hB₀ : MeasurableSet[M 0] B₀)
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n B, MeasurableSet[M n] B → B⊆B₀ →
      μ.real (B∩F n)≤ε*μ.real B)
    (s : Finset ℕ) : μ.real (B₀∩⋂ n∈s, F n) ≤ μ.real B₀*ε^s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert n s hn ih =>
    have hns : n∉s := fun h => (lt_irrefl n) (hn n h)
    have hbs : MeasurableSet[M n] (B₀∩⋂ j∈s, F j) := by
      refine ((hM (Nat.zero_le n)) _ hB₀).inter ?_
      apply MeasurableSet.biInter s.finite_toSet.countable
      intro j hj
      exact hM (Nat.succ_le_of_lt (hn j hj)) _ (hF j)
    have h := hcond n (B₀∩⋂ j∈s, F j) hbs Set.inter_subset_left
    have he : B₀∩⋂ j∈insert n s, F j=(B₀∩⋂ j∈s, F j)∩F n := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [he,Finset.card_insert_of_notMem hns,pow_succ]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ih hε])

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BalancedCycles
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Boundary

lemma balancedPermutation_tail {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e : E) :
    tail (balancedPermutation tail head hb e)=head e :=
  Equiv.ofFiberEquiv_map _ e

theorem exists_closed_trail {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e₀ : E) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → E, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, head (e i)=tail (e (i+1))) ∧ Set.InjOn e (Set.Iio n) := by
  let p := balancedPermutation tail head hb
  let n := Function.minimalPeriod p e₀
  have hn : 0<n := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts e₀)
  refine ⟨n,hn,(fun i => p^[i] e₀),rfl,?_,?_,Function.iterate_injOn_Iio_minimalPeriod⟩
  · exact Function.isPeriodicPt_minimalPeriod p e₀
  · intro i
    dsimp only
    rw [Function.iterate_succ_apply']
    exact (balancedPermutation_tail tail head hb _).symm

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SquareBoundary
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

lemma squareBoundary_finite {S : Set Grid} (hS : S.Finite) : (squareBoundary S).Finite := by
  apply Set.Finite.of_injOn (f := fun e : Edge => (leftSite e,e.2))
    (t := S×ˢ(Set.univ : Set Dir)) ?_ ?_ (hS.prod Set.finite_univ)
  · intro e he
    exact ⟨he.1,Set.mem_univ _⟩
  · rintro ⟨p,d⟩ _ ⟨q,c⟩ _ h
    have hd : d=c := congrArg Prod.snd h
    subst c
    have hp : p=q := add_right_cancel (congrArg Prod.fst h)
    exact Prod.ext hp rfl

lemma squareBoundary_balanced (S : Set Grid) (v : Grid) :
    Fintype.card {d : Dir // (v-step d,d)∈squareBoundary S}=
      Fintype.card {d : Dir // (v,d)∈squareBoundary S} := by
  rcases v with ⟨x,y⟩
  rw [Fintype.card_subtype (fun d : Dir => ((x,y)-step d,d)∈squareBoundary S),
    Fintype.card_subtype (fun d : Dir => ((x,y),d)∈squareBoundary S)]
  simp only [Finset.card_filter,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  simp only [squareBoundary,Set.mem_ofPred_eq,leftSite,rightSite,step,leftOffset,rightOffset]
  simp only [Matrix.cons_val_zero,Prod.mk_add_mk,add_zero,sub_eq_add_neg]
  by_cases h1 : (x,y)∈S <;> by_cases h2 : (x+-1,y)∈S <;>
    by_cases h3 : (x+-1,y+-1)∈S <;> by_cases h4 : (x,y+-1)∈S <;>
    simp_all

theorem squareBoundary_closed_trail {S : Set Grid} (hS : S.Finite)
    (e₀ : Edge) (he₀ : e₀∈squareBoundary S) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → Edge, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, e i∈squareBoundary S) ∧ (∀ i, head (e i)=tail (e (i+1))) ∧
      Set.InjOn e (Set.Iio n) := by
  let := (squareBoundary_finite hS).fintype
  have hb (v : Grid) : Fintype.card {e : squareBoundary S // head e=v}=
      Fintype.card {e : squareBoundary S // tail e=v} :=
    (Fintype.card_congr (incomingEquiv S v)).trans
      ((squareBoundary_balanced S v).trans (Fintype.card_congr (outgoingEquiv S v)).symm)
  obtain ⟨n,hn,e,h0,hn0,hchain,hinj⟩ := exists_closed_trail
    (fun e : squareBoundary S => tail e) (fun e : squareBoundary S => head e) (by intro v; simpa only [Fintype.card_eq_nat_card] using hb v) ⟨e₀,he₀⟩
  refine ⟨n,hn,(fun i => (e i).1),congrArg Subtype.val h0,congrArg Subtype.val hn0,
    fun i => (e i).2,hchain,?_⟩
  intro i hi j hj he
  exact hinj hi hj (Subtype.ext he)

lemma west_root_edge_mem (S : Set Grid) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) : ((0,1),3)∈squareBoundary S := by
  constructor
  · simpa [leftSite,leftOffset] using hroot
  · have hbad : (-1,0)∉S := by
      intro h
      have ht := (hquad _ h).1
      norm_num at ht
    simpa [rightSite,rightOffset] using hbad

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContourSites
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

lemma forward_step (d : Dir) : (step d).1-(step d).2=
    if forwardDir d then (-1 : ℤ) else 1 := by
  fin_cases d <;> norm_num [step,forwardDir,Fin.ext_iff]

lemma twice_forward_card (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0) :
    2*(forwardIndices e n).card=n := by
  have hv (i : ℕ) : (e (i+1)).1=(e i).1+step (e i).2 := (hchain i).symm
  have hd (i : ℕ) :
      ((e (i+1)).1.1-(e (i+1)).1.2)-((e i).1.1-(e i).1.2)=
      if forwardDir (e i).2 then (-1 : ℤ) else 1 := by
    rw [hv]
    simpa only [Prod.fst_add,Prod.snd_add] using (by
      rw [← forward_step]
      ring : ((e i).1.1+(step (e i).2).1-((e i).1.2+(step (e i).2).2))-
        ((e i).1.1-(e i).1.2)=if forwardDir (e i).2 then (-1 : ℤ) else 1)
  have hz : (∑ i∈Finset.range n, (if forwardDir (e i).2 then (-1 : ℤ) else 1))=0 := by
    simp_rw [← hd]
    rw [Finset.sum_range_sub (fun i => (e i).1.1-(e i).1.2),hclose,sub_self]
  have hf : ∑ i∈Finset.range n, (if forwardDir (e i).2 then (1 : ℤ) else 0)=
      ((forwardIndices e n).card : ℤ) := by
    simp [forwardIndices,Finset.sum_boole]
  have he (i : ℕ) : (if forwardDir (e i).2 then (-1 : ℤ) else 1)=
      1-2*(if forwardDir (e i).2 then (1 : ℤ) else 0) := by split <;> norm_num
  simp_rw [he] at hz
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hf] at hz
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hz
  omega

lemma rightSite_direction_injective :
    Function.Injective (fun e : Edge => (rightSite e,e.2)) := by
  rintro ⟨p,d⟩ ⟨q,c⟩ h
  have hd : d=c := congrArg Prod.snd h
  subst c
  have hp : p=q := add_right_cancel (congrArg Prod.fst h)
  exact Prod.ext hp rfl

lemma forward_card_le_twice_outside (e : ℕ → Edge) (n : ℕ)
    (hinj : Set.InjOn e (Set.Iio n)) :
    (forwardIndices e n).card≤2*(outsideSites e n).card := by
  have hb := Finset.card_le_card_of_injOn
    (s := forwardIndices e n) (t := outsideSites e n ×ˢ ({1,2} : Finset Dir))
    (f := fun i => (rightSite (e i),(e i).2))
    (by
      intro i hi
      refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
      simpa only [forwardDir,Finset.mem_insert,Finset.mem_singleton] using (Finset.mem_filter.mp hi).2)
    (by
      intro i hi j hj he
      exact hinj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) (rightSite_direction_injective he))
  have hc : ({1,2} : Finset Dir).card=2 := by decide
  rw [Finset.card_product,hc] at hb
  omega

theorem length_le_four_outside (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) : n≤4*(outsideSites e n).card := by
  have h := twice_forward_card e n hchain hclose
  have h' := forward_card_le_twice_outside e n hinj
  omega

lemma forward_child (e : Edge) (hdir : forwardDir e.2) :
    rightSite e=leftSite e+(1,0) ∨ rightSite e=leftSite e+(0,1) := by
  rcases e with ⟨⟨x,y⟩,d⟩
  rcases hdir with h|h
  · change d=1 at h
    subst d
    left
    simp [rightSite,leftSite,rightOffset,leftOffset]
  · change d=2 at h
    subst d
    right
    simp [rightSite,leftSite,rightOffset,leftOffset]

lemma outsideSites_failed_children (S : Set Grid) (e : ℕ → Edge) (n : ℕ)
    (hmem : ∀ i, e i∈squareBoundary S) :
    ∀ z∈outsideSites e n, z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(hmem i).2,leftSite (e i),(hmem i).1,
    forward_child (e i) (Finset.mem_filter.mp hi).2⟩

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContourWords
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical BigOperators

namespace CriticalPercolation.Boundary

lemma wordEdge_chain {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) :
    head (wordEdge p w i)=tail (wordEdge p w (i+1)) := by
  simp [wordEdge,head,tail,Finset.sum_range_succ,add_assoc]

lemma wordEdge_zero {n : ℕ} (p : Grid) (w : Fin n → Dir) :
    (wordEdge p w 0).1=p := by simp [wordEdge]

lemma wordEdge_reconstruct {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0) :
    ∀ i≤n, wordEdge (e 0).1 (fun j : Fin n => (e j).2) i=e i := by
  let w : Fin n → Dir := fun j => (e j).2
  have hd (i : ℕ) (hi : i<n) : wordDir w i=(e i).2 := by simp [wordDir,hi,w]
  have hv : ∀ i≤n, (wordEdge (e 0).1 w i).1=(e i).1 := by
    intro i hi
    induction i with
    | zero => exact wordEdge_zero _ _
    | succ i ih =>
      have hh : i<n := by omega
      have ih' := ih (by omega)
      have hc := wordEdge_chain (e 0).1 w i
      change (wordEdge (e 0).1 w i).1+step (wordDir w i)=
        (wordEdge (e 0).1 w (i+1)).1 at hc
      rw [← hc,ih',hd i hh]
      exact hchain i
  intro i hi
  apply Prod.ext (hv i hi)
  change wordDir w i=(e i).2
  by_cases hlt : i<n
  · exact hd i hlt
  · have hie : i=n := by omega
    subst i
    simp [wordDir,hn,hclose,w]

lemma card_words (n : ℕ) : Fintype.card (Fin n → Dir)=4^n := by
  simp [Dir]

lemma wordValid_reconstruct {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) :
    wordValid (e 0).1 (fun j : Fin n => (e j).2) := by
  have hr := wordEdge_reconstruct hn e hchain hclose
  refine ⟨?_,?_⟩
  · rw [hr n le_rfl,hr 0 (Nat.zero_le n),hclose]
  · intro i hi j hj he
    rw [hr i hi.le,hr j hj.le] at he
    exact hinj hi hj he

lemma outsideSites_congr {n : ℕ} {e f : ℕ → Edge}
    (h : ∀ i<n, e i=f i) : outsideSites e n=outsideSites f n := by
  have hf : forwardIndices e n=forwardIndices f n := by
    apply Finset.filter_congr
    intro i hi
    rw [h i (Finset.mem_range.mp hi)]
  unfold outsideSites
  rw [hf]
  apply Finset.image_congr
  intro i hi
  dsimp only
  rw [h i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]

theorem finite_good_contour (S : Set Grid) (hS : S.Finite) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) :
    ∃ n : ℕ, ∃ w : Fin (n+1) → Dir,
      wordValid (0,1) w ∧
      (∀ z∈outsideSites (wordEdge (0,1) w) (n+1),
        z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1)) := by
  obtain ⟨l,hl,e,h0,hend,hmem,hchain,hinj⟩ := squareBoundary_closed_trail hS
    ((0,1),3) (west_root_edge_mem S hroot hquad)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  have he : e (n+1)=e 0 := hend.trans h0.symm
  have hp : (e 0).1=(0,1) := congrArg Prod.fst h0
  refine ⟨n,(fun j : Fin (n+1) => (e j).2),?_,?_⟩
  · simpa only [hp] using wordValid_reconstruct hl e hchain he hinj
  · have hr := wordEdge_reconstruct hl e hchain he
    rw [hp] at hr
    rw [outsideSites_congr (fun i hi => hr i hi.le)]
    exact outsideSites_failed_children S e (n+1) hmem

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ContourProbability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

lemma measureReal_countable_union_bound {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω) (b : I → ℝ)
    (hb : ∀ i, 0≤b i) (hs : Summable b) (hA : ∀ i, μ.real (A i)≤b i) :
    μ.real (⋃ i, A i)≤∑' i, b i := by
  have hh (i : I) : μ (A i)≤ENNReal.ofReal (b i) := by
    calc μ (A i)=ENNReal.ofReal (μ.real (A i)) := by simp [Measure.real]
         _ ≤ ENNReal.ofReal (b i) := ENNReal.ofReal_le_ofReal (hA i)
  have h := (measure_iUnion_le A).trans (ENNReal.tsum_le_tsum hh)
  rw [← ENNReal.ofReal_tsum_of_nonneg hb hs] at h
  have ht := ENNReal.toReal_mono (by finiteness) h
  simpa only [Measure.real,ENNReal.toReal_ofReal (tsum_nonneg hb)] using ht

namespace Boundary

lemma wordFailure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω) (F : Grid → Set Ω)
    (q : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card)
    (n : ℕ) (w : Fin n → Dir) : μ.real (wordFailure B F w)≤μ.real B*q^n := by
  by_cases hw : wordValid (0,1) w
  · rw [wordFailure,ite_eq_left hw]
    apply (hfail _).trans
    apply mul_le_mul_of_nonneg_left _ (measureReal_nonneg)
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hq₀ hq₁
      (length_le_four_outside _ _ (wordEdge_chain (0,1) w) hw.1 hw.2)
  · rw [wordFailure,ite_eq_right hw]
    simp only [measureReal_empty]
    positivity

theorem finite_good_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω)
    (S : Ω → Set Grid) (F : Grid → Set Ω)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, 0≤v.1 ∧ 0≤v.2)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F z)
    (q : ℝ) (hq₀ : 0≤q) (hq : 4*q<1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card) :
    μ.real (B∩{ω | (S ω).Finite})≤μ.real B*(4*q)/(1-4*q) := by
  have hsub : B∩{ω | (S ω).Finite}⊆
      ⋃ n : ℕ, ⋃ w : Fin (n+1) → Dir, wordFailure B F w := by
    intro ω hω
    obtain ⟨n,w,hw,hz⟩ := finite_good_contour (S ω) hω.2 (hroot ω hω.1) (hquad ω hω.1)
    refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨w,?_⟩⟩
    rw [wordFailure,ite_eq_left hw]
    refine ⟨hω.1,Set.mem_iInter.mpr fun z => Set.mem_iInter.mpr fun hs => ?_⟩
    exact hchild ω hω.1 z (hz z hs).1 (hz z hs).2
  have hq₁ : q≤1 := by linarith
  have hterm (n : ℕ) :
      μ.real (⋃ w : Fin (n+1) → Dir, wordFailure B F w)≤μ.real B*(4*q)^(n+1) := by
    apply (measureReal_iUnion_fintype_le _).trans
    calc
      (∑ w : Fin (n+1) → Dir, μ.real (wordFailure B F w))≤
          ∑ _w : Fin (n+1) → Dir, μ.real B*q^(n+1) :=
        Finset.sum_le_sum (fun w _ => wordFailure_bound μ B F q hq₀ hq₁ hfail (n+1) w)
      _ = μ.real B*(4*q)^(n+1) := by
        simp only [Finset.sum_const,Finset.card_univ,card_words,nsmul_eq_mul,
          Nat.cast_pow,Nat.cast_ofNat,mul_pow]
        ring
  have hs₀ : Summable (fun n : ℕ => (4*q)^n) :=
    summable_geometric_of_lt_one (by positivity) hq
  have hs : Summable (fun n : ℕ => μ.real B*(4*q)^(n+1)) :=
    ((summable_nat_add_iff 1).mpr hs₀).mul_left _
  have hu := measureReal_countable_union_bound μ
    (fun n => ⋃ w : Fin (n+1) → Dir, wordFailure B F w)
    (fun n => μ.real B*(4*q)^(n+1)) (fun _ => by positivity) hs hterm
  apply ((measureReal_mono hsub).trans hu).trans_eq
  simp_rw [pow_succ]
  rw [tsum_mul_left,tsum_mul_right,tsum_geometric_of_lt_one (by positivity) hq]
  ring

theorem infinite_good_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω)
    (S : Ω → Set Grid) (F : Grid → Set Ω)
    (hB : 0<μ.real B)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, 0≤v.1 ∧ 0≤v.2)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F z)
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card) :
    0<μ.real (B∩{ω | (S ω).Infinite}) := by
  have hh : 4*q<1 := by linarith
  have hf := finite_good_probability_bound μ B S F hroot hquad hchild q hq₀ hh hfail
  have hratio : μ.real B*(4*q)/(1-4*q)<μ.real B := by
    apply (div_lt_iff₀ (by linarith : 0<1-4*q)).mpr
    nlinarith [mul_pos hB (by linarith : 0<1-8*q)]
  have he : B=(B∩{ω | (S ω).Finite})∪(B∩{ω | (S ω).Infinite}) := by
    ext ω
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.Infinite]
    tauto
  have hu := measureReal_union_le (μ := μ)
    (B∩{ω | (S ω).Finite}) (B∩{ω | (S ω).Infinite})
  rw [← he] at hu
  linarith

end Boundary
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SlotContour
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.Boundary

lemma gridSlot_injective : Set.InjOn gridSlot {v | quadrant v} := by
  intro v hv w hw he
  have hh := Nat.pairEquiv.injective (show Nat.pairEquiv (v.1.toNat,v.2.toNat)=
    Nat.pairEquiv (w.1.toNat,w.2.toNat) from he)
  change (v.1.toNat,v.2.toNat)=(w.1.toNat,w.2.toNat) at hh
  have hx := congrArg Prod.fst hh
  have hy := congrArg Prod.snd hh
  apply Prod.ext <;> dsimp only [quadrant,Set.mem_ofPred_eq] at hv hw <;> omega

lemma gridSlot_east (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(1,0)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+1).toNat (v.2+0).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_left _ (by dsimp [quadrant] at hv; omega)

lemma gridSlot_north (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(0,1)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+0).toNat (v.2+1).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_right _ (by dsimp [quadrant] at hv; omega)

lemma specified_grid_failures {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set Ω) (hB : MeasurableSet[M 0] B)
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B → μ.real (A∩F n)≤ε*μ.real A)
    (s : Finset Grid) : μ.real (B∩⋂ z∈s, gridFailure F z)≤μ.real B*ε^s.card := by
  by_cases hs : ∀ z∈s, quadrant z
  · have he : (⋂ z∈s, gridFailure F z)=⋂ n∈s.image gridSlot, F n := by
      ext ω
      constructor
      · intro h
        refine Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h z) hz
        simpa only [gridFailure,ite_eq_left (hs z hz)] using hh
      · intro h
        refine Set.mem_iInter.mpr fun z => Set.mem_iInter.mpr fun hz => ?_
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h (gridSlot z))
          (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
        simpa only [gridFailure,ite_eq_left (hs z hz)] using hh
    rw [he]
    have hc : (s.image gridSlot).card=s.card := Finset.card_image_iff.mpr (by
      intro z hz w hw he
      exact gridSlot_injective (hs z hz) (hs w hw) he)
    have h := specified_failures_with_initialization μ M hM F hF B hB ε hε hcond
      (s.image gridSlot)
    rwa [hc] at h
  · push Not at hs
    obtain ⟨z,hz,hq⟩ := hs
    have he : (⋂ z∈s, gridFailure F z)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h z) hz
      simp only [gridFailure,ite_eq_right hq,Set.mem_empty_iff_false] at hh
    rw [he,Set.inter_empty,measureReal_empty]
    positivity

theorem infinitely_many_good_from_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set Ω) (hmB : MeasurableSet[M 0] B) (hB : 0<μ.real B)
    (S : Ω → Set Grid)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, quadrant v)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F (gridSlot z))
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B →
      μ.real (A∩F n)≤q^4*μ.real A) :
    0<μ.real (B∩{ω | (S ω).Infinite}) := by
  apply infinite_good_positive μ B S (gridFailure F) hB hroot hquad ?_ q hq₀ hq
    (specified_grid_failures μ M hM F hF B hmB (q^4) (by positivity) hcond)
  intro ω hω z hz hc
  have hqz : quadrant z := by
    obtain ⟨y,hy,he|he⟩ := hc
    · rw [he]
      have h := hquad ω hω y hy
      change 0≤y.1+1 ∧ 0≤y.2+0
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
    · rw [he]
      have h := hquad ω hω y hy
      change 0≤y.1+0 ∧ 0≤y.2+1
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
  simpa only [gridFailure,ite_eq_left hqz] using hchild ω hω z hz hc

end CriticalPercolation.Boundary
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_LatticeGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open Boundary

lemma slotSite_quadrant (n : ℕ) : quadrant (slotSite n) := by
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩

lemma gridSlot_slotSite (n : ℕ) : gridSlot (slotSite n)=n := by
  simp [gridSlot,slotSite]

lemma slotSite_gridSlot (v : Site) (hv : quadrant v) : slotSite (gridSlot v)=v := by
  apply gridSlot_injective (slotSite_quadrant _) hv
  exact gridSlot_slotSite _

lemma parent_slot_lt (e : Edge) (h : quadrant (source e)) :
    gridSlot (source e)<gridSlot (target e) := by
  obtain ⟨v,b⟩ := e
  cases b with
  | true => exact gridSlot_east v h
  | false => exact gridSlot_north v h

lemma target_quadrant (e : Edge) (h : quadrant (source e)) : quadrant (target e) := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  change 0≤a ∧ 0≤b at h
  cases s <;> dsimp [target,quadrant] <;> omega

lemma incoming_source {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : source e∈S := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    exact hw
  · have he := Option.some.inj h
    subst e
    exact hn

lemma incoming_target {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : target e=slotSite n := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    simp [target]
  · have he := Option.some.inj h
    subst e
    simp [target]

lemma incoming_exists (n : ℕ) (S : Finset Site)
    (h : ∃ y∈S, slotSite n=y+(1,0) ∨ slotSite n=y+(0,1)) :
    ∃ e, incoming n S=some e := by
  unfold incoming
  split_ifs with hw hn
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · obtain ⟨y,hy,he|he⟩ := h
    · exact (hw (by rwa [he,add_sub_cancel_right])).elim
    · exact (hn (by rwa [he,add_sub_cancel_right])).elim

lemma GrowthState.good_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.good⊆(S.advance n b).good := by
  dsimp [advance]
  split_ifs <;> intro v hv
  · exact Finset.mem_insert_of_mem hv
  · exact hv

lemma GrowthState.initial_valid : GrowthState.initial.Valid 0 := by
  refine ⟨by simp [initial],?_,by simp [initial]⟩
  intro v hv
  have he : v=(0,0) := by simpa [initial] using hv
  subst v
  exact ⟨by norm_num [quadrant],Or.inl rfl⟩

lemma GrowthState.advance_valid (n : ℕ) (S : GrowthState) (b : Bool)
    (h : S.Valid n) : (S.advance n b).Valid (n+1) := by
  refine ⟨S.good_mono n b h.1,?_,?_⟩
  · intro v hv
    change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨slotSite_quadrant n,Or.inr (by rw [gridSlot_slotSite]; omega)⟩
      · exact ⟨(h.2.1 v hv).1,(h.2.1 v hv).2.imp_right (fun hh => by omega)⟩
    · exact ⟨(h.2.1 v hv).1,(h.2.1 v hv).2.imp_right (fun hh => by omega)⟩
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact ⟨S.good_mono n b (h.2.2 e he).1,by have hh := (h.2.2 e he).2; omega⟩
    · have hei : incoming n S.good=some e := by simpa using he
      exact ⟨S.good_mono n b (incoming_source hei),by rw [incoming_target hei,gridSlot_slotSite]; omega⟩

lemma GrowthState.seen_intersection (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (ht : n ≤ gridSlot (target e)) :
    e∉S.seen ∧ ∀ f∈S.seen, endpoints f∩endpoints e⊆{source e} := by
  refine ⟨fun hei => (Nat.not_lt_of_ge ht) (h.2.2 e hei).2,?_⟩
  intro f hf v hv
  have hfs := (h.2.1 (source f) (h.2.2 f hf).1).1
  have hft := (h.2.2 f hf).2
  have hfst := parent_slot_lt f hfs
  rcases hv.1 with rfl|hvf <;> rcases hv.2 with hve|hve
  · exact hve
  · have heq : source f=target e := hve
    rw [heq] at hfst
    omega
  · exact hve
  · have heq : target f=target e := hvf.symm.trans hve
    rw [heq] at hft
    omega

lemma GrowthState.initial_covered : GrowthState.initial.Covered := by
  intro v hv
  exact Or.inl (by simpa [initial] using hv)

lemma GrowthState.advance_covered (n : ℕ) (S : GrowthState) (b : Bool)
    (h : S.Covered) : (S.advance n b).Covered := by
  intro v hv
  change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
  have hold : ∀ v∈S.good, v=(0,0) ∨ ∃ e∈(S.advance n b).seen, target e=v := by
    intro v hv
    rcases h v hv with hv|⟨e,he,hv⟩
    · exact Or.inl hv
    · exact Or.inr ⟨e,S.seen_mono n b he,hv⟩
  split_ifs at hv with ha
  · rcases Finset.mem_insert.mp hv with rfl|hv
    · obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha.1
      exact Or.inr ⟨e,Finset.mem_union.mpr (Or.inr (by simp [he])),incoming_target he⟩
    · exact hold v hv
  · exact hold v hv

lemma GrowthState.outgoing_nonincident (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (he : source e=slotSite n) {f : Edge} (hf : f∈S.seen) :
    Disjoint (endpoints f) (endpoints e) := by
  have hq := (h.2.1 _ (h.2.2 f hf).1).1
  have hf1 := parent_slot_lt f hq
  have hf2 := (h.2.2 f hf).2
  have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
  have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv|hv <;> rcases hw with hw|hw
  · have hh : source f=source e := hv.symm.trans hw
    rw [hh,he2] at hf1
    omega
  · have hh : source f=target e := hv.symm.trans hw
    rw [hh] at hf1
    omega
  · have hh : target f=source e := hv.symm.trans hw
    rw [hh,he2] at hf2
    omega
  · have hh : target f=target e := hv.symm.trans hw
    rw [hh] at hf2
    omega

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_GrowthHistoryGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph Boundary

variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)

lemma boxEdges_subset_corridor_target (e : Edge) :
    boxEdges G ξ j h (target e)⊆corridorEdges G ξ j h e := by
  intro b hb v hv
  exact Or.inl (Or.inr (hb v hv))

lemma good_box_revealed {S : GrowthState} (hs : S.Covered) {v : Site} (hv : v∈S.good) :
    boxEdges G ξ j h v⊆revealed G ξ j h S := by
  rcases hs v hv with rfl|⟨e,he,rfl⟩
  · exact Set.subset_union_left
  · intro b hb
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,boxEdges_subset_corridor_target G ξ j h e hb⟩)

lemma revealed_advance (n : ℕ) (S : GrowthState) (b : Bool) :
    revealed G ξ j h (S.advance n b)=revealed G ξ j h S∪
      ⋃ e∈(incoming n S.good).toFinset, corridorEdges G ξ j h e := by
  ext e
  constructor
  · rintro (he|he)
    · exact Or.inl (Or.inl he)
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      rcases Finset.mem_union.mp hf with hf|hf
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,he⟩))
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,he⟩)
  · rintro ((he|he)|he)
    · exact Or.inl he
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,Finset.mem_union.mpr (Or.inl hf),he⟩)
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,Finset.mem_union.mpr (Or.inr hf),he⟩)

lemma revealed_incoming (n : ℕ) (S : GrowthState) (b : Bool) {e : Edge}
    (he : incoming n S.good=some e) :
    revealed G ξ j h (S.advance n b)=revealed G ξ j h S∪corridorEdges G ξ j h e := by
  rw [revealed_advance,he]
  simp

lemma later_revealed_intersection (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S T : GrowthState) (hc : S.Covered) (hv : T.Valid n)
    {e : Edge} (hp : source e∈S.good) (ht : n ≤ gridSlot (target e)) :
    revealed G ξ j h T∩corridorEdges G ξ j h e⊆revealed G ξ j h S := by
  intro b hb
  rcases hb.1 with hb0|hbT
  · exact Or.inl hb0
  · have hh' := T.seen_intersection n hv ht
    have hh'' := history_intersection_subset G ξ j h hh hhj hsep (↑T.seen) hh'.1 hh'.2
    exact good_box_revealed G ξ j h hc hp (hh'' ⟨hbT,hb.2⟩)

lemma outgoing_unrevealed (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (hn : 0<n)
    {e : Edge} (he : source e=slotSite n) :
    Disjoint (revealed G ξ j h S) (corridorEdges G ξ j h e) := by
  apply Disjoint.sup_left
  · apply edge_box_disjoint G ξ j h hh hhj hsep
    intro hroot
    have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
    have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
    rcases hroot with hh|hh
    · have he0 : gridSlot (source e)=0 := by rw [← hh]; rfl
      omega
    · have he0 : gridSlot (target e)=0 := by rw [← hh]; rfl
      omega
  · exact history_disjoint G ξ j h hh hhj hsep (↑S.seen)
      (fun f hf => S.outgoing_nonincident n hv he hf)

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_PinnedTest
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma blockProbability_eq_pinnedLaw (q : E → unitInterval) (I σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    blockProbability q I A σ=law (pinnedParameters q I σ) A := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn I σ) hA]
  rfl

theorem pinned_prediction_failure (q : E → unitInterval) (I F σ : Set E)
    (hIF : I⊆F) (A C D : Set (Set E))
    (hA : MeasurableSet[blockSigma F] A) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ)
    (hin : 1-δ ≤ (blockProbability q I A σ).toReal)
    (hCfail : (blockProbability q I (A\C) σ).toReal ≤ a)
    (hDfail : (blockProbability q I (A\D) σ).toReal ≤ a) :
    (blockProbability q I (predictionFailure q F A C D δ) σ).toReal ≤ δ+2*a/δ := by
  have hma := (blockSigma_le F) _ hA
  rw [blockProbability_eq_pinnedLaw q I σ A hma] at hin
  rw [blockProbability_eq_pinnedLaw q I σ (A\C) (hma.diff hC)] at hCfail
  rw [blockProbability_eq_pinnedLaw q I σ (A\D) (hma.diff hD)] at hDfail
  have hh := two_prediction_failure (pinnedParameters q I σ) F A C D hA hC hD δ a hδ
    hin hCfail hDfail
  simp_rw [blockProbability_pin_smaller q I F σ hIF C hC,
    blockProbability_pin_smaller q I F σ hIF D hD] at hh
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((blockSigma_le F) _ (measurableSet_predictionFailure q F A C D hA hC hD δ))]
  exact hh

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_GrowthProcess
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

namespace Scheme
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

omit [Countable V] [Countable E] in
lemma accepted_iff (n : ℕ) (S : GrowthState) (ω : Set E) :
    ω∈P.accepted n S ↔ ω∈P.incomingHit n S ∧
      ∀ b : Bool, 1-P.delta ≤ (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S b) ω).toReal := by
  change (¬((ω∉P.incomingHit n S ∨ ω∈P.incomingHit n S ∧
    (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S true) ω).toReal<1-P.delta) ∨
    ω∈P.incomingHit n S ∧
    (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S false) ω).toReal<1-P.delta)) ↔ _
  constructor
  · intro h
    have ha : ω∈P.incomingHit n S := Classical.byContradiction (fun hn => h (Or.inl (Or.inl hn)))
    refine ⟨ha,fun b => ?_⟩
    cases b
    · exact not_lt.mp (fun hb => h (Or.inr ⟨ha,hb⟩))
    · exact not_lt.mp (fun hb => h (Or.inl (Or.inr ⟨ha,hb⟩)))
  · rintro ⟨ha,hb⟩ (h|h)
    · rcases h with h|h
      · exact h ha
      · exact not_lt_of_ge (hb true) h.2
    · exact not_lt_of_ge (hb false) h.2

lemma state_valid (n : ℕ) (w : DecisionCode n) : (P.rule.state n w).Valid n := by
  induction n with
  | zero => exact GrowthState.initial_valid
  | succ n ih => exact GrowthState.advance_valid n _ w.2 (ih w.1)

lemma state_covered (n : ℕ) (w : DecisionCode n) : (P.rule.state n w).Covered := by
  induction n with
  | zero => exact GrowthState.initial_covered
  | succ n ih => exact GrowthState.advance_covered n _ w.2 (ih w.1)

omit [Countable V] [Countable E] in
lemma block_enlarged (n : ℕ) (S : GrowthState) : P.block S⊆P.enlarged n S :=
  revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)

omit [Countable V] [Countable E] in
lemma enlarged_incoming (n : ℕ) (S : GrowthState) {e : Edge} (he : incoming n S.good=some e) :
    P.enlarged n S=P.block S∪P.edgeDomain e :=
  revealed_incoming P.graph P.coordinate P.j P.h n S false he

lemma rootEvent_measurable : MeasurableSet[blockSigma (P.block GrowthState.initial)] P.rootEvent := by
  simp only [rootEvent,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro b
  exact measurableSet_le measurable_const
    (measurable_blockProbability P.parameter _ _ (P.graph.restrictedSeed_measurable _ _ _)).ennreal_toReal

lemma rootEvent_history : MeasurableSet[(P.rule.partition 0).historySigma] P.rootEvent := by
  intro w
  change MeasurableSet[blockSigma (P.block GrowthState.initial)] (P.rootEvent∩Set.univ)
  simpa only [Set.inter_univ] using P.rootEvent_measurable

end Scheme
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_StoredPrediction
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

omit [Countable V] [Countable E] in
lemma stable_initial (hroot : (P.seed∩P.mark (0,0)).Nonempty)
    {ω : Set E} (hω : ω∈P.rootEvent) : P.Stable 0 GrowthState.initial ω := by
  constructor
  · intro v hv
    have he : v=(0,0) := by simpa [GrowthState.initial] using hv
    subst v
    change ω∈P.graph.restrictedSeed P.seed (P.mark (0,0)) _
    rw [P.graph.restrictedSeed_self _ _ hroot]
    trivial
  · intro e he _hn
    obtain ⟨v,b⟩ := e
    have hv : v=(0,0) := by simpa [GrowthState.initial,source] using he
    subst v
    exact hω b

lemma stable_advance (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (n : ℕ) (S : GrowthState) (b : Bool) (ω : Set E)
    (hv : S.Valid n) (hc : S.Covered) (hs : P.Stable n S ω)
    (ha : b=true → ω∈P.accepted n S) : P.Stable (n+1) (S.advance n b) ω := by
  have hold_hit : ∀ v∈S.good, ω∈P.hit v (P.block (S.advance n b)) := by
    intro v hv
    exact P.graph.restrictedSeed_mono _ _ (P.block_enlarged n S) (hs.1 v hv)
  have hold_pred : ∀ e : Edge, source e∈S.good → n+1 ≤ gridSlot (target e) →
      1-P.delta ≤ (blockProbability P.parameter (P.block (S.advance n b))
        (P.hit (target e) (P.block (S.advance n b)∪P.edgeDomain e)) ω).toReal := by
    intro e hp ht
    have hI := later_revealed_intersection P.graph P.coordinate P.j P.h hh hhj hsep
      (n+1) S (S.advance n b) hc (S.advance_valid n b hv) hp ht
    have hprob := P.graph.seed_prediction_persists P.parameter P.seed (P.mark (target e))
      (P.block S) (P.block (S.advance n b)) (P.edgeDomain e) ω (P.block_enlarged n S) hI
    exact (hs.2 e hp (by omega)).trans
      (ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt (blockProbability_le_one _ _ _ _) ENNReal.one_lt_top)) hprob)
  constructor
  · intro v hv
    change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
    split_ifs at hv with hb
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (P.accepted_iff n S ω).mp (ha hb.2) |>.1
      · exact hold_hit v hv
    · exact hold_hit v hv
  · intro e hp ht
    change source e∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hp
    split_ifs at hp with hb
    · rcases Finset.mem_insert.mp hp with he|hp
      · have he' : e=(slotSite n,e.2) := Prod.ext he rfl
        rw [he']
        exact (P.accepted_iff n S ω).mp (ha hb.2) |>.2 e.2
      · exact hold_pred e hp ht
    · exact hold_pred e hp ht

theorem stable_on_cell (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) (n : ℕ) (w : DecisionCode n)
    (ω : Set E) (hc : ω∈(P.rule.partition n).cell w) (hB : ω∈P.rootEvent) :
    P.Stable n (P.rule.state n w) ω := by
  induction n with
  | zero => exact P.stable_initial hroot hB
  | succ n ih =>
    rcases w with ⟨w,b⟩
    rw [P.rule.partition_cell_succ] at hc
    apply P.stable_advance hh hhj hsep n (P.rule.state n w) b ω
      (P.state_valid n w) (P.state_covered n w) (ih w hc.1)
    intro hb
    have hdecision := hc.2
    rw [hb] at hdecision
    change (if ω∈P.accepted n (P.rule.state n w) then true else false)=true at hdecision
    by_contra hn
    simp only [ite_eq_right hn,Bool.false_eq_true] at hdecision

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ActualGrowth
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

lemma actual_succ (n : ℕ) (ω : Set E) :
    P.actual (n+1) ω=(P.actual n ω).advance n
      (if ω∈P.accepted n (P.actual n ω) then true else false) := rfl

lemma actual_good_mono (ω : Set E) : Monotone (fun n => ((P.actual n ω).good : Set Site)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [P.actual_succ]
  exact GrowthState.good_mono _ _ _

lemma actual_root (n : ℕ) (ω : Set E) : (0,0)∈(P.actual n ω).good :=
  P.state_valid n (P.rule.codeOf n ω) |>.1

lemma allGood_root (ω : Set E) : (0,0)∈P.allGood ω := Set.mem_iUnion.mpr ⟨0,P.actual_root 0 ω⟩

lemma allGood_quadrant (ω : Set E) {v : Site} (hv : v∈P.allGood ω) : quadrant v := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
  exact P.state_valid n (P.rule.codeOf n ω) |>.2.1 v hn |>.1

lemma actual_good_birth (n : ℕ) (ω : Set E) {v : Site} (hv : v∈(P.actual n ω).good) :
    v=(0,0) ∨ ∃ k, v=slotSite k ∧ v∈(P.actual (k+1) ω).good := by
  induction n with
  | zero => exact Or.inl (by simpa [actual,DecisionRule.state,rule,GrowthState.initial] using hv)
  | succ n ih =>
    have hvo := hv
    rw [P.actual_succ] at hv
    change v∈(if (incoming n (P.actual n ω).good).isSome ∧
      (if ω∈P.accepted n (P.actual n ω) then true else false)=true
      then insert (slotSite n) (P.actual n ω).good else (P.actual n ω).good) at hv
    by_cases ha : (incoming n (P.actual n ω).good).isSome ∧
      (if ω∈P.accepted n (P.actual n ω) then true else false)=true
    · rw [ite_eq_left ha] at hv
      rcases Finset.mem_insert.mp hv with hv|hv
      · exact Or.inr ⟨n,hv,hvo⟩
      · exact ih hv
    · rw [ite_eq_right ha] at hv
      exact ih hv

lemma good_parent_present (ω : Set E) {e : Edge} (hp : source e∈P.allGood ω) :
    source e∈(P.actual (gridSlot (target e)) ω).good := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hp
  have hq := (P.state_valid n (P.rule.codeOf n ω)).2.1 _ hn |>.1
  have hlt := parent_slot_lt e hq
  rcases P.actual_good_birth n ω hn with he|⟨k,he,hg⟩
  · rw [he]
    exact P.actual_root _ _
  · have hsk : gridSlot (source e)=k := by rw [he,gridSlot_slotSite]
    exact P.actual_good_mono ω (show k+1 ≤ gridSlot (target e) by omega) hg

lemma missing_child_fails (ω : Set E) (z : Site) (hz : z∉P.allGood ω)
    (hc : ∃ y∈P.allGood ω, z=y+(1,0) ∨ z=y+(0,1)) :
    ω∈P.rule.failure (gridSlot z) := by
  obtain ⟨y,hy,hz'⟩ := hc
  let e : Edge := (y,if z=y+(1,0) then true else false)
  have he : target e=z := by
    by_cases hh : z=y+(1,0)
    · simp [e,target,hh]
    · rcases hz' with hz'|hz'
      · exact (hh hz').elim
      · simp [e,target,hz']
  have hp : source e∈P.allGood ω := hy
  have hyp := P.good_parent_present ω hp
  rw [he] at hyp
  have hqz := target_quadrant e (P.allGood_quadrant ω hp)
  rw [he] at hqz
  have hs : slotSite (gridSlot z)=z := slotSite_gridSlot z hqz
  have hex : ∃ f, incoming (gridSlot z) (P.actual (gridSlot z) ω).good=some f := by
    apply incoming_exists
    refine ⟨y,hyp,?_⟩
    rwa [hs]
  obtain ⟨f,hf⟩ := hex
  apply (P.rule.failure_on_cell (gridSlot z) (P.rule.codeOf_mem _ ω)).mpr
  constructor
  · change (incoming (gridSlot z) (P.actual (gridSlot z) ω).good).isSome
    simp [hf]
  · change ω∉P.accepted (gridSlot z) (P.actual (gridSlot z) ω)
    intro ha
    apply hz
    apply Set.mem_iUnion.mpr
    refine ⟨gridSlot z+1,?_⟩
    rw [P.actual_succ]
    change z∈(if (incoming (gridSlot z) (P.actual (gridSlot z) ω).good).isSome ∧
      (if ω∈P.accepted (gridSlot z) (P.actual (gridSlot z) ω) then true else false)=true
      then insert (slotSite (gridSlot z)) (P.actual (gridSlot z) ω).good else (P.actual (gridSlot z) ω).good)
    simp [hf,ha,hs]

lemma allGood_reached (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) {ω : Set E} (hB : ω∈P.rootEvent)
    {v : Site} (hv : v∈P.allGood ω) : ω∈P.graph.seedHitEvent P.seed (P.mark v) := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
  have hs := P.stable_on_cell hh hhj hsep hroot n (P.rule.codeOf n ω) ω (P.rule.codeOf_mem n ω) hB
  have hr := hs.1 v hn
  exact P.graph.seedHitEvent_upper _ _ (Set.inter_subset_left) hr

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_MarkConnectivity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation

theorem infinite_cluster_of_reached_marks {V I : Type*} (H : SimpleGraph V)
    (seed : Finset V) (J : Set I) (hJ : J.Infinite) (mark : I → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ i∈J, ∃ v∈mark i, ∃ a∈seed, H.Reachable a v) :
    ∃ a∈seed, ({v | H.Reachable a v} : Set V).Infinite := by
  let := hJ.to_subtype
  have hex (i : J) : ∃ v∈mark i, ∃ a∈seed, H.Reachable a v := hreach i i.2
  choose v hv using hex
  have hinj : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) (hv i).1 (hij ▸ (hv j).1)
  have hi : (Set.range v).Infinite := Set.infinite_range_of_injective hinj
  by_contra hn
  push Not at hn
  have hf : (⋃ a∈seed, {v | H.Reachable a v}).Finite :=
    seed.finite_toSet.biUnion (fun a ha => hn a ha)
  apply hi.not_finite (hf.subset ?_)
  rintro _ ⟨i,rfl⟩
  obtain ⟨a,ha,hr⟩ := (hv i).2
  exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,hr⟩⟩

namespace BondGraph
variable {V E I : Type*} (G : BondGraph V E)

lemma percolation_of_infinite_marks (p : unitInterval) (B : Set (Set E))
    (J : Set E → Set I) (seed : Finset V) (mark : I → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ ω∈B, ∀ i∈J ω, ∃ v∈mark i, ∃ a∈seed,
      (G.openGraph ω).Reachable a v)
    (hpos : 0 < (G.law p).real (B∩{ω | (J ω).Infinite})) :
    0<G.law p G.percolates := by
  have hsub : B∩{ω | (J ω).Infinite}⊆G.percolates := by
    intro ω hω
    obtain ⟨a,_ha,hi⟩ := infinite_cluster_of_reached_marks (G.openGraph ω) seed
      (J ω) hω.2 mark hdis (hreach ω hω.1)
    exact ⟨a,hi⟩
  exact (ENNReal.toReal_pos_iff.mp hpos).1.trans_le (measure_mono hsub)

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_GrowthEstimate
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)

lemma local_failure_bound (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) (hδ : 0<P.delta)
    (a : ℝ) (hε : 0≤P.delta+2*a/P.delta)
    (hpros : ∀ n S, S.Valid n → S.Covered → (incoming n S.good).isSome →
      ∀ ω b, (blockProbability P.parameter (P.block S)
        (P.incomingHit n S\P.nextHit n S b) ω).toReal ≤ a)
    (n : ℕ) (w : DecisionCode n) (ω : Set E)
    (hw : ω∈(P.rule.partition n).cell w) (hB : ω∈P.rootEvent) :
    (blockProbability P.parameter (P.rule.block (P.rule.state n w))
      {σ | P.rule.active n (P.rule.state n w) ∧ σ∉P.rule.accept n (P.rule.state n w)} ω).toReal
      ≤ P.delta+2*a/P.delta := by
  let S := P.rule.state n w
  have hs := P.stable_on_cell hh hhj hsep hroot n w ω hw hB
  by_cases ha : (incoming n S.good).isSome
  · obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
    have ht : target e=slotSite n := incoming_target he
    have hh := hs.2 e (incoming_source he) (by rw [ht,gridSlot_slotSite])
    have hin : 1-P.delta ≤ (blockProbability P.parameter (P.block S) (P.incomingHit n S) ω).toReal := by
      simpa only [incomingHit,P.enlarged_incoming n S he,ht] using hh
    have hloc := pinned_prediction_failure P.parameter (P.block S) (P.enlarged n S) ω
      (P.block_enlarged n S) (P.incomingHit n S) (P.nextHit n S true) (P.nextHit n S false)
      (P.graph.measurableSet_restrictedSeed _ _ _)
      (P.graph.restrictedSeed_measurable _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
      P.delta a hδ hin (hpros n S (P.state_valid n w) (P.state_covered n w) ha ω true)
      (hpros n S (P.state_valid n w) (P.state_covered n w) ha ω false)
    have hevent : {σ | P.rule.active n S ∧ σ∉P.rule.accept n S}=
        predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
          (P.nextHit n S true) (P.nextHit n S false) P.delta := by
      ext σ
      change ((incoming n S.good).isSome ∧ ¬¬σ∈_) ↔ _
      simp only [ha,true_and,not_not]
    change (blockProbability P.parameter (P.block S) _ ω).toReal ≤ _
    rw [hevent]
    exact hloc
  · have hevent : {σ | P.rule.active n S ∧ σ∉P.rule.accept n S}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      exact ha hσ.1
    change (blockProbability P.parameter (P.block S) _ ω).toReal ≤ _
    rw [hevent]
    simpa only [blockProbability,Set.preimage_empty,measure_empty,ENNReal.toReal_zero] using hε

theorem exploration_percolates (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (seed : Finset V) (hseed : P.seed=seed) (hroot : (P.seed∩P.mark (0,0)).Nonempty)
    (hmark : Pairwise (Disjoint on P.mark))
    (p : unitInterval) (hp : P.parameter=fun _ => p)
    (hB : 0<(law P.parameter).real P.rootEvent) (hδ : 0<P.delta)
    (a q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1) (ha : 0≤a)
    (herr : P.delta+2*a/P.delta ≤ q^4)
    (hpros : ∀ n S, S.Valid n → S.Covered → (incoming n S.good).isSome →
      ∀ ω b, (blockProbability P.parameter (P.block S)
        (P.incomingHit n S\P.nextHit n S b) ω).toReal ≤ a) :
    0<P.graph.law p P.graph.percolates := by
  have hε : 0≤P.delta+2*a/P.delta := by positivity
  have hlocal := P.local_failure_bound hh hhj hsep hroot hδ a hε hpros
  have hcond := P.rule.conditional_failure_bound P.parameter P.rootEvent _ hε hlocal
  have hi := infinitely_many_good_from_tests (law P.parameter)
    (fun n => (P.rule.partition n).historySigma) P.rule.historySigma_mono P.rule.failure
    P.rule.failure_history_measurable P.rootEvent P.rootEvent_history hB P.allGood
    (fun ω _ => P.allGood_root ω) (fun ω _ v hv => P.allGood_quadrant ω hv)
    (fun ω _ => P.missing_child_fails ω) q hq₀ hq (by
      intro n A hm hAB
      exact (hcond n A hm hAB).trans (mul_le_mul_of_nonneg_right herr (measureReal_nonneg)))
  have hlaw : law P.parameter=P.graph.law p := by rw [hp]; exact BernoulliProduct.law_const p
  rw [hlaw] at hi
  apply P.graph.percolation_of_infinite_marks p P.rootEvent P.allGood seed P.mark hmark _ hi
  intro ω hω v hv
  have hr := P.allGood_reached hh hhj hsep hroot hω hv
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hr
  exact ⟨b,hb,a,by simpa only [hseed,Finset.mem_coe] using ha,hr⟩

end CriticalPercolation.Corridor.Scheme
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayScales
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma relay_coordinate_scale (L R m : ℕ) (e ρ : ℝ) (he : 0<e) (hρ : 0 ≤ ρ)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) :
    ρ ≤ e ∧ (L+1)*e+R*ρ<1 ∧ R*ρ+e/4 ≤ 1/4 ∧ R*ρ+e/4 ≤ e ∧
      (L+1)*e+(R+m)*ρ+e/4<1/2 := by
  have hR : 0 ≤ (R:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hm : 0 ≤ (m:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hL : 0 ≤ (L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_RelayProbability
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]

namespace BernoulliProduct
variable {E : Type*}

lemma measurableSet_twoPredictions (q : E → unitInterval) (S : Set E)
    (C D : Set (Set E)) (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma S] (twoPredictions q S C D δ) :=
  (measurableSet_le measurable_const
    ((measurable_blockProbability q S C hC).ennreal_toReal)).inter
  (measurableSet_le measurable_const
    ((measurable_blockProbability q S D hD).ennreal_toReal))

theorem twoPredictions_positive (q : E → unitInterval) (S : Set E)
    (C D : Set (Set E)) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ) (ha : 2*a<δ)
    (hc : (law q).real Cᶜ ≤ a) (hd : (law q).real Dᶜ ≤ a) :
    0<(law q).real (twoPredictions q S C D δ) := by
  have h1 := bad_prediction_bound q S Set.univ C MeasurableSet.univ hC δ hδ
  have h2 := bad_prediction_bound q S Set.univ D MeasurableSet.univ hD δ hδ
  have hcEq : Set.univ \ C = Cᶜ := by ext; simp
  have hdEq : Set.univ \ D = Dᶜ := by ext; simp
  simp only [Set.univ_inter,hcEq,hdEq] at h1 h2
  have he : (twoPredictions q S C D δ)ᶜ=
      {σ | (blockProbability q S C σ).toReal<1-δ}∪
      {σ | (blockProbability q S D σ).toReal<1-δ} := by
    ext σ
    simp only [twoPredictions,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_union,not_and_or,not_le]
  have hm := (blockSigma_le S) _ (measurableSet_twoPredictions q S C D hC hD δ)
  have hcomp : (law q).real (twoPredictions q S C D δ)ᶜ<1 := by
    rw [he]
    calc
      _ ≤ (law q).real {σ | (blockProbability q S C σ).toReal<1-δ}+
          (law q).real {σ | (blockProbability q S D σ).toReal<1-δ} := measureReal_union_le _ _
      _ ≤ (law q).real Cᶜ/δ+(law q).real Dᶜ/δ := add_le_add h1 h2
      _ ≤ a/δ+a/δ := add_le_add (div_le_div_of_nonneg_right hc hδ.le)
        (div_le_div_of_nonneg_right hd hδ.le)
      _ = 2*a/δ := by ring
      _ < 1 := (div_lt_one hδ).mpr ha
  rw [probReal_compl_eq_one_sub hm] at hcomp
  linarith

end BernoulliProduct
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorNormalization
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.Corridor
open BondGraph

variable {V : Type*}

lemma sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]

lemma timeCenter_target (T : ℝ) (v : Site) (b : Bool) :
    timeCenter T (target (v,b))=timeCenter T v+T := by
  cases b <;> simp [target,timeCenter] <;> ring

lemma heightCenter_target (T : ℝ) (v : Site) (b : Bool) :
    heightCenter T (target (v,b))=heightCenter T v+sign b*T/4 := by
  cases b <;> simp [target,heightCenter,sign] <;> ring

lemma normalized_box (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) :
    graphBox (normalized t z T) (J/T) (2520/T) v=
      {x | |localTime t T v x|≤J ∧ |localHeight z T v x|≤J/4+630} := by
  ext x
  change (|t x/T-((v.1 : ℝ)+v.2)|≤J/T ∧
    |4*z x/T-((v.1 : ℝ)-v.2)|≤J/T+2520/T) ↔ _
  have ht : t x/T-((v.1 : ℝ)+v.2)=localTime t T v x/T := by
    dsimp [localTime,timeCenter]; field_simp
  have hz : 4*z x/T-((v.1 : ℝ)-v.2)=4*localHeight z T v x/T := by
    dsimp [localHeight,heightCenter]; field_simp
  rw [ht,hz,abs_div,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
    show J/T+2520/T=(J+2520)/T by ring,div_le_div_iff_of_pos_right hT,
    abs_mul,show |(4 : ℝ)|=4 by norm_num]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨ht,hz⟩ <;> exact ⟨ht,by linarith⟩

lemma normalized_tube (t z : V → ℝ) (T : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    (normalized t z T) ⁻¹' tube (2520/T) (v,b)=
      {x | 0≤localTime t T v x ∧ localTime t T v x≤T ∧
        |localHeight z T v x-sign b*localTime t T v x/4|≤630} := by
  ext x
  have ht : ((v.1 : ℝ)+v.2≤t x/T) ↔ 0≤localTime t T v x := by
    rw [le_div_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> linarith
  have ht' : (t x/T≤(v.1 : ℝ)+v.2+1) ↔ localTime t T v x≤T := by
    rw [div_le_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> nlinarith
  cases b with
  | true =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(t x/T-2*(v.2 : ℝ))|≤2520/T) ↔ _
    have he : 4*z x/T-(t x/T-2*(v.2 : ℝ))=
        4*(localHeight z T v x-sign true*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp; ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩
  | false =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(2*(v.1 : ℝ)-t x/T)|≤2520/T) ↔ _
    have he : 4*z x/T-(2*(v.1 : ℝ)-t x/T)=
        4*(localHeight z T v x-sign false*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp; ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩

lemma normalized_domain (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    graphDomain (normalized t z T) (J/T) (2520/T) (v,b)=
      relayDomain (localTime t T v) (localHeight z T v) J T (sign b) := by
  change (normalized t z T) ⁻¹' (box _ _ v∪box _ _ (target (v,b))∪tube _ (v,b))=_
  rw [Set.preimage_union,Set.preimage_union]
  change graphBox _ _ _ v∪graphBox _ _ _ (target (v,b))∪_=_
  rw [normalized_box t z T J hT,normalized_box t z T J hT,normalized_tube t z T hT]
  ext x
  change ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target,sub_add_eq_sub_sub]

lemma mark_initial (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) 0 (sign b) ρ=mark t z T ρ v := by
  ext x
  simp only [relayMark,mark,Set.mem_ofPred_eq,mul_zero,zero_div,sub_zero,zero_add]

lemma mark_target (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) T (sign b) ρ=mark t z T ρ (target (v,b)) := by
  ext x
  change (T≤localTime t T v x ∧ localTime t T v x≤T+ρ ∧
    |localHeight z T v x-sign b*T/4|≤210) ↔ _
  change _ ↔ (0≤localTime t T (target (v,b)) x ∧ localTime t T (target (v,b)) x≤ρ ∧
    |localHeight z T (target (v,b)) x|≤210)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target]
  have he : z x-heightCenter T v-sign b*T/4=z x-(heightCenter T v+sign b*T/4) := by ring
  rw [he]
  constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨by linarith,by linarith,hc⟩

lemma mark_subset_box (t z : V → ℝ) (T J ρ : ℝ) (hT : 0<T) (hJ : 0≤J) (hρJ : ρ≤J) (v : Site) :
    mark t z T ρ v⊆graphBox (normalized t z T) (J/T) (2520/T) v := by
  rw [normalized_box t z T J hT]
  intro x hx
  exact ⟨by rw [abs_of_nonneg hx.1]; exact hx.2.1.trans hρJ,by linarith [hx.2.2]⟩

lemma coordinateMove_translate {E : Type*} (G : BondGraph V E) (t z : V → ℝ)
    (T : ℝ) (v : Site) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (localTime t T v) (localHeight z T v) m e y s=
      G.coordinateMove t z m e y s := by
  unfold coordinateMove localTime localHeight
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ b, t b-timeCenter T v-(t y-timeCenter T v+1)=t b-(t y+1) := by intro b; ring
  have hz : ∀ b, z b-heightCenter T v-(z y-heightCenter T v+s)=z b-(z y+s) := by intro b; ring
  simp only [ht,hz]

end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CoordinateScheme
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct

namespace CoordinateData
variable {V E : Type*} (C : CoordinateData V E)

lemma T_pos : 0<C.T := by unfold T; positivity

lemma L_large (h : C.Bounds) : 416≤C.L := by
  have : (416 : ℝ)≤C.L := by linarith [h.J_lower,h.L_lower]
  exact_mod_cast this

lemma small_rho (h : C.Bounds) : C.rho≤C.J := by
  have he := h.e_small
  have hr := h.rho_small
  have hle : C.rho≤C.e := (relay_coordinate_scale C.L C.R C.m C.e C.rho
    h.e_pos h.rho_nonneg he hr).1
  have hLp : 0≤(C.L : ℝ)*C.e := mul_nonneg (Nat.cast_nonneg _) h.e_pos.le
  linarith [h.J_lower]

lemma layout (h : C.Bounds) :
    0≤C.scheme.h ∧ C.scheme.h≤C.scheme.j ∧ 2*C.scheme.j+C.scheme.h<1 := by
  change 0≤2520/C.T ∧ 2520/C.T≤C.J/C.T ∧ 2*(C.J/C.T)+2520/C.T<1
  refine ⟨div_nonneg (by norm_num) C.T_pos.le, (div_le_div_iff_of_pos_right C.T_pos).mpr (by linarith [h.J_lower]),?_⟩
  rw [show 2*(C.J/C.T)+2520/C.T=(2*C.J+2520)/C.T by ring,div_lt_one C.T_pos]
  dsimp [T]
  linarith [h.J_lower,h.L_lower]

lemma root_seed (h : C.Bounds) : (C.scheme.seed∩C.scheme.mark (0,0)).Nonempty := by
  refine ⟨C.origin,C.graph.mem_vertexBall_self C.origin C.m,?_⟩
  change 0≤localTime C.time C.T (0,0) C.origin ∧
    localTime C.time C.T (0,0) C.origin≤C.rho ∧ |localHeight C.height C.T (0,0) C.origin|≤210
  simp [localTime,localHeight,timeCenter,heightCenter,h.time_origin,h.height_origin,h.rho_nonneg]

lemma marks_disjoint (h : C.Bounds) : Pairwise (Disjoint on C.scheme.mark) := by
  intro v w hvw
  exact (graph_boxes_disjoint (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
    (C.layout h).2.2 hvw).mono
    (mark_subset_box C.time C.height C.T C.J C.rho C.T_pos (by linarith [h.J_lower]) (C.small_rho h) v)
    (mark_subset_box C.time C.height C.T C.J C.rho C.T_pos (by linarith [h.J_lower]) (C.small_rho h) w)

lemma domain_eq (v : Site) (b : Bool) : C.scheme.edgeDomain (v,b)=
    C.graph.inducedEdges (relayDomain (localTime C.time C.T v) (localHeight C.height C.T v)
      C.J C.T (sign b)) := by
  change C.graph.inducedEdges (graphDomain (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T) (v,b))=_
  rw [normalized_domain C.time C.height C.T C.J C.T_pos]

lemma local_time_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localTime C.time C.T v u-localTime C.time C.T v w|≤C.rho := by
  simpa only [localTime,sub_sub_sub_cancel_right] using h.time_step huw

lemma local_height_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localHeight C.height C.T v u-localHeight C.height C.T v w|≤C.rho := by
  simpa only [localHeight,sub_sub_sub_cancel_right] using h.height_step huw

lemma source_behind (h : C.Bounds) (n : ℕ) (hn : 0<n) :
    ∀ a∈C.scheme.seed, localTime C.time C.T (slotSite n) a≤C.m*C.rho-C.T := by
  intro a ha
  have ht := (abs_le.mp (C.graph.coordinate_ball_bound C.time C.rho h.rho_nonneg h.time_step ha)).2
  rw [h.time_origin,sub_zero] at ht
  have hv := slotSite_quadrant n
  have hnz : slotSite n≠(0,0) := by
    intro he
    have he' := congrArg gridSlot he
    rw [gridSlot_slotSite] at he'
    change n=0 at he'
    omega
  have hsumInt : 1≤(slotSite n).1+(slotSite n).2 := by
    by_contra hs
    have hx : (slotSite n).1=0 := by dsimp [quadrant] at hv; omega
    have hy : (slotSite n).2=0 := by dsimp [quadrant] at hv; omega
    exact hnz (Prod.ext hx hy)
  have hsum : (1 : ℝ)≤((slotSite n).1 : ℝ)+(slotSite n).2 := by exact_mod_cast hsumInt
  have hmul := mul_le_mul_of_nonneg_right hsum C.T_pos.le
  change C.time a-(((slotSite n).1 : ℝ)+(slotSite n).2)*C.T≤_
  linarith

end CoordinateData
end CriticalPercolation.Corridor
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CoordinateProspective
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.Corridor.CoordinateData
open BondGraph Boundary BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (C : CoordinateData V E)

lemma active_slot_positive (n : ℕ) (S : GrowthState) (hv : S.Valid n)
    (ha : (incoming n S.good).isSome) : 0<n := by
  obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
  have ht := parent_slot_lt e (hv.2.1 _ (incoming_source he)).1
  rw [incoming_target he,gridSlot_slotSite] at ht
  omega

theorem prospective_estimate (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s))
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (_hc : S.Covered)
    (ha : (incoming n S.good).isSome) (ω : Set E) (b : Bool) :
    (blockProbability C.scheme.parameter (C.scheme.block S)
      (C.scheme.incomingHit n S\C.scheme.nextHit n S b) ω).toReal≤(C.L+1)*C.kappa := by
  let v := slotSite n
  let F := C.scheme.enlarged n S
  let U := F∪C.scheme.edgeDomain (v,b)
  have hdom := C.domain_eq v b
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
      (localHeight C.height C.T v) C.J C.T (sign b))⊆U := by
    rw [← hdom]
    exact Set.subset_union_right
  have hfresh : Disjoint (C.scheme.block S)
      (C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
        (localHeight C.height C.T v) C.J C.T (sign b))) := by
    rw [← hdom]
    exact outgoing_unrevealed C.graph (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
      (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2 n S hv (active_slot_positive n S hv ha) rfl
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T v) (localHeight C.height C.T v)
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hP : 1≤C.T := by
    have hh : (416 : ℝ)≤C.L := by exact_mod_cast C.L_large h
    dsimp [T]; linarith
  have hh := C.graph.coordinate_pinned_corridor_failure_bs h.connected h.locallyFinite
    C.scheme.seed (C.graph.vertexBall_finite h.locallyFinite C.origin C.m) C.scheme.parameter
    (C.scheme.block S) F U ω Set.subset_union_left
    (localTime C.time C.T v) (localHeight C.height C.T v) (sign b) C.e C.rho C.J C.T
    C.L C.R C.m (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    hP (C.source_behind h n (active_slot_positive n S hv ha))
    (fun {_ _} hh => C.local_time_step h v hh) (fun {_ _} hh => C.local_height_step h v hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper (fun _ _ => rfl) hDU hfresh C.D C.k C.M C.VM h.degree h.M_pos
    h.M_bound h.VM_bound C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small
    h.k_large h.R_large hmoves
  change (blockProbability C.scheme.parameter (C.scheme.block S)
    (C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) 0 (sign b) C.rho) F\
      C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) C.T (sign b) C.rho) U) ω).toReal≤_ at hh
  rw [mark_initial,mark_target] at hh
  exact hh

lemma root_corridor_estimate (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) (b : Bool) :
    (BernoulliProduct.law C.scheme.parameter).real
      (C.scheme.hit (target ((0,0),b))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b)))ᶜ≤C.eta+C.L*C.kappa := by
  let U := C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b)
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T (0,0))
      (localHeight C.height C.T (0,0)) C.J C.T (sign b))⊆U := by
    rw [← C.domain_eq]
    exact Set.subset_union_right
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0))
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hh := C.graph.original_root_corridor_miss_bs h.connected h.locallyFinite C.origin
    (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0)) (sign b) C.e C.rho C.J
    C.L C.R C.m U hDU (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    (by simp [localTime,timeCenter,h.time_origin]) (by simp [localHeight,heightCenter,h.height_origin])
    (fun {_ _} hh => C.local_time_step h (0,0) hh) (fun {_ _} hh => C.local_height_step h (0,0) hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper C.D C.k C.M C.VM h.degree h.M_pos h.M_bound h.VM_bound
    C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small h.k_large h.R_large hmoves
  change (BernoulliProduct.law (fun _ : E => C.p)).real
    (C.graph.restrictedSeed (C.graph.vertexBall C.origin C.m)
      (relayMark (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0)) C.T (sign b) C.rho) U)ᶜ≤_ at hh
  rw [mark_target] at hh
  exact hh

lemma root_positive (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) :
    0<(BernoulliProduct.law C.scheme.parameter).real C.scheme.rootEvent := by
  have he : C.scheme.rootEvent=twoPredictions C.scheme.parameter (C.scheme.block GrowthState.initial)
      (C.scheme.hit (target ((0,0),true))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),true)))
      (C.scheme.hit (target ((0,0),false))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),false))) C.delta := by
    ext ω
    change (∀ b : Bool, 1-C.delta≤(blockProbability C.scheme.parameter
      (C.scheme.block GrowthState.initial) (C.scheme.hit (target ((0,0),b))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b))) ω).toReal) ↔ (_ ∧ _)
    constructor
    · intro hh; exact ⟨hh true,hh false⟩
    · rintro ⟨ht,hf⟩ b; cases b <;> assumption
  rw [he]
  apply twoPredictions_positive _ _ _ _
    (C.graph.restrictedSeed_measurable _ _ _) (C.graph.restrictedSeed_measurable _ _ _)
    C.delta (C.eta+C.L*C.kappa) h.delta_pos h.root_error
    (C.root_corridor_estimate h hmove true) (C.root_corridor_estimate h hmove false)

theorem moves_force_percolation (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) :
    0<C.graph.law C.p C.graph.percolates := by
  let hf := C.graph.vertexBall_finite h.locallyFinite C.origin C.m
  exact C.scheme.exploration_percolates (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2
    hf.toFinset (by simp only [Set.Finite.coe_toFinset]; rfl) (C.root_seed h) (C.marks_disjoint h)
    C.p rfl (C.root_positive h hmove) h.delta_pos ((C.L+1)*C.kappa) C.contour
    h.contour_nonneg h.contour_small (mul_nonneg (by positivity) h.kappa_pos.le) h.test_error (C.prospective_estimate h hmove)

theorem moves_impossible_below_criticality (h : C.Bounds)
    (hp : C.p<C.graph.criticalProbability)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) : False :=
  (not_le_of_gt hp) (C.graph.criticalProbability_le_of_pos (C.moves_force_percolation h hmove))

end CriticalPercolation.Corridor.CoordinateData
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorScaleChoice
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Classical

namespace CriticalPercolation.Corridor.ScaleChoice

lemma J_lower : 26200<J := by norm_num [J]
lemma L_lower : 10*(J+210)<L := by norm_num [J,L]
lemma e_pos : 0<e := by norm_num [e,L]
lemma e_lt : e<1/10 := by norm_num [e,L]
lemma e_small : (L+3)*e<1/100 := by norm_num [e,L]
lemma kappa_pos : 0<kappa := by norm_num [kappa,epsilon,delta,contour,L]
lemma kappa_le : kappa≤1 := by norm_num [kappa,epsilon,delta,contour,L]
lemma log_nonneg : 0≤Real.log (4/kappa) :=
  Real.log_nonneg (by norm_num [kappa,epsilon,delta,contour,L])
lemma eta_pos : 0<eta := by
  unfold eta
  exact div_pos (sq_pos_of_pos kappa_pos) (mul_pos (by norm_num) (by linarith [log_nonneg]))
lemma eta_le : eta≤kappa := by
  unfold eta
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<32) (by linarith [log_nonneg]))]
  have hk := kappa_pos
  have hkl := kappa_le
  have hlog := mul_nonneg hk.le log_nonneg
  nlinarith
lemma eta_lt : eta<1/10 :=
  eta_le.trans_lt (by norm_num [kappa,epsilon,delta,contour,L])
lemma eta_small : eta≤kappa*(kappa/4)/(4*(Real.log (4/kappa)+1)) := by
  have hp : 0<Real.log (4/kappa)+1 := by linarith [log_nonneg]
  unfold eta
  field_simp
  nlinarith [sq_nonneg kappa]
lemma delta_pos : 0<delta := by norm_num [delta,epsilon,contour]
lemma root_error : 2*(eta+L*kappa)<delta := by
  have he := eta_le
  have hn : 2*(kappa+L*kappa)<delta := by norm_num [delta,kappa,epsilon,contour,L]
  linarith
lemma contour_nonneg : 0 ≤ contour := by norm_num [contour]
lemma contour_small : 8*contour<1 := by norm_num [contour]
lemma test_error : delta+2*((L+1)*kappa)/delta ≤ contour^4 := by
  norm_num [delta,kappa,epsilon,contour,L]

lemma trial_scales (pc : ℝ) (D M VM m : ℕ) :
    ∃ k R : ℕ,
      M*⌈Real.log (4/kappa)/(pc/2)^(m+1+VM)⌉₊<k ∧ m<R ∧
      4/(kappa*(1-pc)^(D*k))<(R : ℝ)-m := by
  let k := M*⌈Real.log (4/kappa)/(pc/2)^(m+1+VM)⌉₊+1
  obtain ⟨r,hr⟩ := exists_nat_gt (4/(kappa*(1-pc)^(D*k)))
  refine ⟨k,m+r+1,by dsimp [k]; omega,by omega,?_⟩
  push_cast
  linarith

lemma mesh (R m : ℕ) : ∃ rho : ℝ, 0 < rho ∧ (R+m+1)*rho<e/10 := by
  have hd : (0 : ℝ)<(R:ℝ)+m+1 := by positivity
  refine ⟨e/(20*((R:ℝ)+m+1)),div_pos e_pos (mul_pos (by norm_num) hd),?_⟩
  have he : ((R:ℝ)+m+1)*(e/(20*((R:ℝ)+m+1)))=e/20 := by field_simp
  rw [he]
  linarith [e_pos]

end CriticalPercolation.Corridor.ScaleChoice
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ApproximateMoveEndgame
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
open Corridor

variable {V E : Type*} (G : BondGraph V E)

lemma coordinateMove_sub_const (t z : V → ℝ) (a b : ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (fun x => t x-a) (fun x => z x-b) m e y s=G.coordinateMove t z m e y s := by
  unfold coordinateMove
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ x, t x-a-(t y-a+1)=t x-(t y+1) := by intro x; ring
  have hz : ∀ x, z x-b-(z y-b+s)=z x-(z y+s) := by intro x; ring
  simp only [ht,hz]

theorem approximate_moves_contradiction_bs_oai
    (hconnected : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hmoves : ∀ e eta : ℝ, 0<e → e<1/10 → 0<eta → eta<1/10 →
      ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
        (G.criticalProbability : ℝ)/2≤p ∧ p<G.criticalProbability ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ rho) ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ rho) ∧
        ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
          (G.coordinateMove t z m e y s)) : False := by
  let := G.countable_vertices hconnected hl
  let := G.countable_bonds hconnected hl
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨m,hm⟩ := hmoves ScaleChoice.e ScaleChoice.eta ScaleChoice.e_pos ScaleChoice.e_lt
    ScaleChoice.eta_pos ScaleChoice.eta_lt
  obtain ⟨D,_hDpos,hD⟩ := G.uniform_incident_bound hq
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq (4*m+2)
  obtain ⟨VM,hVM⟩ := G.uniform_ball_bound hq m
  obtain ⟨k,R,hk,hR,hRlarge⟩ := ScaleChoice.trial_scales (G.criticalProbability : ℝ) D (M+1) VM m
  obtain ⟨rho,hrho,hrhosmall⟩ := ScaleChoice.mesh R m
  obtain ⟨t,z,p,hpl,hpu,ht,hz,hmv⟩ := hm rho hrho
  let C : CoordinateData V E := {
    graph := G, origin := o, time := fun x => t x-t o, height := fun x => z x-z o,
    J := ScaleChoice.J, L := ScaleChoice.L, R := R, m := m, D := D, k := k,
    M := M+1, VM := VM, e := ScaleChoice.e, rho := rho, kappa := ScaleChoice.kappa,
    eta := ScaleChoice.eta, delta := ScaleChoice.delta, contour := ScaleChoice.contour,
    pc := G.criticalProbability, p := p }
  have hb : C.Bounds := {
    connected := hconnected
    locallyFinite := hl
    time_origin := sub_self _
    height_origin := sub_self _
    time_step := fun {_ _} h => by simpa only [C,sub_sub_sub_cancel_right] using ht h
    height_step := fun {_ _} h => by simpa only [C,sub_sub_sub_cancel_right] using hz h
    J_lower := ScaleChoice.J_lower
    L_lower := ScaleChoice.L_lower
    e_pos := ScaleChoice.e_pos
    rho_nonneg := hrho.le
    e_small := ScaleChoice.e_small
    rho_small := hrhosmall
    R_gt := hR
    pc_pos := hpc
    pc_lt := hpc1
    p_lower := hpl
    p_upper := hpu.le
    degree := hD
    M_pos := Nat.succ_pos M
    M_bound := fun v => (hM v).trans (Nat.le_succ M)
    VM_bound := hVM
    kappa_pos := ScaleChoice.kappa_pos
    kappa_le := ScaleChoice.kappa_le
    eta_nonneg := ScaleChoice.eta_pos.le
    eta_small := ScaleChoice.eta_small
    k_large := hk.le
    R_large := hRlarge
    delta_pos := ScaleChoice.delta_pos
    root_error := ScaleChoice.root_error
    contour_nonneg := ScaleChoice.contour_nonneg
    contour_small := ScaleChoice.contour_small
    test_error := ScaleChoice.test_error }
  apply C.moves_impossible_below_criticality hb hpu
  intro y s hs
  change 1-ScaleChoice.eta≤(BernoulliProduct.law (fun _ : E => p)).real
    (G.coordinateMove (fun x => t x-t o) (fun x => z x-z o) m ScaleChoice.e y s)
  rw [coordinateMove_sub_const]
  exact hmv y s hs

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs_oai.{u_1, u_2}
