-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:44:31.35981+00:00
-- url     : https://prove2.me/submissions/56d6576b-99c0-4b8a-8034-3a948860fa0e

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_fresh_contact_transfer_bs

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BlockIndependence
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
variable {E I : Type*}

lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

lemma measurableSet_closed_coordinate (e : E) :
    MeasurableSet[coordinateSigma e] {ω : Set E | e ∉ ω} := by
  refine ⟨{False},MeasurableSet.singleton _,?_⟩
  ext ω
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · intro h hp
    exact Eq.mp h hp
  · intro h
    exact propext (iff_false_intro h)

lemma measurableSet_closedBlock (S : Set E) (hS : S.Countable) :
    MeasurableSet[blockSigma S] (closedBlock S) := by
  have heq : closedBlock S = ⋂ e ∈ S, {ω : Set E | e ∉ ω} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left]
  rw [heq]
  apply MeasurableSet.biInter hS
  intro e he
  exact (le_iSup_of_le e (le_iSup_of_le he le_rfl) : coordinateSigma e ≤ blockSigma S)
    _ (measurableSet_closed_coordinate e)

lemma law_closedBlock (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (closedBlock S) = ∏ e ∈ hS.toFinset, bitMeasure (q e) {False} := by
  have heq : closedBlock S = ⋂ e ∈ hS.toFinset, {ω : Set E | (e ∈ ω) = False} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left,
      Set.Finite.mem_toFinset]
    constructor
    · intro h e he
      exact propext (iff_false_intro (h he))
    · intro h e he hp
      exact Eq.mp (h e he) hp
  rw [heq,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e False)
  · intro e _
    exact ⟨{False},MeasurableSet.singleton _,rfl⟩

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

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteSeedTree
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

lemma finite_seed_tree_of_rank {S : Set V} (hS : S.Finite) (o : V)
    (r : V → ℕ)
    (hparent : ∀ v∈S, v≠o → ∃ w∈S, G.fullGraph.Adj w v ∧ r w < r v) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges S ∧ F.ncard ≤ S.ncard ∧
      ∀ v∈S, (G.openGraph F).Reachable o v := by
  let U := S\{o}
  have hU : U.Finite := hS.sdiff
  let := hU.fintype
  have hh : ∀ v : U, ∃ (w : V) (e : E), w∈S ∧ G.ends e=s(w,v.val) ∧
      w≠v.val ∧ r w < r v.val := by
    intro v
    obtain ⟨w,hw,⟨⟨e,_,he⟩,hne⟩,hr⟩ := hparent v.val v.property.1 v.property.2
    exact ⟨w,e,hw,he,hne,hr⟩
  choose w e hw hend hne hr using hh
  let F : Set E := Set.range e
  have hF : F.Finite := Set.finite_range e
  refine ⟨F,hF,?_,?_,?_⟩
  · rintro b ⟨v,rfl⟩ z hz
    rw [hend v] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact hw v
    · exact v.property.1
  · calc
      F.ncard ≤ (Set.univ : Set U).ncard := by
        simpa only [F,Set.image_univ] using (Set.ncard_image_le (f := e) (Set.finite_univ : (Set.univ : Set U).Finite))
      _ = U.ncard := by simp
      _ ≤ S.ncard := Set.ncard_le_ncard Set.sdiff_subset hS
  · intro v hv
    generalize hn : r v=n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hvo : v=o
      · subst v; exact SimpleGraph.Reachable.refl _
      · let a : U := ⟨v,hv,hvo⟩
        have hprev := ih (r (w a)) (by simpa only [← hn] using hr a) (w a) (hw a) rfl
        apply hprev.trans
        exact (show (G.openGraph F).Adj (w a) v from
          ⟨⟨e a,⟨a,rfl⟩,hend a⟩,hne a⟩).reachable

lemma ballRank_mem {o v : V} (h : ∃ n, v∈G.vertexBall o n) :
    v∈G.vertexBall o (G.ballRank o v) := by
  simp only [ballRank,dite_eq_left h]
  exact Nat.find_spec h

lemma ballRank_le {o v : V} {n : ℕ} (h : v∈G.vertexBall o n) : G.ballRank o v ≤ n := by
  have he : ∃ k, v∈G.vertexBall o k := ⟨n,h⟩
  simp only [ballRank,dite_eq_left he]
  exact Nat.find_min' he h

lemma ballRank_eq_zero_iff {o v : V} (h : ∃ n, v∈G.vertexBall o n) :
    G.ballRank o v=0 ↔ v=o := by
  constructor
  · intro hz
    have hh := G.ballRank_mem h
    rw [hz] at hh
    exact hh
  · intro hvo
    subst v
    exact Nat.eq_zero_of_le_zero (G.ballRank_le (show o∈G.vertexBall o 0 from rfl))

lemma ballRank_predecessor {o v : V} (h : ∃ n, v∈G.vertexBall o n) (hne : v≠o) :
    ∃ w, G.fullGraph.Adj w v ∧ G.ballRank o w+1=G.ballRank o v ∧
      w∈G.vertexBall o (G.ballRank o w) := by
  have hn : 0 < G.ballRank o v := Nat.pos_of_ne_zero (fun hh => hne ((G.ballRank_eq_zero_iff h).mp hh))
  obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hv := G.ballRank_mem h
  rw [heq] at hv
  rcases hv with hv|hv
  · have hb := G.ballRank_le hv
    omega
  · obtain ⟨w,hw,hvw⟩ := Set.mem_iUnion₂.mp hv
    have h1 := G.ballRank_le hw
    have h2 := G.ballRank_le (G.vertexBall_step (G.ballRank_mem ⟨n,hw⟩) hvw)
    refine ⟨w,hvw,by omega,G.ballRank_mem ⟨n,hw⟩⟩

lemma finite_seed_tree (hlocal : G.LocallyFinite) (o : V) (m : ℕ) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges (G.vertexBall o m) ∧
      F.ncard ≤ (G.vertexBall o m).ncard ∧
      ∀ v∈G.vertexBall o m, (G.openGraph F).Reachable o v := by
  apply G.finite_seed_tree_of_rank (G.vertexBall_finite hlocal o m) o (G.ballRank o)
  intro v hv hne
  obtain ⟨w,hw,hr,hmem⟩ := G.ballRank_predecessor ⟨m,hv⟩ hne
  exact ⟨w,G.vertexBall_mono o (by have := G.ballRank_le hv; omega) hmem,hw,by omega⟩

end CriticalPercolation.BondGraph
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

lemma measurable_allOpen_block [Countable E] (F : Set E) :
    MeasurableSet[blockSigma F] (allOpen F) := by
  have he : allOpen F=⋂ e : F, {ω : Set E | (e:E)∈ω} := by
    ext ω
    simp only [allOpen,Set.mem_ofPred_eq,Set.mem_iInter]
    exact ⟨fun h e => h e.property,fun h e he => h ⟨e,he⟩⟩
  rw [he]
  apply MeasurableSet.iInter
  intro e
  have hm : MeasurableSet[coordinateSigma (e:E)] {ω : Set E | (e:E)∈ω} :=
    ⟨{True},MeasurableSet.singleton _,by ext ω; simp⟩
  exact (le_iSup_of_le (e:E) (le_iSup_of_le e.property le_rfl) :
    coordinateSigma (e:E)≤blockSigma F) _ hm

end CriticalPercolation.BernoulliProduct
end
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

lemma hitEvent_mono_target (o : V) {A A' : Set V} (h : A ⊆ A') :
    G.hitEvent o A ⊆ G.hitEvent o A' :=
  fun _ hω => hω.mono (Set.inter_subset_inter_right _ h)

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_LevelContactGeometry
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
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma contactDrop_subset_incident (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) :
    G.contactDrop π j o ω ⊆ G.incidentEdges (G.levelContacts π j o ω) := by
  rintro e ⟨v,hv,w,hw,he⟩
  exact ⟨v,hv,by rw [he]; simp⟩

lemma contactDrop_disjoint_exterior (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) :
    Disjoint (G.contactDrop π j o ω) (G.inducedEdges {v | j ≤ π v}) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨v,hv,w,hw,he⟩ he'
  exact (not_le.mpr hw) (he' w (by rw [he]; simp))

lemma exteriorCluster_subset_level (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o) (ω : Set E) : G.exteriorCluster π j o ω ⊆ {v | j ≤ π v} := by
  intro v hv
  have hc : ∀ ⦃x y⦄, x∈{v | j ≤ π v} →
      (G.openGraph (ω∩G.inducedEdges {v | j ≤ π v})).Adj x y → y∈{v | j ≤ π v} := by
    intro x y hx hxy
    obtain ⟨⟨e,he,hend⟩,_⟩ := hxy
    exact he.2 y (by rw [hend]; simp)
  exact ClusterDeletion.reachable_mem_of_closed hc ho hv

lemma cluster_eq_exterior_of_drop_closed (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hclosed : Disjoint (G.contactDrop π j o ω) ω) :
    G.cluster ω o=G.exteriorCluster π j o ω := by
  apply Set.Subset.antisymm
  · intro v hv
    have hc : ∀ ⦃x y⦄, x∈G.exteriorCluster π j o ω →
        (G.openGraph ω).Adj x y → y∈G.exteriorCluster π j o ω := by
      intro x y hx hxy
      obtain ⟨⟨e,he,hend⟩,hne⟩ := hxy
      have hxj := G.exteriorCluster_subset_level π j o ho ω hx
      by_cases hy : j ≤ π y
      · apply hx.trans
        apply SimpleGraph.Adj.reachable
        refine ⟨⟨e,⟨he,?_⟩,hend⟩,hne⟩
        intro z hz
        rw [hend] at hz
        rcases Sym2.mem_iff.mp hz with rfl|rfl
        · exact hxj
        · exact hy
      · have hy' := lt_of_not_ge hy
        exact False.elim (Set.disjoint_left.mp hclosed
          ⟨x,⟨hx,hcross e x y hend hxj hy'⟩,y,hy',hend⟩ he)
    exact ClusterDeletion.reachable_mem_of_closed hc (SimpleGraph.Reachable.refl o) hv
  · exact G.cluster_mono Set.inter_subset_left o

lemma minimumLevel_of_drop_closed (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hcontact : (G.levelContacts π j o ω).Nonempty)
    (hclosed : Disjoint (G.contactDrop π j o ω) ω) :
    ω∈G.minimumLevel π o j := by
  have he := G.cluster_eq_exterior_of_drop_closed π j o ho hcross ω hclosed
  constructor
  · obtain ⟨v,hv,hj⟩ := hcontact
    exact ⟨v,he.symm ▸ hv,hj⟩
  · rintro ⟨v,hv,hj⟩
    have hlt : π v < j := hj
    have hle : j ≤ π v := G.exteriorCluster_subset_level π j o ho ω (he ▸ hv)
    omega

lemma minimumLevel_pairwiseDisjoint (π : V → ℤ) (o : V) :
    Pairwise (fun i j => Disjoint (G.minimumLevel π o i) (G.minimumLevel π o j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ω ⟨⟨v,hv,hvi⟩,hnoti⟩ ⟨⟨w,hw,hwj⟩,hnotj⟩
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · exact hnotj ⟨v,hv,by change π v < j; rw [hvi]; exact hlt⟩
  · exact hnoti ⟨w,hw,by change π w < i; rw [hwj]; exact hgt⟩

lemma measurableSet_minimumLevel [Countable V] [Countable E] (π : V → ℤ) (o : V) (j : ℤ) :
    MeasurableSet (G.minimumLevel π o j) :=
  (G.measurableSet_hitEvent o _).diff (G.measurableSet_hitEvent o _)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LevelContactMeasurability
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
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation

lemma finiteSetChoice_coe {E : Type*} {S : Set E} (hS : S.Finite) :
    (finiteSetChoice S : Set E)=S := by simp [finiteSetChoice,hS]

lemma finiteSetChoice_eq_iff {E : Type*} (S : Set E) (U : Finset E) :
    finiteSetChoice S=U ↔ S=(U : Set E) ∨ (¬S.Finite ∧ U=∅) := by
  by_cases hS : S.Finite
  · have hh : finiteSetChoice S=U ↔ S=(U : Set E) := by
      calc
        finiteSetChoice S=U ↔ (finiteSetChoice S : Set E)=(U : Set E) := Finset.coe_inj.symm
        _ ↔ S=(U : Set E) := by rw [finiteSetChoice_coe hS]
    simpa [hS] using hh
  · have hne : S≠(U : Set E) := fun h => hS (h ▸ U.finite_toSet)
    simp [finiteSetChoice,hS,hne,eq_comm]

lemma measurableSet_set_eq_const {Ω E : Type*} {m : MeasurableSpace Ω} [Countable E]
    (S : Ω → Set E) (hS : @Measurable Ω (Set E) m inferInstance S) (U : Set E) :
    MeasurableSet[m] {ω | S ω=U} := by
  let : MeasurableSpace Ω := m
  have he : {ω | S ω=U}={ω | ∀ e, e∈S ω ↔ e∈U} := by
    ext ω
    exact Set.ext_iff
  rw [he]
  exact (Measurable.forall (fun e => ((measurable_pi_apply e).comp hS).iff measurable_const)).setOf

lemma measurableSet_finiteSetChoice {Ω E : Type*} [MeasurableSpace Ω] [Countable E]
    (S : Ω → Set E) (hS : Measurable S) (U : Finset E) :
    MeasurableSet {ω | finiteSetChoice (S ω)=U} := by
  have hmfinite : MeasurableSet {ω | (S ω).Finite} := by
    have he : {ω | (S ω).Finite}=⋃ F : Finset E, {ω | S ω=(F : Set E)} := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
      exact ⟨fun h => ⟨h.toFinset,h.coe_toFinset.symm⟩,
        fun ⟨F,hF⟩ => hF ▸ F.finite_toSet⟩
    rw [he]
    exact MeasurableSet.iUnion (fun F => measurableSet_set_eq_const S hS _)
  simp_rw [finiteSetChoice_eq_iff]
  exact (measurableSet_set_eq_const S hS _).union
    (hmfinite.compl.inter (MeasurableSet.const _))

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma incident_ncard_le (S : Set V) (hS : S.Finite)
    (D : ℕ) (hD : ∀ v∈S, (G.incidentEdges {v}).ncard ≤ D) :
    (G.incidentEdges S).ncard ≤ S.ncard*D := by
  have he : G.incidentEdges S=⋃ v∈hS.toFinset, G.incidentEdges {v} := by
    ext e
    simp [incidentEdges]
  rw [he]
  calc
    _ ≤ ∑ v∈hS.toFinset, (G.incidentEdges {v}).ncard :=
      Finset.set_ncard_biUnion_le hS.toFinset _
    _ ≤ ∑ _v∈hS.toFinset, D := Finset.sum_le_sum (fun v hv => hD v (hS.mem_toFinset.mp hv))
    _ = _ := by simp [Set.ncard_eq_toFinset_card S hS]

lemma finite_contactDrop (hlocal : G.LocallyFinite) (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    (hS : (G.levelContacts π j o ω).Finite) : (G.contactDrop π j o ω).Finite :=
  (G.finite_incident hlocal hS).subset (G.contactDrop_subset_incident π j o ω)

lemma contactDrop_ncard_le (hlocal : G.LocallyFinite) (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    (hS : (G.levelContacts π j o ω).Finite) (D : ℕ)
    (hD : ∀ v∈G.levelContacts π j o ω, (G.incidentEdges {v}).ncard ≤ D) :
    (G.contactDrop π j o ω).ncard ≤ (G.levelContacts π j o ω).ncard*D :=
  (Set.ncard_le_ncard (G.contactDrop_subset_incident π j o ω) (G.finite_incident hlocal hS)).trans
    (G.incident_ncard_le _ hS D hD)

variable [Countable V] [Countable E]
lemma measurable_exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.exteriorCluster π j o) :=
  (G.measurable_cluster o).comp (measurable_inter_block _)

lemma measurable_levelContacts (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.levelContacts π j o) := by
  refine @Measurable.of_eval (Set E) V (fun _ => Prop)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) (fun _ => inferInstance) _ ?_
  intro v
  exact @Measurable.and (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _
    ((measurable_pi_apply v).comp (G.measurable_exteriorCluster π j o)) measurable_const

lemma measurable_contactDrop (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.contactDrop π j o) := by
  refine @Measurable.of_eval (Set E) E (fun _ => Prop)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) (fun _ => inferInstance) _ ?_
  intro e
  exact @Measurable.exists (Set E) V (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _ (fun v =>
    @Measurable.and (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _
      ((measurable_pi_apply v).comp (G.measurable_levelContacts π j o)) measurable_const)

lemma measurableSet_fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) :
    MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] (G.fewContacts π j o k) := by
  have he : G.fewContacts π j o k=⋃ U : Finset V,
      ({ω | G.levelContacts π j o ω=(U : Set V)}∩{_ω | U.Nonempty ∧ U.card<k}) := by
    ext ω
    simp [fewContacts]
  rw [he]
  exact MeasurableSet.iUnion (fun U =>
    (measurableSet_set_eq_const _ (G.measurable_levelContacts π j o) (U : Set V)).inter
      (MeasurableSet.const _))

omit [Countable V] [Countable E] in
lemma fewContacts_finite (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) (ω : Set E)
    (hω : ω∈G.fewContacts π j o k) :
    (G.levelContacts π j o ω).Finite ∧ (G.levelContacts π j o ω).Nonempty ∧
      (G.levelContacts π j o ω).ncard<k := by
  obtain ⟨U,hU,hne,hcard⟩ := hω
  rw [hU]
  exact ⟨U.finite_toSet,hne,by simpa using hcard⟩

end BondGraph
end CriticalPercolation
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

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CollarDistance
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

lemma vertexCollar_exists (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty) (v : V) :
    ∃ n, v∈G.vertexCollar B n := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc b v)
  exact ⟨n,Set.mem_iUnion₂.mpr ⟨b,hb,hn⟩⟩

lemma distanceTo_mem {B : Set V} {v : V} (h : ∃ n, v∈G.vertexCollar B n) :
    v∈G.vertexCollar B (G.distanceTo B v) := by
  simp only [distanceTo,dite_eq_left h]
  exact Nat.find_spec h

lemma distanceTo_le {B : Set V} {v : V} {n : ℕ} (h : v∈G.vertexCollar B n) :
    G.distanceTo B v ≤ n := by
  have he : ∃ k, v∈G.vertexCollar B k := ⟨n,h⟩
  simp only [distanceTo,dite_eq_left he]
  exact Nat.find_min' he h

lemma distanceTo_le_iff (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (n : ℕ) : G.distanceTo B v ≤ n ↔ v∈G.vertexCollar B n := by
  constructor
  · intro hn
    obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp (G.distanceTo_mem (G.vertexCollar_exists hc hB v))
    have hmono : Monotone (G.vertexBall b) :=
      monotone_nat_of_le_succ fun _ => Set.subset_union_left
    exact Set.mem_iUnion₂.mpr ⟨b,hb,hmono hn hv⟩
  · exact G.distanceTo_le

lemma distanceTo_eq_zero_iff (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) : G.distanceTo B v=0 ↔ v∈B := by
  rw [← Nat.le_zero,G.distanceTo_le_iff hc hB]
  simp [vertexCollar,vertexBall]

lemma distanceTo_adj (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    {v w : V} (hvw : G.fullGraph.Adj v w) : G.distanceTo B w ≤ G.distanceTo B v+1 := by
  obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp (G.distanceTo_mem (G.vertexCollar_exists hc hB v))
  apply G.distanceTo_le
  exact Set.mem_iUnion₂.mpr ⟨b,hb,Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,hvw⟩)⟩

lemma distanceTo_ball (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    {v w : V} {n : ℕ} (hvw : w∈G.vertexBall v n) : G.distanceTo B w ≤ G.distanceTo B v+n := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hvw
    subst w
    exact Nat.le_refl _
  | succ n ih =>
    rcases hvw with hvw|hvw
    · exact (ih hvw).trans (by omega)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hvw
      have h1 := ih hz
      have h2 := G.distanceTo_adj hc hB hzw
      omega

lemma distanceTo_predecessor (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (hv : G.distanceTo B v≠0) :
    ∃ w, G.fullGraph.Adj v w ∧ G.distanceTo B w+1=G.distanceTo B v := by
  obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero hv
  have hmem := G.distanceTo_mem (G.vertexCollar_exists hc hB v)
  rw [heq] at hmem
  obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp hmem
  rcases hv with hv|hv
  · have hh : v∈G.vertexCollar B n := Set.mem_iUnion₂.mpr ⟨b,hb,hv⟩
    have := G.distanceTo_le hh
    omega
  · obtain ⟨w,hw,hwv⟩ := Set.mem_iUnion₂.mp hv
    have h1 := G.distanceTo_le (B := B) (Set.mem_iUnion₂.mpr ⟨b,hb,hw⟩)
    have h2 := G.distanceTo_adj hc hB hwv
    exact ⟨w,hwv.symm,by omega⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CollarErrorBudget
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace CriticalPercolation

lemma collar_error_budget (κ η shells closed : ℝ) (hκ : 0<κ) (hκ1 : κ≤1)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hclosed : 0 < closed) (hshells : 4/(κ*closed) < shells) :
    1/(shells*closed)+Real.exp (-Real.log (4/κ))+
      (Real.log (4/κ)+1)*η/(κ/4)+κ/4 ≤ κ := by
  have hratio : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  have hK : 0 ≤ Real.log (4/κ) := Real.log_nonneg hratio
  have hK1 : 0<Real.log (4/κ)+1 := by linarith
  have hlam : 0<κ/4 := by linarith
  have hden : 0<κ*closed := mul_pos hκ hclosed
  have hs : 0 < shells := (div_pos (by norm_num) hden).trans hshells
  have hfirst : 1/(shells*closed) ≤ κ/4 := by
    apply (div_le_iff₀ (mul_pos hs hclosed)).mpr
    have hh := (div_lt_iff₀ hden).mp hshells
    nlinarith
  have hexp : Real.exp (-Real.log (4/κ))=κ/4 := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hκ)]
    simp
  have hthird : (Real.log (4/κ)+1)*η/(κ/4) ≤ κ/4 := by
    apply (div_le_iff₀ hlam).mpr
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hK1)).mp hη
    nlinarith
  rw [hexp]
  linarith

lemma positive_trial_power (p : ℝ) (hp : 0<p) (m VM : ℕ) :
    0<(p/2)^(m+1+VM) := pow_pos (by linarith) _

lemma trial_ceiling_budget (K s : ℝ) (hs : 0 < s) :
    K ≤ (⌈K/s⌉₊ : ℝ)*s := by
  have hh : K/s ≤ (⌈K/s⌉₊ : ℝ) := Nat.le_ceil _
  exact (div_le_iff₀ hs).mp hh

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_HonestChoice
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical

namespace CriticalPercolation
variable {Ω I : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma firstTest_eq (P : ℕ → Ω → Prop) (ω : Ω) (n : ℕ) :
    firstTest P ω=n ↔ (P n ω ∧ ∀ m<n, ¬P m ω) ∨ ((¬∃ m, P m ω) ∧ n=0) := by
  by_cases h : ∃ m, P m ω
  · simp [firstTest,h,Nat.find_eq_iff]
  · have hn : ¬P n ω := fun hn => h ⟨n,hn⟩
    simp [firstTest,h,hn,eq_comm]

lemma measurableSet_firstTest (P : ℕ → Ω → Prop) (hP : ∀ n, MeasurableSet {ω | P n ω}) (n : ℕ) :
    MeasurableSet {ω | firstTest P ω=n} := by
  simp_rw [firstTest_eq]
  apply MeasurableSet.union
  · exact (hP n).inter ((Measurable.forall (fun m => measurable_const.imp (hP m).mem.not)).setOf)
  · exact (Measurable.exists (fun m => (hP m).mem)).setOf.compl.inter (MeasurableSet.const _)

theorem exists_honest_selector [Countable I] [Nonempty I] (P : Ω → I → Prop)
    (hP : ∀ i, MeasurableSet {ω | P ω i}) :
    ∃ d : Ω → I, (∀ i, MeasurableSet {ω | d ω=i}) ∧
      ∀ ω, (∃ i, P ω i) → P ω (d ω) := by
  obtain ⟨e,he⟩ := exists_surjective_nat I
  let d : Ω → I := fun ω => e (firstTest (fun n ω => P ω (e n)) ω)
  refine ⟨d,?_,?_⟩
  · intro i
    have hh : {ω | d ω=i}=⋃ n : ℕ, ({ω | firstTest (fun n ω => P ω (e n)) ω=n}∩{_ω | e n=i}) := by
      ext ω
      simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨_,rfl,h⟩,fun ⟨n,hn,hni⟩ => by dsimp [d]; rw [hn,hni]⟩
    rw [hh]
    exact MeasurableSet.iUnion (fun n => (measurableSet_firstTest _ (fun m => hP (e m)) n).inter
      (MeasurableSet.const _))
  · intro ω ⟨i,hi⟩
    obtain ⟨n,rfl⟩ := he i
    have hex : ∃ n, P ω (e n) := ⟨n,hi⟩
    dsimp [d,firstTest]
    rw [dite_eq_left hex]
    exact Nat.find_spec hex

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_TrialSelection
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

namespace CriticalPercolation

theorem separated_subset_of_card {V : Type*} (C : V → V → Prop)
    (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (S : Finset V)
    (hb : ∀ v∈S, (S.filter (C v)).card ≤ M) (hcard : M*N ≤ S.card) :
    ∃ U ⊆ S, U.card=N ∧ (U : Set V).Pairwise (fun v w => ¬C v w) := by
  induction N generalizing S with
  | zero => exact ⟨∅,Finset.empty_subset _,by simp,by simp⟩
  | succ N ih =>
    have hSpos : 0 < S.card := by nlinarith
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hSpos
    let T := S.filter (fun w => ¬C v w)
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hbT : ∀ w∈T, (T.filter (C w)).card ≤ M := by
      intro w hw
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hT)).trans (hb w (hT hw))
    have hcT : M*N ≤ T.card := by
      have he := S.card_filter_add_card_filter_not (C v)
      have hh := hb v hv
      change M*N ≤ (S.filter (fun w => ¬C v w)).card
      nlinarith
    obtain ⟨U,hUT,hUc,hUp⟩ := ih T hbT hcT
    have hvU : v∉U := by
      intro h
      exact (Finset.mem_filter.mp (hUT h)).2 (hrefl v)
    refine ⟨insert v U,Finset.insert_subset hv (hUT.trans hT),by simp [hvU,hUc],?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_insert,Set.mem_insert_iff] at hx hy
    rcases hx with rfl|hx  <;> rcases hy with rfl|hy
    · exact (hxy rfl).elim
    · exact (Finset.mem_filter.mp (hUT hy)).2
    · intro h
      exact (Finset.mem_filter.mp (hUT hx)).2 (hsymm h)
    · exact hUp hx hy hxy

theorem exists_weight_interval {V : Type*} (S : Finset V) (s : V → ℝ)
    (hs : ∀ v∈S, s v ≤ 1) (K : ℝ) (hK : 0 ≤ K) (hSK : K ≤ ∑ v∈S, s v) :
    ∃ U ⊆ S, K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simpa using hSK,by simp; linarith⟩
  | @insert v S hv ih =>
    by_cases h : K ≤ ∑ w∈S, s w
    · obtain ⟨U,hU,hlo,hhi⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)) h
      exact ⟨U,hU.trans (Finset.subset_insert _ _),hlo,hhi⟩
    · refine ⟨insert v S,Finset.Subset.refl _,hSK,?_⟩
      rw [Finset.sum_insert hv]
      have hh := hs v (Finset.mem_insert_self _ _)
      linarith

theorem separated_weighted_trials {V : Type*} (C : V → V → Prop)
    (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (S : Finset V)
    (hb : ∀ v∈S, (S.filter (C v)).card ≤ M) (hcard : M*N ≤ S.card)
    (s : V → ℝ) (s₀ K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ v∈S, s₀ ≤ s v ∧ s v ≤ 1) (hN : K ≤ N*s₀) :
    ∃ U ⊆ S, (U : Set V).Pairwise (fun v w => ¬C v w) ∧
      K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1 := by
  obtain ⟨T,hTS,hTc,hTp⟩ := separated_subset_of_card C hrefl hsymm M N hM S hb hcard
  have hKT : K ≤ ∑ v∈T, s v := by
    calc K ≤ N*s₀ := hN
         _ = ∑ _v∈T, s₀ := by simp [hTc]
         _  ≤  _ := Finset.sum_le_sum (fun v hv => (hs v (hTS hv)).1)
  obtain ⟨U,hUT,hlo,hhi⟩ := exists_weight_interval T s (fun v hv => (hs v (hTS hv)).2)
    K hK hKT
  exact ⟨U,hUT.trans hTS,hTp.mono hUT,hlo,hhi⟩

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContactSelection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation

lemma measurableSet_finset_subset {Ω V : Type*} {m : MeasurableSpace Ω}
    (S : Ω → Set V) (hS : @Measurable Ω (Set V) m inferInstance S) (U : Finset V) :
    MeasurableSet[m] {ω | (U : Set V)⊆S ω} := by
  have he : {ω | (U : Set V)⊆S ω}=⋂ v∈U, {ω | v∈S ω} := by
    ext ω
    simp [Set.subset_def]
  rw [he]
  exact MeasurableSet.biInter U.countable_toSet (fun v _ =>
    ((measurable_pi_apply v).comp hS).setOf)

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma levelContacts_reachable (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    {v : V} (hv : v∈G.levelContacts π j o ω) : (G.openGraph ω).Reachable o v :=
  G.cluster_mono Set.inter_subset_left o hv.1

lemma levelContacts_nonempty_of_hit (π : V → ℤ) (j : ℤ) (o : V) (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hhit : ω∈G.hitEvent o {v | π v<j}) :
    (G.levelContacts π j o ω).Nonempty := by
  by_contra h
  have hd : G.contactDrop π j o ω=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨v,hv,w,hw,hend⟩
    exact h ⟨v,hv⟩
  have hc : Disjoint (G.contactDrop π j o ω) ω := by rw [hd]; exact Set.empty_disjoint _
  have he := G.cluster_eq_exterior_of_drop_closed π j o ho hcross ω hc
  obtain ⟨v,hv,hlt⟩ := hhit
  have hle : j ≤ π v := G.exteriorCluster_subset_level π j o ho ω (he ▸ hv)
  exact (not_le.mpr hlt) hle

lemma levelContacts_supply (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) (ω : Set E)
    (hne : (G.levelContacts π j o ω).Nonempty) (hfew : ω∉G.fewContacts π j o k) :
    ∃ S : Finset V, (S : Set V)⊆G.levelContacts π j o ω ∧ k ≤ S.card := by
  by_cases hfin : (G.levelContacts π j o ω).Finite
  · refine ⟨hfin.toFinset,by simp,?_⟩
    by_contra hcard
    exact hfew ⟨hfin.toFinset,hfin.coe_toFinset.symm,
      by simpa using hne,lt_of_not_ge hcard⟩
  · obtain ⟨S,hS,hSfin,hcard⟩ := Set.Infinite.exists_subset_ncard_eq hfin k
    exact ⟨hSfin.toFinset,by simpa using hS,by simpa [Set.ncard_eq_toFinset_card S hSfin] using hcard.ge⟩

variable [Countable V] [Countable E]

lemma measurableSet_manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) :
    MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] (G.manyContacts π j o k) := by
  apply MeasurableSet.diff _ (G.measurableSet_fewContacts π j o k)
  have he : {ω | (G.levelContacts π j o ω).Nonempty}=⋃ v : V, {ω | v∈G.levelContacts π j o ω} := by
    ext ω
    simp [Set.Nonempty]
  rw [he]
  exact MeasurableSet.iUnion (fun v =>
    @Measurable.setOf (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _
      ((measurable_pi_apply v).comp (G.measurable_levelContacts π j o)))

theorem honest_contact_selection (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (hk : M*N ≤ k)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (s : V → ℝ) (s₀ K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ v, π v=j → s₀ ≤ s v ∧ s v ≤ 1) (hN : K ≤ N*s₀) :
    ∃ d : Set E → Finset V,
      (∀ U, MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] {ω | d ω=U}) ∧
      ∀ ω∈G.manyContacts π j o k,
        (d ω : Set V)⊆G.levelContacts π j o ω ∧
        (d ω : Set V).Pairwise (fun v w => ¬C v w) ∧
        K ≤ ∑ v∈d ω, s v ∧ (∑ v∈d ω, s v) ≤ K+1 := by
  let P := fun (ω : Set E) (U : Finset V) =>
    (U : Set V)⊆G.levelContacts π j o ω ∧
    (U : Set V).Pairwise (fun v w => ¬C v w) ∧
    K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1
  have hm (U : Finset V) : MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] {ω | P ω U} :=
    (measurableSet_finset_subset _ (G.measurable_levelContacts π j o) U).inter (MeasurableSet.const _)
  obtain ⟨d,hd,hgood⟩ := @exists_honest_selector (Set E) (Finset V)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance inferInstance P hm
  refine ⟨d,hd,?_⟩
  intro ω hω
  apply hgood
  obtain ⟨S,hS,hcard⟩ := G.levelContacts_supply π j o k ω hω.1 hω.2
  have hb : ∀ v∈S, (S.filter (C v)).card ≤ M := by
    intro v _hv
    have hh : (S.filter (C v) : Set V)⊆{w | C v w} := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hz := (Set.ncard_le_ncard hh (hfinite v)).trans (hbound v)
    simpa only [Set.ncard_coe_finset] using hz
  obtain ⟨U,hU,hsep,hlo,hhi⟩ := separated_weighted_trials C hrefl hsymm M N hM S hb
    (hk.trans hcard) s s₀ K hK (fun v hv => hs v (hS hv).2) hN
  exact ⟨U,(fun _ hv => hS (hU hv)),hsep,hlo,hhi⟩

end BondGraph
end CriticalPercolation
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
namespace BernoulliProduct
variable {E : Type*}

lemma law_allOpen (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (allOpen S)=∏ e∈hS.toFinset, bitMeasure (q e) {True} := by
  have he : allOpen S=⋂ e∈hS.toFinset, {ω : Set E | (e∈ω)=True} := by
    ext ω
    simp [allOpen,Set.subset_def]
  rw [he,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e True)
  · intro e _
    exact ⟨{True},MeasurableSet.singleton _,rfl⟩

lemma law_allOpen_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N) (hq : ∀ e∈S, (p : ℝ) ≤ q e) :
    (p : ℝ)^N ≤ (law q).real (allOpen S) := by
  rw [measureReal_def,law_allOpen q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (p : ℝ)^S.ncard := pow_le_pow_of_le_one p.2.1 p.2.2 hN
    _ = ∏ e∈hS.toFinset, (p : ℝ) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro edge hedge; exact p.2.1
      · intro e he
        change (p : ℝ) ≤ (bitMeasure (q e)).real {True}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,if_true] using hq e (hS.mem_toFinset.mp he)
end BernoulliProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma vertexBalls_disjoint {v w : V} {n : ℕ} (h : w∉G.vertexBall v (n+n)) :
    Disjoint (G.vertexBall v n) (G.vertexBall w n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact h (G.vertexBall_add hz n (G.vertexBall_comm.mp hz'))

lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)

lemma inward_trials_disjoint (F : V → Set E) (m : ℕ)
    (hF : ∀ v, F v⊆G.inducedEdges (G.vertexBall v (2*m+1)))
    {v w : V} (h : w∉G.vertexBall v (4*m+2)) : Disjoint (F v) (F w) := by
  have h' : w∉G.vertexBall v ((2*m+1)+(2*m+1)) := by
    simpa only [show (2*m+1)+(2*m+1)=4*m+2 by omega] using h
  exact (G.inducedEdges_disjoint (G.vertexBalls_disjoint h')).mono (hF v) (hF w)

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

lemma coordinate_collar_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    (B : Set V) (c r : ℝ) (hB : ∀ v∈B, |f v-c| ≤ r)
    {w : V} {n : ℕ} (hw : w∈G.vertexCollar B n) : |f w-c| ≤ r+n*ρ := by
  obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp hw
  calc
    |f w-c| ≤ |f w-f v|+|f v-c| := abs_sub_le _ _ _
    _ ≤ n*ρ+r := add_le_add (G.coordinate_ball_bound f ρ hρ hf hw) (hB v hv)
    _ = _ := add_comm _ _

lemma inducedEdges_mono {S T : Set V} (h : S⊆T) :
    G.inducedEdges S⊆G.inducedEdges T := by
  intro e he v hv
  exact h (he v hv)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SelectedFresh
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
variable {E I : Type*}

lemma block_event_disjoint_forceOn (X Y : Set E) (hXY : Disjoint X Y)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma Y] A) (σ ω : Set E) :
    forceOn X σ ω∈A ↔ ω∈A := by
  have he : forceOn Y (forceOn X σ ω) ω=ω := by
    ext e
    by_cases heY : e∈Y
    · have heX : e∉X := fun h => Set.disjoint_left.mp hXY h heY
      simp only [mem_forceOn,ite_eq_left heY,ite_eq_right heX]
    · simp only [mem_forceOn,ite_eq_right heY]
  have hh := block_event_forceOn Y A hA (forceOn X σ ω) ω
  rw [he] at hh
  exact hh.symm

lemma selectedEvent_eq_iUnion (d : Set E → I) (A : I → Set (Set E)) :
    selectedEvent d A=⋃ i, ({ω | d ω=i}∩A i) := by
  ext ω
  simp only [selectedEvent,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  exact ⟨fun h => ⟨d ω,rfl,h⟩,fun ⟨i,hi,h⟩ => hi.symm ▸ h⟩

lemma measurableSet_selectedEvent [Countable I] (d : Set E → I)
    (A : I → Set (Set E)) (hd : ∀ i, MeasurableSet {ω | d ω=i})
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (selectedEvent d A) := by
  rw [selectedEvent_eq_iUnion]
  exact MeasurableSet.iUnion (fun i => (hd i).inter (hA i))

theorem blockProbability_selected (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i)) (σ : Set E) :
    blockProbability q X (selectedEvent d A) σ=law q (A (d σ)) := by
  unfold blockProbability
  congr 1
  ext ω
  change forceOn X σ ω∈A (d (forceOn X σ ω)) ↔ ω∈A (d σ)
  have hh : d (forceOn X σ ω)=d σ :=
    (block_event_forceOn X {τ | d τ=d σ} (hd _) σ ω).mpr rfl
  rw [hh]
  exact block_event_disjoint_forceOn X Y hXY (A (d σ)) (hA _) σ ω

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LevelCutProbability
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
variable {E I : Type*}

theorem selected_fresh_lower [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, r ≤ (law q).real (A (d σ))) :
    r*(law q).real C ≤ (law q).real (C∩selectedEvent d A) := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      ENNReal.ofReal r ≤ blockProbability q X (selectedEvent d A) σ := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : ENNReal.ofReal r*law q C ≤ law q (selectedEvent d A∩C) := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      _ = ∫⁻ _ in C, ENNReal.ofReal r ∂law q := by
        rw [lintegral_const,Measure.restrict_apply_univ]
      _ ≤ _ := setLIntegral_mono' (blockSigma_le X _ hC) hk
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht

lemma law_closedBlock_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N)
    (hq : ∀ e∈S, (q e : ℝ) ≤ p) :
    (1-(p : ℝ))^N ≤ (law q).real (closedBlock S) := by
  have hp0 : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.2.2
  have hp1 : 1-(p : ℝ) ≤ 1 := by linarith [p.2.1]
  rw [measureReal_def,law_closedBlock q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (1-(p : ℝ))^S.ncard := pow_le_pow_of_le_one hp0 hp1 hN
    _ = ∏ e∈hS.toFinset, (1-(p : ℝ)) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro e he; exact hp0
      · intro e he
        change 1-(p : ℝ) ≤ (bitMeasure (q e)).real {False}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,if_false] using sub_le_sub_left (hq e (hS.mem_toFinset.mp he)) 1

lemma exists_level_small (μ : Measure (Set E)) [IsProbabilityMeasure μ]
    (J : Finset I) (hJ : J.Nonempty) (C M : I → Set (Set E))
    (hM : ∀ i∈J, MeasurableSet (M i))
    (hdis : (J : Set I).PairwiseDisjoint M) (c : ℝ) (hc : 0 < c)
    (hb : ∀ i∈J, c*μ.real (C i) ≤ μ.real (M i)) :
    ∃ i∈J, μ.real (C i) ≤ 1/((J.card : ℝ)*c) := by
  have hsum : (∑ i∈J, μ.real (M i)) ≤ 1 := by
    rw [← measureReal_biUnion_finset hdis hM]
    exact measureReal_le_one
  have hcard : 0 < (J.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hJ
  by_contra h
  push Not at h
  have hs : (∑ i∈J, 1/(J.card : ℝ)) < ∑ i∈J, μ.real (M i) := by
    apply Finset.sum_lt_sum_of_nonempty hJ
    intro i hi
    have hh := mul_lt_mul_of_pos_left (h i hi) hc
    have he : c*(1/((J.card : ℝ)*c))=1/(J.card : ℝ) := by field_simp
    rw [he] at hh
    exact hh.trans_le (hb i hi)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have he : (J.card : ℝ)*(1/(J.card : ℝ))=1 := by field_simp
  rw [he] at hs
  exact (not_lt_of_ge hsum) hs

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FewContacts
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
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem few_contacts_cost (hlocal : G.LocallyFinite) (q : E → unitInterval)
    (π : V → ℤ) (j : ℤ) (o : V) (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval)
    (hq : ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k : ℕ) (hD : ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D) :
    (1-(p : ℝ))^(D*k)*(BernoulliProduct.law q).real (G.fewContacts π j o k) ≤
      (BernoulliProduct.law q).real (G.minimumLevel π o j) := by
  let X := G.inducedEdges {v | j ≤ π v}
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.contactDrop π j o ω)
  let A : Finset E → Set (Set E) := fun U => closedBlock ((U : Set E)∩Xᶜ)
  have hd (U : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=U} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.contactDrop π j o) (G.measurable_contactDrop π j o) U
  have hA (U : Finset E) : MeasurableSet[blockSigma Xᶜ] (A U) :=
    (blockSigma_mono Set.inter_subset_right) _
      (measurableSet_closedBlock _ ((U.finite_toSet.subset Set.inter_subset_left).countable))
  have he (ω : Set E) (hω : ω∈G.fewContacts π j o k) :
      ((d ω : Set E)∩Xᶜ)=G.contactDrop π j o ω := by
    rw [finiteSetChoice_coe (G.finite_contactDrop hlocal π j o ω
      (G.fewContacts_finite π j o k ω hω).1)]
    exact Set.inter_eq_left.mpr (Set.disjoint_left.mp
      (G.contactDrop_disjoint_exterior π j o ω))
  have hb (ω : Set E) (hω : ω∈G.fewContacts π j o k) :
      (1-(p : ℝ))^(D*k) ≤ (BernoulliProduct.law q).real (A (d ω)) := by
    change _ ≤ (BernoulliProduct.law q).real (closedBlock ((d ω : Set E)∩Xᶜ))
    rw [he ω hω]
    have hω' := G.fewContacts_finite π j o k ω hω
    apply law_closedBlock_lower q _ (G.finite_contactDrop hlocal π j o ω hω'.1) p
    · calc
        _ ≤ (G.levelContacts π j o ω).ncard*D :=
          G.contactDrop_ncard_le hlocal π j o ω hω'.1 D (fun v hv => hD v hv.2)
        _ ≤ k*D := Nat.mul_le_mul_right D (Nat.le_of_lt hω'.2.2)
        _ = D*k := Nat.mul_comm _ _
    · rintro e ⟨v,hv,w,hw,hend⟩
      exact hq e v w hend hv.2 hw
  have hh := selected_fresh_lower q X Xᶜ disjoint_compl_right d A hd hA
    (G.fewContacts π j o k) (G.measurableSet_fewContacts π j o k)
    ((1-(p : ℝ))^(D*k)) (pow_nonneg (sub_nonneg.mpr p.2.2) _) hb
  apply hh.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨hω,hclosed⟩
  apply G.minimumLevel_of_drop_closed π j o ho hcross ω
    (G.fewContacts_finite π j o k ω hω).2.1
  change Disjoint ((d ω : Set E)∩Xᶜ) ω at hclosed
  rwa [he ω hω] at hclosed

theorem exists_few_contact_level (hlocal : G.LocallyFinite) (q : E → unitInterval)
    (π : V → ℤ) (o : V) (J : Finset ℤ) (hJ : J.Nonempty)
    (ho : ∀ j∈J, j ≤ π o)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D) :
    ∃ j∈J, (BernoulliProduct.law q).real (G.fewContacts π j o k) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k)) := by
  apply exists_level_small (BernoulliProduct.law q) J hJ (fun j => G.fewContacts π j o k)
    (G.minimumLevel π o) (fun j _ => G.measurableSet_minimumLevel π o j)
  · intro i hi j hj hij
    exact G.minimumLevel_pairwiseDisjoint π o hij
  · exact pow_pos (sub_pos.mpr hp) _
  · intro j hj
    exact G.few_contacts_cost hlocal q π j o (ho j hj) (hcross j hj) p (hq j hj) D k (hD j hj)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshCollar
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
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fresh_collar_transfer_from_geometry (hlocal : G.LocallyFinite)
    (q : E → unitInterval) (π : V → ℤ) (o : V) (Input T : Set V)
    (J : Finset ℤ) (hJ : J.Nonempty) (ho : ∀ j∈J, j ≤ π o)
    (hInput : ∀ j∈J, ∀ v∈Input, π v<j)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k M N : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (F : ℤ → V → Set E) (B : ℤ → V → Set V)
    (hF : ∀ j∈J, ∀ v, F j v ⊆ (G.inducedEdges {w | j ≤ π w})ᶜ)
    (hconnect : ∀ j∈J, ∀ v, π v=j → ∀ b∈B j v, (G.openGraph (F j v)).Reachable v b)
    (hdis : ∀ j∈J, ∀ v w, ¬C v w → Disjoint (F j v) (F j w))
    (s₀ K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hs : ∀ j∈J, ∀ v, π v=j → s₀ ≤ (BernoulliProduct.law q).real (allOpen (F j v)))
    (hN : K ≤ N*s₀)
    (hmean : ∀ j∈J, ∀ v, π v=j →
      1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B j v) T)) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  obtain ⟨j,hj,hfew⟩ := G.exists_few_contact_level hlocal q π o J hJ ho hcross p hp hq D k hD
  obtain ⟨d,hd,hsel⟩ := G.honest_contact_selection π j o k C hrefl hsymm M N hM hk
    hfinite hbound (fun v => (BernoulliProduct.law q).real (allOpen (F j v))) s₀ K hK
    (fun v hv => ⟨hs j hj v hv,measureReal_le_one⟩) hN
  have hh := G.fresh_contact_transfer_bs q (G.inducedEdges {v | j ≤ π v})
    (G.inducedEdges {v | j ≤ π v})ᶜ disjoint_compl_right d (F j) (B j)
    {v | π v=j} T Input o hd (hF j hj) (hconnect j hj)
    (G.manyContacts π j o k) (G.fewContacts π j o k) (G.measurableSet_manyContacts π j o k)
    (by
      intro ω hω
      have hne := G.levelContacts_nonempty_of_hit π j o (ho j hj) (hcross j hj) ω
        (G.hitEvent_mono_target o (hInput j hj) hω)
      by_cases hf : ω∈G.fewContacts π j o k
      · exact Or.inl hf
      · exact Or.inr ⟨hne,hf⟩)
    (by
      intro ω hω v hv
      have hmem := (hsel ω hω).1 hv
      exact ⟨hmem.2,G.levelContacts_reachable π j o ω hmem⟩)
    K η lam (by linarith) hη hlam (hmean j hj)
    (by
      intro ω hω v hv w hw hvw
      exact hdis j hj v w ((hsel ω hω).2.1 hv hw hvw))
    (fun ω hω => (hsel ω hω).2.2.1) (fun ω hω => (hsel ω hω).2.2.2)
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_InwardTrial
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

lemma inward_path (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (l : ℕ) (hl : l ≤ G.distanceTo B v) :
    ∃ (y : V) (P : Set E), P.Finite ∧ P.ncard ≤ l ∧
      G.distanceTo B y+l=G.distanceTo B v ∧ y∈G.vertexBall v l ∧
      P⊆G.inducedEdges (G.vertexBall v l∩{z | G.distanceTo B z ≤ G.distanceTo B v}) ∧
      P⊆(G.inducedEdges {z | G.distanceTo B v ≤ G.distanceTo B z})ᶜ ∧
      (G.openGraph P).Reachable v y := by
  induction l generalizing v with
  | zero =>
    exact ⟨v,∅,Set.finite_empty,by simp,by omega,rfl,Set.empty_subset _,Set.empty_subset _,
      SimpleGraph.Reachable.refl _⟩
  | succ l ih =>
    obtain ⟨w,hw,hr⟩ := G.distanceTo_predecessor hc hB v (by omega)
    obtain ⟨y,P,hP,hcard,hy,hyball,hends,hfresh,hreach⟩ := ih w (by omega)
    have hwball : w∈G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hw
    obtain ⟨⟨e,_,he⟩,hne⟩ := hw
    refine ⟨y,insert e P,hP.insert _,?_,by omega,?_,?_,?_,?_⟩
    · exact (Set.ncard_insert_le _ _).trans (by omega)
    · simpa only [Nat.add_comm 1] using G.vertexBall_add hwball l hyball
    · intro f hf z hz
      rcases hf with rfl|hf
      · rw [he] at hz
        have hz' : z=v ∨ z=w := Sym2.mem_iff.mp hz
        rcases hz' with hz'|hz'
        · subst z
          exact ⟨G.mem_vertexBall_self v (l+1),show G.distanceTo B v ≤ G.distanceTo B v from le_rfl⟩
        · subst z
          exact ⟨G.vertexBall_mono v (by omega) hwball,by change G.distanceTo B w ≤ G.distanceTo B v; omega⟩
      · have hh := hends hf z hz
        have hh2 : G.distanceTo B z ≤ G.distanceTo B w := hh.2
        refine ⟨?_,by change G.distanceTo B z ≤ G.distanceTo B v; omega⟩
        simpa only [Nat.add_comm 1] using G.vertexBall_add hwball l hh.1
    · intro f hf hf'
      rcases hf with rfl|hf
      · have hh := hf' w (by rw [he]; simp)
        change G.distanceTo B v ≤ G.distanceTo B w at hh
        omega
      · apply hfresh hf
        intro z hz
        have hh := hf' z hz
        change G.distanceTo B v ≤ G.distanceTo B z at hh
        change G.distanceTo B w ≤ G.distanceTo B z
        omega
    · apply (show (G.openGraph (insert e P)).Adj v w from
          ⟨⟨e,Set.mem_insert e P,he⟩,hne⟩).reachable.trans
      exact hreach.mono (G.openGraph_mono (Set.subset_insert e P))

lemma inward_seed_trial (hc : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    {B : Set V} (hB : B.Nonempty) (v : V) (m : ℕ) (hm : m<G.distanceTo B v) :
    ∃ (y : V) (F : Set E), F.Finite ∧
      F.ncard ≤ m+1+(G.vertexBall y m).ncard ∧
      G.distanceTo B y+(m+1)=G.distanceTo B v ∧
      F⊆G.inducedEdges (G.vertexBall v (2*m+1)∩{z | G.distanceTo B z ≤ G.distanceTo B v}) ∧
      F⊆(G.inducedEdges {z | G.distanceTo B v ≤ G.distanceTo B z})ᶜ ∧
      ∀ z∈G.vertexBall y m, (G.openGraph F).Reachable v z := by
  obtain ⟨y,P,hP,hcard,hy,hyball,hends,hfresh,hreach⟩ := G.inward_path hc hB v (m+1) (by omega)
  obtain ⟨Q,hQ,hQends,hQcard,hQreach⟩ := G.finite_seed_tree hlocal y m
  refine ⟨y,P∪Q,hP.union hQ,?_,hy,?_,?_,?_⟩
  · exact (Set.ncard_union_le P Q).trans (by omega)
  · intro e he z hz
    rcases he with he|he
    · have hh := hends he z hz
      exact ⟨G.vertexBall_mono v (by omega) hh.1,hh.2⟩
    · have hh := hQends he z hz
      have hle := G.distanceTo_ball hc hB hh
      refine ⟨?_,by change G.distanceTo B z ≤ G.distanceTo B v; omega⟩
      have := G.vertexBall_add hyball m hh
      simpa only [show m+1+m=2*m+1 by omega] using this
  · intro e he he'
    rcases he with he|he
    · exact hfresh he he'
    · obtain ⟨⟨x,z⟩,hxz⟩ := Sym2.mk_surjective (G.ends e)
      have hx : x∈G.ends e := by rw [← hxz]; simp
      have hh := G.distanceTo_ball hc hB (hQends he x hx)
      have hh' := he' x hx
      change G.distanceTo B v ≤ G.distanceTo B x at hh'
      omega
  · intro z hz
    exact (hreach.mono (G.openGraph_mono Set.subset_union_left)).trans
      ((hQreach z hz).mono (G.openGraph_mono Set.subset_union_right))

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProductEmbedding
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
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {A E : Type*}

lemma law_map_preimage (q : E → unitInterval) (i : A → E) (hi : Injective i) :
    (law q).map (fun ω : Set E => i ⁻¹' ω)=law (q∘i) := by
  have hind : iIndepFun (fun a (ω : Set E) => i a∈ω) (law q) :=
    iIndepFun.precomp hi (independent_coordinates q)
  have hh := hind.map_fun_eq_infinitePi_map (fun a => measurable_set_mem (i a))
  change (law q).map (fun ω : Set E => i ⁻¹' ω)=_ at hh
  rw [hh]
  rw [law_eq_infinitePi (q∘i)]
  apply congrArg Measure.infinitePi
  funext a
  rw [law_eq_infinitePi]
  exact Measure.infinitePi_map_eval _ (i a)

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SourceGraph
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
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma withSource_local (hl : G.LocallyFinite) {A : Set V} (hA : A.Finite) :
    (G.withSource A).LocallyFinite := by
  intro v
  have hw : (Set.range (Sum.inr : A → E⊕A)).Finite := by
    let := hA.fintype
    exact Set.finite_range _
  cases v with
  | none =>
    apply hw.subset
    intro e he
    cases e with
    | inl e => simp [withSource] at he
    | inr a => exact ⟨a,rfl⟩
  | some v =>
    apply ((hl v).image Sum.inl |>.union hw).subset
    intro e he
    cases e with
    | inl e =>
      apply Or.inl
      refine ⟨e,?_,rfl⟩
      simpa [withSource] using he
    | inr a => exact Or.inr ⟨a,rfl⟩

lemma withSource_original_adj (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w) :
    ((G.withSource A).openGraph ω).Adj (some v) (some w) := by
  obtain ⟨⟨e,he,hend⟩,hne⟩ := h
  exact ⟨⟨Sum.inl e,he,by simp [withSource,hend]⟩,fun h => hne (Option.some.inj h)⟩

lemma withSource_original_reachable (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Reachable v w) :
    ((G.withSource A).openGraph ω).Reachable (some v) (some w) :=
  h.map ⟨Option.some,fun hvw => G.withSource_original_adj A ω hvw⟩

lemma withSource_seedHit [Countable V] [Countable E] (A B T : Set V)
    (q : (E⊕A) → unitInterval) :
    (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent B T) ≤
      (BernoulliProduct.law q).real ((G.withSource A).seedHitEvent (Option.some '' B) (Option.some '' T)) := by
  have hm : Measurable (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω : Set (E⊕A) → Set E) :=
    Measurable.of_eval (fun edge => measurable_set_mem (Sum.inl edge))
  have hlaw : BernoulliProduct.law (fun e => q (Sum.inl e)) =
      (BernoulliProduct.law q).map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) :=
    (BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective).symm
  rw [hlaw,measureReal_def,
    Measure.map_apply hm (G.measurableSet_seedHitEvent B T)]
  change (BernoulliProduct.law q).real ((fun ω => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent B T) ≤ _
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨v,hv,w,hvw,hw⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨some v,⟨v,hv,rfl⟩,some w,
    G.withSource_original_reachable A ω hvw,⟨w,hw,rfl⟩⟩

lemma withSource_incident (A : Set V) {v : V} (hv : v∉A) :
    (G.withSource A).incidentEdges {some v}=Sum.inl '' G.incidentEdges {v} := by
  ext e
  cases e with
  | inl e => simp [incidentEdges,withSource]
  | inr a =>
    have hne : v≠a.val := fun hh => hv (hh.symm ▸ a.property)
    simp [incidentEdges,withSource,hne]

lemma withSource_trial_reachable (A : Set V) (F : Set E) {v w : V}
    (h : (G.openGraph F).Reachable v w) :
    ((G.withSource A).openGraph (Sum.inl '' F)).Reachable (some v) (some w) := by
  apply G.withSource_original_reachable
  simpa only [Set.preimage_image_eq _ Sum.inl_injective] using h

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SourceLift
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
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma withSource_edge_cases (A : Set V) (e : E⊕A) (v w : Option V)
    (he : (G.withSource A).ends e=s(v,w)) :
    (∃ b x y, e=Sum.inl b ∧ v=some x ∧ w=some y ∧ G.ends b=s(x,y)) ∨
    (∃ a : A, e=Sum.inr a ∧ ((v=none ∧ w=some a.val) ∨ (w=none ∧ v=some a.val))) := by
  cases e with
  | inl e =>
    obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
    change s(x,y)=G.ends e at hxy
    have hh : s(some x,some y)=s(v,w) := by simpa [withSource,← hxy] using he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨e,x,y,rfl,hh.1.symm,hh.2.symm,hxy.symm⟩
    · exact Or.inl ⟨e,y,x,rfl,hh.2.symm,hh.1.symm,by simpa only [Sym2.eq_swap] using hxy.symm⟩
  | inr a =>
    right
    refine ⟨a,rfl,?_⟩
    have hh : s(none,some a.val)=s(v,w) := he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨hh.1.symm,hh.2.symm⟩
    · exact Or.inr ⟨hh.1.symm,hh.2.symm⟩

theorem withSource_transfer_from_geometry (hlocal : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (π : V → ℤ) (H : ℤ) (J : Finset ℤ) (hJ : J.Nonempty)
    (hH : ∀ j∈J, j<H) (hAlevel : ∀ a∈A, H ≤ π a)
    (hInput : ∀ j∈J, ∀ v∈Input, π v<j)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q (Sum.inl e) : ℝ) ≤ p)
    (D k M N : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (F : ℤ → V → Set E) (B : ℤ → V → Set V)
    (hF : ∀ j∈J, ∀ v, F j v ⊆ (G.inducedEdges {w | j ≤ π w})ᶜ)
    (hconnect : ∀ j∈J, ∀ v, π v=j → ∀ b∈B j v, (G.openGraph (F j v)).Reachable v b)
    (hdis : ∀ j∈J, ∀ v w, ¬C v w → Disjoint (F j v) (F j w))
    (s₀ K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hs : ∀ j∈J, ∀ v, π v=j → s₀ ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (allOpen (F j v)))
    (hN : K ≤ N*s₀)
    (hmean : ∀ j∈J, ∀ v, π v=j →
      1-η ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent (B j v) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  let π' : Option V → ℤ := Option.elim' H π
  let C' : Option V → Option V → Prop := fun v w => match v,w with
    | none,none => True
    | some v,some w => C v w
    | _,_ => False
  let F' : ℤ → Option V → Set (E⊕A) := fun j => Option.elim' ∅ (fun v => Sum.inl '' F j v)
  let B' : ℤ → Option V → Set (Option V) := fun j => Option.elim' ∅ (fun v => some '' B j v)
  have hvA (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) : v∉A := by
    intro hva
    have := hAlevel v hva
    have := hH j hj
    omega
  have hcross' (j : ℤ) (hj : j∈J) (e : E⊕A) (v w : Option V)
      (he : (G.withSource A).ends e=s(v,w)) (hv : j ≤ π' v) (hw : π' w<j) : π' v=j := by
    rcases G.withSource_edge_cases A e v w he with ⟨b,x,y,rfl,rfl,rfl,hb⟩|⟨a,rfl,hh⟩
    · exact hcross j hj b x y hb hv hw
    · obtain hh|hh := hh
      · obtain ⟨rfl,rfl⟩ := hh
        have := hAlevel a a.property
        have := hH j hj
        change π a<j at hw
        omega
      · obtain ⟨rfl,rfl⟩ := hh
        change H<j at hw
        have := hH j hj
        omega
  have hs' (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) :
      s₀ ≤ (BernoulliProduct.law q).real (allOpen (Sum.inl '' F j v)) := by
    have hm : Measurable (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω : Set (E⊕A) → Set E) :=
      Measurable.of_eval (fun edge => measurable_set_mem (Sum.inl edge))
    have lawproj := BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective
    have heq : allOpen (Sum.inl '' F j v)=(fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' allOpen (F j v) := by
      ext ω
      simp only [allOpen,mem_ofPred_eq,mem_preimage]
      exact Set.image_subset_iff
    rw [heq,measureReal_def,← Measure.map_apply hm ((blockSigma_le _) _ (measurable_allOpen_block (F j v))),lawproj]
    exact hs j hj v hv
  apply (G.withSource A).fresh_collar_transfer_from_geometry (G.withSource_local hlocal hA)
    q π' none (some '' Input) (some '' T) J hJ (fun j hj => (hH j hj).le)
    (by rintro j hj _ ⟨v,hv,rfl⟩; exact hInput j hj v hv) hcross' p hp
    (by
      intro j hj e v w he hv hw
      rcases G.withSource_edge_cases A e v w he with ⟨b,x,y,rfl,rfl,rfl,hb⟩|⟨a,rfl,hh⟩
      · exact hq j hj b x y hb hv hw
      · obtain hh|hh := hh
        · obtain ⟨rfl,rfl⟩ := hh
          change H=j at hv
          have := hH j hj
          omega
        · obtain ⟨rfl,rfl⟩ := hh
          change H<j at hw
          have := hH j hj
          omega)
    D k M N
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v =>
        rw [G.withSource_incident A (hvA j hj v hv),Set.ncard_image_of_injective _ Sum.inl_injective]
        exact hD j hj v hv)
    hM hk C'
    (by intro v; cases v; trivial; exact hrefl _)
    (by intro v w h; cases v <;> cases w <;> simp_all only [C'])
    (by
      intro v
      cases v with
      | none =>
        have he : {w | C' none w}={none} := by ext w; cases w <;> simp [C']
        rw [he]
        exact Set.finite_singleton _
      | some v =>
        have he : {w | C' (some v) w}=some '' {w | C v w} := by ext w; cases w <;> simp [C']
        rw [he]
        exact (hfinite v).image _)
    (by
      intro v
      cases v with
      | none =>
        have he : {w | C' none w}={none} := by ext w; cases w <;> simp [C']
        rw [he,Set.ncard_singleton]
        omega
      | some v =>
        have he : {w | C' (some v) w}=some '' {w | C v w} := by ext w; cases w <;> simp [C']
        rw [he,Set.ncard_image_of_injective _ (Option.some_injective V)]
        exact hbound v)
    F' B'
    (by
      intro j hj v
      cases v with
      | none => exact Set.empty_subset _
      | some v =>
        rintro e ⟨b,hb,rfl⟩ he
        apply hF j hj v hb
        intro z hz
        exact he (some z) (by simpa [withSource] using hz))
    (by
      intro j hj v hv b hb
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v =>
        obtain ⟨z,hz,rfl⟩ := hb
        exact G.withSource_trial_reachable A (F j v) (hconnect j hj v hv z hz))
    (by
      intro j hj v w h
      cases v <;> cases w
      · simp [F']
      · simp [F']
      · simp [F']
      · exact Set.disjoint_image_of_injective Sum.inl_injective (hdis j hj _ _ h))
    s₀ K η lam hK hη hlam
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v => exact hs' j hj v hv)
    hN
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v => exact (hmean j hj v hv).trans (G.withSource_seedHit A (B j v) T q))

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SourceCollarTransfer
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

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem source_distance_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval) (hInput : Input.Nonempty)
    (m R : ℕ) (J : Finset ℤ) (hJ : J.Nonempty)
    (hJrange : ∀ j∈J, (m : ℤ)<j ∧ j ≤ R)
    (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
    (p₀ p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ e∈G.inducedEdges (G.vertexCollar Input R), (p₀ : ℝ) ≤ q (Sum.inl e) ∧ (q (Sum.inl e) : ℝ) ≤ p)
    (D k M N VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hN : K ≤ N*(p₀ : ℝ)^(m+1+VM))
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  let π : V → ℤ := fun v => G.distanceTo Input v
  let Q : Set V := {v | m<G.distanceTo Input v}
  have ht : ∀ v : Q, ∃ (y : V) (F : Set E), F.Finite ∧
      F.ncard ≤ m+1+(G.vertexBall y m).ncard ∧
      G.distanceTo Input y+(m+1)=G.distanceTo Input v ∧
      F⊆G.inducedEdges (G.vertexBall v (2*m+1)∩{z | G.distanceTo Input z ≤ G.distanceTo Input v}) ∧
      F⊆(G.inducedEdges {z | G.distanceTo Input v ≤ G.distanceTo Input z})ᶜ ∧
      ∀ z∈G.vertexBall y m, (G.openGraph F).Reachable v z := by
    intro v
    exact G.inward_seed_trial hc hl hInput v m v.2
  choose y F hfin hcard hy hends hfresh hreach using ht
  let Ft (j : ℤ) (v : V) : Set E := if h : π v=j ∧ v∈Q then F ⟨v,h.2⟩ else ∅
  let Bt (j : ℤ) (v : V) : Set V := if h : π v=j ∧ v∈Q then G.vertexBall (y ⟨v,h.2⟩) m else ∅
  have hlevel (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) : π v=j ∧ v∈Q := by
    refine ⟨hv,?_⟩
    change m<G.distanceTo Input v
    have hh := (hJrange j hj).1
    change (G.distanceTo Input v : ℤ)=j at hv
    omega
  have hsupp (j : ℤ) (v : V) : Ft j v⊆G.inducedEdges (G.vertexBall v (2*m+1)) := by
    dsimp only [Ft]
    split_ifs with h
    · intro e he z hz
      exact (hends ⟨v,h.2⟩ he z hz).1
    · exact Set.empty_subset _
  have hcollar (j : ℤ) (hj : j∈J) (v : V) : Ft j v⊆G.inducedEdges (G.vertexCollar Input R) := by
    dsimp only [Ft]
    split_ifs with h
    · intro e he z hz
      apply (G.distanceTo_le_iff hc hInput z R).mp
      have h1 : G.distanceTo Input z ≤ G.distanceTo Input v := (hends ⟨v,h.2⟩ he z hz).2
      have h2 := (hJrange j hj).2
      have h3 : (G.distanceTo Input v : ℤ)=j := h.1
      omega
    · exact Set.empty_subset _
  apply G.withSource_transfer_from_geometry hl A Input T hA q π (R+1) J hJ
    (by intro j hj; have := (hJrange j hj).2; omega)
    (by
      intro a ha
      have hh : ¬G.distanceTo Input a ≤ R := by
        intro hh
        exact houtside a ha ((G.distanceTo_le_iff hc hInput a R).mp hh)
      change (R : ℤ)+1 ≤ (G.distanceTo Input a : ℤ)
      omega)
    (by
      intro j hj v hv
      have hv0 := (G.distanceTo_eq_zero_iff hc hInput v).mpr hv
      change (G.distanceTo Input v : ℤ)<j
      have := (hJrange j hj).1
      omega)
    (by
      intro j hj e v w he hv hw
      by_cases hvw : v=w
      · subst w; omega
      · have ha : G.fullGraph.Adj w v := ⟨⟨e,Set.mem_univ _,by simpa only [Sym2.eq_swap] using he⟩,Ne.symm hvw⟩
        have hs := G.distanceTo_adj hc hInput ha
        change j ≤ (G.distanceTo Input v : ℤ) at hv
        change (G.distanceTo Input w : ℤ)<j at hw
        change (G.distanceTo Input v : ℤ)=j
        omega)
    p hp
    (by
      intro j hj e v w he hv hw
      apply (hq e ?_).2
      intro z hz
      rw [he] at hz
      have hz' : z=v ∨ z=w := Sym2.mem_iff.mp hz
      apply (G.distanceTo_le_iff hc hInput z R).mp
      have hjR := (hJrange j hj).2
      change (G.distanceTo Input v : ℤ)=j at hv
      change (G.distanceTo Input w : ℤ)<j at hw
      rcases hz' with hz'|hz' <;> subst z <;> omega)
    D k M N (fun _j _hj v _hv => hD v) hM hk
    (fun v w => w∈G.vertexBall v (4*m+2))
    (fun v => G.mem_vertexBall_self v _) (fun {_ _} h => G.vertexBall_comm.mp h)
    (fun v => G.vertexBall_finite hl v _) hMbound Ft Bt
    (by
      intro j hj v
      dsimp only [Ft]
      split_ifs with h
      · intro e he he'
        apply hfresh ⟨v,h.2⟩ he
        intro z hz
        have hh := he' z hz
        change j ≤ (G.distanceTo Input z : ℤ) at hh
        have hv : (G.distanceTo Input v : ℤ)=j := h.1
        change G.distanceTo Input v ≤ G.distanceTo Input z
        omega
      · exact Set.empty_subset _)
    (by
      intro j hj v hv b hb
      have hh := hlevel j hj v hv
      dsimp only [Bt] at hb
      rw [dite_eq_left hh] at hb
      dsimp only [Ft]
      rw [dite_eq_left hh]
      exact hreach ⟨v,hh.2⟩ b hb)
    (by
      intro j hj v w h
      exact G.inward_trials_disjoint (Ft j) m (hsupp j) h)
    ((p₀ : ℝ)^(m+1+VM)) K η lam hK hη hlam
    (by
      intro j hj v hv
      have hh := hlevel j hj v hv
      have hFfinite : (Ft j v).Finite := by simpa only [Ft,dite_eq_left hh] using hfin ⟨v,hh.2⟩
      apply law_allOpen_lower (fun e => q (Sum.inl e)) (Ft j v) hFfinite p₀ (m+1+VM)
      · rw [show Ft j v=F ⟨v,hh.2⟩ by simp only [Ft,dite_eq_left hh]]
        exact (hcard ⟨v,hh.2⟩).trans (by have := hVM (y ⟨v,hh.2⟩); omega)
      · intro e he
        exact (hq e (hcollar j hj v he)).1)
    hN
    (by
      intro j hj v hv
      have hh := hlevel j hj v hv
      dsimp only [Bt]
      rw [dite_eq_left hh]
      apply hmean
      apply (G.distanceTo_le_iff hc hInput _ R).mp
      have h1 := hy ⟨v,hh.2⟩
      change G.distanceTo Input (y ⟨v,hh.2⟩)+(m+1)=G.distanceTo Input v at h1
      have h2 := (hJrange j hj).2
      change (G.distanceTo Input v : ℤ)=j at hv
      omega)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FreshRegionLaw
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

lemma trim_law_eq (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e) :
    (law q).map (forceOn Sᶜ ∅)=(law r).map (forceOn Sᶜ ∅) := by
  rw [forceOn_map_law,forceOn_map_law]
  congr 1
  funext e
  by_cases he : e∈S
  · simp [pinnedParameters,he,h e he]
  · simp [pinnedParameters,he]

lemma fresh_region_lower (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e)
    (B : Set (Set E)) (hm : MeasurableSet B) (hu : IsUpperSet B) :
    (law r).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ (law q).real B := by
  have he : (law r) ((forceOn Sᶜ ∅) ⁻¹' B)=(law q) ((forceOn Sᶜ ∅) ⁻¹' B) := by
    rw [← Measure.map_apply (measurable_forceOn _ _) hm,
      ← Measure.map_apply (measurable_forceOn _ _) hm,trim_law_eq q r S h]
  rw [measureReal_def,he]
  change (law q).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ _
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  apply hu (a := forceOn Sᶜ ∅ ω) (b := ω) ?_ hω
  intro e he
  by_cases hes : e∈S
  · simpa [forceOn,hes] using he
  · simp [hes] at he

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshCollarExact
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

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fresh_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (m R : ℕ) (hcR : m<R) (Dstar : Set E)
    (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
    (hregion : G.inducedEdges (G.vertexCollar Input R)⊆Dstar)
    (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ e∈Dstar, q (Sum.inl e)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hη₀ : 0≤η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
        ((forceOn Dstarᶜ ∅) ⁻¹' G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤ κ := by
  by_cases hI : Input.Nonempty
  · let p₀ : unitInterval := ⟨(pc : ℝ)/2,by constructor <;> linarith [pc.2.1,pc.2.2]⟩
    let J : Finset ℤ := Finset.Icc ((m : ℤ)+1) (R : ℤ)
    have hJ : J.Nonempty := Finset.nonempty_Icc.mpr (by omega)
    have hJcard : (J.card : ℝ)=(R : ℝ)-m := by
      have hjc : J.card=R-m := by
        change (Finset.Icc ((m : ℤ)+1) (R : ℤ)).card=R-m
        rw [Int.card_Icc]
        omega
      rw [hjc,Nat.cast_sub hcR.le]
    have hK : 0 ≤ Real.log (4/κ) := Real.log_nonneg ((le_div_iff₀ hκ).mpr (by linarith))
    have hs : 0<((pc : ℝ)/2)^(m+1+VM) := positive_trial_power _ hpc₀ _ _
    have hh := G.source_distance_collar_transfer hc hl A Input T hA q hI m R J hJ
      (by intro j hj; have hh := Finset.mem_Icc.mp hj; omega) houtside p₀ pc hpc
      (by
        intro e he
        rw [hq e (hregion he)]
        exact ⟨hpp,hppc⟩)
      D k M ⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ VM hD hM hk hMbound hVM
      (Real.log (4/κ)) η (κ/4) hK hη₀ (by linarith)
      (trial_ceiling_budget _ _ hs)
      (by
        intro y hy
        exact (hmean y hy).trans (fresh_region_lower (fun e => q (Sum.inl e))
          (fun _ => p') Dstar hq _ (G.measurableSet_seedHitEvent _ _)
          (G.seedHitEvent_upper _ _)))
    rw [hJcard] at hh
    exact hh.trans (collar_error_budget κ η ((R : ℝ)-m) _ hκ hκ1 hη
      (pow_pos (by linarith) _) hR)
  · have he : Input=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    subst Input
    have he : (G.withSource A).hitEvent none (some '' (∅ : Set V))=∅ := by
      ext ω
      simp [hitEvent]
    rw [he,Set.empty_sdiff,measureReal_empty]
    exact hκ.le

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayGeometry
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

namespace CriticalPercolation.Relay

lemma width_lower (i : ℕ) : 2 ≤ width i := le_max_left _ _
lemma width_upper (i : ℕ) : width i ≤ 210 := by
  apply max_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) i]
lemma width_next (i : ℕ) : width i ≤ width (i+1)+1/2 := by
  have h1 := width_lower (i+1)
  have h2 : 210-((i+1 : ℕ) : ℝ)/2 ≤ width (i+1) := le_max_right _ _
  unfold width at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  exact max_le (by linarith) (by linarith)
lemma width_last (L : ℕ) (hL : 416 ≤ L) : width L=2 := by
  apply max_eq_left
  have : (416 : ℝ) ≤ L := by exact_mod_cast hL
  linarith

lemma selectedSign_cases (u : ℝ) : selectedSign u=-1 ∨ selectedSign u=1 := by
  unfold selectedSign
  split  <;>  simp

lemma selectedSign_abs (u : ℝ) : |selectedSign u|=1 := by
  rcases selectedSign_cases u with h|h  <;>  rw [h]  <;>  norm_num

lemma move_towards_axis (u b : ℝ) (hu : |u| ≤ b) :
    |u+selectedSign u| ≤ max 1 (b-1) := by
  rw [abs_le] at hu ⊢
  have h1 : 1 ≤ max 1 (b-1) := le_max_left _ _
  have h2 : b-1 ≤ max 1 (b-1) := le_max_right _ _
  unfold selectedSign
  split  <;>  constructor  <;>  linarith

lemma full_step_height (i : ℕ) (u σ d e ε : ℝ) (hσ : |σ|=1)
    (hu : |u| ≤ width i+d) (hd₀ : 0 ≤ d) (hd : d+e/4 ≤ 1/4)
    (hε : |ε| ≤ e/4) :
    |u+selectedSign u-σ/4+ε| ≤ width (i+1) := by
  have h1 := width_lower (i+1)
  have h2 := width_next i
  have hs : |σ/4|=1/4 := by rw [abs_div,hσ]; norm_num
  calc
    _  ≤  |u+selectedSign u|+|σ/4|+|ε| :=
      by linarith [abs_add_le (u+selectedSign u-σ/4) ε, abs_sub (u+selectedSign u) (σ/4)]
    _  ≤  max 1 (width i+d-1)+1/4+e/4 := by
      rw [hs]
      linarith [move_towards_axis u (width i+d) hu]
    _  ≤  width (i+1) := by
      rcases le_total 1 (width i+d-1) with hh|hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith

lemma full_step_time (i : ℕ) (y z d e : ℝ)
    (hy : |y-(i : ℝ)| ≤ (i+1)*e+d) (hz : |z-(y+1)| ≤ e/4)
    (hde : d+e/4 ≤ e) : |z-((i+1 : ℕ) : ℝ)| ≤ (i+2)*e := by
  rw [abs_le] at hy hz ⊢
  push_cast
  constructor  <;>  nlinarith

lemma path_axis_bound (L i : ℕ) (hi : i ≤ L) (y x : ℝ×ℝ) (d e σ : ℝ)
    (hσ : |σ|=1) (he : 0 ≤ e)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    |x.2-σ*x.1/4| ≤ 210+d+100+((L+1)*e+d+100)/4 := by
  have ht : |x.1-(i : ℝ)| ≤ (L+1)*e+d+100 := by
    have hc : (i : ℝ) ≤ L := by exact_mod_cast hi
    calc
      _  ≤  |x.1-y.1|+|y.1-(i : ℝ)| := abs_sub_le _ _ _
      _  ≤  100+((i+1)*e+d) := add_le_add hxt hyt
      _  ≤  _ := by nlinarith
  have hsame : σ*(i : ℝ)/4-σ*x.1/4=σ*((i : ℝ)-x.1)/4 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(i : ℝ)/4|+|σ*(i : ℝ)/4-σ*x.1/4| := by
      linarith [abs_sub_le x.2 (σ*(i : ℝ)/4) (σ*x.1/4),
        abs_sub_le x.2 y.2 (σ*(i : ℝ)/4)]
    _  ≤  100+(width i+d)+((L+1)*e+d+100)/4 := by
      rw [hsame,abs_div,abs_mul,hσ,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4),abs_sub_comm (i : ℝ)]
      exact add_le_add (add_le_add hxz hyz) (div_le_div_of_nonneg_right ht (by norm_num))
    _  ≤  _ := by linarith [width_upper i]

lemma band_mem_domain (J T σ : ℝ) (hσ : |σ|=1)
    (x : ℝ×ℝ) (ht : -J ≤ x.1 ∧ x.1 ≤ T+J)
    (hz : |x.2-σ*x.1/4| ≤ 630) : x∈domain J T σ := by
  have ha : |σ|=1 := hσ
  by_cases h0 : x.1 < 0
  · apply Or.inl; apply Or.inl
    have hx : |x.1| ≤ J := by rw [abs_of_neg h0]; linarith [ht.1]
    refine ⟨hx,?_⟩
    calc
      |x.2|  ≤  |x.2-σ*x.1/4|+|σ*x.1/4| := by simpa using abs_sub_le x.2 (σ*x.1/4) 0
      _  ≤  630+J/4 := by
        rw [abs_div,abs_mul,ha,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        exact add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
      _ = _ := add_comm _ _
  · by_cases h1 : T < x.1
    · apply Or.inl; apply Or.inr
      have hx : |x.1-T| ≤ J := by rw [abs_of_pos (by linarith)]; linarith [ht.2]
      refine ⟨hx,?_⟩
      calc
        _  ≤  |x.2-σ*x.1/4|+|σ*x.1/4-σ*T/4| := abs_sub_le _ _ _
        _ = |x.2-σ*x.1/4|+|x.1-T|/4 := by
          rw [show σ*x.1/4-σ*T/4=σ*(x.1-T)/4 by ring,abs_div,abs_mul,ha,one_mul]
          norm_num
        _  ≤  630+J/4 := add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
        _ = _ := add_comm _ _
    · exact Or.inr ⟨by linarith,by linarith,hz⟩

lemma move_path_contained (J : ℝ) (L i : ℕ) (hi : i ≤ L) (hJ : 26200 < J)
    (y x : ℝ×ℝ) (d e σ : ℝ) (hσ : |σ|=1) (he : 0 ≤ e)
    (hsmall : (L+1)*e+d < 1)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    x∈domain J (L+1/2) σ := by
  have hi' : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hi₀ : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have heL : 0 ≤ (L+1)*e := mul_nonneg (by positivity) he
  apply band_mem_domain J (L+1/2) σ hσ x
  · rw [abs_le] at hyt hxt
    constructor  <;>  nlinarith
  · exact (path_axis_bound L i hi y x d e σ hσ he hyt hyz hxt hxz).trans (by linarith)

lemma last_crossing_height (L : ℕ) (y x : ℝ×ℝ) (d σ : ℝ) (hσ : |σ|=1)
    (hy : |y.2-σ*(L : ℝ)/4| ≤ 2+d) (hx : |x.2-y.2| ≤ 100) (hd : d < 1) :
    |x.2-σ*(L+1/2)/4| < 210 := by
  have he : σ*(L : ℝ)/4-σ*(L+1/2)/4=-σ/8 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(L : ℝ)/4|+|σ*(L : ℝ)/4-σ*(L+1/2)/4| :=
      by linarith [abs_sub_le x.2 (σ*(L : ℝ)/4) (σ*(L+1/2)/4),
        abs_sub_le x.2 y.2 (σ*(L : ℝ)/4)]
    _  ≤  100+(2+d)+1/8 := by
      rw [he,abs_div,abs_neg,hσ]
      norm_num
      linarith
    _  <  _ := by linarith

end CriticalPercolation.Relay
namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma exists_first_crossing (f : V → ℝ) (ρ T : ℝ)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y| ≤ ρ)
    {a b : V} (w : H.Walk a b) (ha : f a < T) (hb : T ≤ f b) :
    ∃ x∈w.support, T ≤ f x ∧ f x ≤ T+ρ := by
  induction w with
  | nil =>  exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T ≤ f c
    · refine ⟨c,?_,hc,?_⟩
      · simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr w.start_mem_support
      · have hh := hf hac
        rw [abs_le] at hh
        linarith
    · obtain ⟨x,hx,h1,h2⟩ := ih (lt_of_not_ge hc) hb
      exact ⟨x,by simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx,h1,h2⟩
end SimpleGraph.Walk
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayMoves
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

lemma walk_reachable_induced (S : Set V) (ω : Set E) {a b : V}
    (w : (G.openGraph ω).Walk a b) (hw : ∀ x∈w.support,x∈S) :
    (G.openGraph (ω∩G.inducedEdges S)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac w ih =>
    have hc : c∈S := hw c (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr w.start_mem_support)
    have ha : a∈S := hw a (by simp)
    exact ((G.open_induced_adj S ω a c).mpr ⟨hac,ha,hc⟩).reachable.trans
      (ih (fun x hx => hw x (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx)))

lemma relay_collar_bounds (t z : V → ℝ) (σ e ρ : ℝ) (hρ : 0 ≤ ρ)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (R i : ℕ) {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    |t y-(i : ℝ)| ≤ (i+1)*e+R*ρ ∧ |z y-σ*(i : ℝ)/4| ≤ Relay.width i+R*ρ := by
  exact ⟨G.coordinate_collar_bound t ρ hρ ht _ _ _ (fun _ h => h.1) hy,
    G.coordinate_collar_bound z ρ hρ hz _ _ _ (fun _ h => h.2) hy⟩

lemma full_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i<L) (hsmall : (L+1)*e+R*ρ<1)
    (hheight : R*ρ+e/4 ≤ 1/4) (htime : R*ρ+e/4 ≤ e)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    coordinateMove G t z m e y (Relay.selectedSign (z y-σ*(i : ℝ)/4)) ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1))} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,hbz⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  have hb : b∈relayRegion t z σ e (i+1) := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        Relay.full_step_time i (t y) (t b) (R*ρ) e hy'.1 hbt htime
    have hh := Relay.full_step_height i (z y-σ*(i : ℝ)/4) σ (R*ρ) e
      (z b-(z y+Relay.selectedSign (z y-σ*(i : ℝ)/4))) hσ hy'.2
      (mul_nonneg (Nat.cast_nonneg _) hρ) hheight hbz
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    push_cast
    ring_nf
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,b,G.walk_reachable_induced _ ω w ?_,hb⟩
  intro x hx
  exact Relay.move_path_contained J L i hi.le hJ (t y,z y) (t x,z x)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 (hw x hx).1 (hw x hx).2

lemma last_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hL : 416 ≤ L) (hsmall : (L+1)*e+(R+m)*ρ+e/4<1/2)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e L) R) (s : ℝ) :
    coordinateMove G t z m e y s ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ)} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,_⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R L hy
  have hma : |t a-t y| ≤ m*ρ := G.coordinate_ball_bound t ρ hρ ht ha
  have hnR : 0 ≤ (R : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnm : 0 ≤ (m : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnL : 0 ≤ (L+1 : ℝ)*e := mul_nonneg (by positivity) he
  have hyt := abs_le.mp hy'.1
  have hbt' := abs_le.mp hbt
  have hma' := abs_le.mp hma
  have haT : t a<L+1/2 := by linarith
  have hbT : (L : ℝ)+1/2 ≤ t b := by linarith
  have hadj : ∀ ⦃u v⦄, (G.openGraph ω).Adj u v → |t u-t v| ≤ ρ :=
    fun _ _ h => ht (G.openGraph_mono (Set.subset_univ _) h)
  obtain ⟨x,hx,hx₁,hx₂⟩ := _root_.OAI.SimpleGraph.Walk.exists_first_crossing t ρ (L+1/2) hadj w haT hbT
  have hxz : |z x-σ*(L+1/2)/4|<210 := by
    apply Relay.last_crossing_height L (t y,z y) (t x,z x) (R*ρ) σ hσ
    · simpa only [Relay.width_last L hL] using hy'.2
    · exact (hw x hx).2
    · linarith
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,?_,⟨hx₁,hx₂,hxz.le⟩⟩
  apply G.walk_reachable_induced _ ω (w.takeUntil x hx)
  intro v hv
  have hv' : v∈w.support := (w.isSubwalk_takeUntil hx).support_subset hv
  apply Relay.move_path_contained J L L le_rfl hJ (t y,z y) (t v,z v)
    (R*ρ) e σ hσ he _ hy'.1 hy'.2 (hw v hv').1 (hw v hv').2
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_RelayScales
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
variable {V E : Type*} (G : BondGraph V E)

lemma vertexCollar_mono {S T : Set V} (hST : S⊆T) (R : ℕ) :
    G.vertexCollar S R⊆G.vertexCollar T R := by
  intro y hy
  obtain ⟨v,hv,hy⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_iUnion₂.mpr ⟨v,hST hv,hy⟩

lemma initial_mark_subset_relay (t z : V → ℝ) (σ e ρ : ℝ) (hρ : ρ ≤ e) :
    relayMark t z 0 σ ρ⊆relayRegion t z σ e 0 := by
  intro v hv
  obtain ⟨ht₀,ht₁,hz⟩ := hv
  change |t v-(0:ℕ)| ≤ ((0:ℕ)+1)*e ∧ |z v-σ*(0:ℕ)/4| ≤ Relay.width 0
  norm_num [Relay.width] at ht₀ ht₁ hz ⊢
  exact ⟨by rw [abs_of_nonneg ht₀]; linarith,hz⟩

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

lemma relay_collar_in_domain (t z : V → ℝ) (σ e ρ J : ℝ) (L R i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i ≤ L) (hsmall : (L+1)*e+R*ρ<1)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ) :
    G.vertexCollar (relayRegion t z σ e i) R⊆relayDomain t z J (L+1/2) σ := by
  intro y hy
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  apply Relay.move_path_contained J L i hi hJ (t y,z y) (t y,z y)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 <;> norm_num

lemma forceOutside_induced (S : Set V) (ω : Set E) :
    BernoulliProduct.forceOn (G.inducedEdges S)ᶜ ∅ ω=ω∩G.inducedEdges S := by
  ext b
  by_cases hb : b∈G.inducedEdges S <;> simp [hb]

lemma corridorRelay_subset (t z : V → ℝ) (σ e ρ : ℝ) (hρe : ρ ≤ e)
    (L i : ℕ) (hi : i ≤ L) : corridorRelay t z σ e ρ L i⊆relayRegion t z σ e i := by
  by_cases h0 : i=0
  · subst i
    simpa [corridorRelay] using initial_mark_subset_relay t z σ e ρ hρe
  · simp only [corridorRelay,ite_eq_right h0,ite_eq_left hi,Subset.rfl]

theorem coordinate_moves_relay_estimates (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (p : unitInterval) (η : ℝ)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
      (G.coordinateMove t z m e y s)) :
    ∀ i ≤ L,
      G.vertexCollar (corridorRelay t z σ e ρ L i) R⊆relayDomain t z J (L+1/2) σ ∧
      ∀ y∈G.vertexCollar (corridorRelay t z σ e ρ L i) R,
        1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
          ((BernoulliProduct.forceOn (G.inducedEdges (relayDomain t z J (L+1/2) σ))ᶜ ∅) ⁻¹'
            G.seedHitEvent (G.vertexBall y m) (corridorRelay t z σ e ρ L (i+1))) := by
  obtain ⟨hρe,hsmall,hheight,htime,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  intro i hi
  have hsub := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R
  refine ⟨hsub.trans (G.relay_collar_in_domain t z σ e ρ J L R i hσ he.le hρ hJ hi hsmall ht hz),?_⟩
  intro y hy
  apply (hmove y (Relay.selectedSign (z y-σ*(i:ℝ)/4)) (Relay.selectedSign_abs _)).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_preimage,G.forceOutside_induced]
  by_cases hiL : i<L
  · have hh := G.full_relay_move t z σ e ρ J L R m i hσ he.le hρ hJ hiL hsmall
      hheight htime ht hz (hsub hy) hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1)) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,if_false,ite_eq_left (by omega : i+1 ≤ L)] using hh
  · have hiEq : i=L := by omega
    subst i
    have hh := G.last_relay_move t z σ e ρ J L R m hσ he.le hρ hJ hL hlast ht hz
      (hsub hy) _ hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,if_false,ite_eq_right (by omega : ¬L+1 ≤ L)] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SourceRelaySeparation
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma source_outside_relay_collar (t z : V → ℝ) (σ e ρ P : ℝ) (L R m i : ℕ)
    (he : 0<e) (hρ : 0 ≤ ρ) (hi : i ≤ L) (hPi : 1 ≤ P+i)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {a : V} (ha : t a ≤ m*ρ-P) :
    a∉G.vertexCollar (corridorRelay t z σ e ρ L i) R := by
  intro hin
  obtain ⟨hρe,_,_,_,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  have hs := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R hin
  have hb := (G.relay_collar_bounds t z σ e ρ hρ ht hz R i hs).1
  have hi' : (i:ℝ) ≤ L := by exact_mod_cast hi
  have hile : (i+1)*e ≤ (L+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
  have hb' := (abs_le.mp hb).1
  nlinarith

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

lemma relay_failure_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ : ℝ) (N : ℕ)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A 0\A N) ≤ N*κ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsub : A 0\A (N+1) ⊆ (A 0\A N)∪(A N\A (N+1)) := by
      intro ω hω
      by_cases hn : ω∈A N
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    calc
      _ ≤ μ.real ((A 0\A N)∪(A N\A (N+1))) := measureReal_mono hsub
      _ ≤ μ.real (A 0\A N)+μ.real (A N\A (N+1)) := measureReal_union_le _ _
      _ ≤ N*κ+κ := add_le_add (ih (fun i hi => h i (by omega))) (h N (by omega))
      _ = _ := by push_cast; ring

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshCorridor
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem coordinate_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource A).hitEvent none (some '' relayMark t z 0 σ ρ)\
        (G.withSource A).hitEvent none (some '' relayMark t z (L+1/2) σ ρ)) ≤ (L+1)*κ := by
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L i)
  have hh := relay_failure_bound (BernoulliProduct.law q) H κ (L+1) (by
    intro i hi
    have hiL : i ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove i hiL
    apply G.fresh_collar_transfer hc hl A _ _ hA q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ P L R m i he hρ hiL
        (by linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz (hsource a ha))
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean)
  simpa [H,corridorRelay,show ¬L+1 ≤ L by omega] using hh

end CriticalPercolation.BondGraph
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

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_SourceConnectivity
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
variable {V E : Type*} (G : BondGraph V E)

lemma withSource_reachable_from_seed (A : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) {v : V}
    (hv : ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) :
    ((G.withSource A).openGraph ω).Reachable none (some v) := by
  obtain ⟨a,ha,hav⟩ := hv
  have hh : ((G.withSource A).openGraph ω).Adj none (some a) :=
    ⟨⟨Sum.inr ⟨a,ha⟩,hw ⟨a,ha⟩,rfl⟩,by simp⟩
  exact hh.reachable.trans (G.withSource_original_reachable A ω hav)

lemma withSource_reachable_to_seed (A : Set V) (ω : Set (E⊕A)) {v : V}
    (hv : ((G.withSource A).openGraph ω).Reachable none (some v)) :
    ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v := by
  have hi : ∀ w, ((G.withSource A).openGraph ω).Reachable none w →
      Option.elim' True (fun v => ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) w := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => trivial
    | @tail u w hr huw ih =>
      obtain ⟨⟨b,hb,hend⟩,hne⟩ := huw
      cases w with
      | none => trivial
      | some w =>
        rcases G.withSource_edge_cases A b u (some w) hend with
          ⟨b,v,w',rfl,rfl,hw',hb'⟩|⟨a,rfl,hh⟩
        · have he : w'=w := Option.some.inj hw'.symm
          subst w'
          obtain ⟨a,ha,hav⟩ := ih
          refine ⟨a,ha,hav.trans ?_⟩
          exact (show (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w from
            ⟨⟨b,hb,hb'⟩,fun h => hne (congrArg some h)⟩).reachable
        · rcases hh with ⟨rfl,hh⟩|⟨hh,_⟩
          · have he : w=a.val := Option.some.inj hh
            exact ⟨a.val,a.property,he.symm ▸ SimpleGraph.Reachable.refl _⟩
          · simp at hh
  exact hi (some v) hv

lemma source_hit_iff_seedHit (A T : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) :
    ω∈(G.withSource A).hitEvent none (some '' T) ↔
      Sum.inl ⁻¹' ω∈G.seedHitEvent A T := by
  constructor
  · rintro ⟨w,hr,v,hv,rfl⟩
    obtain ⟨a,ha,hav⟩ := G.withSource_reachable_to_seed A ω hr
    exact Set.mem_iUnion₂.mpr ⟨a,ha,v,hav,hv⟩
  · intro h
    obtain ⟨a,ha,v,hav,hv⟩ := Set.mem_iUnion₂.mp h
    exact ⟨some v,G.withSource_reachable_from_seed A ω hw ⟨a,ha,hav⟩,v,hv,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_SourceEventLaw
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

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable E] in
lemma source_hit_ae_seed (A T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    (G.withSource A).hitEvent none (some '' T) =ᵐ[BernoulliProduct.law q]
      ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,law_coordinate,hq a]
    simp [bitMeasure]
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  exact propext (G.source_hit_iff_seedHit A T ω hω)

lemma source_hit_diff_probability (A B T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹'
        (G.seedHitEvent A B\G.seedHitEvent A T)) := by
    apply measure_congr
    filter_upwards [G.source_hit_ae_seed A B q hq,G.source_hit_ae_seed A T q hq] with ω hB hT
    exact propext (and_congr (eq_iff_iff.mp hB) (not_congr (eq_iff_iff.mp hT)))
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' _)=_
  rw [← Measure.map_apply (Measurable.of_eval (fun bond => measurable_set_mem (Sum.inl bond)))
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) _=_
  rw [law_map_preimage q Sum.inl Sum.inl_injective]
  rfl

lemma restricted_seed_diff_probability (A B T : Set V) (q : E → unitInterval) (R : Set E) :
    BernoulliProduct.law q (G.restrictedSeed A B R\G.restrictedSeed A T R)=
      BernoulliProduct.law (pinnedParameters q Rᶜ ∅) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn _ _)
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  congr 1
  have he (ω : Set E) : forceOn Rᶜ ∅ ω=ω∩R := by
    ext e
    by_cases he : e∈R <;> simp [he]
  ext ω
  simp only [Set.mem_sdiff,Set.mem_preimage,restrictedSeed,Set.mem_ofPred_eq,he]

lemma restricted_seed_diff_le_source (A B T : Set V) (q : E → unitInterval)
    (I F R σ : Set E) (hFR : F⊆R) :
    (blockProbability q I (G.restrictedSeed A B F\G.restrictedSeed A T R) σ).toReal ≤
      (BernoulliProduct.law (Sum.elim (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)
        (fun _ : A => 1))).real
        ((G.withSource A).hitEvent none (some '' B)\(G.withSource A).hitEvent none (some '' T)) := by
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((G.restrictedSeed_measurable _ _ _).diff (G.restrictedSeed_measurable _ _ _))]
  rw [measureReal_def,G.source_hit_diff_probability A B T _ (fun _ => rfl)]
  change (BernoulliProduct.law (pinnedParameters q I σ)).real _ ≤
    (BernoulliProduct.law (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)).real _
  rw [measureReal_def,measureReal_def,← G.restricted_seed_diff_probability]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  exact Set.sdiff_subset_sdiff_left (G.restrictedSeed_mono A B hFR)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ProspectiveCorridor
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
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem coordinate_pinned_corridor_failure_bs_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : E → unitInterval)
    (I F U ω : Set E) (hFU : F⊆U)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q b=p')
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hfresh : Disjoint I (G.inducedEdges (relayDomain t z J (L+1/2) σ)))
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.blockProbability q I
      (G.restrictedSeed A (relayMark t z 0 σ ρ) F\
        G.restrictedSeed A (relayMark t z (L+1/2) σ ρ) U) ω).toReal ≤ (L+1)*κ := by
  let r : E → unitInterval := pinnedParameters (pinnedParameters q I ω) Uᶜ ∅
  let q' : (E⊕A) → unitInterval := Sum.elim r (fun _ => 1)
  have hq' : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q' (Sum.inl b)=p' := by
    intro b hb
    have hbU := hDU hb
    have hbI : b∉I := fun hi => Set.disjoint_left.mp hfresh hi hb
    simpa [q',r,pinnedParameters,hbU,hbI] using hq b hb
  exact (G.restricted_seed_diff_le_source A _ _ q I F U ω hFU).trans
    (G.coordinate_corridor_failure hc hl A hA q' t z σ e ρ J P L R m
      hσ he hρ hJ hL heL hr hP hsource ht hz hcR pc p' hpc₀ hpc hpp hppc hq'
      D k M VM hD hM hMbound hVM κ η hκ hκ1 hη₀ hη hk hR hmove)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs_oai.{u_1, u_2}
