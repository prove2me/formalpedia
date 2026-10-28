-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:44:29.901734+00:00
-- url     : https://prove2.me/submissions/3dad471d-7bae-4678-9fb3-f92cca0b9a1d

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_expected_heavy_normalizedDiscrepancy_bound_bs

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

lemma force_singleton_preimage_null (q : E → unitInterval) (e : E) (σ : Set E)
    (hb : bitMeasure (q e) {e ∈ σ} ≠ 0)
    (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q (forceOn {e} σ ⁻¹' A) = 0 := by
  let B := forceOn {e} σ ⁻¹' A
  let C := {ω : Set E | (e ∈ ω) = (e ∈ σ)}
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e ∈ σ}, MeasurableSet.singleton _, rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e ≤ blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (measurable_forceOn_block {e} σ)
  have hmul := ((independent_blocks q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have hsub : C ∩ B ⊆ A := by
    intro ω hω
    have heq : forceOn {e} σ ω = ω := by
      ext f
      change (if f ∈ ({e} : Set E) then f ∈ σ else f ∈ ω) ↔ f ∈ ω
      by_cases hf : f = e
      · subst f
        simpa only [Set.mem_singleton_iff, ↓reduceIte] using (Iff.of_eq hω.1.symm)
      · simp only [Set.mem_singleton_iff, ite_eq_right hf]
    have hh : forceOn {e} σ ω ∈ A := hω.2
    rwa [heq] at hh
  have hz : law q (C ∩ B) = 0 := measure_mono_null hsub hnull
  rw [hz, law_coordinate] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_left hb

lemma bitMeasure_true_ne_zero (p : unitInterval) (hp : (0:ℝ) < p) :
    bitMeasure p {True} ≠ 0 := by
  have hh := bitMeasure_real_singleton p True
  simp only [bitWeight, if_true] at hh
  intro hz
  have : (bitMeasure p).real {True} = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hh] at this
  exact (ne_of_gt hp) this

lemma insert_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (e : E) (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q ((fun ω => insert e ω) ⁻¹' A) = 0 := by
  have hh := force_singleton_preimage_null q e Set.univ (bitMeasure_true_ne_zero (q e) (hq e))
    A hA hnull
  have heq : forceOn {e} Set.univ = (fun ω : Set E => insert e ω) := by
    funext ω
    ext f
    change (if f ∈ ({e} : Set E) then True else f ∈ ω) ↔ (f = e ∨ f ∈ ω)
    simp only [Set.mem_singleton_iff]
    split_ifs <;> tauto
  rwa [heq] at hh

lemma measurable_union_left (S : Set E) : Measurable (fun ω : Set E => S ∪ ω) :=
  Measurable.of_eval (fun edge => measurable_const.or (measurable_set_mem edge))

lemma finite_union_preimage_null (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (S : Set E) (hS : S.Finite) (A : Set (Set E)) (hA : MeasurableSet A)
    (hnull : law q A = 0) : law q ((fun ω => S ∪ ω) ⁻¹' A) = 0 := by
  induction S,hS using Set.Finite.induction_on generalizing A with
  | empty =>
    have hh : (fun ω : Set E => (∅ : Set E) ∪ ω) = id := funext (fun _ => Set.empty_union _)
    rw [hh,Set.preimage_id_eq]
    exact hnull
  | @insert e S he hS ih =>
    have hi := insert_preimage_null q hq e A hA hnull
    have hm : Measurable (fun ω : Set E => insert e ω) := by
      simpa only [Set.singleton_union] using measurable_union_left ({e} : Set E)
    have hh := ih ((fun ω => insert e ω) ⁻¹' A) (hA.preimage hm) hi
    simpa only [Set.preimage_preimage,Function.comp_def,Set.insert_union] using hh

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_FiniteForcing
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma forceOn_empty_eq_sdiff (S ω : Set E) : forceOn S ∅ ω = ω \ S := by
  classical
  ext e
  show (if e∈S then e∈(∅ : Set E) else e∈ω) ↔ _
  split_ifs <;> simp_all

end CriticalPercolation.BernoulliProduct
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

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

lemma measurable_infinite_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.measurable_cluster v)).eq_const ⊤

theorem measurableSet_percolates [Countable V] [Countable E] :
    MeasurableSet G.percolates := by
  exact (Measurable.exists fun v => G.measurable_infinite_cluster v).setOf

lemma law_zero_percolates [Countable V] [Countable E] : G.law 0 G.percolates = 0 := by
  rw [law, ProbabilityTheory.setBernoulli_zero,
    Measure.dirac_apply' _ G.measurableSet_percolates]
  simp

lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp

lemma law_percolates_eq_zero_of_lt_critical {p : unitInterval}
    (hp : p < G.criticalProbability) : G.law p G.percolates = 0 := by
  by_contra h
  exact (not_le_of_gt hp) (G.criticalProbability_le_of_pos (pos_iff_ne_zero.mpr h))

lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Link
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

namespace CriticalPercolation
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)

lemma link_refl (s b u : V) : link H s b u u := Or.inl (.refl _)

lemma link_trans {s b u v z : V} : link H s b u v → link H s b v z → link H s b u z := by
  rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩) (k | ⟨k1,k2⟩ | ⟨k1,k2⟩)
  · exact Or.inl (h.trans k)
  · exact Or.inr (Or.inl ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inr ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inl ⟨h1,h2.trans k⟩)
  · exact Or.inr (Or.inl ⟨h1,k2⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,h2.trans k⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,k2⟩)

lemma edge_reachable (s b : V) : (SimpleGraph.edge s b).Reachable s b := by
  rcases eq_or_ne s b with rfl | h
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,h⟩)

theorem reachable_sup_edge (s b u v : V) :
    (H ⊔ SimpleGraph.edge s b).Reachable u v ↔ link H s b u v := by
  constructor
  · intro h
    have h' := ((H ⊔ SimpleGraph.edge s b).reachable_iff_reflTransGen u v).mp h
    clear h
    induction h' with
    | refl => exact link_refl H s b u
    | @tail z v _ hz ih =>
      apply link_trans H ih
      rcases hz with hz | hz
      · exact Or.inl hz.reachable
      · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hz).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _,.refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _,.refl _⟩)
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact h.mono le_sup_left
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).mono le_sup_right |>.trans
        (h2.mono le_sup_left))
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).symm.mono le_sup_right |>.trans
        (h2.mono le_sup_left))

end Wiring
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
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
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma prop_openEdge_reachable (G : BondGraph V E) (ω : Set E)
    {v e t} (he : ω e) (heq : G.ends e = s(v,t)) :
    (G.openGraph ω).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩)

end CriticalPercolation.LazyDFS

end
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

lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.openGraph ω).Reachable o w ↔
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_OpenGraphInsert
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
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*}

lemma openGraph_insert (G : BondGraph V E) (s : Set E) (e : E) (a b : V)
    (he : G.ends e = s(a,b)) :
    G.openGraph (insert e s) = G.openGraph s ⊔ SimpleGraph.edge a b := by
  rw [openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

omit [Fintype V] in
lemma cluster_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : G.cluster ω u = G.cluster ω v := by
  ext z
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩

omit [Fintype V] in
lemma cluster_insert_endpoint (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y)) :
    G.cluster (insert e ω) x = G.cluster ω x ∪ G.cluster ω y := by
  ext v
  simp only [cluster,Set.mem_ofPred_eq,Set.mem_union,G.openGraph_insert ω e x y he,
    Wiring.reachable_sup_edge]
  constructor
  · rintro (h|⟨_,h⟩|⟨_,h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _,h⟩)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_InfiniteUniquenessGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_insert_edge_unchanged (ω : Set E) (e : E) (o : V)
    (hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω o) :
    G.cluster (insert e ω) o = G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro y hy
    have hr := ((G.openGraph (insert e ω)).reachable_iff_reflTransGen o y).mp hy
    clear hy
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨f,hf,hfe⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases hf with rfl | hf
      · exact False.elim (hends x (by simp [hfe]) ih)
      · have hadj : (G.openGraph ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨f,hf,hfe⟩,hne⟩
        exact ih.trans hadj.reachable
  · exact G.cluster_mono (Set.subset_insert e ω) o

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

lemma modularMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S =
      G.stabilizerWeight o a * G.modularMass a S := by
  unfold modularMass
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  split_ifs with hx
  · exact G.stabilizerWeight_change_base hc hl o a x
  · exact (mul_zero _).symm

lemma modularMass_eq_top_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (S : Set V) : G.modularMass o S = ∞ ↔ G.modularMass a S = ∞ := by
  rw [G.modularMass_change_base hc hl o a S,ENNReal.mul_eq_top]
  simp [G.stabilizerWeight_ne_top o a,(G.stabilizerWeight_pos hc hl o a).ne']

lemma modularMass_mono (o : V) {S T : Set V} (h : S⊆T) :
    G.modularMass o S ≤ G.modularMass o T := by
  apply ENNReal.tsum_le_tsum
  intro x
  split_ifs with hS hT
  · rfl
  · exact False.elim (hT (h hS))
  · exact zero_le
  · rfl

lemma modularMass_finite (o : V) {S : Set V} (hS : S.Finite) :
    G.modularMass o S < ∞ := by
  classical
  unfold modularMass
  rw [tsum_eq_sum (s := hS.toFinset) (fun x hx => by
    simp only [hS.mem_toFinset] at hx
    simp only [ite_eq_right hx])]
  apply ENNReal.sum_lt_top.mpr
  intro x hx
  rw [ite_eq_left (hS.mem_toFinset.mp hx)]
  exact ENNReal.ofReal_lt_top

lemma infinite_of_modularMass_top (o : V) {S : Set V} (hS : G.modularMass o S = ∞) :
    S.Infinite := by
  intro hf
  have hh := G.modularMass_finite o hf
  rw [hS] at hh
  exact (lt_irrefl _ hh)

lemma Aut.stabilizerWeight (φ : G.Aut) (o x : V) :
    G.stabilizerWeight (φ.vertex o) (φ.vertex x) = G.stabilizerWeight o x := by
  simp only [CriticalPercolation.BondGraph.stabilizerWeight,Aut.modularRatio]

lemma Aut.modularMass_image (φ : G.Aut) (o : V) (S : Set V) :
    G.modularMass (φ.vertex o) (φ.vertex '' S) = G.modularMass o S := by
  unfold modularMass
  rw [←φ.vertex.tsum_eq]
  apply tsum_congr
  intro x
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,Aut.stabilizerWeight]

lemma measurable_modularClusterMass [Countable V] [Countable E] (o v : V) :
    Measurable (fun ω : Set E => G.modularMass o (G.cluster ω v)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (G.measurable_reachable v x).setOf measurable_const

lemma measurableSet_heavyClusterEvent [Countable V] [Countable E] (o v : V) :
    MeasurableSet (G.heavyClusterEvent o v) :=
  measurableSet_eq_fun (G.measurable_modularClusterMass o v) measurable_const

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyClusterNumber
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularMass_union_le (o : V) (S T : Set V) :
    G.modularMass o (S ∪ T) ≤ G.modularMass o S + G.modularMass o T := by
  unfold modularMass
  rw [←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hs : x∈S <;> by_cases ht : x∈T <;> simp [hs,ht]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakClusters
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

lemma clusterPeaks_eq_of_reachable {ω : Set E} {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.clusterPeaks ω x = G.clusterPeaks ω y := by
  ext z
  exact and_congr (⟨fun hz => h.symm.trans hz,fun hz => h.trans hz⟩) Iff.rfl

lemma peakBound_iff_of_reachable (N : ℕ) {ω : Set E} {x y : V}
    (h : (G.openGraph ω).Reachable x y) : G.peakBound N ω x ↔ G.peakBound N ω y := by
  unfold peakBound
  rw [G.clusterPeaks_eq_of_reachable h]

lemma Aut.clusterPeak_iff (φ : G.Aut) (ω : Set E) (x : V) :
    G.clusterPeak (φ.edge '' ω) (φ.vertex x) ↔ G.clusterPeak ω x := by
  unfold clusterPeak
  constructor
  · intro h z hz
    have hr : (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex x) (φ.vertex z) :=
      (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mpr hz
    simpa only [Aut.stabilizerWeight] using h (φ.vertex z) hr
  · intro h z hz
    obtain ⟨y,rfl⟩ := φ.vertex.surjective z
    rw [Aut.stabilizerWeight]
    exact h y ((SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).mp hz)

lemma Aut.clusterPeaks_image (φ : G.Aut) (ω : Set E) (v : V) :
    φ.vertex '' G.clusterPeaks ω v = G.clusterPeaks (φ.edge '' ω) (φ.vertex v) := by
  ext z
  obtain ⟨y,rfl⟩ := φ.vertex.surjective z
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right,clusterPeaks,Set.mem_ofPred_eq,
    φ.clusterPeak_iff]
  exact and_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)).symm Iff.rfl

lemma Aut.peakBound_iff (φ : G.Aut) (N : ℕ) (ω : Set E) (v : V) :
    G.peakBound N (φ.edge '' ω) (φ.vertex v) ↔ G.peakBound N ω v := by
  change (∃ S : Finset V, S.card ≤ N ∧ G.clusterPeaks (φ.edge '' ω) (φ.vertex v) ⊆ S) ↔ _
  rw [←φ.clusterPeaks_image]
  constructor
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex.symm,(Finset.card_image_le).trans hS,?_⟩
    intro x hx
    exact Finset.mem_image.mpr ⟨φ.vertex x,h ⟨x,hx,rfl⟩,φ.vertex.symm_apply_apply x⟩
  · rintro ⟨S,hS,h⟩
    refine ⟨S.image φ.vertex,(Finset.card_image_le).trans hS,?_⟩
    rintro y ⟨x,hx,rfl⟩
    exact Finset.mem_image.mpr ⟨x,h hx,rfl⟩

lemma measurable_clusterPeak [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.clusterPeak ω x) := by
  exact .forall (fun z => (G.measurable_reachable x z).imp measurable_const)

lemma measurable_mem_clusterPeaks [Countable V] [Countable E] (v x : V) :
    Measurable (fun ω : Set E => x∈G.clusterPeaks ω v) :=
  (G.measurable_reachable v x).and (G.measurable_clusterPeak x)

lemma measurable_peakBound [Countable V] [Countable E] (N : ℕ) (v : V) :
    Measurable (fun ω : Set E => G.peakBound N ω v) := by
  exact .exists (fun S : Finset V => measurable_const.and
    (.forall (fun x => (G.measurable_mem_clusterPeaks v x).imp measurable_const)))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularSuperlevels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_le_one_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight a x ≤ 1 ↔ G.stabilizerWeight o x ≤ G.stabilizerWeight o a := by
  rw [G.stabilizerWeight_change_base hc hl o a x]
  conv_rhs => rhs; rw [←mul_one (G.stabilizerWeight o a)]
  exact (ENNReal.mul_le_mul_iff_right (G.stabilizerWeight_pos hc hl o a).ne'
    (G.stabilizerWeight_ne_top o a)).symm

lemma finite_clusterUpperSet_of_mass_ne_top {ω : Set E} {v : V}
    (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (ε := 1) one_ne_zero).subset
  intro x hx
  change 1 ≤ if x∈G.cluster ω v then G.stabilizerWeight v x else 0
  rw [ite_eq_left hx.1]
  exact hx.2

lemma clusterPeaks_finite_of_mass_ne_top (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Finite := by
  apply (G.finite_clusterUpperSet_of_mass_ne_top hm).subset
  intro x hx
  refine ⟨hx.1,?_⟩
  have hh := (G.stabilizerWeight_le_one_iff hc hl v x v).mp (hx.2 v hx.1.symm)
  simpa only [G.stabilizerWeight_self] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakRatioTransport
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

lemma one_le_modularClusterMass (ω : Set E) (x : V) :
    1 ≤ G.modularMass x (G.cluster ω x) := by
  have h := ENNReal.le_tsum (f := fun y => if y∈G.cluster ω x then G.stabilizerWeight x y else 0) x
  have hx : x∈G.cluster ω x := SimpleGraph.Reachable.refl x
  simpa only [modularMass,ite_eq_left hx,G.stabilizerWeight_self] using h

lemma measurable_peakRatioTransport [Countable V] [Countable E] (x y : V) :
    Measurable (fun ω : Set E => G.peakRatioTransport ω x y) := by
  apply Measurable.ite (G.measurable_mem_clusterPeaks x y).setOf _ measurable_const
  apply Measurable.mul (G.measurable_modularClusterMass y x).inv
  apply Measurable.inv
  apply Measurable.of_discrete.comp
  apply measurable_ncard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakRatioTransport_aut (φ : G.Aut) (ω : Set E) (x y : V) :
    G.peakRatioTransport (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.peakRatioTransport ω x y := by
  unfold peakRatioTransport
  rw [←φ.cluster_image,φ.modularMass_image,←φ.clusterPeaks_image,
    Set.ncard_image_of_injective _ φ.vertex.injective]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

lemma peakRatioTransport_incoming (ω : Set E) (y : V) :
    (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      if G.clusterPeak ω y ∧ G.modularMass y (G.cluster ω y) ≠ ∞ then
        ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹ else 0 := by
  by_cases hp : G.clusterPeak ω y
  · have heq : (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
        ((G.modularMass y (G.cluster ω y))⁻¹ * ((G.clusterPeaks ω y).ncard : ℝ≥0∞)⁻¹) *
          G.modularMass y (G.cluster ω y) := by
      conv_rhs => rhs; unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro x
      by_cases hx : x∈G.cluster ω y
      · rw [ite_eq_left hx,peakRatioTransport,ite_eq_left ⟨hx.symm,hp⟩,
          G.cluster_eq_of_reachable hx.symm,G.clusterPeaks_eq_of_reachable hx.symm]
      · have hnot : y∉G.clusterPeaks ω x := fun h => hx h.1.symm
        simp only [peakRatioTransport,ite_eq_right hnot,zero_mul,ite_eq_right hx,mul_zero]
    rw [heq]
    by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · simp [hp,hm]
    · rw [ite_eq_left ⟨hp,hm⟩,mul_right_comm,
        ENNReal.inv_mul_cancel (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω y))) hm,
        one_mul]
  · have hz : ∀ x, G.peakRatioTransport ω x y = 0 := by
      intro x
      exact ite_eq_right (fun h => hp h.2)
    simp only [hz,zero_mul,tsum_zero,hp,false_and,if_false]

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

lemma measurable_reciprocalClusterMass [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.reciprocalClusterMass ω x) :=
  (G.measurable_modularClusterMass x x).inv

lemma Aut.reciprocalClusterMass (φ : G.Aut) (ω : Set E) (x : V) :
    G.reciprocalClusterMass (φ.edge '' ω) (φ.vertex x)=G.reciprocalClusterMass ω x := by
  unfold CriticalPercolation.BondGraph.reciprocalClusterMass
  rw [←φ.cluster_image,φ.modularMass_image]

lemma finiteMassIndicator_eq_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable x y) :
    G.finiteMassIndicator ω x=G.finiteMassIndicator ω y := by
  unfold finiteMassIndicator
  simp only [G.cluster_eq_of_reachable h,G.modularMass_eq_top_change_base hc hl x y]

lemma stabilizerWeight_mul_reverse (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    G.stabilizerWeight x y*G.stabilizerWeight y x=1 := by
  rw [←G.stabilizerWeight_change_base hc hl x y x,G.stabilizerWeight_self]

lemma stabilizerWeight_inv (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (x y : V) :
    (G.stabilizerWeight x y)⁻¹=G.stabilizerWeight y x := by
  apply (ENNReal.mul_left_inj (G.stabilizerWeight_pos hc hl x y).ne' (G.stabilizerWeight_ne_top x y)).mp
  rw [ENNReal.inv_mul_cancel (G.stabilizerWeight_pos hc hl x y).ne' (G.stabilizerWeight_ne_top x y),
    G.stabilizerWeight_mul_reverse hc hl]

lemma reciprocalClusterMass_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) {x y : V} (h : (G.openGraph ω).Reachable y x) :
    G.reciprocalClusterMass ω x=G.stabilizerWeight y x*G.reciprocalClusterMass ω y := by
  unfold reciprocalClusterMass
  rw [G.cluster_eq_of_reachable h.symm,G.modularMass_change_base hc hl x y,
    ENNReal.mul_inv (Or.inl (G.stabilizerWeight_pos hc hl x y).ne') (Or.inl (G.stabilizerWeight_ne_top x y)),
    G.stabilizerWeight_inv hc hl]

lemma sum_reciprocalClusterMass (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (y : V) :
    (∑' x, if x∈G.cluster ω y then G.reciprocalClusterMass ω x else 0)=G.finiteMassIndicator ω y := by
  calc
    _ = (G.modularMass y (G.cluster ω y))*G.reciprocalClusterMass ω y := by
      unfold modularMass
      rw [←ENNReal.tsum_mul_right]
      apply tsum_congr
      intro x
      by_cases h : x∈G.cluster ω y
      · simp only [ite_eq_left h,G.reciprocalClusterMass_change_base hc hl ω h]
      · simp only [ite_eq_right h,zero_mul]
    _ = _ := by
      unfold reciprocalClusterMass finiteMassIndicator
      split_ifs with hm
      · simp [hm]
      · exact ENNReal.mul_inv_cancel
          (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω y))) hm

lemma measurable_incidentClusterCount [Countable V] [Countable E] (e : E) :
    Measurable (fun ω : Set E => G.incidentClusterCount ω e) := by
  apply Measurable.tsum
  intro x
  exact (G.measurable_reciprocalClusterMass x).ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf measurable_const

lemma incident_cluster_iff_ends (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) (x : V) :
    e∈G.incidentEdges (G.cluster ω x) ↔ x∈G.cluster ω a ∨ x∈G.cluster ω b := by
  constructor
  · rintro ⟨v,hv,hve⟩
    rw [he,Sym2.mem_iff] at hve
    rcases hve with rfl|rfl
    · exact Or.inl hv.symm
    · exact Or.inr hv.symm
  · rintro (ha|hb)
    · exact ⟨a,ha.symm,by simp [he]⟩
    · exact ⟨b,hb.symm,by simp [he]⟩

lemma incidentClusterCount_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.incidentClusterCount ω e = if (G.openGraph ω).Reachable a b then
      G.finiteMassIndicator ω a else G.finiteMassIndicator ω a+G.finiteMassIndicator ω b := by
  unfold incidentClusterCount
  simp only [G.incident_cluster_iff_ends ω e a b he]
  by_cases hr : (G.openGraph ω).Reachable a b
  · rw [ite_eq_left hr]
    have hC := G.cluster_eq_of_reachable hr
    simp only [hC,or_self,G.sum_reciprocalClusterMass hc hl]
    exact (G.finiteMassIndicator_eq_of_reachable hc hl ω hr).symm
  · rw [ite_eq_right hr,←G.sum_reciprocalClusterMass hc hl ω a,←G.sum_reciprocalClusterMass hc hl ω b,
      ←ENNReal.tsum_add]
    apply tsum_congr
    intro x
    have hnot : ¬(x∈G.cluster ω a ∧ x∈G.cluster ω b) := fun h => hr (h.1.trans h.2.symm)
    by_cases ha : x∈G.cluster ω a <;> by_cases hb : x∈G.cluster ω b <;>
      simp_all only [true_or,or_true,false_or,if_true,if_false,zero_add,add_zero,and_self,not_true_eq_false]

lemma incidentClusterCount_le_two (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : G.incidentClusterCount ω e≤2 := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.incidentClusterCount_of_ends hc hl ω e a b he.symm]
  unfold finiteMassIndicator
  split_ifs <;> norm_num

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterCountFlip
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma modularMass_union_ne_top (o : V) (S T : Set V) :
    G.modularMass o (S∪T)≠∞ ↔ G.modularMass o S≠∞ ∧ G.modularMass o T≠∞ := by
  constructor
  · intro h
    exact ⟨ne_top_of_le_ne_top h (G.modularMass_mono o Set.subset_union_left),
      ne_top_of_le_ne_top h (G.modularMass_mono o Set.subset_union_right)⟩
  · rintro ⟨hS,hT⟩
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hS,hT⟩) (G.modularMass_union_le o S T)

lemma finiteMassIndicator_insert (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.finiteMassIndicator (insert e ω) a=G.finiteMassIndicator ω a*G.finiteMassIndicator ω b := by
  have hh : G.modularMass a (G.cluster (insert e ω) a)≠∞ ↔
      G.modularMass a (G.cluster ω a)≠∞ ∧ G.modularMass b (G.cluster ω b)≠∞ := by
    rw [G.cluster_insert_endpoint ω e a b he,G.modularMass_union_ne_top]
    exact and_congr_right (fun _ => not_congr (G.modularMass_eq_top_change_base hc hl a b (G.cluster ω b)))
  by_cases ha : G.modularMass a (G.cluster ω a)=∞ <;>
    by_cases hb : G.modularMass b (G.cluster ω b)=∞
  · have hi : G.modularMass a (G.cluster (insert e ω) a)=∞ := by tauto
    simp [finiteMassIndicator,ha,hb,hi]
  · have hi : G.modularMass a (G.cluster (insert e ω) a)=∞ := by tauto
    simp [finiteMassIndicator,ha,hb,hi]
  · have hi : G.modularMass a (G.cluster (insert e ω) a)=∞ := by tauto
    simp [finiteMassIndicator,ha,hb,hi]
  · have hi := hh.mpr ⟨ha,hb⟩
    simp [finiteMassIndicator,ha,hb,hi]

lemma incidentClusterCount_insert_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.incidentClusterCount (insert e ω) e=G.finiteMassIndicator ω a*G.finiteMassIndicator ω b := by
  rw [G.incidentClusterCount_of_ends hc hl _ e a b he,
    ite_eq_left (LazyDFS.prop_openEdge_reachable G (insert e ω) (Set.mem_insert e ω) he),
    G.finiteMassIndicator_insert hc hl ω e a b he]

lemma incidentClusterCount_flip_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    (G.incidentClusterCount ω e).toReal-(G.incidentClusterCount (insert e ω) e).toReal =
    if ¬(G.openGraph ω).Reachable a b ∧
      ¬(G.modularMass a (G.cluster ω a)=∞ ∧ G.modularMass b (G.cluster ω b)=∞) then 1 else 0 := by
  rw [G.incidentClusterCount_of_ends hc hl ω e a b he,G.incidentClusterCount_insert_of_ends hc hl ω e a b he]
  by_cases hr : (G.openGraph ω).Reachable a b
  · have hf := G.finiteMassIndicator_eq_of_reachable hc hl ω hr
    rw [ite_eq_left hr,←hf]
    unfold finiteMassIndicator
    split_ifs <;> simp_all
  · simp only [ite_eq_right hr]
    unfold finiteMassIndicator
    by_cases ha : G.modularMass a (G.cluster ω a)=∞ <;>
      by_cases hb : G.modularMass b (G.cluster ω b)=∞ <;> norm_num [ha,hb,hr]

lemma forceOn_univ_singleton (e : E) (ω : Set E) :
    BernoulliProduct.forceOn {e} Set.univ ω=insert e ω := by
  ext f
  by_cases hf : f=e <;> simp [hf]

lemma forceOn_empty_singleton (e : E) (ω : Set E) :
    BernoulliProduct.forceOn {e} ∅ ω=ω\{e} := BernoulliProduct.forceOn_empty_eq_sdiff {e} ω

end CriticalPercolation.BondGraph
end
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

lemma bondWeight_ne_top (o : V) (e : E) : G.bondWeight o e ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro v hv
  exact G.stabilizerWeight_ne_top o v

lemma bondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (e : E) : G.bondWeight o e = G.stabilizerWeight o a * G.bondWeight a e := by
  unfold bondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact G.stabilizerWeight_change_base hc hl o a v

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

lemma bondWeight_le_at_end (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o v : V) (e : E)
    (hv : v∈G.ends e) : G.bondWeight o e ≤ (2*K : ℕ)*G.stabilizerWeight o v := by
  rw [G.bondWeight_change_base hc hl o v]
  have hsum : G.bondWeight v e ≤ (2*K : ℕ) := by
    calc
      _ ≤ ∑ w∈(G.ends e).toFinset, (K : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' : w∈G.ends e := Sym2.mem_toFinset.mp hw
        exact G.stabilizerWeight_le_ball_bound hc hl K hK
          (G.common_bond_ball_one hv hw') (G.common_bond_ball_one hw' hv)
      _ = ((G.ends e).toFinset.card * K : ℕ) := by simp [nsmul_eq_mul]
      _ ≤ (2*K : ℕ) := by
        have hh : (G.ends e).toFinset.card≤2 := by
          rw [Sym2.card_toFinset]
          split_ifs <;> omega
        exact_mod_cast Nat.mul_le_mul_right K hh
  calc _ ≤ G.stabilizerWeight o v * (2*K : ℕ) := by gcongr
       _ = _ := mul_comm _ _

lemma weighted_incidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o : V) (S : Set V) :
    (∑' e : E, if e∈G.incidentEdges S then G.bondWeight o e else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass o S := by
  calc
    _ ≤ ∑' e : E, ∑' v : V, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e∈G.incidentEdges S
      · rw [ite_eq_left he]
        obtain ⟨v,hv,hve⟩ := he
        simpa only [ite_eq_left (show v∈S ∧ v∈G.ends e from ⟨hv,hve⟩)] using
          (ENNReal.le_tsum v (f := fun v => if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0))
      · simp only [ite_eq_right he]; exact zero_le
    _ = ∑' v : V, ∑' e : E, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' v : V, if v∈S then (D*(2*K) : ℕ)*G.stabilizerWeight o v else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v∈S
      · simp only [hv,true_and,if_true]
        have hf : (G.incidentEdges {v}).Finite := by simpa [incidentEdges] using hl v
        have hm (e : E) : e∈G.incidentEdges {v} ↔ v∈G.ends e := by
          simp [incidentEdges]
        have ht : (∑' e : E, if v∈G.ends e then G.bondWeight o e else 0) =
            ∑ e∈hf.toFinset, G.bondWeight o e := by
          rw [tsum_eq_sum (s := hf.toFinset) (fun e he => by
            simp only [hf.mem_toFinset,hm] at he
            exact ite_eq_right he)]
          apply Finset.sum_congr rfl
          intro e he
          exact ite_eq_left ((hm e).mp (hf.mem_toFinset.mp he))
        rw [ht]
        calc
          _ ≤ ∑ e∈hf.toFinset, (2*K : ℕ)*G.stabilizerWeight o v := by
            apply Finset.sum_le_sum
            intro e he
            exact G.bondWeight_le_at_end hc hl K hK o v e ((hm e).mp (hf.mem_toFinset.mp he))
          _ = ((G.incidentEdges {v}).ncard : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
          _ ≤ (D : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            gcongr
            exact_mod_cast hD v
          _ = _ := by simp only [Nat.cast_mul,mul_assoc]
      · simp only [hv,false_and,if_false,tsum_zero,le_refl]
    _ = _ := by
      unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp

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

lemma OrbitRepresentatives.incoming_finite_ae (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (F : Set E → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun ω => F ω x y))
    (ha : ∀ (φ : G.Aut) ω x y, F (φ.edge '' ω) (φ.vertex x) (φ.vertex y) = F ω x y)
    (N : ℝ≥0∞) (hN : N < ∞) (hb : ∀ ω x, ∑' y, F ω x y ≤ N) (v : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, F ω x v * G.stabilizerWeight v x) < ∞ := by
  have hout : (∑ x ∈ R.roots, ∫⁻ ω, ∑' y, F ω x y ∂G.law p) < ∞ := by
    apply ENNReal.sum_lt_top.mpr
    intro x hx
    exact (calc
      (∫⁻ ω, ∑' y, F ω x y ∂G.law p) ≤ ∫⁻ _ : Set E, N ∂G.law p :=
        lintegral_mono (fun ω => hb ω x)
      _ = N := by simp).trans_lt hN
  rw [OrbitRepresentatives.random_tilted_transport G R hc hl p F hm ha] at hout
  obtain ⟨u,hu,φ,rfl⟩ := R.cover v
  have hu' : (∫⁻ ω, ∑' x, F ω x u * G.stabilizerWeight u x ∂G.law p) < ∞ :=
    (Finset.single_le_sum (fun _ _ => zero_le) hu).trans_lt hout
  have he : (∫⁻ ω, ∑' x, F ω x (φ.vertex u) * G.stabilizerWeight (φ.vertex u) x ∂G.law p) =
      ∫⁻ ω, ∑' x, F ω x u * G.stabilizerWeight u x ∂G.law p := by
    conv_lhs => rw [←G.law_map_aut p φ]
    rw [lintegral_map (Measurable.tsum (fun x => (hm x _).mul_const _))
      (BernoulliProduct.measurable_image_equiv φ.edge)]
    apply lintegral_congr
    intro ω
    rw [←φ.vertex.tsum_eq]
    simp only [ha,Aut.stabilizerWeight]
  exact ae_lt_top (Measurable.tsum (fun x => (hm x _).mul_const _)) (he.trans_lt hu').ne

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_NormalizedIncidenceTransport
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

lemma Aut.mem_ends_iff (φ : G.Aut) (e : E) (v : V) :
    φ.vertex v∈G.ends (φ.edge e) ↔ v∈G.ends e := by
  rw [φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]

lemma Aut.incident_cluster_iff (φ : G.Aut) (ω : Set E) (x : V) (e : E) :
    φ.edge e∈G.incidentEdges (G.cluster (φ.edge '' ω) (φ.vertex x)) ↔
      e∈G.incidentEdges (G.cluster ω x) := by
  rw [←φ.cluster_image]
  constructor
  · rintro ⟨v,⟨w,hw,rfl⟩,hwe⟩
    exact ⟨w,hw,(Aut.mem_ends_iff G φ e w).mp hwe⟩
  · rintro ⟨v,hv,hve⟩
    exact ⟨φ.vertex v,⟨v,hv,rfl⟩,(Aut.mem_ends_iff G φ e v).mpr hve⟩

lemma measurable_incidentCluster [Countable V] [Countable E] (x : V) (e : E) :
    Measurable (fun ω : Set E => e∈G.incidentEdges (G.cluster ω x)) :=
  Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)

lemma measurable_normalizedSelectedIncidence [Countable V] [Countable E]
    (H : (Set E) → E → ℝ≥0∞) (hm : ∀ e, Measurable (fun ω => H ω e)) (x : V) :
    Measurable (fun ω : Set E => G.normalizedSelectedIncidence H ω x) := by
  apply Measurable.mul _ (G.measurable_reciprocalClusterMass x)
  exact Measurable.tsum (fun e => ((hm e).mul_const _).ite
    (G.measurable_incidentCluster x e).setOf measurable_const)

lemma measurable_normalizedIncidenceTransport [Countable V] [Countable E]
    (H : (Set E) → E → ℝ≥0∞) (hm : ∀ e, Measurable (fun ω => H ω e)) (x y : V) :
    Measurable (fun ω : Set E => G.normalizedIncidenceTransport H ω x y) := by
  apply Measurable.tsum
  intro e
  exact (((hm e).mul_const _).mul (G.measurable_reciprocalClusterMass x)).ite
    ((G.measurable_incidentCluster x e).and measurable_const).setOf measurable_const

lemma Aut.normalizedIncidenceTransport (H : (Set E) → E → ℝ≥0∞)
    (ha : ∀ (φ : G.Aut) ω e, H (φ.edge '' ω) (φ.edge e)=H ω e)
    (φ : G.Aut) (ω : Set E) (x y : V) :
    G.normalizedIncidenceTransport H (φ.edge '' ω) (φ.vertex x) (φ.vertex y)=
      G.normalizedIncidenceTransport H ω x y := by
  unfold CriticalPercolation.BondGraph.normalizedIncidenceTransport
  rw [←φ.edge.tsum_eq]
  simp only [φ.incident_cluster_iff,φ.mem_ends_iff,ha,φ.stabilizerWeight,φ.reciprocalClusterMass]

lemma normalizedIncidenceTransport_out (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (x : V) :
    (∑' y, G.normalizedIncidenceTransport H ω x y)=G.normalizedSelectedIncidence H ω x := by
  unfold normalizedIncidenceTransport normalizedSelectedIncidence
  rw [ENNReal.tsum_comm,←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro e
  by_cases he : e∈G.incidentEdges (G.cluster ω x)
  · simp only [he,true_and,if_true]
    rw [tsum_eq_sum (s := (G.ends e).toFinset) (fun y hy => by
      simpa only [Sym2.mem_toFinset] using (ite_eq_right (by simpa only [Sym2.mem_toFinset] using hy) :
        (if y∈G.ends e then H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0)=0))]
    have heq : (∑ y∈(G.ends e).toFinset, if y∈G.ends e then
        H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x else 0) =
      ∑ y∈(G.ends e).toFinset, H ω e*G.stabilizerWeight x y*G.reciprocalClusterMass ω x := by
      apply Finset.sum_congr rfl
      intro y hy
      exact ite_eq_left (Sym2.mem_toFinset.mp hy)
    rw [heq,←Finset.sum_mul,←Finset.mul_sum]
    rfl
  · simp only [he,false_and,if_false,tsum_zero,zero_mul]

lemma normalizedIncidenceTransport_in (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (H : (Set E) → E → ℝ≥0∞) (ω : Set E) (y : V) :
    (∑' x, G.normalizedIncidenceTransport H ω x y*G.stabilizerWeight y x)=
      ∑' e, if y∈G.ends e then H ω e*G.incidentClusterCount ω e else 0 := by
  unfold normalizedIncidenceTransport
  simp only [←ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro e
  by_cases hy : y∈G.ends e
  · simp only [hy,and_true,if_true,incidentClusterCount,←ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    by_cases he : e∈G.incidentEdges (G.cluster ω x)
    · simp only [ite_eq_left he]
      calc _ = (H ω e*G.reciprocalClusterMass ω x)*
          (G.stabilizerWeight x y*G.stabilizerWeight y x) := by ac_rfl
           _ = _ := by rw [G.stabilizerWeight_mul_reverse hc hl,mul_one]
    · simp only [ite_eq_right he,zero_mul,mul_zero]
  · simp only [hy,and_false,if_false,zero_mul,tsum_zero]

lemma normalizedSelectedIncidence_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (H : (Set E) → E → ℝ≥0∞) (hH : ∀ ω e, H ω e≤1) (ω : Set E) (x : V) :
    G.normalizedSelectedIncidence H ω x≤(D*(2*K) : ℕ) := by
  unfold normalizedSelectedIncidence
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [reciprocalClusterMass,hm]
  · calc
      _ ≤ ((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x))*G.reciprocalClusterMass ω x := by
        apply mul_le_mul_left
        apply le_trans _ (G.weighted_incidence_le hc hl D K hD hK x _)
        apply ENNReal.tsum_le_tsum
        intro e
        split_ifs
        · exact mul_le_of_le_one_left zero_le (hH ω e)
        · rfl
      _ = _ := by
        rw [reciprocalClusterMass,mul_assoc,ENNReal.mul_inv_cancel
          (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm,mul_one]

theorem expected_normalizedSelectedIncidence [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (H : (Set E) → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e))
    (ha : ∀ (φ : G.Aut) ω e, H (φ.edge '' ω) (φ.edge e)=H ω e) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫⁻ ω, G.normalizedSelectedIncidence H ω x ∂G.law p)=
      ∑ y∈(G.orbitRepresentatives hq).roots, ∫⁻ ω,
        ∑' e, if y∈G.ends e then H ω e*G.incidentClusterCount ω e else 0 ∂G.law p := by
  simpa only [G.normalizedIncidenceTransport_out,G.normalizedIncidenceTransport_in hc hl] using
    OrbitRepresentatives.random_tilted_transport G (G.orbitRepresentatives hq) hc hl p
      (G.normalizedIncidenceTransport H) (G.measurable_normalizedIncidenceTransport H hm)
      (fun φ => Aut.normalizedIncidenceTransport G H ha φ)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ExpectedIncidenceTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

lemma lintegral_ne_top_of_uniform_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ≥0∞) (C : ℝ≥0∞) (hC : C≠∞)
    (hb : ∀ a, f a≤C) : (∫⁻ a, f a ∂μ)≠∞ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top μ Set.univ))
  simpa only [lintegral_const] using lintegral_mono hb

lemma sum_integral_toReal {α ι : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (S : Finset ι) (F : ι → α → ℝ≥0∞) (hm : ∀ i∈S, Measurable (F i))
    (C : ι → ℝ≥0∞) (hC : ∀ i∈S, C i≠∞) (hb : ∀ i∈S, ∀ a, F i a≤C i) :
    (∑ i∈S, ∫ a, (F i a).toReal ∂μ)=(∑ i∈S, ∫⁻ a, F i a ∂μ).toReal := by
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_toReal (hm i hi).aemeasurable (Eventually.of_forall (fun a =>
      lt_top_iff_ne_top.mpr (ne_top_of_le_ne_top (hC i hi) (hb i hi a))))
  · intro i hi
    exact lintegral_ne_top_of_uniform_bound μ (F i) (C i) (hC i hi) (hb i hi)

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma selectedIncidenceReturn_eq_tsum (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞)
    (ω : Set E) (y : V) : G.selectedIncidenceReturn hl H ω y =
      ∑' e, if y∈G.ends e then H ω e*G.incidentClusterCount ω e else 0 := by
  rw [tsum_eq_sum (s := (hl y).toFinset) (fun e he => ite_eq_right (by simpa using he))]
  apply Finset.sum_congr rfl
  intro e he
  exact (ite_eq_left ((hl y).mem_toFinset.mp he)).symm

lemma measurable_selectedIncidenceReturn [Countable V] [Countable E]
    (hl : G.LocallyFinite) (H : Set E → E → ℝ≥0∞) (hm : ∀ e, Measurable (fun ω => H ω e)) (y : V) :
    Measurable (fun ω => G.selectedIncidenceReturn hl H ω y) :=
  Finset.measurable_sum _ (fun e _ => (hm e).mul (G.measurable_incidentClusterCount e))

lemma selectedIncidenceReturn_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (H : Set E → E → ℝ≥0∞) (hH : ∀ ω e, H ω e≤1) (ω : Set E) (y : V) :
    G.selectedIncidenceReturn hl H ω y≤(hl y).toFinset.card*2 := by
  unfold selectedIncidenceReturn
  calc _ ≤ ∑ _e∈(hl y).toFinset, (2:ℝ≥0∞) := by
          apply Finset.sum_le_sum
          intro e _
          exact (mul_le_mul' (hH ω e) (G.incidentClusterCount_le_two hc hl ω e)).trans_eq (one_mul 2)
       _ = _ := by simp

lemma selectedIncidenceReturn_toReal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (H : Set E → E → ℝ≥0∞) (hH : ∀ ω e, H ω e≤1) (ω : Set E) (y : V) :
    (G.selectedIncidenceReturn hl H ω y).toReal=
      ∑ e∈(hl y).toFinset, (H ω e).toReal*(G.incidentClusterCount ω e).toReal := by
  unfold selectedIncidenceReturn
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro e _
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hH ω e))
      (ne_top_of_le_ne_top (by norm_num : (2:ℝ≥0∞)≠∞) (G.incidentClusterCount_le_two hc hl ω e))

lemma expected_selectedIncidence_real [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (H : Set E → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e)) (hH : ∀ ω e, H ω e≤1)
    (ha : ∀ (φ : G.Aut) ω e, H (φ.edge '' ω) (φ.edge e)=H ω e) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.normalizedSelectedIncidence H ω x).toReal ∂G.law p)=
      ∑ y∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.selectedIncidenceReturn hl H ω y).toReal ∂G.law p := by
  rw [sum_integral_toReal (G.law p) _ _ (fun x _ => G.measurable_normalizedSelectedIncidence H hm x)
      (fun _ => (D*(2*K) : ℕ)) (fun _ _ => ENNReal.natCast_ne_top _)
      (fun x _ ω => G.normalizedSelectedIncidence_le hc hl D K hD hK H hH ω x),
    sum_integral_toReal (G.law p) _ _ (fun y _ => G.measurable_selectedIncidenceReturn hl H hm y)
      (fun y => (hl y).toFinset.card*2) (fun _ _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num))
      (fun y _ ω => G.selectedIncidenceReturn_le hc hl H hH ω y)]
  congr 1
  simp_rw [G.selectedIncidenceReturn_eq_tsum]
  exact G.expected_normalizedSelectedIncidence hc hl hq p H hm ha

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyPeaks
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyPeakTransport (N : ℕ) (x y : V) :
    Measurable (fun ω : Set E => G.heavyPeakTransport N ω x y) := by
  apply measurable_const.ite _ measurable_const
  exact (G.measurableSet_heavyClusterEvent x x).inter
    ((G.measurable_peakBound N x).and (G.measurable_mem_clusterPeaks x y)).setOf

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_aut (N : ℕ) (φ : G.Aut) (ω : Set E) (x y : V) :
    G.heavyPeakTransport N (φ.edge '' ω) (φ.vertex x) (φ.vertex y) =
      G.heavyPeakTransport N ω x y := by
  unfold heavyPeakTransport
  rw [←φ.cluster_image,φ.modularMass_image,φ.peakBound_iff,←φ.clusterPeaks_image]
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_out_bound (N : ℕ) (ω : Set E) (x : V) :
    (∑' y, G.heavyPeakTransport N ω x y) ≤ N := by
  by_cases hb : G.peakBound N ω x
  · obtain ⟨S,hS,hcover⟩ := hb
    calc
      _ ≤ ∑' y, if y∈S then (1 : ℝ≥0∞) else 0 := by
        apply ENNReal.tsum_le_tsum
        intro y
        unfold heavyPeakTransport
        split_ifs with hh hs
        · rfl
        · exact False.elim (hs (hcover hh.2.2))
        · exact zero_le
        · rfl
      _ = (S.card : ℝ≥0∞) := by
        rw [tsum_eq_sum (s := S) (fun y hy => ite_eq_right hy)]
        calc
          _ = ∑ y ∈ S, (1 : ℝ≥0∞) := Finset.sum_congr rfl (fun y hy => ite_eq_left hy)
          _ = _ := by simp
      _ ≤ N := by exact_mod_cast hS
  · simp only [heavyPeakTransport,hb,false_and,and_false,if_false,tsum_zero,zero_le]

omit [Countable V] [Countable E] in
lemma heavyPeakTransport_infinite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (N : ℕ) (ω : Set E) (y : V)
    (hh : G.modularMass y (G.cluster ω y) = ∞) (hb : G.peakBound N ω y)
    (hp : G.clusterPeak ω y) :
    (∑' x, G.heavyPeakTransport N ω x y * G.stabilizerWeight y x) = ∞ := by
  apply top_unique
  rw [←hh]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : x ∈ G.cluster ω y
  · have hxy : (G.openGraph ω).Reachable x y := hx.symm
    have he : G.cluster ω x = G.cluster ω y := G.cluster_eq_of_reachable hxy
    have hhx : G.modularMass x (G.cluster ω x) = ∞ := by
      rw [he,G.modularMass_eq_top_change_base hc hl x y]
      exact hh
    have hbx : G.peakBound N ω x := (G.peakBound_iff_of_reachable N hxy).mpr hb
    have hcond : G.modularMass x (G.cluster ω x) = ∞ ∧ G.peakBound N ω x ∧
        y∈G.clusterPeaks ω x := ⟨hhx,hbx,⟨hxy,hp⟩⟩
    simp only [ite_eq_left hx,heavyPeakTransport,ite_eq_left hcond,one_mul,le_refl]
  · simp only [ite_eq_right hx,zero_le]

lemma no_heavy_finite_peaks_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (p : unitInterval) :
    ∀ᵐ ω ∂G.law p, ∀ y : V, ∀ N : ℕ,
      ¬ (G.modularMass y (G.cluster ω y) = ∞ ∧ G.peakBound N ω y ∧ G.clusterPeak ω y) := by
  apply ae_all_iff.mpr
  intro y
  apply ae_all_iff.mpr
  intro N
  have hfin := OrbitRepresentatives.incoming_finite_ae G (G.orbitRepresentatives hq)
    hc hl p (G.heavyPeakTransport N) (G.measurable_heavyPeakTransport N)
    (G.heavyPeakTransport_aut N) N (ENNReal.natCast_lt_top N) (G.heavyPeakTransport_out_bound N) y
  filter_upwards [hfin] with ω hω
  rintro ⟨hh,hb,hp⟩
  rw [G.heavyPeakTransport_infinite hc hl N ω y hh hb hp] at hω
  exact (lt_irrefl _ hω)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PeakReturn
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurable_peakReturn [Countable V] [Countable E] (x : V) :
    Measurable (fun ω : Set E => G.peakReturn ω x) := by
  apply Measurable.ite (G.measurable_clusterPeak x).setOf _ measurable_const
  apply Measurable.inv
  apply (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
  apply measurable_encard.comp
  exact Measurable.of_eval (fun vertex => G.measurable_mem_clusterPeaks x vertex)

lemma peakReturn_eq_inv_ncard (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (hf : (G.clusterPeaks ω x).Finite) :
    G.peakReturn ω x = ((G.clusterPeaks ω x).ncard : ℝ≥0∞)⁻¹ := by
  rw [peakReturn,ite_eq_left hp,hf.encard_eq_coe,ENat.toENNReal_coe]
  rfl

lemma peakReturn_le_one (ω : Set E) (x : V) : G.peakReturn ω x ≤ 1 := by
  unfold peakReturn
  split_ifs with hp
  · apply ENNReal.inv_le_one.mpr
    have hh : (1 : ℕ∞) ≤ (G.clusterPeaks ω x).encard :=
      Set.one_le_encard_iff_nonempty.mpr ⟨x,SimpleGraph.Reachable.refl x,hp⟩
    exact_mod_cast hh
  · exact zero_le

lemma peakRatioTransport_incoming_ae [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (y : V) :
    ∀ᵐ ω ∂G.law p, (∑' x, G.peakRatioTransport ω x y * G.stabilizerWeight y x) =
      G.peakReturn ω y := by
  filter_upwards [G.no_heavy_finite_peaks_ae hc hl hq p] with ω hω
  rw [G.peakRatioTransport_incoming]
  by_cases hp : G.clusterPeak ω y
  · by_cases hm : G.modularMass y (G.cluster ω y) = ∞
    · have hi : (G.clusterPeaks ω y).Infinite := by
        intro hf
        exact hω y hf.toFinset.card ⟨hm,⟨hf.toFinset,le_rfl,fun _ hx => hf.mem_toFinset.mpr hx⟩,hp⟩
      simp [peakReturn,hp,hm,hi.encard_eq]
    · rw [ite_eq_left ⟨hp,hm⟩,G.peakReturn_eq_inv_ncard ω y hp
        (G.clusterPeaks_finite_of_mass_ne_top hc hl ω y hm)]
  · simp only [hp,false_and,if_false,peakReturn]

lemma clusterPeak_of_subset {ω τ : Set E} (h : ω⊆τ) {x : V}
    (hp : G.clusterPeak τ x) : G.clusterPeak ω x :=
  fun y hy => hp y (hy.mono (G.openGraph_mono h))

lemma eventually_cluster_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) {x y : V} (hy : y∈G.cluster ω x) :
    ∀ᶠ n in atTop, y∈G.cluster (a n) x := by
  obtain ⟨S,hS,hSω,hSy⟩ := G.mem_cluster_finite_witness hy
  have h : ∀ e∈S, ∀ᶠ n in atTop, e∈a n := by
    intro e he
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hu ▸ hSω he)
    exact eventually_atTop.mpr ⟨n,fun m hm => ha hm hn⟩
  filter_upwards [(Filter.eventually_all_finite hS).mpr h] with n hn
  exact G.cluster_mono hn x hSy

lemma eventually_peaks_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) {x y : V} (hy : y∈G.clusterPeaks ω x) :
    ∀ᶠ n in atTop, y∈G.clusterPeaks (a n) x := by
  filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy.1] with n hn
  refine ⟨hn,G.clusterPeak_of_subset ?_ hy.2⟩
  exact hu ▸ Set.subset_iUnion a n

lemma tendsto_peakCount_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) (x : V)
    (hi : (G.clusterPeaks ω x).Infinite) :
    Tendsto (fun n => ((G.clusterPeaks (a n) x).encard : ℝ≥0∞)) atTop (𝓝 ∞) := by
  apply ENNReal.tendsto_nhds_top_iff_nat.mpr
  intro N
  obtain ⟨S,hS,hcard⟩ := hi.exists_subset_card_eq (N+1)
  have he : ∀ y∈(S : Set V), ∀ᶠ n in atTop, y∈G.clusterPeaks (a n) x :=
    fun y hy => G.eventually_peaks_of_exhaustion a ω ha hu (hS hy)
  filter_upwards [(Filter.eventually_all_finite S.finite_toSet).mpr he] with n hn
  have hh := ENat.toENNReal_mono (Set.encard_mono hn)
  have hb : ((N+1 : ℕ) : ℝ≥0∞) ≤ ((G.clusterPeaks (a n) x).encard : ℝ≥0∞) := by
    simpa only [Set.encard_coe_eq_coe_finsetCard,ENat.toENNReal_coe,hcard] using hh
  have hN : (N : ℝ≥0∞) < ((N+1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self N
  exact hN.trans_le hb

lemma tendsto_peakReturn_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n = ω) (x : V)
    (h : ¬ G.clusterPeak ω x ∨ (G.clusterPeaks ω x).Infinite) :
    Tendsto (fun n => G.peakReturn (a n) x) atTop (𝓝 0) := by
  rcases h with hp|hi
  · have hw : ∃ y, (G.openGraph ω).Reachable x y ∧ ¬G.stabilizerWeight x y ≤ 1 := by
      obtain ⟨y,hy⟩ := not_forall.mp hp
      exact ⟨y,Classical.not_imp.mp hy⟩
    obtain ⟨y,hy,hyw⟩ := hw
    have he : ∀ᶠ n in atTop, G.peakReturn (a n) x = 0 := by
      filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy] with n hn
      exact ite_eq_right (fun hh => hyw (hh y hn))
    exact tendsto_const_nhds.congr' (he.mono (fun _ hh => hh.symm))
  · have ht := (G.tendsto_peakCount_of_exhaustion a ω ha hu x hi).inv
    simp only [ENNReal.inv_top] at ht
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall (fun _ => zero_le))
    apply Eventually.of_forall
    intro n
    unfold peakReturn
    split_ifs
    · rfl
    · exact zero_le

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma abs_centeredCoefficient_le_one (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (e : E) :
    |centeredCoefficient p ω e|≤1 := by
  unfold centeredCoefficient
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hp.1,hp.2]

lemma norm_weightedIncidenceTerm_le (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) (e : E) :
    ‖G.weightedIncidenceTerm p ω x e‖ ≤
      (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
  unfold weightedIncidenceTerm
  split_ifs
  · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_centeredCoefficient_le_one p hp ω e)
  · simp

lemma summable_weightedIncidence_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Summable (fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal) := by
  apply ENNReal.summable_toReal
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
    (G.weighted_incidence_le hc hl D K hD hK x _)

lemma abs_weightedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1)
    (ω : Set E) (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    |G.weightedDiscrepancy p ω x| ≤ (D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal := by
  have hs := G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm
  calc
    _ ≤ ∑' e, (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal :=
      tsum_of_norm_bounded hs.hasSum (G.norm_weightedIncidenceTerm_le p hp ω x)
    _ = (∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro e
      split_ifs
      · exact G.bondWeight_ne_top x e
      · exact ENNReal.zero_ne_top
    _ ≤ ((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hm)
        (G.weighted_incidence_le hc hl D K hD hK x _)
    _ = _ := by rw [ENNReal.toReal_mul,ENNReal.toReal_natCast]

lemma measurable_weightedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.weightedDiscrepancy p ω x) := by
  apply Measurable.tsum
  intro e
  unfold weightedIncidenceTerm centeredCoefficient
  apply Measurable.ite
    (Measurable.exists (fun v => (G.measurable_reachable x v).and measurable_const)).setOf
    _ measurable_const
  exact measurable_const.mul (measurable_const.ite (measurable_set_mem e).setOf measurable_const)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_NormalizedDiscrepancy
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

lemma normalizedAbsoluteDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (hp : p∈Icc 0 1) (ω : Set E) (x : V) :
    G.normalizedAbsoluteDiscrepancy p ω x ≤ (D*(2*K) : ℕ) := by
  unfold normalizedAbsoluteDiscrepancy
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [hm]
  · apply (ENNReal.div_le_iff (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).mpr
    calc _ ≤ ENNReal.ofReal ((D*(2*K) : ℕ)*(G.modularMass x (G.cluster ω x)).toReal) :=
          ENNReal.ofReal_le_ofReal (G.abs_weightedDiscrepancy_le hc hl D K hD hK p hp ω x hm)
         _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_natCast,ENNReal.ofReal_toReal hm]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MonotoneBernoulli
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct

lemma uniform01_map_threshold (p : unitInterval) :
    Priority.uniform01.map (fun t : ℝ => t < p) = bitMeasure p := by
  have hm : Measurable (fun t : ℝ => t < p) := (measurable_id.lt measurable_const)
  have ht : Priority.uniform01 {t : ℝ | t < p} = ENNReal.ofReal p := by
    rw [Priority.uniform01,Measure.restrict_apply hm.setOf]
    have he : {t : ℝ | t < p} ∩ Icc 0 1 = Ico (0 : ℝ) (p : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_Icc,Set.mem_Ico]
      exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.le.trans p.property.2⟩⟩
    rw [he,Real.volume_Ico,sub_zero]
  have htrue : (Priority.uniform01.map (fun t : ℝ => t < p)) {True} = bitMeasure p {True} := by
    rw [Measure.map_apply hm (measurableSet_singleton _)]
    have he : (fun t : ℝ => t < p) ⁻¹' {True} = {t : ℝ | t < p} := by ext t; simp
    rw [he,ht]
    simp [bitMeasure,ENNReal.coe_nnreal_eq]
  apply Measure.ext_of_singleton
  intro b
  by_cases hb : b
  · have he : b=True := propext (iff_true_intro hb)
    simpa only [he] using htrue
  · have he : b=False := propext (iff_false_intro hb)
    rw [he]
    have hcompl : ({True} : Set Prop)ᶜ = {False} := by ext a; simp
    rw [←hcompl,measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
      measure_compl (measurableSet_singleton _) (measure_ne_top _ _),htrue,
      Measure.map_apply hm MeasurableSet.univ]
    simp

variable {E : Type*}

lemma measurable_atParameter (p : unitInterval) : Measurable (atParameter (E := E) p) :=
  Measurable.of_eval (fun edge => (measurable_pi_apply edge).lt measurable_const)

lemma markLaw_map_atParameter (p : unitInterval) :
    (markLaw (E := E)).map (atParameter p) = law (fun _ => p) := by
  have he : atParameter (E := E) p = MeasurableEquiv.setOfPred ∘ (fun u : E → ℝ => fun e => u e < p) := rfl
  rw [he,←Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    markLaw,Measure.infinitePi_map_pi (fun _ : E => Priority.uniform01)
      (f := fun _ : E => fun t : ℝ => t < (p : ℝ))
      (fun _ => measurable_id.lt measurable_const)]
  simp only [uniform01_map_threshold,law]

lemma atParameter_mono (u : E → ℝ) : Monotone (fun p : unitInterval => atParameter p u) :=
  fun _ _ hp _ he => (show _ < (_ : ℝ) from he).trans_le hp

lemma atParameter_iUnion (p : unitInterval) (q : ℕ → unitInterval)
    (hqp : ∀ n, q n ≤ p) (hq : Tendsto q atTop (𝓝 p)) (u : E → ℝ) :
    (⋃ n, atParameter (q n) u) = atParameter p u := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset (fun n => atParameter_mono u (hqp n))
  · intro e he
    have he' : u e < (p : ℝ) := he
    have hq' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (p : ℝ)) :=
      continuous_subtype_val.continuousAt.tendsto.comp hq
    obtain ⟨n,hn⟩ := (hq'.eventually (lt_mem_nhds he')).exists
    exact Set.mem_iUnion.mpr ⟨n,hn⟩

lemma measurable_reindexMarks (e : E ≃ E) : Measurable (reindexMarks e) :=
  Measurable.of_eval (fun edge => measurable_pi_apply (e.symm edge))

lemma markLaw_map_reindex (e : E ≃ E) :
    (markLaw (E := E)).map (reindexMarks e) = markLaw := by
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : E => ℝ) e)) = reindexMarks e := by
    funext u x
    obtain ⟨y,rfl⟩ := e.surjective x
    simp [MeasurableEquiv.piCongrLeft_apply_apply,reindexMarks]
  rw [←he]
  exact Measure.infinitePi_map_piCongrLeft (fun _ : E => Priority.uniform01) e

lemma atParameter_reindex (e : E ≃ E) (p : unitInterval) (u : E → ℝ) :
    atParameter p (reindexMarks e u) = e '' atParameter p u := by
  ext x
  obtain ⟨y,rfl⟩ := e.surjective x
  simp [atParameter,reindexMarks]

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_MarkedTiltedTransport
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
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma expected_mark_transport_aut
    (F : (E → ℝ) → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun u => F u x y))
    (ha : ∀ (φ : G.Aut) u x y,
      F (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) = F u x y)
    (φ : G.Aut) (x y : V) :
    (∫⁻ u, F u (φ.vertex x) (φ.vertex y) ∂markLaw) = ∫⁻ u, F u x y ∂markLaw := by
  conv_lhs => rw [←markLaw_map_reindex φ.edge]
  rw [lintegral_map (hm _ _) (measurable_reindexMarks φ.edge)]
  simp only [ha]

omit [Countable E] in
lemma OrbitRepresentatives.mark_tilted_transport (R : G.OrbitRepresentatives)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (F : (E → ℝ) → V → V → ℝ≥0∞) (hm : ∀ x y, Measurable (fun u => F u x y))
    (ha : ∀ (φ : G.Aut) u x y,
      F (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) = F u x y) :
    (∑ x ∈ R.roots, ∫⁻ u, ∑' y, F u x y ∂markLaw) =
      ∑ y ∈ R.roots, ∫⁻ u, ∑' x, F u x y * G.stabilizerWeight y x ∂markLaw := by
  simp_rw [lintegral_tsum (fun y => (hm _ y).aemeasurable),
    lintegral_tsum (fun x => ((hm x _).mul_const _).aemeasurable),
    lintegral_mul_const _ (hm _ _)]
  exact OrbitRepresentatives.tilted_massTransport_ennreal G R hc hl _
    (G.expected_mark_transport_aut F hm ha)

omit [Countable V] [Countable E] in
lemma marks_ae_of_law_ae (p : unitInterval) (P : Set E → Prop) (h : ∀ᵐ ω ∂G.law p, P ω) :
    ∀ᵐ u ∂markLaw, P (atParameter p u) := by
  apply ae_of_ae_map (measurable_atParameter p).aemeasurable
  rwa [markLaw_map_atParameter,BernoulliProduct.law_const]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyThinning
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma measurable_heavyFlag (p : unitInterval) (x : V) :
    Measurable (fun u => G.heavyFlag p u x) :=
  ((G.measurable_modularClusterMass x x).comp (measurable_atParameter p)).eq_const ∞

omit [Countable V] [Countable E] in
lemma heavyFlag_iff_of_reachable (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {p q : unitInterval} (hqp : q≤p) (u : E → ℝ) {x y : V}
    (hxy : (G.openGraph (atParameter q u)).Reachable x y) :
    G.heavyFlag p u x ↔ G.heavyFlag p u y := by
  have hr := hxy.mono (G.openGraph_mono (atParameter_mono u hqp))
  unfold heavyFlag
  rw [G.cluster_eq_of_reachable hr,G.modularMass_eq_top_change_base hc hl x y]

omit [Countable V] [Countable E] in
lemma heavyFlag_aut (φ : G.Aut) (p : unitInterval) (u : E → ℝ) (x : V) :
    G.heavyFlag p (reindexMarks φ.edge u) (φ.vertex x) ↔ G.heavyFlag p u x := by
  unfold heavyFlag
  rw [atParameter_reindex,←φ.cluster_image,φ.modularMass_image]

lemma measurable_heavyRestrictedPeakTransport (p q : unitInterval) (x y : V) :
    Measurable (fun u => G.heavyRestrictedPeakTransport p q u x y) :=
  ((G.measurable_peakRatioTransport x y).comp (measurable_atParameter q)).ite
    (G.measurable_heavyFlag p x).setOf measurable_const

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_aut (p q : unitInterval) (φ : G.Aut)
    (u : E → ℝ) (x y : V) :
    G.heavyRestrictedPeakTransport p q (reindexMarks φ.edge u) (φ.vertex x) (φ.vertex y) =
    G.heavyRestrictedPeakTransport p q u x y := by
  simp only [heavyRestrictedPeakTransport,G.heavyFlag_aut,atParameter_reindex,G.peakRatioTransport_aut]

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_out (p q : unitInterval) (u : E → ℝ) (x : V) :
    (∑' y, G.heavyRestrictedPeakTransport p q u x y) =
    if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 := by
  by_cases h : G.heavyFlag p u x <;> simp only [heavyRestrictedPeakTransport,h,if_true,if_false,
    clusterPeakRatio,tsum_zero]

omit [Countable V] [Countable E] in
lemma heavyRestrictedPeakTransport_swap (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    {p q : unitInterval} (hqp : q≤p) (u : E → ℝ) (x y : V) :
    G.heavyRestrictedPeakTransport p q u x y =
    if G.heavyFlag p u y then G.peakRatioTransport (atParameter q u) x y else 0 := by
  by_cases hy : y∈G.clusterPeaks (atParameter q u) x
  · simp only [heavyRestrictedPeakTransport,G.heavyFlag_iff_of_reachable hc hl hqp u hy.1]
  · simp only [heavyRestrictedPeakTransport,peakRatioTransport,ite_eq_right hy,ite_self]

lemma heavyRestrictedPeakTransport_incoming_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) (y : V) :
    ∀ᵐ u ∂markLaw, (∑' x, G.heavyRestrictedPeakTransport p q u x y * G.stabilizerWeight y x) =
      if G.heavyFlag p u y then G.peakReturn (atParameter q u) y else 0 := by
  have ha := G.marks_ae_of_law_ae q _ (G.peakRatioTransport_incoming_ae hc hl hq q y)
  filter_upwards [ha] with u hu
  simp only [G.heavyRestrictedPeakTransport_swap hc hl hqp]
  by_cases h : G.heavyFlag p u y
  · simpa only [h,if_true] using hu
  · simp only [h,if_false,zero_mul,tsum_zero]

lemma expected_heavy_clusterPeakRatio
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    {p q : unitInterval} (hqp : q≤p) :
    (∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter q u) x else 0 ∂markLaw) =
    ∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter q u) x else 0 ∂markLaw := by
  simp_rw [←G.heavyRestrictedPeakTransport_out]
  rw [OrbitRepresentatives.mark_tilted_transport G (G.orbitRepresentatives hq) hc hl
    (G.heavyRestrictedPeakTransport p q) (G.measurable_heavyRestrictedPeakTransport p q)
    (G.heavyRestrictedPeakTransport_aut p q)]
  apply Finset.sum_congr rfl
  intro x _
  exact lintegral_congr_ae (G.heavyRestrictedPeakTransport_incoming_ae hc hl hq hqp x)

lemma tendsto_expected_heavy_peakReturn
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) (x : V) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  have hmeas (n : ℕ) : Measurable (fun u =>
      if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) :=
    ((G.measurable_peakReturn x).comp (measurable_atParameter (q n))).ite
      (G.measurable_heavyFlag p x).setOf measurable_const
  have hbound (n : ℕ) : ∀ᵐ u ∂markLaw,
      (if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) ≤ (1:ℝ≥0∞) := by
    exact Eventually.of_forall (fun u => by split_ifs; exact G.peakReturn_le_one _ x; exact zero_le)
  have hae := G.marks_ae_of_law_ae p _ (G.no_heavy_finite_peaks_ae hc hl hq p)
  have ht : ∀ᵐ u ∂markLaw, Tendsto (fun n =>
      if G.heavyFlag p u x then G.peakReturn (atParameter (q n) u) x else 0) atTop (𝓝 (0:ℝ≥0∞)) := by
    filter_upwards [hae] with u hu
    by_cases h : G.heavyFlag p u x
    · simp only [h,if_true]
      apply G.tendsto_peakReturn_of_exhaustion _ _
        ((atParameter_mono u).comp hmono) (atParameter_iUnion p q hqp hlim u) x
      by_cases hp : G.clusterPeak (atParameter p u) x
      · right
        intro hf
        exact hu x hf.toFinset.card ⟨h,⟨hf.toFinset,le_rfl,fun _ hy => hf.mem_toFinset.mpr hy⟩,hp⟩
      · exact Or.inl hp
    · simp only [h,if_false]
      exact tendsto_const_nhds
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence (μ := (markLaw : Measure (E → ℝ)))
      (fun _ => (1:ℝ≥0∞)) hmeas hbound (by simp) ht

theorem tendsto_sum_expected_heavy_clusterPeakRatio
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n ≤ p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x ∈ (G.orbitRepresentatives hq).roots,
      ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter (q n) u) x else 0 ∂markLaw)
      atTop (𝓝 0) := by
  simp_rw [G.expected_heavy_clusterPeakRatio hc hl hq (hqp _)]
  have ht := tendsto_finsetSum (G.orbitRepresentatives hq).roots
    (fun x _ => G.tendsto_expected_heavy_peakReturn hc hl hq p q hmono hqp hlim x)
  simpa only [Finset.sum_const_zero] using ht

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation

lemma ennreal_tendsto_zero_of_uniform_tail (f g : ℕ → ℝ≥0∞) (c b : ℕ → ℝ≥0∞)
    (hc : ∀ N, c N≠∞) (hg : Tendsto g atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0))
    (hle : ∀ N n, f n ≤ c N*g n+b N) : Tendsto f atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hh := ENNReal.half_pos hε.ne'
  obtain ⟨N,hN⟩ := (ENNReal.tendsto_nhds_zero.mp hb (ε/2) hh).exists
  have ht : Tendsto (fun n => c N*g n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hg (Or.inr (hc N))
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht (ε/2) hh] with n hn
  exact (hle N n).trans ((add_le_add hn hN).trans_eq (ENNReal.add_halves ε))

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

theorem tendsto_expected_heavy_normalizedDiscrepancy
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫⁻ u, if G.heavyFlag p u x then
      G.normalizedAbsoluteDiscrepancy (q n) (atParameter (q n) u) x else 0 ∂markLaw) atTop (𝓝 0) := by
  let r := fun n => ∫⁻ u, if G.heavyFlag p u x then G.clusterPeakRatio (atParameter (q n) u) x else 0 ∂markLaw
  have hr : Tendsto r atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (G.tendsto_sum_expected_heavy_clusterPeakRatio hc hl hq p q hmono hqp hlim)
    · exact fun _ => zero_le
    · intro n
      exact Finset.single_le_sum (f := fun y => ∫⁻ u,
        if G.heavyFlag p u y then G.clusterPeakRatio (atParameter (q n) u) y else 0 ∂markLaw)
        (fun _ _ => zero_le) hx
  apply ennreal_tendsto_zero_of_uniform_tail _ r
    (fun N => (D*(2*K) : ℕ)*ENNReal.ofReal ((16:ℝ)^N))
    (fun N => (G.orbitRepresentatives hq).roots.card *
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)*
        (ENNReal.ofReal (1/2:ℝ))^N*2)
  · intro N
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  · exact hr
  · let A : ℝ≥0∞ := (G.orbitRepresentatives hq).roots.card *
      ENNReal.ofReal (5*((D*(2*K)^2 : ℕ)*16)^2*((G.orbitRepresentatives hq).roots.card : ℝ)^3+1)
    have hA : A≠∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have ht := ENNReal.Tendsto.const_mul (a := A) (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
      (show ENNReal.ofReal (1/2:ℝ)<1 by norm_num)) (Or.inr hA)
    simpa only [mul_zero,zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr (by norm_num : (2:ℝ≥0∞)≠∞))
  · intro N n
    exact G.expected_heavy_normalizedDiscrepancy_bound_bs hc hl hq D K hD hK p (q n) N x hx

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_SignedDiscrepancyContinuity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma normalizedSignedDiscrepancy_heavy (p : ℝ) (ω : Set E) (x : V)
    (h : G.modularMass x (G.cluster ω x)=∞) : G.normalizedSignedDiscrepancy p ω x=0 := by
  simp [normalizedSignedDiscrepancy,h]

lemma enorm_normalizedSignedDiscrepancy (p : ℝ) (ω : Set E) (x : V) :
    ‖G.normalizedSignedDiscrepancy p ω x‖ₑ=G.normalizedAbsoluteDiscrepancy p ω x := by
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [G.normalizedSignedDiscrepancy_heavy p ω x hm,normalizedAbsoluteDiscrepancy,hm]
  · have hpos : 0<(G.modularMass x (G.cluster ω x)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm
    rw [Real.enorm_eq_ofReal_abs,normalizedSignedDiscrepancy,abs_div,abs_of_pos hpos,
      ENNReal.ofReal_div_of_pos hpos,ENNReal.ofReal_toReal hm]
    rfl

lemma measurable_normalizedSignedDiscrepancy [Countable V] [Countable E] (p : ℝ) (x : V) :
    Measurable (fun ω : Set E => G.normalizedSignedDiscrepancy p ω x) :=
  (G.measurable_weightedDiscrepancy p x).div (G.measurable_modularClusterMass x x).ennreal_toReal

lemma norm_normalizedSignedDiscrepancy_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (ω : Set E) (x : V) :
    ‖G.normalizedSignedDiscrepancy p ω x‖≤(D*(2*K) : ℕ) := by
  have h := G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK p p.property ω x
  rw [←G.enorm_normalizedSignedDiscrepancy,←ENNReal.ofReal_natCast,Real.enorm_eq_ofReal_abs] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

lemma eventually_incident_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (x : V) (e : E) :
    ∀ᶠ n in atTop, (e∈G.incidentEdges (G.cluster (a n) x))=(e∈G.incidentEdges (G.cluster ω x)) := by
  by_cases h : e∈G.incidentEdges (G.cluster ω x)
  · obtain ⟨v,hv,hve⟩ := h
    filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hv] with n hn
    exact propext ⟨fun _ => ⟨v,hv,hve⟩,fun _ => ⟨v,hn,hve⟩⟩
  · apply Eventually.of_forall
    intro n
    apply propext
    constructor
    · rintro ⟨v,hv,hve⟩
      exact ⟨v,G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hv,hve⟩
    · exact fun hn => False.elim (h hn)

lemma eventually_mem_of_exhaustion (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (e : E) :
    ∀ᶠ n in atTop, (e∈a n)=(e∈ω) := by
  by_cases h : e∈ω
  · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hu ▸ h)
    exact eventually_atTop.mpr ⟨n,fun m hm => propext ⟨fun _ => h,fun _ => ha hm hn⟩⟩
  · apply Eventually.of_forall
    intro n
    exact propext ⟨fun hn => hu ▸ Set.mem_iUnion.mpr ⟨n,hn⟩, fun hn => False.elim (h hn)⟩

lemma tendsto_weightedDiscrepancy_of_exhaustion (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (p : unitInterval) (q : ℕ → unitInterval) (hq : Tendsto q atTop (𝓝 p))
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.weightedDiscrepancy (q n) (a n) x) atTop (𝓝 (G.weightedDiscrepancy p ω x)) := by
  have hq' : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 (p : ℝ)) := continuous_subtype_val.continuousAt.tendsto.comp hq
  apply tendsto_tsum_of_dominated_convergence (G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm)
  · intro e
    have heq : ∀ᶠ n in atTop, G.weightedIncidenceTerm (q n) (a n) x e=G.weightedIncidenceTerm (q n) ω x e := by
      filter_upwards [G.eventually_incident_of_exhaustion a ω ha hu x e,
        eventually_mem_of_exhaustion a ω ha hu e] with n hn hn'
      simp only [weightedIncidenceTerm,centeredCoefficient,hn,hn']
    have heq' : (fun n => G.weightedIncidenceTerm (q n) (a n) x e) =ᶠ[atTop]
        (fun n => G.weightedIncidenceTerm (q n) ω x e) := heq
    apply Tendsto.congr' heq'.symm
    by_cases hi : e∈G.incidentEdges (G.cluster ω x)
    · by_cases ho : e∈ω
      · simp only [weightedIncidenceTerm,centeredCoefficient,ite_eq_left hi,ite_eq_left ho]
        exact tendsto_const_nhds.mul (tendsto_const_nhds.sub hq')
      · simp only [weightedIncidenceTerm,centeredCoefficient,ite_eq_left hi,ite_eq_right ho]
        exact tendsto_const_nhds.mul hq'.neg
    · simp only [weightedIncidenceTerm,ite_eq_right hi]
      exact tendsto_const_nhds
  · apply Eventually.of_forall
    intro n e
    apply (G.norm_weightedIncidenceTerm_le (q n) (q n).property (a n) x e).trans
    by_cases hi : e∈G.incidentEdges (G.cluster (a n) x)
    · have hf : e∈G.incidentEdges (G.cluster ω x) := by
        obtain ⟨v,hv,hve⟩ := hi
        exact ⟨v,G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hv,hve⟩
      simp only [ite_eq_left hi,ite_eq_left hf,le_refl]
    · simp only [ite_eq_right hi,ENNReal.toReal_zero]
      exact ENNReal.toReal_nonneg

lemma tendsto_modularMass_toReal_of_exhaustion
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => (G.modularMass x (G.cluster (a n) x)).toReal) atTop
      (𝓝 (G.modularMass x (G.cluster ω x)).toReal) := by
  have hterm (S : Set V) (y : V) : (if y∈S then G.stabilizerWeight x y else 0)≠∞ := by
    split_ifs
    · exact G.stabilizerWeight_ne_top x y
    · exact ENNReal.zero_ne_top
  simp only [modularMass,ENNReal.tsum_toReal_eq (hterm _)]
  apply tendsto_tsum_of_dominated_convergence (ENNReal.summable_toReal hm)
  · intro y
    by_cases hy : y∈G.cluster ω x
    · apply tendsto_const_nhds.congr'
      filter_upwards [G.eventually_cluster_of_exhaustion a ω ha hu hy] with n hn
      simp only [ite_eq_left hy,ite_eq_left hn]
    · have hn (n : ℕ) : y∉G.cluster (a n) x := fun h => hy (G.cluster_mono (hu ▸ Set.subset_iUnion a n) x h)
      simp only [ite_eq_right hy,ite_eq_right (hn _)]
      exact tendsto_const_nhds
  · apply Eventually.of_forall
    intro n y
    by_cases hn : y∈G.cluster (a n) x
    · have hy : y∈G.cluster ω x := G.cluster_mono (hu ▸ Set.subset_iUnion a n) x hn
      simp only [ite_eq_left hn,ite_eq_left hy,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,le_refl]
    · simp only [ite_eq_right hn,ENNReal.toReal_zero,norm_zero]
      exact ENNReal.toReal_nonneg

lemma tendsto_normalizedSignedDiscrepancy_finiteMass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (a : ℕ → Set E) (ω : Set E) (ha : Monotone a) (hu : ⋃ n, a n=ω)
    (p : unitInterval) (q : ℕ → unitInterval) (hq : Tendsto q atTop (𝓝 p))
    (x : V) (hm : G.modularMass x (G.cluster ω x)≠∞) :
    Tendsto (fun n => G.normalizedSignedDiscrepancy (q n) (a n) x) atTop
      (𝓝 (G.normalizedSignedDiscrepancy p ω x)) := by
  exact (G.tendsto_weightedDiscrepancy_of_exhaustion hc hl D K hD hK a ω ha hu p q hq x hm).div
    (G.tendsto_modularMass_toReal_of_exhaustion a ω ha hu x hm)
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le (G.one_le_modularClusterMass ω x))) hm).ne'

lemma integrable_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) (x : V) :
    Integrable (fun u => G.normalizedSignedDiscrepancy p (atParameter p u) x) markLaw := by
  apply Integrable.of_bound
    (((G.measurable_normalizedSignedDiscrepancy p x).comp (measurable_atParameter p)).aestronglyMeasurable)
    (D*(2*K) : ℕ)
  exact Eventually.of_forall (fun u => G.norm_normalizedSignedDiscrepancy_le hc hl D K hD hK p _ x)

theorem tendsto_L1_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫⁻ u, ‖G.normalizedSignedDiscrepancy (q n) (atParameter (q n) u) x -
      G.normalizedSignedDiscrepancy p (atParameter p u) x‖ₑ ∂markLaw) atTop (𝓝 0) := by
  let f := fun (r : unitInterval) u => G.normalizedSignedDiscrepancy r (atParameter r u) x
  have hfm (r : unitInterval) : Measurable (f r) :=
    (G.measurable_normalizedSignedDiscrepancy r x).comp (measurable_atParameter r)
  let a := fun n u => if G.heavyFlag p u x then
    G.normalizedAbsoluteDiscrepancy (q n) (atParameter (q n) u) x else 0
  let b := fun n u => if G.heavyFlag p u x then 0 else ‖f (q n) u-f p u‖ₑ
  have hbm (n : ℕ) : Measurable (b n) :=
    measurable_const.ite (G.measurable_heavyFlag p x).setOf ((hfm _).sub (hfm _)).enorm
  have hb : Tendsto (fun n => ∫⁻ u, b n u ∂markLaw) atTop (𝓝 0) := by
    have hbound (n : ℕ) : ∀ᵐ u ∂markLaw, b n u≤((D*(2*K) : ℕ) : ℝ≥0∞)+((D*(2*K) : ℕ) : ℝ≥0∞) := by
      apply Eventually.of_forall
      intro u
      dsimp only [b]
      split_ifs
      · exact zero_le
      · apply enorm_sub_le.trans
        simpa only [f,G.enorm_normalizedSignedDiscrepancy] using
          add_le_add (G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK _ (q n).property _ x)
            (G.normalizedAbsoluteDiscrepancy_le hc hl D K hD hK _ p.property _ x)
    have ht : ∀ᵐ u ∂markLaw, Tendsto (fun n => b n u) atTop (𝓝 (0:ℝ≥0∞)) := by
      apply Eventually.of_forall
      intro u
      by_cases hh : G.heavyFlag p u x
      · simp only [b,ite_eq_left hh]
        exact tendsto_const_nhds
      · simp only [b,ite_eq_right hh]
        have ht := G.tendsto_normalizedSignedDiscrepancy_finiteMass hc hl D K hD hK
          (fun n => atParameter (q n) u) (atParameter p u) ((atParameter_mono u).comp hmono)
          (atParameter_iUnion p q hqp hlim u) p q hlim x hh
        simpa only [f,sub_self,enorm_zero] using (ht.sub_const (f p u)).enorm
    simpa only [lintegral_zero] using tendsto_lintegral_of_dominated_convergence
      (μ := (markLaw : Measure (E → ℝ)))
      (fun _ => ((D*(2*K) : ℕ) : ℝ≥0∞)+((D*(2*K) : ℕ) : ℝ≥0∞)) hbm hbound (by
        simpa only [lintegral_const,measure_univ,mul_one] using
          (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _,ENNReal.natCast_ne_top _⟩)) ht
  have ha := G.tendsto_expected_heavy_normalizedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx
  have heq (n : ℕ) (u : E → ℝ) : ‖f (q n) u-f p u‖ₑ=a n u+b n u := by
    by_cases hh : G.heavyFlag p u x
    · simp only [a,b,ite_eq_left hh,add_zero,f,G.normalizedSignedDiscrepancy_heavy p _ x hh,
        sub_zero,G.enorm_normalizedSignedDiscrepancy]
    · simp only [a,b,ite_eq_right hh,zero_add]
  change Tendsto (fun n => ∫⁻ u, ‖f (q n) u-f p u‖ₑ ∂markLaw) atTop (𝓝 0)
  have hi (n : ℕ) : (∫⁻ u, ‖f (q n) u-f p u‖ₑ ∂markLaw) =
      (∫⁻ u, a n u ∂markLaw)+(∫⁻ u, b n u ∂markLaw) := by
    simp_rw [heq]
    exact lintegral_add_right _ (hbm n)
  simp_rw [hi]
  simpa only [add_zero] using ha.add hb

 theorem tendsto_expected_normalizedSignedDiscrepancy [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p))
    (x : V) (hx : x∈(G.orbitRepresentatives hq).roots) :
    Tendsto (fun n => ∫ u, G.normalizedSignedDiscrepancy (q n) (atParameter (q n) u) x ∂markLaw)
      atTop (𝓝 (∫ u, G.normalizedSignedDiscrepancy p (atParameter p u) x ∂markLaw)) := by
  apply tendsto_integral_of_L1 (fun u => G.normalizedSignedDiscrepancy p (atParameter p u) x)
  · exact (G.integrable_normalizedSignedDiscrepancy hc hl D K hD hK p x).aestronglyMeasurable
  · exact Eventually.of_forall (fun n => G.integrable_normalizedSignedDiscrepancy hc hl D K hD hK (q n) x)
  · exact G.tendsto_L1_normalizedSignedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_SignedIncidenceTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma normalizedSelectedIncidence_toReal (H : Set E → E → ℝ≥0∞)
    (hH : ∀ ω e, H ω e≠∞) (ω : Set E) (x : V) :
    (G.normalizedSelectedIncidence H ω x).toReal =
      (∑' e, if e∈G.incidentEdges (G.cluster ω x) then
        (H ω e).toReal*(G.bondWeight x e).toReal else 0)*(G.reciprocalClusterMass ω x).toReal := by
  unfold normalizedSelectedIncidence
  rw [ENNReal.toReal_mul,ENNReal.tsum_toReal_eq]
  · congr 1
    apply tsum_congr
    intro e
    split_ifs <;> simp only [ENNReal.toReal_mul,ENNReal.toReal_zero]
  · intro e
    split_ifs
    · exact ENNReal.mul_ne_top (hH ω e) (G.bondWeight_ne_top x e)
    · exact ENNReal.zero_ne_top

lemma normalizedSignedDiscrepancy_eq_selected (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : ℝ) (ω : Set E) (x : V) :
    G.normalizedSignedDiscrepancy p ω x =
      (G.normalizedSelectedIncidence (fun ω e => if e∈ω then 1 else 0) ω x).toReal -
        p*(G.normalizedSelectedIncidence (fun _ _ => 1) ω x).toReal := by
  by_cases hm : G.modularMass x (G.cluster ω x)=∞
  · simp [G.normalizedSignedDiscrepancy_heavy p ω x hm,normalizedSelectedIncidence,reciprocalClusterMass,hm]
  · let A := fun e => (if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0).toReal
    have hAs : Summable A := G.summable_weightedIncidence_bound hc hl D K hD hK ω x hm
    let B := fun e => if e∈ω then A e else 0
    have hBs : Summable B := hAs.indicator (fun e => e∈ω)
    have he (e : E) : G.weightedIncidenceTerm p ω x e=B e-p*A e := by
      by_cases hi : e∈G.incidentEdges (G.cluster ω x) <;> by_cases ho : e∈ω <;>
        simp [weightedIncidenceTerm,centeredCoefficient,A,B,hi,ho] <;> ring
    have hdisc : G.weightedDiscrepancy p ω x=(∑' e, B e)-p*(∑' e, A e) := by
      simp_rw [weightedDiscrepancy,he]
      rw [hBs.tsum_sub (hAs.mul_left p),tsum_mul_left]
    rw [G.normalizedSelectedIncidence_toReal _ (fun _ _ => by
        split_ifs
        · exact ENNReal.one_ne_top
        · exact ENNReal.zero_ne_top),
      G.normalizedSelectedIncidence_toReal _ (fun _ _ => ENNReal.one_ne_top)]
    have hAeq : (fun e => if e∈G.incidentEdges (G.cluster ω x) then
        (1:ℝ≥0∞).toReal*(G.bondWeight x e).toReal else 0)=A := by
      funext e
      by_cases he : e∈G.incidentEdges (G.cluster ω x) <;> simp [A,he]
    have hBeq : (fun e => if e∈G.incidentEdges (G.cluster ω x) then
        (if e∈ω then (1:ℝ≥0∞) else 0).toReal*(G.bondWeight x e).toReal else 0)=B := by
      funext e
      by_cases hi : e∈G.incidentEdges (G.cluster ω x) <;> by_cases ho : e∈ω <;> simp [A,B,hi,ho]
    rw [hAeq,hBeq,normalizedSignedDiscrepancy,hdisc,reciprocalClusterMass,ENNReal.toReal_inv]
    ring

lemma integrable_selectedIncidence_toReal [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (H : Set E → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e)) (hH : ∀ ω e, H ω e≤1) (x : V) :
    Integrable (fun ω => (G.normalizedSelectedIncidence H ω x).toReal) (G.law p) := by
  apply Integrable.of_bound ((G.measurable_normalizedSelectedIncidence H hm x).ennreal_toReal.aestronglyMeasurable)
    (D*(2*K) : ℕ)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono (ENNReal.natCast_ne_top _) (G.normalizedSelectedIncidence_le hc hl D K hD hK H hH ω x)).trans_eq
    (ENNReal.toReal_natCast _)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SignedCountIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

omit [Countable V] [Countable E] in
lemma incidentClusterCount_toReal_le_two (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : (G.incidentClusterCount ω e).toReal≤2 := by
  exact (ENNReal.toReal_mono (by norm_num : (2:ℝ≥0∞)≠∞) (G.incidentClusterCount_le_two hc hl ω e)).trans_eq (by norm_num)

omit [Countable E] in
lemma measurable_centeredCoefficient (p : ℝ) (e : E) :
    Measurable (fun ω : Set E => centeredCoefficient p ω e) :=
  measurable_const.ite (measurable_set_mem e).setOf measurable_const

lemma integrable_centered_incidentClusterCount (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (e : E) :
    Integrable (fun ω => centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal) (G.law p) := by
  apply Integrable.of_bound ((measurable_centeredCoefficient p e).mul
    (G.measurable_incidentClusterCount e).ennreal_toReal).aestronglyMeasurable 2
  apply Eventually.of_forall
  intro ω
  change ‖centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal‖≤2
  rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (mul_le_mul (abs_centeredCoefficient_le_one p p.property ω e)
    (G.incidentClusterCount_toReal_le_two hc hl ω e) ENNReal.toReal_nonneg zero_le_one).trans_eq (one_mul 2)

lemma integrable_selectedIncidenceReturn_toReal (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (H : Set E → E → ℝ≥0∞)
    (hm : ∀ e, Measurable (fun ω => H ω e)) (hH : ∀ ω e, H ω e≤1) (y : V) :
    Integrable (fun ω => (G.selectedIncidenceReturn hl H ω y).toReal) (G.law p) := by
  apply Integrable.of_bound
    (G.measurable_selectedIncidenceReturn hl H hm y).ennreal_toReal.aestronglyMeasurable ((hl y).toFinset.card*2)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num))
    (G.selectedIncidenceReturn_le hc hl H hH ω y)).trans_eq (by simp)

theorem expected_signed_discrepancy_count (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)=
      ∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
        ∫ ω, centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal ∂G.law p := by
  let A : Set E → E → ℝ≥0∞ := fun _ _ => 1
  let B : Set E → E → ℝ≥0∞ := fun ω e => if e∈ω then 1 else 0
  have hAm (e : E) : Measurable (fun ω => A ω e) := measurable_const
  have hBm (e : E) : Measurable (fun ω => B ω e) :=
    measurable_const.ite (measurable_set_mem e).setOf measurable_const
  have hA (ω : Set E) (e : E) : A ω e≤1 := le_rfl
  have hB (ω : Set E) (e : E) : B ω e≤1 := by dsimp [B]; split_ifs <;> simp
  have hAt := G.expected_selectedIncidence_real hc hl hq D K hD hK p A hAm hA (fun _ _ _ => rfl)
  have hBt := G.expected_selectedIncidence_real hc hl hq D K hD hK p B hBm hB (by
    intro φ ω e
    simp only [B,Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right])
  calc
    _ = (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.normalizedSelectedIncidence B ω x).toReal ∂G.law p) -
        (p:ℝ)*(∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, (G.normalizedSelectedIncidence A ω x).toReal ∂G.law p) := by
      rw [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [G.normalizedSignedDiscrepancy_eq_selected hc hl D K hD hK]
      rw [integral_sub (G.integrable_selectedIncidence_toReal hc hl D K hD hK p B hBm hB x)
        ((G.integrable_selectedIncidence_toReal hc hl D K hD hK p A hAm hA x).const_mul p),integral_const_mul]
    _ = _ := by
      rw [hBt,hAt,Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      rw [←integral_const_mul,←integral_sub
        (G.integrable_selectedIncidenceReturn_toReal hc hl p B hBm hB y)
        ((G.integrable_selectedIncidenceReturn_toReal hc hl p A hAm hA y).const_mul p)]
      rw [←integral_finsetSum _ (fun e _ => G.integrable_centered_incidentClusterCount hc hl p e)]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω
      change (G.selectedIncidenceReturn hl B ω y).toReal -
        (p:ℝ)*(G.selectedIncidenceReturn hl A ω y).toReal =
        ∑ e∈(hl y).toFinset, centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal
      rw [G.selectedIncidenceReturn_toReal hc hl B hB,G.selectedIncidenceReturn_toReal hc hl A hA,
        Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : e∈ω <;> simp [A,B,centeredCoefficient,he]; ring

end CriticalPercolation.BondGraph
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_BernoulliSingletonIntegration
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma integral_singleton_decomposition (q : E → unitInterval) (e : E)
    (f : Set E → ℝ) (hm : Measurable f) (C : ℝ) (hb : ∀ ω, ‖f ω‖≤C) :
    (∫ ω, f ω ∂law q) = (q e : ℝ)*(∫ ω, f (forceOn {e} Set.univ ω) ∂law q)+
      (1-(q e : ℝ))*(∫ ω, f (forceOn {e} ∅ ω) ∂law q) := by
  have hi (σ : Set E) : Integrable f ((law q).map (forceOn {e} σ)) := by
    exact Integrable.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hb)
  conv_lhs => rw [law_singleton_decomposition q e]
  rw [integral_add_measure ((hi _).smul_measure (measure_ne_top _ _))
    ((hi _).smul_measure (measure_ne_top _ _)),integral_smul_measure,integral_smul_measure,
    integral_map (measurable_forceOn _ _).aemeasurable hm.aestronglyMeasurable,
    integral_map (measurable_forceOn _ _).aemeasurable hm.aestronglyMeasurable]
  have ht := bitMeasure_real_singleton (q e) True
  have hf := bitMeasure_real_singleton (q e) False
  simp only [measureReal_def,bitWeight,if_true,if_false] at ht hf
  simp only [smul_eq_mul,ht,hf]

lemma integral_centered_singleton (q : E → unitInterval) (e : E)
    (f : Set E → ℝ) (hm : Measurable f) (C : ℝ) (hC : 0≤C) (hb : ∀ ω, ‖f ω‖≤C) :
    (∫ ω, (if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))*f ω ∂law q) =
      (q e : ℝ)*(1-(q e : ℝ))*
        ((∫ ω, f (forceOn {e} Set.univ ω) ∂law q) - (∫ ω, f (forceOn {e} ∅ ω) ∂law q)) := by
  have hm' : Measurable (fun ω => (if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))*f ω) :=
    (measurable_const.ite (measurable_set_mem e).setOf measurable_const).mul hm
  have hb' (ω : Set E) : ‖(if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))*f ω‖≤C := by
    rw [norm_mul]
    have hc : ‖(if e∈ω then 1-(q e : ℝ) else -(q e : ℝ))‖≤1 := by
      split_ifs <;> simp only [Real.norm_eq_abs]
      · rw [abs_of_nonneg (sub_nonneg.mpr (q e).property.2)]
        linarith [(q e).property.1]
      · rw [abs_neg,abs_of_nonneg (q e).property.1]
        exact (q e).property.2
    exact (mul_le_mul_of_nonneg_left (hb ω) (norm_nonneg _)).trans
      ((mul_le_mul_of_nonneg_right hc hC).trans_eq (one_mul C))
  rw [integral_singleton_decomposition q e _ hm' C hb']
  have ht (ω : Set E) : e∈forceOn {e} Set.univ ω := by simp
  have hf (ω : Set E) : e∉forceOn {e} ∅ ω := by simp
  simp only [ite_eq_left (ht _),ite_eq_right (hf _),integral_const_mul]
  ring

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CriticalHeavyIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterCountDrop_of_ends (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.clusterCountDrop ω e =
      if ¬(G.openGraph (ω\{e})).Reachable a b ∧
        ¬(G.modularMass a (G.cluster (ω\{e}) a)=∞ ∧
          G.modularMass b (G.cluster (ω\{e}) b)=∞) then 1 else 0 := by
  have hi : insert e (ω\{e})=insert e ω := by ext f; by_cases h : f=e <;> simp [h]
  simpa only [clusterCountDrop,hi] using G.incidentClusterCount_flip_of_ends hc hl (ω\{e}) e a b he

lemma clusterCountDrop_mem (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : G.clusterCountDrop ω e=0 ∨ G.clusterCountDrop ω e=1 := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.clusterCountDrop_of_ends hc hl ω e a b he.symm]
  split_ifs <;> simp

lemma measurable_clusterCountDrop [Countable V] [Countable E] (e : E) :
    Measurable (fun ω => G.clusterCountDrop ω e) := by
  unfold clusterCountDrop
  exact ((G.measurable_incidentClusterCount e).comp
    (by have h := BernoulliProduct.measurable_forceOn ({e}:Set E) ∅
        change Measurable (fun ω => BernoulliProduct.forceOn {e} ∅ ω) at h
        simpa only [forceOn_empty_singleton] using h)).ennreal_toReal.sub
    ((G.measurable_incidentClusterCount e).comp
    (by have h := BernoulliProduct.measurable_forceOn ({e}:Set E) Set.univ
        change Measurable (fun ω => BernoulliProduct.forceOn {e} Set.univ ω) at h
        simpa only [forceOn_univ_singleton] using h)).ennreal_toReal

lemma integral_centered_incidentClusterCount [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval) (e : E) :
    (∫ ω, centeredCoefficient p ω e*(G.incidentClusterCount ω e).toReal ∂G.law p) =
      -(p:ℝ)*(1-(p:ℝ))*(∫ ω, G.clusterCountDrop ω e ∂G.law p) := by
  have h := BernoulliProduct.integral_centered_singleton (fun _ : E => p) e
    (fun ω => (G.incidentClusterCount ω e).toReal)
    (G.measurable_incidentClusterCount e).ennreal_toReal 2 (by norm_num) (fun ω => by
      simpa only [Function.comp_apply,Real.norm_of_nonneg ENNReal.toReal_nonneg] using
        G.incidentClusterCount_toReal_le_two hc hl ω e)
  rw [BernoulliProduct.law_const, ←show G.law p=ProbabilityTheory.setBernoulli Set.univ p from rfl] at h
  change (∫ ω, (if e∈ω then 1-(p:ℝ) else -(p:ℝ))*(G.incidentClusterCount ω e).toReal ∂G.law p) = _
  rw [h]
  simp only [forceOn_empty_singleton,forceOn_univ_singleton]
  have hi (σ : Set E) : Integrable (fun ω => (G.incidentClusterCount
      (BernoulliProduct.forceOn {e} σ ω) e).toReal) (G.law p) := by
    apply Integrable.of_bound ((G.measurable_incidentClusterCount e).ennreal_toReal.comp
      (BernoulliProduct.measurable_forceOn _ _)).aestronglyMeasurable 2
    exact Eventually.of_forall (fun ω => by
      simpa only [Function.comp_apply,Real.norm_of_nonneg ENNReal.toReal_nonneg] using
        G.incidentClusterCount_toReal_le_two hc hl _ e)
  have hio := hi Set.univ
  have hic := hi ∅
  simp only [forceOn_empty_singleton,forceOn_univ_singleton] at hio hic
  rw [show (∫ ω, G.clusterCountDrop ω e ∂G.law p) =
      (∫ ω, (G.incidentClusterCount (ω\{e}) e).toReal ∂G.law p)-
      (∫ ω, (G.incidentClusterCount (insert e ω) e).toReal ∂G.law p) from integral_sub hic hio]
  ring

theorem expected_signed_discrepancy_drop [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (p : unitInterval) :
    (∑ x∈(G.orbitRepresentatives hq).roots, ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)=
      -(p:ℝ)*(1-(p:ℝ))*(∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
        ∫ ω, G.clusterCountDrop ω e ∂G.law p) := by
  rw [G.expected_signed_discrepancy_count hc hl hq D K hD hK]
  simp_rw [G.integral_centered_incidentClusterCount hc hl,Finset.mul_sum]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ForcedDisconnectContinuity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma forcedClosedSeparated_of_ends (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.forcedClosedSeparated ω e ↔ ¬(G.openGraph (ω\{e})).Reachable a b := by
  unfold forcedClosedSeparated
  constructor
  · rintro ⟨x,hx,y,hy,hxy⟩ hab
    rw [he,Sym2.mem_iff] at hx hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
    · exact hxy (.refl _)
    · exact hxy hab
    · exact hxy hab.symm
    · exact hxy (.refl _)
  · intro h
    exact ⟨a,by simp [he],b,by simp [he],h⟩

lemma disconnectedIndicator_of_ends (ω : Set E) (e : E) (a b : V) (he : G.ends e=s(a,b)) :
    G.disconnectedIndicator ω e=if ¬(G.openGraph (ω\{e})).Reachable a b then 1 else 0 := by
  simp only [disconnectedIndicator,G.forcedClosedSeparated_of_ends ω e a b he]

lemma measurable_forcedClosedSeparated [Countable V] [Countable E] (e : E) :
    Measurable (fun ω => G.forcedClosedSeparated ω e) := by
  unfold forcedClosedSeparated
  apply Measurable.exists
  intro a
  apply measurable_const.and
  apply Measurable.exists
  intro b
  apply measurable_const.and
  exact ((G.measurable_reachable a b).comp (by
    have h := measurable_forceOn ({e}:Set E) ∅
    change Measurable (fun ω => forceOn {e} ∅ ω) at h
    simpa only [forceOn_empty_singleton] using h)).not

lemma measurable_disconnectedIndicator [Countable V] [Countable E] (e : E) :
    Measurable (fun ω => G.disconnectedIndicator ω e) :=
  measurable_const.ite (G.measurable_forcedClosedSeparated e).setOf measurable_const

lemma norm_disconnectedIndicator_le (ω : Set E) (e : E) : ‖G.disconnectedIndicator ω e‖≤1 := by
  unfold disconnectedIndicator
  split_ifs <;> norm_num

lemma clusterCountDrop_eq_disconnected_of_finite (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) (hω : ∀ x, (G.cluster ω x).Finite) :
    G.clusterCountDrop ω e=G.disconnectedIndicator ω e := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.clusterCountDrop_of_ends hc hl ω e a b he.symm,
    G.disconnectedIndicator_of_ends ω e a b he.symm]
  have ha : G.modularMass a (G.cluster (ω\{e}) a)≠∞ :=
    (G.modularMass_finite a ((hω a).subset (G.cluster_mono Set.sdiff_subset a))).ne
  simp only [ha,false_and,not_false_eq_true,and_true]

lemma clusterCountDrop_le_disconnected (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (e : E) : G.clusterCountDrop ω e≤G.disconnectedIndicator ω e := by
  obtain ⟨⟨a,b⟩,he⟩ := Quot.exists_rep (G.ends e)
  rw [G.clusterCountDrop_of_ends hc hl ω e a b he.symm,
    G.disconnectedIndicator_of_ends ω e a b he.symm]
  split_ifs <;> norm_num at *
  tauto

lemma finite_clusters_ae_of_subcritical [Countable V] [Countable E] (p : unitInterval)
    (hp : p<G.criticalProbability) : ∀ᵐ ω ∂G.law p, ∀ x, (G.cluster ω x).Finite := by
  have h := G.law_percolates_eq_zero_of_lt_critical hp
  have ha : ∀ᵐ ω ∂G.law p, ω∉G.percolates := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using h
  filter_upwards [ha] with ω hω x
  by_contra hf
  exact hω ⟨x,hf⟩

lemma clusterCountDrop_eq_disconnected_ae_subcritical [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (p : unitInterval)
    (hp : p<G.criticalProbability) (e : E) :
    (fun ω => G.clusterCountDrop ω e)=ᵐ[G.law p] (fun ω => G.disconnectedIndicator ω e) := by
  filter_upwards [G.finite_clusters_ae_of_subcritical p hp] with ω hω
  exact G.clusterCountDrop_eq_disconnected_of_finite hc hl ω e hω

lemma eventually_disconnectedIndicator (a : ℕ → Set E) (ω : Set E)
    (ha : Monotone a) (hu : ⋃ n, a n=ω) (e : E) :
    ∀ᶠ n in atTop, G.disconnectedIndicator (a n) e=G.disconnectedIndicator ω e := by
  have hmono : Monotone (fun n => a n\{e}) := fun _ _ h => Set.sdiff_subset_sdiff_left (ha h)
  have hU : (⋃ n, a n\{e})=ω\{e} := by
    rw [←Set.iUnion_sdiff,hu]
  obtain ⟨⟨x,y⟩,he⟩ := Quot.exists_rep (G.ends e)
  simp_rw [G.disconnectedIndicator_of_ends _ e x y he.symm]
  by_cases h : (G.openGraph (ω\{e})).Reachable x y
  · filter_upwards [G.eventually_cluster_of_exhaustion (fun n => a n\{e}) (ω\{e}) hmono hU h] with n hn
    change (G.openGraph (a n\{e})).Reachable x y at hn
    simp only [hn,h,not_true_eq_false,if_false]
  · apply Eventually.of_forall
    intro n
    have hn : ¬(G.openGraph (a n\{e})).Reachable x y := fun hn => h
      (G.cluster_mono (Set.sdiff_subset_sdiff_left (hu ▸ Set.subset_iUnion a n)) x hn)
    simp only [hn,h,not_false_eq_true,if_true]

lemma integral_atParameter [Countable V] [Countable E] (p : unitInterval)
    (f : Set E → ℝ) (hf : Measurable f) :
    (∫ u, f (atParameter p u) ∂markLaw) = ∫ ω, f ω ∂G.law p := by
  rw [←integral_map (measurable_atParameter p).aemeasurable hf.aestronglyMeasurable,
    markLaw_map_atParameter,BernoulliProduct.law_const]
  rfl

theorem tendsto_integral_disconnectedIndicator [Countable V] [Countable E]
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) (e : E) :
    Tendsto (fun n => ∫ ω, G.disconnectedIndicator ω e ∂G.law (q n)) atTop
      (𝓝 (∫ ω, G.disconnectedIndicator ω e ∂G.law p)) := by
  have hm (r : unitInterval) : Measurable (fun u => G.disconnectedIndicator (atParameter r u) e) :=
    (G.measurable_disconnectedIndicator e).comp (measurable_atParameter r)
  have ht (u : E → ℝ) : Tendsto (fun n => G.disconnectedIndicator (atParameter (q n) u) e) atTop
      (𝓝 (G.disconnectedIndicator (atParameter p u) e)) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm (G.eventually_disconnectedIndicator (fun n => atParameter (q n) u)
      (atParameter p u) ((atParameter_mono u).comp hmono) (atParameter_iUnion p q hqp hlim u) e))
  have h := tendsto_integral_of_dominated_convergence (μ := (markLaw : Measure (E → ℝ)))
    (fun _ => (1:ℝ)) (fun n => (hm (q n)).aestronglyMeasurable) (integrable_const 1)
    (fun n => Eventually.of_forall (fun u => G.norm_disconnectedIndicator_le _ e)) (Eventually.of_forall ht)
  simpa only [G.integral_atParameter _ _ (G.measurable_disconnectedIndicator e)] using h

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CriticalHeavyDrop
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology BigOperators

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma integrable_disconnectedIndicator (p : unitInterval) (e : E) :
    Integrable (fun ω => G.disconnectedIndicator ω e) (G.law p) :=
  Integrable.of_bound (G.measurable_disconnectedIndicator e).aestronglyMeasurable 1
    (Eventually.of_forall (fun ω => G.norm_disconnectedIndicator_le ω e))

lemma integrable_clusterCountDrop (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (p : unitInterval) (e : E) : Integrable (fun ω => G.clusterCountDrop ω e) (G.law p) := by
  apply Integrable.of_bound (G.measurable_clusterCountDrop e).aestronglyMeasurable 1
  apply Eventually.of_forall
  intro ω
  rcases G.clusterCountDrop_mem hc hl ω e with h|h <;> simp [h]

lemma tendsto_expected_signed_discrepancy_law (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K)
    (p : unitInterval) (q : ℕ → unitInterval) (hmono : Monotone q)
    (hqp : ∀ n, q n≤p) (hlim : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => ∑ x∈(G.orbitRepresentatives hq).roots,
      ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) atTop
      (𝓝 (∑ x∈(G.orbitRepresentatives hq).roots,
        ∫ ω, G.normalizedSignedDiscrepancy p ω x ∂G.law p)) := by
  apply tendsto_finsetSum _
  intro x hx
  have h := G.tendsto_expected_normalizedSignedDiscrepancy hc hl hq D K hD hK p q hmono hqp hlim x hx
  simpa only [G.integral_atParameter _ _ (G.measurable_normalizedSignedDiscrepancy _ x)] using h

theorem critical_expected_drop_eq_disconnected (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1) :
    (∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.clusterCountDrop ω e ∂G.law G.criticalProbability) =
    (∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law G.criticalProbability) := by
  obtain ⟨D,hD0,hD⟩ := G.uniform_incident_bound hq
  obtain ⟨K,hK⟩ := G.uniform_ball_bound hq 1
  obtain ⟨q,hmono,hqmem,hlim⟩ := exists_seq_strictMono_tendsto' hp0
  have hqp : ∀ n, q n≤G.criticalProbability := fun n => (hqmem n).2.le
  have hsig := G.tendsto_expected_signed_discrepancy_law hc hl hq D K hD hK
    G.criticalProbability q hmono.monotone hqp hlim
  have hd : Tendsto (fun n => ∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law (q n)) atTop
      (𝓝 (∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law G.criticalProbability)) := by
    apply tendsto_finsetSum _
    intro y hy
    apply tendsto_finsetSum _
    intro e he
    exact G.tendsto_integral_disconnectedIndicator G.criticalProbability q hmono.monotone hqp hlim e
  have hqreal : Tendsto (fun n => (q n:ℝ)) atTop (𝓝 (G.criticalProbability:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  have hprod := ((hqreal.neg.mul (hqreal.const_sub 1)).mul hd)
  have heq (n : ℕ) : (∑ x∈(G.orbitRepresentatives hq).roots,
      ∫ ω, G.normalizedSignedDiscrepancy (q n) ω x ∂G.law (q n)) =
      -(q n:ℝ)*(1-(q n:ℝ))*(∑ y∈(G.orbitRepresentatives hq).roots, ∑ e∈(hl y).toFinset,
      ∫ ω, G.disconnectedIndicator ω e ∂G.law (q n)) := by
    rw [G.expected_signed_discrepancy_drop hc hl hq D K hD hK]
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    apply Finset.sum_congr rfl
    intro e he
    exact integral_congr_ae (G.clusterCountDrop_eq_disconnected_ae_subcritical hc hl (q n) (hqmem n).2 e)
  have hv := tendsto_nhds_unique hsig (hprod.congr' (Eventually.of_forall (fun n => (heq n).symm)))
  rw [G.expected_signed_discrepancy_drop hc hl hq D K hD hK] at hv
  apply mul_left_cancel₀ (a := -(G.criticalProbability:ℝ)*(1-(G.criticalProbability:ℝ))) _ hv
  exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt (show 0<(G.criticalProbability:ℝ) from hp0)))
    (sub_ne_zero.mpr (ne_of_gt (show (G.criticalProbability:ℝ)<1 from hp1)))

theorem critical_root_incident_drop_ae (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1)
    (y : V) (hy : y∈(G.orbitRepresentatives hq).roots) (e : E) (he : y∈G.ends e) :
    (fun ω => G.disconnectedIndicator ω e)=ᵐ[G.law G.criticalProbability]
      (fun ω => G.clusterCountDrop ω e) := by
  let f := fun (e : E) ω => G.disconnectedIndicator ω e-G.clusterCountDrop ω e
  have hnon (e : E) (ω : Set E) : 0≤f e ω := sub_nonneg.mpr (G.clusterCountDrop_le_disconnected hc hl ω e)
  have hint (e : E) : Integrable (f e) (G.law G.criticalProbability) :=
    (G.integrable_disconnectedIndicator _ e).sub (G.integrable_clusterCountDrop hc hl _ e)
  have hsum : (∑ z∈(G.orbitRepresentatives hq).roots, ∑ a∈(hl z).toFinset,
      ∫ ω, f a ω ∂G.law G.criticalProbability)=0 := by
    simp_rw [f,integral_sub (G.integrable_disconnectedIndicator _ _)
      (G.integrable_clusterCountDrop hc hl _ _),Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (G.critical_expected_drop_eq_disconnected hc hl hq hp0 hp1).symm
  have hout : (∑ a∈(hl y).toFinset, ∫ ω, f a ω ∂G.law G.criticalProbability)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun z hz => Finset.sum_nonneg
      (fun a ha => integral_nonneg (hnon a)))).mp hsum y hy
  have hin : (∫ ω, f e ω ∂G.law G.criticalProbability)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a ha => integral_nonneg (hnon a))).mp hout e
      ((hl y).mem_toFinset.mpr he)
  have hae := (integral_eq_zero_iff_of_nonneg (hnon e) (hint e)).mp hin
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp hω

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_HeavyFiniteGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_distinctHeavyEvent [Countable V] [Countable E] (o x y : V) :
    MeasurableSet (G.distinctHeavyEvent o x y) :=
  ((G.measurable_modularClusterMass o x).eq_const ∞).and
    (((G.measurable_modularClusterMass o y).eq_const ∞).and (G.measurable_reachable x y).not) |>.setOf

lemma Aut.distinctHeavyEvent_image_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (o x y : V) (ω : Set E) :
    φ.edge '' ω ∈ G.distinctHeavyEvent o (φ.vertex x) (φ.vertex y) ↔
      ω∈G.distinctHeavyEvent o x y := by
  have hi (v : V) : G.modularMass o (G.cluster (φ.edge '' ω) (φ.vertex v))=∞ ↔
      G.modularMass o (G.cluster ω v)=∞ := by
    rw [G.modularMass_eq_top_change_base hc hl o (φ.vertex o),←φ.cluster_image,φ.modularMass_image]
  exact and_congr (hi x) (and_congr (hi y)
    (not_congr (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := x) (v := y))))

lemma Aut.distinctHeavyEvent_measure [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (p : unitInterval) (o x y : V) :
    G.law p (G.distinctHeavyEvent o (φ.vertex x) (φ.vertex y))=
      G.law p (G.distinctHeavyEvent o x y) := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_distinctHeavyEvent _ _ _)]
  congr 1
  ext ω
  exact φ.distinctHeavyEvent_image_iff G hc hl o x y ω

lemma distinctHeavy_force_adjacent_length (o : V) (n : ℕ) :
    ∀ (ω : Set E) (x y : V), lengthReach G.fullGraph n x y →
      ω∈G.distinctHeavyEvent o x y →
      ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
        S∪ω∈G.distinctHeavyEvent o a b := by
  induction n with
  | zero =>
    intro ω x y hxy h
    exact False.elim (h.2.2 (hxy ▸ SimpleGraph.Reachable.refl x))
  | succ n ih =>
    rintro ω x y ⟨u,hxu,huy⟩ ⟨hx,hy,hxy⟩
    by_cases hxuω : (G.openGraph ω).Reachable x u
    · refine ⟨∅,Set.finite_empty,u,y,huy,?_⟩
      rw [Set.empty_union]
      refine ⟨?_,hy,fun huy => hxy (hxuω.trans huy)⟩
      rwa [←G.cluster_eq_of_reachable hxuω]
    · obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huy
      have hends : ∀ v∈G.ends e, v∉G.cluster ω x := by
        intro v hv
        rw [he,Sym2.mem_iff] at hv
        rcases hv with rfl|rfl
        · exact hxuω
        · exact hxy
      have hc := G.cluster_insert_edge_unchanged ω e x hends
      have hnewx : G.modularMass o (G.cluster (insert e ω) x)=∞ := hc ▸ hx
      have hay : (G.openGraph (insert e ω)).Adj u y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert e ω,he⟩,hne⟩
      have hnewu : G.modularMass o (G.cluster (insert e ω) u)=∞ := by
        have hh : G.modularMass o (G.cluster (insert e ω) y)=∞ :=
          top_unique (hy ▸ G.modularMass_mono o (G.cluster_mono (Set.subset_insert e ω) y))
        rwa [←G.cluster_eq_of_reachable hay.reachable] at hh
      have hnot : ¬(G.openGraph (insert e ω)).Reachable x u := by
        change u∉G.cluster (insert e ω) x
        rwa [hc]
      obtain ⟨S,hS,a,b,hab,hhab⟩ := ih (insert e ω) x u hxu ⟨hnewx,hnewu,hnot⟩
      refine ⟨insert e S,hS.insert e,a,b,hab,?_⟩
      simpa only [Set.insert_union,Set.union_insert] using hhab

lemma distinctHeavy_force_adjacent (hc : G.fullGraph.Connected) (o : V)
    (ω : Set E) (x y : V) (h : ω∈G.distinctHeavyEvent o x y) :
    ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
      S∪ω∈G.distinctHeavyEvent o a b := by
  obtain ⟨n,hn⟩ := (reachable_iff_exists_lengthReach G.fullGraph x y).mp (hc x y)
  exact G.distinctHeavy_force_adjacent_length o n ω x y hn h

lemma atMostOneHeavy_ae_of_adjacent_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : 0<(p:ℝ)) (o : V)
    (hnull : ∀ x y, G.fullGraph.Adj x y → G.law p (G.distinctHeavyEvent o x y)=0) :
    ∀ᵐ ω ∂G.law p, ω∈G.atMostOneHeavy o := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.fullGraph.Adj x y → (S : Set E)∪ω∉G.distinctHeavyEvent o x y := by
    intro S x y
    by_cases hxy : G.fullGraph.Adj x y
    · have hz := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
        (fun _ => hp) (S : Set E) S.finite_toSet (G.distinctHeavyEvent o x y)
        (G.measurableSet_distinctHeavyEvent o x y)
        (by rw [BernoulliProduct.law_const]; exact hnull x y hxy)
      rw [BernoulliProduct.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E)∪ω∉G.distinctHeavyEvent o x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.distinctHeavy_force_adjacent hc o ω x y ⟨hx,hy,hxy⟩
  have hnot := hω hS.toFinset a b hab
  exact hnot (by simpa only [Set.Finite.coe_toFinset] using hh)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CriticalHeavyUniqueness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma critical_root_adjacent_heavy_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1) (o x y : V)
    (hx : x∈(G.orbitRepresentatives hq).roots) (hxy : G.fullGraph.Adj x y) :
    G.law G.criticalProbability (G.distinctHeavyEvent o x y)=0 := by
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have hae := G.critical_root_incident_drop_ae hc hl hq hp0 hp1 x hx e (by simp [he])
  have han : ∀ᵐ ω ∂G.law G.criticalProbability, ω∉G.distinctHeavyEvent o x y := by
    filter_upwards [hae] with ω hω hbad
    obtain ⟨hxH,hyH,hR⟩ := hbad
    have hclosed : e∉ω := fun h => hR (LazyDFS.prop_openEdge_reachable G ω h he)
    have hs : ω\{e}=ω := by ext f; by_cases hf : f=e <;> simp_all
    have hx' : G.modularMass x (G.cluster ω x)=∞ :=
      (G.modularMass_eq_top_change_base hc hl o x _).mp hxH
    have hy' : G.modularMass y (G.cluster ω y)=∞ :=
      (G.modularMass_eq_top_change_base hc hl o y _).mp hyH
    rw [G.disconnectedIndicator_of_ends ω e x y he,G.clusterCountDrop_of_ends hc hl ω e x y he,hs] at hω
    norm_num [hR,hx',hy'] at hω
  rw [ae_iff] at han
  simpa only [not_not,Set.ofPred_mem_eq] using han

lemma critical_adjacent_heavy_null [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hp0 : 0<G.criticalProbability) (hp1 : G.criticalProbability<1) (o x y : V)
    (hxy : G.fullGraph.Adj x y) :
    G.law G.criticalProbability (G.distinctHeavyEvent o x y)=0 := by
  obtain ⟨r,hr,φ,hφ⟩ := (G.orbitRepresentatives hq).cover x
  obtain ⟨s,hs⟩ := φ.vertex.surjective y
  rw [←hφ,←hs,φ.distinctHeavyEvent_measure G hc hl]
  exact G.critical_root_adjacent_heavy_null hc hl hq hp0 hp1 o r s hr
    ((φ.fullGraph_adj G r s).mp (by simpa only [hφ,hs] using hxy))

theorem atMostOneHeavy_critical_ae_bs_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp1 : G.criticalProbability<1) (o : V) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ω∈G.atMostOneHeavy o := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_cases hp0 : 0<G.criticalProbability
  · exact G.atMostOneHeavy_ae_of_adjacent_null hc G.criticalProbability hp0 o
      (fun x y hxy => G.critical_adjacent_heavy_null hc hl hq hp0 hp1 o x y hxy)
  · have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hp0) (unitInterval.nonneg _)
    rw [he]
    have hnull := G.law_zero_percolates
    have hnp : ∀ᵐ ω ∂G.law 0, ω∉G.percolates := by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hnull
    filter_upwards [hnp] with ω hω
    intro x y hx hy
    exact False.elim (hω ⟨x,G.infinite_of_modularMass_top o hx⟩)

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.atMostOneHeavy_critical_ae_bs_oai.{u_1, u_2}
