-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:53:26.364303+00:00
-- url     : https://prove2.me/submissions/748da8c0-63b8-4d05-a754-ad1086f60275

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_nonunimodular_critical_mass_finite_ae_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_subcritical_seedExpectation_bound_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_uniform_lower_nestedLayer_blocks_bs

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

theorem percolates_null_iff [Countable V] (μ : Measure (Set E)) :
    μ G.percolates = 0 ↔ ∀ v, μ {ω | (G.cluster ω v).Infinite} = 0 := by
  have heq : G.percolates = ⋃ v, {ω | (G.cluster ω v).Infinite} := by
    ext ω
    simp [percolates]
  rw [heq, measure_iUnion_null_iff]

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

lemma finite_subset_cluster_finite_witness {ω : Set E} {v : V} {K : Set V}
    (hK : K.Finite) (hKv : K ⊆ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ K ⊆ G.cluster s v := by
  classical
  have h : ∀ w ∈ K, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v :=
    fun w hw => G.mem_cluster_finite_witness (hKv hw)
  choose s hs hsω hws using h
  let := hK.fintype
  refine ⟨⋃ w : K, s w w.property, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun w => hs w w.property
  · exact Set.iUnion_subset fun w => hsω w w.property
  · intro w hw
    exact G.cluster_mono (Set.subset_iUnion (fun w : K => s w w.property) ⟨w, hw⟩)
      v (hws w hw)

end BondGraph

end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

lemma expect_mul_const (w : E → A → ℝ) (f : (E → A) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  classical
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  ring

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Distribution
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

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_nonneg {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f := by
  rw [← expect_zero w]
  exact expect_mono hw hf

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_const_mul (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact expect_mul_const w f c
end CriticalPercolation.FiniteProduct

end
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

lemma incidentEdges_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v, hv, he⟩
  exact ⟨v, h hv, he⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

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

lemma bitWeight_sum (p : unitInterval) : ∑ b, bitWeight p b = 1 := by
  simp [bitWeight]

lemma bitWeight_nonneg (p : unitInterval) (b : Prop) : 0 ≤ bitWeight p b := by
  unfold bitWeight
  split_ifs
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2

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

lemma integral_bits_eq_expect [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      FiniteProduct.expect (fun e => bitWeight (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold FiniteProduct.expect FiniteProduct.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => bitMeasure_real_singleton (q e) (ω e))

lemma integral_law_eq_expect [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      FiniteProduct.expect (fun e => bitWeight (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, integral_bits_eq_expect]
  rfl

lemma law_map_restrict (q : E → unitInterval) (s : Set E) :
    (law q).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) =
      law (fun e : s => q e) := by
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_set_iff.mpr (fun bond => measurable_set_mem bond.val)
  unfold law
  rw [Measure.map_map hmeas MeasurableEquiv.setOfPred.measurable]
  have hcomp : (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) ∘
      MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ s.domRestrict := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_restrict']

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEvent
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
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteOpenWitness
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma real_law_restrict (p : unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law (fun _ : E => p)).real {ω | s ∩ ω ∈ A} =
      (law (fun _ : s => p)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← law_map_restrict (fun _ : E => p) s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]

lemma finiteWitness_exhaustion (A : Set (Set E)) (hmono : IsUpperSet A)
    (hw : HasFiniteOpenWitness A) (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    (⋃ n, {ω | K n ∩ ω ∈ A}) = A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact hmono Set.inter_subset_right hn
  · intro h
    obtain ⟨s, hs, hsω, hsA⟩ := hw ω h
    obtain ⟨n, hn⟩ := BondGraph.finite_subset_exhaustion K hs (Set.subset_univ _)
    exact Set.mem_iUnion.mpr ⟨n, hmono (Set.subset_inter hn hsω) hsA⟩

lemma finiteWitness_exhaustion_mono (A : Set (Set E)) (hmono : IsUpperSet A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Monotone (fun n => {ω | K n ∩ ω ∈ A}) := by
  intro m n h ω hω
  exact hmono (Set.inter_subset_inter_left _ (K.mono h)) hω

lemma tendsto_real_finiteWitness (p : unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law (fun _ : E => p)).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law (fun _ : E => p))
    (finiteWitness_exhaustion_mono A hmono K)
  rw [finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MeasurableSetRestrict
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurableSet_restrict (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    MeasurableSet {ω | s ∩ ω ∈ A} := by
  let := hs.fintype
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ∩ ω ∈ A} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        {u : Set s | Subtype.val '' u ∈ A} := by
    ext ω
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
      ext e
      simp
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hi]
  rw [he]
  exact hf (.of_discrete)

lemma measurableSet_finiteWitness [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A) : MeasurableSet A := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  rw [← finiteWitness_exhaustion A hmono hw K]
  exact MeasurableSet.iUnion fun n => measurableSet_restrict (K n) (K.finite n) A

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterTail
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterTail_isUpperSet (o : V) (n : ℕ) : IsUpperSet (G.clusterTail o n) := by
  rintro ω ω' h ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω.trans (G.cluster_mono h o), hn⟩

lemma clusterTail_hasFiniteOpenWitness (o : V) (n : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.clusterTail o n) := by
  rintro ω ⟨K, hK, hKω, hn⟩
  obtain ⟨s, hs, hsω, hKs⟩ := G.finite_subset_cluster_finite_witness hK hKω
  exact ⟨s, hs, hsω, K, hK, hKs, hn⟩

lemma infiniteEvent_subset_clusterTail (o : V) (n : ℕ) :
    G.infiniteEvent o ⊆ G.clusterTail o n := by
  intro ω hω
  obtain ⟨K, hKω, hK, hn⟩ := hω.exists_subset_ncard_eq n
  exact ⟨K, hK, hKω, hn.ge⟩

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

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

lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteProductPin
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
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Potential
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
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_prop_mask_pin (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert expect_mask_pin w e b f using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Score
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
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma expect_prop_ite (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e True f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e False g using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

end CriticalPercolation.LazyDFS

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedFresh
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
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
lemma expect_square_add_const (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,expect_const_mul]

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma real_eq_expect_indicator [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = FiniteProduct.expect (fun e => bitWeight (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← integral_law_eq_expect]
  exact (integral_indicator_one (.of_discrete)).symm

end CriticalPercolation.BernoulliProduct
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Fintype E]

lemma prob_eq_real (q : E → unitInterval) (A : Set (Set E)) :
    FiniteProduct.prob (fun e => bitWeight (q e)) (fun ω => ω ∈ A) = (law q).real A := by
  rw [real_eq_expect_indicator]
  unfold FiniteProduct.prob
  rfl

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma clusterTail_iff_card [Fintype V] (ω : Set E) (u : V) (s : ℕ) :
    ω ∈ G.clusterTail u s ↔ s ≤ (G.cluster ω u).toFinset.card := by
  constructor
  · rintro ⟨K,hK,hsub,hs⟩
    exact hs.trans (by simpa only [Set.ncard_eq_toFinset_card'] using Set.ncard_le_ncard hsub)
  · intro hs
    exact ⟨G.cluster ω u, Set.toFinite _, Set.Subset.rfl, by simpa only [Set.ncard_eq_toFinset_card'] using hs⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteInduced
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
variable {V E : Type*} (G : BondGraph V E)

lemma induced_adj_mem (S : Set V) (ω : Set (G.inducedEdges S)) {u v : V}
    (h : (G.openGraph (Subtype.val '' ω)).Adj u v) : u∈S ∧ v∈S := by
  obtain ⟨⟨e,⟨a,ha,rfl⟩,he⟩,_⟩ := h
  constructor
  · exact a.property u (by rw [he]; simp)
  · exact a.property v (by rw [he]; simp)

lemma induce_reachable (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) :
    ((G.induce S).openGraph ω).Reachable u v ↔
      (G.openGraph (Subtype.val '' ω)).Reachable u.val v.val := by
  constructor
  · intro h
    exact h.map ⟨Subtype.val, fun {a b} hab => (G.induce_adj S ω a b).mp hab⟩
  · intro h
    have H : ∀ w, (G.openGraph (Subtype.val '' ω)).Reachable u.val w →
        ∀ hw : w∈S, ((G.induce S).openGraph ω).Reachable u ⟨w,hw⟩ := by
      intro w hh
      rw [SimpleGraph.reachable_iff_reflTransGen] at hh
      induction hh with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail w z _ hz ih =>
        intro hmem
        have hw := (G.induced_adj_mem S ω hz).1
        exact (ih hw).trans ((G.induce_adj S ω ⟨w,hw⟩ ⟨z,hmem⟩).mpr hz).reachable
    exact H v.val h v.property

lemma induced_cluster_subset (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) :
    G.cluster (Subtype.val '' ω) u.val ⊆ S := by
  intro v hv
  rw [cluster,Set.mem_ofPred_eq,SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact u.property
  | tail _ hadj _ => exact (G.induced_adj_mem S ω hadj).2

lemma induce_cluster_image (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) :
    Subtype.val '' ((G.induce S).cluster ω u) = G.cluster (Subtype.val '' ω) u.val := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (G.induce_reachable S ω u a).mp ha
  · intro hv
    have hmem := G.induced_cluster_subset S ω u hv
    exact ⟨⟨v,hmem⟩,(G.induce_reachable S ω u ⟨v,hmem⟩).mpr hv,rfl⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_UniformGeometry
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

lemma uniform_positive_ball_bound (hquasi : G.QuasiTransitive)
    (n : ℕ) : ∃ M : ℕ, 1≤M ∧ ∀ v, (G.vertexBall v n).ncard ≤ M := by
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hquasi n
  exact ⟨M+1,by omega,fun v => (hM v).trans (Nat.le_succ M)⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceDegree
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
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma incident_card_le (S : Set V) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D) :
    (G.incidentEdges S).toFinset.card ≤ S.toFinset.card * D := by
  have he : (G.incidentEdges S).toFinset =
      S.toFinset.biUnion (fun v => (G.incidentEdges {v}).toFinset) := by
    ext e
    constructor
    · intro hh
      obtain ⟨v,hv,hev⟩ := Set.mem_toFinset.mp hh
      exact Finset.mem_biUnion.mpr ⟨v,Set.mem_toFinset.mpr hv,
        Set.mem_toFinset.mpr ⟨v,Set.mem_singleton v,hev⟩⟩
    · intro hh
      obtain ⟨v,hv,hev⟩ := Finset.mem_biUnion.mp hh
      obtain ⟨z,hz,he⟩ := Set.mem_toFinset.mp hev
      have hzv : z=v := Set.mem_singleton_iff.mp hz
      subst z
      exact Set.mem_toFinset.mpr ⟨v,Set.mem_toFinset.mp hv,he⟩
  rw [he]
  calc _ ≤ ∑ v ∈ S.toFinset, (G.incidentEdges {v}).toFinset.card := Finset.card_biUnion_le
       _ ≤ ∑ _v ∈ S.toFinset, D := Finset.sum_le_sum (fun v _ => hD v)
       _ = _ := by simp

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceSearch
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

namespace CriticalPercolation.IncidenceSearch

variable {V E : Type*} [DecidableEq E]

lemma compile_valid (G : BondGraph V E) (v : V) (n : ℕ) (st : State E) :
    (compile G v n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨h.choose_spec.1,ih _,ih _⟩
    · trivial

lemma good_closed (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∉ ω) :
    Good G v ω (st.closed e) := by
  refine ⟨fun a ha => Finset.mem_insert_of_mem (hs.1 ha),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_false (fun h => he.1 (hs.1 h)) hω
    · exact hs.2.1 a ha
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

lemma good_open (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∈ ω) :
    Good G v ω (st.open e) := by
  refine ⟨Finset.insert_subset_insert e hs.1,?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_true (Finset.mem_insert_self _ _) hω
    · have hae : a≠e := fun hh => he.1 (hh ▸ ha)
      simpa only [State.open,Finset.mem_insert,hae,false_or] using hs.2.1 a ha
  · intro a ha
    change a ∈ G.incidentEdges (G.cluster ((insert e st.opened : Finset E) : Set E) v)
    rw [Finset.coe_insert]
    apply G.incidentEdges_mono (G.cluster_mono (Set.subset_insert e (st.opened : Set E)) v)
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha

lemma terminal_cluster (G : BondGraph V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (ht : ¬∃ e, Available G v st e) :
    G.cluster ω v = G.cluster (st.opened : Set E) v ∧
      (st.read : Set E) = G.incidentEdges (G.cluster ω v) := by
  have hread : ∀ e ∈ G.incidentEdges (G.cluster (st.opened : Set E) v), e ∈ st.read := by
    intro e he
    by_contra hh
    exact ht ⟨e,hh,he⟩
  have hc : G.cluster ω v = G.cluster (st.opened : Set E) v := by
    have hh := G.roots_eq_of_incident (S := {v}) (U := G.cluster (st.opened : Set E) v)
      (ω := (st.opened : Set E)) (ω' := ω)
      (by simp only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster])
      (fun e he => hs.2.1 e (hread e he))
    simpa only [ClusterDeletion.roots_singleton,ClusterDeletion.component,BondGraph.cluster] using hh
  refine ⟨hc,?_⟩
  rw [hc]
  exact Set.Subset.antisymm hs.2.2 hread

variable [Fintype E]

lemma compile_terminal (G : BondGraph V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
    (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
    let out := (compile G v n st).run (fun e => decide (e∈ω))
    Good G v ω out ∧ ¬∃ e, Available G v out e := by
  induction n generalizing st with
  | zero => omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : Available G v st e := h.choose_spec
      have hc : (insert e st.read).card = st.read.card+1 := Finset.card_insert_of_notMem he.1
      have hle : st.read.card < Fintype.card E := by
        have hh := Finset.card_le_univ (s := insert e st.read)
        rw [hc] at hh
        omega
      have hn' : Fintype.card E - (insert e st.read).card < n := by rw [hc]; omega
      simp only [SearchTree.run]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        Good G v ω out ∧ ¬∃ a, Available G v out a)
      by_cases hω : e∈ω
      · simp only [hω,decide_true,if_true]
        exact ih (st.open e) (good_open G v ω st hs e he hω) hn'
      · simp only [hω,decide_false,Bool.false_eq_true,if_false]
        exact ih (st.closed e) (good_closed G v ω st hs e he hω) hn'
    · exact ⟨hs,h⟩

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_QueryMartingale
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

variable [Fintype E] [DecidableEq E]

lemma centeredSum_moments (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hf : LazyDFS.Fresh w p used) :
    expect w (t.centeredSum p) = 0 ∧
      expect w (fun ω => (t.centeredSum p ω)^2) =
        p*(1-p)*expect w (fun ω => (t.queryCount ω : ℝ)) := by
  induction t generalizing used w with
  | done r => simp [centeredSum,queryCount,expect_const w hw]
  | ask e l r hl hr =>
    have h0 := hl (insert e used) ht.2.1 (pin w e False)
      (pin_normalized w hw e False) (LazyDFS.fresh_pin w p used hf e False)
    have h1 := hr (insert e used) ht.2.2 (pin w e True)
      (pin_normalized w hw e True) (LazyDFS.fresh_pin w p used hf e True)
    have he := hf e ht.1
    constructor
    · simp only [centeredSum]
      erw [expect_prop_ite]
      simp only [expect_add, expect_const _ (pin_normalized w hw e False),
        expect_const _ (pin_normalized w hw e True),h0.1,h1.1,he.1,he.2]
      ring
    · have hx : (fun ω => ((.ask e l r : SearchTree E R).centeredSum p ω)^2) =
          (fun ω => if ω e then ((1-p)+r.centeredSum p ω)^2
            else (-p+l.centeredSum p ω)^2) := by funext ω; simp only [centeredSum]; split_ifs <;> rfl
      rw [hx]
      erw [expect_prop_ite,
        expect_square_add_const _ (pin_normalized w hw e False),
        expect_square_add_const _ (pin_normalized w hw e True),h0.1,h1.1,h0.2,h1.2,he.1,he.2]
      have hc : (fun ω => ((.ask e l r : SearchTree E R).queryCount ω : ℝ)) =
          (fun ω => 1+(if ω e then (r.queryCount ω : ℝ) else (l.queryCount ω : ℝ))) := by
        funext ω; simp only [queryCount]; split_ifs <;> simp
      rw [hc,expect_add]
      erw [expect_prop_ite,expect_const w hw,he.1,he.2]
      ring

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_IncidenceIdentity
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

namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}

lemma compile_trace (G : BondGraph V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.queryCount ω + st.read.card = out.read.card ∧
      t.centeredSum p ω + readSum p ω st = readSum p ω out := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.queryCount,SearchTree.centeredSum]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hcard : (insert e st.read).card = st.read.card + 1 := Finset.card_insert_of_notMem he
      have hsum : readSum p ω (st.open e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.open,Finset.sum_insert he]
      have hsum' : readSum p ω (st.closed e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (1 + if ω e then (compile G v n (st.open e)).queryCount ω else
          (compile G v n (st.closed e)).queryCount ω) + st.read.card = out.read.card ∧
        (if ω e then (1-p)+(compile G v n (st.open e)).centeredSum p ω else
          -p+(compile G v n (st.closed e)).centeredSum p ω) + readSum p ω st = readSum p ω out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,if_true]
        dsimp only at hopen
        constructor
        · have hh := hopen.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum,ite_eq_left hω] at hopen
          linarith [hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,if_false]
        dsimp only at hclosed
        constructor
        · have hh := hclosed.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum',ite_eq_right hω] at hclosed
          linarith [hclosed.2]
    · simp [SearchTree.run,SearchTree.queryCount,SearchTree.centeredSum]

variable [Fintype E]

lemma tree_valid (G : BondGraph V E) (v : V) : (tree G v).Valid ∅ :=
  compile_valid G v _ _

lemma tree_read (G : BondGraph V E) (v : V) (ω : Set E) :
    (((tree G v).run (fun e => decide (e∈ω))).read : Set E) =
      G.incidentEdges (G.cluster ω v) := by
  have hg : Good G v ω (⟨∅,∅⟩ : State E) := by simp [Good]
  have hh := compile_terminal G v ω (Fintype.card E+1) ⟨∅,∅⟩ hg (by simp)
  exact (terminal_cluster G v ω _ hh.1 hh.2).2

lemma tree_mem_read (G : BondGraph V E) (v : V) (ω : Set E) (e : E) :
    e ∈ ((tree G v).run (fun a => decide (a∈ω))).read ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  exact Set.ext_iff.mp (tree_read G v ω) e

lemma tree_count (G : BondGraph V E) (v : V) (ω : Set E) :
    (tree G v).queryCount ω = (G.incidentEdges (G.cluster ω v)).toFinset.card := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω (0:ℝ)).1
  change (tree G v).queryCount ω + (∅ : Finset E).card =
    ((tree G v).run (fun e => decide (e∈ω))).read.card at h
  simp only [Finset.card_empty,add_zero] at h
  refine h.trans (congrArg Finset.card ?_)
  ext e
  rw [Set.mem_toFinset]
  exact tree_mem_read G v ω e

lemma tree_centered (G : BondGraph V E) (v : V) (ω : Set E) (p : ℝ) :
    (tree G v).centeredSum p ω = ∑ e,
      if e∈G.incidentEdges (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0 := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω p).2
  change (tree G v).centeredSum p ω + readSum p ω ⟨∅,∅⟩ =
    readSum p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [readSum,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then 1-p else -p) else 0 := by
      simp only [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_FiniteClusterTransport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation

lemma finite_subset_size_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (S : Set α) (n : ℕ) :
    (∃ K : Set β, K.Finite ∧ K ⊆ f '' S ∧ n≤K.ncard) ↔
      ∃ K : Set α, K.Finite ∧ K ⊆ S ∧ n≤K.ncard := by
  constructor
  · rintro ⟨K,hK,hKS,hn⟩
    refine ⟨f ⁻¹' K,hK.preimage hf.injOn,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,heq⟩ := hKS ha
      exact hf heq ▸ hb
    · rwa [Set.ncard_preimage_of_injective_subset_range hf
        (hKS.trans (Set.image_subset_range _ _))]
  · rintro ⟨K,hK,hKS,hn⟩
    exact ⟨f '' K,hK.image f,Set.image_mono hKS,
      (Set.ncard_image_of_injective K hf) ▸ hn⟩

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_clusterTail (S : Set V) (ω : Set (G.inducedEdges S)) (u : S) (n : ℕ) :
    ω ∈ (G.induce S).clusterTail u n ↔
      Subtype.val '' ω ∈ G.clusterTail u.val n := by
  change _ ↔ ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster (Subtype.val '' ω) u.val ∧ n≤K.ncard
  rw [← G.induce_cluster_image]
  exact (finite_subset_size_image Subtype.val Subtype.val_injective _ n).symm

lemma induce_law_event (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (A : Set (Set E)) :
    ((G.induce S).law p).real {ω | Subtype.val '' ω ∈ A} =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ A} := by
  simpa only [law,← BernoulliProduct.law_const] using
    (BernoulliProduct.real_law_restrict p (G.inducedEdges S) hS A).symm

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteAdjacentMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_incident_image_subset (S : Set V) (v : S) :
    Subtype.val '' ((G.induce S).incidentEdges {v}) ⊆ G.incidentEdges {v.val} := by
  rintro e ⟨a,ha,rfl⟩
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left] at ha ⊢
  rw [← G.induce_ends_map S a]
  exact Sym2.mem_map.mpr ⟨v,ha,rfl⟩

lemma induce_incident_bound (hlocal : G.LocallyFinite) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (S : Set V) (v : S) :
    ((G.induce S).incidentEdges {v}).ncard ≤ D := by
  calc
    _ = (Subtype.val '' ((G.induce S).incidentEdges {v})).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.incidentEdges {v.val}).ncard := Set.ncard_le_ncard
      (G.induce_incident_image_subset S v) (G.finite_incident hlocal (Set.finite_singleton _))
    _ ≤ D := hD v.val

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

lemma measurable_modularClusterMass [Countable V] [Countable E] (o v : V) :
    Measurable (fun ω : Set E => G.modularMass o (G.cluster ω v)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (G.measurable_reachable v x).setOf measurable_const

end CriticalPercolation.BondGraph
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

end BondGraph
end CriticalPercolation
end
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

lemma finite_clusters_ae_of_subcritical [Countable V] [Countable E] (p : unitInterval)
    (hp : p<G.criticalProbability) : ∀ᵐ ω ∂G.law p, ∀ x, (G.cluster ω x).Finite := by
  have h := G.law_percolates_eq_zero_of_lt_critical hp
  have ha : ∀ᵐ ω ∂G.law p, ω∉G.percolates := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using h
  filter_upwards [ha] with ω hω x
  by_contra hf
  exact hω ⟨x,hf⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ModularGrowth
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

lemma stabilizerOrbit_subset_ball {x y : V} {n : ℕ} (hy : y ∈ G.vertexBall x n) :
    G.stabilizerOrbit x y ⊆ G.vertexBall x n := by
  intro z hz
  obtain ⟨φ,hx,rfl⟩ := G.mem_stabilizerOrbit.mp hz
  rw [←hx]
  exact (Aut.vertexBall_mem G φ x y n).mpr hy

lemma modularRatio_le_suborbitCard (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularRatio x y ≤ (G.suborbitCard x y : ℝ) := by
  apply div_le_self (Nat.cast_nonneg _)
  exact_mod_cast G.suborbitCard_pos hc hl y x

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ContractingDomains
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

lemma safeBallDomain_mono (o : V) (R : ℕ) : Monotone (fun T => G.safeBallDomain o T R) := by
  rintro A B h x ⟨z,hx,hz⟩
  exact ⟨z,hx,fun y hy => (hz y hy).trans h⟩

lemma safeBallDomain_subset (o : V) (T : ℝ) (R : ℕ) :
    G.safeBallDomain o T R⊆{x | G.modularRatio x o≤T} := by
  rintro x ⟨z,hx,hz⟩
  exact hz x hx

lemma modularRatio_ball_upper (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ z y, y∈G.vertexBall z R → G.modularRatio y z≤C := by
  obtain ⟨M,hM,hbound⟩ := G.uniform_positive_ball_bound hq R
  refine ⟨M,by exact_mod_cast hM,?_⟩
  intro z y hy
  calc
    G.modularRatio y z ≤ (G.suborbitCard y z : ℝ) := G.modularRatio_le_suborbitCard hc hl y z
    _ ≤ M := by
      exact_mod_cast (Set.ncard_le_ncard
        (G.stabilizerOrbit_subset_ball ((G.vertexBall_comm).mp hy))
        (G.vertexBall_finite hl y R)).trans (hbound y)

lemma safeBallDomain_low_inclusion (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ o T, {x | G.modularRatio x o≤T/C}⊆G.safeBallDomain o T R := by
  obtain ⟨C,hC,hbound⟩ := G.modularRatio_ball_upper hc hl hq R
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C,hC,?_⟩
  rintro o T x hx
  refine ⟨x,G.mem_vertexBall_self x R,?_⟩
  intro y hy
  rw [←G.modularRatio_cocycle hc hl y x o]
  calc
    G.modularRatio y x * G.modularRatio x o ≤ C*G.modularRatio x o :=
      mul_le_mul_of_nonneg_right (hbound x y hy) (G.modularRatio_pos hc hl x o).le
    _ ≤ T := by
      have hh := (le_div_iff₀ hCp).mp hx
      simpa only [mul_comm] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_MoveWitness
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

lemma walk_induced_support {S : Set V} {ω : Set E} {a b : V}
    (w : (G.openGraph (ω∩G.inducedEdges S)).Walk a b) (hb : b∈S) :
    ∀ x∈w.support, x∈S := by
  induction w with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
    subst x
    exact hb
  | @cons a c b hac w ih =>
    intro x hx
    rcases (List.mem_cons.mp hx) with hxa|hx
    · rw [hxa]
      exact ((G.open_induced_adj S ω a c).mp hac).2.1
    · exact ih hb x hx

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_StripMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_induced_subset (ω : Set E) (S : Set V) {a : V} (ha : a∈S) :
    G.cluster (ω∩G.inducedEdges S) a⊆S := by
  rintro b ⟨w⟩
  exact G.walk_induced_support w.reverse ha b w.reverse.start_mem_support

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_FreshExitWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma freshClusterBoundary_induced_mono {S : Set V} {v : V} (hv : v∈S)
    {ω η : Set E} (hωη : ω⊆η) :
    G.freshClusterBoundary (G.inducedEdges S) v ω ⊆
      G.freshClusterBoundary (G.inducedEdges S) v η := by
  rintro e ⟨⟨x,y,he,hx,hy⟩,heS⟩
  have hyS : y∈S := G.cluster_induced_subset ω S hv hy
  have hxS : x∉S := by
    intro hxS
    apply heS
    intro z hz
    rw [he] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact hxS
    · exact hyS
  refine ⟨⟨x,y,he,fun hx' => hxS (G.cluster_induced_subset η S hv hx'),?_⟩,heS⟩
  exact G.cluster_mono (Set.inter_subset_inter_left _ hωη) v hy

lemma freshExitEvent_upper {S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    IsUpperSet (G.freshExitEvent S v N) := by
  rintro ω η hωη ⟨F,hF,hFω⟩
  exact ⟨F,hF,fun e he =>
    ⟨G.freshClusterBoundary_induced_mono hv hωη (hFω he).1,hωη (hFω he).2⟩⟩

lemma freshExitEvent_finiteWitness {S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    BernoulliProduct.HasFiniteOpenWitness (G.freshExitEvent S v N) := by
  rintro ω ⟨F,hF,hFω⟩
  let X := G.inducedEdges S
  let C := G.cluster (ω∩X) v
  let T : Set V := (⋃ e∈(F : Set E), (↑(G.ends e).toFinset : Set V))∩C
  have hT : T.Finite :=
    (F.finite_toSet.biUnion (fun e _ => (G.ends e).toFinset.finite_toSet)).inter_of_left C
  obtain ⟨J,hJ,hJω,hconn⟩ := G.finite_subset_cluster_finite_witness hT Set.inter_subset_right
  have hsub : J∪(F : Set E)⊆ω := Set.union_subset
    (hJω.trans Set.inter_subset_left) (fun e he => (hFω he).2)
  refine ⟨J∪(F : Set E),hJ.union F.finite_toSet,hsub,F,hF,fun e he => ?_⟩
  obtain ⟨⟨x,y,hexy,_,hy⟩,heX⟩ := (hFω he).1
  have hyT : y∈T := by
    refine ⟨Set.mem_iUnion₂.mpr ⟨e,he,?_⟩,hy⟩
    have hm : y∈G.ends e := by rw [hexy]; simp
    simpa only [Finset.mem_coe,Sym2.mem_toFinset] using hm
  have hyJ : y∈G.cluster ((J∪(F : Set E))∩X) v :=
    G.cluster_mono (Set.subset_inter Set.subset_union_left
      (hJω.trans Set.inter_subset_right)) v (hconn hyT)
  have hx' : x∉G.cluster ((J∪(F : Set E))∩X) v := by
    intro hreach
    apply heX
    intro vertex hvertex
    rw [hexy] at hvertex
    rcases Sym2.mem_iff.mp hvertex with rfl | rfl
    · exact G.cluster_induced_subset (J∪(F : Set E)) S hv hreach
    · exact G.cluster_induced_subset ω S hv hy
  exact ⟨⟨⟨x,y,hexy,hx',hyJ⟩,heX⟩,Or.inr he⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_DomainFreshExit
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
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma domainFreshExitEvent_upper {D S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    IsUpperSet (G.domainFreshExitEvent D S v N) :=
  (G.freshExitEvent_upper hv N).preimage (fun _ _ h => Set.inter_subset_inter_left _ h)

lemma domainFreshExitEvent_finiteWitness {D S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    HasFiniteOpenWitness (G.domainFreshExitEvent D S v N) := by
  intro ω hω
  obtain ⟨F,hF,hFω,hFe⟩ := G.freshExitEvent_finiteWitness hv N _ hω
  refine ⟨F,hF,hFω.trans Set.inter_subset_left,?_⟩
  change F∩G.inducedEdges D ∈ G.freshExitEvent S v N
  rwa [Set.inter_eq_left.mpr (hFω.trans Set.inter_subset_right)]

lemma measurableSet_domainFreshExitEvent [Countable E]
    {D S : Set V} {v : V} (hv : v∈S) (N : ℕ) :
    MeasurableSet (G.domainFreshExitEvent D S v N) :=
  measurableSet_finiteWitness _ (G.domainFreshExitEvent_upper hv N)
    (G.domainFreshExitEvent_finiteWitness hv N)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_NestedLayerGeometry
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

lemma modularRatio_ball_weight (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ C : ℝ, 1≤C ∧ ∀ o x y, y∈G.vertexBall x R →
      G.modularRatio x o≤C*G.modularRatio y o := by
  obtain ⟨C,hC,hbound⟩ := G.modularRatio_ball_upper hc hl hq R
  refine ⟨C,hC,fun o x y hy => ?_⟩
  rw [←G.modularRatio_cocycle hc hl x y o]
  exact mul_le_mul_of_nonneg_right (hbound y x (G.vertexBall_comm.mp hy))
    (G.modularRatio_pos hc hl y o).le

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BlockLocalization
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

lemma finset_weight_lower (o : V) (C : Set V) (F : Finset V) (hF : (F : Set V)⊆C)
    (r : ℝ≥0∞) (hr : ∀ x∈F, r≤G.stabilizerWeight o x) :
    r*F.card≤G.modularMass o C := by
  calc
    r*F.card = ∑ _x∈F, r := by simp [nsmul_eq_mul,mul_comm]
    _ ≤ ∑ x∈F, if x∈C then G.stabilizerWeight o x else 0 := by
      apply Finset.sum_le_sum
      intro x hx
      rw [ite_eq_left (hF hx)]
      exact hr x hx
    _ ≤ _ := ENNReal.sum_le_tsum F

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteSusceptibility
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

namespace CriticalPercolation
open FiniteProduct

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_subset_endpoint_union (ω : Set E) (v : V) :
    G.cluster ω v ⊆ {v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v) := by
  intro z hz
  change (G.openGraph ω).Reachable v z at hz
  rw [SimpleGraph.reachable_iff_reflTransGen] at hz
  induction hz with
  | refl => exact Or.inl rfl
  | @tail u z hv hu _ =>
    obtain ⟨⟨e,he,heq⟩,_⟩ := hu
    have hzmem : z ∈ G.ends e := by rw [heq]; simp
    have heI : e ∈ G.openIncident ω v := by
      exact ⟨⟨u,(SimpleGraph.reachable_iff_reflTransGen _ _).mpr hv,
        by rw [heq]; simp⟩,he⟩
    have hout : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) :=
      (G.ends e).out_eq.symm
    rw [hout,Sym2.mem_iff] at hzmem
    exact Or.inr (hzmem.elim (fun h => Or.inl ⟨e,heI,h.symm⟩)
      (fun h => Or.inr ⟨e,heI,h.symm⟩))

lemma cluster_card_le_open_incident [Fintype V] [Fintype E] (ω : Set E) (v : V) :
    G.clusterSize ω v ≤ 1 + 2*(G.openIncident ω v).ncard := by
  calc
    _ ≤ ({v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v)).ncard := by
      simpa only [clusterSize,← Set.ncard_eq_toFinset_card'] using
        Set.ncard_le_ncard (G.cluster_subset_endpoint_union ω v)
    _ ≤ ({v} : Set V).ncard + (((fun e => (G.ends e).out.1) '' G.openIncident ω v).ncard +
      ((fun e => (G.ends e).out.2) '' G.openIncident ω v).ncard) :=
      (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _)
    _ ≤ _ := by
      have h1 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.1)
      have h2 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.2)
      simp only [Set.ncard_singleton]
      omega

lemma openIncident_card_centered [Fintype E] (p : ℝ) (ω : Set E) (v : V) :
    ((G.openIncident ω v).ncard : ℝ) = (IncidenceSearch.tree G v).centeredSum p ω +
      p*((IncidenceSearch.tree G v).queryCount ω : ℝ) := by
  rw [IncidenceSearch.tree_centered,IncidenceSearch.tree_count]
  simp only [Set.ncard_eq_toFinset_card']
  have ha : ((G.openIncident ω v).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.openIncident ω v then (1:ℝ) else 0 := by simp
  have hb : ((G.incidentEdges (G.cluster ω v)).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.incidentEdges (G.cluster ω v) then (1:ℝ) else 0 := by simp
  rw [ha,hb,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : e∈G.incidentEdges (G.cluster ω v) <;> by_cases ho : e∈ω <;>
    simp [openIncident,hi,ho]

lemma finite_susceptibility_bound [Fintype V] [Fintype E]
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D)
    (hpD : 4*p*D ≤ 1) (v : V) :
    expect w (fun ω => (G.clusterSize {e | ω e} v : ℝ)) ≤ 2 := by
  let t := IncidenceSearch.tree G v
  let a := expect w (fun ω => (G.clusterSize {e | ω e} v : ℝ))
  have hmean := (t.centeredSum_moments ∅ (IncidenceSearch.tree_valid G v) p w hw
    (fun e _ => ⟨h0 e,h1 e⟩)).1
  have hquery : expect w (fun ω => (t.queryCount ω : ℝ)) ≤ D*a := by
    calc
      _ ≤ expect w (fun ω => (D:ℝ)*(G.clusterSize {e | ω e} v : ℝ)) := by
        apply expect_mono hn
        intro ω
        have hcount : t.queryCount ω = (G.incidentEdges (G.cluster {e | ω e} v)).toFinset.card :=
          IncidenceSearch.tree_count G v {e | ω e}
        rw [hcount]
        exact_mod_cast (by simpa only [clusterSize,mul_comm] using
          G.incident_card_le (G.cluster {e | ω e} v) D hD)
      _ = _ := expect_const_mul _ _ _
  have hcluster : a ≤ 1+2*p*(D*a) := by
    calc
      _ ≤ expect w (fun ω => 1+2*((G.openIncident {e | ω e} v).ncard : ℝ)) := by
        apply expect_mono hn
        intro ω
        exact_mod_cast G.cluster_card_le_open_incident {e | ω e} v
      _ = 1+2*p*expect w (fun ω => (t.queryCount ω : ℝ)) := by
        have hopen (ω : E → Prop) : ((G.openIncident {e | ω e} v).ncard : ℝ) =
            t.centeredSum p ω + p*(t.queryCount ω : ℝ) :=
          G.openIncident_card_centered p {e | ω e} v
        simp_rw [hopen]
        rw [expect_add,expect_const w hw,expect_const_mul,expect_add,hmean,
          expect_const_mul]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hquery (mul_nonneg (by norm_num) hp.1 : 0≤2*p)
        linarith
  have ha : 0≤a := expect_nonneg hn (fun _ => Nat.cast_nonneg _)
  nlinarith

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_SusceptibilityMeasure
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
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma finite_clusterTail_measure_bound [Fintype V] [Fintype E]
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (u : V) (s : ℕ) :
    (s:ℝ)*(G.law p).real (G.clusterTail u s) ≤ 2 := by
  let w := fun _ : E => BernoulliProduct.bitWeight p
  have hn : ∀ e b, 0≤w e b := fun _ => BernoulliProduct.bitWeight_nonneg p
  have ht := G.finite_susceptibility_bound p p.property w
    (fun _ => BernoulliProduct.bitWeight_sum p) hn
    (fun _ => by simp only [w,BernoulliProduct.bitWeight,if_false])
    (fun _ => by simp only [w,BernoulliProduct.bitWeight,if_true]) D
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) hpD u
  have hprob : (G.law p).real (G.clusterTail u s) = prob w (fun ω => ω∈G.clusterTail u s) := by
    simpa only [law,← BernoulliProduct.law_const,w] using
      (BernoulliProduct.prob_eq_real (fun _ : E => p) (G.clusterTail u s)).symm
  rw [hprob,prob,← expect_const_mul]
  refine le_trans (expect_mono hn ?_) ht
  intro ω
  change (s:ℝ)*(if {e | ω e}∈G.clusterTail u s then 1 else 0) ≤
    (G.clusterSize {e | ω e} u : ℝ)
  by_cases hh : {e | ω e} ∈ G.clusterTail u s
  · simp only [ite_eq_left hh,mul_one]
    exact_mod_cast (G.clusterTail_iff_card {e | ω e} u s).mp hh
  · simp only [ite_eq_right hh,mul_zero]
    exact Nat.cast_nonneg _

lemma induce_clusterTail_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (u : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).clusterTail u s) =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} := by
  have he : (G.induce S).clusterTail u s =
      {ω | Subtype.val '' ω ∈ G.clusterTail u.val s} := by
    ext ω
    exact G.induce_clusterTail S ω u s
  rw [he,G.induce_law_event S hS]

lemma induced_clusterTail_measure_bound (hlocal : G.LocallyFinite)
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (S : Set V) (hS : S.Finite) (u : S) (s : ℕ) :
    (s:ℝ)*(G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} ≤ 2 := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  have h := (G.induce S).finite_clusterTail_measure_bound p D
    (G.induce_incident_bound hlocal D hD S) hpD u s
  rwa [G.induce_clusterTail_real S (G.finite_inducedEdges hlocal hS)] at h

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_PositiveCritical
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

lemma small_parameter_tail_bound (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1)
    (u : V) (s : ℕ) : (s:ℝ)*(G.law p).real (G.clusterTail u s) ≤ 2 := by
  let K := G.inducedBallExhaustion hconnected hlocal u
  have ht := BernoulliProduct.tendsto_real_finiteWitness p (G.clusterTail u s)
    (G.clusterTail_isUpperSet u s) (G.clusterTail_hasFiniteOpenWitness u s) K
  have ht' : Tendsto (fun n => (s:ℝ)*(G.law p).real {ω | K n ∩ ω ∈ G.clusterTail u s})
      atTop (𝓝 ((s:ℝ)*(G.law p).real (G.clusterTail u s))) := by
    simpa only [law,← BernoulliProduct.law_const] using ht.const_mul (s:ℝ)
  apply le_of_tendsto ht'
  exact Filter.Eventually.of_forall (fun n => G.induced_clusterTail_measure_bound hlocal p D hD hpD
    (G.vertexBall u n) (G.vertexBall_finite hlocal u n) ⟨u,G.mem_vertexBall_self u n⟩ s)

lemma small_parameter_infinite_null (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) (u : V) :
    G.law p (G.infiniteEvent u) = 0 := by
  have hreal : (G.law p).real (G.infiniteEvent u) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! hp
    obtain ⟨n,hn⟩ := exists_nat_gt (2/(G.law p).real (G.infiniteEvent u))
    have hh : (n:ℝ)*(G.law p).real (G.infiniteEvent u) ≤ 2 := by
      calc
        _ ≤ (n:ℝ)*(G.law p).real (G.clusterTail u n) :=
          mul_le_mul_of_nonneg_left (measureReal_mono (G.infiniteEvent_subset_clusterTail u n))
            (Nat.cast_nonneg _)
        _ ≤ 2 := G.small_parameter_tail_bound hconnected hlocal p D hD hpD u n
    have hlt := (div_lt_iff₀ hp).mp hn
    linarith
  have hh := (ENNReal.toReal_eq_zero_iff _).mp hreal
  exact hh.resolve_right (measure_ne_top _ _)

lemma small_parameter_percolates_null (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) :
    G.law p G.percolates = 0 := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  apply (G.percolates_null_iff (G.law p)).mpr
  exact G.small_parameter_infinite_null hconnected hlocal p D hD hpD

theorem criticalProbability_pos (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) :
    (0:ℝ)<G.criticalProbability := by
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hquasi
  have hd : (0:ℝ)<4*(D:ℝ)+1 := by positivity
  let p₀ : unitInterval := ⟨1/(4*(D:ℝ)+1), by
    constructor
    · positivity
    · exact (div_le_one hd).mpr (by
        have hh : (0:ℝ) ≤ 4 * (D:ℝ) := by positivity
        linarith)⟩
  have he : (p₀:ℝ)*(4*(D:ℝ)+1)=1 := div_mul_cancel₀ _ hd.ne'
  have hp₀ : (0:ℝ)<p₀ := one_div_pos.mpr hd
  have hsmall : ∀ p : unitInterval, p≤p₀ → 4*(p:ℝ)*D≤1 := by
    intro p hp
    have hn : (0:ℝ)≤D := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (show (p:ℝ)≤p₀ from hp) hn
    nlinarith [p₀.property.1]
  have hle : p₀≤G.criticalProbability := by
    apply le_sInf
    intro p hp
    by_contra h
    have hpp : p≤p₀ := (not_le.mp h).le
    have hz := G.small_parameter_percolates_null hconnected hlocal p D hD (hsmall p hpp)
    exact (ne_of_gt hp) hz
  exact hp₀.trans_le hle

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_LayerExposure
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
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma entrySeeds_subset_cluster (D : Set V) (o : V) (ω : Set E) :
    G.entrySeeds D o ω⊆G.cluster ω o :=
  fun _ h => G.cluster_mono Set.inter_subset_left o h.1

lemma measurable_entrySeeds [Countable V] [Countable E] (D : Set V) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges D)ᶜ) inferInstance
      (G.entrySeeds D o) := by
  let : MeasurableSpace (Set E) := blockSigma (G.inducedEdges D)ᶜ
  change Measurable (G.entrySeeds D o)
  apply Measurable.of_eval
  intro x
  exact (((measurable_pi_apply x).comp ((G.measurable_cluster o).comp
    (measurable_inter_block (G.inducedEdges D)ᶜ))).and measurable_const)

lemma measurableSet_entrySeed [Countable V] [Countable E] (D : Set V) (o x : V) :
    MeasurableSet[blockSigma (G.inducedEdges D)ᶜ] {ω | x∈G.entrySeeds D o ω} := by
  let : MeasurableSpace (Set E) := blockSigma (G.inducedEdges D)ᶜ
  exact ((measurable_pi_apply x).comp (G.measurable_entrySeeds D o)).setOf

lemma entrySeed_eq_or_adj_exterior {D : Set V} {o x : V} {ω : Set E}
    (hx : x∈G.entrySeeds D o ω) :
    x=o ∨ ∃ y, y∉D ∧ G.fullGraph.Adj x y := by
  by_cases he : x=o
  · exact Or.inl he
  right
  obtain ⟨w⟩ := hx.1.symm
  obtain ⟨y,hxy,w',hw⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne he w
  obtain ⟨⟨e,heω,hexy⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  refine ⟨y,?_,G.openGraph_mono (Set.subset_univ _) hxy⟩
  intro hy
  apply heω.2
  intro z hz
  rw [hexy] at hz
  exact (Sym2.mem_iff.mp hz).elim (fun h => h ▸ hx.2) (fun h => h ▸ hy)

lemma entrySeeds_weight_band_start (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (R : ℕ) :
    ∃ a U : ℝ, 0<a ∧ 0<U ∧ a*U≤1 ∧ (∀ o, o∈G.safeBallDomain o U R) ∧
      ∀ o T, a*T≤1 → ∀ ω x,
      x∈G.entrySeeds (G.safeBallDomain o T R) o ω →
      a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  obtain ⟨B,hB,hball⟩ := G.modularRatio_ball_weight hc hl hq 1
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨1/(C*B),C,by positivity,hC0,?_,?_,fun o T hroot ω x hx => ⟨?_,G.safeBallDomain_subset o T R hx.2⟩⟩
  · have he : (1/(C*B))*C=1/B := by field_simp
    rw [he]
    exact (div_le_one hB0).mpr hB
  · intro o
    apply hlow o C
    change G.modularRatio o o≤C/C
    rw [G.modularRatio_self,div_self hC0.ne']
  rcases G.entrySeed_eq_or_adj_exterior hx with rfl|⟨y,hy,hxy⟩
  · simpa only [G.modularRatio_self] using hroot
  have hlower : T/C<G.modularRatio y o := lt_of_not_ge (fun hh => hy (hlow o T hh))
  have hbound : G.modularRatio y o≤B*G.modularRatio x o :=
    hball o y x (G.vertexBall_comm.mp (G.vertexBall_step (G.mem_vertexBall_self x 0) hxy))
  have : T<(G.modularRatio x o)*(C*B) := by
    have hh := (div_lt_iff₀ hC0).mp (hlower.trans_le hbound)
    nlinarith
  have hh := (div_lt_iff₀ (mul_pos hC0 hB0)).mpr this
  simpa only [one_div,inv_mul_eq_div] using hh.le

lemma layerStopped_eq (D H : Set V) (ω : Set E) :
    ((ω∩(G.inducedEdges D\G.inducedEdges H))∩G.inducedEdges D)∩G.inducedEdges Hᶜ =
      (ω∩G.inducedEdges D)∩G.inducedEdges Hᶜ := by
  ext e
  constructor
  · exact fun h => ⟨⟨h.1.1.1,h.1.2⟩,h.2⟩
  · intro h
    refine ⟨⟨⟨h.1.1,h.1.2,?_⟩,h.1.2⟩,h.2⟩
    intro he
    obtain ⟨x,y,hxy⟩ : ∃ x y, G.ends e=s(x,y) := Sym2.exists.mp ⟨G.ends e,rfl⟩
    have hx : x∈G.ends e := by rw [hxy]; simp
    exact h.2 x hx (he x hx)

lemma domainLayer_restrict (D H : Set V) (x : V) (hx : x∉H) (N : ℕ)
    (ω : Set E) :
    ω∩(G.inducedEdges D\G.inducedEdges H)∈G.domainFreshExitEvent D Hᶜ x N ↔
      ω∈G.domainFreshExitEvent D Hᶜ x N := by
  constructor
  · exact G.domainFreshExitEvent_upper hx N Set.inter_subset_left
  · rintro ⟨F,hF,hFe⟩
    refine ⟨F,hF,?_⟩
    intro e he
    obtain ⟨⟨⟨u,v,hev,hu,hv⟩,heH⟩,heω,heD⟩ := hFe he
    have hvH := G.cluster_induced_subset (ω∩G.inducedEdges D) Hᶜ hx hv
    have hn : e∉G.inducedEdges H := by
      intro hh
      exact hvH (hh v (by rw [hev]; simp))
    have hu' : u∉G.cluster (((ω∩(G.inducedEdges D\G.inducedEdges H))∩G.inducedEdges D)∩
        G.inducedEdges Hᶜ) x := by
      rw [G.layerStopped_eq]
      exact hu
    have hv' : v∈G.cluster (((ω∩(G.inducedEdges D\G.inducedEdges H))∩G.inducedEdges D)∩
        G.inducedEdges Hᶜ) x := by
      rw [G.layerStopped_eq]
      exact hv
    exact ⟨⟨⟨u,v,hev,hu',hv'⟩,heH⟩,⟨heω,heD,hn⟩,heD⟩

lemma boundedLayer_restrict (D H : Set V) (x : V) (hx : x∉H) (N : ℕ) (M : ℝ≥0∞)
    (ω : Set E) :
    ω∩(G.inducedEdges D\G.inducedEdges H)∈G.boundedDomainFreshExitEvent D Hᶜ x N M ↔
      ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M := by
  simp only [boundedDomainFreshExitEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.layerStopped_eq,G.domainLayer_restrict D H x hx N ω]

lemma measurableSet_boundedDomainFreshExit [Countable V] [Countable E]
    (D S : Set V) (x : V) (hx : x∈S) (N : ℕ) (M : ℝ≥0∞) :
    MeasurableSet (G.boundedDomainFreshExitEvent D S x N M) := by
  apply (G.measurableSet_domainFreshExitEvent hx N).inter
  apply measurableSet_le _ measurable_const
  exact (G.measurable_modularClusterMass x x).comp
    (((measurable_inter_block (G.inducedEdges S)).mono (blockSigma_le _) le_rfl).comp
      ((measurable_inter_block (G.inducedEdges D)).mono (blockSigma_le _) le_rfl))

lemma measurableSet_boundedLayer [Countable V] [Countable E]
    (D H : Set V) (x : V) (hx : x∉H) (N : ℕ) (M : ℝ≥0∞) :
    MeasurableSet[blockSigma (G.inducedEdges D\G.inducedEdges H)]
      (G.boundedDomainFreshExitEvent D Hᶜ x N M) := by
  have he : G.boundedDomainFreshExitEvent D Hᶜ x N M=
      (fun ω : Set E => ω∩(G.inducedEdges D\G.inducedEdges H)) ⁻¹'
        G.boundedDomainFreshExitEvent D Hᶜ x N M := by
    ext ω
    exact (G.boundedLayer_restrict D H x hx N M ω).symm
  rw [he]
  exact (G.measurableSet_boundedDomainFreshExit D Hᶜ x hx N M).preimage (measurable_inter_block _)

lemma entry_good_independent [Countable V] [Countable E]
    (q : unitInterval) (D H : Set V) (o x : V) (hx : x∉H) (N : ℕ) (M : ℝ≥0∞) :
    (G.law q) ({ω | x∈G.entrySeeds D o ω}∩G.boundedDomainFreshExitEvent D Hᶜ x N M)=
      (G.law q) {ω | x∈G.entrySeeds D o ω}*
        (G.law q) (G.boundedDomainFreshExitEvent D Hᶜ x N M) := by
  have hdis : Disjoint (G.inducedEdges D)ᶜ (G.inducedEdges D\G.inducedEdges H) :=
    Set.disjoint_left.mpr (fun e he hf => he hf.1)
  simpa only [law,←law_const] using ((independent_disjoint_blocks (fun _ : E => q) _ _ hdis).indepSet_of_measurableSet
    (G.measurableSet_entrySeed D o x) (G.measurableSet_boundedLayer D H x hx N M)).measure_inter_eq_mul

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_LayerCounting
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma openLayerExit_endpoints {D H : Set V} {ω : Set E} {x : V} (hx : x∉H)
    {e : E} (he : e∈G.openLayerExits D H ω x) :
    ∃ u v, G.ends e=s(u,v) ∧ u∈H ∧ v∉H ∧ v∈G.layerComponent D H ω x ∧ e∈ω ∧
      e∈G.inducedEdges D := by
  obtain ⟨⟨⟨u,v,heuv,hu,hv⟩,heH⟩,heω,heD⟩ := he
  have hvH := G.cluster_induced_subset (ω∩G.inducedEdges D) Hᶜ hx hv
  refine ⟨u,v,heuv,?_,hvH,hv,heω,heD⟩
  by_contra huH
  apply heH
  intro z hz
  rw [heuv] at hz
  rcases Sym2.mem_iff.mp hz with rfl|rfl
  · exact huH
  · exact hvH

lemma openLayerExit_child {D H : Set V} (hHD : H⊆D) {o x : V} {ω : Set E}
    (hx : x∈G.entrySeeds D o ω) (hxH : x∉H) {e : E}
    (he : e∈G.openLayerExits D H ω x) :
    e∈G.incidentEdges (G.entrySeeds H o ω) := by
  obtain ⟨u,v,heuv,huH,hvH,hv,heω,heD⟩ := G.openLayerExit_endpoints hxH he
  have hprevious : x∈G.cluster (ω∩(G.inducedEdges H)ᶜ) o := by
    apply G.cluster_mono _ o hx.1
    intro f hf
    exact ⟨hf.1,fun hh => hf.2 (G.inducedEdges_monotone hHD hh)⟩
  have hmiddle : v∈G.cluster (ω∩(G.inducedEdges H)ᶜ) x := by
    apply G.cluster_mono _ x hv
    intro f hf
    refine ⟨hf.1.1,?_⟩
    intro hh
    obtain ⟨a,b,hab⟩ : ∃ a b, G.ends f=s(a,b) := Sym2.exists.mp ⟨G.ends f,rfl⟩
    have ha : a∈G.ends f := by rw [hab]; simp
    exact hf.2 a ha (hh a ha)
  have hneq : v≠u := by intro hh; subst v; exact hvH huH
  have hedge : (G.openGraph (ω∩(G.inducedEdges H)ᶜ)).Adj v u := by
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨e,⟨heω,?_⟩,?_⟩,hneq⟩
    · intro hh
      exact hvH (hh v (by rw [heuv]; simp))
    · rw [heuv,Sym2.eq_swap]
  exact ⟨u,⟨hprevious.trans (hmiddle.trans hedge.reachable),huH⟩,by rw [heuv]; simp⟩

lemma openLayerExit_common_component {D H : Set V} {ω : Set E} {x y : V}
    (hx : x∉H) (hy : y∉H) {e : E}
    (hex : e∈G.openLayerExits D H ω x) (hey : e∈G.openLayerExits D H ω y) :
    y∈G.layerComponent D H ω x := by
  obtain ⟨u,v,heuv,huH,hvH,hv,_,_⟩ := G.openLayerExit_endpoints hx hex
  obtain ⟨a,b,heab,haH,hbH,hb,_,_⟩ := G.openLayerExit_endpoints hy hey
  have hevb : v=b := by
    have heq : s(u,v)=s(a,b) := heuv.symm.trans heab
    rcases Sym2.eq_iff.mp heq with hh|hh
    · exact hh.2
    · exact False.elim (hvH (hh.2 ▸ haH))
  subst b
  exact hv.trans hb.symm

lemma comparable_parents_card_le (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (C : Set V) (A : Finset V) (hAC : (A : Set V)⊆C)
    (a T : ℝ) (ha : 0<a) (hT : 0<T)
    (hband : ∀ y∈A, a*T≤G.modularRatio y o)
    (hx : G.modularRatio x o≤T) (M K : ℕ) (hMK : (M:ℝ)≤a*K)
    (hm : G.modularMass x C≤M) : A.card≤K := by
  have hlow := G.finset_weight_lower o C A hAC (ENNReal.ofReal (a*T))
    (fun y hy => ENNReal.ofReal_le_ofReal (hband y hy))
  have hmass : G.modularMass o C≤ENNReal.ofReal T*M := by
    rw [G.modularMass_change_base hc hl o x C]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hx) hm
  have hh := hlow.trans hmass
  have hh' : a*T*(A.card:ℝ)≤T*M := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (mul_pos ha hT).le,
      ←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul hT.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ)≤T*M)).mp hh
  apply Nat.cast_le.mp (show (A.card:ℝ)≤K from ?_)
  have hc' : a*(A.card:ℝ)≤M := (mul_le_mul_iff_right₀ hT).mp (by
    calc
      T*(a*(A.card:ℝ))=a*T*(A.card:ℝ) := by ring
      _ ≤ T*M := hh')
  exact (mul_le_mul_iff_right₀ ha).mp (hc'.trans hMK)

lemma finite_relation_count {α β : Type*} (A : Finset α) (B : Finset β)
    (r : α → β → Prop) (N K : ℕ)
    (hN : ∀ x∈A, N≤(B.filter (r x)).card)
    (hK : ∀ y∈B, (A.filter (fun x => r x y)).card≤K) :
    N*A.card≤K*B.card := by
  calc
    N*A.card = ∑ _x∈A, N := by simp [Nat.mul_comm]
    _ ≤ ∑ x∈A, (B.filter (r x)).card := Finset.sum_le_sum hN
    _ = ∑ y∈B, (A.filter (fun x => r x y)).card := by
      simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _y∈B, K := Finset.sum_le_sum hK
    _ = K*B.card := by simp [Nat.mul_comm]

lemma layer_exit_fiber_card (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D H : Set V) (ω : Set E) (o : V) (A : Finset V)
    (a T : ℝ) (ha : 0<a) (hT : 0<T) (M N K : ℕ) (hMK : (M:ℝ)≤a*K)
    (hA : ∀ x∈A, x∉H ∧ a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T ∧
      ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M) (e : E) :
    (A.filter (fun x => e∈G.openLayerExits D H ω x)).card≤K := by
  let F := A.filter (fun x => e∈G.openLayerExits D H ω x)
  by_cases hF : F.Nonempty
  · obtain ⟨x,hx⟩ := hF
    have hxA := (Finset.mem_filter.mp hx).1
    apply G.comparable_parents_card_le hc hl o x (G.layerComponent D H ω x) F _
      a T ha hT _ (hA x hxA).2.2.1 M K hMK (hA x hxA).2.2.2.2
    · intro y hy
      exact G.openLayerExit_common_component (hA x hxA).1
        (hA y (Finset.mem_filter.mp hy).1).1 (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
    · intro y hy
      exact (hA y (Finset.mem_filter.mp hy).1).2.1
  · have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card≤K
    rw [he,Finset.card_empty]
    exact Nat.zero_le K

lemma layer_seed_counting (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D H : Set V) (hHD : H⊆D) (ω : Set E) (o : V) (A : Finset V)
    (a T : ℝ) (ha : 0<a) (hT : 0<T) (M N K d : ℕ) (hMK : (M:ℝ)≤a*K)
    (hd : ∀ v, (G.incidentEdges {v}).ncard≤d)
    (hfinite : (G.entrySeeds H o ω).Finite)
    (hA : ∀ x∈A, x∈G.entrySeeds D o ω ∧ x∉H ∧ a*T≤G.modularRatio x o ∧
      G.modularRatio x o≤T ∧ ω∈G.boundedDomainFreshExitEvent D Hᶜ x N M) :
    N*A.card≤K*d*(G.entrySeeds H o ω).ncard := by
  let F := (G.finite_incident hl hfinite).toFinset
  have hN : ∀ x∈A, N≤(F.filter (fun e => e∈G.openLayerExits D H ω x)).card := by
    intro x hx
    obtain ⟨B,hB,hBx⟩ := (hA x hx).2.2.2.2.1
    apply hB.trans (Finset.card_le_card _)
    intro e he
    apply Finset.mem_filter.mpr
    have hh : e∈G.openLayerExits D H ω x := hBx he
    exact ⟨(G.finite_incident hl hfinite).mem_toFinset.mpr
      (G.openLayerExit_child hHD (hA x hx).1 (hA x hx).2.1 hh),hh⟩
  have hK : ∀ e∈F, (A.filter (fun x => e∈G.openLayerExits D H ω x)).card≤K :=
    fun e _ => G.layer_exit_fiber_card hc hl D H ω o A a T ha hT M N K hMK
      (fun x hx => (hA x hx).2) e
  have hcount := finite_relation_count A F (fun x e => e∈G.openLayerExits D H ω x) N K hN hK
  have hF : F.card≤(G.entrySeeds H o ω).ncard*d := by
    rw [←Set.ncard_eq_toFinset_card _ (G.finite_incident hl hfinite)]
    exact G.incident_ncard_le _ hfinite d (fun v _ => hd v)
  calc
    N*A.card ≤ K*F.card := hcount
    _ ≤ K*((G.entrySeeds H o ω).ncard*d) := Nat.mul_le_mul_left K hF
    _ = K*d*(G.entrySeeds H o ω).ncard := by ring

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_LayerExpectation
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation

lemma vertexCount_finite {V : Type*} (S : Set V) (hS : S.Finite) :
    vertexCount S=S.ncard := by
  unfold vertexCount
  rw [tsum_eq_sum (s := hS.toFinset) (fun x hx => ite_eq_right (fun h => hx (hS.mem_toFinset.mpr h)))]
  rw [Set.ncard_eq_toFinset_card S hS]
  calc
    _ = ∑ x∈hS.toFinset, (1:ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact ite_eq_left (hS.mem_toFinset.mp hx)
    _ = _ := by simp

lemma measurable_vertexCount {V Ω : Type*} [Countable V] [MeasurableSpace Ω]
    (S : Ω → Set V) (hS : ∀ x, MeasurableSet {ω | x∈S ω}) : Measurable (fun ω => vertexCount (S ω)) := by
  apply Measurable.tsum
  intro x
  exact measurable_const.ite (hS x) measurable_const

lemma lintegral_vertexCount {V Ω : Type*} [Countable V] [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Ω → Set V) (hS : ∀ x, MeasurableSet {ω | x∈S ω}) :
    (∫⁻ ω, vertexCount (S ω) ∂μ)=∑' x, μ {ω | x∈S ω} := by
  unfold vertexCount
  rw [lintegral_tsum (fun x => (measurable_const.ite (hS x) measurable_const).aemeasurable)]
  apply tsum_congr
  intro x
  exact lintegral_indicator_one (hS x)

namespace BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_goodEntrySeed [Countable V] [Countable E]
    (D H : Set V) (o x : V) (N M : ℕ) :
    MeasurableSet {ω | x∈G.goodEntrySeeds D H o N M ω} := by
  by_cases hx : x∈H
  · have he : {ω | x∈G.goodEntrySeeds D H o N M ω}=∅ := by
      ext ω; simp [goodEntrySeeds,hx]
    rw [he]; exact MeasurableSet.empty
  · have he : {ω | x∈G.goodEntrySeeds D H o N M ω}=
        {ω | x∈G.entrySeeds D o ω}∩G.boundedDomainFreshExitEvent D Hᶜ x N M := by
      ext ω; simp [goodEntrySeeds,hx]
    rw [he]
    exact ((blockSigma_le _) _ (G.measurableSet_entrySeed D o x)).inter
      (G.measurableSet_boundedDomainFreshExit D Hᶜ x hx N M)

lemma lintegral_entrySeeds [Countable V] [Countable E]
    (q : unitInterval) (D : Set V) (o : V) :
    (∫⁻ ω, vertexCount (G.entrySeeds D o ω) ∂G.law q)=G.seedExpectation q D o :=
  lintegral_vertexCount _ _ (fun x => (blockSigma_le _) _ (G.measurableSet_entrySeed D o x))

lemma seedExpectation_self_le [Countable V] [Countable E] (q : unitInterval)
    (D : Set V) (o : V) (ho : o∈D) : 1≤G.seedExpectation q D o := by
  have he : {ω : Set E | o∈G.entrySeeds D o ω}=Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact ⟨SimpleGraph.Reachable.refl o,ho⟩
  have hh := ENNReal.le_tsum (f := fun x => G.law q {ω | x∈G.entrySeeds D o ω}) o
  rw [he,measure_univ] at hh
  exact hh

lemma expected_goodSeeds_lower [Countable V] [Countable E]
    (q : unitInterval) (D H : Set V) (o : V) (N M : ℕ) (θ : ℝ≥0∞)
    (hband : ∀ x, (∃ ω, x∈G.entrySeeds D o ω) → x∉H)
    (hprob : ∀ x, (∃ ω, x∈G.entrySeeds D o ω) →
      θ≤G.law q (G.boundedDomainFreshExitEvent D Hᶜ x N M)) :
    θ*G.seedExpectation q D o≤
      ∫⁻ ω, vertexCount (G.goodEntrySeeds D H o N M ω) ∂G.law q := by
  rw [lintegral_vertexCount _ _ (fun x => G.measurableSet_goodEntrySeed D H o x N M)]
  unfold seedExpectation
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases hx : ∃ ω, x∈G.entrySeeds D o ω
  · have he : {ω | x∈G.goodEntrySeeds D H o N M ω}=
        {ω | x∈G.entrySeeds D o ω}∩G.boundedDomainFreshExitEvent D Hᶜ x N M := by
      ext ω; simp [goodEntrySeeds,hband x hx]
    rw [he,G.entry_good_independent q D H o x (hband x hx) N M,mul_comm θ]
    exact mul_le_mul_right (hprob x hx) _
  · have he : {ω | x∈G.entrySeeds D o ω}=∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hh => hx ⟨ω,hh⟩
    rw [he,measure_empty,mul_zero]
    exact zero_le

lemma expected_layer_expansion [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (q : unitInterval) (hqc : q<G.criticalProbability)
    (D H : Set V) (hHD : H⊆D) (o : V) (a T : ℝ) (ha : 0<a) (hT : 0<T)
    (M N K d : ℕ) (hMK : (M:ℝ)≤a*K) (hd : ∀ v, (G.incidentEdges {v}).ncard≤d)
    (θ : ℝ≥0∞)
    (hband : ∀ ω x, x∈G.entrySeeds D o ω →
      x∉H ∧ a*T≤G.modularRatio x o ∧ G.modularRatio x o≤T)
    (hprob : ∀ x, (∃ ω, x∈G.entrySeeds D o ω) →
      θ≤G.law q (G.boundedDomainFreshExitEvent D Hᶜ x N M)) :
    N*θ*G.seedExpectation q D o≤(K*d)*G.seedExpectation q H o := by
  have hcount : ∀ᵐ ω ∂G.law q, (N:ℝ≥0∞)*vertexCount (G.goodEntrySeeds D H o N M ω)≤
      ((K*d:ℕ):ℝ≥0∞)*vertexCount (G.entrySeeds H o ω) := by
    filter_upwards [G.finite_clusters_ae_of_subcritical q hqc] with ω hω
    have hfD : (G.entrySeeds D o ω).Finite := (hω o).subset (G.entrySeeds_subset_cluster D o ω)
    have hfH : (G.entrySeeds H o ω).Finite := (hω o).subset (G.entrySeeds_subset_cluster H o ω)
    have hfA : (G.goodEntrySeeds D H o N M ω).Finite := hfD.subset Set.inter_subset_left
    have hh := G.layer_seed_counting hc hl D H hHD ω o hfA.toFinset a T ha hT M N K d hMK hd hfH
      (fun x hx => by
        have hx' := hfA.mem_toFinset.mp hx
        exact ⟨hx'.1,(hband ω x hx'.1).1,(hband ω x hx'.1).2.1,(hband ω x hx'.1).2.2,hx'.2.2⟩)
    rw [vertexCount_finite _ hfA,vertexCount_finite _ hfH,Set.ncard_eq_toFinset_card _ hfA]
    exact_mod_cast hh
  have hi := lintegral_mono_ae hcount
  rw [lintegral_const_mul _ (measurable_vertexCount _ (fun x => G.measurableSet_goodEntrySeed D H o x N M)),
    lintegral_const_mul _ (measurable_vertexCount _ (fun x =>
      (blockSigma_le _) _ (G.measurableSet_entrySeed H o x))),G.lintegral_entrySeeds q H o] at hi
  have hlow := G.expected_goodSeeds_lower q D H o N M θ
    (fun x ⟨ω,hω⟩ => (hband ω x hω).1) hprob
  calc
    _ ≤ (N:ℝ≥0∞)*(∫⁻ ω, vertexCount (G.goodEntrySeeds D H o N M ω) ∂G.law q) := by
      simpa only [mul_assoc] using mul_le_mul_right hlow (N:ℝ≥0∞)
    _ ≤ _ := by simpa only [Nat.cast_mul] using hi

end BondGraph
end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_LayerContradiction
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

theorem no_critical_percolation_of_all_light
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (hpc : G.criticalProbability<1) (o : V)
    (hm : ∀ v, ∀ᵐ ω ∂G.law G.criticalProbability,
      G.modularMass v (G.cluster ω v)≠∞) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra hper
  obtain ⟨R,θ,hθ,M,hM,hblock⟩ := G.uniform_lower_nestedLayer_blocks_bs hc hl hq hu o
    G.criticalProbability (G.criticalProbability_pos hc hl hq) hpc
    (lt_of_le_of_ne zero_le (Ne.symm hper)) hm
  obtain ⟨a,U,ha,hU,haU,hstart,hband⟩ := G.entrySeeds_weight_band_start hc hl hq R
  obtain ⟨d,hdpos,hd⟩ := G.uniform_incident_bound hq
  obtain ⟨K,hK⟩ := exists_nat_gt ((M:ℝ)/a)
  have hKpos : 0<K := by
    exact_mod_cast (lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg M) ha.le) hK)
  have hMK : (M:ℝ)≤a*K := by
    have hh := (div_lt_iff₀ ha).mp hK
    linarith
  have hKdpos : (0:ℝ)<(K*d:ℕ) := by exact_mod_cast Nat.mul_pos hKpos (by omega : 0<d)
  obtain ⟨N,hN⟩ := exists_nat_gt (2*((K*d:ℕ):ℝ)/θ)
  have hNθ : 2*((K*d:ℕ):ℝ)≤(N:ℝ)*θ := ((div_lt_iff₀ hθ).mp hN).le
  obtain ⟨δ,hδ,hδ1,hδa,q,hqpos,hqc,hgood⟩ := hblock a ha N
  let T : ℕ → ℝ := fun n => δ^n*U
  let D : ℕ → Set V := fun n => G.safeBallDomain o (T n) R
  let S : ℕ → ℝ≥0∞ := fun n => G.seedExpectation q (D n) o
  have hTpos : ∀ n, 0<T n := fun n => mul_pos (pow_pos hδ n) hU
  have hTs : ∀ n, T (n+1)=δ*T n := by
    intro n
    dsimp [T]
    rw [pow_succ]
    ring
  have hTdec : ∀ n, T (n+1)≤T n := by
    intro n
    rw [hTs]
    exact mul_le_of_le_one_left (hTpos n).le hδ1.le
  have hTU : ∀ n, T n≤U := by
    intro n
    induction n with
    | zero => simp [T]
    | succ n ih => exact (hTdec n).trans ih
  have haT : ∀ n, a*T n≤1 := fun n =>
    (mul_le_mul_of_nonneg_left (hTU n) ha.le).trans haU
  have hD : ∀ n, D (n+1)⊆D n := fun n => G.safeBallDomain_mono o R (hTdec n)
  have hseed : ∀ n ω x, x∈G.entrySeeds (D n) o ω →
      x∉D (n+1) ∧ a*T n≤G.modularRatio x o ∧ G.modularRatio x o≤T n := by
    intro n ω x hx
    have hb := hband o (T n) (haT n) ω x hx
    refine ⟨?_,hb⟩
    intro hh
    have he := G.safeBallDomain_subset o (T (n+1)) R hh
    change G.modularRatio x o≤T (n+1) at he
    rw [hTs] at he
    nlinarith [hTpos n]
  have hprob : ∀ n x, (∃ ω, x∈G.entrySeeds (D n) o ω) →
      ENNReal.ofReal θ≤G.law q (G.boundedDomainFreshExitEvent (D n) (D (n+1))ᶜ x N M) := by
    rintro n x ⟨ω,hω⟩
    have hh := hgood (T n) (hTpos n) x hω.2 (hseed n ω x hω).2.1
    change θ<(G.law q (G.boundedDomainFreshExitEvent (D n)
      (G.safeBallDomain o (δ*T n) R)ᶜ x N M)).toReal at hh
    have he := ENNReal.ofReal_le_ofReal hh.le
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at he
    simpa only [D,hTs] using he
  obtain ⟨C,hC,hbound⟩ := G.subcritical_seedExpectation_bound_bs hl hq q hqc o
  have hSFin : ∀ n, S n≠∞ := fun n => ne_top_of_le_ne_top hC (hbound (D n))
  have hstep : ∀ n, 2*(S n).toReal≤(S (n+1)).toReal := by
    intro n
    have he := G.expected_layer_expansion hc hl q hqc (D n) (D (n+1)) (hD n) o a (T n)
      ha (hTpos n) M N K d hMK hd (ENNReal.ofReal θ) (hseed n) (hprob n)
    have hf : ((K:ℝ≥0∞)*d)*S (n+1)≠∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) (hSFin (n+1))
    have hr := ENNReal.toReal_mono hf he
    change (((N:ℝ≥0∞)*ENNReal.ofReal θ)*S n).toReal≤
      (((K:ℝ≥0∞)*d)*S (n+1)).toReal at hr
    simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hθ.le] at hr
    have hn := mul_le_mul_of_nonneg_right hNθ (ENNReal.toReal_nonneg (a := S n))
    push_cast at hn hKdpos
    nlinarith
  have hinit : 1≤(S 0).toReal := by
    have he := G.seedExpectation_self_le q (D 0) o (by simpa [D,T] using hstart o)
    have hh := ENNReal.toReal_mono (hSFin 0) he
    simpa using hh
  have hgrow : ∀ n : ℕ, (n:ℝ)+1≤(S n).toReal := by
    intro n
    induction n with
    | zero => simpa using hinit
    | succ n ih =>
      have hs := hstep n
      push_cast
      have hn : (0:ℝ)≤n := Nat.cast_nonneg n
      nlinarith
  obtain ⟨n,hn⟩ := exists_nat_gt C.toReal
  have hh := (hgrow n).trans (ENNReal.toReal_mono hC (hbound (D n)))
  linarith

theorem nonunimodular_no_percolation_at_criticality_bs_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (hpc : G.criticalProbability<1) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨o⟩ := hc.nonempty
  apply G.no_critical_percolation_of_all_light hc hl hq hu hpc o
  intro v
  exact (G.nonunimodular_critical_mass_finite_ae_bs hc hl hq hpc hu v).mono (fun _ h => (h v).ne)

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs_oai.{u_1, u_2}
