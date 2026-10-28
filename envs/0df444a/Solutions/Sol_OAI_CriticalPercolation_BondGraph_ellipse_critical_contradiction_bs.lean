-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:47:39.319338+00:00
-- url     : https://prove2.me/submissions/6cd4f9e3-cb5a-4f0b-b577-263d3d8bb678

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction_bs

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

end CriticalPercolation.FiniteProduct

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ContinuousExpectWeights
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

namespace CriticalPercolation.FiniteProduct
variable {E B : Type*} [Fintype E] [Fintype B]

lemma continuous_expect_weights (f : (E → B) → ℝ) :
    Continuous (fun w : E → B → ℝ => expect w f) := by
  classical
  unfold expect density
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  exact (continuous_apply (ω e)).comp (continuous_apply e)

end CriticalPercolation.FiniteProduct

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

lemma continuous_bitWeight (b : Prop) : Continuous (fun p : unitInterval => bitWeight p b) := by
  by_cases hb : b
  · simpa [bitWeight, hb] using (continuous_subtype_val : Continuous (fun p : unitInterval => (p : ℝ)))
  · simp only [bitWeight, ite_eq_right hb]
    fun_prop

lemma continuous_real_law_finite [Fintype E] (A : Set (Set E)) :
    Continuous (fun p : unitInterval => (law (fun _ : E => p)).real A) := by
  have h (p : unitInterval) : (law (fun _ : E => p)).real A =
      FiniteProduct.expect (fun _ : E => bitWeight p)
        (fun ω : E → Prop => A.indicator (fun _ => (1 : ℝ)) {e | ω e}) := by
    rw [← integral_law_eq_expect]
    exact (integral_indicator_one (.of_discrete) :
      (∫ ω, A.indicator (1 : Set E → ℝ) ω ∂law (fun _ : E => p)) = _).symm
  simp_rw [h]
  apply (FiniteProduct.continuous_expect_weights _).comp
  exact continuous_pi fun _ => continuous_pi fun b => continuous_bitWeight b

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

lemma continuous_real_law_restrict (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    Continuous (fun p : unitInterval => (law (fun _ : E => p)).real
      {ω | s ∩ ω ∈ A}) := by
  let := hs.fintype
  simp_rw [real_law_restrict _ s hs A]
  exact continuous_real_law_finite _

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

lemma lowerSemicontinuous_real_finiteWitness [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A) :
    LowerSemicontinuous (fun p : unitInterval => (law (fun _ : E => p)).real A) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  intro p a ha
  have ht := (tendsto_real_finiteWitness p A hmono hw K).eventually (lt_mem_nhds ha)
  obtain ⟨n, hn⟩ := ht.exists
  have hc := (continuous_real_law_restrict (K n) (K.finite n) A).continuousAt (x := p)
  filter_upwards [hc.eventually (lt_mem_nhds hn)] with q hq
  exact lt_of_lt_of_le hq (measureReal_mono (fun ω hω => hmono Set.inter_subset_right hω))

lemma exists_lower_parameter [Countable E] {I : Type*} [Finite I]
    (A : I → Set (Set E)) (hmono : ∀ i, IsUpperSet (A i))
    (hw : ∀ i, HasFiniteOpenWitness (A i)) (p : unitInterval) (hp : 0 < p)
    (a : I → ℝ) (ha : ∀ i, a i < (law (fun _ : E => p)).real (A i)) :
    ∃ q : unitInterval, (p : ℝ) / 2 ≤ q ∧ q < p ∧
      ∀ i, a i < (law (fun _ : E => q)).real (A i) := by
  have hall : ∀ᶠ q in 𝓝 p, ∀ i, a i < (law (fun _ : E => q)).real (A i) :=
    Filter.eventually_all.mpr fun i =>
      lowerSemicontinuous_real_finiteWitness (A i) (hmono i) (hw i) p (a i) (ha i)
  have hp' : (0 : ℝ) < p := hp
  have hhalf : ∀ᶠ q : unitInterval in 𝓝 p, (p : ℝ) / 2 < q :=
    continuous_subtype_val.continuousAt.eventually (lt_mem_nhds (by linarith : (p : ℝ) / 2 < p))
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
  obtain ⟨q, hq, hqp, hqA⟩ :=
    ((hhalf.filter_mono nhdsWithin_le_nhds).and
      ((show ∀ᶠ q in 𝓝[<] p, q < p from self_mem_nhdsWithin).and
        (hall.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨q, le_of_lt hq, hqp, hqA⟩

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

lemma measurableSet_clusterTail [Countable E] (o : V) (n : ℕ) :
    MeasurableSet (G.clusterTail o n) :=
  BernoulliProduct.measurableSet_finiteWitness _ (G.clusterTail_isUpperSet o n)
    (G.clusterTail_hasFiniteOpenWitness o n)

lemma clusterTail_antitone (o : V) : Antitone (G.clusterTail o) := by
  rintro m n h ω ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω, h.trans hn⟩

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DiskWinding
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

namespace CriticalPercolation.DiskWinding

lemma increment_add_of_short {a b c : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) :
    increment a b+increment b c=increment a c := by
  let z := increment a b+increment b c-increment a c
  have hco : (z : Real.Angle)=0 := by
    simp only [z,increment,Real.Angle.coe_sub,Real.Angle.coe_add,Real.Angle.coe_toReal]
    abel
  have hbounded : -Real.pi<z ∧ z≤Real.pi := by
    obtain ⟨habl,habu⟩ := abs_lt.mp hab
    obtain ⟨hbcl,hbcu⟩ := abs_lt.mp hbc
    obtain ⟨hacl,hacu⟩ := abs_lt.mp hac
    dsimp [z]
    constructor <;> linarith [Real.pi_pos]
  have hz := Real.Angle.toReal_coe_eq_self_iff.mpr hbounded
  rw [hco,Real.Angle.toReal_zero] at hz
  dsimp [z] at hz
  linarith

lemma sum_successive_sub (f : ℕ → ℝ) (K : ℕ) :
    ∑ k∈Finset.range K, (f (k+1)-f k)=f K-f 0 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; ring

lemma cell_balance {a b c d : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) (had : |increment a d|<Real.pi/4)
    (hdc : |increment d c|<Real.pi/4) :
    increment a b+increment b c=increment a d+increment d c :=
  (increment_add_of_short hab hbc hac).trans (increment_add_of_short had hdc hac).symm

theorem boundary_sum_zero (F : ℕ → ℕ → Real.Angle) (N K : ℕ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hhoriz : ∀ i≤N, ∀ k<K, |increment (F i k) (F i (k+1))|<Real.pi/4)
    (hvert : ∀ i<N, ∀ k≤K, |increment (F i k) (F (i+1) k)|<Real.pi/4)
    (hdiag : ∀ i<N, ∀ k<K, |increment (F i k) (F (i+1) (k+1))|<Real.pi/4) :
    ∑ k∈Finset.range K, increment (F N k) (F N (k+1))=0 := by
  have step : ∀ i<N,
      (∑ k∈Finset.range K, increment (F (i+1) k) (F (i+1) (k+1)))=
      ∑ k∈Finset.range K, increment (F i k) (F i (k+1)) := by
    intro i hi
    let v : ℕ → ℝ := fun k => increment (F i k) (F (i+1) k)
    have hver : ∑ k∈Finset.range K, (v (k+1)-v k)=0 := by
      rw [sum_successive_sub]
      dsimp [v]
      rw [hseam i (by omega),hseam (i+1) (by omega),sub_self]
    have heach : ∀ k∈Finset.range K,
        increment (F (i+1) k) (F (i+1) (k+1))=
        increment (F i k) (F i (k+1))+(v (k+1)-v k) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h := cell_balance (hhoriz i (by omega) k hk')
        (hvert i hi (k+1) (by omega)) (hdiag i hi k hk')
        (hvert i hi k (by omega)) (hhoriz (i+1) (by omega) k hk')
      dsimp [v]
      linarith
    rw [Finset.sum_congr rfl heach,Finset.sum_add_distrib,hver,add_zero]
  have all : ∀ i≤N, ∑ k∈Finset.range K, increment (F i k) (F i (k+1))=0 := by
    intro i
    induction i with
    | zero =>
      intro _
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcenter k (by have := Finset.mem_range.mp hk; omega),
        hcenter (k+1) (by have := Finset.mem_range.mp hk; omega)]
      simp [increment]
    | succ i ih =>
      intro hi
      rw [step i (by omega),ih (by omega)]
  exact all N le_rfl

lemma boundary_sum_lift (F : ℕ → Real.Angle) (b : ℕ → ℝ) (K : ℕ)
    (hlift : ∀ k≤K, F k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi) :
    ∑ k∈Finset.range K, increment (F k) (F (k+1))=b K-b 0 := by
  rw [←sum_successive_sub b K]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [increment,hlift k (by omega),hlift (k+1) (by omega),←Real.Angle.coe_sub]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨(abs_lt.mp (hstep k hk')).1,
    (abs_lt.mp (hstep k hk')).2.le⟩

theorem exists_large_edge (F : ℕ → ℕ → Real.Angle) (N K : ℕ) (b : ℕ → ℝ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hlift : ∀ k≤K, F N k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi)
    (hturn : b K-b 0=2*Real.pi) :
    (∃ i≤N, ∃ k<K, Real.pi/4≤|increment (F i k) (F i (k+1))|) ∨
    (∃ i<N, ∃ k≤K, Real.pi/4≤|increment (F i k) (F (i+1) k)|) ∨
    (∃ i<N, ∃ k<K, Real.pi/4≤|increment (F i k) (F (i+1) (k+1))|) := by
  by_contra hn
  push Not at hn
  have hz := boundary_sum_zero F N K hcenter hseam hn.1 hn.2.1 hn.2.2
  have ht := boundary_sum_lift (F N) b K hlift hstep
  rw [hz,hturn] at ht
  linarith [Real.pi_pos]

lemma boundary_mesh_lifts (φ e : ℕ → ℝ) (K : ℕ)
    (hmesh : ∀ k<K, |φ (k+1)-φ k|<Real.pi/32)
    (herr : ∀ k≤K, |e k|<Real.pi/8) :
    ∀ k<K, |(2*φ (k+1)+Real.pi+e (k+1))-(2*φ k+Real.pi+e k)|<Real.pi := by
  intro k hk
  obtain ⟨hma,hmb⟩ := abs_lt.mp (hmesh k hk)
  obtain ⟨hea,heb⟩ := abs_lt.mp (herr k (by omega))
  obtain ⟨hfa,hfb⟩ := abs_lt.mp (herr (k+1) (by omega))
  apply abs_lt.mpr
  constructor <;> linarith [Real.pi_pos]

end CriticalPercolation.DiskWinding
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_DensityModular
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
open scoped Classical

variable {E : Type*} [Fintype E]

lemma density_modular (w : E → Prop → ℝ) (x y : E → Prop) :
    density w x * density w y = density w (x ⊓ y) * density w (x ⊔ y) := by
  unfold density
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Pi.inf_apply, Pi.sup_apply]
  by_cases hx : x e <;> by_cases hy : y e <;> simp [hx, hy, mul_comm]

lemma expect_mul_ge (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : Monotone f) (hg : Monotone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω * g ω) := by
  have h := fkg f g (density w) (fun ω => density_nonneg hpos ω) hf0 hg0 hf hg
    (fun x y => le_of_eq (density_modular w x y))
  simpa only [expect, sum_density w hw, one_mul] using h

end CriticalPercolation.FiniteProduct

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

lemma monotone_indicator_upper (A : Set (Set E)) (hA : IsUpperSet A) :
    Monotone (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  intro ω ω' h
  change (if {e | ω e} ∈ A then (1 : ℝ) else 0) ≤
    (if {e | ω' e} ∈ A then (1 : ℝ) else 0)
  split_ifs with ha hb
  · rfl
  · exact (hb (hA h ha)).elim
  · norm_num
  · rfl

lemma real_eq_expect_indicator [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = FiniteProduct.expect (fun e => bitWeight (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← integral_law_eq_expect]
  exact (integral_indicator_one (.of_discrete)).symm

lemma finite_harris [Fintype E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  simp_rw [real_eq_expect_indicator]
  have he : (fun ω : E → Prop => (A ∩ B).indicator (1 : Set E → ℝ) {e | ω e}) =
      (fun ω => A.indicator (1 : Set E → ℝ) {e | ω e} *
        B.indicator (1 : Set E → ℝ) {e | ω e}) := by
    funext ω
    by_cases ha : {e | ω e} ∈ A <;> by_cases hb : {e | ω e} ∈ B <;> simp [ha, hb]
  rw [he]
  exact FiniteProduct.expect_mul_ge _ (fun e => bitWeight_sum (q e))
    (fun e b => bitWeight_nonneg (q e) b) _ _
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (monotone_indicator_upper A hA) (monotone_indicator_upper B hB)

lemma real_law_restrict_general (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law q).real {ω | s ∩ ω ∈ A} =
      (law (fun e : s => q e)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← law_map_restrict q s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]

lemma finite_restriction_harris (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real {ω | s ∩ ω ∈ A} * (law q).real {ω | s ∩ ω ∈ B} ≤
      (law q).real {ω | s ∩ ω ∈ A ∩ B} := by
  let := hs.fintype
  simp_rw [real_law_restrict_general _ s hs]
  exact finite_harris _ _ _ (fun _ _ h => hA (Set.image_mono h))
    (fun _ _ h => hB (Set.image_mono h))

lemma HasFiniteOpenWitness.inter {A B : Set (Set E)}
    (hA : HasFiniteOpenWitness A) (hB : HasFiniteOpenWitness B)
    (hAm : IsUpperSet A) (hBm : IsUpperSet B) : HasFiniteOpenWitness (A ∩ B) := by
  rintro ω ⟨hωA, hωB⟩
  obtain ⟨s, hs, hsω, hsA⟩ := hA ω hωA
  obtain ⟨t, ht, htω, htB⟩ := hB ω hωB
  exact ⟨s ∪ t, hs.union ht, Set.union_subset hsω htω,
    hAm Set.subset_union_left hsA, hBm Set.subset_union_right htB⟩

lemma tendsto_real_finiteWitness_general (q : E → unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law q).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law q).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law q)
    (finiteWitness_exhaustion_mono A hmono K)
  rw [finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

theorem harris_finiteWitness [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : HasFiniteOpenWitness A) (hwB : HasFiniteOpenWitness B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  exact le_of_tendsto_of_tendsto
    ((tendsto_real_finiteWitness_general q A hA hwA K).mul
      (tendsto_real_finiteWitness_general q B hB hwB K))
    (tendsto_real_finiteWitness_general q (A ∩ B) (hA.inter hB)
      (hwA.inter hwB hA hB) K)
    (Eventually.of_forall fun n => finite_restriction_harris q (K n) (K.finite n) A B hA hB)

end CriticalPercolation.BernoulliProduct
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FavoredFinite
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
variable {E I : Type*}

lemma upper_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, IsUpperSet (A i)) : IsUpperSet (⋃ i∈s, A i) := by
  intro ω τ h hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨i,hi,hA i hi h hω⟩

lemma finiteWitness_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, HasFiniteOpenWitness (A i)) :
    HasFiniteOpenWitness (⋃ i∈s, A i) := by
  intro ω hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKs,hKA⟩ := hA i hi ω hω
  exact ⟨K,hK,hKs,Set.mem_iUnion₂.mpr ⟨i,hi,hKA⟩⟩

theorem finite_miss_product [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, HasFiniteOpenWitness (A i)) :
    ∏ i∈s, (1-(law q).real (A i)) ≤ 1-(law q).real (⋃ i∈s, A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm := hA i (Finset.mem_insert_self i s)
    have hw' := hw i (Finset.mem_insert_self i s)
    have hs : ∀ j∈s, IsUpperSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hsw : ∀ j∈s, HasFiniteOpenWitness (A j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hind := ih hs hsw
    let B := ⋃ j∈s, A j
    have hBm := upper_biUnion A s hs
    have hBw := finiteWitness_biUnion A s hsw
    have hH := harris_finiteWitness q (A i) B hm hBm hw' hBw
    have hu := measureReal_union_add_inter (s := A i)
      (measurableSet_finiteWitness B hBm hBw) (μ := law q)
      (measure_ne_top _ _) (measure_ne_top _ _)
    have hb : (law q).real (A i)≤1 := measureReal_le_one
    have hp := mul_le_mul_of_nonneg_left hind (by linarith : 0≤1-(law q).real (A i))
    rw [Finset.prod_insert hi]
    rw [Finset.set_biUnion_insert]
    change (1-(law q).real (A i))*(∏ j∈s, (1-(law q).real (A j)))≤
      1-(law q).real (A i∪B)
    change _≤1-(law q).real B at hind
    change _≤(1-(law q).real (A i))*(1-(law q).real B) at hp
    nlinarith

theorem exists_favored_finite [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, HasFiniteOpenWitness (A i)) (a : ℝ) (ha : 0≤a)
    (hu : 1-a^s.card<(law q).real (⋃ i∈s, A i)) :
    ∃ i∈s, 1-a<(law q).real (A i) := by
  by_contra hn
  push Not at hn
  have hp : a^s.card≤∏ i∈s, (1-(law q).real (A i)) := by
    rw [←Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => ha)
    intro i hi
    linarith [hn i hi]
  have hH := finite_miss_product q A s hA hw
  linarith

end CriticalPercolation.BernoulliProduct
end
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

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_OpenRay
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
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma openWalk_getVert_ball {ω : Set E} {a b : V} (w : (G.openGraph ω).Walk a b) :
    ∀ n≤w.length, w.getVert n∈G.vertexBall a n := by
  intro n
  induction n with
  | zero => intro _; simpa using G.mem_vertexBall_self a 0
  | succ n ih =>
    intro hn
    exact G.vertexBall_step (ih (by omega))
      (G.openGraph_mono (Set.subset_univ _) (w.adj_getVert_succ (by omega)))

end CriticalPercolation.BondGraph
end
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

lemma boxMove_eq_restrictedSeed (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    G.boxMove t z m q B y s=G.restrictedSeed (G.vertexBall y m)
      {b | (|t b-(t y+1)|≤q ∧ |z b-(z y+s)|≤q) ∧ |t b-t y|≤B ∧ |z b-z y|≤B}
      (G.inducedEdges {x | |t x-t y|≤B ∧ |z x-z y|≤B}) := by
  ext ω
  constructor
  · rintro ⟨a,ha,b,w,hw,ht,hz⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,G.walk_reachable_induced _ ω w hw,⟨ht,hz⟩,hw b w.end_mem_support⟩
  · intro h
    obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp h
    let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
    refine ⟨a,ha,b,w',?_,hb.1.1,hb.1.2⟩
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact G.walk_induced_support w hb.2 x hx

lemma restrictedSeed_upper (A T : Set V) (S : Set E) : IsUpperSet (G.restrictedSeed A T S) := by
  intro ω τ h hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_left S h) hω

lemma restrictedSeed_finiteWitness (A T : Set V) (S : Set E) :
    BernoulliProduct.HasFiniteOpenWitness (G.restrictedSeed A T S) := by
  intro ω hω
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKsub,hKr⟩ := G.mem_cluster_finite_witness hr
  refine ⟨K,hK,fun _ he => (hKsub he).1,?_⟩
  change K∩S∈G.seedHitEvent A T
  rw [Set.inter_eq_left.mpr (fun _ he => (hKsub he).2)]
  exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hKr,hb⟩

lemma boxMove_upper (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    IsUpperSet (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_upper _ _ _

lemma boxMove_finiteWitness (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    BernoulliProduct.HasFiniteOpenWitness (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_finiteWitness _ _ _

lemma boxMove_measurable [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    MeasurableSet (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_measurable _ _ _

lemma lower_two_boxMoves [Countable E] (t z : V → ℝ) (m : ℕ) (q B : ℝ)
    (o : V) (pc : unitInterval) (hpc : 0<pc) (eta : ℝ)
    (hm : ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.boxMove t z m q B o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ b : Bool,
      1-eta<(BernoulliProduct.law (fun _ : E => p)).real
        (G.boxMove t z m q B o (Corridor.sign b)) :=
  BernoulliProduct.exists_lower_parameter _ (fun _ => G.boxMove_upper _ _ _ _ _ _ _)
    (fun _ => G.boxMove_finiteWitness _ _ _ _ _ _ _) pc hpc (fun _ => 1-eta) hm

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_MoveExit
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

namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}

lemma bounded_first_crossing (f : V → ℝ) (D T : ℝ) (hD : 0≤D)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y|≤D)
    {a b : V} (w : H.Walk a b) (ha : f a<T) (hb : T≤f b) :
    ∃ x, ∃ p : H.Walk a x, p.support⊆w.support ∧
      (∀ v∈p.support, f v≤T+D) ∧ T≤f x := by
  induction w with
  | nil => exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T≤f c
    · refine ⟨c,hac.toWalk,?_,?_,hc⟩
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · exact (_root_.SimpleGraph.Walk.cons hac w).start_mem_support
        · exact List.mem_cons_of_mem a w.start_mem_support
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · linarith
        · have hh := (abs_le.mp (hf hac)).1
          linarith
    · obtain ⟨x,p,hp,hpb,hpx⟩ := ih (lt_of_not_ge hc) hb
      refine ⟨x,_root_.SimpleGraph.Walk.cons hac p,?_,?_,hpx⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons.mpr (Or.inr (hp hv))
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · rw [hv]
          linarith
        · exact hpb v hv

end SimpleGraph.Walk
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseExit
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

namespace CriticalPercolation.EuclideanEllipse

lemma finite_circle_cover (zeta : ℝ) (hzeta : 0<zeta) :
    ∃ S : Finset Circle, ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta := by
  obtain ⟨S,_hS,hSf,hcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).finite_cover_balls hzeta
  refine ⟨hSf.toFinset,?_⟩
  intro c
  obtain ⟨d,hd,hcd⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ c))
  change dist (c : ℂ) (d : ℂ)<zeta at hcd
  exact ⟨d,hSf.mem_toFinset.mpr hd,by simpa only [dist_eq_norm] using hcd⟩

lemma exists_radial_circle (z : ℂ) (hz : z≠0) :
    ∃ c : Circle, z=‖z‖•(c : ℂ) := by
  let c : Circle := ⟨‖z‖⁻¹•z,by
    apply mem_sphere_zero_iff_norm.mpr
    exact norm_smul_inv_norm (𝕜 := ℝ) hz⟩
  refine ⟨c,?_⟩
  change z=‖z‖•(‖z‖⁻¹•z)
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]

lemma annulus_covered (S : Finset Circle) (zeta : ℝ)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (z : ℂ) (hlo : 1≤‖z‖) (hhi : ‖z‖≤1+zeta) :
    ∃ d∈S, ‖z-(d : ℂ)‖≤2*zeta := by
  have hz : z≠0 := by intro h; subst z; norm_num at hlo
  obtain ⟨c,hc⟩ := exists_radial_circle z hz
  obtain ⟨d,hd,hcd⟩ := hcover c
  have he : z-(c : ℂ)=(‖z‖-1)•(c : ℂ) := by rw [sub_smul,one_smul,←hc]
  have hdiff : ‖z-(c : ℂ)‖=‖z‖-1 := by
    rw [he,norm_smul,Real.norm_eq_abs,Circle.norm_coe,mul_one,abs_of_nonneg (by linarith)]
  refine ⟨d,hd,?_⟩
  have htri : ‖z-(d : ℂ)‖≤‖z-(c : ℂ)‖+‖(c : ℂ)-(d : ℂ)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z-(c : ℂ)) ((c : ℂ)-(d : ℂ))
  linarith

end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ellipseExit_iff (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) (ω : Set E) :
    ω∈G.ellipseExit Psi A zeta c ↔ ∃ a∈A, ∃ x, ∃ w : (G.openGraph ω).Walk a x,
      (∀ v∈w.support, ‖Psi v‖≤1+zeta) ∧ ‖Psi x-(c : ℂ)‖≤2*zeta := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1⟩
    intro v hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact G.walk_induced_support w hx.2 v hv
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.walk_reachable_induced _ ω w hw,hx,hw x w.end_mem_support⟩

lemma ellipseExit_upper (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    IsUpperSet (G.ellipseExit Psi A zeta c) := G.restrictedSeed_upper _ _ _
lemma ellipseExit_finiteWitness (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    BernoulliProduct.HasFiniteOpenWitness (G.ellipseExit Psi A zeta c) := G.restrictedSeed_finiteWitness _ _ _

lemma full_infinite_cluster_exit (Psi : V → ℂ) (ω : Set E) (a : V)
    (hi : (G.cluster ω a).Infinite)
    (hbound : (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) a).Finite) :
    ∃ b∈G.cluster ω a, 1<‖Psi b‖ := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbound.subset
  rintro b ⟨w⟩
  apply G.walk_reachable_induced _ ω w
  intro x hx
  exact hn x (w.takeUntil x hx).reachable

theorem infinite_cluster_ellipseExit (Psi : V → ℂ) (A : Set V) (zeta D : ℝ)
    (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster ω a).Infinite)
    (hbound : ∀ a∈A, (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) a).Finite) :
    ω∈⋃ c∈S, G.ellipseExit Psi A zeta c := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.full_infinite_cluster_exit Psi ω a hi (hbound a ha)
  have hstep : ∀ ⦃x y⦄, (G.openGraph ω).Adj x y → |‖Psi x‖-‖Psi y‖|≤D := by
    intro x y hxy
    exact (abs_norm_sub_norm_le _ _).trans (hPsi (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨x,p,_hp,hpb,hpx⟩ := _root_.OAI.SimpleGraph.Walk.bounded_first_crossing (fun x => ‖Psi x‖) D 1 hD hstep w (hseed a ha) hb.le
  obtain ⟨c,hc,hcx⟩ := EuclideanEllipse.annulus_covered S zeta hcover (Psi x) hpx (by linarith [hpb x p.end_mem_support])
  apply Set.mem_iUnion₂.mpr
  refine ⟨c,hc,(G.ellipseExit_iff Psi A zeta c ω).mpr ⟨a,ha,x,p,?_,hcx⟩⟩
  intro v hv
  linarith [hpb v hv]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseLinear
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open LinearMap

namespace CriticalPercolation.EllipseLinear

lemma center_left (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d a b=1 ∧ height a b c d a b=1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring

lemma center_right (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d c d=1 ∧ height a b c d c d= -1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring

lemma det_lower_of_separation (θ ψ : ℝ)
    (hsep : Real.pi/4≤|DiskWinding.increment ((2*θ : ℝ) : Real.Angle)
      ((2*ψ : ℝ) : Real.Angle)|) :
    (1 : ℝ)/4≤|det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)| := by
  let t : Real.Angle := ((2*ψ : ℝ) : Real.Angle)-((2*θ : ℝ) : Real.Angle)
  have ht : t=((2*(ψ-θ) : ℝ) : Real.Angle) := by
    dsimp [t]
    rw [←Real.Angle.coe_sub]
    congr 1
    ring
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0≤Real.pi/4) (Real.Angle.abs_toReal_le_pi t) hsep
  rw [Real.cos_abs,Real.Angle.cos_toReal,ht,Real.Angle.cos_coe,
    Real.cos_two_mul,Real.cos_pi_div_four] at hcos
  have hsqrt : Real.sqrt 2≤(7 : ℝ)/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg 2]
  have hsq := Real.sin_sq_add_cos_sq (ψ-θ)
  have hsin : (1 : ℝ)/4≤|Real.sin (ψ-θ)| := by
    nlinarith [sq_abs (Real.sin (ψ-θ)),abs_nonneg (Real.sin (ψ-θ))]
  have heq : det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)=
      Real.sin (ψ-θ) := by rw [Real.sin_sub]; unfold det; ring
  rwa [heq]

lemma row_bound {a b c d : ℝ} (ha : |a|≤1) (hb : |b|≤1)
    (hc : |c|≤1) (hd : |d|≤1) (hdet : (1 : ℝ)/4≤|det a b c d|)
    (x y q : ℝ) (hq : 0≤q) (hx : |x|≤q) (hy : |y|≤q) :
    |time a b c d x y|≤16*q ∧ |height a b c d x y|≤16*q := by
  have hpos : 0 < |det a b c d| := by linarith
  have hdb : |d-b|≤2 := (abs_sub d b).trans (by linarith)
  have hac : |a-c|≤2 := (abs_sub a c).trans (by linarith)
  have hdb' : |d+b|≤2 := (abs_add_le d b).trans (by linarith)
  have hca : |c+a|≤2 := (abs_add_le c a).trans (by linarith)
  have hprod : ∀ z w : ℝ, |z|≤2 → |w|≤q → |z*w|≤2*q := by
    intro z w hz hw
    rw [abs_mul]
    exact mul_le_mul hz hw (abs_nonneg _) (by norm_num)
  constructor
  · unfold time
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d-b)*x+(a-c)*y|≤|(d-b)*x|+|(a-c)*y| := abs_add_le _ _
      _ ≤4*q := by linarith [hprod (d-b) x hdb hx,hprod (a-c) y hac hy]
      _ ≤16*q*|det a b c d| := by nlinarith
  · unfold height
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d+b)*x-(c+a)*y|≤|(d+b)*x|+|(c+a)*y| := abs_sub _ _
      _ ≤4*q := by linarith [hprod (d+b) x hdb' hx,hprod (c+a) y hca hy]
      _ ≤16*q*|det a b c d| := by nlinarith

lemma time_sub (a b c d x y x' y' : ℝ) :
    time a b c d x y-time a b c d x' y'=time a b c d (x-x') (y-y') := by
  unfold time; ring
lemma height_sub (a b c d x y x' y' : ℝ) :
    height a b c d x y-height a b c d x' y'=height a b c d (x-x') (y-y') := by
  unfold height; ring

lemma source_budgets {eps : ℝ} (heps : 0<eps) (heps' : eps<1/10) :
    16*(4*(eps/1000))<eps/8 ∧
    16*((1+eps/1000)^2)<30 := by constructor <;> nlinarith

end CriticalPercolation.EllipseLinear
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_EllipseMoves
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

lemma circle_component_bounds (c : Circle) : |(c : ℂ).re|≤1 ∧ |(c : ℂ).im|≤1 := by
  constructor
  · exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe c)
  · exact (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe c)

lemma ellipse_coordinates_norm_bound (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (x : V) : |ellipseTime Psi c d x|≤16*‖Psi x‖ ∧ |ellipseHeight Psi c d x|≤16*‖Psi x‖ := by
  exact EllipseLinear.row_bound (circle_component_bounds c).1 (circle_component_bounds c).2
    (circle_component_bounds d).1 (circle_component_bounds d).2 hdet (Psi x).re (Psi x).im
    ‖Psi x‖ (norm_nonneg _) (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

lemma ellipse_coordinates_sub (Psi : V → ℂ) (c d : Circle) (x y : V) :
    ellipseTime Psi c d x-ellipseTime Psi c d y=
      ellipseTime (fun v => Psi v-Psi y) c d x ∧
    ellipseHeight Psi c d x-ellipseHeight Psi c d y=
      ellipseHeight (fun v => Psi v-Psi y) c d x := by
  constructor
  · exact EllipseLinear.time_sub _ _ _ _ _ _ _ _
  · exact EllipseLinear.height_sub _ _ _ _ _ _ _ _

lemma ellipse_coordinates_step (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (D : ℝ) (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |ellipseTime Psi c d x-ellipseTime Psi c d y|≤16*D) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y → |ellipseHeight Psi c d x-ellipseHeight Psi c d y|≤16*D) := by
  constructor
  · intro x y hxy
    rw [(ellipse_coordinates_sub Psi c d x y).1]
    exact (ellipse_coordinates_norm_bound (fun v => Psi v-Psi y) c d hdet x).1.trans (by nlinarith [hPsi hxy])
  · intro x y hxy
    rw [(ellipse_coordinates_sub Psi c d x y).2]
    exact (ellipse_coordinates_norm_bound (fun v => Psi v-Psi y) c d hdet x).2.trans (by nlinarith [hPsi hxy])

theorem ellipseExit_boxMove (Psi Psi' : V → ℂ) (o : V) (m : ℕ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (eps : ℝ) (heps : 0<eps) (heps' : eps<1/10) (ho : Psi o=0)
    (hpert : ∀ x, ‖Psi x-Psi' x‖≤(eps/1000)*‖Psi' x‖) (b : Bool) :
    G.ellipseExit Psi' (G.vertexBall o m) (eps/1000) (if b then c else d) ⊆
      G.boxMove (ellipseTime Psi c d) (ellipseHeight Psi c d) m (eps/8) 30 o (Corridor.sign b) := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.ellipseExit_iff _ _ _ _ ω).mp hω
  have hzeta : 0<eps/1000 := by positivity
  have hzeta' : eps/1000<1/10000 := by linarith
  have hdet' : EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im≠0 := by
    intro he
    rw [he,abs_zero] at hdet
    norm_num at hdet
  have hto : ellipseTime Psi c d o=0 := by simp [ellipseTime,ho,EllipseLinear.time]
  have hzo : ellipseHeight Psi c d o=0 := by simp [ellipseHeight,ho,EllipseLinear.height]
  have hpath : ∀ y∈w.support, ‖Psi y‖≤(1+eps/1000)^2 := by
    intro y hy
    have htri : ‖Psi y‖≤‖Psi y-Psi' y‖+‖Psi' y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Psi y-Psi' y) (Psi' y)
    nlinarith [hpert y,hw y hy]
  have hterminal : ‖Psi x-((if b then c else d) : Circle)‖≤4*(eps/1000) := by
    have htri : ‖Psi x-((if b then c else d) : Circle)‖≤
        ‖Psi x-Psi' x‖+‖Psi' x-((if b then c else d) : Circle)‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (Psi x-Psi' x)
        (Psi' x-((if b then c else d) : Circle))
    nlinarith [hpert x,hw x w.end_mem_support,mul_pos hzeta (by linarith : 0<1-eps/1000)]
  have hcenter : EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=1 ∧
      EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=Corridor.sign b := by
    cases b
    · exact EllipseLinear.center_right _ _ _ _ hdet'
    · exact EllipseLinear.center_left _ _ _ _ hdet'
  have hend := ellipse_coordinates_norm_bound (fun v => Psi v-((if b then c else d) : Circle)) c d hdet x
  have htend : |ellipseTime Psi c d x-1|≤eps/8 := by
    rw [←hcenter.1,ellipseTime,EllipseLinear.time_sub]
    exact hend.1.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  have hzend : |ellipseHeight Psi c d x-Corridor.sign b|≤eps/8 := by
    rw [←hcenter.2,ellipseHeight,EllipseLinear.height_sub]
    exact hend.2.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  refine ⟨a,ha,x,w,?_,?_,?_⟩
  · intro y hy
    rw [hto,hzo,sub_zero,sub_zero]
    have hnorm := ellipse_coordinates_norm_bound Psi c d hdet y
    have hbudget : 16*‖Psi y‖≤30 := (mul_le_mul_of_nonneg_left (hpath y hy) (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').2.le
    exact ⟨hnorm.1.trans hbudget,hnorm.2.trans hbudget⟩
  · simpa only [hto,zero_add] using htend
  · simpa only [hzo,zero_add] using hzend

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EuclideanEllipse
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

lemma diagonal_add (a b : ℝ) (z w : ℂ) :
    diagonal a b (z+w)=diagonal a b z+diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_add]
lemma diagonal_sub (a b : ℝ) (z w : ℂ) :
    diagonal a b (z-w)=diagonal a b z-diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_sub]
lemma diagonal_comp (a b c d : ℝ) (z : ℂ) :
    diagonal a b (diagonal c d z)=diagonal (a*c) (b*d) z := by
  apply Complex.ext <;> simp [diagonal,mul_assoc]
lemma diagonal_one (z : ℂ) : diagonal 1 1 z=z := by apply Complex.ext <;> simp [diagonal]
lemma diagonal_neg (a b : ℝ) (z : ℂ) : diagonal a b (-z)= -diagonal a b z := by
  apply Complex.ext <;> simp [diagonal]

lemma diagonal_norm_le (a b M : ℝ) (hM : 0≤M) (ha : |a|≤M) (hb : |b|≤M) (z : ℂ) :
    ‖diagonal a b z‖≤M*‖z‖ := by
  have ha2 : a^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr ha
  have hb2 : b^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hb
  have hsq : ‖diagonal a b z‖^2≤(M*‖z‖)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,mul_pow,Complex.sq_norm,Complex.normSq_apply]
    dsimp [diagonal]
    nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg z.re),
      mul_le_mul_of_nonneg_right hb2 (sq_nonneg z.im)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq

lemma normalize_sub (R W : ℝ) (c : Circle) (z w : ℂ) :
    normalize R W c (z-w)=normalize R W c z-normalize R W c w := by
  simp only [normalize,mul_sub,diagonal_sub]

lemma expand_normalize (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    expand R W c (normalize R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,mul_one_div_cancel hR,mul_one_div_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]

lemma normalize_expand (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    normalize R W c (expand R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,one_div_mul_cancel hR,one_div_mul_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]

lemma normalize_norm_le (R W : ℝ) (hW : 0<W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖normalize R W c z‖≤‖z‖/W := by
  have hR : 0<R := hW.trans_le hWR
  have h1 : |1/R|≤1/W := by rw [abs_of_pos (one_div_pos.mpr hR)]; exact one_div_le_one_div_of_le hW hWR
  have h2 : |1/W|≤1/W := (abs_of_pos (one_div_pos.mpr hW)).le
  have h := diagonal_norm_le (1/R) (1/W) (1/W) (by positivity) h1 h2 ((c : ℂ)⁻¹*z)
  simpa [normalize,norm_mul,Circle.norm_coe,div_eq_mul_inv,mul_comm]
    using h

lemma expand_norm_le (R W : ℝ) (hW : 0≤W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖expand R W c z‖≤R*‖z‖ := by
  have hR := hW.trans hWR
  have h := diagonal_norm_le R W R hR (by simp [abs_of_nonneg hR])
    (by simpa [abs_of_nonneg hW] using hWR) ((c : ℂ)⁻¹*z)
  simpa only [expand,norm_mul,Circle.norm_coe,norm_inv,inv_one,one_mul] using h

lemma normalize_center (W : ℝ) (c : Circle) (z : ℂ) :
    normalize W W c z=(1/W : ℝ)•z := by
  have he : ∀ w : ℂ, diagonal (1/W) (1/W) w=(1/W : ℝ)•w := by intro w; apply Complex.ext <;> simp [diagonal]
  rw [normalize,he,mul_smul_comm,←mul_assoc,mul_inv_cancel₀ c.coe_ne_zero,one_mul]

lemma normalize_neg (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W (-c) z=normalize R W c z := by
  simp only [normalize,Circle.coe_neg,inv_neg,neg_mul,diagonal_neg,mul_neg,neg_neg]

lemma normalize_components (R W : ℝ) (c : Circle) (z : ℂ) :
    (((c : ℂ)⁻¹*normalize R W c z).re=(1/R)*((c : ℂ)⁻¹*z).re) ∧
    (((c : ℂ)⁻¹*normalize R W c z).im=(1/W)*((c : ℂ)⁻¹*z).im) := by
  simp [normalize,diagonal]

lemma normalize_origin (R W : ℝ) (c : Circle) : normalize R W c 0=0 := by
  simp [normalize,diagonal,Complex.ext_iff]

lemma normalize_real_linear (R W : ℝ) (c : Circle) (z w : ℂ) (a b : ℝ) :
    normalize R W c (a•z+b•w)=a•normalize R W c z+b•normalize R W c w := by
  have hd : ∀ q : ℂ, ∀ t : ℝ, diagonal (1/R) (1/W) (t•q)=t•diagonal (1/R) (1/W) q := by
    intro q t
    apply Complex.ext <;> simp [diagonal,Complex.mul_re,Complex.mul_im] <;> ring
  simp only [normalize,mul_add,mul_smul_comm,diagonal_add,hd]

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripCompactness
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

lemma seedDomainTail_measurable [Countable V] [Countable E] (A S : Set V) (n : ℕ) :
    MeasurableSet (G.seedDomainTail A S n) := by
  have hm : Measurable (fun ω : Set E => ω∩G.inducedEdges S) :=
    (BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (G.measurableSet_clusterTail a n).preimage hm

lemma seedDomainTail_antitone (A S : Set V) : Antitone (G.seedDomainTail A S) := by
  intro n m hnm ω hω
  obtain ⟨a,ha,ht⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.clusterTail_antitone a hnm ht⟩

lemma seedDomainInfinite_eq_iInter (A S : Set V) (hA : A.Finite) :
    G.seedDomainInfinite A S=⋂ n, G.seedDomainTail A S n := by
  ext ω
  constructor
  · rintro ⟨a,ha,hi⟩
    exact Set.mem_iInter.mpr fun n => Set.mem_iUnion₂.mpr
      ⟨a,ha,G.infiniteEvent_subset_clusterTail a n hi⟩
  · intro hω
    by_contra hn
    have hf : ∀ a∈A, (G.cluster (ω∩G.inducedEdges S) a).Finite := by
      intro a ha
      by_contra hi
      exact hn ⟨a,ha,hi⟩
    let K := ⋃ a∈A, G.cluster (ω∩G.inducedEdges S) a
    have hK : K.Finite := hA.biUnion hf
    obtain ⟨a,ha,L,hL,hLa,hLn⟩ := Set.mem_iUnion₂.mp
      (Set.mem_iInter.mp hω (K.ncard+1))
    have hs : L⊆K := fun x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hLa hx⟩
    have hc := Set.ncard_le_ncard hs hK
    omega

lemma seedDomainInfinite_probability [Countable V] [Countable E]
    (μ : Measure (Set E)) [IsFiniteMeasure μ] (A S : Set V) (hA : A.Finite)
    (r : ℝ) (h : ∀ n, r≤μ.real (G.seedDomainTail A S n)) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (G.seedDomainTail_measurable A S n).nullMeasurableSet)
    (G.seedDomainTail_antitone A S) ⟨0,measure_ne_top _ _⟩
  rw [←G.seedDomainInfinite_eq_iInter A S hA] at ht
  exact ge_of_tendsto ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht)
    (Filter.Eventually.of_forall h)

lemma RayPrefix.reachable {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (i : Fin (n+1)) : (G.openGraph ω).Reachable a (p.vertex i) := by
  suffices hh : ∀ k, ∀ hk : k<n+1, (G.openGraph ω).Reachable a (p.vertex ⟨k,hk⟩) from
    hh i.val i.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have he : (⟨0,hk⟩ : Fin (n+1))=0 := by ext; simp
    rw [he,p.start]
  | succ k ih =>
    intro hk
    exact (ih (by omega)).trans (p.adjacent ⟨k,by omega⟩).reachable

lemma RayPrefix.clusterTail {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n) :
    ω∈G.clusterTail a (n+1) := by
  refine ⟨Set.range p.vertex,Set.finite_range _,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact p.reachable G i
  · rw [Set.ncard_range_of_injective p.injective,Nat.card_fin]

lemma exit_gives_prefix (A S K : Set V) (n : ℕ)
    (hK : ∀ a∈A, G.vertexBall a n⊆K) {ω : Set E}
    (hω : ω∈G.restrictedSeed A (S\K) (G.inducedEdges S)) :
    ∃ a∈A, ∃ p : G.RayPrefix ω a n, ∀ i, p.vertex i∈S∩K := by
  obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp hω
  let p := w.toPath
  let q := p.val.mapLe (G.openGraph_mono Set.inter_subset_left)
  have hlen : n<q.length := by
    by_contra hn
    have h := G.openWalk_getVert_ball q q.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hb.2 (hK a ha (G.vertexBall_mono a (by omega) h))
  let r : G.RayPrefix ω a n := {
    vertex := fun i => q.getVert i.val
    start := q.getVert_zero
    adjacent := fun i => q.adj_getVert_succ (by omega)
    injective := by
      intro i j hij
      apply Fin.ext
      have hpath : q.IsPath := p.property.mapLe _
      exact hpath.getVert_injOn (by change i.val≤q.length; omega)
        (by change j.val≤q.length; omega) hij
    ball := fun i => G.openWalk_getVert_ball q i.val (by omega) }
  refine ⟨a,ha,r,?_⟩
  intro i
  refine ⟨?_,hK a ha (G.vertexBall_mono a (by omega) (r.ball i))⟩
  have hs := G.walk_induced_support p.val hb.1 (p.val.getVert i.val)
    (p.val.getVert_mem_support i.val)
  simpa only [r,q,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,SimpleGraph.Hom.ofLE_apply] using hs

theorem local_domain_exit_compactness [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (A S : Set V) (hA : A.Finite) (Sj Tj : ℕ → Set V) (r : ℝ)
    (hlocal : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Sj j∩K⊆S)
    (hescape : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Disjoint (Tj j) K)
    (hprob : ∀ j, r≤μ.real (G.restrictedSeed A (Sj j∩Tj j) (G.inducedEdges (Sj j)))) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  apply G.seedDomainInfinite_probability μ A S hA r
  intro n
  let K := ⋃ a∈A, G.vertexBall a n
  have hK : K.Finite := hA.biUnion (fun a _ => G.vertexBall_finite hl a n)
  obtain ⟨j,hj,hj'⟩ := ((hlocal K hK).and (hescape K hK)).exists
  apply (hprob j).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hout : ω∈G.restrictedSeed A (Sj j\K) (G.inducedEdges (Sj j)) := by
    obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hr,hb.1,fun hk => Set.disjoint_left.mp hj' hb.2 hk⟩
  obtain ⟨a,ha,p,hp⟩ := G.exit_gives_prefix A (Sj j) K n
    (fun a ha x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hx⟩) hout
  have ht := (G.prefix_inside_domain p S (fun i => hj (hp i))).clusterTail G
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.clusterTail_antitone a (Nat.le_succ n) ht⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_MovingStrips
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

lemma unit_pair_bounds {a b : ℝ} (h : a^2+b^2=1) :
    -1≤a ∧ a≤1 ∧ -1≤b ∧ b≤1 := by
  have ha : a^2≤1 := by nlinarith [sq_nonneg b]
  have hb : b^2≤1 := by nlinarith [sq_nonneg a]
  constructor
  · nlinarith [sq_nonneg (a+1)]
  constructor
  · nlinarith [sq_nonneg (a-1)]
  constructor <;> nlinarith [sq_nonneg (b+1),sq_nonneg (b-1)]

theorem uniform_long_strip_exits [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (u v : V → ℝ) (A : Set V) (hA : A.Finite) (W r : ℝ)
    (hW : 0<W) (hr : 0 < r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 →
      μ (G.stripPercolates (normalCoordinate u v a b) (2*W))=0) :
    ∃ N : ℕ, ∀ L : ℝ, (N : ℝ)≤L → ∀ a b : ℝ, a^2+b^2=1 →
      μ.real (G.longStripExit u v A W L a b) < r := by
  by_contra hn
  push Not at hn
  choose L hL a b hab hprob using hn
  have hseq : ∀ n, (a n,b n)∈Set.Icc ((-1 : ℝ),(-1 : ℝ)) (1,1) := by
    intro n
    have h := unit_pair_bounds (hab n)
    exact ⟨⟨h.1,h.2.2.1⟩,h.2.1,h.2.2.2⟩
  obtain ⟨c,_hc,φ,hφ,hc⟩ := isCompact_Icc.tendsto_subseq hseq
  have ha : Tendsto (fun n => a (φ n)) atTop (𝓝 c.1) := (continuous_fst.tendsto c).comp hc
  have hb : Tendsto (fun n => b (φ n)) atTop (𝓝 c.2) := (continuous_snd.tendsto c).comp hc
  have hunit : c.1^2+c.2^2=1 := by
    apply tendsto_nhds_unique ((ha.pow 2).add (hb.pow 2))
    simpa only [hab] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hpar : ∀ x, Tendsto (fun n => parallelCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (parallelCoordinate u v c.1 c.2 x)) := fun x =>
    (ha.mul_const (u x)).add (hb.mul_const (v x))
  have hnorm : ∀ x, Tendsto (fun n => normalCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (normalCoordinate u v c.1 c.2 x)) := fun x =>
    (hb.neg.mul_const (u x)).add (ha.mul_const (v x))
  have hLtop : Tendsto (fun n => L (φ n)) atTop atTop :=
    tendsto_atTop_mono (fun n => hL (φ n))
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  let Sj := fun n => {x | |normalCoordinate u v (a (φ n)) (b (φ n)) x|≤W}
  let Tj := fun n => {x | L (φ n)≤|parallelCoordinate u v (a (φ n)) (b (φ n)) x|}
  let S := {x | |normalCoordinate u v c.1 c.2 x|≤2*W}
  have hlocal : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Sj n∩K⊆S := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |normalCoordinate u v (a (φ n)) (b (φ n)) x|≤W → x∈S := by
      apply hK.eventually_all.mpr
      intro x _hx
      by_cases hx : x∈S
      · exact Eventually.of_forall (fun _ _ => hx)
      · have hh : W < |normalCoordinate u v c.1 c.2 x| := by
          change ¬|normalCoordinate u v c.1 c.2 x|≤2*W at hx
          linarith
        filter_upwards [(hnorm x).abs.eventually (lt_mem_nhds hh)] with n hn
        exact fun hnx => False.elim (not_lt_of_ge hnx hn)
    exact he.mono fun n hn x hx => hn x hx.2 hx.1
  have hescape : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Disjoint (Tj n) K := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |parallelCoordinate u v (a (φ n)) (b (φ n)) x|<L (φ n) := by
      apply hK.eventually_all.mpr
      intro x _hx
      let M := |parallelCoordinate u v c.1 c.2 x|+1
      have hm : |parallelCoordinate u v c.1 c.2 x|<M := by dsimp [M]; linarith
      filter_upwards [(hpar x).abs.eventually (gt_mem_nhds hm),
        (tendsto_atTop.mp hLtop M)] with n hn hn'
      exact hn.trans_le hn'
    exact he.mono fun n hn => Set.disjoint_left.mpr (fun x hx hk =>
      not_lt_of_ge hx (hn x hk))
  have hmass := G.local_domain_exit_compactness hl μ A S hA Sj Tj r hlocal hescape
    (fun n => hprob (φ n))
  have hf : μ (G.seedDomainInfinite A S)=0 := measure_mono_null
    (fun ω hω => by obtain ⟨x,_hx,hx⟩ := hω; exact ⟨x,hx⟩) (hnull c.1 c.2 hunit)
  rw [measureReal_def,hf,ENNReal.toReal_zero] at hmass
  exact not_le_of_gt hr hmass

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseBoundary
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

namespace CriticalPercolation.EuclideanEllipse

lemma rotated_re (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=(c : ℂ).re*z.re+(c : ℂ).im*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_re]
lemma rotated_im (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).im= -(c : ℂ).im*z.re+(c : ℂ).re*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_im,add_comm]
lemma norm_rotated (c : Circle) (z : ℂ) : ‖(c : ℂ)⁻¹*z‖=‖z‖ := by
  rw [norm_mul,norm_inv,Circle.norm_coe,inv_one,one_mul]

lemma original_components (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=R*((c : ℂ)⁻¹*normalize R W c z).re ∧
    ((c : ℂ)⁻¹*z).im=W*((c : ℂ)⁻¹*normalize R W c z).im := by
  obtain ⟨hre,him⟩ := normalize_components R W c z
  rw [hre,him]
  constructor <;> field_simp

lemma normalize_transverse_le (R W zeta : ℝ) (hR : R≠0) (hW : 0<W)
    (c : Circle) (z : ℂ) (hz : ‖normalize R W c z‖≤1+zeta) :
    |((c : ℂ)⁻¹*z).im|≤W*(1+zeta) := by
  rw [(original_components R W hR hW.ne' c z).2,abs_mul,abs_of_pos hW]
  apply mul_le_mul_of_nonneg_left _ hW.le
  exact ((Complex.abs_im_le_norm _).trans_eq (norm_rotated c _)).trans hz

lemma normalized_far_major (R W zeta : ℝ) (hR : 0<R) (hW : W≠0)
    (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|)
    (z : ℂ) (hz : ‖normalize R W c z-(d : ℂ)‖≤2*zeta) :
    R/10≤|((c : ℂ)⁻¹*z).re| := by
  have hdiff : |((c : ℂ)⁻¹*normalize R W c z).re-((c : ℂ)⁻¹*(d : ℂ)).re|≤2*zeta := by
    calc
      _ = |((c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))).re| := by rw [mul_sub,Complex.sub_re]
      _ ≤ ‖(c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))‖ := Complex.abs_re_le_norm _
      _ = ‖normalize R W c z-(d : ℂ)‖ := norm_rotated c _
      _ ≤ 2*zeta := hz
  have ha := abs_sub_abs_le_abs_sub (((c : ℂ)⁻¹*(d : ℂ)).re)
    (((c : ℂ)⁻¹*normalize R W c z).re)
  rw [abs_sub_comm] at ha
  have hmajor : (1 : ℝ)/10≤|((c : ℂ)⁻¹*normalize R W c z).re| := by linarith
  rw [(original_components R W hR.ne' hW c z).1,abs_mul,abs_of_pos hR]
  nlinarith

lemma doubled_angle_le_sine (theta : ℝ) :
    |((2*theta : ℝ) : Real.Angle).toReal|≤Real.pi*|Real.sin theta| := by
  let t : Real.Angle := ((2*theta : ℝ) : Real.Angle)
  have ht : |t.toReal/2|≤Real.pi/2 := by rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; exact div_le_div_of_nonneg_right (Real.Angle.abs_toReal_le_pi t) (by norm_num)
  have heq : 2•((t.toReal/2 : ℝ) : Real.Angle)=2•((theta : ℝ) : Real.Angle) := by
    rw [Real.Angle.two_nsmul_coe_div_two,Real.Angle.coe_toReal]
    dsimp [t]
    rw [←Real.Angle.coe_nsmul]
    congr 1
    simp only [two_smul]
    ring
  have hs := Real.Angle.abs_sin_eq_of_two_nsmul_eq heq
  simp only [Real.Angle.sin_coe] at hs
  have hj := Real.mul_abs_le_abs_sin ht
  rw [hs,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hj
  have hp := Real.pi_pos
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  field_simp at hm
  dsimp [t] at hm
  nlinarith

end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ellipseExit_subset_longStrip (pi : V → ℂ) (A : Set V) (R W zeta : ℝ)
    (hR : 0<R) (hW : 0<W) (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|) :
    G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d ⊆
      G.longStripExit (fun x => (pi x).re) (fun x => (pi x).im) A
        (W*(1+zeta)) (R/10) (c : ℂ).re (c : ℂ).im := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.ellipseExit_iff _ A zeta d ω).mp hω
  have hpath : ∀ y∈w.support, |normalCoordinate (fun x => (pi x).re)
      (fun x => (pi x).im) (c : ℂ).re (c : ℂ).im y|≤W*(1+zeta) := by
    intro y hy
    change |-(c : ℂ).im*(pi y).re+(c : ℂ).re*(pi y).im|≤_
    rw [←EuclideanEllipse.rotated_im]
    exact EuclideanEllipse.normalize_transverse_le R W zeta hR.ne' hW c (pi y) (hw y hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,G.walk_reachable_induced _ ω w hpath,hpath x w.end_mem_support,?_⟩
  change R/10≤|(c : ℂ).re*(pi x).re+(c : ℂ).im*(pi x).im|
  rw [←EuclideanEllipse.rotated_re]
  exact EuclideanEllipse.normalized_far_major R W zeta hR hW.ne' hzeta c d hd (pi x) hx

theorem favored_boundary_major_small [Countable V] [Countable E]
    (hl : G.LocallyFinite) (mu : Measure (Set E)) [IsFiniteMeasure mu]
    (pi : V → ℂ) (A : Set V) (hA : A.Finite) (W zeta r : ℝ)
    (hW : 0<W) (hzeta : 0≤zeta) (hzeta' : zeta≤1/10000) (hr : 0 < r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      mu (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) :
    ∃ N : ℕ, ∀ R : ℝ, 0<R → 10*(N : ℝ)≤R → ∀ c d : Circle,
      r ≤ mu.real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) →
      |((c : ℂ)⁻¹*(d : ℂ)).re|<1/8 := by
  obtain ⟨N,hN⟩ := G.uniform_long_strip_exits hl mu (fun x => (pi x).re)
    (fun x => (pi x).im) A hA (W*(1+zeta)) r (by positivity) hr
    (fun a b hab => hnull a b hab _)
  refine ⟨N,?_⟩
  intro R hR hRN c d hprob
  by_contra hn
  have hunit : (c : ℂ).re^2+(c : ℂ).im^2=1 := by
    have h := Circle.normSq_coe c
    simpa [Complex.normSq_apply,pow_two] using h
  have hsmall := hN (R/10) (by linarith) (c : ℂ).re (c : ℂ).im hunit
  have hmono := ENNReal.toReal_mono (measure_ne_top mu _)
    (measure_mono (G.ellipseExit_subset_longStrip pi A R W zeta hR hW hzeta' c d (le_of_not_gt hn)))
  exact (not_lt_of_ge (hprob.trans hmono) hsmall).elim

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseMesh
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
open scoped Topology

namespace CriticalPercolation.EuclideanEllipse

lemma normalize_basis (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W c z=z.re•normalize R W c 1+z.im•normalize R W c Complex.I := by
  have hz : z=z.re•(1 : ℂ)+z.im•Complex.I := by
    apply Complex.ext <;> simp
  rw [hz,normalize_real_linear]
  simp

lemma basis_difference_bound (R W R' W' : ℝ) (c d : Circle) (q : ℝ) (hq : 0≤q)
    (h1 : ‖normalize R W c 1-normalize R' W' d 1‖≤q)
    (hI : ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖≤q) (z : ℂ) :
    ‖normalize R W c z-normalize R' W' d z‖≤2*q*‖z‖ := by
  have he : normalize R W c z-normalize R' W' d z=
      z.re•(normalize R W c 1-normalize R' W' d 1)+
      z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I) := by
    rw [normalize_basis R W c z,normalize_basis R' W' d z]
    simp only [smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖z.re•(normalize R W c 1-normalize R' W' d 1)‖+
      ‖z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I)‖ := norm_add_le _ _
    _ = |z.re| * ‖normalize R W c 1-normalize R' W' d 1‖+
      |z.im| * ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ |z.re| * q+|z.im| * q := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ ≤ 2*q*‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) hq,
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) hq]

lemma diskRadius_bounds (W U : ℝ) (hWU : W≤U) {p : ℝ×ℝ} (hp : p∈parameterDisk) :
    W≤diskRadius W U p ∧ diskRadius W U p≤U := by
  obtain ⟨⟨hs,_hφ⟩,hs',_hφ'⟩ := hp
  dsimp [diskRadius]
  constructor <;> nlinarith

lemma diskNormalize_continuousOn (W U : ℝ) (hW : 0<W) (hWU : W≤U) (z : ℂ) :
    ContinuousOn (fun p => diskNormalize W U p z) parameterDisk := by
  have hR : ∀ p∈parameterDisk, diskRadius W U p≠0 := fun p hp =>
    ne_of_gt (hW.trans_le (diskRadius_bounds W U hWU hp).1)
  have hc : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)) := by
    simp only [Circle.coe_exp]
    fun_prop
  have hcinv : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)⁻¹) :=
    hc.inv₀ (fun p => (Circle.exp p.2).coe_ne_zero)
  have hRd : ContinuousOn (fun p => 1/diskRadius W U p) parameterDisk := by
    apply continuousOn_const.div
    · unfold diskRadius
      fun_prop
    · exact hR
  unfold diskNormalize normalize diagonal
  apply hc.continuousOn.mul
  have hre := hRd.mul (Complex.continuous_re.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have him := (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => 1/W) parameterDisk).mul
    (Complex.continuous_im.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have hd := (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => Complex.I) parameterDisk))
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  apply Complex.ext <;> simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add,sub_zero]

theorem diskNormalize_uniform_comparison (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ delta : ℝ, 0<delta ∧ ∀ p∈parameterDisk, ∀ q∈parameterDisk,
      dist p q<delta → ∀ z : ℂ,
        ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖ := by
  let F : (ℝ×ℝ) → (ℂ × ℂ) := fun p => (diskNormalize W U p 1,diskNormalize W U p Complex.I)
  have hc : ContinuousOn F parameterDisk := (diskNormalize_continuousOn W U hW hWU 1).prodMk
    (diskNormalize_continuousOn W U hW hWU Complex.I)
  have hcompact : IsCompact parameterDisk := isCompact_Icc
  have hu := hcompact.uniformContinuousOn_of_continuous hc
  have hU : 0<U := hW.trans_le hWU
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (zeta/(2*U)) (by positivity)
  refine ⟨delta,hdelta,?_⟩
  intro p hp q hq hpq z
  have h := hclose p hp q hq hpq
  rw [Prod.dist_eq] at h
  have h1 : ‖diskNormalize W U p 1-diskNormalize W U q 1‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_left _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hI : ‖diskNormalize W U p Complex.I-diskNormalize W U q Complex.I‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_right _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hnorm := basis_difference_bound (diskRadius W U p) W (diskRadius W U q) W
    (Circle.exp p.2) (Circle.exp q.2) (zeta/(2*U)) (by positivity) h1 hI (diskExpand W U q z)
  have hqR := diskRadius_bounds W U hWU hq
  have hexpand : ‖diskExpand W U q z‖≤U*‖z‖ :=
    (expand_norm_le (diskRadius W U q) W hW.le hqR.1 (Circle.exp q.2) z).trans
      (mul_le_mul_of_nonneg_right hqR.2 (norm_nonneg _))
  have hcancel : diskNormalize W U q (diskExpand W U q z)=z :=
    normalize_expand _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ z
  change ‖diskNormalize W U p (diskExpand W U q z)-diskNormalize W U q (diskExpand W U q z)‖≤_ at hnorm
  rw [hcancel] at hnorm
  apply hnorm.trans
  have hmul := mul_le_mul_of_nonneg_left hexpand (by positivity : 0≤2*(zeta/(2*U)))
  convert hmul using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseAngles
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

namespace CriticalPercolation.EuclideanEllipse

lemma circle_arg_re (c : Circle) : Real.cos (c : ℂ).arg=(c : ℂ).re := by
  simpa only [Circle.norm_coe,div_one] using Complex.cos_arg c.coe_ne_zero

lemma circle_arg_im (c : Circle) : Real.sin (c : ℂ).arg=(c : ℂ).im := by
  simpa only [Circle.norm_coe,div_one] using Complex.sin_arg (c : ℂ)

lemma circle_exp_re (phi : ℝ) : (Circle.exp phi : ℂ).re=Real.cos phi := by
  simp only [Circle.coe_exp,Complex.exp_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]

lemma circle_exp_im (phi : ℝ) : (Circle.exp phi : ℂ).im=Real.sin phi := by
  simp only [Circle.coe_exp,Complex.exp_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]

lemma rotated_major_cos (phi : ℝ) (c : Circle) :
    ((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re=Real.cos ((c : ℂ).arg-phi) := by
  rw [rotated_re,circle_exp_re,circle_exp_im,Real.cos_sub,circle_arg_re,circle_arg_im]
  ring

lemma boundary_error_lt (phi : ℝ) (c : Circle)
    (hc : |((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re|<1/8) :
    |boundaryError phi c|<Real.pi/8 := by
  have he : lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)=
      ((2*((c : ℂ).arg-phi-Real.pi/2) : ℝ) : Real.Angle) := by
    rw [lineAngle,←Real.Angle.coe_sub]
    congr 1
    ring
  have hs : |Real.sin ((c : ℂ).arg-phi-Real.pi/2)|<1/8 := by
    rw [Real.sin_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_sub,abs_neg]
    rwa [rotated_major_cos] at hc
  have hh := doubled_angle_le_sine ((c : ℂ).arg-phi-Real.pi/2)
  rw [boundaryError,he]
  exact hh.trans_lt (by nlinarith [Real.pi_pos])

lemma boundary_lift (phi : ℝ) (c : Circle) :
    lineAngle c=((2*phi+Real.pi+boundaryError phi c : ℝ) : Real.Angle) := by
  simp only [Real.Angle.coe_add,boundaryError,Real.Angle.coe_toReal]
  abel

lemma boundary_error_seam (c : Circle) : boundaryError Real.pi c=boundaryError 0 c := by
  unfold boundaryError
  congr 1
  have he : ((2*Real.pi+Real.pi : ℝ) : Real.Angle)=((Real.pi : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,zero_add]
  simp [he]

lemma circle_exp_pi : Circle.exp Real.pi= -(Circle.exp 0) := by
  apply Subtype.ext
  apply Complex.ext
  · simp only [circle_exp_re,Circle.coe_neg,Complex.neg_re,Real.cos_pi,Real.cos_zero]
  · simp only [circle_exp_im,Circle.coe_neg,Complex.neg_im,Real.sin_pi,Real.sin_zero,neg_zero]

lemma diskNormalize_seam (W U s : ℝ) : diskNormalize W U (s,Real.pi)=diskNormalize W U (s,0) := by
  funext z
  change normalize _ W (Circle.exp Real.pi) z=normalize _ W (Circle.exp 0) z
  rw [circle_exp_pi,normalize_neg]
  rfl

lemma diskNormalize_center (W U phi : ℝ) : diskNormalize W U (0,phi)=diskNormalize W U (0,0) := by
  funext z
  simp only [diskNormalize,diskRadius,mul_zero,add_zero,normalize_center]

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseGrid
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

namespace CriticalPercolation.EuclideanEllipse

lemma gridPoint_mem {N K i k : ℕ} (hN : 0<N) (hK : 0<K) (hi : i≤N) (hk : k≤K) :
    gridPoint N K i k∈parameterDisk := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  have hir : (i : ℝ)≤N := Nat.cast_le.mpr hi
  have hkr : (k : ℝ)≤K := Nat.cast_le.mpr hk
  change (0≤(i : ℝ)/N ∧ 0≤(k : ℝ)*Real.pi/K) ∧ (i : ℝ)/N≤1 ∧ (k : ℝ)*Real.pi/K≤Real.pi
  exact ⟨⟨by positivity,by positivity⟩,(div_le_one hNr).mpr hir,
    (div_le_iff₀ hKr).mpr (by nlinarith [Real.pi_pos])⟩

lemma gridPoint_dist {N K : ℕ} (hN : 0<N) (hK : 0<K) (i k : ℕ) (a b : ℕ)
    (ha : a≤1) (hb : b≤1) :
    dist (gridPoint N K i k) (gridPoint N K (i+a) (k+b)) ≤ max (1/(N : ℝ)) (Real.pi/K) := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  rw [Prod.dist_eq]
  have hfirst : dist (gridPoint N K i k).1 (gridPoint N K (i+a) (k+b)).1≤1/(N : ℝ) := by
    change |(i : ℝ)/N-(i+a : ℕ)/N|≤_
    rw [Nat.cast_add]
    have he : (i : ℝ)/N-((i : ℝ)+a)/N= -(a : ℝ)/N := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg a),abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) hNr.le
  have hsecond : dist (gridPoint N K i k).2 (gridPoint N K (i+a) (k+b)).2≤Real.pi/K := by
    change |(k : ℝ)*Real.pi/K-(k+b : ℕ)*Real.pi/K|≤_
    rw [Nat.cast_add]
    have he : (k : ℝ)*Real.pi/K-((k : ℝ)+b)*Real.pi/K= -((b : ℝ)*Real.pi)/K := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤(b : ℝ)*Real.pi),abs_of_pos hKr]
    apply div_le_div_of_nonneg_right _ hKr.le
    have hb' : (b : ℝ)≤1 := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  exact max_le_max hfirst hsecond

lemma exists_grid_mesh (delta : ℝ) (hdelta : 0<delta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ max (1/(N : ℝ)) (Real.pi/K)<delta ∧ Real.pi/K<Real.pi/32 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/delta)
  obtain ⟨K,hK⟩ := exists_nat_gt (max (Real.pi/delta) 32)
  have hNr : 0<(N : ℝ) := lt_trans (by positivity) hN
  have hKr : 0<(K : ℝ) := lt_trans (by norm_num : (0 : ℝ)<32) ((le_max_right _ _).trans_lt hK)
  have hNm : 1/(N : ℝ)<delta := (div_lt_iff₀ hNr).mpr (by
    have := (div_lt_iff₀ hdelta).mp hN
    nlinarith)
  have hKm : Real.pi/(K : ℝ)<delta := (div_lt_iff₀ hKr).mpr (by
    have := (div_lt_iff₀ hdelta).mp ((le_max_left _ _).trans_lt hK)
    nlinarith)
  have hK32 : Real.pi/(K : ℝ)<Real.pi/32 := div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    ((le_max_right _ _).trans_lt hK)
  exact ⟨N,K,Nat.cast_pos.mp hNr,Nat.cast_pos.mp hKr,max_lt hNm hKm,hK32⟩

lemma gridPoint_angular_step (N K k : ℕ) (hK : 0<K) :
    |(gridPoint N K (0 : ℕ) (k+1)).2-(gridPoint N K 0 k).2|=Real.pi/K := by
  change |((k+1 : ℕ) : ℝ)*Real.pi/K-(k : ℝ)*Real.pi/K|=_
  rw [Nat.cast_add,Nat.cast_one]
  have he : ((k : ℝ)+1)*Real.pi/K-(k : ℝ)*Real.pi/K=Real.pi/K := by ring
  rw [he,abs_of_nonneg (by positivity)]

theorem exists_grid_comparison (W U zeta : ℝ) (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ Real.pi/K<Real.pi/32 ∧
      ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K → ∀ z : ℂ,
        ‖diskNormalize W U (gridPoint N K i k) (diskExpand W U (gridPoint N K (i+a) (k+b)) z)-z‖≤zeta*‖z‖ := by
  obtain ⟨delta,hd,hcomp⟩ := diskNormalize_uniform_comparison W U zeta hW hWU hzeta
  obtain ⟨N,K,hN,hK,hm,hangle⟩ := exists_grid_mesh delta hd
  refine ⟨N,K,hN,hK,hangle,?_⟩
  intro i hi k hk a ha b hb hia hkb z
  exact hcomp _ (gridPoint_mem hN hK hi hk) _ (gridPoint_mem hN hK hia hkb)
    ((gridPoint_dist hN hK i k a b ha hb).trans_lt hm) z

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseSeed
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

lemma seedInfiniteEvent_mono {A B : Set V} (hAB : A⊆B) :
    G.seedInfiniteEvent A⊆G.seedInfiniteEvent B := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi⟩

theorem exists_seed_infinite_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (o : V) (q : E → unitInterval)
    (hone : BernoulliProduct.law q G.percolates=1) (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, 1-eps<(BernoulliProduct.law q).real (G.seedInfiniteEvent (G.vertexBall o m)) := by
  let A : ℕ → Set (Set E) := fun n => G.seedInfiniteEvent (G.vertexBall o n)
  have hmono : Monotone A := fun _ _ h => G.seedInfiniteEvent_mono (G.vertexBall_mono o h)
  have heq : (⋃ n, A n)=G.percolates := by
    ext ω
    constructor
    · intro h
      obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨a,hi⟩
    · rintro ⟨a,hi⟩
      obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc o a)
      exact Set.mem_iUnion.mpr ⟨n,a,hn,hi⟩
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(BernoulliProduct.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  exact hnear.exists

theorem exists_favored_ellipse [Countable E]
    (Psi : V → ℂ) (A : Set V) (zeta D : ℝ) (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(BernoulliProduct.law q).real (G.seedInfiniteEvent A))
    (hbound : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x∈A,
      (G.cluster (ω∩G.inducedEdges {x | ‖Psi x‖≤1}) x).Finite) :
    ∃ c∈S, 1-a<(BernoulliProduct.law q).real (G.ellipseExit Psi A zeta c) := by
  have hsub : G.seedInfiniteEvent A ≤ᵐ[BernoulliProduct.law q] ⋃ c∈S, G.ellipseExit Psi A zeta c := by
    filter_upwards [hbound] with ω hω
    exact fun hi => G.infinite_cluster_ellipseExit Psi A zeta D hD hDz hPsi hseed S hcover hi hω
  have hprob := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact BernoulliProduct.exists_favored_finite q (fun c => G.ellipseExit Psi A zeta c) S
    (fun c _ => G.ellipseExit_upper Psi A zeta c) (fun c _ => G.ellipseExit_finiteWitness Psi A zeta c)
    a ha (hi.trans_le hprob)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseSeparation
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

namespace CriticalPercolation.EuclideanEllipse

theorem separated_neighboring_ellipses (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta)
    (chooseCenter : (ℂ → ℂ) → Circle)
    (hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (normalize U W (Circle.exp phi)) : ℂ)).re|<1/8) :
    ∃ p∈parameterDisk, ∃ q∈parameterDisk,
      (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
      (1 : ℝ)/4≤|EllipseLinear.det
        (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
        (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
  obtain ⟨N,K,hN,hK,hangle,hcomp⟩ := exists_grid_comparison W U zeta hW hWU hzeta
  have hNr : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hKr : (K : ℝ)≠0 := (Nat.cast_pos.mpr hK).ne'
  let phi : ℕ → ℝ := fun k => (k : ℝ)*Real.pi/K
  let centers : ℕ → ℕ → Circle := fun i k => chooseCenter (diskNormalize W U (gridPoint N K i k))
  let F : ℕ → ℕ → Real.Angle := fun i k => lineAngle (centers i k)
  have hp0 : phi 0=0 := by simp [phi]
  have hpK : phi K=Real.pi := by dsimp [phi]; field_simp
  have hn : ∀ k, diskNormalize W U (gridPoint N K N k)=normalize U W (Circle.exp (phi k)) := by
    intro k
    simp only [diskNormalize,gridPoint,div_self hNr,diskRadius,mul_one,add_sub_cancel,phi]
  have hc : ∀ k≤K, F 0 k=F 0 0 := by
    intro k _hk
    dsimp [F,centers,gridPoint]
    simp only [Nat.cast_zero,zero_div,zero_mul]
    rw [diskNormalize_center W U ((k : ℝ)*Real.pi/K)]
  have hs : ∀ i≤N, F i K=F i 0 := by
    intro i _hi
    have he : gridPoint N K i K=((i : ℝ)/N,Real.pi) := by
      simp only [gridPoint]
      congr 1
    have he0 : gridPoint N K i 0=((i : ℝ)/N,0) := by simp [gridPoint]
    dsimp [F,centers]
    rw [he,he0,diskNormalize_seam]
  let err : ℕ → ℝ := fun k => boundaryError (phi k) (centers N k)
  let b : ℕ → ℝ := fun k => 2*phi k+Real.pi+err k
  have herr : ∀ k≤K, |err k|<Real.pi/8 := by
    intro k _hk
    apply boundary_error_lt
    simpa only [centers,hn] using hboundary (phi k)
  have hlift : ∀ k≤K, F N k=(b k : Real.Angle) := by
    intro k _hk
    exact boundary_lift (phi k) (centers N k)
  have hmesh : ∀ k<K, |phi (k+1)-phi k|<Real.pi/32 := by
    intro k _hk
    have he := gridPoint_angular_step N K k hK
    exact he.trans_lt hangle
  have hstep := DiskWinding.boundary_mesh_lifts phi err K hmesh herr
  have hturn : b K-b 0=2*Real.pi := by
    have hcseam : centers N K=centers N 0 := by
      dsimp [centers]
      rw [hn,hn,hpK,hp0,circle_exp_pi]
      congr 1
      funext z
      exact normalize_neg U W (Circle.exp 0) z
    have heseam : err K=err 0 := by
      dsimp [err]
      rw [hpK,hp0,hcseam,boundary_error_seam]
    dsimp [b]
    rw [hpK,hp0,heseam]
    ring
  have hex := DiskWinding.exists_large_edge F N K b hc hs hlift hstep hturn
  have edge : ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K →
      Real.pi/4≤|DiskWinding.increment (F i k) (F (i+a) (k+b))| →
      ∃ p∈parameterDisk, ∃ q∈parameterDisk,
        (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
        (1 : ℝ)/4≤|EllipseLinear.det
          (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
          (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
    intro i hi k hk a ha b hb hia hkb hsep
    refine ⟨gridPoint N K i k,gridPoint_mem hN hK hi hk,
      gridPoint N K (i+a) (k+b),gridPoint_mem hN hK hia hkb,hcomp i hi k hk a ha b hb hia hkb,?_⟩
    have hd := EllipseLinear.det_lower_of_separation (centers i k : ℂ).arg (centers (i+a) (k+b) : ℂ).arg hsep
    simpa only [circle_arg_re,circle_arg_im] using hd
  rcases hex with ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩
  · exact edge i hi k (by omega) 0 (by omega) 1 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k hk 1 (by omega) 0 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k (by omega) 1 (by omega) 1 (by omega) (by omega) (by omega) hik

end CriticalPercolation.EuclideanEllipse
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripOrigin
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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

lemma exists_strip_scale (B K d : ℝ) (hd : 0<d) :
    ∃ U : ℝ, 0<U ∧ B<U ∧ K/U<d := by
  obtain ⟨U,hU⟩ := exists_gt (max 0 (max B (K/d)))
  have hU0 : 0<U := (le_max_left _ _).trans_lt hU
  have hBU : B<U := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hU
  have hKU : K/d<U := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hU
  exact ⟨U,hU0,hBU,(div_lt_iff₀ hU0).mpr (by nlinarith [(div_lt_iff₀ hd).mp hKU])⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_EllipseProbability
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

lemma normalized_edge_bound (pi : V → ℂ) (R W D : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D) :
    ∀ ⦃x y⦄, G.fullGraph.Adj x y →
      ‖EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y)‖≤D/W := by
  intro x y hxy
  rw [←EuclideanEllipse.normalize_sub]
  exact (EuclideanEllipse.normalize_norm_le R W hW hWR c _).trans
    (div_le_div_of_nonneg_right (hpi hxy) hW.le)

lemma normalized_clusters_finite (pi : V → ℂ) (R W : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (mu : Measure (Set E))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) a).Finite) :
    ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) a).Finite := by
  have hR : 0<R := hW.trans_le hWR
  have hsub : {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}⊆
      {x | |(pi x).re|≤R ∧ |(pi x).im|≤R} := by
    intro x hx
    change ‖EuclideanEllipse.normalize R W c (pi x)‖≤1 at hx
    have hn : ‖pi x‖≤R := by
      calc
        _ = ‖EuclideanEllipse.expand R W c (EuclideanEllipse.normalize R W c (pi x))‖ := by
          rw [EuclideanEllipse.expand_normalize R W hR.ne' hW.ne']
        _ ≤ R*‖EuclideanEllipse.normalize R W c (pi x)‖ := EuclideanEllipse.expand_norm_le R W hW.le hWR c _
        _ ≤ R := by nlinarith
    exact ⟨(Complex.abs_re_le_norm _).trans hn,(Complex.abs_im_le_norm _).trans hn⟩
  filter_upwards [hbox R R] with ω hω a
  exact (hω a).subset (G.cluster_mono (Set.inter_subset_inter_right _ (G.inducedEdges_mono hsub)) a)

theorem all_ellipses_favored [Countable E]
    (pi : V → ℂ) (A : Set V) (W B D zeta : ℝ) (hD : 0≤D) (hW : 0<W)
    (hBW : B<W) (hDz : D/W≤zeta)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hA : ∀ a∈A, ‖pi a‖≤B) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(BernoulliProduct.law q).real (G.seedInfiniteEvent A))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite) :
    ∀ R : ℝ, W≤R → ∀ c : Circle, ∃ d∈S,
      1-a<(BernoulliProduct.law q).real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) := by
  intro R hWR c
  have hseed : ∀ x∈A, ‖EuclideanEllipse.normalize R W c (pi x)‖<1 := by
    intro x hx
    exact (EuclideanEllipse.normalize_norm_le R W hW hWR c (pi x)).trans_lt
      ((div_lt_one hW).mpr ((hA x hx).trans_lt hBW))
  have hbound : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ x∈A,
      (G.cluster (ω∩G.inducedEdges {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) x).Finite := by
    filter_upwards [G.normalized_clusters_finite pi R W hW hWR c (BernoulliProduct.law q) hbox] with ω hω x _hx
    exact hω x
  exact G.exists_favored_ellipse _ A zeta (D/W) (by positivity) hDz
    (G.normalized_edge_bound pi R W D hW hWR c hpi) hseed S hcover q a ha hi hbound

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseOrigin
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

theorem ellipse_origin_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hone : BernoulliProduct.law (fun _ : E => pc) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => pc)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ R W : ℝ, ∃ c d e : Circle,
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y| ≤ rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y| ≤ rho) ∧
      ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
        (G.boxMove (ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e)
          (ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e) m (eps/8) 30 o (Corridor.sign b)) := by
  let zeta := eps/1000
  have hzeta : 0<zeta := by dsimp [zeta]; positivity
  have hzeta' : zeta≤1/10000 := by dsimp [zeta]; linarith
  let a := min (eta/2) (1/2)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have haeta : a<eta := (min_le_left _ _).trans_lt (by linarith)
  have haone : a<1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨S,hS⟩ := EuclideanEllipse.finite_circle_cover zeta hzeta
  obtain ⟨m,hm⟩ := G.exists_seed_infinite_probability hc o (fun _ : E => pc) hone (a^S.card) (pow_pos ha _)
  have hAfin := G.vertexBall_finite hl o m
  obtain ⟨B,hB⟩ := (hAfin.image (fun x => ‖pi x‖)).bddAbove
  have hAB : ∀ x∈G.vertexBall o m, ‖pi x‖≤B := fun x hx => hB ⟨x,hx,rfl⟩
  refine ⟨m,?_⟩
  intro rho hrho
  obtain ⟨W,hW,hBW,hmesh⟩ := exists_strip_scale B D (min zeta (rho/16)) (lt_min hzeta (by positivity))
  have hDz : D/W≤zeta := hmesh.le.trans (min_le_left _ _)
  have hDrho : 16*(D/W) ≤ rho := by have := hmesh.trans_le (min_le_right _ _); linarith
  have hfav := G.all_ellipses_favored pi (G.vertexBall o m) W B D zeta hD hW hBW hDz hpi hAB
    S hS (fun _ : E => pc) a ha.le hm hbox
  let chooseCenter : (ℂ → ℂ) → Circle := fun f => Classical.epsilon
    (fun c => c∈S ∧ 1-a<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.ellipseExit (f ∘ pi) (G.vertexBall o m) zeta c))
  have hselect : ∀ R : ℝ, W≤R → ∀ c : Circle,
      1-a<(BernoulliProduct.law (fun _ : E => pc)).real
        (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) (G.vertexBall o m) zeta
          (chooseCenter (EuclideanEllipse.normalize R W c))) := by
    intro R hWR c
    exact (Classical.epsilon_spec (hfav R hWR c)).2
  obtain ⟨N,hN⟩ := G.favored_boundary_major_small hl (BernoulliProduct.law (fun _ : E => pc))
    pi (G.vertexBall o m) hAfin W zeta (1-a) hW hzeta.le hzeta' (by linarith) hnull
  let U := max W (10*(N : ℝ))
  have hWU : W≤U := le_max_left _ _
  have hU : 0<U := hW.trans_le hWU
  have hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (EuclideanEllipse.normalize U W (Circle.exp phi)) : ℂ)).re|<1/8 := by
    intro phi
    exact hN U hU (le_max_right _ _) _ _ (hselect U hWU _).le
  obtain ⟨p,hp,q,hq,hcomp,hdet⟩ := EuclideanEllipse.separated_neighboring_ellipses W U zeta hW hWU hzeta chooseCenter hboundary
  have hpR := EuclideanEllipse.diskRadius_bounds W U hWU hp
  have hqR := EuclideanEllipse.diskRadius_bounds W U hWU hq
  let R := EuclideanEllipse.diskRadius W U p
  let c := Circle.exp p.2
  let Psi := EuclideanEllipse.diskNormalize W U p ∘ pi
  let Psi' := EuclideanEllipse.diskNormalize W U q ∘ pi
  let d := chooseCenter (EuclideanEllipse.diskNormalize W U p)
  let e := chooseCenter (EuclideanEllipse.diskNormalize W U q)
  have hstep := G.ellipse_coordinates_step Psi d e hdet (D/W)
    (G.normalized_edge_bound pi R W D hW hpR.1 c hpi)
  have hpert : ∀ x, ‖Psi x-Psi' x‖≤zeta*‖Psi' x‖ := by
    intro x
    have hh := hcomp (Psi' x)
    have he : EuclideanEllipse.diskExpand W U q (Psi' x)=pi x :=
      EuclideanEllipse.expand_normalize _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ (pi x)
    rwa [he] at hh
  have hPsi0 : Psi o=0 := by
    change EuclideanEllipse.normalize R W c (pi o)=0
    rw [hpo,EuclideanEllipse.normalize_origin]
  refine ⟨R,W,c,d,e,(fun {_ _} h => (hstep.1 h).trans hDrho),
    (fun {_ _} h => (hstep.2 h).trans hDrho),?_⟩
  intro b
  cases b
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U q) hqR.1 (Circle.exp q.2)
    have hmono := ENNReal.toReal_mono (measure_ne_top (BernoulliProduct.law (fun _ : E => pc)) _)
      (measure_mono (G.ellipseExit_boxMove Psi Psi' o m d e hdet eps heps heps' hPsi0 hpert false))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U p) hpR.1 (Circle.exp p.2)
    have hsame : ∀ x, ‖Psi x-Psi x‖≤(eps/1000)*‖Psi x‖ := by intro x; simp only [sub_self,norm_zero]; positivity
    have hmono := ENNReal.toReal_mono (measure_ne_top (BernoulliProduct.law (fun _ : E => pc)) _)
      (measure_mono (G.ellipseExit_boxMove Psi Psi o m d e hdet eps heps heps' hPsi0 hsame true))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_MoveTransport
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

lemma boxMove_aut_subset (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    G.boxMove t z m q B o s ⊆ (fun ω => φ.edge '' ω) ⁻¹'
      G.boxMove t z m q B (φ.vertex o) s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  let w' := w.map (Aut.openGraphIso G φ ω).toHom
  refine ⟨φ.vertex a,(Aut.vertexBall_mem G φ o a m).mpr ha,φ.vertex b,w',?_,?_,?_⟩
  · intro x hx
    change x∈(w.map (Aut.openGraphIso G φ ω).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    change |t (φ.vertex v)-t (φ.vertex o)|≤B ∧ |z (φ.vertex v)-z (φ.vertex o)|≤B
    rw [ht,hz]
    exact hw v hv
  · have h : t (φ.vertex b)-(t (φ.vertex o)+1)=t b-(t o+1) := by linarith [ht b o]
    rwa [h]
  · have h : z (φ.vertex b)-(z (φ.vertex o)+s)=z b-(z o+s) := by linarith [hz b o]
    rwa [h]

lemma boxMove_aut_probability [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ) (p : unitInterval)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    (G.law p).real (G.boxMove t z m q B o s) ≤
      (G.law p).real (G.boxMove t z m q B (φ.vertex o) s) := by
  have hm : G.law p (G.boxMove t z m q B o s) ≤
      G.law p (G.boxMove t z m q B (φ.vertex o) s) := by
    conv_rhs => rw [← G.law_map_aut p φ]
    rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
      (G.boxMove_measurable _ _ _ _ _ _ _)]
    exact measure_mono (G.boxMove_aut_subset t z m q B o s φ ht hz)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hm

lemma boxMove_close_center (t z : V → ℝ) (m c : ℕ) (e s : ℝ) (he : e<1/10)
    {x y : V} (hxy : x∈G.vertexBall y c)
    (ht : |t x-t y|≤e/8) (hz : |z x-z y|≤e/8) :
    G.boxMove t z m (e/8) 30 x s ⊆ G.coordinateMove t z (m+c) e y s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  refine ⟨a,?_,b,w,?_,?_,?_⟩
  · simpa only [Nat.add_comm c m] using G.vertexBall_add hxy m ha
  · intro v hv
    have hvb := hw v hv
    constructor
    · have := abs_sub_le (t v) (t x) (t y)
      linarith [hvb.1]
    · have := abs_sub_le (z v) (z x) (z y)
      linarith [hvb.2]
  · have hh := abs_sub_le (t b) (t x+1) (t y+1)
    rw [add_sub_add_right_eq_sub] at hh
    linarith
  · have hh := abs_sub_le (z b) (z x+s) (z y+s)
    rw [add_sub_add_right_eq_sub] at hh
    linarith

theorem uniform_moves_of_origin [Countable V] [Countable E]
    (t z : V → ℝ) (o : V) (m c : ℕ) (e eta rho : ℝ)
    (he : e<1/10) (hrho : 0 ≤ rho) (hmesh : c*rho≤e/8)
    (ht : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y| ≤ rho)
    (hz : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y| ≤ rho)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y) ∧
      (∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y))
    (pc : unitInterval) (hpc : 0<pc)
    (horigin : ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.boxMove t z m (e/8) 30 o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ y s, |s|=1 →
      1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z (m+c) e y s) := by
  obtain ⟨p,hpl,hpu,hp⟩ := G.lower_two_boxMoves t z m (e/8) 30 o pc hpc eta horigin
  refine ⟨p,hpl,hpu,?_⟩
  intro y s hs
  obtain ⟨b,hb⟩ : ∃ b : Bool, Corridor.sign b=s := by
    rcases (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hs with h|h
    · exact ⟨true,by simpa [Corridor.sign] using h.symm⟩
    · exact ⟨false,by simpa [Corridor.sign] using h.symm⟩
  obtain ⟨φ,hφ,hφt,hφz⟩ := hdense y
  have htt := (G.coordinate_ball_bound t rho hrho ht hφ).trans hmesh
  have hzz := (G.coordinate_ball_bound z rho hrho hz hφ).trans hmesh
  have hsub := G.boxMove_close_center t z m c e s he hφ htt hzz
  have hm : (G.law p).real (G.boxMove t z m (e/8) 30 (φ.vertex o) s)≤
      (G.law p).real (G.coordinateMove t z (m+c) e y s) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hp' := hp b
  rw [hb] at hp'
  have hp'' : 1-eta≤(G.law p).real (G.boxMove t z m (e/8) 30 o s) := by
    simpa only [law,BernoulliProduct.law_const] using hp'.le
  simpa only [law,BernoulliProduct.law_const] using
    hp''.trans ((G.boxMove_aut_probability t z m (e/8) 30 o s p φ hφt hφz).trans hm)

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EllipseUniform
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

lemma ellipse_aut_differences (pi : V → ℂ) (R W : ℝ) (c d e : Circle) (phi : G.Aut)
    (hphi : ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y) :
    (∀ x y, ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y) ∧
    (∀ x y, ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y) := by
  have hPsi : ∀ x y,
      EuclideanEllipse.normalize R W c (pi (phi.vertex x))-EuclideanEllipse.normalize R W c (pi (phi.vertex y))=
      EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y) := by
    intro x y
    rw [←EuclideanEllipse.normalize_sub,←EuclideanEllipse.normalize_sub,hphi]
  constructor
  · intro x y
    rw [(ellipse_coordinates_sub _ d e (phi.vertex x) (phi.vertex y)).1,
      (ellipse_coordinates_sub _ d e x y).1]
    exact congrArg (fun z : ℂ => EllipseLinear.time (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)
  · intro x y
    rw [(ellipse_coordinates_sub _ d e (phi.vertex x) (phi.vertex y)).2,
      (ellipse_coordinates_sub _ d e x y).2]
    exact congrArg (fun z : ℂ => EllipseLinear.height (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)

theorem ellipse_uniform_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : BernoulliProduct.law (fun _ : E => pc) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => pc)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y| ≤ rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y| ≤ rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.ellipse_origin_moves hc hl pi o D pc hD hpo hpi hone hbox hnull eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hr : 0 < r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r ≤ rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨R,W,a,b,d,ht,hz,hmoves⟩ := hm r hr
  let t := ellipseTime (EuclideanEllipse.normalize R W a ∘ pi) b d
  let z := ellipseHeight (EuclideanEllipse.normalize R W a ∘ pi) b d
  have htdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      (∀ x y, t (phi.vertex x)-t (phi.vertex y)=t x-t y) ∧
      (∀ x y, z (phi.vertex x)-z (phi.vertex y)=z x-z y) := by
    intro y
    obtain ⟨phi,hphi,hphiP⟩ := hdense y
    exact ⟨phi,hphi,G.ellipse_aut_differences pi R W a b d phi hphiP⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.uniform_moves_of_origin t z o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨t,z,p,hpl,hpu,fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩

theorem ellipse_critical_contradiction_bs_oai [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.fullGraph.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.vertexBall y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : BernoulliProduct.law (fun _ : E => G.criticalProbability) G.percolates=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ x,
      (G.cluster (ω∩G.inducedEdges {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      BernoulliProduct.law (fun _ : E => G.criticalProbability)
        (G.stripPercolates (normalCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) : False := by
  apply G.approximate_moves_contradiction_bs hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.ellipse_uniform_moves hc hl pi o c D G.criticalProbability hD hpc hpo hpi hdense hone hbox hnull eps eta he he' heta

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.ellipse_critical_contradiction_bs_oai.{u_1, u_2}
