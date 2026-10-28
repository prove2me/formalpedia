-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.critical_strip_null_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:47:11.933878+00:00
-- url     : https://prove2.me/submissions/d19605f6-f312-4851-a193-8fe830a92957

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_unique_cluster_direction_unbounded_ae_bs

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

theorem percolates_mono {ω ω' : Set E} (h : ω ⊆ ω')
    (hω : ω ∈ G.percolates) : ω' ∈ G.percolates := by
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, hv.mono (G.cluster_mono h v)⟩

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

theorem percolates_null_iff [Countable V] (μ : Measure (Set E)) :
    μ G.percolates = 0 ↔ ∀ v, μ {ω | (G.cluster ω v).Infinite} = 0 := by
  have heq : G.percolates = ⋃ v, {ω | (G.cluster ω v).Infinite} := by
    ext ω
    simp [percolates]
  rw [heq, measure_iUnion_null_iff]

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

lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S

theorem zero_one_of_finite_erasure_invariant (q : E → unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinvariant : ∀ (S : Set E), S.Finite → ∀ ω,
      forceOn S ∅ ω ∈ A ↔ ω ∈ A) : law q A = 0 ∨ law q A = 1 := by
  let mA : MeasurableSpace (Set E) := MeasurableSpace.generateFrom {A}
  have hmA : mA ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) := MeasurableSpace.generateFrom_singleton_le hA
  have hi : ∀ S : Finset E, Indep (blockSigma (S : Set E)) mA (law q) := by
    intro S
    have htail : MeasurableSet[blockSigma (S : Set E)ᶜ] A := by
      have hh := hA.preimage (measurable_forceOn_block (S : Set E) ∅)
      have heq : forceOn (S : Set E) ∅ ⁻¹' A = A := by
        ext ω
        exact hinvariant _ S.finite_toSet ω
      rwa [heq] at hh
    exact indep_of_indep_of_le_right (independent_blocks q (S : Set E))
      (MeasurableSpace.generateFrom_singleton_le htail)
  have hd : Directed (· ≤ ·) (fun S : Finset E => blockSigma (S : Set E)) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩ <;> apply iSup₂_le <;> intro e he
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_left T he) le_rfl)
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_right S he) le_rfl)
  have hall : (⨆ S : Finset E, blockSigma (S : Set E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
    apply le_antisymm (iSup_le fun S => blockSigma_le _)
    change (⨆ e, coordinateSigma e) ≤ _
    apply iSup_le
    intro e
    exact le_iSup_of_le {e} (le_iSup_of_le e
      (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl))
  have h := indep_iSup_of_directed_le hi (fun S => blockSigma_le (S : Set E)) hmA hd
  rw [hall] at h
  exact measure_eq_zero_or_one_of_indepSet_self
    (h.indepSet_of_measurableSet hA (MeasurableSpace.measurableSet_generateFrom (by simp)))

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_PercolationTail
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
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_union_subset (ω S : Set E) (o : V) :
    G.cluster (ω ∪ S) o ⊆ G.cluster ω o ∪
      ⋃ e ∈ S, ⋃ v ∈ (G.ends e).toFinset, G.cluster ω v := by
  intro z hz
  have hr := ((G.openGraph (ω ∪ S)).reachable_iff_reflTransGen o z).mp hz
  clear hz
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @tail x y hr hxy ih =>
    obtain ⟨⟨e, he, heq⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    rcases he with he | he
    · have hadj : (G.openGraph ω).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩
      rcases ih with ho | h
      · exact Or.inl (ho.trans hadj.reachable)
      · obtain ⟨f,hf,h⟩ := Set.mem_iUnion₂.mp h
        obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,Set.mem_iUnion₂.mpr
          ⟨v,hv,hh.trans hadj.reachable⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr
        ⟨y,by simp [heq], .refl _⟩⟩)

lemma percolates_union_finite_iff (ω S : Set E) (hS : S.Finite) :
    ω ∪ S ∈ G.percolates ↔ ω ∈ G.percolates := by
  constructor
  · rintro ⟨o,ho⟩
    by_contra hω
    have hfinite : ∀ v, (G.cluster ω v).Finite :=
      fun v => Set.not_infinite.mp (fun hv => hω ⟨v,hv⟩)
    exact ho (((hfinite o).union (hS.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hfinite v)).subset
        (G.cluster_union_subset ω S o))
  · exact G.percolates_mono Set.subset_union_left

lemma percolates_diff_finite_iff (ω S : Set E) (hS : S.Finite) :
    ω \ S ∈ G.percolates ↔ ω ∈ G.percolates := by
  constructor
  · exact G.percolates_mono Set.sdiff_subset
  · intro hω
    have hh := G.percolates_mono (show ω ⊆ (ω \ S) ∪ S from
      fun e he => by by_cases hs : e ∈ S; exact Or.inr hs; exact Or.inl ⟨he,hs⟩) hω
    exact (G.percolates_union_finite_iff (ω \ S) S hS).mp hh

end CriticalPercolation.BondGraph
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

lemma rayPrefix_nonempty (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) (n : ℕ) : Nonempty (G.RayPrefix ω o n) := by
  have hn : ¬G.cluster ω o⊆G.vertexBall o n := fun h => hi ((G.vertexBall_finite hl o n).subset h)
  obtain ⟨b,hb,hbn⟩ := Set.not_subset.mp hn
  obtain ⟨w⟩ := hb
  let p := w.toPath
  have hlen : n<p.val.length := by
    by_contra hn
    have h := G.openWalk_getVert_ball p.val p.val.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hbn (G.vertexBall_mono o (by omega) h)
  refine ⟨{ vertex := fun i => p.val.getVert i.val
            start := p.val.getVert_zero
            adjacent := ?_
            injective := ?_
            ball := ?_ }⟩
  · intro i
    exact p.val.adj_getVert_succ (by omega)
  · intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn (by change i.val≤p.val.length; omega)
      (by change j.val≤p.val.length; omega) hij
  · intro i
    exact G.openWalk_getVert_ball p.val i.val (by omega)

lemma rayPrefix_finite (hl : G.LocallyFinite) (ω : Set E) (o : V) (n : ℕ) :
    Finite (G.RayPrefix ω o n) := by
  let := (G.vertexBall_finite hl o n).to_subtype
  let f : G.RayPrefix ω o n → (Fin (n+1) → G.vertexBall o n) := fun p i =>
    ⟨p.vertex i,G.vertexBall_mono o (by omega) (p.ball i)⟩
  apply Finite.of_injective f
  intro p q hpq
  apply RayPrefix.ext
  funext i
  exact congrArg Subtype.val (congrFun hpq i)

lemma RayPrefix.restrict_refl {ω : Set E} {o : V} {i : ℕ} (p : G.RayPrefix ω o i) :
    p.restrict G le_rfl=p := by ext k; rfl

lemma RayPrefix.restrict_trans {ω : Set E} {o : V} {i j k : ℕ}
    (hij : i≤j) (hjk : j≤k) (p : G.RayPrefix ω o k) :
    (p.restrict G hjk).restrict G hij=p.restrict G (hij.trans hjk) := by ext k; rfl

theorem infinite_cluster_openRay (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) : ∃ r : G.OpenRay ω, r.vertex 0=o := by
  let : ∀ n, Finite (G.RayPrefix ω o n) := G.rayPrefix_finite hl ω o
  let : ∀ n, Nonempty (G.RayPrefix ω o n) := G.rayPrefix_nonempty hl hi
  obtain ⟨f,hf⟩ := exists_seq_forall_proj_of_forall_finite (α := fun n => G.RayPrefix ω o n)
    (fun {i j} h p => RayPrefix.restrict G (i := i) (j := j) h p)
    (fun {_} p => p.restrict_refl G) (fun {_ _ _} hij hjk p => p.restrict_trans G hij hjk)
    (fun _ _ => Set.toFinite _)
  let r : ℕ → V := fun n => (f n).vertex ⟨n,Nat.lt_succ_self n⟩
  have hcoh : ∀ i j (h : i≤j), (f j).vertex ⟨i,by omega⟩=r i := by
    intro i j hij
    have h := congrArg (fun p : G.RayPrefix ω o i => p.vertex ⟨i,Nat.lt_succ_self i⟩) (hf hij)
    exact h
  have hinj : Function.Injective r := by
    intro i j hij
    have hh : (f (max i j)).vertex ⟨i,by omega⟩=(f (max i j)).vertex ⟨j,by omega⟩ := by
      rw [hcoh i _ (le_max_left _ _),hcoh j _ (le_max_right _ _),hij]
    exact congrArg Fin.val ((f (max i j)).injective hh)
  have hadj : ∀ n, (G.openGraph ω).Adj (r n) (r (n+1)) := by
    intro n
    have h := (f (n+1)).adjacent ⟨n,Nat.lt_succ_self n⟩
    change (G.openGraph ω).Adj ((f (n+1)).vertex ⟨n,by omega⟩)
      ((f (n+1)).vertex ⟨n+1,by omega⟩) at h
    simpa only [hcoh n (n+1) (Nat.le_succ n),hcoh (n+1) (n+1) le_rfl] using h
  exact ⟨⟨r,hinj,hadj⟩,(f 0).start⟩

theorem infinite_induced_openRay (hl : G.LocallyFinite) (ω : Set E) (S : Set V) (o : V)
    (hi : (G.cluster (ω∩G.inducedEdges S) o).Infinite) :
    ∃ r : G.OpenRay ω, r.vertex 0=o ∧ ∀ n, r.vertex n∈S := by
  obtain ⟨r,hr⟩ := G.infinite_cluster_openRay hl hi
  refine ⟨⟨r.vertex,r.injective,fun n => G.openGraph_mono Set.inter_subset_left (r.adjacent n)⟩,
    hr,?_⟩
  intro n
  exact ((G.open_induced_adj S ω _ _).mp (r.adjacent n)).2.1

lemma no_bounded_ray_rectangles (hl : G.LocallyFinite) (u v : V → ℝ) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
      ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∀ U W : ℝ, ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
  intro U W a
  by_contra hi
  obtain ⟨r,_hr,hS⟩ := G.infinite_induced_openRay hl ω _ a hi
  exact h ⟨r,U,W,hS⟩

end CriticalPercolation.BondGraph
end
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_CorridorNormalization
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
open BondGraph

variable {V : Type*}

lemma sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]

end CriticalPercolation.Corridor
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
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma axisExit_upper (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    IsUpperSet (G.axisExit u v A L W D b) := G.restrictedSeed_upper _ _ _
lemma axisExit_finiteWitness (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    BernoulliProduct.HasFiniteOpenWitness (G.axisExit u v A L W D b) :=
  G.restrictedSeed_finiteWitness _ _ _

lemma axisExit_iff (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) (ω : Set E) :
    ω∈G.axisExit u v A L W D b ↔
      ∃ a∈A, ∃ x, ∃ w : (G.openGraph ω).Walk a x,
        (∀ y∈w.support, |u y|≤L+D ∧ |v y|≤W) ∧
        L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1,hx.2.1⟩
    intro y hy
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hy
    exact G.walk_induced_support w hx.2.2 y hy
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.walk_reachable_induced _ ω w hw,
      hx.1,hx.2,hw x w.end_mem_support⟩

lemma axisExit_of_crossing (u v : V → ℝ) (A : Set V) (L W D : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    {ω : Set E} {a x : V} (ha : a∈A) (hal : |u a|<L)
    (w : (G.openGraph ω).Walk a x) (hx : L≤|u x|)
    (hv : ∀ y∈w.support, |v y|≤W) :
    ω∈G.axisExit u v A L W D true ∪ G.axisExit u v A L W D false := by
  have hu' : ∀ ⦃x y⦄, (G.openGraph ω).Adj x y → |abs (u x)-abs (u y)|≤D := by
    intro x y hxy
    exact (abs_abs_sub_abs_le _ _).trans (hu (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨y,p,hp,hpb,hpy⟩ := _root_.OAI.SimpleGraph.Walk.bounded_first_crossing (fun x => |u x|) D L hD hu' w hal hx
  have hpath : ∀ z∈p.support, |u z|≤L+D ∧ |v z|≤W :=
    fun z hz => ⟨hpb z hz,hv z (hp hz)⟩
  by_cases hy : 0≤u y
  · apply Or.inl
    apply (G.axisExit_iff u v A L W D true ω).mpr
    refine ⟨a,ha,y,p,hpath,?_,?_⟩
    · simpa [Corridor.sign,abs_of_nonneg hy] using hpy
    · simpa [Corridor.sign,abs_of_nonneg hy] using hpb y p.end_mem_support
  · apply Or.inr
    apply (G.axisExit_iff u v A L W D false ω).mpr
    have hy' : u y≤0 := (lt_of_not_ge hy).le
    refine ⟨a,ha,y,p,hpath,?_,?_⟩
    · simpa [Corridor.sign,abs_of_nonpos hy'] using hpy
    · simpa [Corridor.sign,abs_of_nonpos hy'] using hpb y p.end_mem_support

lemma favored_of_union [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : BernoulliProduct.HasFiniteOpenWitness A)
    (hwB : BernoulliProduct.HasFiniteOpenWitness B)
    (a : ℝ) (ha : 0≤a) (hu : 1-a^2<(BernoulliProduct.law q).real (A∪B)) :
    1-a<(BernoulliProduct.law q).real A ∨ 1-a<(BernoulliProduct.law q).real B := by
  have hH := BernoulliProduct.harris_finiteWitness q A B hA hB hwA hwB
  have hBmeas := BernoulliProduct.measurableSet_finiteWitness B hB hwB
  have hunion := measureReal_union_add_inter (s := A) hBmeas (μ := BernoulliProduct.law q)
    (measure_ne_top _ _) (measure_ne_top _ _)
  have hAl : (BernoulliProduct.law q).real A≤1 := measureReal_le_one
  have hBl : (BernoulliProduct.law q).real B≤1 := measureReal_le_one
  by_contra hn
  push Not at hn
  have hm : a^2≤(1-(BernoulliProduct.law q).real A)*(1-(BernoulliProduct.law q).real B) := by
    nlinarith [mul_le_mul (by linarith : a≤1-(BernoulliProduct.law q).real A)
      (by linarith : a≤1-(BernoulliProduct.law q).real B) ha (by linarith : 0≤1-(BernoulliProduct.law q).real A)]
  nlinarith

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

lemma infinite_strip_unbounded (u v : V → ℝ) (W L : ℝ) (ω : Set E) (a : V)
    (ha : |v a|≤W)
    (hi : (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite)
    (hbox : (G.cluster (ω∩G.inducedEdges {x | |u x|≤L ∧ |v x|≤W}) a).Finite) :
    ∃ b∈G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a, L < |u b| := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbox.subset
  rintro b ⟨w⟩
  let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
  apply G.walk_reachable_induced _ ω w'
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  have hr : x∈G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a := (w.takeUntil x hx).reachable
  exact ⟨hn x hr,G.cluster_induced_subset ω _ ha hr⟩

lemma strip_cluster_gives_exit (u v : V → ℝ) (A : Set V) (W L D : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hA : ∀ a∈A, |u a|<L ∧ |v a|≤W)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster (ω∩G.inducedEdges {x | |v x|≤W}) a).Infinite)
    (hbox : ∀ a∈A, (G.cluster (ω∩G.inducedEdges {x | |u x|≤L ∧ |v x|≤W}) a).Finite) :
    ω∈G.axisExit u v A L W D true∪G.axisExit u v A L W D false := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.infinite_strip_unbounded u v W L ω a (hA a ha).2 hi (hbox a ha)
  apply G.axisExit_of_crossing u v A L W D hD hu ha (hA a ha).1
    (w.mapLe (G.openGraph_mono Set.inter_subset_left)) hb.le
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact G.cluster_induced_subset ω _ (hA a ha).2 (w.takeUntil x hx).reachable

lemma stripPercolates_measurable [Countable V] [Countable E] (v : V → ℝ) (W : ℝ) :
    MeasurableSet (G.stripPercolates v W) := by
  exact G.measurableSet_percolates.preimage ((BernoulliProduct.measurable_inter_block _).mono (BernoulliProduct.blockSigma_le _) le_rfl)

lemma someStripPercolates_measurable [Countable V] [Countable E] (v : V → ℝ) :
    MeasurableSet (G.someStripPercolates v) :=
  MeasurableSet.iUnion (fun n => G.stripPercolates_measurable v n)

lemma stripPercolates_diff_iff (v : V → ℝ) (W : ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.stripPercolates v W ↔ ω∈G.stripPercolates v W := by
  change (ω\S)∩G.inducedEdges {x | |v x|≤W}∈G.percolates ↔ _
  have heq : (ω\S)∩G.inducedEdges {x | |v x|≤W}=
      (ω∩G.inducedEdges {x | |v x|≤W})\S := by ext e; simp only [Set.mem_inter_iff,Set.mem_sdiff]; tauto
  rw [heq]
  exact G.percolates_diff_finite_iff _ S hS

lemma someStripPercolates_zero_one [Countable V] [Countable E]
    (v : V → ℝ) (q : E → unitInterval) :
    BernoulliProduct.law q (G.someStripPercolates v)=0 ∨
      BernoulliProduct.law q (G.someStripPercolates v)=1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q _ (G.someStripPercolates_measurable v)
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  simp only [someStripPercolates,Set.mem_iUnion]
  exact exists_congr (fun n => G.stripPercolates_diff_iff v n ω S hS)

lemma seedStripInfinite_mono (v : V → ℝ) {A B : Set V} (hAB : A⊆B)
    {W U : ℝ} (hWU : W≤U) : G.seedStripInfinite v A W⊆G.seedStripInfinite v B U := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi.mono (G.cluster_mono
    (Set.inter_subset_inter_right _ (G.inducedEdges_mono (fun _ hx => hx.trans hWU))) a)⟩

lemma seedStripInfinite_exhaustion (hc : G.fullGraph.Connected) (v : V → ℝ) (o : V) :
    (⋃ n : ℕ, G.seedStripInfinite v (G.vertexBall o n) n)=G.someStripPercolates v := by
  ext ω
  constructor
  · intro h
    obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n,a,hi⟩
  · intro h
    obtain ⟨n,a,hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨r,hr⟩ := G.reachable_mem_vertexBall (hc o a)
    refine Set.mem_iUnion.mpr ⟨max n r,?_⟩
    exact G.seedStripInfinite_mono v (G.vertexBall_mono o (le_max_right n r))
      (by exact_mod_cast le_max_left n r) ⟨a,hr,hi⟩

theorem exists_seed_strip_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (v : V → ℝ) (o : V) (q : E → unitInterval)
    (hpos : 0<BernoulliProduct.law q (G.someStripPercolates v))
    (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, ∃ W : ℝ, 0≤W ∧
      (∀ a∈G.vertexBall o m, |v a|≤W) ∧
      1-eps<(BernoulliProduct.law q).real (G.seedStripInfinite v (G.vertexBall o m) W) := by
  have hone := (G.someStripPercolates_zero_one v q).resolve_left (ne_of_gt hpos)
  let A := fun n : ℕ => G.seedStripInfinite v (G.vertexBall o n) n
  have hmono : Monotone A := fun n r hn => G.seedStripInfinite_mono v
    (G.vertexBall_mono o hn) (Nat.cast_le.mpr hn)
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  have heq : (⋃ n, A n)=G.someStripPercolates v := G.seedStripInfinite_exhaustion hc v o
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(BernoulliProduct.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  obtain ⟨m,hm⟩ := hnear.exists
  obtain ⟨M,hM⟩ := ((G.vertexBall_finite hl o m).image (fun a => |v a|)).bddAbove
  refine ⟨m,max (m : ℝ) M,?_,?_,?_⟩
  · exact (Nat.cast_nonneg m).trans (le_max_left _ _)
  · intro a ha
    exact (hM (Set.mem_image_of_mem _ ha)).trans (le_max_right _ _)
  · apply hm.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.seedStripInfinite_mono v (Set.Subset.refl _) (le_max_left _ _))

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripContinuity
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

lemma axisExit_mono_width (u v : V → ℝ) (A : Set V) (L D : ℝ) (b : Bool)
    {W M : ℝ} (h : W≤M) : G.axisExit u v A L W D b⊆G.axisExit u v A L M D b := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.axisExit_iff u v A L W D b ω).mp hω
  exact (G.axisExit_iff u v A L M D b ω).mpr
    ⟨a,ha,x,w,fun y hy => ⟨(hw y hy).1,(hw y hy).2.trans h⟩,hx⟩

lemma reachable_level_mem_exit_union (u v : V → ℝ) (A : Set V) (Q D : ℝ)
    (hD : 0≤D) (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    {ω : Set E} {a x : V} (ha : a∈A) (hva : |v a|<Q)
    (hw : (G.openGraph ω).Reachable a x) (hx : Q≤|v x|) :
    ω∈⋃ n : ℕ, G.axisExit v u A Q n D true∪G.axisExit v u A Q n D false := by
  obtain ⟨w⟩ := hw
  obtain ⟨M,hM⟩ := (w.support.toFinset.finite_toSet.image (fun x => |u x|)).bddAbove
  obtain ⟨n,hn⟩ := exists_nat_gt M
  apply Set.mem_iUnion.mpr
  refine ⟨n,G.axisExit_of_crossing v u A Q n D hD hv ha hva w hx ?_⟩
  intro y hy
  exact (hM (Set.mem_image_of_mem _ (by simpa using hy))).trans hn.le

theorem exists_transverse_exit_probability [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (W Q D : ℝ) (q : E → unitInterval) (r : ℝ)
    (hD : 0≤D) (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hA : ∀ a∈A, |v a|<Q)
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a, (G.cluster ω a).Infinite →
      ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hprob : r<(BernoulliProduct.law q).real (G.seedStripInfinite v A W)) :
    ∃ M : ℕ, r<(BernoulliProduct.law q).real
      (G.axisExit v u A Q M D true∪G.axisExit v u A Q M D false) := by
  let B := fun n : ℕ => G.axisExit v u A Q n D true∪G.axisExit v u A Q n D false
  have hmono : Monotone B := fun n m hnm =>
    Set.union_subset_union (G.axisExit_mono_width v u A Q D true (Nat.cast_le.mpr hnm))
      (G.axisExit_mono_width v u A Q D false (Nat.cast_le.mpr hnm))
  have hsub : G.seedStripInfinite v A W ≤ᵐ[BernoulliProduct.law q] ⋃ n, B n := by
    filter_upwards [hdir] with ω hω
    intro hseed
    obtain ⟨a,ha,hi⟩ := hseed
    have hi' : (G.cluster ω a).Infinite := hi.mono (G.cluster_mono Set.inter_subset_left a)
    obtain ⟨n,hn⟩ := exists_nat_gt Q
    obtain ⟨x,hx,hvx⟩ := hω a hi' n
    exact G.reachable_level_mem_exit_union u v A Q D hD hv ha (hA a ha) hx
      (hn.le.trans (hvx.le.trans (le_abs_self _)))
  have hb : r<(BernoulliProduct.law q).real (⋃ n, B n) :=
    hprob.trans_le (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub))
  have ht := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact (hreal.eventually (lt_mem_nhds hb)).exists

lemma longitudinal_exit_probability [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (W U D : ℝ) (q : E → unitInterval) (r : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hA : ∀ a∈A, |u a|<U ∧ |v a|≤W)
    (hbox : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a∈A,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (hprob : r<(BernoulliProduct.law q).real (G.seedStripInfinite v A W)) :
    r<(BernoulliProduct.law q).real
      (G.axisExit u v A U W D true∪G.axisExit u v A U W D false) := by
  apply hprob.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hbox] with ω hω
  exact fun hseed => G.strip_cluster_gives_exit u v A W U D hD hu hA hseed hω

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripLinear
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

lemma signed_div_abs (b : Bool) (x U : ℝ) (hU : 0<U) :
    |Corridor.sign b*x/U|=|x|/U := by
  rw [abs_div,abs_mul,Corridor.sign_abs,one_mul,abs_of_pos hU]

lemma signed_exit_error (b : Bool) (x U D : ℝ) (hU : 0<U)
    (hx : U≤Corridor.sign b*x) (hx' : Corridor.sign b*x≤U+D) :
    |Corridor.sign b*x/U-1|≤D/U := by
  rw [abs_of_nonneg (by exact sub_nonneg.mpr ((le_div_iff₀ hU).mpr (by simpa using hx)))]
  exact (sub_le_iff_le_add).mpr ((div_le_iff₀ hU).mpr (by
    simpa only [add_mul,div_mul_cancel₀ _ hU.ne',one_mul,add_comm] using hx'))

lemma strip_coordinate_bounds (u v : V → ℝ) (U Q : ℝ) (a b : Bool)
    (hU : 0<U) (hQ : 0<Q) (x : V) :
    |stripTime u v U Q a b x|≤|u x|/U+|v x|/Q ∧
    |stripHeight u v U Q a b x|≤|u x|/U+|v x|/Q := by
  constructor
  · exact (abs_add_le _ _).trans_eq (by rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ])
  · exact (abs_sub _ _).trans_eq (by rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ])

lemma strip_coordinate_increments (u v : V → ℝ) (U Q D : ℝ) (a b : Bool)
    (hU : 0<U) (hQ : 0<Q)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D) :
    (∀ ⦃x y⦄, G.fullGraph.Adj x y →
      |stripTime u v U Q a b x-stripTime u v U Q a b y|≤D/U+D/Q) ∧
    (∀ ⦃x y⦄, G.fullGraph.Adj x y →
      |stripHeight u v U Q a b x-stripHeight u v U Q a b y|≤D/U+D/Q) := by
  have hsum : ∀ ⦃x y⦄, G.fullGraph.Adj x y →
      |Corridor.sign a*(u x-u y)/U|+|Corridor.sign b*(v x-v y)/Q|≤D/U+D/Q := by
    intro x y hxy
    rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ]
    exact add_le_add (div_le_div_of_nonneg_right (hu hxy) hU.le)
      (div_le_div_of_nonneg_right (hv hxy) hQ.le)
  constructor
  · intro x y hxy
    calc
      _ = |Corridor.sign a*(u x-u y)/U+Corridor.sign b*(v x-v y)/Q| := by
        congr 1; unfold stripTime; ring
      _ ≤ _ := (abs_add_le _ _).trans (hsum hxy)
  · intro x y hxy
    calc
      _ = |Corridor.sign a*(u x-u y)/U-Corridor.sign b*(v x-v y)/Q| := by
        congr 1; unfold stripHeight; ring
      _ ≤ _ := (abs_sub _ _).trans (hsum hxy)

lemma longitudinal_exit_boxMove (u v : V → ℝ) (o : V) (m : ℕ)
    (U Q W D eps : ℝ) (a b : Bool) (huo : u o=0) (hvo : v o=0)
    (hU : 0<U) (hQ : 0<Q) (heps : 0<eps) (hep : eps<1/10)
    (hDU : D/U≤eps/1000) (hWQ : W/Q≤eps/1000) :
    G.axisExit u v (G.vertexBall o m) U W D a ⊆
      G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o 1 := by
  intro ω hω
  obtain ⟨x,hx,y,w,hw,hy,hy'⟩ := (G.axisExit_iff u v (G.vertexBall o m) U W D a ω).mp hω
  have ho : stripTime u v U Q a b o=0 ∧ stripHeight u v U Q a b o=0 := by
    simp [stripTime,stripHeight,huo,hvo]
  have hpath : ∀ x∈w.support,
      |stripTime u v U Q a b x|≤30 ∧ |stripHeight u v U Q a b x|≤30 := by
    intro z hz
    have hb := strip_coordinate_bounds u v U Q a b hU hQ z
    have h1 := div_le_div_of_nonneg_right (hw z hz).1 hU.le
    have h2 := div_le_div_of_nonneg_right (hw z hz).2 hQ.le
    have huq : (U+D)/U=1+D/U := by rw [add_div,div_self hU.ne']
    rw [huq] at h1
    constructor <;> linarith [hb.1,hb.2]
  have he1 := signed_exit_error a (u y) U D hU hy hy'
  have he2 : |Corridor.sign b*v y/Q|≤W/Q := by
    rw [signed_div_abs b _ _ hQ]
    exact div_le_div_of_nonneg_right (hw y w.end_mem_support).2 hQ.le
  refine ⟨x,hx,y,w,?_,?_,?_⟩
  · simpa only [ho.1,ho.2,sub_zero] using hpath
  · rw [ho.1,zero_add]
    have h := abs_add_le (Corridor.sign a*u y/U-1) (Corridor.sign b*v y/Q)
    have heq : stripTime u v U Q a b y-1=(Corridor.sign a*u y/U-1)+Corridor.sign b*v y/Q := by
      unfold stripTime; ring
    rw [heq]
    linarith
  · rw [ho.2,zero_add]
    have h := abs_sub (Corridor.sign a*u y/U-1) (Corridor.sign b*v y/Q)
    have heq : stripHeight u v U Q a b y-1=(Corridor.sign a*u y/U-1)-Corridor.sign b*v y/Q := by
      unfold stripHeight; ring
    rw [heq]
    linarith

lemma transverse_exit_boxMove (u v : V → ℝ) (o : V) (m : ℕ)
    (U Q M D eps : ℝ) (a b : Bool) (huo : u o=0) (hvo : v o=0)
    (hU : 0<U) (hQ : 0<Q) (heps : 0<eps) (hep : eps<1/10)
    (hMU : M/U≤eps/1000) (hDQ : D/Q≤eps/1000) :
    G.axisExit v u (G.vertexBall o m) Q M D b ⊆
      G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o (-1) := by
  intro ω hω
  obtain ⟨x,hx,y,w,hw,hy,hy'⟩ := (G.axisExit_iff v u (G.vertexBall o m) Q M D b ω).mp hω
  have ho : stripTime u v U Q a b o=0 ∧ stripHeight u v U Q a b o=0 := by
    simp [stripTime,stripHeight,huo,hvo]
  have hpath : ∀ x∈w.support,
      |stripTime u v U Q a b x|≤30 ∧ |stripHeight u v U Q a b x|≤30 := by
    intro z hz
    have hb := strip_coordinate_bounds u v U Q a b hU hQ z
    have h1 := div_le_div_of_nonneg_right (hw z hz).1 hQ.le
    have h2 := div_le_div_of_nonneg_right (hw z hz).2 hU.le
    have huq : (Q+D)/Q=1+D/Q := by rw [add_div,div_self hQ.ne']
    rw [huq] at h1
    constructor <;> linarith [hb.1,hb.2]
  have he1 := signed_exit_error b (v y) Q D hQ hy hy'
  have he2 : |Corridor.sign a*u y/U|≤M/U := by
    rw [signed_div_abs a _ _ hU]
    exact div_le_div_of_nonneg_right (hw y w.end_mem_support).2 hU.le
  refine ⟨x,hx,y,w,?_,?_,?_⟩
  · simpa only [ho.1,ho.2,sub_zero] using hpath
  · rw [ho.1,zero_add]
    have h := abs_add_le (Corridor.sign a*u y/U) (Corridor.sign b*v y/Q-1)
    have heq : stripTime u v U Q a b y-1=Corridor.sign a*u y/U+(Corridor.sign b*v y/Q-1) := by
      unfold stripTime; ring
    rw [heq]
    linarith
  · rw [ho.2,zero_add]
    have h := abs_sub (Corridor.sign a*u y/U) (Corridor.sign b*v y/Q-1)
    have heq : stripHeight u v U Q a b y-(-1)=Corridor.sign a*u y/U-(Corridor.sign b*v y/Q-1) := by
      unfold stripHeight; ring
    rw [heq]
    linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripOrigin
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

lemma exists_strip_scale (B K d : ℝ) (hd : 0<d) :
    ∃ U : ℝ, 0<U ∧ B<U ∧ K/U<d := by
  obtain ⟨U,hU⟩ := exists_gt (max 0 (max B (K/d)))
  have hU0 : 0<U := (le_max_left _ _).trans_lt hU
  have hBU : B<U := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hU
  have hKU : K/d<U := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hU
  exact ⟨U,hU0,hBU,(div_lt_iff₀ hU0).mpr (by nlinarith [(div_lt_iff₀ hd).mp hKU])⟩

theorem strip_origin_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (u v : V → ℝ) (o : V) (D : ℝ) (p : unitInterval)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hstrip : 0<(BernoulliProduct.law (fun _ : E => p)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => p),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => p), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ U Q : ℝ, ∃ a b : Bool,
      0<U ∧ 0<Q ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |stripTime u v U Q a b x-stripTime u v U Q a b y| ≤ rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y →
        |stripHeight u v U Q a b x-stripHeight u v U Q a b y| ≤ rho) ∧
      ∀ s : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => p)).real
        (G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o
          (Corridor.sign s)) := by
  obtain ⟨m,W,hW,hseed,hprob⟩ := G.exists_seed_strip_probability hc hl v o
    (fun _ : E => p) hstrip ((eta/30)^2) (sq_pos_of_pos (by linarith))
  refine ⟨m,?_⟩
  intro rho hrho
  let d := min (eps/1000) (rho/2)
  have hd : 0<d := lt_min (by linarith) (by linarith)
  have hde : d≤eps/1000 := min_le_left _ _
  have hdr : d ≤ rho/2 := min_le_right _ _
  obtain ⟨Q,hQ,hWQ,hKQ⟩ := exists_strip_scale W (max W D) d hd
  have hDQ : D/Q≤d := ((div_le_div_of_nonneg_right (le_max_right W D) hQ.le).trans hKQ.le)
  have hWQ' : W/Q≤d := ((div_le_div_of_nonneg_right (le_max_left W D) hQ.le).trans hKQ.le)
  obtain ⟨M,hMprob⟩ := G.exists_transverse_exit_probability u v (G.vertexBall o m) W Q D
    (fun _ : E => p) (1-(eta/30)^2) hD hv (fun a ha => (hseed a ha).trans_lt hWQ) hdir hprob
  obtain ⟨K,hK⟩ := ((G.vertexBall_finite hl o m).image (fun x => |u x|)).bddAbove
  obtain ⟨U,hU,hKU,hMU⟩ := exists_strip_scale K (max (M : ℝ) D) d hd
  have hDU : D/U≤d := ((div_le_div_of_nonneg_right (le_max_right (M : ℝ) D) hU.le).trans hMU.le)
  have hMU' : (M : ℝ)/U≤d := ((div_le_div_of_nonneg_right (le_max_left (M : ℝ) D) hU.le).trans hMU.le)
  have hUprob := G.longitudinal_exit_probability u v (G.vertexBall o m) W U D
    (fun _ : E => p) (1-(eta/30)^2) hD hu
    (fun a ha => ⟨(hK (Set.mem_image_of_mem _ ha)).trans_lt hKU,hseed a ha⟩)
    ((hbox U W).mono (fun _ h a _ => h a)) hprob
  have hesq : 1-(eta/10)^2≤1-(eta/30)^2 := by nlinarith [sq_nonneg eta]
  have hsignU := favored_of_union (fun _ : E => p) _ _
    (G.axisExit_upper u v _ U W D true) (G.axisExit_upper u v _ U W D false)
    (G.axisExit_finiteWitness u v _ U W D true) (G.axisExit_finiteWitness u v _ U W D false)
    (eta/10) (by linarith) (hesq.trans_lt hUprob)
  have hsignQ := favored_of_union (fun _ : E => p) _ _
    (G.axisExit_upper v u _ Q M D true) (G.axisExit_upper v u _ Q M D false)
    (G.axisExit_finiteWitness v u _ Q M D true) (G.axisExit_finiteWitness v u _ Q M D false)
    (eta/10) (by linarith) (hesq.trans_lt hMprob)
  have hbool : ∀ (F : Bool → ℝ), (1-eta/10<F true ∨ 1-eta/10<F false) →
      ∃ a : Bool, 1-eta<F a := by
    intro F h
    rcases h with h|h
    · exact ⟨true,(by linarith : 1-eta<1-eta/10).trans h⟩
    · exact ⟨false,(by linarith : 1-eta<1-eta/10).trans h⟩
  obtain ⟨a,ha⟩ := hbool (fun a => (BernoulliProduct.law (fun _ : E => p)).real
    (G.axisExit u v (G.vertexBall o m) U W D a)) hsignU
  obtain ⟨b,hb⟩ := hbool (fun b => (BernoulliProduct.law (fun _ : E => p)).real
    (G.axisExit v u (G.vertexBall o m) Q M D b)) hsignQ
  have hcmesh := G.strip_coordinate_increments u v U Q D a b hU hQ hu hv
  have hmesh : D/U+D/Q ≤ rho := by linarith
  refine ⟨U,Q,a,b,hU,hQ,(fun {_ _} h => (hcmesh.1 h).trans hmesh),
    (fun {_ _} h => (hcmesh.2 h).trans hmesh),?_⟩
  intro s
  cases s
  · apply hb.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.transverse_exit_boxMove u v o m U Q M D eps a b huo hvo hU hQ heps heps'
      (hMU'.trans hde) (hDQ.trans hde))
  · apply ha.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.longitudinal_exit_boxMove u v o m U Q W D eps a b huo hvo hU hQ heps heps'
      (hDU.trans hde) (hWQ'.trans hde))

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripUniform
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

lemma strip_aut_differences (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (φ : G.Aut)
    (hu : ∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y)
    (hv : ∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y) :
    (∀ x y, stripTime u v U Q a b (φ.vertex x)-stripTime u v U Q a b (φ.vertex y)=
      stripTime u v U Q a b x-stripTime u v U Q a b y) ∧
    (∀ x y, stripHeight u v U Q a b (φ.vertex x)-stripHeight u v U Q a b (φ.vertex y)=
      stripHeight u v U Q a b x-stripHeight u v U Q a b y) := by
  constructor
  · intro x y
    calc
      _ = Corridor.sign a*(u (φ.vertex x)-u (φ.vertex y))/U+
        Corridor.sign b*(v (φ.vertex x)-v (φ.vertex y))/Q := by unfold stripTime; ring
      _ = _ := by rw [hu,hv]; unfold stripTime; ring
  · intro x y
    calc
      _ = Corridor.sign a*(u (φ.vertex x)-u (φ.vertex y))/U-
        Corridor.sign b*(v (φ.vertex x)-v (φ.vertex y))/Q := by unfold stripHeight; ring
      _ = _ := by rw [hu,hv]; unfold stripHeight; ring

theorem strip_uniform_moves [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hstrip : 0<(BernoulliProduct.law (fun _ : E => pc)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => pc), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0 < rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |t x-t y| ≤ rho) ∧
      (∀ ⦃x y⦄, G.fullGraph.Adj x y → |z x-z y| ≤ rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.strip_origin_moves hc hl u v o D pc hD huo hvo hu hv
    hstrip hdir hbox eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hcpos : 0<(c : ℝ)+1 := by positivity
  have hr : 0 < r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r ≤ rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨U,Q,a,b,_hU,_hQ,ht,hz,hmoves⟩ := hm r hr
  have htdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, stripTime u v U Q a b (φ.vertex x)-stripTime u v U Q a b (φ.vertex y)=
        stripTime u v U Q a b x-stripTime u v U Q a b y) ∧
      (∀ x y, stripHeight u v U Q a b (φ.vertex x)-stripHeight u v U Q a b (φ.vertex y)=
        stripHeight u v U Q a b x-stripHeight u v U Q a b y) := by
    intro y
    obtain ⟨φ,hφ,hφu,hφv⟩ := hdense y
    exact ⟨φ,hφ,G.strip_aut_differences u v U Q a b φ hφu hφv⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.uniform_moves_of_origin (stripTime u v U Q a b)
    (stripHeight u v U Q a b) o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨stripTime u v U Q a b,stripHeight u v U Q a b,p,hpl,hpu,
    fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩

theorem strip_critical_contradiction [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.criticalProbability : ℝ))
    (hpc1 : (G.criticalProbability : ℝ)<1) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hstrip : 0<(BernoulliProduct.law (fun _ : E => G.criticalProbability)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite) : False := by
  apply G.approximate_moves_contradiction_bs hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.strip_uniform_moves hc hl u v o c D G.criticalProbability hD hpc huo hvo hu hv hdense
    hstrip hdir hbox eps eta he he' heta

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_StripCritical
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

theorem critical_strip_null_bs_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (hpc1 : G.criticalProbability<1)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hvunbounded : ∀ n : ℕ, ∃ x, (n : ℝ)<v x)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    G.law G.criticalProbability (G.someStripPercolates v)=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra hne
  have hstrip : 0<(BernoulliProduct.law (fun _ : E => G.criticalProbability))
      (G.someStripPercolates v) := by
    simpa only [law,BernoulliProduct.law_const] using (pos_iff_ne_zero.mpr hne)
  have hsub : G.someStripPercolates v⊆G.percolates := by
    intro ω hω
    obtain ⟨n,a,ha⟩ := Set.mem_iUnion.mp hω
    exact ⟨a,ha.mono (G.cluster_mono Set.inter_subset_left a)⟩
  have hpositive : 0<G.law G.criticalProbability G.percolates :=
    (pos_iff_ne_zero.mpr hne).trans_le (measure_mono hsub)
  have hpc := G.criticalProbability_pos hc hl hq
  have hdir := G.unique_cluster_direction_unbounded_ae_bs hc hl hq hg G.criticalProbability
    ⟨hpc,hpc1⟩ hpositive v hvunbounded
  have hdir' : ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x := by
    simpa only [law,BernoulliProduct.law_const] using hdir
  have hbox : ∀ U W : ℝ, ∀ᵐ ω ∂BernoulliProduct.law (fun _ : E => G.criticalProbability), ∀ a,
      (G.cluster (ω∩G.inducedEdges {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
    intro U W
    have h := hnoray.mono (fun ω hω => G.no_bounded_ray_rectangles hl u v ω hω U W)
    simpa only [law,BernoulliProduct.law_const] using h
  exact G.strip_critical_contradiction hc hl hq u v o c D hD hpc hpc1 huo hvo hu hv hdense
    hstrip hdir' hbox

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.critical_strip_null_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.critical_strip_null_bs_oai.{u_1, u_2}
