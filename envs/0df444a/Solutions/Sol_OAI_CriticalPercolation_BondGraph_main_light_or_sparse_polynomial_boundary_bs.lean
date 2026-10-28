-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:52:06.74599+00:00
-- url     : https://prove2.me/submissions/20a45e9d-a8c7-4f23-aee1-9234aef1862f

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_CombinatoriallyUnimodular_exponential_critical_null_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_eventually_no_superpolynomial_band_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_uniform_rooted_probability_bs
import Theorems.Thm_OAI_CriticalPercolation_Sharpness_critical_null_of_unique_bs

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

lemma infiniteEvent_eq_iInter_clusterTail (o : V) :
    G.infiniteEvent o = ⋂ n, G.clusterTail o n := by
  apply Set.Subset.antisymm
  · exact Set.subset_iInter fun n => G.infiniteEvent_subset_clusterTail o n
  · intro ω hω
    change (G.cluster ω o).Infinite
    intro hfin
    obtain ⟨K, hK, hKω, hn⟩ := Set.mem_iInter.mp hω ((G.cluster ω o).ncard + 1)
    have hle := Set.ncard_le_ncard hKω hfin
    omega

lemma tendsto_real_clusterTail [Countable E] (p : unitInterval) (o : V) :
    Tendsto (fun n => (G.law p).real (G.clusterTail o n)) atTop
      (𝓝 ((G.law p).real (G.infiniteEvent o))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (G.measurableSet_clusterTail o n).nullMeasurableSet)
    (G.clusterTail_antitone o)
    ⟨0, measure_ne_top _ _⟩
  rw [← G.infiniteEvent_eq_iInter_clusterTail o] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma Aut.preimage_clusterTail (φ : G.Aut) (o : V) (n : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.clusterTail (φ.vertex o) n =
      G.clusterTail o n := by
  ext ω
  simp only [Set.mem_preimage, clusterTail, Set.mem_ofPred_eq]
  rw [← φ.cluster_image]
  constructor
  · rintro ⟨K, hK, hKω, hn⟩
    refine ⟨φ.vertex.symm '' K, hK.image _, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hKω hv
      simpa using hw
    · rwa [Set.ncard_image_of_injective _ φ.vertex.symm.injective]
  · rintro ⟨K, hK, hKω, hn⟩
    exact ⟨φ.vertex '' K, hK.image _, Set.image_mono hKω,
      by rwa [Set.ncard_image_of_injective _ φ.vertex.injective]⟩

lemma Aut.clusterTail_real [Countable E] (φ : G.Aut) (p : unitInterval) (o : V) (n : ℕ) :
    (G.law p).real (G.clusterTail (φ.vertex o) n) = (G.law p).real (G.clusterTail o n) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_clusterTail _ _), φ.preimage_clusterTail]

theorem subcritical_uniform_clusterTail
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (p : unitInterval) (hp : 0 < p)
    (θ : ℝ) (hθ : 0 < θ)
    (hroot : ∀ o, θ ≤ (G.law p).real (G.infiniteEvent o)) (L : ℕ) :
    ∃ q : unitInterval, (p : ℝ) / 2 ≤ q ∧ q < p ∧
      ∀ o, 3 * θ / 4 < (G.law q).real (G.clusterTail o L) := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  obtain ⟨S, hS, hcover⟩ := hquasi
  let := hS.fintype
  obtain ⟨q, hhalf, hqp, hq⟩ := BernoulliProduct.exists_lower_parameter
    (fun o : S => G.clusterTail o.val L)
    (fun o => G.clusterTail_isUpperSet o.val L)
    (fun o => G.clusterTail_hasFiniteOpenWitness o.val L)
    p hp (fun _ => 3 * θ / 4) (by
      intro o
      rw [BernoulliProduct.law_const]
      change 3 * θ / 4 < (G.law p).real (G.clusterTail o.val L)
      have hn := measureReal_mono (μ := G.law p) (G.infiniteEvent_subset_clusterTail o.val L)
      have ho := hroot o.val
      linarith)
  refine ⟨q, hhalf, hqp, fun o => ?_⟩
  obtain ⟨v, hv, φ, rfl⟩ := hcover o
  rw [φ.clusterTail_real]
  simpa only [BernoulliProduct.law_const, law] using hq ⟨v, hv⟩

lemma tendsto_real_clusterTail_subcritical [Countable V] [Countable E]
    {p : unitInterval} (hp : p < G.criticalProbability) (o : V) :
    Tendsto (fun n => (G.law p).real (G.clusterTail o n)) atTop (𝓝 0) := by
  have hz : G.law p (G.infiniteEvent o) = 0 := by
    exact measure_mono_null (show G.infiniteEvent o ⊆ G.percolates from
      fun ω hω => ⟨o, hω⟩) (G.law_percolates_eq_zero_of_lt_critical hp)
  simpa only [measureReal_def, hz, ENNReal.toReal_zero] using G.tendsto_real_clusterTail p o

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_BandScale
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

namespace CriticalPercolation

lemma bandScale_zero (L : ℕ) : bandScale L 0 = L := by simp [bandScale]
lemma bandScale_succ (L j : ℕ) : bandScale L (j + 1) = bandScale L j ^ 2 := by
  simp only [bandScale, pow_succ, pow_mul]
lemma bandScale_ge {L : ℕ} (_hL : 2 ≤ L) (j : ℕ) : L ≤ bandScale L j := by
  exact Nat.le_pow (by positivity)

lemma bandScale_tendsto {L : ℕ} (hL : 2 ≤ L) :
    Tendsto (bandScale L) atTop atTop := by
  exact (tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < L)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))

lemma log_bandScale {L : ℕ} (_hL : 2 ≤ L) (j : ℕ) :
    Real.log (bandScale L j) = (2 : ℝ) ^ j * Real.log L := by
  simp [bandScale, Nat.cast_pow, Real.log_pow]

lemma band_weight {L : ℕ} (hL : 2 ≤ L) (j : ℕ) :
    (Real.log (bandScale L j))⁻¹ ^ 2 =
      (1 / 4 : ℝ) ^ j * (Real.log L)⁻¹ ^ 2 := by
  rw [log_bandScale hL, mul_inv_rev, mul_pow, mul_comm]
  congr 1
  rw [← inv_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

lemma band_weight_sum_lt {L : ℕ} (hL : 2 ≤ L) (k : ℕ) :
    ∑ j ∈ Finset.range k, (Real.log (bandScale L j))⁻¹ ^ 2 <
      4 / (3 * (Real.log L) ^ 2) := by
  have hlog : 0 < Real.log L := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  simp_rw [band_weight hL]
  rw [← Finset.sum_mul]
  have hg : ∑ j ∈ Finset.range k, (1/4:ℝ)^j < 4/3 := by
    have he := geom_sum_mul (1/4:ℝ) k
    have hp := pow_pos (by norm_num : (0:ℝ) < 1/4) k
    nlinarith
  have hi : 0 < (Real.log L)⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hlog)
  have hm := mul_lt_mul_of_pos_right hg hi
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  simp [div_eq_mul_inv, inv_pow, mul_assoc, mul_comm, mul_left_comm]

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma real_clusterBand [Countable E] (p : unitInterval) (o : V) (s : ℕ) :
    (G.law p).real (G.clusterBand o s) =
      (G.law p).real (G.clusterTail o s) - (G.law p).real (G.clusterTail o (s ^ 2)) := by
  exact measureReal_sdiff (G.clusterTail_antitone o (Nat.le_pow (by omega)))
    (G.measurableSet_clusterTail o (s ^ 2))

lemma sum_real_clusterBand [Countable E] (p : unitInterval) (o : V) (L k : ℕ) :
    ∑ j ∈ Finset.range k, (G.law p).real (G.clusterBand o (bandScale L j)) =
      (G.law p).real (G.clusterTail o L) -
        (G.law p).real (G.clusterTail o (bandScale L k)) := by
  simp_rw [G.real_clusterBand, ← bandScale_succ]
  simpa only [bandScale_zero] using Finset.sum_range_sub'
    (fun j => (G.law p).real (G.clusterTail o (bandScale L j))) k

theorem exists_subcritical_clusterBand [Nonempty V]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hp : 0 < G.criticalProbability)
    (θ : ℝ) (hθ : 0 < θ)
    (hroot : ∀ o, θ ≤ (G.law G.criticalProbability).real (G.infiniteEvent o))
    (L : ℕ) (hL : 2 ≤ L) (hlarge : 4 / (3 * (Real.log L)^2) < θ / 4) :
    ∃ q : unitInterval, (G.criticalProbability : ℝ) / 2 ≤ q ∧
      q < G.criticalProbability ∧ ∃ z : V, ∃ s : ℕ, L ≤ s ∧
      (Real.log s)⁻¹ ^ 2 ≤ (G.law q).real (G.clusterBand z s) ∧
      ∀ o, θ / 2 ≤ (G.law q).real (G.clusterTail o s) := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  obtain ⟨q, hqhalf, hqpc, hq⟩ := G.subcritical_uniform_clusterTail
    hconnected hlocal hquasi G.criticalProbability hp θ hθ hroot L
  have hex : ∃ k, ∃ z : V, (G.law q).real (G.clusterTail z (bandScale L k)) < θ / 2 := by
    let o : V := Classical.arbitrary V
    have ht := (G.tendsto_real_clusterTail_subcritical hqpc o).comp (bandScale_tendsto hL)
    obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ) < θ/2))).exists
    exact ⟨k, o, hk⟩
  let k := Nat.find hex
  obtain ⟨z, hz⟩ := Nat.find_spec hex
  have hpre : ∀ j < k, ∀ o : V,
      θ / 2 ≤ (G.law q).real (G.clusterTail o (bandScale L j)) := by
    intro j hj o
    by_contra! h
    exact Nat.find_min hex hj ⟨o, h⟩
  have hsum : θ / 4 < ∑ j ∈ Finset.range k,
      (G.law q).real (G.clusterBand z (bandScale L j)) := by
    rw [G.sum_real_clusterBand]
    have hqz := hq z
    change (G.law q).real (G.clusterTail z (bandScale L k)) < θ / 2 at hz
    linarith
  have hexj : ∃ j ∈ Finset.range k, (Real.log (bandScale L j))⁻¹ ^ 2 ≤
      (G.law q).real (G.clusterBand z (bandScale L j)) := by
    by_contra! hj
    have hle := Finset.sum_le_sum (s := Finset.range k) (fun j hjk => (hj j hjk).le)
    have hlt := (band_weight_sum_lt hL k).trans hlarge
    linarith
  obtain ⟨j, hj, hband⟩ := hexj
  exact ⟨q, hqhalf, hqpc, z, bandScale L j, bandScale_ge hL j, hband,
    hpre j (Finset.mem_range.mp hj)⟩

end BondGraph
end CriticalPercolation
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

lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h

theorem independent_block_family (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndep (fun i => blockSigma (S i)) (law q) := by
  apply (iIndep_iff _ _).mpr
  intro t
  induction t using Finset.induction_on with
  | empty => intro f hf; simp
  | @insert i t hi ih =>
    intro f hf
    let T := ⋃ j ∈ t, S j
    have hj : ∀ j ∈ t, blockSigma (S j) ≤ blockSigma T := by
      intro j hj
      exact blockSigma_mono (fun e he => Set.mem_iUnion₂.mpr ⟨j,hj,he⟩)
    have hm : MeasurableSet[blockSigma T] (⋂ j ∈ t, f j) := by
      apply MeasurableSet.biInter t.finite_toSet.countable
      intro j hjt
      exact hj j hjt _ (hf j (Finset.mem_insert_of_mem hjt))
    have hdis : Disjoint (S i) T := by
      apply Set.disjoint_left.mpr
      intro e hei heT
      obtain ⟨j,hjt,hje⟩ := Set.mem_iUnion₂.mp heT
      exact Set.disjoint_left.mp (hS (by intro h; subst j; exact hi hjt)) hei hje
    have hmuli := ((independent_disjoint_blocks q (S i) T hdis).indepSet_of_measurableSet
      (hf i (Finset.mem_insert_self i t)) hm).measure_inter_eq_mul
    rw [Finset.set_biInter_insert,Finset.prod_insert hi,hmuli]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma independent_block_events (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (A : I → Set (Set E))
    (hA : ∀ i, MeasurableSet[blockSigma (S i)] (A i)) : iIndepSet A (law q) :=
  (independent_block_family q S hS).iIndepSets'.iIndepSet_of_mem hA
    (fun i => blockSigma_le (S i) _ (hA i))

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

lemma law_closedBlock_const (p : unitInterval) (S : Set E) (hS : S.Finite) :
    law (fun _ : E => p) (closedBlock S) =
      (bitMeasure p {False}) ^ S.ncard := by
  rw [law_closedBlock (fun _ : E => p) S hS,Finset.prod_const]
  rw [Set.ncard_eq_toFinset_card S hS]

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ClosedCutProbability
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma bitMeasure_false_ne_zero (p : unitInterval) (hp : (p:ℝ)<1) :
    bitMeasure p {False} ≠ 0 := by
  have hh := bitMeasure_real_singleton p False
  simp only [bitWeight,if_false] at hh
  intro hz
  have : (bitMeasure p).real {False}=0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  linarith

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ClosedBoundedCuts
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma frequently_closedBlock_ae_of_card_le (p : unitInterval) (hp : (p:ℝ)<1)
    (S : ℕ → Set E) (hS : ∀ n, (S n).Finite)
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m))) (N : ℕ)
    (hN : ∀ n, (S n).ncard ≤ N) :
    ∀ᵐ ω ∂law (fun _ : E => p), ∃ᶠ n in atTop, ω ∈ closedBlock (S n) := by
  let A := fun n => closedBlock (S n)
  have hm' : ∀ n, MeasurableSet[blockSigma (S n)] (A n) :=
    fun n => measurableSet_closedBlock (S n) (hS n).countable
  have hm : ∀ n, MeasurableSet (A n) := fun n => blockSigma_le (S n) _ (hm' n)
  have hi := independent_block_events (fun _ : E => p) S hdis A hm'
  have hprob : ∀ n, (bitMeasure p {False})^N ≤ law (fun _ : E => p) (A n) := by
    intro n
    rw [law_closedBlock_const p (S n) (hS n)]
    exact pow_le_pow_of_le_one zero_le (prob_le_one) (hN n)
  have hsum : (∑' n, law (fun _ : E => p) (A n)) = ∞ := by
    apply top_unique
    calc
      ∞ = ∑' _n : ℕ, (bitMeasure p {False})^N :=
        (ENNReal.tsum_const_eq_top_of_ne_zero
          (pow_ne_zero _ (bitMeasure_false_ne_zero p hp))).symm
      _ ≤ _ := ENNReal.tsum_le_tsum hprob
  have hlim := measure_limsup_eq_one hm hi hsum
  have hh : ∀ᵐ ω ∂law (fun _ : E => p), ω ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr hlim
  exact hh.mono (fun _ h => Filter.mem_limsup_iff_frequently_mem.mp h)

end CriticalPercolation.BernoulliProduct
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CutEdges
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
open scoped Classical

variable {V E : Type*}

lemma not_reachable_of_cut_closed (G : BondGraph V E) (O : Set V) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) {a b : V} (ha : a ∉ O) (hb : b ∈ O) :
    ¬(G.openGraph ω).Reachable a b := by
  intro hab
  have hclosed : ∀ ⦃v z⦄, v ∈ Oᶜ → (G.openGraph ω).Adj v z → z ∈ Oᶜ := by
    intro v z hv hvz hz
    obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvz
    exact hc e ⟨v,z,heq,hv,hz⟩ he
  exact (ClusterDeletion.reachable_mem_of_closed hclosed ha hab) hb

end CriticalPercolation.BondGraph

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

lemma orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) (u : V) :
    ∃ C : ℕ, ∀ v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  have hpath : ∀ z : S, ∃ n, u ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hconnected z u)
  choose n hn using hpath
  let := hS.fintype
  let C := ∑ z : S, n z
  refine ⟨C,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  refine ⟨φ,(Aut.vertexBall_mem G φ z u C).mpr ?_⟩
  exact G.vertexBall_mono z (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨z,hz⟩ : S))) (hn ⟨z,hz⟩)

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

lemma uniform_orbit_density_radius (hconnected : G.fullGraph.Connected)
    (hquasi : G.QuasiTransitive) :
    ∃ C : ℕ, ∀ u v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨R,hR⟩ := G.finite_subset_vertexBall hconnected o hS
  refine ⟨R+R,?_⟩
  intro u v
  obtain ⟨z,hz,φ,hφ⟩ := hcover u
  obtain ⟨w,hw,ψ,hψ⟩ := hcover v
  refine ⟨Aut.trans G (Aut.symm G φ) ψ,?_⟩
  change ψ.vertex (φ.vertex.symm u) ∈ G.vertexBall v (R+R)
  rw [← hφ,Equiv.symm_apply_apply,← hψ,Aut.vertexBall_mem]
  exact G.vertexBall_add ((G.vertexBall_comm).mp (hR hw)) R (hR hz)

lemma vertexBall_ncard_pos (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    0 < (G.vertexBall o n).ncard :=
  (Set.ncard_pos (G.vertexBall_finite hlocal o n)).mpr ⟨o,G.mem_vertexBall_self o n⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_GrowthAlternatives
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma volume_le_maxVolume (hq : G.QuasiTransitive) (v : V) (n : ℕ) :
    (G.vertexBall v n).ncard ≤ G.maxVolume n := by
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq n
  exact le_csSup ⟨M,by rintro _ ⟨w,rfl⟩; exact hM w⟩ ⟨v,rfl⟩

lemma exists_maxVolume [Nonempty V] (hq : G.QuasiTransitive) (n : ℕ) :
    ∃ v, G.maxVolume n=(G.vertexBall v n).ncard := by
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq n
  have hne : (Set.range fun v => (G.vertexBall v n).ncard).Nonempty := Set.range_nonempty _
  obtain ⟨v,hv⟩ := Nat.sSup_mem hne ⟨M,by rintro _ ⟨w,rfl⟩; exact hM w⟩
  exact ⟨v,hv.symm⟩

lemma vertexBall_add_cover (o : V) (r s : ℕ) :
    G.vertexBall o (r+s) ⊆ ⋃ v∈G.vertexBall o r, G.vertexBall v s := by
  induction s with
  | zero =>
    intro v hv
    exact Set.mem_iUnion₂.mpr ⟨v,hv,rfl⟩
  | succ s ih =>
    rintro w (hw|hw)
    · obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp (ih hw)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,G.vertexBall_mono v (Nat.le_succ _) hw⟩
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      obtain ⟨v,hv,hz⟩ := Set.mem_iUnion₂.mp (ih hz)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,G.vertexBall_step hz hzw⟩

lemma ncard_biUnion_le_sum {ι X : Type*} (S : Finset ι) (F : ι → Set X)
    (hF : ∀ i∈S, (F i).Finite) :
    (⋃ i∈(S : Set ι), F i).ncard ≤ ∑ i∈S, (F i).ncard := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp only [Finset.mem_insert] at hF
    rw [Finset.coe_insert,Set.biUnion_insert,Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left
      (ih (fun i hi => hF i (Or.inr hi))) _)

lemma maxVolume_submultiplicative [Nonempty V] (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (r s : ℕ) :
    G.maxVolume (r+s) ≤ G.maxVolume r*G.maxVolume s := by
  obtain ⟨o,ho⟩ := G.exists_maxVolume hq (r+s)
  rw [ho]
  have hfin := G.vertexBall_finite hl o r
  have hu := hfin.biUnion fun v _ => G.vertexBall_finite hl v s
  calc
    _ ≤ (⋃ v∈G.vertexBall o r, G.vertexBall v s).ncard :=
      Set.ncard_le_ncard (G.vertexBall_add_cover o r s) hu
    _ ≤ ∑ v∈hfin.toFinset, (G.vertexBall v s).ncard := by
      simpa only [Set.Finite.coe_toFinset] using ncard_biUnion_le_sum hfin.toFinset
        (fun v => G.vertexBall v s) (fun v _ => G.vertexBall_finite hl v s)
    _ ≤ ∑ _v∈hfin.toFinset, G.maxVolume s := Finset.sum_le_sum fun v _ => G.volume_le_maxVolume hq v s
    _ = (G.vertexBall o r).ncard*G.maxVolume s := by
      simp only [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hfin,Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _ (G.volume_le_maxVolume hq o r)

lemma maxVolume_pos [Nonempty V] (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (n : ℕ) :
    0<G.maxVolume n := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact (G.vertexBall_ncard_pos hl v n).trans_le (G.volume_le_maxVolume hq v n)

lemma log_maxVolume_subadditive [Nonempty V] (hl : G.LocallyFinite) (hq : G.QuasiTransitive) :
    Subadditive (fun n => Real.log (G.maxVolume n : ℝ)) := by
  intro r s
  have hr : (0:ℝ)<G.maxVolume r := Nat.cast_pos.mpr (G.maxVolume_pos hl hq r)
  have hs : (0:ℝ)<G.maxVolume s := Nat.cast_pos.mpr (G.maxVolume_pos hl hq s)
  have hrs : (0:ℝ)<G.maxVolume (r+s) := Nat.cast_pos.mpr (G.maxVolume_pos hl hq _)
  calc
    _ ≤ Real.log ((G.maxVolume r : ℝ)*G.maxVolume s) := Real.log_le_log hrs (by
      exact_mod_cast G.maxVolume_submultiplicative hl hq r s)
    _ = _ := Real.log_mul hr.ne' hs.ne'

lemma uniform_subexponential_of_log_limit [Nonempty V] (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive)
    (hlim : Tendsto (fun n => Real.log (G.maxVolume n : ℝ)/(n:ℝ)) atTop (𝓝 0)) :
    G.SubexponentialGrowth := by
  intro o ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max N 1,?_⟩
  intro n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  calc
    _ ≤ Real.log (G.maxVolume n : ℝ) := Real.log_le_log
      (Nat.cast_pos.mpr (G.vertexBall_ncard_pos hl o n)) (by exact_mod_cast G.volume_le_maxVolume hq o n)
    _ ≤ ε*n := (div_lt_iff₀ hn0).mp (hN n (by omega)) |>.le

theorem growth_alternative [Nonempty V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) :
    G.SubexponentialGrowth ∨ ∃ a : ℝ, 0<a ∧ ∃ N : ℕ, ∀ n≥N, ∀ v : V,
      a*n ≤ Real.log ((G.vertexBall v n).ncard : ℝ) := by
  let u := fun n => Real.log (G.maxVolume n : ℝ)
  have hu : Subadditive u := G.log_maxVolume_subadditive hl hq
  have hnon : ∀ n, 0≤u n := fun n => Real.log_nonneg (by exact_mod_cast G.maxVolume_pos hl hq n)
  have hb : BddBelow (Set.range fun n => u n/(n:ℝ)) := ⟨0,by
    rintro x ⟨n,rfl⟩
    exact div_nonneg (hnon n) (Nat.cast_nonneg _)⟩
  have hlim := hu.tendsto_lim hb
  have hlimnon : 0≤hu.lim := ge_of_tendsto hlim (Eventually.of_forall fun n => div_nonneg (hnon n) (Nat.cast_nonneg _))
  by_cases hz : hu.lim=0
  · exact Or.inl (G.uniform_subexponential_of_log_limit hl hq (hz ▸ hlim))
  · have hpos : 0<hu.lim := lt_of_le_of_ne hlimnon (Ne.symm hz)
    obtain ⟨C,hC⟩ := G.uniform_orbit_density_radius hc hq
    refine Or.inr ⟨hu.lim/2,half_pos hpos,2*C+1,?_⟩
    intro n hn v
    have hnC : C<n := by omega
    obtain ⟨o,ho⟩ := G.exists_maxVolume hq (n-C)
    obtain ⟨φ,hφ⟩ := hC o v
    have hsub : G.vertexBall (φ.vertex o) (n-C) ⊆ G.vertexBall v n := by
      have hh := G.vertexBall_add hφ (n-C)
      simpa only [Nat.add_sub_of_le hnC.le] using hh
    have hcard := Set.ncard_le_ncard hsub (G.vertexBall_finite hl v n)
    rw [Aut.vertexBall_ncard G φ,← ho] at hcard
    have hm : (0:ℝ)<(n-C : ℕ) := by exact_mod_cast (show 0<n-C by omega)
    have hh := (le_div_iff₀ hm).mp (hu.lim_le_div hb (by omega : n-C≠0))
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (G.maxVolume_pos hl hq (n-C)))
      (Nat.cast_le.mpr hcard)
    change hu.lim*(n-C : ℕ) ≤ u (n-C) at hh
    have he : ((n-C : ℕ):ℝ)=(n:ℝ)-C := Nat.cast_sub hnC.le
    rw [he] at hh
    change u (n-C) ≤ _ at hlog
    have hnc : 2*(C:ℝ)+1≤n := by exact_mod_cast hn
    nlinarith

theorem superpolynomial_or_polynomial_scales :
    G.SuperpolynomialGrowth ∨ ∃ d : ℕ, ∀ R : ℕ, ∃ n≥R, ∃ v : V,
      (G.vertexBall v n).ncard ≤ n^d := by
  by_cases h : G.SuperpolynomialGrowth
  · exact Or.inl h
  · unfold SuperpolynomialGrowth at h
    push Not at h
    obtain ⟨d,hd⟩ := h
    exact Or.inr ⟨d,fun R => by
      obtain ⟨n,hn,v,hv⟩ := hd R
      exact ⟨n,hn,v,hv.le⟩⟩

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_BallCutGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma ballCut_endpoints (o : V) (n : ℕ) {e : E} (he : e ∈ G.ballCut o n) :
    ∃ x y, G.ends e = s(x,y) ∧ x ∈ G.vertexBall o (n+1) \ G.vertexBall o n ∧
      y ∈ G.vertexBall o n := by
  obtain ⟨x,y,he,hx,hy⟩ := he
  have hne : y ≠ x := by rintro rfl; exact hx hy
  have hadj : G.fullGraph.Adj y x :=
    (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_univ e,he.trans (Sym2.eq_swap)⟩,hne⟩
  exact ⟨x,y,he,⟨G.vertexBall_step hy hadj,hx⟩,hy⟩

lemma ballCut_subset_incident_sphere (o : V) (n : ℕ) :
    G.ballCut o n ⊆ G.incidentEdges (G.vertexBall o (n+1) \ G.vertexBall o n) := by
  intro e he
  obtain ⟨x,y,he,hx,_⟩ := G.ballCut_endpoints o n he
  exact ⟨x,hx,by simp [he]⟩

lemma ballCut_finite (hl : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.ballCut o n).Finite :=
  (G.finite_incident hl ((G.vertexBall_finite hl o (n+1)).sdiff)).subset
    (G.ballCut_subset_incident_sphere o n)

lemma ballCut_endpoints_mem (o : V) (n : ℕ) {e : E} (he : e ∈ G.ballCut o n)
    {x : V} (hx : x ∈ G.ends e) : x ∈ G.vertexBall o (n+1) := by
  obtain ⟨a,b,he,ha,hb⟩ := G.ballCut_endpoints o n he
  rw [he] at hx
  rcases Sym2.mem_iff.mp hx with rfl|rfl
  · exact ha.1
  · exact G.vertexBall_mono o (Nat.le_succ n) hb

lemma ballCut_pairwise_disjoint (o : V) : Pairwise (fun n m =>
    Disjoint (G.ballCut o n) (G.ballCut o m)) := by
  suffices h : ∀ n m : ℕ, n < m → Disjoint (G.ballCut o n) (G.ballCut o m) by
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with hlt|hlt
    · exact h n m hlt
    · exact (h m n hlt).symm
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro e hen hem
  obtain ⟨x,y,he,hx,hy⟩ := hem
  have hmem : x ∈ G.ends e := by simp [he]
  exact hx (G.vertexBall_mono o (Nat.succ_le_iff.mpr hnm)
    (G.ballCut_endpoints_mem o n hen hmem))

lemma ballCut_card_le (hl : G.LocallyFinite) (o : V) (n D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) :
    (G.ballCut o n).ncard ≤
      (G.vertexBall o (n+1) \ G.vertexBall o n).ncard * D := by
  exact (Set.ncard_le_ncard (G.ballCut_subset_incident_sphere o n)
    (G.finite_incident hl ((G.vertexBall_finite hl o (n+1)).sdiff))).trans
      (G.incident_ncard_le _ ((G.vertexBall_finite hl o (n+1)).sdiff) D (fun v _ => hD v))

lemma cluster_subset_ball_of_closed_ballCut (o : V) (n : ℕ) (ω : Set E)
    (hc : Disjoint (G.ballCut o n) ω) {v : V} (hv : v ∈ G.vertexBall o n) :
    G.cluster ω v ⊆ G.vertexBall o n := by
  intro x hx
  by_contra hnot
  exact G.not_reachable_of_cut_closed (G.vertexBall o n) ω
    (fun e he => Set.disjoint_left.mp hc he) hnot hv hx.symm

lemma frequently_small_increments_of_linear_scales (f : ℕ → ℕ) (C : ℕ)
    (hf : ∀ R : ℕ, ∃ n≥R, f n ≤ C*n) :
    ∃ᶠ n in atTop, f (n+1)-f n ≤ C := by
  by_contra h
  rw [not_frequently] at h
  obtain ⟨N,hN⟩ := eventually_atTop.mp h
  have hg (k : ℕ) : (C+1)*k ≤ f (N+k) := by
    induction k with
    | zero => omega
    | succ k ih =>
      have hh := hN (N+k) (by omega)
      have he : N+(k+1)=N+k+1 := by omega
      rw [he]
      have hinc : f (N+k)+C+1 ≤ f (N+k+1) := by omega
      nlinarith
  obtain ⟨n,hn,hfn⟩ := hf ((C+1)*N+1)
  have hNn : N ≤ n := by nlinarith
  have hh := hg (n-N)
  rw [Nat.add_sub_cancel' hNn] at hh
  have he := Nat.sub_add_cancel hNn
  nlinarith

lemma frequently_small_spheres_of_linear_scales (hl : G.LocallyFinite)
    (o : V) (C : ℕ) (hf : ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ C*n) :
    ∃ᶠ n in atTop, (G.vertexBall o (n+1) \ G.vertexBall o n).ncard ≤ C := by
  have hh := frequently_small_increments_of_linear_scales (fun n => (G.vertexBall o n).ncard) C hf
  apply hh.mono
  intro n hn
  rwa [Set.ncard_sdiff (G.vertexBall_mono o (Nat.le_succ n))
    (G.vertexBall_finite hl o n)]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SparseLinearCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem sparse_linear_percolates_null (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ C*n)
    (p : unitInterval) (hp : (p:ℝ)<1) : G.law p G.percolates=0 := by
  obtain ⟨r,hr,hrsmall⟩ := Filter.extraction_of_frequently_atTop
    (G.frequently_small_spheres_of_linear_scales hl o C hlin)
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hq
  have hcuts := BernoulliProduct.frequently_closedBlock_ae_of_card_le p hp
    (fun n => G.ballCut o (r n)) (fun n => G.ballCut_finite hl o (r n))
    (fun n m hnm => G.ballCut_pairwise_disjoint o (hr.injective.ne hnm)) (C*D)
    (fun n => (G.ballCut_card_le hl o (r n) D hD).trans
      (Nat.mul_le_mul_right D (hrsmall n)))
  rw [BernoulliProduct.law_const] at hcuts
  have hno : ∀ᵐ ω ∂G.law p, ω ∉ G.percolates := by
    filter_upwards [hcuts] with ω hω
    rintro ⟨v,hv⟩
    obtain ⟨N,hN⟩ := G.reachable_mem_vertexBall (hc o v)
    obtain ⟨n,hn,hncut⟩ := Filter.frequently_atTop.mp hω N
    have hNrad : N ≤ r n := hn.trans (hr.id_le n)
    exact hv ((G.vertexBall_finite hl o (r n)).subset
      (G.cluster_subset_ball_of_closed_ballCut o (r n) ω hncut
        (G.vertexBall_mono o hNrad hN)))
  rw [ae_iff] at hno
  simpa only [not_not,Set.ofPred_mem_eq] using hno

theorem sparse_linear_critical_one (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ C*n) :
    G.criticalProbability=1 := by
  apply le_antisymm le_top
  apply le_sInf
  intro p hp
  by_contra h
  have hlt : (p:ℝ)<1 := lt_of_not_ge h
  exact (ne_of_gt hp) (G.sparse_linear_percolates_null hc hl hq o C hlin p hlt)

lemma fixed_root_linear_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ C*n) :
    ∀ R : ℕ, ∃ n≥R, (G.vertexBall o n).ncard ≤ (2*C)*n := by
  obtain ⟨K,hK⟩ := G.orbit_density_radius hc hq o
  intro R
  obtain ⟨n,hn,v,hv⟩ := hlin (R+2*K)
  obtain ⟨φ,hφ⟩ := hK v
  have hKn : K≤n := by omega
  have hsub : G.vertexBall (φ.vertex o) (n-K) ⊆ G.vertexBall v n := by
    simpa only [Nat.add_sub_of_le hKn] using G.vertexBall_add hφ (n-K)
  have hcard := Set.ncard_le_ncard hsub (G.vertexBall_finite hl v n)
  rw [Aut.vertexBall_ncard G φ] at hcard
  refine ⟨n-K,by omega,hcard.trans (hv.trans ?_)⟩
  have hbound : n≤2*(n-K) := by omega
  calc
    C*n ≤ C*(2*(n-K)) := Nat.mul_le_mul_left C hbound
    _ = (2*C)*(n-K) := by ring

theorem moving_sparse_linear_critical_one (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (C : ℕ)
    (hlin : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ C*n) :
    G.criticalProbability=1 := by
  obtain ⟨o⟩ := hc.nonempty
  exact G.sparse_linear_critical_one hc hl hq o (2*C)
    (G.fixed_root_linear_scales hc hl hq o C hlin)

end CriticalPercolation.BondGraph
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SuperpolynomialMain
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

theorem no_percolation_at_criticality_superpolynomial
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hpc : G.criticalProbability<1)
    (hsub : G.SubexponentialGrowth) (hsuper : G.SuperpolynomialGrowth) :
    G.law G.criticalProbability G.percolates = 0 := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  let := hconnected.nonempty
  by_contra hbad
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability_bs hconnected hlocal hquasi
    G.criticalProbability (pos_iff_ne_zero.mpr hbad)
  have hθ1 : θ≤1 := (hroot (Classical.arbitrary V)).trans measureReal_le_one
  have hpcpos := G.criticalProbability_pos hconnected hlocal hquasi
  let ε : ℝ := min ((G.criticalProbability:ℝ)/2) (1-(G.criticalProbability:ℝ))
  have hε : 0<ε := lt_min (by positivity) (by exact sub_pos.mpr hpc)
  have hforbid := G.eventually_no_superpolynomial_band_bs hconnected hlocal hquasi hsub hsuper θ hθ hθ1 ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp hforbid
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ L : ℕ in atTop, 4/(3*(Real.log L)^2)<θ/4 := by
    have hh := (tendsto_const_nhds (x := (4:ℝ))).div_atTop
      (((tendsto_pow_atTop (α := ℝ) (n := 2) (by norm_num)).comp hl).const_mul_atTop (by norm_num : (0:ℝ)<3))
    exact hh.eventually (gt_mem_nhds (by positivity : (0:ℝ)<θ/4))
  obtain ⟨L,hLN,hL,hlarge⟩ := ((eventually_ge_atTop N).and ((eventually_ge_atTop 2).and hlarge)).exists
  obtain ⟨p,hphalf,hppc,z,s,hs,hband,htail⟩ := G.exists_subcritical_clusterBand
    hconnected hlocal hquasi hpcpos θ hθ hroot L hL hlarge
  apply hN s (hLN.trans hs) p z
  · exact (min_le_left _ _).trans hphalf
  · exact (min_le_right _ _).trans (by exact sub_le_sub_left (show (p:ℝ)≤G.criticalProbability from hppc.le) 1)
  · exact hband
  · exact htail

end CriticalPercolation.BondGraph
end
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

lemma infiniteEvent_eq_light_union_heavy (o v : V) :
    G.infiniteEvent v = G.lightInfiniteEvent o v ∪ G.heavyClusterEvent o v := by
  ext ω
  change (G.cluster ω v).Infinite ↔
    ((G.cluster ω v).Infinite ∧ _) ∨ _
  constructor
  · intro h
    rcases lt_or_eq_of_le (le_top : G.modularMass o (G.cluster ω v) ≤ ∞) with hl|hh
    · exact Or.inl ⟨h,hl⟩
    · exact Or.inr hh
  · rintro (⟨h,_⟩|h)
    · exact h
    · exact G.infinite_of_modularMass_top o h

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_MainResidualBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma atMostOneInfinite_ae_of_no_light_or_two_heavy
    [Countable V] [Countable E] (p : unitInterval) (o : V)
    (hl : ∀ v, G.law p (G.lightInfiniteEvent o v) = 0)
    (hh : ∀ x y, G.law p (G.twoHeavyDistinctEvent o x y) = 0) :
    ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hla : ∀ᵐ ω ∂G.law p, ∀ v, ω ∉ G.lightInfiniteEvent o v := by
    apply ae_all_iff.mpr
    intro v
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hl v
  have hha : ∀ᵐ ω ∂G.law p, ∀ x y, ω ∉ G.twoHeavyDistinctEvent o x y := by
    apply ae_all_iff.mpr
    intro x
    apply ae_all_iff.mpr
    intro y
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hh x y
  filter_upwards [hla,hha] with ω hωl hωh
  intro x y hx hy
  have hheavy (v : V) (hv : (G.cluster ω v).Infinite) :
      ω ∈ G.heavyClusterEvent o v := by
    have hm : ω ∈ G.infiniteEvent v := hv
    rw [G.infiniteEvent_eq_light_union_heavy o v] at hm
    exact hm.resolve_left (hωl v)
  by_contra hxy
  exact hωh x y ⟨⟨hheavy x hx,hheavy y hy⟩,hxy⟩

lemma positive_light_or_two_heavy_of_exponential_critical_percolation
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (hper : G.law G.criticalProbability G.percolates ≠ 0) :
    (∃ v, 0 < G.law G.criticalProbability (G.lightInfiniteEvent o v)) ∨
      ∃ x y, 0 < G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra h
  push Not at h
  have hln : ∀ v, G.law G.criticalProbability (G.lightInfiniteEvent o v) = 0 :=
    fun v => le_antisymm (h.1 v) bot_le
  have hhn : ∀ x y, G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y) = 0 :=
    fun x y => le_antisymm (h.2 x y) bot_le
  exact hper (Sharpness.critical_null_of_unique_bs G hc hl hq o γ hγ N hgrowth
    (G.atMostOneInfinite_ae_of_no_light_or_two_heavy G.criticalProbability o hln hhn))

theorem main_residual_boundary [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability < 1) (o : V)
    (hper : G.law G.criticalProbability G.percolates ≠ 0) :
    (¬ G.CombinatoriallyUnimodular ∧
      ((∃ v, 0 < G.law G.criticalProbability (G.lightInfiniteEvent o v)) ∨
        ∃ x y, 0 < G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y))) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2 ≤ d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ n^d) := by
  rcases G.growth_alternative hc hl hq with hg | ⟨γ,hγ,N,hgrowth⟩
  · rcases G.superpolynomial_or_polynomial_scales with hsp | ⟨d,hd⟩
    · exact False.elim (hper (G.no_percolation_at_criticality_superpolynomial hc hl hq hpc hg hsp))
    · right
      refine ⟨hg,d,?_,hd⟩
      by_contra hsmall
      have hd1 : d ≤ 1 := by omega
      have hlin : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard ≤ 1*n := by
        intro R
        obtain ⟨n,hn,v,hv⟩ := hd (max R 1)
        refine ⟨n,le_trans (le_max_left _ _) hn,v,hv.trans ?_⟩
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd1 with rfl|rfl
        · simp only [pow_zero,one_mul]
          exact le_trans (le_max_right _ _) hn
        · simp
      have he := G.moving_sparse_linear_critical_one hc hl hq 1 hlin
      rw [he] at hpc
      exact (lt_irrefl _ hpc)
  · left
    refine ⟨?_,G.positive_light_or_two_heavy_of_exponential_critical_percolation
      hc hl hq o γ hγ N hgrowth hper⟩
    intro hu
    exact hper (CombinatoriallyUnimodular.exponential_critical_null_bs G hu hc hl hq hpc
      o γ hγ N hgrowth)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_MainLightBoundary
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

lemma critical_twoHeavyDistinct_null (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hp1 : G.criticalProbability<1) (o x y : V) :
    G.law G.criticalProbability (G.twoHeavyDistinctEvent o x y)=0 := by
  have h := G.atMostOneHeavy_critical_ae_bs hc hl hq hp1 o
  have hh : ∀ᵐ ω ∂G.law G.criticalProbability, ω∉G.twoHeavyDistinctEvent o x y := by
    filter_upwards [h] with ω hω ⟨⟨hx,hy⟩,hnot⟩
    exact hnot (hω x y hx hy)
  rw [ae_iff] at hh
  simpa only [not_not,Set.ofPred_mem_eq] using hh

theorem main_light_or_sparse_polynomial_boundary_bs_oai [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o : V)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    (¬G.CombinatoriallyUnimodular ∧
      ∃ v, 0<G.law G.criticalProbability (G.lightInfiniteEvent o v)) ∨
    (G.SubexponentialGrowth ∧ ∃ d : ℕ, 2≤d ∧
      ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) := by
  rcases G.main_residual_boundary hc hl hq hpc o hper with ⟨hu,hlight|hheavy⟩|hsparse
  · exact Or.inl ⟨hu,hlight⟩
  · obtain ⟨x,y,hxy⟩ := hheavy
    rw [G.critical_twoHeavyDistinct_null hc hl hq hpc o x y] at hxy
    exact False.elim ((lt_irrefl _) hxy)
  · exact Or.inr hsparse

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs_oai.{u_1, u_2}
