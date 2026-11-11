-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:26:41.929201+00:00
-- url     : https://prove2.me/submissions/d938bc5f-b7c1-42dc-adb9-894dd29f51bf

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_criticalProbability_pos
import Theorems.Thm_OAI_CriticalPercolation_FiniteClusters_restrict_cluster
import Theorems.Thm_OAI_CriticalPercolation_IncidenceSearch_compile_terminal
import Theorems.Thm_OAI_CriticalPercolation_SearchTree_normalized_centered_bound

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact Measurable.of_eval fun vertex => G.measurable_reachable v vertex

lemma measurable_infinite_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.measurable_cluster v)).eq_const ⊤

lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp

lemma law_percolates_eq_zero_of_lt_critical {p : unitInterval}
    (hp : p < G.criticalProbability) : G.law p G.percolates = 0 := by
  by_contra h
  exact (not_le_of_gt hp) (G.criticalProbability_le_of_pos (pos_iff_ne_zero.mpr h))

lemma cluster_subset_endpoints (ω : Set E) (v : V) :
    G.cluster ω v ⊆ insert v {w | ∃ e ∈ ω, w ∈ G.ends e} := by
  intro w hw
  have h := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp hw
  clear hw
  induction h with
  | refl => exact Set.mem_insert _ _
  | @tail u w h huw _ =>
      obtain ⟨⟨e, he, heq⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      exact Or.inr ⟨e, he, by simp [heq]⟩

lemma finite_cluster_of_finite_bonds {ω : Set E} (hω : ω.Finite) (v : V) :
    (G.cluster ω v).Finite := by
  classical
  have hf : {w | ∃ e ∈ ω, w ∈ G.ends e}.Finite := by
    have heq : {w | ∃ e ∈ ω, w ∈ G.ends e} =
        ⋃ e ∈ ω, (↑(G.ends e).toFinset : Set V) := by
      ext w
      simp
    rw [heq]
    exact hω.biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  exact (hf.insert v).subset (G.cluster_subset_endpoints ω v)

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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma expect_sub (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω - g ω) = expect w f - expect w g := by
  classical
  simp [expect, mul_sub, Finset.sum_sub_distrib]

lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)

omit [Fintype A] in
lemma density_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P] (ω : E → A) :
    density w ω =
      density (fun e : {e // P e} => w e) (fun e => ω e) *
      density (fun e : {e // ¬ P e} => w e) (fun e => ω e) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun e => w e (ω e))).symm

lemma expect_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : (E → A) → ℝ) :
    expect w f =
      expect (fun e : {e // P e} => w e) (fun a =>
        expect (fun e : {e // ¬ P e} => w e) (fun b =>
          f ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b)))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  unfold expect
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have h₁ : (fun i : {e // P e} => e.symm (a, b) i) = a :=
    congrArg Prod.fst (e.apply_symm_apply (a, b))
  have h₂ : (fun i : {e // ¬ P e} => e.symm (a, b) i) = b :=
    congrArg Prod.snd (e.apply_symm_apply (a, b))
  rw [density_split w P, h₁, h₂, mul_assoc]

lemma expect_factor (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : ({e // P e} → A) → ℝ) (g : ({e // ¬ P e} → A) → ℝ) :
    expect w (fun ω => f (fun e => ω e) * g (fun e => ω e)) =
      expect (fun e : {e // P e} => w e) f *
        expect (fun e : {e // ¬ P e} => w e) g := by
  classical
  rw [expect_split w P]
  have h₁ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = a := by
    intro a b
    exact congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  have h₂ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // ¬ P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = b := by
    intro a b
    exact congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  simp_rw [h₁, h₂]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  ring

lemma expect_indep (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (S : Set E) {f g : (E → A) → ℝ}
    (hf : DependsOn f S) (hg : DependsOn g Sᶜ) :
    expect w (fun ω => f ω * g ω) = expect w f * expect w g := by
  classical
  obtain ⟨f', rfl⟩ := dependsOn_iff_exists_comp.mp hf
  obtain ⟨g', rfl⟩ := dependsOn_iff_exists_comp.mp hg
  have hw₁ : ∀ e : S, ∑ a, w e a = 1 := fun e => hw e
  have hw₂ : ∀ e : {e // e ∉ S}, ∑ a, w e a = 1 := fun e => hw e
  have hf' : expect w (fun ω => f' (fun e => ω e)) =
      expect (fun e : S => w e) f' := by
    have h := expect_factor w (fun e => e ∈ S) f' (fun _ => 1)
    simpa only [mul_one, expect_const _ hw₂] using h
  have hg' : expect w (fun ω => g' (fun e => ω e)) =
      expect (fun e : {e // e ∉ S} => w e) g' := by
    have h := expect_factor w (fun e => e ∈ S) (fun _ => 1) g'
    simp only [one_mul, expect_const _ hw₁] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  change expect w (fun ω => f' (fun e => ω e) * g' (fun e => ω e)) =
    expect w (fun ω => f' (fun e => ω e)) * expect w (fun ω => g' (fun e => ω e))
  rw [hf', hg']
  convert expect_factor w (fun e => e ∈ S) f' g' using 1
  all_goals try with_reducible_and_instances rfl
  rfl

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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ComponentSelf
attribute [-simp] _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Distribution
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ContinuousExpectWeights
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩

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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteOpenWitness
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MeasurableSetRestrict
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterTail
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma infiniteEvent_subset_clusterTail (o : V) (n : ℕ) :
    G.infiniteEvent o ⊆ G.clusterTail o n := by
  intro ω hω
  obtain ⟨K, hKω, hK, hn⟩ := hω.exists_subset_ncard_eq n
  exact ⟨K, hK, hKω, hn.ge⟩

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

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphBalls
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Link
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteProductPin
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Potential
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Delta
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_eval_indicator (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) : expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  classical
  have ht (ω : E → A) : density w ω * (if ω e = b then 1 else 0) =
      ∏ j, w j (ω j) * (if j = e then if ω j = b then 1 else 0 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [density]
  simp only [expect, ht]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) : (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
      if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp
end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_coordinate_mask (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_pin_eq_force (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (b : Prop) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect w (fun ω => f (Function.update ω e b)) := by
  apply mul_left_cancel₀ hb
  exact (expect_mask_pin w e b f).symm.trans (expect_coordinate_mask w hw e b f)

lemma expect_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect (pin w e a) (fun ω => f (Function.update ω e b)) := by
  rw [expect_pin_eq_force w hw e b hb,expect_pin_eq_force w hw e a ha]
  simp only [Function.update_idem]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OpenGraphInsert
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ExpectClosedFlip
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma expect_closed_flip (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : w e False = 1-p) (h1 : w e True = p) (f : Set E → ℝ) :
    expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      expect w (fun ω => if ω e then (1-p)*f ω else 0) := by
  have he0 : w e False ≠ 0 := by rw [h0]; linarith [hp.2]
  have he1 : w e True ≠ 0 := by rw [h1]; exact hp.1.ne'
  have he := expect_pin_transport w hw e False True he0 he1 f
  have hc : expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      w e False * expect (pin w e False) (fun ω => p*f (Function.update ω e True)) := by
    convert expect_prop_mask_pin w e False (fun ω => p*f (Function.update ω e True)) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext ω
    by_cases hb : ω e <;> simp [hb]
  have ho : expect w (fun ω => if ω e then (1-p)*f ω else 0) =
      w e True * expect (pin w e True) (fun ω => (1-p)*f ω) := by
    convert expect_prop_mask_pin w e True (fun ω => (1-p)*f ω) using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext ω
    by_cases hb : ω e <;> simp [hb]
  erw [hc,ho,expect_const_mul,expect_const_mul,h0,h1,he]
  ring

lemma expect_closed_flip_decidable [d : DecidableEq E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : w e False = 1-p) (h1 : w e True = p) (f : Set E → ℝ) :
    expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      expect w (fun ω => if ω e then (1-p)*f ω else 0) := by
  have hup (ω : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) ω e True =
        Function.update ω e True := by
    have hd : (fun a b => Classical.propDecidable (a=b)) = d := Subsingleton.elim _ _
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' ω e True) hd
  have h := expect_closed_flip w hw e hp h0 h1 f
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases hc : ω e
  · simp only [hc,not_true_eq_false,ite_false, if_false]
  · simp only [hc,not_false_eq_true,ite_true, if_true]
    exact congrArg (fun σ : Set E => p*f σ) (hup ω).symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
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

lemma HasFiniteOpenWitness.inter {A B : Set (Set E)}
    (hA : HasFiniteOpenWitness A) (hB : HasFiniteOpenWitness B)
    (hAm : IsUpperSet A) (hBm : IsUpperSet B) : HasFiniteOpenWitness (A ∩ B) := by
  rintro ω ⟨hωA, hωB⟩
  obtain ⟨s, hs, hsω, hsA⟩ := hA ω hωA
  obtain ⟨t, ht, htω, htB⟩ := hB ω hωB
  exact ⟨s ∪ t, hs.union ht, Set.union_subset hsω htω,
    hAm Set.subset_union_left hsA, hBm Set.subset_union_right htB⟩

end CriticalPercolation.BernoulliProduct
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteInterpolationMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_twoClusterEvent [Countable V] [Countable E] (u v : V) (s : ℕ) :
    MeasurableSet (G.twoClusterEvent u v s) := by
  exact ((G.measurable_reachable u v).setOf.compl.inter
    (G.measurableSet_clusterTail u s)).inter (G.measurableSet_clusterTail v s)

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_WitnessEvents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.reachable_map (φ : G.Aut) (ω : Set E) (u v : V) :
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex u) (φ.vertex v) ↔
      (G.openGraph ω).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)

lemma Aut.clusterTail_map (φ : G.Aut) (ω : Set E) (u : V) (s : ℕ) :
    φ.edge '' ω ∈ G.clusterTail (φ.vertex u) s ↔ ω ∈ G.clusterTail u s := by
  exact Set.ext_iff.mp (Aut.preimage_clusterTail G φ u s) ω

lemma twoClusterEvent_comm (u v : V) (s : ℕ) :
    G.twoClusterEvent u v s = G.twoClusterEvent v u s := by
  ext ω
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h,hu⟩,hv⟩
    exact ⟨⟨fun hc => h hc.symm,hv⟩,hu⟩
  · rintro ⟨⟨h,hv⟩,hu⟩
    exact ⟨⟨fun hc => h hc.symm,hu⟩,hv⟩

lemma twoClusterEvent_sym2 {u v x y : V} (h : s(u,v)=s(x,y)) (s : ℕ) :
    G.twoClusterEvent u v s = G.twoClusterEvent x y s := by
  rcases Sym2.eq_iff.mp h with h | h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · rcases h with ⟨rfl,rfl⟩; exact G.twoClusterEvent_comm _ _ _

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterDiscrepancy
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
lemma cluster_disjoint_of_not_reachable {ω : Set E} {u v : V}
    (h : ¬ (G.openGraph ω).Reachable u v) : Disjoint (G.cluster ω u) (G.cluster ω v) := by
  apply Set.disjoint_left.mpr
  intro z hu hv
  exact h (hu.trans hv.symm)

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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_CappedDiscrepancy
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

lemma capped_gap_nonneg {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    0 ≤ min a 1 + min b 1 - min (a+b) 1 := by
  rcases le_total a 1 with ha1|ha1 <;> rcases le_total b 1 with hb1|hb1
  · rw [min_eq_left ha1,min_eq_left hb1]
    exact sub_nonneg.mpr (min_le_left _ _)
  · rw [min_eq_left ha1,min_eq_right hb1]
    linarith [min_le_right (a+b) 1]
  · rw [min_eq_right ha1,min_eq_left hb1]
    linarith [min_le_right (a+b) 1]
  · rw [min_eq_right ha1,min_eq_right hb1]
    linarith [min_le_right (a+b) 1]

lemma cappedMass_nonneg (s m : ℕ) : 0 ≤ cappedMass s m := by
  unfold cappedMass
  positivity

lemma cappedMass_gap (s a b : ℕ) (hs : 0 < s) :
    (if s≤a ∧ s≤b then (1:ℝ) else 0) ≤
      cappedMass s a + cappedMass s b - cappedMass s (a+b) := by
  have hs' : 0<(s:ℝ) := Nat.cast_pos.mpr hs
  simp only [cappedMass,Nat.cast_add,add_div]
  split_ifs with h
  · have ha : 1 ≤ (a:ℝ)/s := (le_div_iff₀ hs').mpr (by simpa only [one_mul] using (Nat.cast_le.mpr h.1 : (s:ℝ)≤a))
    have hb : 1 ≤ (b:ℝ)/s := (le_div_iff₀ hs').mpr (by simpa only [one_mul] using (Nat.cast_le.mpr h.2 : (s:ℝ)≤b))
    rw [min_eq_right ha,min_eq_right hb]
    linarith [min_le_right ((a:ℝ)/s+(b:ℝ)/s) 1]
  · exact capped_gap_nonneg (by positivity) (by positivity)

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceSearch
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

end CriticalPercolation.IncidenceSearch
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceIdentity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
        simp only [hω,hω',decide_true,ite_true, if_true]
        dsimp only at hopen
        constructor
        · have hh := hopen.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum,ite_eq_left hω] at hopen
          linarith [hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,ite_false, if_false]
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryBand
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

lemma centeredSum_eq_zero_of_count (t : SearchTree E R) (ω : E → Prop)
    (h : t.queryCount ω = 0) (p : ℝ) : t.centeredSum p ω = 0 := by
  cases t with
  | done r => rfl
  | ask e l r => simp [queryCount] at h

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_InfiniteUniquenessGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma measurableSet_distinctInfiniteEvent [Countable V] [Countable E] (x y : V) :
    MeasurableSet (G.distinctInfiniteEvent x y) :=
  ((G.measurable_infinite_cluster x).and
    ((G.measurable_infinite_cluster y).and (G.measurable_reachable x y).not)).setOf

lemma distinctInfiniteEvent_subset_twoClusterEvent (x y : V) (s : ℕ) :
    G.distinctInfiniteEvent x y ⊆ G.twoClusterEvent x y s := by
  rintro ω ⟨hx,hy,hxy⟩
  exact ⟨⟨hxy,G.infiniteEvent_subset_clusterTail x s hx⟩,
    G.infiniteEvent_subset_clusterTail y s hy⟩

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

lemma distinctInfinite_force_adjacent_length (n : ℕ) :
    ∀ (ω : Set E) (x y : V), lengthReach G.fullGraph n x y →
      ω ∈ G.distinctInfiniteEvent x y →
      ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
        S ∪ ω ∈ G.distinctInfiniteEvent a b := by
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
      rwa [← G.cluster_eq_of_reachable hxuω]
    · obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huy
      have hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω x := by
        intro v hv
        rw [he,Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact hxuω
        · exact hxy
      have hc := G.cluster_insert_edge_unchanged ω e x hends
      have hnewx : (G.cluster (insert e ω) x).Infinite := hc ▸ hx
      have hay : (G.openGraph (insert e ω)).Adj u y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert e ω,he⟩,hne⟩
      have hnewu : (G.cluster (insert e ω) u).Infinite := by
        have hh := hy.mono (G.cluster_mono (Set.subset_insert e ω) y)
        rwa [← G.cluster_eq_of_reachable hay.reachable] at hh
      have hnot : ¬ (G.openGraph (insert e ω)).Reachable x u := by
        change u ∉ G.cluster (insert e ω) x
        rwa [hc]
      obtain ⟨S,hS,a,b,hab,hhab⟩ := ih (insert e ω) x u hxu ⟨hnewx,hnewu,hnot⟩
      refine ⟨insert e S,hS.insert e,a,b,hab,?_⟩
      simpa only [Set.insert_union,Set.union_insert] using hhab

lemma distinctInfinite_force_adjacent (hconnected : G.fullGraph.Connected)
    (ω : Set E) (x y : V) (h : ω ∈ G.distinctInfiniteEvent x y) :
    ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.fullGraph.Adj a b ∧
      S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  obtain ⟨n,hn⟩ := (reachable_iff_exists_lengthReach G.fullGraph x y).mp (hconnected x y)
  exact G.distinctInfinite_force_adjacent_length n ω x y hn h

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEventUpperSet
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma hitEvent_isUpperSet (o : V) (A : Set V) : IsUpperSet (G.hitEvent o A) :=
  fun _ _ h => G.hitEvent_mono_edges o A h

lemma hitEvent_hasFiniteOpenWitness (o : V) (A : Set V) :
    BernoulliProduct.HasFiniteOpenWitness (G.hitEvent o A) := by
  rintro ω ⟨v, hv, hvA⟩
  obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
  exact ⟨s, hs, hsω, v, hvs, hvA⟩

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ExhaustionEvents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*} [Countable E]

lemma tendsto_real_sdiff_finiteWitness (p : unitInterval) (A B : Set (Set E))
    (hAm : IsUpperSet A) (hBm : IsUpperSet B)
    (hA : HasFiniteOpenWitness A) (hB : HasFiniteOpenWitness B)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A \ B})
      atTop (𝓝 ((law (fun _ : E => p)).real (A \ B))) := by
  have hAB := hA.inter hB hAm hBm
  have hABm : IsUpperSet (A∩B) := fun _ _ h hh => ⟨hAm h hh.1,hBm h hh.2⟩
  have h1 := tendsto_real_finiteWitness p A hAm hA K
  have h2 := tendsto_real_finiteWitness p (A∩B) hABm hAB K
  have he (n : ℕ) : (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A \ B} =
      (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A} -
        (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A∩B} := by
    exact eq_sub_iff_add_eq.mpr (measureReal_sdiff_add_inter
      (measurableSet_restrict (K n) (K.finite n) B))
  have he' : (law (fun _ : E => p)).real (A \ B) =
      (law (fun _ : E => p)).real A - (law (fun _ : E => p)).real (A∩B) := by
    exact eq_sub_iff_add_eq.mpr (measureReal_sdiff_add_inter
      (measurableSet_finiteWitness B hBm hB))
  simp_rw [he,he']
  exact h1.sub h2

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

omit [Countable E] in
lemma twoClusterEvent_sdiff (u v : V) (s : ℕ) :
    G.twoClusterEvent u v s = (G.clusterTail u s ∩ G.clusterTail v s) \ G.hitEvent u {v} := by
  ext ω
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_sdiff,
    hitEvent,Set.inter_singleton_nonempty,cluster]
  tauto

lemma tendsto_real_twoCluster_restrict (p : unitInterval) (u v : V) (s : ℕ)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real {ω | K n ∩ ω ∈ G.twoClusterEvent u v s})
      atTop (𝓝 ((G.law p).real (G.twoClusterEvent u v s))) := by
  rw [G.twoClusterEvent_sdiff]
  simp only [law,← BernoulliProduct.law_const]
  apply BernoulliProduct.tendsto_real_sdiff_finiteWitness
  · exact fun _ _ h hh => ⟨G.clusterTail_isUpperSet u s h hh.1,
      G.clusterTail_isUpperSet v s h hh.2⟩
  · exact G.hitEvent_isUpperSet u {v}
  · exact (G.clusterTail_hasFiniteOpenWitness u s).inter
      (G.clusterTail_hasFiniteOpenWitness v s) (G.clusterTail_isUpperSet u s)
      (G.clusterTail_isUpperSet v s)
  · exact G.hitEvent_hasFiniteOpenWitness u {v}

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_TailProduct
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteEnergy
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
  simp only [bitWeight, ite_true, if_true] at hh
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_Weight
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule0

noncomputable section
open Set
open scoped BigOperators Classical

namespace CriticalPercolation.Sharpness
open FiniteProduct

variable {E A : Type*} [Fintype E]

lemma weight_sum (p : ℝ) : ∑ b, weight p b = 1 := by
  simp [weight]

lemma weight_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (b : Prop) :
    0 ≤ weight p b := by
  by_cases h : b <;> simp [weight, h, hp.1, hp.2]

lemma hasDerivAt_weight (p : ℝ) (b : Prop) :
    HasDerivAt (fun q => weight q b) (if b then 1 else -1) p := by
  by_cases hb : b
  · convert hasDerivAt_id' p using 1 <;> first | rfl | simp [weight, hb]
  · convert (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id' p) using 1 <;>
      first | rfl | (simp only [weight, ite_eq_right hb]; first | rfl | norm_num)

lemma hasDerivAt_density (p : ℝ) (ω : E → Prop) :
    HasDerivAt (fun q => density (fun _ : E => weight q) ω)
      (∑ e, (∏ j ∈ Finset.univ.erase e, weight p (ω j)) *
        (if ω e then 1 else -1)) p := by
  simpa only [density, smul_eq_mul] using
    HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun (e : E) _ => hasDerivAt_weight p (ω e))

lemma density_score {p : ℝ} (hp : p ∈ Ioo 0 1) (ω : E → Prop) (e : E) :
    (∏ j ∈ Finset.univ.erase e, weight p (ω j)) * (if ω e then 1 else -1) =
      density (fun _ : E => weight p) ω *
        (if ω e then p⁻¹ else -(1-p)⁻¹) := by
  unfold density
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hp1 : 1-p ≠ 0 := (sub_pos.mpr hp.2).ne'
  by_cases he : ω e <;> simp [weight, he, hp0, hp1]

lemma hasDerivAt_expect_score {p : ℝ} (hp : p ∈ Ioo 0 1) (f : (E → Prop) → ℝ) :
    HasDerivAt (fun q => expect (fun _ : E => weight q) f)
      (∑ e, expect (fun _ : E => weight p)
        (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω)) p := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (ω : E → Prop) _ => (hasDerivAt_density p ω).mul_const (f ω))
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  simp only [expect, Finset.sum_mul, density_score hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  apply Finset.sum_congr rfl
  intro e _
  ring

lemma expect_eval_indicator [Fintype A] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  have hi (ω : E → A) : (if ω e = b then (1:ℝ) else 0) =
      ∏ j, (if j = e then if ω j = b then 1 else 0 else 1) := by simp
  simp only [expect, hi, density, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) :
      (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
        if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp

lemma expect_coordinate_mask [Fintype A] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by
        rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact expect_eval_indicator w hw e b

lemma score_eq_difference {p : ℝ} (hp : p ∈ Ioo 0 1) (e : E) (f : (E → Prop) → ℝ) :
    expect (fun _ : E => weight p)
      (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω) =
    expect (fun _ : E => weight p) (fun ω => f (Function.update ω e True)) -
      expect (fun _ : E => weight p) (fun ω => f (Function.update ω e False)) := by
  have he : (fun ω => (if ω e then p⁻¹ else -(1-p)⁻¹) * f ω) =
      (fun ω => (if ω e = True then f ω else 0) * p⁻¹ -
        (if ω e = False then f ω else 0) * (1-p)⁻¹) := by
    funext ω
    by_cases h : ω e <;> simp [h, mul_comm]
  rw [he, expect_sub, expect_mul_const, expect_mul_const]
  have h1 : expect (fun _ : E => weight p)
      (fun ω => if ω e = True then f ω else 0) =
      p * expect (fun _ : E => weight p) (fun ω => f (Function.update ω e True)) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p) e True f using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  have h0 : expect (fun _ : E => weight p)
      (fun ω => if ω e = False then f ω else 0) =
      (1-p) * expect (fun _ : E => weight p) (fun ω => f (Function.update ω e False)) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p) e False f using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  rw [h1, h0]
  have hp0 := hp.1.ne'
  have hp1 := (sub_pos.mpr hp.2).ne'
  field_simp

theorem hasDerivAt_expect {p : ℝ} (hp : p ∈ Ioo 0 1) (f : (E → Prop) → ℝ) :
    HasDerivAt (fun q => expect (fun _ : E => weight q) f)
      (∑ e, expect (fun _ : E => weight p)
        (fun ω => f (Function.update ω e True) - f (Function.update ω e False))) p := by
  have hd := hasDerivAt_expect_score hp f
  simpa only [score_eq_difference hp, expect_sub] using hd

omit [Fintype E] in
lemma force_false_subset_true (ω : Set E) (e : E) :
    Set.Subset (Function.update ω e False) (Function.update ω e True) := by
  intro j hj
  change Function.update ω e True j
  change Function.update ω e False j at hj
  by_cases h : j=e
  · subst j; exact of_eq_true (Function.update_self e True ω)
  · erw [Function.update_of_ne h] at hj ⊢
    exact hj

omit [Fintype E] in
lemma indicator_difference (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (e : E) (ω : Set E) :
    (if F (Function.update ω e True) then (1:ℝ) else 0) -
        (if F (Function.update ω e False) then 1 else 0) =
      if pivotal F e ω then 1 else 0 := by
  have hm := hF _ _ (force_false_subset_true ω e)
  by_cases h1 : F (Function.update ω e True) <;>
    by_cases h0 : F (Function.update ω e False) <;> simp_all [pivotal]

theorem hasDerivAt_probability {p : ℝ} (hp : p ∈ Ioo 0 1)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    HasDerivAt (fun q => probability q F) (∑ e, probability p (pivotal F e)) p := by
  have hd := hasDerivAt_expect hp (fun ω => if F ω then (1:ℝ) else 0)
  convert hd using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  apply Finset.sum_congr rfl
  intro e _
  unfold probability
  congr 1
  funext ω
  exact (indicator_difference F hF e ω).symm

lemma probability_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    0 ≤ probability p F := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun _ => 0) (g := fun ω => if F ω then 1 else 0)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 0, probability] using h

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ContinuousProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule5
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*} [Fintype E]

lemma continuous_probability (F : Set E → Prop) :
    Continuous (fun p : ℝ => probability p F) := by
  unfold probability expect
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  exact continuous_iff_continuousAt.mpr (fun p => (hasDerivAt_density p ω).continuousAt)

lemma probability_monotoneOn (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) :
    MonotoneOn (fun p : ℝ => probability p F) (Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    (continuous_probability F).continuousOn
  · intro p hp
    rw [interior_Icc] at hp
    exact (hasDerivAt_probability hp F hF).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_probability hp F hF).deriv]
    exact Finset.sum_nonneg fun e _ => probability_nonneg ⟨hp.1.le,hp.2.le⟩ _

end CriticalPercolation.Sharpness
end
end CurrentModule5

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SharpnessPhi
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule6
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

variable {E V : Type*}

lemma probability_eq_real [Fintype E] (p : unitInterval) (F : Set E → Prop) :
    probability (p : ℝ) F = (BernoulliProduct.law (fun _ : E => p)).real {ω | F ω} := by
  rw [← integral_indicator_one (μ := BernoulliProduct.law (fun _ : E => p))
    (s := {ω | F ω}) (.of_discrete), BernoulliProduct.integral_law_eq_expect]
  rfl

variable (G : BondGraph V E)

lemma finite_probability_restrict (p : unitInterval) (K : Set E) (hK : K.Finite)
    (F : Set K → Prop) :
    letI := hK.fintype
    probability (p : ℝ) F = (G.law p).real {ω | F (Subtype.val ⁻¹' ω)} := by
  let := hK.fintype
  rw [probability_eq_real, ← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [measureReal_def, Measure.map_apply hmeas (.of_discrete)]
  rw [BernoulliProduct.law_const]
  rfl

end CriticalPercolation.Sharpness
end
end CurrentModule6

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ParameterLeftBounds
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

lemma real_finiteWitness_mono_parameter (A : Set (Set E)) (hA : IsUpperSet A)
    (hw : BernoulliProduct.HasFiniteOpenWitness A) {p q : unitInterval} (hpq : p ≤ q) :
    (G.law p).real A ≤ (G.law q).real A := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  have hfinite (n : ℕ) : (G.law p).real {ω | K n ∩ ω ∈ A} ≤
      (G.law q).real {ω | K n ∩ ω ∈ A} := by
    let := (K.finite n).fintype
    let F : Set (K n) → Prop := fun τ => Subtype.val '' τ ∈ A
    have hf : ∀ s t, s ⊆ t → F s → F t := fun _ _ h => hA (Set.image_mono h)
    have hh := Sharpness.probability_monotoneOn F hf p.property q.property hpq
    change Sharpness.probability (p:ℝ) F ≤ Sharpness.probability (q:ℝ) F at hh
    rw [Sharpness.finite_probability_restrict G p (K n) (K.finite n),
      Sharpness.finite_probability_restrict G q (K n) (K.finite n)] at hh
    have he (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set (K n)) = K n ∩ ω := by
      ext e
      simp
    simpa only [F,he] using hh
  have htp := BernoulliProduct.tendsto_real_finiteWitness p A hA hw K
  have htq := BernoulliProduct.tendsto_real_finiteWitness q A hA hw K
  simp only [BernoulliProduct.law_const] at htp htq
  exact le_of_tendsto_of_tendsto htp htq (Eventually.of_forall hfinite)

lemma sdiff_bound_of_subcritical (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : BernoulliProduct.HasFiniteOpenWitness A)
    (hwB : BernoulliProduct.HasFiniteOpenWitness B)
    (p : unitInterval) (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q : unitInterval, (p:ℝ)/2 ≤ q → q < p → (G.law q).real (A\B) ≤ C/(q:ℝ)) :
    (G.law p).real (A\B) ≤ 2*C/(p:ℝ) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hAp : (G.law p).real A - ε < (G.law p).real A := by linarith
  obtain ⟨q,hhalf,hqp,hqA⟩ := BernoulliProduct.exists_lower_parameter
    (I := Unit) (fun _ => A) (fun _ => hA) (fun _ => hwA) p hp
    (fun _ => (G.law p).real A - ε)
    (fun _ => by simpa only [BernoulliProduct.law_const,law] using hAp)
  have hq : (G.law p).real A - ε < (G.law q).real A := by
    simpa only [BernoulliProduct.law_const,law] using hqA ()
  have hABm : IsUpperSet (A∩B) := fun _ _ h hh => ⟨hA h hh.1,hB h hh.2⟩
  have hABw := hwA.inter hwB hA hB
  have hAB := G.real_finiteWitness_mono_parameter (A∩B) hABm hABw hqp.le
  have hmeas := BernoulliProduct.measurableSet_finiteWitness B hB hwB
  have hsumP := measureReal_sdiff_add_inter (μ := G.law p) (s := A) hmeas
  have hsumQ := measureReal_sdiff_add_inter (μ := G.law q) (s := A) hmeas
  have hp' : (0:ℝ) < p := hp
  have hq' : (0:ℝ) < q := lt_of_lt_of_le (by linarith : (0:ℝ)<(p:ℝ)/2) hhalf
  have hinv : C/(q:ℝ) ≤ 2*C/(p:ℝ) := by
    apply (div_le_div_iff₀ hq' hp').mpr
    nlinarith
  linarith [hb q hhalf hqp]

lemma twoCluster_bound_of_subcritical (u v : V) (s : ℕ)
    (p : unitInterval) (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q : unitInterval, (p:ℝ)/2 ≤ q → q < p →
      (G.law q).real (G.twoClusterEvent u v s) ≤ C/(q:ℝ)) :
    (G.law p).real (G.twoClusterEvent u v s) ≤ 2*C/(p:ℝ) := by
  rw [G.twoClusterEvent_sdiff] at hb ⊢
  exact G.sdiff_bound_of_subcritical (G.clusterTail u s ∩ G.clusterTail v s) (G.hitEvent u {v})
    (fun _ _ h hh => ⟨G.clusterTail_isUpperSet u s h hh.1,G.clusterTail_isUpperSet v s h hh.2⟩)
    (G.hitEvent_isUpperSet u {v})
    ((G.clusterTail_hasFiniteOpenWitness u s).inter (G.clusterTail_hasFiniteOpenWitness v s)
      (G.clusterTail_isUpperSet u s) (G.clusterTail_isUpperSet v s))
    (G.hitEvent_hasFiniteOpenWitness u {v}) p hp C hC hb

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LevelContactMeasurability
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassInfinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma size_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : size G ω u = size G ω v := by
  unfold size
  rw [G.cluster_eq_of_reachable h]

lemma mass_eq_of_reachable (s : ℕ) {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : mass G s ω u = mass G s ω v := by
  unfold mass
  rw [size_eq_of_reachable G h]

lemma mass_nonneg (s : ℕ) (ω : Set E) (v : V) : 0 ≤ mass G s ω v :=
  div_nonneg (cappedMass_nonneg _ _) (Nat.cast_nonneg _)

lemma cappedMass_le_one (s n : ℕ) : cappedMass s n ≤ 1 := min_le_right _ _

lemma mass_mul_size_le_one (s : ℕ) (ω : Set E) (v : V) :
    mass G s ω v * size G ω v ≤ 1 := by
  by_cases h : size G ω v = 0
  · simp [mass,h]
  · rw [mass,div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr h)]
    exact cappedMass_le_one _ _

lemma mass_eq_zero_of_infinite (s : ℕ) {ω : Set E} {v : V}
    (h : (G.cluster ω v).Infinite) : mass G s ω v = 0 := by
  simp [mass,size,h.ncard]

lemma coefficient_abs_le {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (ω : Set E) (e : E) :
    |coefficient p ω e| ≤ 1/p := by
  unfold coefficient
  split_ifs
  · rw [abs_div,abs_neg,abs_of_nonneg (sub_nonneg.mpr hp.2.le),abs_of_pos hp.1]
    exact div_le_div_of_nonneg_right (by linarith [hp.1]) hp.1.le
  · rw [abs_one]
    exact (le_div_iff₀ hp.1).mpr (by linarith [hp.2])

lemma rootAbsolute_nonneg (s : ℕ) (p : ℝ) (ω : Set E) (v : V) :
    0 ≤ rootAbsolute G s p ω v := mul_nonneg (mass_nonneg G s ω v) (abs_nonneg _)

lemma abs_rootDiscrepancy (s : ℕ) (p : ℝ) (ω : Set E) (v : V) :
    |rootDiscrepancy G s p ω v| = rootAbsolute G s p ω v := by
  rw [rootDiscrepancy,abs_mul,abs_of_nonneg (mass_nonneg G s ω v)]
  rfl

lemma rootAbsolute_bound (hl : G.LocallyFinite) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (s : ℕ) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) (ω : Set E) (v : V) :
    rootAbsolute G s p ω v ≤ D/p := by
  by_cases hC : (G.cluster ω v).Finite
  · have hI := G.finite_incident hl hC
    have hsum : |rootSum G p ω v| ≤ (G.incidentEdges (G.cluster ω v)).ncard / p := by
      rw [rootSum,tsum_eq_sum (s := hI.toFinset) (fun e he => by
        simp only [hI.mem_toFinset] at he
        simp only [he,ite_false, if_false])]
      calc
        _ ≤ ∑ e∈hI.toFinset, |if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e∈hI.toFinset, |coefficient p ω e| := by
          apply Finset.sum_congr rfl
          intro e he
          rw [ite_eq_left (hI.mem_toFinset.mp he)]
        _ ≤ ∑ _e∈hI.toFinset, 1/p := Finset.sum_le_sum (fun e _ => coefficient_abs_le hp ω e)
        _ = _ := by rw [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hI]; ring
    calc
      _ ≤ mass G s ω v * ((G.incidentEdges (G.cluster ω v)).ncard / p) :=
        mul_le_mul_of_nonneg_left hsum (mass_nonneg G s ω v)
      _ ≤ mass G s ω v * ((size G ω v : ℝ)*D/p) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (by exact_mod_cast G.incident_ncard_le _ hC D (fun w _ => hD w)) hp.1.le)
          (mass_nonneg G s ω v)
      _ = (mass G s ω v * size G ω v)*(D/p) := by ring
      _ ≤ 1*(D/p) := mul_le_mul_of_nonneg_right (mass_mul_size_le_one G s ω v) (div_nonneg (Nat.cast_nonneg _) hp.1.le)
      _ = _ := one_mul _
  · rw [rootAbsolute,mass_eq_zero_of_infinite G s hC,zero_mul]
    exact div_nonneg (Nat.cast_nonneg _) hp.1.le

lemma edgeMass_nonneg (s : ℕ) (ω : Set E) (e : E) : 0 ≤ edgeMass G s ω e := by
  unfold edgeMass
  split_ifs
  · simpa using cappedMass_nonneg s (size G ω (G.ends e).out.1)
  · exact add_nonneg (cappedMass_nonneg _ _) (cappedMass_nonneg _ _)

lemma edgeMass_le_two (s : ℕ) (ω : Set E) (e : E) : edgeMass G s ω e ≤ 2 := by
  unfold edgeMass
  have h1 := cappedMass_le_one s (size G ω (G.ends e).out.1)
  have h2 := cappedMass_le_one s (size G ω (G.ends e).out.2)
  split_ifs <;> linarith

lemma edgeDiscrepancy_abs_le (s : ℕ) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1)
    (ω : Set E) (e : E) : |edgeDiscrepancy G s p ω e| ≤ 2/p := by
  rw [edgeDiscrepancy,abs_mul,abs_of_nonneg (edgeMass_nonneg G s ω e)]
  calc
    _ ≤ (1/p)*2 := mul_le_mul (coefficient_abs_le hp ω e) (edgeMass_le_two G s ω e)
      (edgeMass_nonneg G s ω e) (div_nonneg zero_le_one hp.1.le)
    _ = _ := by ring

variable [Countable V] [Countable E]

lemma measurable_size (v : V) : Measurable (fun ω => size G ω v) :=
  measurable_ncard.comp (G.measurable_cluster v)

lemma measurable_mass (s : ℕ) (v : V) : Measurable (fun ω => mass G s ω v) := by
  exact ((measurable_of_countable (fun n : ℕ => cappedMass s n / (n:ℝ))).comp
    (measurable_size G v))

omit [Countable E] in
lemma measurable_coefficient (p : ℝ) (e : E) : Measurable (fun ω => coefficient p ω e) :=
  measurable_const.ite (measurable_set_mem e).setOf measurable_const

lemma measurable_incidentCluster (v : V) (e : E) :
    MeasurableSet {ω : Set E | e ∈ G.incidentEdges (G.cluster ω v)} := by
  apply (Measurable.exists (fun w => (G.measurable_reachable v w).and measurable_const)).setOf

lemma measurable_rootSum (p : ℝ) (v : V) : Measurable (fun ω => rootSum G p ω v) := by
  exact Measurable.tsum (fun e => (measurable_coefficient p e).ite
    (measurable_incidentCluster G v e) measurable_const)

lemma measurable_rootAbsolute (s : ℕ) (p : ℝ) (v : V) :
    Measurable (fun ω => rootAbsolute G s p ω v) :=
  (measurable_mass G s v).mul (measurable_rootSum G p v).abs

lemma measurable_edgeMass (s : ℕ) (e : E) : Measurable (fun ω => edgeMass G s ω e) := by
  have hm (v : V) := (measurable_of_countable (cappedMass s)).comp (measurable_size G v)
  exact (hm _).add (measurable_const.ite (G.measurable_reachable _ _).setOf (hm _))

lemma measurable_edgeDiscrepancy (s : ℕ) (p : ℝ) (e : E) :
    Measurable (fun ω => edgeDiscrepancy G s p ω e) :=
  (measurable_coefficient p e).mul (measurable_edgeMass G s e)

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassEndpointFinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.FiniteClusters
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma clusterTail_iff_size {ω : Set E} {v : V} (hC : (G.cluster ω v).Finite) (s : ℕ) :
    ω ∈ G.clusterTail v s ↔ s ≤ size G ω v := by
  constructor
  · rintro ⟨A,hA,hAC,hs⟩
    exact hs.trans (Set.ncard_le_ncard hAC hC)
  · intro hs
    exact ⟨G.cluster ω v,hC,Subset.rfl,hs⟩

lemma size_insert_disconnected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : ¬(G.openGraph ω).Reachable x y)
    (hx : (G.cluster ω x).Finite) (hy : (G.cluster ω y).Finite) :
    size G (insert e ω) x = size G ω x + size G ω y := by
  unfold size
  rw [G.cluster_insert_endpoint ω e x y he,
    Set.ncard_union_eq (G.cluster_disjoint_of_not_reachable hxy) hx hy]

lemma size_insert_connected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : (G.openGraph ω).Reachable x y) :
    size G (insert e ω) x = size G ω x := by
  unfold size
  rw [G.cluster_insert_endpoint ω e x y he,G.cluster_eq_of_reachable hxy,Set.union_self]

lemma edgeMass_gap (s : ℕ) (hs : 0 < s) (ω : Set E) (e : E)
    (hx : (G.cluster ω (G.ends e).out.1).Finite)
    (hy : (G.cluster ω (G.ends e).out.2).Finite) :
    (if ω ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s then (1:ℝ) else 0) ≤
      edgeMass G s ω e - edgeMass G s (insert e ω) e := by
  have he : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) := (G.ends e).out_eq.symm
  have hopen := LazyDFS.prop_openEdge_reachable G (insert e ω) (Set.mem_insert e ω) he
  unfold edgeMass
  rw [ite_eq_left hopen,add_zero]
  by_cases hc : (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2
  · rw [ite_eq_left hc,size_insert_connected G ω e _ _ he hc]
    simp [BondGraph.twoClusterEvent,hc]
  · rw [ite_eq_right hc,size_insert_disconnected G ω e _ _ he hc hx hy]
    have hh := cappedMass_gap s (size G ω (G.ends e).out.1) (size G ω (G.ends e).out.2) hs
    simpa only [BondGraph.twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
      clusterTail_iff_size G hx,clusterTail_iff_size G hy,hc,not_false_eq_true,and_true,true_and] using hh

variable [Fintype E]
lemma finite_expect_edgeDiscrepancy (s : ℕ) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    expect w (fun ω => edgeDiscrepancy G s p ω e) =
      expect w (fun ω => if ¬ω e then edgeMass G s ω e - edgeMass G s (insert e ω) e else 0) := by
  let : DecidableEq E := Classical.decEq E
  have hflip := expect_closed_flip_decidable w hw e hp h0 h1 (fun ω => edgeMass G s ω e / p)
  have hu (ω : Set E) : (Function.update ω e True : Set E) = insert e ω := by
    ext a
    change Function.update (fun a => ω a) e True a ↔ a=e ∨ a∈ω
    by_cases ha : a=e
    · subst a; simp [Function.update]
    · simp only [Function.update_of_ne ha,ha,false_or]; rfl
  have hleft : (fun ω : Set E => if ¬ω e then p*(edgeMass G s (Function.update ω e True) e / p) else 0) =
      (fun ω => if ¬ω e then edgeMass G s (insert e ω) e else 0) := by
    funext ω
    rw [hu]
    split_ifs <;> field_simp [hp.1.ne']
  erw [hleft] at hflip
  have heq (ω : Set E) : edgeDiscrepancy G s p ω e =
      (if ¬ω e then edgeMass G s ω e else 0) -
        (if ω e then (1-p)*(edgeMass G s ω e / p) else 0) := by
    unfold edgeDiscrepancy coefficient
    change (if ω e then -(1-p)/p else 1) * edgeMass G s ω e = _
    by_cases hb : ω e <;> simp only [hb,ite_true, if_true,ite_false, if_false,not_true_eq_false,not_false_eq_true,sub_zero,zero_sub,one_mul]
    ring
  have hfunc := funext heq
  erw [hfunc,expect_sub,← hflip,← expect_sub]
  congr 1
  funext ω
  by_cases hb : ω e <;> simp [hb]

lemma finite_endpoint_le_expect (s : ℕ) (hs : 0 < s) (p : ℝ) (hp : p ∈ Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    prob w (fun ω => ω ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) ≤
      expect w (fun ω => edgeDiscrepancy G s p ω e) := by
  rw [finite_expect_edgeDiscrepancy G s p hp w hw e h0 h1]
  apply expect_mono hn
  intro ω
  by_cases hb : ω e
  · have hconn := LazyDFS.prop_openEdge_reachable G ω hb (G.ends e).out_eq.symm
    have hno : ¬ (ω : Set E) ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s := by
      intro hh
      exact hh.1.1 hconn
    change (if (ω : Set E) ∈ G.twoClusterEvent _ _ s then (1:ℝ) else 0) ≤ _
    simp only [hno,ite_false, if_false,hb,not_true_eq_false,le_refl]
  · simp only [hb,not_false_eq_true,ite_true, if_true]
    exact edgeMass_gap G s hs ω e (G.finite_cluster_of_finite_bonds (Set.toFinite ω) _)
      (G.finite_cluster_of_finite_bonds (Set.toFinite ω) _)

lemma finite_endpoint_le_integral (s : ℕ) (hs : 0 < s) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (e : E) :
    (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) ≤
      ∫ ω, edgeDiscrepancy G s p ω e ∂G.law p := by
  have hh := finite_endpoint_le_expect G s hs p hp (fun _ => BernoulliProduct.bitWeight p)
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    e (by simp [BernoulliProduct.bitWeight]) (by simp [BernoulliProduct.bitWeight])
  rw [BondGraph.law,← BernoulliProduct.law_const,BernoulliProduct.integral_law_eq_expect]
  convert hh using 1
  · exact (Sharpness.probability_eq_real p
      (fun ω => ω ∈ G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)).symm
  · rfl

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassFinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.FiniteClusters
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma size_pos {ω : Set E} {v : V} (hC : (G.cluster ω v).Finite) :
    0 < size G ω v := (Set.ncard_pos hC).mpr ⟨v,SimpleGraph.Reachable.refl v⟩

lemma mass_eq_min (s : ℕ) (hs : 0 < s) (ω : Set E) (v : V)
    (hC : (G.cluster ω v).Finite) :
    mass G s ω v = min (1/(s:ℝ)) (1/(size G ω v : ℝ)) := by
  have hm : (0:ℝ) < size G ω v := Nat.cast_pos.mpr (size_pos G hC)
  have hs' : (0:ℝ) < s := Nat.cast_pos.mpr hs
  unfold mass cappedMass
  by_cases hms : (size G ω v : ℝ)/s ≤ 1
  · rw [min_eq_left hms,min_eq_left]
    · field_simp
    · apply (div_le_div_iff₀ hs' hm).mpr
      have hh := (div_le_one hs').mp hms
      simpa only [one_mul] using hh
  · have hh : (s:ℝ) ≤ size G ω v := (one_le_div hs').mp (le_of_lt (lt_of_not_ge hms))
    rw [min_eq_right (le_of_lt (lt_of_not_ge hms)),min_eq_right]
    apply (div_le_div_iff₀ hm hs').mpr
    simpa only [one_mul] using hh

lemma mass_le_normalized (s T D : ℕ) (hs : 0 < s) (hT : 0<T) (hD : 1≤D)
    (ω : Set E) (v : V) (hC : (G.cluster ω v).Finite) (hTD : T ≤ D*size G ω v) :
    mass G s ω v ≤ (D:ℝ)*min (1/(s:ℝ)) (1/(T:ℝ)) := by
  rw [mass_eq_min G s hs ω v hC,mul_min_of_nonneg _ _ (Nat.cast_nonneg D)]
  apply le_min
  · exact (min_le_left _ _).trans
      (le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.mpr hD))
  · apply (min_le_right _ _).trans
    rw [mul_one_div]
    apply (div_le_div_iff₀ (Nat.cast_pos.mpr (size_pos G hC)) (Nat.cast_pos.mpr hT)).mpr
    simpa only [one_mul,Nat.cast_mul] using (Nat.cast_le.mpr hTD : (T:ℝ)≤(D*size G ω v : ℕ))

variable [Fintype E]

lemma rootSum_eq_centered (p : ℝ) (hp : p≠0) (ω : Set E) (v : V) :
    rootSum G p ω v = -(IncidenceSearch.tree G v).centeredSum p ω / p := by
  rw [IncidenceSearch.tree_centered,rootSum,tsum_fintype,← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e∈G.incidentEdges (G.cluster ω v)
  · by_cases hω : e∈ω <;> simp [he,hω,hp,coefficient]
  · simp [he]

lemma finite_rootAbsolute_expect (p : ℝ) (hp : p ∈ Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p ∅) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (K : ℕ) (v : V) :
    expect w (fun ω => rootAbsolute G (4^K) p ω v) ≤ (D:ℝ)/p*(6/(2:ℝ)^K) := by
  let t := IncidenceSearch.tree G v
  have hwel (ω : Set E) : rootAbsolute G (4^K) p ω v ≤
      (D:ℝ)/p * (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := by
    rw [rootAbsolute,rootSum_eq_centered G p hp.1.ne' ω v,abs_div,abs_neg,abs_of_pos hp.1]
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p]
      simp
    · have hC := G.finite_cluster_of_finite_bonds (Set.toFinite ω) v
      have hTD : t.queryCount ω ≤ D*size G ω v := by
        rw [IncidenceSearch.tree_count,← Set.ncard_eq_toFinset_card']
        simpa only [size,mul_comm] using G.incident_ncard_le _ hC D (fun w _ => hD w)
      have hh := mass_le_normalized G (4^K) (t.queryCount ω) D
        (by positivity) (Nat.pos_of_ne_zero hT) hDpos ω v hC hTD
      have hh' : mass G (4^K) ω v ≤ (D:ℝ)*min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
      calc
        _ ≤ ((D:ℝ)*min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) *
            (|t.centeredSum p ω|/p) := mul_le_mul_of_nonneg_right hh'
              (div_nonneg (abs_nonneg _) hp.1.le)
        _ = _ := by ring
  calc
    _ ≤ expect w (fun ω => (D:ℝ)/p *
        (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)))) := expect_mono hn hwel
    _ = (D:ℝ)/p * expect w (fun ω =>
        |t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := expect_const_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (t.normalized_centered_bound ∅ (IncidenceSearch.tree_valid G v) p
        ⟨hp.1.le,hp.2.le⟩ w hw hn hf K) (div_nonneg (Nat.cast_nonneg D) hp.1.le)

lemma finite_rootAbsolute_integral (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (K : ℕ) (v : V) :
    (∫ ω, rootAbsolute G (4^K) p ω v ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^K) := by
  rw [BondGraph.law,← BernoulliProduct.law_const,BernoulliProduct.integral_law_eq_expect]
  exact finite_rootAbsolute_expect G p hp _
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ _ => ⟨by simp [BernoulliProduct.bitWeight],by simp [BernoulliProduct.bitWeight]⟩)
    D hDpos hD K v

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassRestriction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma cluster_inter_eq {ω K : Set E} {v : V}
    (h : G.incidentEdges (G.cluster ω v) ⊆ K) :
    G.cluster (K ∩ ω) v = G.cluster ω v := by
  apply Set.Subset.antisymm (fun _ hr => hr.mono (G.openGraph_mono inter_subset_right))
  intro w hw
  rw [BondGraph.cluster,Set.mem_ofPred_eq,SimpleGraph.reachable_iff_reflTransGen] at hw ⊢
  induction hw with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u w hu huw ih =>
    apply ih.tail
    obtain ⟨⟨e,he,hend⟩,hne⟩ := huw
    refine ⟨⟨e,⟨h ?_,he⟩,hend⟩,hne⟩
    exact ⟨u,((G.openGraph ω).reachable_iff_reflTransGen _ _).mpr hu,by rw [hend]; simp⟩

lemma restrict_incident (K : Set E) (S : Set V) :
    (G.restrictEdges K).incidentEdges S = Subtype.val ⁻¹' (G.incidentEdges S) := rfl

lemma restrict_local (hl : G.LocallyFinite) (K : Set E) : (G.restrictEdges K).LocallyFinite := by
  intro v
  change (Subtype.val ⁻¹' {e : E | v ∈ G.ends e} : Set K).Finite
  exact (hl v).preimage Subtype.val_injective.injOn

lemma restrict_incident_bound (hl : G.LocallyFinite) (K : Set E) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D) (v : V) :
    ((G.restrictEdges K).incidentEdges {v}).ncard ≤ D := by
  rw [restrict_incident]
  exact (Set.ncard_le_ncard_of_injOn Subtype.val (fun _ h => h)
    Subtype.val_injective.injOn (G.finite_incident hl (Set.finite_singleton v))).trans (hD v)

lemma restrict_rootSum_eq {K ω : Set E} {v : V}
    (h : G.incidentEdges (G.cluster ω v) ⊆ K) (p : ℝ) :
    rootSum (G.restrictEdges K) p (Subtype.val ⁻¹' ω) v = rootSum G p ω v := by
  unfold rootSum
  rw [restrict_cluster,cluster_inter_eq G h,restrict_incident]
  change (∑' e : K, if e.val ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e.val else 0) = _
  apply tsum_subtype_eq_of_support_subset (s := K)
    (f := fun e => if e ∈ G.incidentEdges (G.cluster ω v) then coefficient p ω e else 0)
  intro e he
  by_contra hn
  have hi : e ∉ G.incidentEdges (G.cluster ω v) := fun hi => hn (h hi)
  exact he (ite_eq_right hi)

lemma restrict_rootAbsolute_eq {K ω : Set E} {v : V}
    (h : G.incidentEdges (G.cluster ω v) ⊆ K) (s : ℕ) (p : ℝ) :
    rootAbsolute (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) v = rootAbsolute G s p ω v := by
  rw [rootAbsolute,restrict_rootSum_eq G h]
  unfold rootAbsolute mass size
  rw [restrict_cluster,cluster_inter_eq G h]

lemma eventually_incident_subset (hl : G.LocallyFinite)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) {ω : Set E} {v : V}
    (hC : (G.cluster ω v).Finite) : ∀ᶠ n in atTop, G.incidentEdges (G.cluster ω v) ⊆ K n := by
  have hi := G.finite_incident hl hC
  have hh (e : E) : ∀ᶠ n in atTop, e ∈ K n := by
    have : e ∈ ⋃ n, K n := by rw [K.iUnion_eq]; trivial
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp this
    exact eventually_atTop.mpr ⟨n,fun m hm => K.mono hm hn⟩
  exact (eventually_all_finite hi).mpr (fun e _ => hh e)

variable [Countable V] [Countable E]

omit [Countable E] in
lemma measurable_restrict (K : Set E) :
    Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
  Measurable.of_eval (fun edge => measurable_set_mem edge.val)

lemma restricted_rootAbsolute_integral (p : unitInterval) (K : Set E) (hK : K.Finite)
    (s : ℕ) (v : V) :
    (∫ ω, rootAbsolute (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) v ∂G.law p) =
    ∫ ω, rootAbsolute (G.restrictEdges K) s p ω v ∂(G.restrictEdges K).law p := by
  let := hK.fintype
  simp only [BondGraph.law,← BernoulliProduct.law_const]
  rw [← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  rw [integral_map (measurable_restrict K).aemeasurable
    (measurable_rootAbsolute (G.restrictEdges K) s p v).aestronglyMeasurable]

omit [Countable V] [Countable E] in
lemma ae_finite_clusters (p : unitInterval) (hp : p < G.criticalProbability) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Finite := by
  have hh := G.law_percolates_eq_zero_of_lt_critical hp
  rw [measure_eq_zero_iff_ae_notMem] at hh
  filter_upwards [hh] with ω hω v
  exact not_not.mp (fun hc => hω ⟨v,hc⟩)

theorem subcritical_rootAbsolute_bound (hl : G.LocallyFinite)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability)
    (k : ℕ) (v : V) :
    (∫ ω, rootAbsolute G (4^k) p ω v ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  let : IsProbabilityMeasure (G.law p) := by
    unfold BondGraph.law
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let F := fun n ω => rootAbsolute (G.restrictEdges (K n)) (4^k) p (Subtype.val ⁻¹' ω) v
  have hb (n : ℕ) : (∫ ω, F n ω ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
    rw [show (∫ ω, F n ω ∂G.law p) = _ from
      restricted_rootAbsolute_integral G p (K n) (K.finite n) (4^k) v]
    let := (K.finite n).fintype
    exact finite_rootAbsolute_integral (G.restrictEdges (K n)) p hp D hDpos
      (restrict_incident_bound G hl (K n) D hD) k v
  have ht : Tendsto (fun n => ∫ ω, F n ω ∂G.law p) atTop
      (𝓝 (∫ ω, rootAbsolute G (4^k) p ω v ∂G.law p)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (D:ℝ)/(p:ℝ))
    · intro n
      exact ((measurable_rootAbsolute (G.restrictEdges (K n)) (4^k) p v).comp
        (measurable_restrict (K n))).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro ω
      dsimp only [F]
      rw [Real.norm_eq_abs,abs_of_nonneg (rootAbsolute_nonneg _ _ _ _ _)]
      exact rootAbsolute_bound (G.restrictEdges (K n)) (restrict_local G hl (K n)) D
        (restrict_incident_bound G hl (K n) D hD) (4^k) hp _ v
    · filter_upwards [ae_finite_clusters G p hpc] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_incident_subset G hl K (hω v)] with n hn
      exact (restrict_rootAbsolute_eq G hn (4^k) p).symm
  exact le_of_tendsto ht (Eventually.of_forall hb)

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassEndpoint
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma restrict_edgeDiscrepancy_eq {K ω : Set E} (e : K)
    (hx : G.incidentEdges (G.cluster ω (G.ends e.val).out.1) ⊆ K)
    (hy : G.incidentEdges (G.cluster ω (G.ends e.val).out.2) ⊆ K)
    (s : ℕ) (p : ℝ) :
    edgeDiscrepancy (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) e =
      edgeDiscrepancy G s p ω e.val := by
  have hc := cluster_inter_eq G hx
  have hconn : ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)).Reachable
      (G.ends e.val).out.1 (G.ends e.val).out.2 ↔
        (G.openGraph ω).Reachable (G.ends e.val).out.1 (G.ends e.val).out.2 := by
    rw [G.restrictEdges_openGraph]
    exact Set.ext_iff.mp hc _
  unfold edgeDiscrepancy edgeMass size coefficient
  change (if e.val ∈ ω then -(1-p)/p else 1) *
    (cappedMass s ((G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) (G.ends e.val).out.1).ncard +
      (if ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)).Reachable (G.ends e.val).out.1 (G.ends e.val).out.2 then 0
       else cappedMass s ((G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) (G.ends e.val).out.2).ncard)) = _
  rw [hconn,restrict_cluster,restrict_cluster,cluster_inter_eq G hx,cluster_inter_eq G hy]

lemma restrict_twoCluster (K : Set E) (ω : Set E) (u v : V) (s : ℕ) :
    Subtype.val ⁻¹' ω ∈ (G.restrictEdges K).twoClusterEvent u v s ↔
      K ∩ ω ∈ G.twoClusterEvent u v s := by
  simp only [BondGraph.twoClusterEvent,Set.mem_inter_iff,BondGraph.clusterTail,
    Set.mem_ofPred_eq,restrict_cluster,G.restrictEdges_openGraph]

variable [Countable V] [Countable E]

lemma restrict_twoCluster_real (p : unitInterval) (K : Set E) (u v : V) (s : ℕ) :
    ((G.restrictEdges K).law p).real ((G.restrictEdges K).twoClusterEvent u v s) =
      (G.law p).real {ω | K ∩ ω ∈ G.twoClusterEvent u v s} := by
  simp only [BondGraph.law,← BernoulliProduct.law_const]
  rw [← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  simp only [measureReal_def]
  rw [Measure.map_apply (measurable_restrict K)
    ((G.restrictEdges K).measurableSet_twoClusterEvent u v s)]
  congr 2
  ext ω
  exact restrict_twoCluster G K ω u v s

lemma restricted_edgeDiscrepancy_integral (p : unitInterval) (K : Set E) (e : K) (s : ℕ) :
    (∫ ω, edgeDiscrepancy (G.restrictEdges K) s p (Subtype.val ⁻¹' ω) e ∂G.law p) =
      ∫ ω, edgeDiscrepancy (G.restrictEdges K) s p ω e ∂(G.restrictEdges K).law p := by
  simp only [BondGraph.law,← BernoulliProduct.law_const]
  rw [← BernoulliProduct.law_map_restrict (fun _ : E => p) K]
  rw [integral_map (measurable_restrict K).aemeasurable
    (measurable_edgeDiscrepancy (G.restrictEdges K) s p e).aestronglyMeasurable]

theorem subcritical_endpoint_le_integral (hl : G.LocallyFinite)
    (s : ℕ) (hs : 0 < s) (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1)
    (hpc : p < G.criticalProbability) (e : E) :
    (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) ≤
      ∫ ω, edgeDiscrepancy G s p ω e ∂G.law p := by
  let K₀ := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let K : Set.FiniteExhaustion (Set.univ : Set E) :=
    { toFun := fun n => insert e (K₀ n)
      finite' := fun n => (K₀.finite n).insert e
      subset_succ' := fun n => Set.insert_subset_insert (K₀.subset_succ n)
      iUnion_eq' := by
        apply Set.eq_univ_of_forall
        intro a
        obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (K₀.iUnion_eq.symm ▸ Set.mem_univ a)
        exact Set.mem_iUnion.mpr ⟨n,Or.inr hn⟩ }
  let en (n : ℕ) : K n := ⟨e,Or.inl rfl⟩
  let F := fun n ω => edgeDiscrepancy (G.restrictEdges (K n)) s p (Subtype.val ⁻¹' ω) (en n)
  have hb (n : ℕ) : (G.law p).real {ω | K n ∩ ω ∈
      G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s} ≤ ∫ ω, F n ω ∂G.law p := by
    rw [← restrict_twoCluster_real G p (K n),show (∫ ω, F n ω ∂G.law p) = _ from
      restricted_edgeDiscrepancy_integral G p (K n) (en n) s]
    let := (K.finite n).fintype
    exact finite_endpoint_le_integral (G.restrictEdges (K n)) s hs p hp (en n)
  have ht : Tendsto (fun n => ∫ ω, F n ω ∂G.law p) atTop
      (𝓝 (∫ ω, edgeDiscrepancy G s p ω e ∂G.law p)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 2/(p:ℝ))
    · intro n
      exact ((measurable_edgeDiscrepancy (G.restrictEdges (K n)) s p (en n)).comp
        (measurable_restrict (K n))).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Eventually.of_forall
      intro ω
      exact edgeDiscrepancy_abs_le (G.restrictEdges (K n)) s hp _ (en n)
    · filter_upwards [ae_finite_clusters G p hpc] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_incident_subset G hl K (hω (G.ends e).out.1),
        eventually_incident_subset G hl K (hω (G.ends e).out.2)] with n hn hm
      exact (restrict_edgeDiscrepancy_eq G (en n) hn hm s p).symm
  exact le_of_tendsto_of_tendsto (G.tendsto_real_twoCluster_restrict p _ _ s K) ht
    (Eventually.of_forall hb)

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma small_cluster_subset {r : ℕ} {ω : Set E} {v : V} (h : small G r ω v) :
    G.cluster ω v ⊆ G.vertexBall v r :=
  h v (SimpleGraph.Reachable.refl v)

lemma small_finite (hl : G.LocallyFinite) {r : ℕ} {ω : Set E} {v : V}
    (h : small G r ω v) : (G.cluster ω v).Finite :=
  (G.vertexBall_finite hl v r).subset (small_cluster_subset G h)

lemma small_reachable (r : ℕ) {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : small G r ω u ↔ small G r ω v := by
  unfold small
  rw [G.cluster_eq_of_reachable h]

lemma eventually_small (hc : G.fullGraph.Connected) {ω : Set E} {v : V}
    (hC : (G.cluster ω v).Finite) : ∀ᶠ r in atTop, small G r ω v := by
  obtain ⟨n,hn⟩ := G.finite_subset_vertexBall hc v hC
  apply eventually_atTop.mpr
  refine ⟨n+n,fun m hm x hx y hy => ?_⟩
  exact G.vertexBall_mono x hm (G.vertexBall_add ((G.vertexBall_comm).mp (hn hx)) n (hn hy))

lemma small_aut (φ : G.Aut) (r : ℕ) (ω : Set E) (v : V) :
    small G r (φ.edge '' ω) (φ.vertex v) ↔ small G r ω v := by
  unfold small
  rw [← φ.cluster_image]
  constructor
  · intro h x hx y hy
    exact (φ.vertexBall_mem G x y r).mp (h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩)
  · rintro h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (φ.vertexBall_mem G x y r).mpr (h x hx y hy)

lemma mass_aut (φ : G.Aut) (s : ℕ) (ω : Set E) (v : V) :
    mass G s (φ.edge '' ω) (φ.vertex v) = mass G s ω v := by
  unfold mass size
  rw [← φ.cluster_image,Set.ncard_image_of_injective _ φ.vertex.injective]

lemma coefficient_aut (φ : G.Aut) (p : ℝ) (ω : Set E) (e : E) :
    coefficient p (φ.edge '' ω) (φ.edge e) = coefficient p ω e := by
  simp [coefficient]

lemma incidentCluster_aut (φ : G.Aut) (ω : Set E) (v : V) (e : E) :
    φ.edge e ∈ G.incidentEdges (G.cluster (φ.edge '' ω) (φ.vertex v)) ↔
      e ∈ G.incidentEdges (G.cluster ω v) := by
  rw [← φ.cluster_image]
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,Set.mem_image,φ.preserves,Sym2.mem_map]
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,y,hy,hyx⟩
    exact ⟨x,hx,(φ.vertex.injective hyx) ▸ hy⟩
  · rintro ⟨x,hx,he⟩
    exact ⟨φ.vertex x,⟨x,hx,rfl⟩,x,he,rfl⟩

lemma incidentRoots (ω : Set E) (e : E) :
    {v | e ∈ G.incidentEdges (G.cluster ω v)} =
      G.cluster ω (G.ends e).out.1 ∪ G.cluster ω (G.ends e).out.2 := by
  ext v
  have he : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) := (G.ends e).out_eq.symm
  have hend (x : V) : x ∈ G.ends e ↔ x = (G.ends e).out.1 ∨ x = (G.ends e).out.2 := by
    conv_lhs => rw [he]
    exact Sym2.mem_iff
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,hend,Set.mem_union]
  constructor
  · rintro ⟨x,hx,hx' | hx'⟩
    · subst x; exact Or.inl (SimpleGraph.Reachable.symm hx)
    · subst x; exact Or.inr (SimpleGraph.Reachable.symm hx)
  · rintro (h | h)
    · exact ⟨_,SimpleGraph.Reachable.symm h,Or.inl rfl⟩
    · exact ⟨_,SimpleGraph.Reachable.symm h,Or.inr rfl⟩

variable [Countable V] [Countable E]
lemma measurable_small (r : ℕ) (v : V) : Measurable (fun ω => small G r ω v) := by
  exact Measurable.forall (fun x => (G.measurable_reachable v x).imp
    (Measurable.forall (fun y => (G.measurable_reachable v y).imp measurable_const)))

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportSums
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma weight_reachable (r s : ℕ) {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : weight G r s ω u = weight G r s ω v := by
  rw [weight,weight,small_reachable G r h,mass_eq_of_reachable G s h]

lemma weight_nonneg (r s : ℕ) (ω : Set E) (v : V) : 0 ≤ weight G r s ω v := by
  unfold weight
  split_ifs
  · exact mass_nonneg G s ω v
  · rfl

lemma clusterWeight_nonneg (r s : ℕ) (ω : Set E) (v : V) : 0 ≤ clusterWeight G r s ω v := by
  unfold clusterWeight
  split_ifs
  · exact cappedMass_nonneg _ _
  · rfl

lemma clusterWeight_le (r s : ℕ) (ω : Set E) (v : V) :
    clusterWeight G r s ω v ≤ cappedMass s (size G ω v) := by
  unfold clusterWeight
  split_ifs
  · rfl
  · exact cappedMass_nonneg _ _

lemma weighted_cluster_summable (hl : G.LocallyFinite) (r s : ℕ) (ω : Set E) (x : V) :
    Summable (fun u => if u ∈ G.cluster ω x then weight G r s ω u else 0) := by
  by_cases hs : small G r ω x
  · apply summable_of_ne_finset_zero (s := (small_finite G hl hs).toFinset)
    intro u hu
    simpa only [Set.Finite.mem_toFinset,not_false_eq_true] using
      (ite_eq_right (show u ∉ G.cluster ω x from fun h => hu ((small_finite G hl hs).mem_toFinset.mpr h)) :
        (if u ∈ G.cluster ω x then weight G r s ω u else 0) = 0)
  · have hz : (fun u => if u ∈ G.cluster ω x then weight G r s ω u else 0) = 0 := by
      funext u
      by_cases hu : u ∈ G.cluster ω x
      · rw [ite_eq_left hu,← weight_reachable G r s hu,weight,ite_eq_right hs]
        rfl
      · simp [hu]
    rw [hz]
    exact summable_zero

lemma tsum_weighted_cluster (hl : G.LocallyFinite) (r s : ℕ) (ω : Set E) (x : V) :
    (∑' u, if u ∈ G.cluster ω x then weight G r s ω u else 0) = clusterWeight G r s ω x := by
  by_cases hs : small G r ω x
  · have hC := small_finite G hl hs
    have hpos : 0 < size G ω x := (Set.ncard_pos hC).mpr ⟨x,SimpleGraph.Reachable.refl x⟩
    rw [tsum_eq_sum (s := hC.toFinset) (fun u hu => ite_eq_right (fun h => hu (hC.mem_toFinset.mpr h)))]
    calc
      _ = ∑ _u ∈ hC.toFinset, mass G s ω x := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [ite_eq_left (hC.mem_toFinset.mp hu),← weight_reachable G r s (hC.mem_toFinset.mp hu),weight,ite_eq_left hs]
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,← Set.ncard_eq_toFinset_card _ hC]
        change (size G ω x : ℝ) * (cappedMass s (size G ω x) / size G ω x) = _
        rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hpos.ne')]
        exact (ite_eq_left hs).symm
  · rw [clusterWeight,ite_eq_right hs]
    calc
      _ = ∑' _u : V, (0:ℝ) := by
        apply tsum_congr
        intro u
        by_cases hu : u ∈ G.cluster ω x
        · rw [ite_eq_left hu,← weight_reachable G r s hu,weight,ite_eq_right hs]
        · rw [ite_eq_right hu]
      _ = 0 := tsum_zero

lemma transport_sum_out (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) :
    (∑' e, transport G r s p ω u e) = if small G r ω u then rootDiscrepancy G s p ω u else 0 := by
  have hf : (fun e => transport G r s p ω u e) =
      (fun e => weight G r s ω u * (if e ∈ G.incidentEdges (G.cluster ω u) then coefficient p ω e else 0)) := by
    funext e
    unfold transport
    split_ifs <;> simp
  rw [hf,tsum_mul_left]
  unfold weight rootDiscrepancy rootSum
  split_ifs <;> simp

lemma transport_sum_in (hl : G.LocallyFinite) (r s : ℕ) (p : ℝ) (ω : Set E) (e : E) :
    (∑' u, transport G r s p ω u e) = coefficient p ω e * truncatedEdgeMass G r s ω e := by
  let x := (G.ends e).out.1
  let y := (G.ends e).out.2
  have hi (u : V) : e ∈ G.incidentEdges (G.cluster ω u) ↔
      u ∈ G.cluster ω x ∪ G.cluster ω y := by
    exact Set.ext_iff.mp (incidentRoots G ω e) u
  by_cases hxy : (G.openGraph ω).Reachable x y
  · have heq := G.cluster_eq_of_reachable hxy
    have hf : (fun u => transport G r s p ω u e) =
        fun u => coefficient p ω e * (if u ∈ G.cluster ω x then weight G r s ω u else 0) := by
      funext u
      unfold transport
      rw [hi,← heq,Set.union_self]
      split_ifs <;> ring
    rw [hf,tsum_mul_left,tsum_weighted_cluster G hl]
    simp only [truncatedEdgeMass,show (G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 from hxy,ite_true, if_true,add_zero]
    rfl
  · have hd := G.cluster_disjoint_of_not_reachable hxy
    have hf : (fun u => transport G r s p ω u e) = fun u => coefficient p ω e *
        ((if u ∈ G.cluster ω x then weight G r s ω u else 0) +
          (if u ∈ G.cluster ω y then weight G r s ω u else 0)) := by
      funext u
      unfold transport
      rw [hi]
      by_cases hx : u ∈ G.cluster ω x
      · have hy : u ∉ G.cluster ω y := fun hy => Set.disjoint_left.mp hd hx hy
        simp only [hx,hy,Set.mem_union,true_or,ite_true, if_true,ite_false, if_false,add_zero]
        ring
      · by_cases hy : u ∈ G.cluster ω y
        · simp only [hx,hy,Set.mem_union,or_true,ite_true, if_true,ite_false, if_false,zero_add] <;> ring
        · simp only [hx,hy,Set.mem_union,or_false,ite_false, if_false,add_zero,mul_zero]
    rw [hf,tsum_mul_left,(weighted_cluster_summable G hl r s ω x).tsum_add
      (weighted_cluster_summable G hl r s ω y),tsum_weighted_cluster G hl,tsum_weighted_cluster G hl]
    simp only [truncatedEdgeMass,show ¬(G.openGraph ω).Reachable (G.ends e).out.1 (G.ends e).out.2 from hxy,ite_false, if_false]
    rfl

lemma truncatedEdgeMass_nonneg (r s : ℕ) (ω : Set E) (e : E) :
    0 ≤ truncatedEdgeMass G r s ω e := by
  unfold truncatedEdgeMass
  split_ifs
  · simpa using clusterWeight_nonneg G r s ω (G.ends e).out.1
  · exact add_nonneg (clusterWeight_nonneg G r s ω _) (clusterWeight_nonneg G r s ω _)

lemma truncatedEdgeMass_le (r s : ℕ) (ω : Set E) (e : E) :
    truncatedEdgeMass G r s ω e ≤ edgeMass G s ω e := by
  unfold truncatedEdgeMass edgeMass
  split_ifs
  · simpa using clusterWeight_le G r s ω (G.ends e).out.1
  · exact add_le_add (clusterWeight_le G r s ω _) (clusterWeight_le G r s ω _)

lemma transport_sum_in_bound (hl : G.LocallyFinite) (r s : ℕ) {p : ℝ}
    (hp : p ∈ Ioo 0 1) (ω : Set E) (e : E) :
    |∑' u, transport G r s p ω u e| ≤ 2/p := by
  rw [transport_sum_in G hl,abs_mul,abs_of_nonneg (truncatedEdgeMass_nonneg G r s ω e)]
  calc
    _ ≤ (1/p)*2 := mul_le_mul (coefficient_abs_le hp ω e)
      ((truncatedEdgeMass_le G r s ω e).trans (edgeMass_le_two G s ω e))
      (truncatedEdgeMass_nonneg G r s ω e) (div_nonneg zero_le_one hp.1.le)
    _ = _ := by ring

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportFinite
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma transport_row_zero (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) (e : E)
    (he : e ∉ G.incidentEdges (G.vertexBall u r)) : transport G r s p ω u e = 0 := by
  unfold transport weight
  by_cases hs : small G r ω u
  · have hi : e ∉ G.incidentEdges (G.cluster ω u) := by
      rintro ⟨v,hv,hve⟩
      exact he ⟨v,small_cluster_subset G hs hv,hve⟩
    rw [ite_eq_right hi]
  · simp only [hs,ite_false, if_false,zero_mul,ite_self]

lemma transport_column_zero (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) (e : E)
    (hu : u ∉ G.vertexBall (G.ends e).out.1 r ∪ G.vertexBall (G.ends e).out.2 r) :
    transport G r s p ω u e = 0 := by
  unfold transport weight
  by_cases hs : small G r ω u
  · have hi : e ∉ G.incidentEdges (G.cluster ω u) := by
      intro he
      have he' : u ∈ G.cluster ω (G.ends e).out.1 ∪ G.cluster ω (G.ends e).out.2 :=
        Set.ext_iff.mp (incidentRoots G ω e) u |>.mp he
      rcases he' with h | h
      · exact hu (Or.inl (G.vertexBall_comm.mp (small_cluster_subset G hs h.symm)))
      · exact hu (Or.inr (G.vertexBall_comm.mp (small_cluster_subset G hs h.symm)))
    rw [ite_eq_right hi]
  · simp only [hs,ite_false, if_false,zero_mul,ite_self]

lemma mass_le_one (s : ℕ) (ω : Set E) (v : V) : mass G s ω v ≤ 1 := by
  by_cases hn : size G ω v = 0
  · simp [mass,hn]
  · have hp : (0:ℝ) < size G ω v := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (div_le_one hp).mpr
    exact (cappedMass_le_one _ _).trans (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)

lemma weight_le_one (r s : ℕ) (ω : Set E) (v : V) : weight G r s ω v ≤ 1 := by
  unfold weight
  split_ifs
  · exact mass_le_one G s ω v
  · norm_num

lemma transport_bound (r s : ℕ) {p : ℝ} (hp : p ∈ Ioo 0 1)
    (ω : Set E) (u : V) (e : E) : |transport G r s p ω u e| ≤ 1/p := by
  unfold transport
  split_ifs
  · rw [abs_mul,abs_of_nonneg (weight_nonneg G r s ω u)]
    exact (mul_le_mul (weight_le_one G r s ω u) (coefficient_abs_le hp ω e)
      (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · simpa only [abs_zero] using div_nonneg (show (0:ℝ)≤1 by norm_num) hp.1.le

lemma transport_aut (φ : G.Aut) (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) (e : E) :
    transport G r s p (φ.edge '' ω) (φ.vertex u) (φ.edge e) = transport G r s p ω u e := by
  simp only [transport,weight,incidentCluster_aut G φ,small_aut G φ,mass_aut G φ,coefficient_aut G φ]

variable [Countable V] [Countable E]
lemma measurable_weight (r s : ℕ) (u : V) : Measurable (fun ω => weight G r s ω u) :=
  (measurable_mass G s u).ite (measurable_small G r u).setOf measurable_const

lemma measurable_transport (r s : ℕ) (p : ℝ) (u : V) (e : E) :
    Measurable (fun ω => transport G r s p ω u e) :=
  ((measurable_weight G r s u).mul (measurable_coefficient p e)).ite
    (measurable_incidentCluster G u e) measurable_const

lemma integrable_transport (r s : ℕ) (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1) (u : V) (e : E) :
    Integrable (fun ω => transport G r s p ω u e) (G.law p) := by
  apply Integrable.mono' (integrable_const (1/(p:ℝ))) (measurable_transport G r s p u e).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => transport_bound G r s hp ω u e)

lemma expectedTransport_aut (φ : G.Aut) (r s : ℕ) (p : unitInterval) (u : V) (e : E) :
    expectedTransport G r s p (φ.vertex u) (φ.edge e) = expectedTransport G r s p u e := by
  unfold expectedTransport
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [integral_map (BernoulliProduct.measurable_image_equiv φ.edge).aemeasurable
    (measurable_transport G r s p (φ.vertex u) (φ.edge e)).aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ω => transport_aut G φ r s p ω u e)

omit [Countable V] [Countable E] in
lemma expectedTransport_row_zero (r s : ℕ) (p : unitInterval) (u : V) (e : E)
    (he : e ∉ G.incidentEdges (G.vertexBall u r)) : expectedTransport G r s p u e = 0 := by
  unfold expectedTransport
  simp only [transport_row_zero G r s p _ u e he,integral_zero]

omit [Countable V] [Countable E] in
lemma expectedTransport_column_zero (r s : ℕ) (p : unitInterval) (u : V) (e : E)
    (hu : u ∉ G.vertexBall (G.ends e).out.1 r ∪ G.vertexBall (G.ends e).out.2 r) :
    expectedTransport G r s p u e = 0 := by
  unfold expectedTransport
  simp only [transport_column_zero G r s p _ u e hu,integral_zero]

omit [Countable V] [Countable E] in
lemma expectedTransport_row_finite (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval) (u : V) :
    (Function.support (expectedTransport G r s p u)).Finite := by
  apply (G.finite_incident hl (G.vertexBall_finite hl u r)).subset
  intro e he
  by_contra hn
  exact he (expectedTransport_row_zero G r s p u e hn)

omit [Countable V] [Countable E] in
lemma expectedTransport_column_finite (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval) (e : E) :
    (Function.support (fun u => expectedTransport G r s p u e)).Finite := by
  apply ((G.vertexBall_finite hl (G.ends e).out.1 r).union
    (G.vertexBall_finite hl (G.ends e).out.2 r)).subset
  intro u hu
  by_contra hn
  exact hu (expectedTransport_column_zero G r s p u e hn)

lemma expectedTransport_sum_out (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (u : V) :
    (∑' e, expectedTransport G r s p u e) = ∫ ω, ∑' e, transport G r s p ω u e ∂G.law p := by
  have hI := G.finite_incident hl (G.vertexBall_finite hl u r)
  rw [tsum_eq_sum (s := hI.toFinset) (fun e he => expectedTransport_row_zero G r s p u e
    (fun h => he (hI.mem_toFinset.mpr h)))]
  unfold expectedTransport
  rw [← integral_finsetSum _ (fun e _ => integrable_transport G r s p hp u e)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  exact (tsum_eq_sum (s := hI.toFinset) (fun e he => transport_row_zero G r s p ω u e
    (fun h => he (hI.mem_toFinset.mpr h)))).symm

lemma expectedTransport_sum_in (hl : G.LocallyFinite) (r s : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (e : E) :
    (∑' u, expectedTransport G r s p u e) = ∫ ω, ∑' u, transport G r s p ω u e ∂G.law p := by
  have hB := (G.vertexBall_finite hl (G.ends e).out.1 r).union
    (G.vertexBall_finite hl (G.ends e).out.2 r)
  rw [tsum_eq_sum (s := hB.toFinset) (fun u hu => expectedTransport_column_zero G r s p u e
    (fun h => hu (hB.mem_toFinset.mpr h)))]
  unfold expectedTransport
  rw [← integral_finsetSum _ (fun u _ => integrable_transport G r s p hp u e)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  exact (tsum_eq_sum (s := hB.toFinset) (fun u hu => transport_column_zero G r s p ω u e
    (fun h => hu (hB.mem_toFinset.mpr h)))).symm

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterTransportLimit
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma transport_sum_out_le (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) :
    (∑' e, transport G r s p ω u e) ≤ rootAbsolute G s p ω u := by
  rw [transport_sum_out]
  split_ifs
  · exact (le_abs_self _).trans_eq (abs_rootDiscrepancy G s p ω u)
  · exact rootAbsolute_nonneg G s p ω u

omit [Countable V] [Countable E] in
lemma transport_sum_out_abs (r s : ℕ) (p : ℝ) (ω : Set E) (u : V) :
    |∑' e, transport G r s p ω u e| ≤ rootAbsolute G s p ω u := by
  rw [transport_sum_out]
  split_ifs
  · exact (abs_rootDiscrepancy G s p ω u).le
  · exact (abs_zero).le.trans (rootAbsolute_nonneg G s p ω u)

lemma integrable_transport_out (hl : G.LocallyFinite) (D : ℕ)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (r s : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (u : V) :
    Integrable (fun ω => ∑' e, transport G r s p ω u e) (G.law p) := by
  apply Integrable.mono' (integrable_const ((D:ℝ)/(p:ℝ)))
    (Measurable.tsum (fun e => measurable_transport G r s p u e)).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => (transport_sum_out_abs G r s p ω u).trans
    (rootAbsolute_bound G hl D hD s hp ω u))

lemma expectedTransport_out_bound (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (r k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) (u : V) :
    (∑' e, expectedTransport G r (4^k) p u e) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  rw [expectedTransport_sum_out G hl r (4^k) p hp u]
  refine (integral_mono_ae (integrable_transport_out G hl D hD r (4^k) p hp u) ?_
    (Eventually.of_forall (fun ω => transport_sum_out_le G r (4^k) p ω u))).trans
    (subcritical_rootAbsolute_bound G hl D hDpos hD p hp hpc k u)
  apply Integrable.mono' (integrable_const ((D:ℝ)/(p:ℝ)))
    (measurable_rootAbsolute G (4^k) p u).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rootAbsolute_nonneg G (4^k) p ω u)]
    exact rootAbsolute_bound G hl D hD (4^k) hp ω u)

omit [Countable V] [Countable E] in
lemma eventually_truncatedEdgeMass (hc : G.fullGraph.Connected) {ω : Set E} {e : E}
    (hx : (G.cluster ω (G.ends e).out.1).Finite)
    (hy : (G.cluster ω (G.ends e).out.2).Finite) (s : ℕ) :
    ∀ᶠ r in atTop, truncatedEdgeMass G r s ω e = edgeMass G s ω e := by
  filter_upwards [eventually_small G hc hx,eventually_small G hc hy] with r hr hs
  simp only [truncatedEdgeMass,clusterWeight,hr,hs,ite_true, if_true,edgeMass]

lemma expectedTransport_in_tendsto (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (s : ℕ) (p : unitInterval) (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) (e : E) :
    Tendsto (fun r => ∑' u, expectedTransport G r s p u e) atTop
      (𝓝 (∫ ω, edgeDiscrepancy G s p ω e ∂G.law p)) := by
  simp only [expectedTransport_sum_in G hl _ s p hp e]
  apply tendsto_integral_of_dominated_convergence (fun _ => 2/(p:ℝ))
  · intro r
    exact (Measurable.tsum (fun u => measurable_transport G r s p u e)).aestronglyMeasurable
  · exact integrable_const _
  · intro r
    exact Eventually.of_forall (fun ω => transport_sum_in_bound G hl r s hp ω e)
  · filter_upwards [ae_finite_clusters G p hpc] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_truncatedEdgeMass G hc (hω _) (hω _) s] with r hr
    rw [transport_sum_in G hl,hr]
    rfl

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_Unimodularity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.cluster_empty _root_.OAI.CriticalPercolation.BondGraph.empty_not_percolates _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.openGraph_empty _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma UnimodularRoot.quasiTransitive (R : G.UnimodularRoot) : G.QuasiTransitive :=
  ⟨R.roots,R.roots.finite_toSet,R.cover⟩

lemma bondShare_pos (e : E) : 0 < G.bondShare e := by
  apply one_div_pos.mpr
  exact Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty _)))

lemma bondShare_count (e : E) : ((G.ends e).toFinset.card : ℝ) * G.bondShare e = 1 := by
  unfold bondShare
  exact mul_one_div_cancel (ne_of_gt (by
    exact Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty _)))))

lemma Aut.bondShare (φ : G.Aut) (e : E) : G.bondShare (φ.edge e) = G.bondShare e := by
  have hfin : (G.ends (φ.edge e)).toFinset = (G.ends e).toFinset.map φ.vertex.toEmbedding := by
    ext v
    simp only [Sym2.mem_toFinset,Finset.mem_map,Equiv.toEmbedding_apply,φ.preserves,Sym2.mem_map]
  simp only [CriticalPercolation.BondGraph.bondShare,hfin,Finset.card_map]

lemma Aut.incident_iff (φ : G.Aut) (u : V) (e : E) :
    φ.vertex u ∈ G.ends (φ.edge e) ↔ u ∈ G.ends e := by
  rw [φ.preserves,Sym2.mem_map]
  simp only [φ.vertex.injective.eq_iff,exists_eq_right]

lemma splitBondTransport_zero (F : V → E → ℝ) {u v : V}
    (hv : v ∉ ⋃ e ∈ Function.support (F u), {v | v ∈ G.ends e}) :
    G.splitBondTransport F u v = 0 := by
  unfold splitBondTransport
  have hz (e : E) : (if v ∈ G.ends e then G.bondShare e * F u e else 0) = 0 := by
    by_cases he : v ∈ G.ends e
    · have hf : F u e = 0 := by
        by_contra hn
        exact hv (Set.mem_iUnion₂.mpr ⟨e,hn,he⟩)
      simp [he,hf]
    · simp [he]
  simp only [hz,tsum_zero]

lemma splitBondTransport_row_finite (F : V → E → ℝ)
    (hf : ∀ u, (Function.support (F u)).Finite) (u : V) :
    (Function.support (G.splitBondTransport F u)).Finite := by
  have endpoints_finite (edge : E) : {vertex | vertex ∈ G.ends edge}.Finite := by
    convert (G.ends edge).toFinset.finite_toSet using 1
    all_goals try with_reducible_and_instances rfl
    ext vertex
    exact Sym2.mem_toFinset.symm
  apply ((hf u).biUnion fun edge _ => endpoints_finite edge).subset
  intro v hv
  by_contra hn
  exact hv (G.splitBondTransport_zero F hn)

lemma splitBondTransport_column_finite (hl : G.LocallyFinite) (F : V → E → ℝ)
    (hf : ∀ e, (Function.support (fun u => F u e)).Finite) (v : V) :
    (Function.support (fun u => G.splitBondTransport F u v)).Finite := by
  apply ((hl v).biUnion (fun e _ => hf e)).subset
  intro u hu
  by_contra hn
  have hz (e : E) : (if v ∈ G.ends e then G.bondShare e * F u e else 0) = 0 := by
    by_cases he : v ∈ G.ends e
    · have hf : F u e = 0 := by
        by_contra hne
        exact hn (Set.mem_iUnion₂.mpr ⟨e,he,hne⟩)
      simp [he,hf]
    · simp [he]
  exact hu (by simp only [splitBondTransport,hz,tsum_zero])

lemma splitBondTransport_aut (F : V → E → ℝ)
    (hF : ∀ (φ : G.Aut) u e, F (φ.vertex u) (φ.edge e) = F u e)
    (φ : G.Aut) (u v : V) :
    G.splitBondTransport F (φ.vertex u) (φ.vertex v) = G.splitBondTransport F u v := by
  unfold splitBondTransport
  rw [← φ.edge.tsum_eq]
  simp only [Aut.incident_iff,Aut.bondShare,hF]

lemma tsum_incident_share (e : E) (a : ℝ) :
    (∑' v : V, if v ∈ G.ends e then G.bondShare e * a else 0) = a := by
  rw [tsum_eq_sum (s := (G.ends e).toFinset) (fun v hv => ite_eq_right (fun h => hv (Sym2.mem_toFinset.mpr h)))]
  calc
    _ = ∑ _v ∈ (G.ends e).toFinset, G.bondShare e * a := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [ite_eq_left (Sym2.mem_toFinset.mp hv)]
    _ = a := by
      rw [Finset.sum_const,nsmul_eq_mul,← mul_assoc,bondShare_count,one_mul]

lemma splitBondTransport_sum_out (F : V → E → ℝ)
    (hf : ∀ u, (Function.support (F u)).Finite) (u : V) :
    (∑' v, G.splitBondTransport F u v) = ∑' e, F u e := by
  have ht (v : V) : G.splitBondTransport F u v =
      ∑ e ∈ (hf u).toFinset, if v ∈ G.ends e then G.bondShare e * F u e else 0 := by
    apply tsum_eq_sum
    intro e he
    have hz : F u e = 0 := not_not.mp (fun h => he ((hf u).mem_toFinset.mpr h))
    simp [hz]
  have hs (e : E) : Summable (fun v => if v ∈ G.ends e then G.bondShare e * F u e else 0) := by
    apply summable_of_ne_finset_zero (s := (G.ends e).toFinset)
    exact fun v hv => ite_eq_right (fun h => hv (Sym2.mem_toFinset.mpr h))
  simp only [ht]
  rw [Summable.tsum_finsetSum (fun e _ => hs e)]
  simp only [tsum_incident_share]
  exact (tsum_eq_sum (s := (hf u).toFinset) (fun e he =>
    not_not.mp (fun h => he ((hf u).mem_toFinset.mpr h)))).symm

lemma splitBondTransport_sum_in (hl : G.LocallyFinite) (F : V → E → ℝ)
    (hf : ∀ e, (Function.support (fun u => F u e)).Finite) (v : V) :
    (∑' u, G.splitBondTransport F u v) =
      ∑' e, if v ∈ G.ends e then G.bondShare e * ∑' u, F u e else 0 := by
  have ht (u : V) : G.splitBondTransport F u v =
      ∑ e ∈ (hl v).toFinset, G.bondShare e * F u e := by
    unfold splitBondTransport
    rw [tsum_eq_sum (f := fun e => if v ∈ G.ends e then G.bondShare e * F u e else 0)
      (s := (hl v).toFinset) (fun e he => ite_eq_right (fun h => he ((hl v).mem_toFinset.mpr h)))]
    apply Finset.sum_congr rfl
    intro e he
    rw [ite_eq_left (show v ∈ G.ends e from (hl v).mem_toFinset.mp he)]
  have hs (e : E) : Summable (fun u => G.bondShare e * F u e) :=
    (summable_of_hasFiniteSupport (hf e)).mul_left _
  simp only [ht]
  rw [Summable.tsum_finsetSum (fun e _ => hs e)]
  simp only [tsum_mul_left]
  rw [tsum_eq_sum (f := fun e => if v ∈ G.ends e then G.bondShare e * ∑' u, F u e else 0)
    (s := (hl v).toFinset) (fun e he => ite_eq_right (fun h => he ((hl v).mem_toFinset.mpr h)))]
  apply Finset.sum_congr rfl
  intro e he
  rw [ite_eq_left (show v ∈ G.ends e from (hl v).mem_toFinset.mp he)]

lemma UnimodularRoot.bond_balance (R : G.UnimodularRoot) (hl : G.LocallyFinite)
    (F : V → E → ℝ) (hF : ∀ (φ : G.Aut) u e, F (φ.vertex u) (φ.edge e) = F u e)
    (hr : ∀ u, (Function.support (F u)).Finite)
    (hc : ∀ e, (Function.support (fun u => F u e)).Finite) :
    (∑ u ∈ R.roots, R.weight u * ∑' e, F u e) =
      ∑ v ∈ R.roots, R.weight v *
        ∑' e, if v ∈ G.ends e then G.bondShare e * ∑' u, F u e else 0 := by
  have h := R.balance (G.splitBondTransport F) (G.splitBondTransport_aut F hF)
    (G.splitBondTransport_row_finite F hr) (G.splitBondTransport_column_finite hl F hc)
  simpa only [G.splitBondTransport_sum_out F hr,G.splitBondTransport_sum_in hl F hc] using h

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_UnimodularAverages
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteClusters

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma incident_tsum_eq (hl : G.LocallyFinite) (v : V) (f : E → ℝ) :
    (∑' e, if v ∈ G.ends e then G.bondShare e * f e else 0) =
      ∑ e ∈ (hl v).toFinset, G.bondShare e * f e := by
  rw [tsum_eq_sum (f := fun e => if v ∈ G.ends e then G.bondShare e * f e else 0)
    (s := (hl v).toFinset) (fun e he => ite_eq_right (fun h => he ((hl v).mem_toFinset.mpr h)))]
  apply Finset.sum_congr rfl
  intro e he
  exact ite_eq_left (show v ∈ G.ends e from (hl v).mem_toFinset.mp he)

lemma UnimodularRoot.truncated_average_bound (R : G.UnimodularRoot)
    (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (r k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) :
    (∑ v ∈ R.roots, R.weight v * ∑ e ∈ (hl v).toFinset, G.bondShare e *
      ∑' u, expectedTransport G r (4^k) p u e) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  have hb := UnimodularRoot.bond_balance G R hl (expectedTransport G r (4^k) p)
    (fun φ u e => expectedTransport_aut G φ r (4^k) p u e)
    (expectedTransport_row_finite G hl r (4^k) p)
    (expectedTransport_column_finite G hl r (4^k) p)
  simp only [G.incident_tsum_eq hl] at hb
  rw [← hb]
  calc
    _ ≤ ∑ u ∈ R.roots, R.weight u * ((D:ℝ)/p*(6/(2:ℝ)^k)) := by
      apply Finset.sum_le_sum
      intro u hu
      exact mul_le_mul_of_nonneg_left (expectedTransport_out_bound G hl D hDpos hD r k p hp hpc u)
        (R.positive u hu).le
    _ = _ := by rw [← Finset.sum_mul,R.normalized,one_mul]

lemma UnimodularRoot.average_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability) :
    (∑ v ∈ R.roots, R.weight v * ∑ e ∈ (hl v).toFinset, G.bondShare e *
      ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω e ∂G.law p) ≤ (D:ℝ)/p*(6/(2:ℝ)^k) := by
  apply le_of_tendsto (x := atTop) (f := fun r => ∑ v ∈ R.roots, R.weight v *
    ∑ e ∈ (hl v).toFinset, G.bondShare e * ∑' u, expectedTransport G r (4^k) p u e) ?_
    (Eventually.of_forall (fun r => UnimodularRoot.truncated_average_bound G R hl D hDpos hD r k p hp hpc))
  apply tendsto_finsetSum
  intro v hv
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro e he
  exact (expectedTransport_in_tendsto G hc hl (4^k) p hp hpc e).const_mul _

lemma UnimodularRoot.incident_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ u, (G.incidentEdges {u}).ncard ≤ D) (k : ℕ) (p : unitInterval)
    (hp : (p:ℝ) ∈ Ioo 0 1) (hpc : p < G.criticalProbability)
    {v : V} (hv : v ∈ R.roots) {e : E} (he : v ∈ G.ends e) :
    R.weight v * G.bondShare e * (G.law p).real
        (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
      (D:ℝ)/p*(6/(2:ℝ)^k) := by
  have hle (f : E) := subcritical_endpoint_le_integral G hl (4^k) (by positivity) p hp hpc f
  have hn (f : E) : 0 ≤ ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p := measureReal_nonneg.trans (hle f)
  calc
    _ ≤ R.weight v * (G.bondShare e * ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω e ∂G.law p) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hle e) (G.bondShare_pos e).le)
        (R.positive v hv).le
    _ ≤ R.weight v * ∑ f ∈ (hl v).toFinset, G.bondShare f *
        ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p := by
      apply mul_le_mul_of_nonneg_left _ (R.positive v hv).le
      exact Finset.single_le_sum (fun f _ => mul_nonneg (G.bondShare_pos f).le (hn f))
        ((hl v).mem_toFinset.mpr he)
    _ ≤ ∑ u ∈ R.roots, R.weight u * ∑ f ∈ (hl u).toFinset, G.bondShare f *
        ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p := by
      exact Finset.single_le_sum (f := fun u => R.weight u * ∑ f ∈ (hl u).toFinset,
        G.bondShare f * ∫ ω, FiniteClusters.edgeDiscrepancy G (4^k) p ω f ∂G.law p)
        (fun u hu => mul_nonneg (R.positive u hu).le
        (Finset.sum_nonneg (fun f _ => mul_nonneg (G.bondShare_pos f).le (hn f)))) hv
    _ ≤ _ := UnimodularRoot.average_bound G R hc hl D hDpos hD k p hp hpc

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_UnimodularAdjacent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma Aut.twoClusterEvent_preimage (φ : G.Aut) (u v : V) (s : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.twoClusterEvent (φ.vertex u) (φ.vertex v) s =
      G.twoClusterEvent u v s := by
  ext ω
  simp only [twoClusterEvent,Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [Aut.reachable_map,Aut.clusterTail_map,Aut.clusterTail_map]

lemma Aut.twoClusterEvent_real (φ : G.Aut) (p : unitInterval) (u v : V) (s : ℕ) :
    (G.law p).real (G.twoClusterEvent (φ.vertex u) (φ.vertex v) s) =
      (G.law p).real (G.twoClusterEvent u v s) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_twoClusterEvent _ _ _),Aut.twoClusterEvent_preimage]

lemma Aut.edgeTwoCluster_real (φ : G.Aut) (p : unitInterval) (e : E) (s : ℕ) :
    (G.law p).real (G.twoClusterEvent (G.ends (φ.edge e)).out.1 (G.ends (φ.edge e)).out.2 s) =
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s) := by
  have hend : s(φ.vertex (G.ends e).out.1,φ.vertex (G.ends e).out.2) =
      s((G.ends (φ.edge e)).out.1,(G.ends (φ.edge e)).out.2) := by
    calc
      _ = Sym2.map φ.vertex (G.ends e) := by
        conv_rhs => rw [← (G.ends e).out_eq]
        rfl
      _ = G.ends (φ.edge e) := (φ.preserves e).symm
      _ = _ := (G.ends (φ.edge e)).out_eq.symm
  rw [← G.twoClusterEvent_sym2 hend s]
  exact Aut.twoClusterEvent_real G φ p _ _ _

theorem UnimodularRoot.subcritical_adjacent_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (e : E) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : unitInterval), (p:ℝ) ∈ Ioo 0 1 → p < G.criticalProbability →
      ∀ k : ℕ, (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
        A/((p:ℝ)*(2:ℝ)^k) := by
  obtain ⟨D,hDpos,hD⟩ := G.uniform_incident_bound (UnimodularRoot.quasiTransitive G R)
  obtain ⟨u,hu,φ,hφ⟩ := R.cover (G.ends e).out.1
  let f := φ.edge.symm e
  have hf : φ.edge f = e := φ.edge.apply_symm_apply e
  have huf : u ∈ G.ends f := by
    apply (Aut.incident_iff G φ u f).mp
    rw [hf,hφ]
    exact Sym2.out_fst_mem _
  let w := R.weight u * G.bondShare f
  have hw : 0 < w := mul_pos (R.positive u hu) (G.bondShare_pos f)
  have hDreal : (0:ℝ) < D := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hDpos)
  refine ⟨6*(D:ℝ)/w,by positivity,?_⟩
  intro p hp hpc k
  have hb := UnimodularRoot.incident_bound G R hc hl D hDpos hD k p hp hpc hu huf
  have heq := Aut.edgeTwoCluster_real G φ p f (4^k)
  rw [hf] at heq
  rw [heq]
  calc
    _ ≤ ((D:ℝ)/p*(6/(2:ℝ)^k))/w := by
      apply (le_div_iff₀ hw).mpr
      simpa only [w,mul_comm] using hb
    _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev] <;> ring

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_UnimodularUnique
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma UnimodularRoot.critical_adjacent_bound (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1)
    (e : E) : ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ,
      (G.law G.criticalProbability).real
        (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^k)) ≤
      A/((G.criticalProbability:ℝ)*(2:ℝ)^k) := by
  obtain ⟨A,hA,hbound⟩ := UnimodularRoot.subcritical_adjacent_bound G R hc hl e
  have hp : (0:ℝ) < G.criticalProbability :=
    G.criticalProbability_pos hc hl (UnimodularRoot.quasiTransitive G R)
  refine ⟨2*A,by positivity,?_⟩
  intro k
  have hb := G.twoCluster_bound_of_subcritical (G.ends e).out.1 (G.ends e).out.2 (4^k)
    G.criticalProbability hp (A/(2:ℝ)^k) (by positivity) (fun q hhalf hq => ?_)
  · convert hb using 1
    all_goals try with_reducible_and_instances rfl
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · have hq0 : (0:ℝ) < q := lt_of_lt_of_le (by linarith : (0:ℝ)<(G.criticalProbability:ℝ)/2) hhalf
    have hh := hbound q ⟨hq0,hq.trans hpc⟩ hq k
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring

lemma UnimodularRoot.critical_adjacent_distinctInfinite_null (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1)
    (x y : V) (hxy : G.fullGraph.Adj x y) :
    G.law G.criticalProbability (G.distinctInfiniteEvent x y) = 0 := by
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  obtain ⟨A,_,hA⟩ := UnimodularRoot.critical_adjacent_bound G R hc hl hpc e
  have hp := G.criticalProbability_pos hc hl (UnimodularRoot.quasiTransitive G R)
  have hb (k : ℕ) : (G.law G.criticalProbability).real (G.distinctInfiniteEvent x y) ≤
      A/((G.criticalProbability:ℝ)*(2:ℝ)^k) := by
    have hs := measureReal_mono (G.distinctInfiniteEvent_subset_twoClusterEvent x y (4^k))
      (μ := G.law G.criticalProbability)
    have heq : s(x,y) = s((G.ends e).out.1,(G.ends e).out.2) := he.symm.trans (G.ends e).out_eq.symm
    rw [G.twoClusterEvent_sym2 heq (4^k)] at hs
    exact hs.trans (hA k)
  have ht : Tendsto (fun k : ℕ => A/((G.criticalProbability:ℝ)*(2:ℝ)^k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hp)
  have hz : (G.law G.criticalProbability).real (G.distinctInfiniteEvent x y) = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hb)) measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz

lemma atMostOneInfinite_ae_of_adjacent_null (hc : G.fullGraph.Connected)
    (p : unitInterval) (hp : 0 < p)
    (hadj : ∀ x y, G.fullGraph.Adj x y → G.law p (G.distinctInfiniteEvent x y) = 0) :
    ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.fullGraph.Adj x y → (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
    intro S x y
    by_cases hxy : G.fullGraph.Adj x y
    · have hz := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
        (fun _ => hp) (S : Set E) S.finite_toSet (G.distinctInfiniteEvent x y)
        (G.measurableSet_distinctInfiniteEvent x y)
        (by rw [BernoulliProduct.law_const]; exact hadj x y hxy)
      rw [BernoulliProduct.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.distinctInfinite_force_adjacent hc ω x y ⟨hx,hy,hxy⟩
  exact hω hS.toFinset a b hab (by simpa only [Set.Finite.coe_toFinset] using hh)

theorem UnimodularRoot.critical_atMostOneInfinite_ae_oai (R : G.UnimodularRoot)
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hpc : G.criticalProbability < 1) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ω ∈ G.atMostOneInfinite :=
  G.atMostOneInfinite_ae_of_adjacent_null hc G.criticalProbability
    (G.criticalProbability_pos hc hl (UnimodularRoot.quasiTransitive G R))
    (UnimodularRoot.critical_adjacent_distinctInfinite_null G R hc hl hpc)

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.UnimodularRoot.critical_atMostOneInfinite_ae_oai.{u_1, u_2}
