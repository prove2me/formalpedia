-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:57:00.601317+00:00
-- url     : https://prove2.me/submissions/89834bc9-4369-4264-aeee-33473777ba4d

import Mathlib
import Definitions.Def_OAIQ078B002

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

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

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

lemma expect_sum {J : Type*} [Fintype J] (w : E → A → ℝ)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j, f j ω) = ∑ j, expect w (f j) := by
  classical
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_DyadicBound
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
lemma sum_two_pow (N : ℕ) : ∑ k ∈ Finset.range N, (2:ℝ)^k = 2^N-1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring

lemma sum_two_inv_pow (N : ℕ) : ∑ k ∈ Finset.range N, 1/(2:ℝ)^k = 2-2/2^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    field_simp
    ring

lemma dyadic_sum_bound (N K : ℕ) :
    (∑ k ∈ Finset.range N,
      min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) ≤ 6/2^K := by
  have hfour (k : ℕ) : (4:ℝ)^k = (2^k)^2 := by
    rw [← pow_mul,mul_comm k 2,pow_mul]
    norm_num
  have hnonneg (k : ℕ) : 0 ≤ min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by positivity
  calc
    _ ≤ ∑ k ∈ Finset.range (K+N),
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro k _ _
      exact hnonneg k
    _ = (∑ k ∈ Finset.range K,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) +
        ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(K+k+1)/4^K) ((2:ℝ)^(K+k+1)/4^(K+k)) :=
      Finset.sum_range_add _ _ _
    _ ≤ (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) +
        ∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun k _ => min_le_left _ _)
      · exact Finset.sum_le_sum (fun k _ => min_le_right _ _)
    _ ≤ 6/2^K := by
      have h1 : (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) =
          2*(2^K-1)/4^K := by
        simp only [pow_succ,mul_div_assoc]
        rw [← Finset.sum_mul,sum_two_pow]
        ring
      have h2 : (∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k)) =
          2/2^K * (2-2/2^N) := by
        have he (k : ℕ) : (2:ℝ)^(K+k+1)/4^(K+k) = (2/2^K)*(1/2^k) := by
          rw [hfour,pow_succ,pow_add]
          field_simp
        simp_rw [he]
        rw [← Finset.mul_sum,sum_two_inv_pow]
      rw [h1,h2,hfour]
      have hpowK : (0:ℝ)<2^K := by positivity
      have hpowN : (0:ℝ)<2^N := by positivity
      have h1' : 2*((2:ℝ)^K-1)/((2:ℝ)^K)^2 ≤ 2/2^K := by
        apply (div_le_iff₀ (sq_pos_of_pos hpowK)).mpr
        field_simp
        nlinarith
      have h2' : (2/(2:ℝ)^K) * (2-2/2^N) ≤ 4/2^K := by
        calc _ ≤ (2/(2:ℝ)^K)*2 := mul_le_mul_of_nonneg_left (by have := (div_nonneg (by norm_num : (0:ℝ)≤2) hpowN.le); linarith) (by positivity)
             _ = _ := by ring
      calc _ ≤ 2/(2:ℝ)^K+4/2^K := add_le_add h1' h2'
           _ = _ := by ring

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

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_SubexponentialVolumes
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

namespace CriticalPercolation

lemma subexponential_enlargement (v : ℕ → ℕ) (hv : ∀ n, 0<v n)
    (hg : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N, Real.log (v n : ℝ) ≤ ε*n)
    (t R : ℕ) : ∃ n≥R, v (n+t) ≤ 2*v n := by
  by_contra! hbad
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  let ε := Real.log 2/(2*((t:ℝ)+1))
  have hd : 0<2*((t:ℝ)+1) := by positivity
  have hε : 0<ε := div_pos hc hd
  have hεeq : ε*(2*((t:ℝ)+1)) = Real.log 2 := div_mul_cancel₀ _ hd.ne'
  obtain ⟨N,hN⟩ := hg ε hε
  let n₀ := max R N
  have hnR : R≤n₀ := le_max_left _ _
  have hnN : N≤n₀ := le_max_right _ _
  have hstep (n : ℕ) (hn : R≤n) :
      Real.log (v n : ℝ)+Real.log 2 < Real.log (v (n+t) : ℝ) := by
    have hp : (0:ℝ)<v n := Nat.cast_pos.mpr (hv n)
    have hh : (2:ℝ)*(v n:ℝ) < (v (n+t):ℝ) := by exact_mod_cast hbad n hn
    have hl := Real.log_lt_log (mul_pos (by norm_num) hp) hh
    rwa [Real.log_mul (by norm_num) hp.ne',add_comm] at hl
  have hlow : ∀ k : ℕ, (k:ℝ)*Real.log 2 ≤ Real.log (v (n₀+k*t) : ℝ) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero,Nat.cast_zero,zero_mul]
      exact Real.log_nonneg (by exact_mod_cast hv n₀)
    | succ k ih =>
      have hs := hstep (n₀+k*t) (hnR.trans (Nat.le_add_right _ _))
      have he : n₀+(k+1)*t = n₀+k*t+t := by ring
      rw [he,Nat.cast_add,Nat.cast_one]
      nlinarith
  let k := n₀+1
  have hboth : (k:ℝ)*Real.log 2 ≤ ε*(n₀+k*t : ℕ) :=
    (hlow k).trans (hN _ (hnN.trans (Nat.le_add_right _ _)))
  have hnum : (k:ℝ)*(2*((t:ℝ)+1)) ≤ (n₀+k*t : ℕ) := by
    apply (mul_le_mul_iff_left₀ hc).mp
    calc
      _ = ((k:ℝ)*Real.log 2)*(2*((t:ℝ)+1)) := by ring
      _ ≤ (ε*(n₀+k*t : ℕ))*(2*((t:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right hboth hd.le
      _ = _ := by rw [mul_right_comm,hεeq]; ring
  dsimp only [k] at hnum
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hnum
  nlinarith [(Nat.cast_nonneg n₀ : (0:ℝ)≤n₀),(Nat.cast_nonneg t : (0:ℝ)≤t),mul_nonneg (Nat.cast_nonneg n₀ : (0:ℝ)≤n₀)
    (Nat.cast_nonneg t : (0:ℝ)≤t)]

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma subexponential_ball_enlargement (hlocal : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (o : V) (t R : ℕ) :
    ∃ n≥R, (G.vertexBall o (n+t)).ncard ≤ 2*(G.vertexBall o n).ncard := by
  apply subexponential_enlargement _ _ (hg o)
  intro n
  exact (Set.ncard_pos (G.vertexBall_finite hlocal o n)).mpr ⟨o,G.mem_vertexBall_self o n⟩

end BondGraph
end CriticalPercolation
end
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchTree
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

namespace CriticalPercolation

namespace SearchTree
variable {E R : Type*}

lemma reads_disjoint [DecidableEq E] (t : SearchTree E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : ∀ e ∈ t.reads ω, e ∉ used := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · by_cases he : ω e = true
      · have hm : f ∈ r.reads ω := by simpa [reads,he] using hf
        exact fun hx => hr _ h.2.2 _ hm (Finset.mem_insert_of_mem hx)
      · have hm : f ∈ l.reads ω := by simpa [reads,he] using hf
        exact fun hx => hl _ h.2.1 _ hm (Finset.mem_insert_of_mem hx)

lemma reads_nodup [DecidableEq E] (t : SearchTree E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : (t.reads ω).Nodup := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    rw [reads,List.nodup_cons]
    by_cases he : ω e = true
    · simp only [he,↓reduceIte]
      exact ⟨fun hm => reads_disjoint r _ h.2.2 ω e hm (Finset.mem_insert_self _ _), hr _ h.2.2⟩
    · simp only [he]
      exact ⟨fun hm => reads_disjoint l _ h.2.1 ω e hm (Finset.mem_insert_self _ _), hl _ h.2.1⟩
end SearchTree

end CriticalPercolation

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Delta
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ExpectClosedFlip
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
  · simp only [hc,not_true_eq_false,if_false]
  · simp only [hc,not_false_eq_true,if_true]
    exact congrArg (fun σ : Set E => p*f σ) (hup ω).symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_WeightedCauchy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical

namespace CriticalPercolation.FiniteEntropy
variable {X A : Type*} [Fintype X] [Fintype A]

lemma weighted_cauchy (w f g : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * f x * g x)^2 ≤ (∑ x, w x * (f x)^2) * ∑ x, w x * (g x)^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; apply le_of_eq; ring

end CriticalPercolation.FiniteEntropy

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

lemma twoClusterEvent_iff_endpoint [Fintype V] (ω : Set E) (u v : V) (s : ℕ) :
    ω ∈ G.twoClusterEvent u v s ↔ BinaryLaw.endpointEvent G u v s ω := by
  simp only [twoClusterEvent, Set.mem_inter_iff, Set.mem_ofPred_eq,
    clusterTail_iff_card, BinaryLaw.endpointEvent, and_assoc]

lemma finite_endpoint_prob [Fintype V] [Fintype E] (p : unitInterval) (u v : V) (s : ℕ) :
    FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
      (BinaryLaw.endpointEvent G u v s) = (G.law p).real (G.twoClusterEvent u v s) := by
  rw [law, ← BernoulliProduct.law_const, ← BernoulliProduct.prob_eq_real]
  congr 1
  funext ω
  exact propext (G.twoClusterEvent_iff_endpoint ω u v s).symm

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_WitnessEvents
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

namespace CriticalPercolation
namespace BernoulliProduct
variable {E : Type*}

lemma tendsto_real_inter_finiteWitness (p : unitInterval) (A B : Set (Set E))
    (hmono : IsUpperSet A) (hw : HasFiniteOpenWitness A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real (B ∩ {ω | K n ∩ ω ∈ A}))
      atTop (𝓝 ((law (fun _ : E => p)).real (B∩A))) := by
  have hm : Monotone (fun n => B ∩ {ω | K n ∩ ω ∈ A}) :=
    fun _ _ h => Set.inter_subset_inter_right _ (finiteWitness_exhaustion_mono A hmono K h)
  have h := tendsto_measure_iUnion_atTop (μ := law (fun _ : E => p)) hm
  rw [← Set.inter_iUnion,finiteWitness_exhaustion A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma witnessedTwoCluster_subset_restrict {K S : Set E} (hKS : K⊆S) (u v : V) (s : ℕ) :
    G.witnessedTwoCluster K u v s ⊆ {ω | S∩ω ∈ G.twoClusterEvent u v s} := by
  rintro ω ⟨hsep,hu,hv⟩
  refine ⟨⟨?_,G.clusterTail_isUpperSet u s (Set.inter_subset_inter_left _ hKS) hu⟩,
    G.clusterTail_isUpperSet v s (Set.inter_subset_inter_left _ hKS) hv⟩
  intro h
  exact hsep (G.cluster_mono Set.inter_subset_right u h)

lemma measurableSet_witnessedTwoCluster [Countable V] [Countable E]
    (K : Set E) (hK : K.Finite) (u v : V) (s : ℕ) :
    MeasurableSet (G.witnessedTwoCluster K u v s) :=
  (G.measurable_reachable u v).setOf.compl.inter
    (BernoulliProduct.measurableSet_restrict K hK _)

lemma tendsto_real_witnessedTwoCluster (p : unitInterval) (u v : V) (s : ℕ)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real (G.witnessedTwoCluster (K n) u v s)) atTop
      (𝓝 ((G.law p).real (G.twoClusterEvent u v s))) := by
  have ht := BernoulliProduct.tendsto_real_inter_finiteWitness p
    (G.clusterTail u s ∩ G.clusterTail v s) {ω | ¬(G.openGraph ω).Reachable u v}
    ((G.clusterTail_isUpperSet u s).inter (G.clusterTail_isUpperSet v s))
    ((G.clusterTail_hasFiniteOpenWitness u s).inter (G.clusterTail_hasFiniteOpenWitness v s)
      (G.clusterTail_isUpperSet u s) (G.clusterTail_isUpperSet v s)) K
  simpa only [witnessedTwoCluster,twoClusterEvent,Set.inter_assoc,law,
    ← BernoulliProduct.law_const] using ht

lemma exists_finite_witnessedTwoCluster [Countable E] (p : unitInterval) (u v : V) (s : ℕ)
    (hpos : 0 < (G.law p).real (G.twoClusterEvent u v s)) :
    ∃ K : Set E, K.Finite ∧ (G.law p).real (G.twoClusterEvent u v s)/2 ≤
      (G.law p).real (G.witnessedTwoCluster K u v s) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  obtain ⟨n,hn⟩ := ((G.tendsto_real_witnessedTwoCluster p u v s K).eventually
    (eventually_gt_nhds (by linarith : (G.law p).real (G.twoClusterEvent u v s)/2 <
      (G.law p).real (G.twoClusterEvent u v s)))).exists
  exact ⟨K n,K.finite n,hn.le⟩

lemma Aut.reachable_map (φ : G.Aut) (ω : Set E) (u v : V) :
    (G.openGraph (φ.edge '' ω)).Reachable (φ.vertex u) (φ.vertex v) ↔
      (G.openGraph ω).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)

lemma Aut.clusterTail_map (φ : G.Aut) (ω : Set E) (u : V) (s : ℕ) :
    φ.edge '' ω ∈ G.clusterTail (φ.vertex u) s ↔ ω ∈ G.clusterTail u s := by
  exact Set.ext_iff.mp (Aut.preimage_clusterTail G φ u s) ω

lemma Aut.witnessedTwoCluster_preimage (φ : G.Aut) (K : Set E) (u v : V) (s : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹'
      G.witnessedTwoCluster (φ.edge '' K) (φ.vertex u) (φ.vertex v) s =
        G.witnessedTwoCluster K u v s := by
  ext ω
  simp only [witnessedTwoCluster,Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [← Set.image_inter φ.edge.injective,Aut.reachable_map,
    Aut.clusterTail_map,Aut.clusterTail_map]

lemma Aut.witnessedTwoCluster_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (K : Set E) (hK : K.Finite) (u v : V) (s : ℕ) :
    (G.law p).real (G.witnessedTwoCluster (φ.edge '' K) (φ.vertex u) (φ.vertex v) s) =
      (G.law p).real (G.witnessedTwoCluster K u v s) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_witnessedTwoCluster _ (hK.image _) _ _ _),
    Aut.witnessedTwoCluster_preimage]

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BallIncidence
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

namespace CriticalPercolation

lemma sum_comp_le_fibre_bound {α β : Type*} (S : Finset α) (T : Finset β)
    (g : α → β) (f : β → ℝ) (L : ℕ) (hf : ∀ b, 0≤f b)
    (hmap : ∀ a∈S, g a∈T) (hL : ∀ b, (S.filter (fun a => g a=b)).card≤L) :
    ∑ a∈S, f (g a) ≤ (L:ℝ)*∑ b∈T, f b := by
  rw [Finset.sum_comp]
  calc
    _ ≤ ∑ b∈S.image g, (L:ℝ)*f b := by
      apply Finset.sum_le_sum
      intro b _
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hL b)) (hf b)
    _ ≤ ∑ b∈T, (L:ℝ)*f b := Finset.sum_le_sum_of_subset_of_nonneg
      (by rintro b hb; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb; exact hmap a ha)
      (fun b _ _ => mul_nonneg (Nat.cast_nonneg _) (hf b))
    _ = _ := (Finset.mul_sum _ _ _).symm

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_map (φ : G.Aut) {K : Set E} {S : Set V}
    (hKS : K⊆G.inducedEdges S) : φ.edge '' K ⊆ G.inducedEdges (φ.vertex '' S) := by
  rintro e ⟨a,ha,rfl⟩ v hv
  rw [φ.preserves] at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w,hKS ha w hw,rfl⟩

lemma translated_bonds_in_ball (o u v : V) (n C W : ℕ) (φ : G.Aut)
    (hv : v∈G.vertexBall o n) (hφ : φ.vertex u ∈ G.vertexBall v C)
    {K : Set E} (hK : K⊆G.inducedEdges (G.vertexBall u W)) :
    φ.edge '' K ⊆ G.inducedEdges (G.vertexBall o (n+C+W)) := by
  apply (Aut.inducedEdges_map G φ hK).trans
  apply G.inducedEdges_monotone
  rw [Aut.vertexBall_image]
  exact G.vertexBall_add (G.vertexBall_add hv C hφ) W

lemma orbit_edge_fibre_bound (hlocal : G.LocallyFinite) (C M : ℕ)
    (hM : ∀ v, (G.vertexBall v C).ncard≤M) (u : V) (e : E) (hu : u∈G.ends e)
    (φ : V → G.Aut) (hφ : ∀ v, (φ v).vertex u ∈ G.vertexBall v C)
    (S : Finset V) (f : E) : (S.filter (fun v => (φ v).edge e=f)).card ≤ 2*M := by
  have hsub : (↑(S.filter (fun v => (φ v).edge e=f)) : Set V) ⊆
      G.vertexBall (G.ends f).out.1 C ∪ G.vertexBall (G.ends f).out.2 C := by
    intro v hv
    have he : (φ v).edge e=f := (Finset.mem_filter.mp hv).2
    have hm : (φ v).vertex u ∈ G.ends f := by
      rw [← he,(φ v).preserves]
      exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
    rw [(G.ends f).out_eq.symm,Sym2.mem_iff] at hm
    have hd := (G.vertexBall_comm).mp (hφ v)
    exact hm.elim (fun h => Or.inl (h ▸ hd)) (fun h => Or.inr (h ▸ hd))
  have hc := Set.ncard_le_ncard hsub
    ((G.vertexBall_finite hlocal _ C).union (G.vertexBall_finite hlocal _ C))
  simp only [Set.ncard_coe_finset] at hc
  have hh := Set.ncard_union_le (G.vertexBall (G.ends f).out.1 C)
    (G.vertexBall (G.ends f).out.2 C)
  exact hc.trans (hh.trans (by have h1 := hM (G.ends f).out.1; have h2 := hM (G.ends f).out.2; omega))

end BondGraph
end CriticalPercolation
end
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
lemma cluster_disjoint_of_not_reachable {ω : Set E} {u v : V}
    (h : ¬ (G.openGraph ω).Reachable u v) : Disjoint (G.cluster ω u) (G.cluster ω v) := by
  apply Set.disjoint_left.mpr
  intro z hu hv
  exact h (hu.trans hv.symm)

lemma clusterSize_pos (ω : Set E) (v : V) : 0 < G.clusterSize ω v := by
  apply Finset.card_pos.mpr
  exact ⟨v, Set.mem_toFinset.mpr (SimpleGraph.Reachable.refl _)⟩

lemma clusterSize_eq_of_reachable {ω : Set E} {u v : V}
    (h : (G.openGraph ω).Reachable u v) : G.clusterSize ω u = G.clusterSize ω v := by
  unfold clusterSize
  rw [G.cluster_eq_of_reachable h]

lemma sum_rootMass_cluster (f : ℕ → ℝ) (ω : Set E) (u : V) :
    (∑ v, if (G.openGraph ω).Reachable u v then G.rootMass f ω v else 0) =
      f (G.clusterSize ω u) := by
  have he : (fun v => if (G.openGraph ω).Reachable u v then G.rootMass f ω v else 0) =
      (fun v => if v ∈ G.cluster ω u then G.rootMass f ω u else 0) := by
    funext v
    by_cases hv : (G.openGraph ω).Reachable u v
    · simp only [cluster, Set.mem_ofPred_eq, hv,if_true,rootMass,
        G.clusterSize_eq_of_reachable hv]
    · simp [cluster,hv]
  rw [he,Finset.sum_ite]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_zero,add_zero]
  have hfilter : Finset.univ.filter (fun v => v ∈ G.cluster ω u) = (G.cluster ω u).toFinset := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset]
  rw [hfilter]
  change (G.clusterSize ω u : ℝ) * (f (G.clusterSize ω u) / G.clusterSize ω u) = _
  field_simp [show (G.clusterSize ω u : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (G.clusterSize_pos ω u).ne']

omit [Fintype V] in
lemma incident_cluster_iff (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y)) (v : V) :
    e ∈ G.incidentEdges (G.cluster ω v) ↔
      (G.openGraph ω).Reachable x v ∨ (G.openGraph ω).Reachable y v := by
  constructor
  · rintro ⟨z,hz,hze⟩
    rw [he] at hze
    rcases (by simpa using hze : z=x ∨ z=y) with rfl|rfl
    · exact Or.inl hz.symm
    · exact Or.inr hz.symm
  · rintro (hx|hy)
    · exact ⟨x,hx.symm,by simp [he]⟩
    · exact ⟨y,hy.symm,by simp [he]⟩

lemma sum_incident_rootMass (f : ℕ → ℝ) (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) :
    (∑ v, if e ∈ G.incidentEdges (G.cluster ω v) then G.rootMass f ω v else 0) =
      f (G.clusterSize ω x) + if (G.openGraph ω).Reachable x y then 0 else f (G.clusterSize ω y) := by
  simp_rw [G.incident_cluster_iff ω e x y he]
  by_cases hxy : (G.openGraph ω).Reachable x y
  · have hi : ∀ v, ((G.openGraph ω).Reachable x v ∨ (G.openGraph ω).Reachable y v) ↔
          (G.openGraph ω).Reachable x v := fun v =>
        ⟨fun h => h.elim id (fun hy => hxy.trans hy), Or.inl⟩
    simp_rw [hi]
    rw [G.sum_rootMass_cluster,ite_eq_left hxy,add_zero]
  · have hi : ∀ v, (if (G.openGraph ω).Reachable x v ∨ (G.openGraph ω).Reachable y v
          then G.rootMass f ω v else 0) =
        (if (G.openGraph ω).Reachable x v then G.rootMass f ω v else 0) +
        (if (G.openGraph ω).Reachable y v then G.rootMass f ω v else 0) := by
      intro v
      by_cases hx : (G.openGraph ω).Reachable x v <;>
        by_cases hy : (G.openGraph ω).Reachable y v <;> simp [hx,hy]
      exact (hxy (hx.trans hy.symm)).elim
    simp_rw [hi]
    rw [Finset.sum_add_distrib,G.sum_rootMass_cluster,G.sum_rootMass_cluster,ite_eq_right hxy]

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

lemma clusterSize_insert_of_disconnected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : ¬ (G.openGraph ω).Reachable x y) :
    G.clusterSize (insert e ω) x = G.clusterSize ω x + G.clusterSize ω y := by
  unfold clusterSize
  rw [G.cluster_insert_endpoint ω e x y he,Set.toFinset_union,Finset.card_union_of_disjoint]
  exact Set.disjoint_toFinset.mpr (G.cluster_disjoint_of_not_reachable hxy)

lemma clusterSize_insert_of_connected (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : (G.openGraph ω).Reachable x y) :
    G.clusterSize (insert e ω) x = G.clusterSize ω x := by
  unfold clusterSize
  rw [G.cluster_insert_endpoint ω e x y he,G.cluster_eq_of_reachable hxy,Set.union_self]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_CappedDiscrepancy
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

namespace BondGraph
open FiniteProduct

variable {V E : Type*} [Fintype V] (G : BondGraph V E)

lemma edgeClusterMass_insert_gap (f : ℕ → ℝ) (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) :
    G.edgeClusterMass f ω e - G.edgeClusterMass f (insert e ω) e =
      if (G.openGraph ω).Reachable x y then 0 else
        f (G.clusterSize ω x) + f (G.clusterSize ω y) -
          f (G.clusterSize ω x + G.clusterSize ω y) := by
  have hopen : (G.openGraph (insert e ω)).Reachable x y :=
    LazyDFS.prop_openEdge_reachable G (insert e ω) (Set.mem_insert e ω) he
  simp only [edgeClusterMass,G.sum_incident_rootMass f ω e x y he,
    G.sum_incident_rootMass f (insert e ω) e x y he,ite_eq_left hopen,add_zero]
  by_cases hc : (G.openGraph ω).Reachable x y
  · rw [ite_eq_left hc,G.clusterSize_insert_of_connected ω e x y he hc]
    simp only [ite_eq_left hc,add_zero,sub_self]
  · rw [ite_eq_right hc,G.clusterSize_insert_of_disconnected ω e x y he hc,ite_eq_right hc]

lemma capped_edge_gap (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y))
    (s : ℕ) (hs : 0 < s) :
    (if BinaryLaw.endpointEvent G x y s ω then (1:ℝ) else 0) ≤
      G.edgeClusterMass (cappedMass s) ω e - G.edgeClusterMass (cappedMass s) (insert e ω) e := by
  rw [G.edgeClusterMass_insert_gap _ ω e x y he]
  by_cases hc : (G.openGraph ω).Reachable x y
  · simp [BinaryLaw.endpointEvent,hc]
  · have hh := cappedMass_gap s (G.clusterSize ω x) (G.clusterSize ω y) hs
    simp only [BinaryLaw.endpointEvent,hc,not_false_eq_true,true_and,if_false,clusterSize,
      ← Set.ncard_eq_toFinset_card'] at hh ⊢
    exact hh

variable [Fintype E]

lemma expect_edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    expect w (fun ω => G.edgeDiscrepancy f p ω e) =
      expect w (fun ω => if ¬ω e then
        G.edgeClusterMass f ω e - G.edgeClusterMass f (insert e ω) e else 0) := by
  let : DecidableEq E := Classical.decEq E
  have hflip := expect_closed_flip_decidable w hw e hp h0 h1 (fun ω => G.edgeClusterMass f ω e / p)
  have hu (ω : Set E) : {a | Function.update ω e True a} = insert e ω := by
    ext a
    change Function.update (fun a => ω a) e True a ↔ a=e ∨ a∈ω
    by_cases ha : a=e
    · subst a; simp [Function.update]
    · simp only [Function.update_of_ne ha,ha,false_or]; rfl
  have hleft : (fun ω : Set E => if ¬ω e then p*(G.edgeClusterMass f (Function.update ω e True) e / p) else 0) =
      (fun ω => if ¬ω e then G.edgeClusterMass f (insert e ω) e else 0) := by
    funext ω
    rw [show (Function.update ω e True : Set E) = insert e ω from hu ω]
    split_ifs <;> field_simp [hp.1.ne']
  erw [hleft] at hflip
  have heq (ω : Set E) : G.edgeDiscrepancy f p ω e =
      (if ¬ω e then G.edgeClusterMass f ω e else 0) -
        (if ω e then (1-p)*(G.edgeClusterMass f ω e / p) else 0) := by
    change (if ω e then -(1-p)/p else 1) * G.edgeClusterMass f ω e = _
    by_cases hb : ω e <;> simp only [hb,if_true,if_false,not_true_eq_false,not_false_eq_true,sub_zero,zero_sub,one_mul]
    ring
  have hfunc : (fun ω : Set E => G.edgeDiscrepancy f p ω e) =
      (fun ω => (if ¬ω e then G.edgeClusterMass f ω e else 0) -
        (if ω e then (1-p)*(G.edgeClusterMass f ω e / p) else 0)) := funext heq
  erw [hfunc]
  erw [expect_sub,← hflip,← expect_sub]
  congr 1
  funext ω
  by_cases hb : ω e <;> simp [hb]

lemma endpoint_prob_le_discrepancy (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (e : E) (x y : V) (he : G.ends e = s(x,y))
    (h0 : w e False=1-p) (h1 : w e True=p) (s : ℕ) (hs : 0 < s) :
    prob w (BinaryLaw.endpointEvent G x y s) ≤
      expect w (fun ω => G.edgeDiscrepancy (cappedMass s) p ω e) := by
  rw [G.expect_edgeDiscrepancy _ p hp w hw e h0 h1]
  apply expect_mono hn
  intro ω
  by_cases hb : ω e
  · have hconn : (G.openGraph ω).Reachable x y := LazyDFS.prop_openEdge_reachable G ω hb he
    simp [hb,BinaryLaw.endpointEvent,hconn]
  · simp only [hb,not_false_eq_true,if_true]
    exact G.capped_edge_gap ω e x y he s hs

lemma sum_edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (ω : Set E) :
    (∑ e, G.edgeDiscrepancy f p ω e) =
      ∑ v, G.rootMass f ω v * G.clusterDiscrepancy p ω v := by
  simp only [edgeDiscrepancy,edgeClusterMass,clusterDiscrepancy,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring

end BondGraph
end CriticalPercolation
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

omit [Fintype E] in
lemma rootMass_capped_eq (s : ℕ) (hs : 0 < s) (ω : Set E) (v : V) :
    G.rootMass (cappedMass s) ω v = min (1/(s:ℝ)) (1/(G.clusterSize ω v : ℝ)) := by
  have hm : (0:ℝ)<G.clusterSize ω v := Nat.cast_pos.mpr (G.clusterSize_pos ω v)
  have hs' : (0:ℝ) < s := Nat.cast_pos.mpr hs
  unfold rootMass cappedMass
  by_cases hms : (G.clusterSize ω v : ℝ)/s ≤ 1
  · rw [min_eq_left hms,min_eq_left]
    · field_simp
    · apply (div_le_div_iff₀ hs' hm).mpr
      have hh := (div_le_one hs').mp hms
      simpa only [one_mul] using hh
  · have hh : (s:ℝ) ≤ G.clusterSize ω v := by
      have hh := le_of_lt (lt_of_not_ge hms)
      exact (one_le_div hs').mp hh
    rw [min_eq_right (le_of_lt (lt_of_not_ge hms)),min_eq_right]
    apply (div_le_div_iff₀ hm hs').mpr
    simpa only [one_mul] using hh

omit [Fintype E] in
lemma capped_root_le_normalized (s T D : ℕ) (hs : 0 < s) (hT : 0<T) (hD : 1≤D)
    (ω : Set E) (v : V) (hTD : T ≤ D*G.clusterSize ω v) :
    G.rootMass (cappedMass s) ω v ≤ (D:ℝ)*min (1/(s:ℝ)) (1/(T:ℝ)) := by
  rw [G.rootMass_capped_eq s hs ω v,mul_min_of_nonneg _ _ (Nat.cast_nonneg D)]
  apply le_min
  · calc min (1/(s:ℝ)) (1/(G.clusterSize ω v : ℝ)) ≤ 1/(s:ℝ) := min_le_left _ _
         _ ≤ (D:ℝ)*(1/(s:ℝ)) := by
           exact le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.mpr hD)
  · calc min (1/(s:ℝ)) (1/(G.clusterSize ω v : ℝ)) ≤ 1/(G.clusterSize ω v : ℝ) := min_le_right _ _
         _ ≤ (D:ℝ)*(1/(T:ℝ)) := by
           rw [mul_one_div]
           apply (div_le_div_iff₀ (Nat.cast_pos.mpr (G.clusterSize_pos ω v)) (Nat.cast_pos.mpr hT)).mpr
           simpa only [one_mul,Nat.cast_mul] using (Nat.cast_le.mpr hTD : (T:ℝ)≤ (D*G.clusterSize ω v : ℕ))

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

lemma truncate_valid [DecidableEq E] (t : SearchTree E R) (n : ℕ) (used : Finset E)
    (h : t.Valid used) : (t.truncate n).Valid used := by
  induction n generalizing t used with
  | zero => simp [truncate,Valid]
  | succ n ih =>
    cases t with
    | done r => trivial
    | ask e l r => exact ⟨h.1, ih l _ h.2.1, ih r _ h.2.2⟩

lemma queryCount_truncate_le (t : SearchTree E R) (n : ℕ) (ω : E → Prop) :
    (t.truncate n).queryCount ω ≤ n := by
  induction n generalizing t with
  | zero => simp [truncate,queryCount]
  | succ n ih =>
    cases t with
    | done r => simp [truncate,queryCount]
    | ask e l r =>
      simp only [truncate,queryCount]
      split_ifs <;> have := ih r <;> have := ih l <;> omega

lemma centeredSum_truncate_eq (t : SearchTree E R) (n : ℕ) (ω : E → Prop)
    (h : t.queryCount ω ≤ n) (p : ℝ) :
    (t.truncate n).centeredSum p ω = t.centeredSum p ω := by
  induction n generalizing t with
  | zero =>
    cases t with
    | done r => rfl
    | ask e l r => simp [queryCount] at h
  | succ n ih =>
    cases t with
    | done r => rfl
    | ask e l r =>
      by_cases he : ω e
      · simp only [queryCount,ite_eq_left he] at h
        simp only [truncate,centeredSum,ite_eq_left he]
        rw [ih r (by omega)]
      · simp only [queryCount,ite_eq_right he] at h
        simp only [truncate,centeredSum,ite_eq_right he]
        rw [ih l (by omega)]

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

lemma truncated_second_le (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : LazyDFS.Fresh w p used) (n : ℕ) :
    expect w (fun ω => ((t.truncate n).centeredSum p ω)^2) ≤ p*(1-p)*n := by
  rw [(t.truncate n).centeredSum_moments used (t.truncate_valid n used ht) p w hw hf |>.2]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  calc expect w (fun ω => ((t.truncate n).queryCount ω : ℝ)) ≤ expect w (fun _ => (n:ℝ)) :=
        expect_mono hn (fun ω => Nat.cast_le.mpr (t.queryCount_truncate_le n ω))
       _ = n := expect_const w hw _

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryBand
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_abs_sq_le (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) :
    (expect w (fun ω => |f ω|))^2 ≤ expect w (fun ω => (f ω)^2) := by
  have h := FiniteEntropy.weighted_cauchy (density w) (fun ω => |f ω|) (fun _ => 1)
    (fun ω => density_nonneg hn ω)
  simp only [mul_one,one_pow,sq_abs] at h
  have hw1 : ∑ ω, density w ω = 1 := by
    simpa only [expect,mul_one] using expect_const w hw (1:ℝ)
  simpa only [hw1,mul_one,expect] using h

lemma expect_abs_le_of_second_le (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) {a : ℝ} (ha : 0≤a)
    (hf : expect w (fun ω => (f ω)^2) ≤ a^2) : expect w (fun ω => |f ω|) ≤ a := by
  nlinarith [expect_abs_sq_le w hw hn f]

end CriticalPercolation.FiniteProduct
namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*}

lemma queryCount_eq_reads_length (t : SearchTree E R) (ω : E → Prop) :
    t.queryCount ω = (t.reads (fun e => decide (ω e))).length := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    by_cases he : ω e <;> simp [queryCount,reads,he,hl,hr,Nat.add_comm]

lemma centeredSum_eq_zero_of_count (t : SearchTree E R) (ω : E → Prop)
    (h : t.queryCount ω = 0) (p : ℝ) : t.centeredSum p ω = 0 := by
  cases t with
  | done r => rfl
  | ask e l r => simp [queryCount] at h

variable [Fintype E] [DecidableEq E]

lemma queryCount_le_card (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (ω : E → Prop) : t.queryCount ω ≤ Fintype.card E := by
  rw [queryCount_eq_reads_length]
  exact List.Nodup.length_le_card (t.reads_nodup used ht _)

lemma band_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (k : ℕ) :
    expect w (fun ω => if 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1)
      then |t.centeredSum p ω| else 0) ≤ (2:ℝ)^(k+1) := by
  calc
    _ ≤ expect w (fun ω => |(t.truncate (4^(k+1))).centeredSum p ω|) := by
      apply expect_mono hn
      intro ω
      split_ifs with h
      · rw [t.centeredSum_truncate_eq _ ω h.2.le p]
      · exact abs_nonneg _
    _ ≤ (2:ℝ)^(k+1) := by
      apply expect_abs_le_of_second_le w hw hn _ (by positivity)
      have ht' := t.truncated_second_le used ht p hp w hw hn hf (4^(k+1))
      have hpp : p*(1-p) ≤ 1 := by nlinarith [hp.2,sq_nonneg p]
      have hN : (4^(k+1) : ℝ) = ((2:ℝ)^(k+1))^2 := by
        rw [← pow_mul, mul_comm (k+1) 2, pow_mul]
        norm_num
      calc _ ≤ p*(1-p)*(4^(k+1) : ℕ) := ht'
           _ ≤ (4^(k+1) : ℝ) := by
             simpa using mul_le_mul_of_nonneg_right hpp (by positivity : 0≤(4^(k+1):ℝ))
           _ = _ := hN

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryNormalized
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

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma normalized_centered_bound (t : SearchTree E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (K : ℕ) :
    expect w (fun ω => |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) ≤ 6/(2:ℝ)^K := by
  let N := Fintype.card E + 1
  let a (k : ℕ) := min (1/(4:ℝ)^K) (1/(4:ℝ)^k)
  let b (k : ℕ) (ω : E → Prop) :=
    if 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1)
      then |t.centeredSum p ω| else 0
  have ha (k : ℕ) : 0≤a k := by dsimp [a]; positivity
  have hb (k : ℕ) (ω : E → Prop) : 0≤b k ω := by
    dsimp [b]; split_ifs <;> positivity
  have hpoint (ω : E → Prop) : |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) ≤
        ∑ k ∈ Finset.range N, b k ω * a k := by
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p,abs_zero,zero_mul]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hb k ω) (ha k))
    · let k := Nat.log 4 (t.queryCount ω)
      have hklo : 4^k ≤ t.queryCount ω := Nat.pow_log_le_self 4 hT
      have hkhi : t.queryCount ω < 4^(k+1) := Nat.lt_pow_succ_log_self (by omega) _
      have hkN : k ∈ Finset.range N := by
        apply Finset.mem_range.mpr
        have h1 := Nat.log_le_self 4 (t.queryCount ω)
        have h2 := t.queryCount_le_card used ht ω
        dsimp [k,N]
        omega
      calc
        _ ≤ b k ω * a k := by
          have hband : 4^k ≤ t.queryCount ω ∧ t.queryCount ω < 4^(k+1) := ⟨hklo,hkhi⟩
          simp only [b,ite_eq_left hband]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply min_le_min le_rfl
          apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(4:ℝ)^k)
          exact_mod_cast hklo
        _ ≤ _ := Finset.single_le_sum (fun j _ => mul_nonneg (hb j ω) (ha j)) hkN
  calc
    _ ≤ expect w (fun ω => ∑ k ∈ Finset.range N, b k ω * a k) := expect_mono hn hpoint
    _ = ∑ k ∈ Finset.range N, expect w (b k) * a k := by
      simp only [expect,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ k ∈ Finset.range N, (2:ℝ)^(k+1)*a k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (t.band_centered_bound used ht p hp w hw hn hf k) (ha k)
    _ = ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [a]
      rw [mul_min_of_nonneg _ _ (by positivity)]
      simp only [mul_one_div]
    _ ≤ _ := dyadic_sum_bound N K

end CriticalPercolation.SearchTree
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_FiniteAdjacent
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
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma clusterDiscrepancy_eq_centered (p : ℝ) (hp : p≠0) (ω : Set E) (v : V) :
    G.clusterDiscrepancy p ω v = -(IncidenceSearch.tree G v).centeredSum p ω / p := by
  rw [IncidenceSearch.tree_centered,clusterDiscrepancy,← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  change (if e∈G.incidentEdges (G.cluster ω v) then
      (if e∈ω then -(1-p)/p else 1) else 0) =
    -(if e∈G.incidentEdges (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0)/p
  by_cases he : e∈G.incidentEdges (G.cluster ω v)
  · by_cases hω : e∈ω <;> simp [he,hω,hp]
  · simp [he]

lemma root_discrepancy_bound (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p ∅) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D) (K : ℕ) (v : V) :
    expect w (fun ω => G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) ≤
      (D:ℝ)/p*(6/(2:ℝ)^K) := by
  let t := IncidenceSearch.tree G v
  have hwel : ∀ ω : Set E, G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v| ≤
      (D:ℝ)/p * (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := by
    intro ω
    rw [G.clusterDiscrepancy_eq_centered p hp.1.ne' ω v,abs_div,abs_neg,abs_of_pos hp.1]
    change G.rootMass (cappedMass (4^K)) ω v * (|t.centeredSum p ω|/p) ≤ _
    by_cases hT : t.queryCount ω = 0
    · rw [t.centeredSum_eq_zero_of_count ω hT p]
      simp
    · have hTD : t.queryCount ω ≤ D*G.clusterSize ω v := by
        rw [IncidenceSearch.tree_count]
        simpa only [clusterSize,mul_comm] using G.incident_card_le (G.cluster ω v) D hD
      have hh := G.capped_root_le_normalized (4^K) (t.queryCount ω) D
        (by positivity) (Nat.pos_of_ne_zero hT) hDpos ω v hTD
      have hh' : G.rootMass (cappedMass (4^K)) ω v ≤ (D:ℝ)*
          min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
      calc
        _ ≤ ((D:ℝ)*min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) *
            (|t.centeredSum p ω|/p) := mul_le_mul_of_nonneg_right hh'
              (div_nonneg (abs_nonneg _) hp.1.le)
        _ = _ := by ring
  calc
    _ ≤ expect w (fun ω => (D:ℝ)/p *
        (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ)))) := by
      exact expect_mono hn (fun ω => hwel ω)
    _ = (D:ℝ)/p * expect w (fun ω =>
        |t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.queryCount ω : ℝ))) := expect_const_mul _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (t.normalized_centered_bound ∅ (IncidenceSearch.tree_valid G v) p
        ⟨hp.1.le,hp.2.le⟩ w hw hn hf K) (div_nonneg (Nat.cast_nonneg D) hp.1.le)

theorem finite_averaged_adjacent (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).toFinset.card ≤ D)
    (x y : E → V) (he : ∀ e, G.ends e = s(x e,y e)) (K : ℕ) :
    (∑ e, prob w (BinaryLaw.endpointEvent G (x e) (y e) (4^K))) ≤
      (Fintype.card V : ℝ)*((D:ℝ)/p*(6/(2:ℝ)^K)) := by
  have hf : LazyDFS.Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  calc
    _ ≤ ∑ e, expect w (fun ω => G.edgeDiscrepancy (cappedMass (4^K)) p ω e) := by
      apply Finset.sum_le_sum
      intro e _
      exact G.endpoint_prob_le_discrepancy p hp w hw hn e (x e) (y e) (he e)
        (h0 e) (h1 e) (4^K) (by positivity)
    _ = expect w (fun ω => ∑ v, G.rootMass (cappedMass (4^K)) ω v * G.clusterDiscrepancy p ω v) := by
      erw [← expect_sum]
      congr 1
      funext ω
      exact G.sum_edgeDiscrepancy _ p ω
    _ ≤ expect w (fun ω => ∑ v, G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) := by
      apply expect_mono hn
      intro ω
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left (le_abs_self _)
      exact div_nonneg (cappedMass_nonneg _ _) (Nat.cast_nonneg _)
    _ = ∑ v, expect w (fun ω => G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) := by
      erw [expect_sum]
    _ ≤ ∑ _v : V, (D:ℝ)/p*(6/(2:ℝ)^K) := by
      exact Finset.sum_le_sum (fun v _ => G.root_discrepancy_bound p hp w hw hn hf D hDpos hD K v)
    _ = _ := by simp

end BondGraph
end CriticalPercolation
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

lemma induce_twoClusterEvent (S : Set V) (ω : Set (G.inducedEdges S)) (u v : S) (n : ℕ) :
    ω ∈ (G.induce S).twoClusterEvent u v n ↔
      Subtype.val '' ω ∈ G.twoClusterEvent u.val v.val n := by
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.induce_reachable,G.induce_clusterTail]

lemma induce_law_event (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (A : Set (Set E)) :
    ((G.induce S).law p).real {ω | Subtype.val '' ω ∈ A} =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ A} := by
  simpa only [law,← BernoulliProduct.law_const] using
    (BernoulliProduct.real_law_restrict p (G.inducedEdges S) hS A).symm

lemma induce_twoCluster_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (u v : S) (n : ℕ) :
    ((G.induce S).law p).real ((G.induce S).twoClusterEvent u v n) =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.twoClusterEvent u.val v.val n} := by
  have he : (G.induce S).twoClusterEvent u v n =
      {ω | Subtype.val '' ω ∈ G.twoClusterEvent u.val v.val n} := by
    ext ω
    exact G.induce_twoClusterEvent S ω u v n
  rw [he,G.induce_law_event S hS]

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

lemma finite_averaged_adjacent_measure [Fintype V] [Fintype E]
    (p : unitInterval) (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (x y : E → V) (he : ∀ e, G.ends e = s(x e,y e)) (K : ℕ) :
    (∑ e, (G.law p).real (G.twoClusterEvent (x e) (y e) (4^K))) ≤
      (Fintype.card V : ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  have h := G.finite_averaged_adjacent p hp (fun _ : E => BernoulliProduct.bitWeight p)
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ => by simp [BernoulliProduct.bitWeight])
    (fun _ => by simp [BernoulliProduct.bitWeight]) D hDpos
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) x y he K
  simpa only [G.finite_endpoint_prob] using h

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

lemma induced_averaged_adjacent (hlocal : G.LocallyFinite)
    (p : unitInterval) (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (S : Set V) (hS : S.Finite) (K : ℕ) :
    ∑ e ∈ (G.finite_inducedEdges hlocal hS).toFinset,
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈
        G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)} ≤
      (S.ncard : ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  let x (e : G.inducedEdges S) : S := ⟨(G.ends e.val).out.1,e.property _ (Sym2.out_fst_mem _)⟩
  let y (e : G.inducedEdges S) : S := ⟨(G.ends e.val).out.2,e.property _ (Sym2.out_snd_mem _)⟩
  have he (e : G.inducedEdges S) : (G.induce S).ends e = s(x e,y e) := by
    apply (G.induce_ends_eq S e (x e) (y e)).mpr
    exact (G.ends e.val).out_eq.symm
  have hh := (G.induce S).finite_averaged_adjacent_measure p hp D hDpos
    (G.induce_incident_bound hlocal D hD S) x y he K
  simp_rw [G.induce_twoCluster_real S (G.finite_inducedEdges hlocal hS)] at hh
  rw [Finset.sum_subtype (G.finite_inducedEdges hlocal hS).toFinset
    (fun e => (G.finite_inducedEdges hlocal hS).mem_toFinset)]
  simpa only [x,y,Set.ncard_eq_toFinset_card',Set.toFinset_card] using hh

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_InfiniteAdjacent
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma adjacent_bound_of_geometry (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (C M D : ℕ) (hM : ∀ v, (G.vertexBall v C).ncard≤M)
    (hDpos : 1≤D) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hdense : ∀ u v, ∃ φ : G.Aut, φ.vertex u ∈ G.vertexBall v C)
    (p : unitInterval) (hp : (p:ℝ)∈Set.Ioo 0 1) (e : E) (K : ℕ) :
    (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
      8*(M:ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  let a := (G.ends e).out.1
  let b := (G.ends e).out.2
  let δ := (G.law p).real (G.twoClusterEvent a b (4^K))
  let Q := (D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)
  have hQ : 0≤Q := by
    dsimp [Q]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hp.1.le) (by positivity)
  change δ ≤ 8*(M:ℝ)*Q
  by_cases hδ : 0<δ
  swap
  · exact (not_lt.mp hδ).trans (by positivity)
  obtain ⟨J,hJ,hJmass⟩ := G.exists_finite_witnessedTwoCluster p a b (4^K) hδ
  obtain ⟨W,hW⟩ := G.finite_bonds_in_ball hconnected a (hJ.insert e)
  have hJW : J⊆G.inducedEdges (G.vertexBall a W) := fun f hf => hW (Or.inr hf)
  have heW : e∈G.inducedEdges (G.vertexBall a W) := hW (Or.inl rfl)
  choose φ hφ using hdense a
  obtain ⟨n,_,hn⟩ := G.subexponential_ball_enlargement hlocal hg a (C+W) 0
  let B := G.vertexBall a n
  let S := G.vertexBall a (n+C+W)
  have hBf : B.Finite := G.vertexBall_finite hlocal a n
  have hSf : S.Finite := G.vertexBall_finite hlocal a _
  have hEf := G.finite_inducedEdges hlocal hSf
  let q (f : E) := (G.law p).real {ω | G.inducedEdges S∩ω ∈
    G.twoClusterEvent (G.ends f).out.1 (G.ends f).out.2 (4^K)}
  have hq : ∀ f, 0≤q f := fun _ => measureReal_nonneg
  have hmap : ∀ v∈hBf.toFinset, (φ v).edge e∈hEf.toFinset := by
    intro v hv
    apply hEf.mem_toFinset.mpr
    exact G.translated_bonds_in_ball a a v n C W (φ v) (hBf.mem_toFinset.mp hv)
      (hφ v) (Set.singleton_subset_iff.mpr heW) ⟨e,rfl,rfl⟩
  have hvbound : ∀ v∈hBf.toFinset, δ/2≤q ((φ v).edge e) := by
    intro v hv
    have hsub := G.translated_bonds_in_ball a a v n C W (φ v)
      (hBf.mem_toFinset.mp hv) (hφ v) hJW
    have hm := measureReal_mono (G.witnessedTwoCluster_subset_restrict hsub
      ((φ v).vertex a) ((φ v).vertex b) (4^K)) (μ := G.law p)
    rw [Aut.witnessedTwoCluster_real G (φ v) p J hJ a b (4^K)] at hm
    have hend : s((φ v).vertex a,(φ v).vertex b) =
        s((G.ends ((φ v).edge e)).out.1,(G.ends ((φ v).edge e)).out.2) := by
      calc
        _ = G.ends ((φ v).edge e) := by
          rw [(φ v).preserves,(G.ends e).out_eq.symm,Sym2.map_mk]
        _ = _ := (G.ends ((φ v).edge e)).out_eq.symm
    rw [G.twoClusterEvent_sym2 hend (4^K)] at hm
    exact hJmass.trans hm
  have hfib := G.orbit_edge_fibre_bound hlocal C M hM a e (Sym2.out_fst_mem _)
    φ hφ hBf.toFinset
  have havg := G.induced_averaged_adjacent hlocal p hp D hDpos hD S hSf K
  change (∑ f∈hEf.toFinset, q f) ≤ (S.ncard:ℝ)*Q at havg
  have hratio : S.ncard≤2*B.ncard := by simpa only [S,B,Nat.add_assoc] using hn
  have hsum : (B.ncard:ℝ)*(δ/2) ≤ (B.ncard:ℝ)*(4*(M:ℝ)*Q) := by
    calc
      _ = ∑ v∈hBf.toFinset, δ/2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Set.ncard_eq_toFinset_card B hBf]
      _ ≤ ∑ v∈hBf.toFinset, q ((φ v).edge e) := Finset.sum_le_sum hvbound
      _ ≤ (2*M:ℕ)*∑ f∈hEf.toFinset, q f :=
        sum_comp_le_fibre_bound hBf.toFinset hEf.toFinset (fun v => (φ v).edge e) q
          (2*M) hq hmap hfib
      _ ≤ (2*M:ℕ)*((S.ncard:ℝ)*Q) :=
        mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg _)
      _ ≤ (2*M:ℕ)*(((2*B.ncard:ℕ):ℝ)*Q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hratio) hQ) (Nat.cast_nonneg _)
      _ = _ := by push_cast; ring
  have hBpos : (0:ℝ)<B.ncard := Nat.cast_pos.mpr (G.vertexBall_ncard_pos hlocal a n)
  have hh := (mul_le_mul_iff_right₀ hBpos).mp hsum
  linarith

theorem subexponential_adjacent_bound_bs_oai (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) :
    ∃ A : ℝ, 0<A ∧ ∀ (p : unitInterval), (p:ℝ)∈Set.Ioo 0 1 → ∀ (e : E) (K : ℕ),
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
        A/((p:ℝ)*(2:ℝ)^K) := by
  obtain ⟨C,hC⟩ := G.uniform_orbit_density_radius hconnected hquasi
  obtain ⟨M,hMpos,hM⟩ := G.uniform_positive_ball_bound hquasi C
  obtain ⟨D,hDpos,hD⟩ := G.uniform_incident_bound hquasi
  have hm : (0:ℝ)<M := by exact_mod_cast hMpos
  have hd : (0:ℝ)<D := by exact_mod_cast hDpos
  refine ⟨48*(M:ℝ)*D, by positivity, ?_⟩
  intro p hp e K
  have hh := G.adjacent_bound_of_geometry hconnected hlocal hg C M D hM hDpos hD hC p hp e K
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.subexponential_adjacent_bound_bs_oai.{u_1, u_2}
