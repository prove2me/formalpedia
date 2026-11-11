-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:52.031339+00:00
-- url     : https://prove2.me/submissions/f6fe227d-1725-45fc-a0ec-014cc8290a9f

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_atMostOneHeavy_critical_ae
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_criticalProbability_pos
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_main_all_light_or_sparse_boundary
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_uniform_lower_nestedLayer_blocks

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.delete_bot
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

namespace ClusterDeletion
variable {V : Type*}

lemma delete_antitone (H : SimpleGraph V) {U U' : Set V} (h : U ⊆ U') :
    delete H U' ≤ delete H U :=
  fun _ _ hh => ⟨hh.1, fun hv => hh.2.1 (h hv), fun hw => hh.2.2 (h hw)⟩

lemma delete_le (H : SimpleGraph V) (U : Set V) : delete H U ≤ H :=
  fun _ _ h => h.1

lemma roots_mono {H H' : SimpleGraph V} (h : H ≤ H') (S : Set V) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  exact ⟨s, hs, hsv.mono h⟩

lemma component_mono {H H' : SimpleGraph V} (h : H ≤ H') (s : V) :
    component H s ⊆ component H' s :=
  fun _ hv => hv.mono h

lemma reachable_not_mem_roots {H : SimpleGraph V} {S : Set V} {s v : V}
    (hs : s ∉ roots H S) (hsv : H.Reachable s v) : v ∉ roots H S := by
  rintro ⟨u, hu, huv⟩
  exact hs ⟨u, hu, huv.trans hsv.symm⟩

lemma delete_roots_component (H : SimpleGraph V) (S : Set V) (s : V)
    (hs : s ∉ roots H S) :
    component (delete H (roots H S)) s = component H s := by
  apply Set.Subset.antisymm (component_mono (delete_le _ _) _)
  intro v hv
  have hr := (H.reachable_iff_reflTransGen s v).mp hv
  clear hv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      have hsu : H.Reachable s u := (H.reachable_iff_reflTransGen _ _).mpr hr
      have hsv : H.Reachable s v := hsu.trans huv.reachable
      exact ih.trans (SimpleGraph.Adj.reachable
        ⟨huv, reachable_not_mem_roots hs hsu, reachable_not_mem_roots hs hsv⟩)

lemma delete_delete (H : SimpleGraph V) (U W : Set V) :
    delete (delete H U) W = delete H (W ∪ U) := by
  ext v w
  simp only [delete, Set.mem_union, not_or]
  tauto

lemma delete_roots_union_component (H : SimpleGraph V) (S U : Set V) (s : V)
    (hs : s ∉ roots (delete H U) S) :
    component (delete H (roots (delete H U) S ∪ U)) s = component (delete H U) s := by
  rw [← delete_delete]
  exact delete_roots_component _ _ _ hs

lemma residual_nonneg (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) (U : Set V) : 0 ≤ residual H S s F U := by
  classical
  unfold residual
  split_ifs
  · rfl
  · exact sub_nonneg.mpr (hF (component_mono (delete_antitone H Set.subset_union_left) s))

lemma residual_monotone (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) : Monotone (residual H S s F) := by
  classical
  intro U U' hUU'
  have hW : roots (delete H U') S ⊆ roots (delete H U) S :=
    roots_mono (delete_antitone H hUU') S
  by_cases hs : s ∉ roots (delete H U) S
  · have hs' : s ∉ roots (delete H U') S := fun h => hs (hW h)
    rw [residual, ite_eq_left hs, residual, ite_eq_left hs']
    rw [delete_roots_union_component H S U s hs,
      delete_roots_union_component H S U' s hs']
    have hh₁ := hF (component_mono (delete_antitone H hW) s)
    have hh₂ := hF (component_mono (delete_antitone H hUU') s)
    exact sub_le_sub hh₁ hh₂
  · rw [residual, ite_eq_right hs]
    exact residual_nonneg H S s hF U'

end ClusterDeletion
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma dependsOn_exact_roots (S U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.roots (G.openGraph ω) S = U)
      (G.incidentEdges U) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.roots_eq_of_incident h (fun e he => (hω e he).to_iff),
    fun h => G.roots_eq_of_incident h (fun e he => (hω e he).symm.to_iff)⟩

lemma delete_openGraph_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.delete (G.openGraph ω) U)
      (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext v w
  change ((G.openGraph ω).Adj v w ∧ v ∉ U ∧ w ∉ U) ↔
    ((G.openGraph ω').Adj v w ∧ v ∉ U ∧ w ∉ U)
  by_cases hv : v ∈ U
  · simp [hv]
  by_cases hw : w ∈ U
  · simp [hw]
  simp only [hv, hw, not_false_eq_true, and_self, and_true, openGraph,
    SimpleGraph.fromEdgeSet_adj]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ (G.incidentEdges U)ᶜ := by
    intro e heq
    rintro ⟨x, hxU, hxe⟩
    have := hxe
    simp only [heq, Sym2.mem_iff] at this
    rcases this with rfl | rfl
    · exact hv hxU
    · exact hw hxU
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mpr heω, heq⟩, hne⟩

lemma deleted_roots_eq_of_incident {S U W : Set V} {ω ω' : Set E}
    (hW : ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω) U) S = W)
    (hω : ∀ e ∈ G.incidentEdges W, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω') U) S = W := by
  apply ClusterDeletion.roots_eq_of_adj_eq_incident hW
  intro v v' hv
  change ((G.openGraph ω).Adj v v' ∧ v ∉ U ∧ v' ∉ U) ↔
    ((G.openGraph ω').Adj v v' ∧ v ∉ U ∧ v' ∉ U)
  rw [G.openGraph_adj_eq_of_incident hω hv]

lemma dependsOn_exact_deleted_roots (S U W : Set V) :
    DependsOn (fun ω : Set E =>
      ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω) U) S = W)
      (G.incidentEdges W) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.deleted_roots_eq_of_incident h (fun e he => (hω e he).to_iff),
    fun h => G.deleted_roots_eq_of_incident h (fun e he => (hω e he).symm.to_iff)⟩

end BondGraph
end CriticalPercolation

open scoped BigOperators
open Set

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

lemma component_self (H : SimpleGraph V) (s : V) : s ∈ component H s :=
  SimpleGraph.Reachable.refl s

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

lemma component_eq_of_mem {H : SimpleGraph V} {s t : V}
    (h : t ∈ component H s) : component H t = component H s := by
  ext v
  exact ⟨fun hv => h.trans hv, fun hv => h.symm.trans hv⟩

lemma not_mem_roots_iff_disjoint (H : SimpleGraph V) (S : Set V) (s : V) :
    s ∉ roots H S ↔ Disjoint (component H s) S := by
  rw [Set.disjoint_left]
  constructor
  · intro hs t ht hS
    exact hs ⟨t, hS, ht.symm⟩
  · intro hd ⟨t, ht, hts⟩
    exact hd hts.symm ht

lemma component_delete_component (H : SimpleGraph V) (s t : V)
    (h : t ∉ component H s) :
    component (delete H (component H s)) t = component H t := by
  simpa only [roots_singleton] using
    (delete_roots_component H {s} t (by simpa only [roots_singleton] using h))

lemma roots_delete_component (H : SimpleGraph V) (S : Set V) (s : V)
    (h : s ∉ roots H S) : roots (delete H (component H s)) S = roots H S := by
  ext v
  constructor
  · intro hv
    exact roots_mono (delete_le H _) S hv
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, ht, ?_⟩
    have hts : t ∉ component H s := fun hg => h ⟨t, ht, hg.symm⟩
    change v ∈ component (delete H (component H s)) t
    rw [component_delete_component H s t hts]
    exact htv

lemma delete_empty (H : SimpleGraph V) : delete H ∅ = H := by
  ext v w
  simp only [delete, Set.mem_empty_iff_false, not_false_eq_true, and_true]

end CriticalPercolation.ClusterDeletion

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

lemma expect_partition {B : Type*} [Fintype B] [DecidableEq B] (w : E → A → ℝ)
    (r : (E → A) → B) (f : B → (E → A) → ℝ) :
    expect w (fun ω => f (r ω) ω) =
      ∑ b, expect w (fun ω => if r ω = b then f b ω else 0) := by
  classical
  simp only [expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  rw [← Finset.mul_sum]
  simp

lemma expect_exposure {B : Type*} [Fintype B] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (r : (E → A) → B) (D : B → Set E)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (E → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  classical
  rw [expect_partition w r f,
    expect_partition w r (fun b _ => expect w (f b))]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have hi : DependsOn (fun ω => if r ω = b then (1 : ℝ) else 0) (D b) := by
    intro ω ω' hω
    change (if r ω = b then (1 : ℝ) else 0) = (if r ω' = b then 1 else 0)
    have hh : (r ω = b) = (r ω' = b) := hr b hω
    rw [hh]
  have hleft : (fun ω => if r ω = b then f b ω else 0) =
      (fun ω => (if r ω = b then (1 : ℝ) else 0) * f b ω) := by
    funext ω
    split_ifs <;> simp
  have hright : (fun ω => if r ω = b then expect w (f b) else 0) =
      (fun ω => (if r ω = b then (1 : ℝ) else 0) * expect w (f b)) := by
    funext ω
    split_ifs <;> simp
  rw [hleft, hright, expect_indep w hw (D b) hi (hf b), expect_mul_const]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ExpectedCluster
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma finite_spatialMarkov (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S U : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω =>
      F (roots (delete (G.openGraph ω) U) S)
        (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S))) =
    expect w (fun ω => expect w (fun ω' =>
      F (roots (delete (G.openGraph ω) U) S)
        (delete (G.openGraph ω') (roots (delete (G.openGraph ω) U) S)))) := by
  classical
  refine expect_exposure w hw
    (fun ω => roots (delete (G.openGraph ω) U) S) G.incidentEdges
    (G.dependsOn_exact_deleted_roots S U)
    (fun W ω => F W (delete (G.openGraph ω) W)) ?_
  intro W ω ω' hω
  exact congrArg (F W) (G.delete_openGraph_dependsOn W hω)

lemma expectedResidual_eq (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => residual (G.openGraph ω) S s F U) := by
  classical
  have h := G.finite_spatialMarkov w hw S U
    (fun W H => if s ∉ W then F (component H s) - F (component (delete H U) s) else 0)
  have hu : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hu] at h
  change _ = expect w (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
    F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S)) s) -
    F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S ∪ U)) s)
    else 0)
  rw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_const w hw]
  · rw [expect_sub]
    rfl

lemma expectedResidual_nonneg (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) (U : Set V) :
    0 ≤ G.expectedResidual w S s F U := by
  rw [expectedResidual_eq G w hw, ← expect_const w hw 0]
  exact expect_mono hpos fun ω => residual_nonneg (G.openGraph ω) S s hF U

lemma expectedResidual_monotone (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.expectedResidual w S s F) := by
  intro U U' hUU'
  rw [expectedResidual_eq G w hw, expectedResidual_eq G w hw]
  exact expect_mono hpos fun ω => residual_monotone (G.openGraph ω) S s hF hUU'

end CriticalPercolation.BondGraph

open scoped BigOperators

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Distribution
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

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]

lemma expect_sum {J : Type*} [Fintype J] (w : E → A → ℝ)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j, f j ω) = ∑ j, expect w (f j) := by
  classical
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterUpdate
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

open scoped Classical

omit [Fintype V] in
lemma expectedCluster_antitone (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Antitone (G.expectedCluster w s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => hF (component_mono (delete_antitone _ hU) s)

omit [Fintype V] in
lemma clusterUpdate_monotone (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.clusterUpdate w S s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => G.expectedCluster_antitone w hpos s hF
    (roots_mono (delete_antitone _ hU) S)

omit [Fintype V] in
lemma clusterUpdate_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : ∀ U, 0 ≤ F U) (U : Set V) :
    0 ≤ G.clusterUpdate w S s F U :=
  expect_nonneg hpos fun _ => expect_nonneg hpos fun _ => hF _

lemma clusterUpdate_exposure (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F g : Set V → ℝ) :
    (expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
      g (component (G.openGraph ω) s) * G.expectedCluster w s F (roots (G.openGraph ω) S)
      else 0)) =
    G.avoidedAverage w S s (fun U => g U * G.clusterUpdate w S s F U) := by
  classical
  have h := G.finite_spatialMarkov w hw {s} ∅
    (fun U H => if Disjoint U S then g U * G.expectedCluster w s F (roots H S) else 0)
  simp only [delete_empty, roots_singleton] at h
  have hleft : (fun ω : E → Prop =>
      if Disjoint (component (G.openGraph ω) s) S then
        g (component (G.openGraph ω) s) * G.expectedCluster w s F
          (roots (delete (G.openGraph ω) (component (G.openGraph ω) s)) S) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then
        g (component (G.openGraph ω) s) * G.expectedCluster w s F
          (roots (G.openGraph ω) S) else 0) := by
    funext ω
    rw [← not_mem_roots_iff_disjoint]
    split_ifs with hs
    · rfl
    · rw [roots_delete_component _ S s hs]
  rw [hleft] at h
  erw [h]
  unfold avoidedAverage
  congr 1
  funext ω
  rw [← not_mem_roots_iff_disjoint]
  split_ifs
  · rw [expect_zero]
  · rw [expect_const_mul]
    rfl

lemma avoidedAverage_exposure (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s F =
      expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
        G.expectedCluster w s F (roots (G.openGraph ω) S) else 0) := by
  classical
  have h := G.finite_spatialMarkov w hw S ∅
    (fun W H => if s ∉ W then F (component H s) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.openGraph ω) S then
      F (component (delete (G.openGraph ω) (roots (G.openGraph ω) S)) s) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then F (component (G.openGraph ω) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_component _ S s hs]
  rw [hleft] at h
  change expect w _ = _
  erw [h]
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rfl

lemma clusterUpdate_stationary (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s (G.clusterUpdate w S s F) = G.avoidedAverage w S s F := by
  have h := G.clusterUpdate_exposure w hw S s F (fun _ => 1)
  simp only [one_mul] at h
  exact h.symm.trans (G.avoidedAverage_exposure w hw S s F).symm

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_Earlier
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*} {n : ℕ}

lemma root_not_mem_earlier {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)

lemma earlier_mono (x : Fin n → V) {k l : Fin n} (hkl : k ≤ l) :
    earlier x k ⊆ earlier x l := by
  rintro v ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans_le hkl, rfl⟩

lemma first_unique {H : SimpleGraph V} {x : Fin n → V} {k l i : Fin n}
    (hk : first H x k) (hki : x i ∈ component H (x k))
    (hl : first H x l) (hli : x i ∈ component H (x l)) : k = l := by
  apply le_antisymm
  · by_contra! h
    exact hk ⟨x l, ⟨l, h, rfl⟩, hli.trans hki.symm⟩
  · by_contra! h
    exact hl ⟨x k, ⟨k, h, rfl⟩, hki.trans hli.symm⟩

lemma exists_first (H : SimpleGraph V) (x : Fin n → V) (i : Fin n) :
    ∃ k, first H x k ∧ x i ∈ component H (x k) := by
  classical
  let J := Finset.univ.filter (fun j => x i ∈ component H (x j))
  have hi : i ∈ J := by simp [J, component_self]
  have hJ : J.Nonempty := ⟨i, hi⟩
  let k := J.min' hJ
  have hkJ : k ∈ J := Finset.min'_mem J hJ
  have hki : x i ∈ component H (x k) := (Finset.mem_filter.mp hkJ).2
  refine ⟨k, ?_, hki⟩
  rintro ⟨v, ⟨j, hj, rfl⟩, hjk⟩
  have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk.trans hki⟩
  have hkj : k ≤ j := Finset.min'_le J j hjJ
  exact (not_lt_of_ge hkj) hj

lemma select_nonneg (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
    0 ≤ select H x k i := by unfold select; positivity

lemma select_zero_of_lt (H : SimpleGraph V) (x : Fin n → V) {k i : Fin n} (hik : i < k) :
    select H x k i = 0 := by
  apply ite_eq_right
  rintro ⟨hk, hki⟩
  exact hk ⟨x i, ⟨i, hik, rfl⟩, hki.symm⟩

lemma select_diag (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) :
    select H x k k = if first H x k then 1 else 0 := by
  simp only [select, component_self, and_true]

lemma select_mul_sum (H : SimpleGraph V) (x : Fin n → V) (i : Fin n)
    (a : Fin n → ℝ) {k : Fin n} (hk : first H x k)
    (hki : x i ∈ component H (x k)) :
    ∑ l, select H x l i * a l = a k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp [select, hk, hki]
  · intro l _ hlk
    have hh : ¬ (first H x l ∧ x i ∈ component H (x l)) := by
      rintro ⟨hl, hli⟩
      exact hlk (first_unique hl hli hk hki)
    simp [select, hh]
  · simp

lemma select_mass (H : SimpleGraph V) (x : Fin n → V) (i : Fin n) :
    ∑ k, select H x k i = 1 := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  simpa using select_mul_sum H x i (fun _ => 1) hk hki

lemma cluster_partition (H : SimpleGraph V) (x : Fin n → V)
    (F : Set V → ℝ) (i : Fin n) :
    F (component H (x i)) = ∑ k, select H x k i * F (component H (x k)) := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  rw [select_mul_sum H x i _ hk hki, component_eq_of_mem hki]

lemma first_hit_not_mem_roots_iff (H : SimpleGraph V) (x : Fin n → V)
    {j i : Fin n} (hj : first H x j) (hji : x i ∈ component H (x j)) (k : Fin n) :
    x i ∉ roots H (earlier x k) ↔ k ≤ j := by
  constructor
  · intro hi
    by_contra! hjk
    exact hi ⟨x j, ⟨j, hjk, rfl⟩, hji⟩
  · rintro hkj ⟨v, ⟨l, hlk, rfl⟩, hli⟩
    exact hj ⟨x l, ⟨l, hlk.trans_le hkj, rfl⟩, hli.trans hji.symm⟩

lemma select_truncation (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
    (if x i ∉ roots H (earlier x k) then (1 : ℝ) else 0) =
      select H x k i + ∑ l, if k < l then select H x l i else 0 := by
  classical
  obtain ⟨j, hj, hji⟩ := exists_first H x i
  have he : ∀ l, select H x l i = if l = j then 1 else 0 := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp [select, hj, hji]
    · have hh : ¬ (first H x l ∧ x i ∈ component H (x l)) := by
        rintro ⟨hl, hli⟩
        exact hlj (first_unique hl hli hj hji)
      simp [select, hh, hlj]
  simp_rw [he]
  have hsum : (∑ l : Fin n, if k < l then if l = j then (1 : ℝ) else 0 else 0) =
      if k < j then 1 else 0 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      simp [hlj]
    · simp
  rw [hsum]
  simp only [first_hit_not_mem_roots_iff H x hj hji k]
  rcases lt_trichotomy k j with h | h | h
  · simp [h, ne_of_lt h, le_of_lt h]
  · subst j
    simp
  · simp [ne_of_gt h, not_le_of_gt h, not_lt_of_gt h]

end CriticalPercolation.ClusterColumns

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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BlockIndependence
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteMarkovAvg
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

namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]

lemma avg_const (μ : X → ℝ) (c : ℝ) : avg μ (fun _ => c) = (∑ x, μ x) * c := by
  classical
  exact (Finset.sum_mul _ _ _).symm

lemma avg_mono {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) {f g : X → ℝ}
    (h : ∀ x, f x ≤ g x) : avg μ f ≤ avg μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)

lemma avg_stationary (K : X → X → ℝ) (μ : X → ℝ)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) :
    avg μ (step K f) = avg μ f := by
  classical
  simp only [step, avg]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hstat]

lemma avg_iterate (K : X → X → ℝ) (μ : X → ℝ)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) (n : ℕ) :
    avg μ ((step K)^[n] f) = avg μ f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', avg_stationary K μ hstat, ih]

omit [Fintype X] in
lemma remainder_nonneg {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    {a : ℝ} {z : X} (haK : ∀ x, a ≤ K x z) (x y : X) :
    0 ≤ remainder K a z x y := by
  classical
  unfold remainder
  split_ifs with h
  · subst y
    exact sub_nonneg.mpr (haK x)
  · simpa using hK x y

lemma remainder_mass (K : X → X → ℝ) (hK : ∀ x, ∑ y, K x y = 1)
    (a : ℝ) (z x : X) : ∑ y, remainder K a z x y = 1 - a := by
  classical
  simp [remainder, Finset.sum_sub_distrib, hK]

lemma step_remainder (K : X → X → ℝ) (a : ℝ) (z : X) (f : X → ℝ) (x : X) :
    step K f x = a * f z + avg (remainder K a z x) f := by
  classical
  simp [step, avg, remainder, sub_mul, Finset.sum_sub_distrib, ite_mul]

lemma step_bounds {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) {f : X → ℝ} {l u : ℝ}
    (hf : ∀ x, l ≤ f x ∧ f x ≤ u) (x : X) :
    a * f z + (1 - a) * l ≤ step K f x ∧
      step K f x ≤ a * f z + (1 - a) * u := by
  rw [step_remainder K a z]
  have hlo := avg_mono (remainder_nonneg hK haK x) (fun x => (hf x).1)
  have hup := avg_mono (remainder_nonneg hK haK x) (fun x => (hf x).2)
  rw [avg_const, remainder_mass K hmass] at hlo
  rw [avg_const, remainder_mass K hmass] at hup
  constructor <;> linarith

lemma iterate_bounds {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) {f : X → ℝ} {l u : ℝ}
    (hf : ∀ x, l ≤ f x ∧ f x ≤ u) (n : ℕ) :
    ∃ l' u', (∀ x, l' ≤ (step K)^[n] f x ∧ (step K)^[n] f x ≤ u') ∧
      u' - l' = (1 - a)^n * (u-l) := by
  induction n with
  | zero => exact ⟨l, u, hf, by simp⟩
  | succ n ih =>
      obtain ⟨l', u', hb, hd⟩ := ih
      refine ⟨a * (step K)^[n] f z + (1-a)*l',
        a * (step K)^[n] f z + (1-a)*u', ?_, ?_⟩
      · intro x
        simpa only [Function.iterate_succ_apply'] using step_bounds hK hmass haK hb x
      · calc
          _ = (1-a) * (u'-l') := by ring
          _ = _ := by rw [hd, pow_succ]; ring

lemma iterate_distance {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) (μ : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y)
    {f : X → ℝ} {l u : ℝ} (hf : ∀ x, l ≤ f x ∧ f x ≤ u)
    (n : ℕ) (x : X) :
    |(step K)^[n] f x - avg μ f| ≤ (1-a)^n * (u-l) := by
  obtain ⟨l', u', hb, hd⟩ := iterate_bounds hK hmass haK hf n
  have hlo := avg_mono hμ (fun x => (hb x).1)
  have hup := avg_mono hμ (fun x => (hb x).2)
  rw [avg_const, hμmass, one_mul, avg_iterate K μ hstat] at hlo
  rw [avg_const, hμmass, one_mul, avg_iterate K μ hstat] at hup
  rw [← hd, abs_le]
  have := hb x
  constructor <;> linarith

lemma tendsto_iterate {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (ha : 0 < a) (ha_one : a ≤ 1) (haK : ∀ x, a ≤ K x z)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) (x : X) :
    Filter.Tendsto (fun n => (step K)^[n] f x) Filter.atTop (nhds (avg μ f)) := by
  classical
  let : Nonempty X := ⟨z⟩
  let l := Finset.univ.inf' Finset.univ_nonempty f
  let u := Finset.univ.sup' Finset.univ_nonempty f
  have hb : ∀ y, l ≤ f y ∧ f y ≤ u := by
    intro y
    exact ⟨Finset.inf'_le _ (Finset.mem_univ y), Finset.le_sup' _ (Finset.mem_univ y)⟩
  have hpow : Filter.Tendsto (fun n : ℕ => (1-a)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ha_one) (by linarith)
  have hlim := hpow.mul_const (u-l)
  simp only [zero_mul] at hlim
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := (Metric.tendsto_atTop.mp hlim) ε hε
  obtain ⟨N, hN⟩ := he
  refine ⟨N, fun n hn => ?_⟩
  have hlt := hN n hn
  rw [Real.dist_eq, sub_zero] at hlt
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (iterate_distance hK hmass haK μ hμ hμmass hstat hb n x)
    (lt_of_le_of_lt (le_abs_self _) hlt)

end CriticalPercolation.FiniteMarkov

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_DensityModular
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_HitValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V : Type*}

lemma jointHitValue_nonneg (A T U : Set V) : 0 ≤ jointHitValue A T U := by
  unfold jointHitValue; positivity
lemma jointHitValue_monotone (A T : Set V) : Monotone (jointHitValue A T) := by
  intro U W hUW
  unfold jointHitValue
  split_ifs with hU hW hW
  · exact le_rfl
  · exact (hW ⟨hU.1.mono (Set.inter_subset_inter_left A hUW),
      hU.2.mono (Set.inter_subset_inter_left T hUW)⟩).elim
  · norm_num
  · exact le_rfl

lemma jointHitValue_eq_hitValue {A T U : Set V} (hA : (U ∩ A).Nonempty) :
    jointHitValue A T U = hitValue T U := by simp [jointHitValue, hitValue, hA]

lemma component_inter_nonempty_iff (H : SimpleGraph V) (s : V) (A : Set V) :
    (component H s ∩ A).Nonempty ↔ s ∈ roots H A := by
  constructor
  · rintro ⟨t, ht, hA⟩
    exact ⟨t, hA, ht.symm⟩
  · rintro ⟨t, hA, ht⟩
    exact ⟨t, ht.symm, hA⟩

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_HitOthers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.ClusterColumns
open scoped Classical

variable {V : Type*} {n : ℕ}

lemma hitOthers_nonneg (x : Fin n → V) (k : Fin n) (U : Set V) :
    0 ≤ hitOthers x k U := by unfold hitOthers; positivity

lemma hitOthers_le_one (x : Fin n → V) (k : Fin n) (U : Set V) :
    hitOthers x k U ≤ 1 := by unfold hitOthers; split_ifs <;> norm_num

lemma hitOthers_monotone (x : Fin n → V) (k : Fin n) : Monotone (hitOthers x k) := by
  intro U W hUW
  unfold hitOthers
  split_ifs with hU hW hW
  · exact le_rfl
  · obtain ⟨j, hj, hjU⟩ := hU
    exact (hW ⟨j, hj, hUW hjU⟩).elim
  · norm_num
  · exact le_rfl

lemma hitOthers_singleton (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    hitOthers x k {x k} = 0 := by
  apply ite_eq_right
  rintro ⟨j, hj, hjk⟩
  exact hj (hx hjk)

end CriticalPercolation.ClusterColumns

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ExpectedResidualAlt
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.delete_bot _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma expectedResidual_alt (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
        G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
          F (component (delete (G.openGraph ω) U) s) else 0) := by
  have h := G.finite_spatialMarkov w hw S U
    (fun W H => if s ∉ W then G.expectedCluster w s F W -
      F (component (delete H U) s) else 0)
  have hdel : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hdel] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
        F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S ∪ U)) s)
      else 0) =
      (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
        G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
          F (component (delete (G.openGraph ω) U) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_union_component _ S U s hs]
  rw [hleft] at h
  erw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rw [expect_sub, expect_const w hw]
    rfl

lemma later_cluster_residual (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s t : V) (F g : Set V → ℝ) (Q : Set V → Prop)
    (hQ : ∀ U, Q U → Disjoint U S ∧ s ∉ U) :
    (expect w (fun ω => if Q (component (G.openGraph ω) t) then
      if s ∉ roots (G.openGraph ω) S then
        g (component (G.openGraph ω) t) *
          (G.expectedCluster w s F (roots (G.openGraph ω) S) -
            F (component (G.openGraph ω) s)) else 0 else 0)) =
    expect w (fun ω => if Q (component (G.openGraph ω) t) then
      g (component (G.openGraph ω) t) *
        G.expectedResidual w S s F (component (G.openGraph ω) t) else 0) := by
  have h := G.finite_spatialMarkov w hw {t} ∅
    (fun U H => if Q U then if s ∉ roots H S then
      g U * (G.expectedCluster w s F (roots H S) - F (component H s)) else 0 else 0)
  simp only [delete_empty, roots_singleton] at h
  have hleft : (fun ω : E → Prop => if Q (component (G.openGraph ω) t) then
      if s ∉ roots (delete (G.openGraph ω) (component (G.openGraph ω) t)) S then
        g (component (G.openGraph ω) t) *
          (G.expectedCluster w s F (roots (delete (G.openGraph ω) (component (G.openGraph ω) t)) S) -
            F (component (delete (G.openGraph ω) (component (G.openGraph ω) t)) s))
        else 0 else 0) =
      (fun ω => if Q (component (G.openGraph ω) t) then
        if s ∉ roots (G.openGraph ω) S then
          g (component (G.openGraph ω) t) *
            (G.expectedCluster w s F (roots (G.openGraph ω) S) - F (component (G.openGraph ω) s))
          else 0 else 0) := by
    funext ω
    by_cases hq : Q (component (G.openGraph ω) t)
    · simp only [ite_eq_left hq]
      obtain ⟨hd, hs⟩ := hQ _ hq
      rw [roots_delete_component _ S t ((not_mem_roots_iff_disjoint _ S t).mpr hd),
        component_delete_component _ t s hs]
    · simp only [ite_eq_right hq]
  rw [hleft] at h
  erw [h]
  congr 1
  funext ω
  by_cases hq : Q (component (G.openGraph ω) t)
  · simp only [ite_eq_left hq]
    rw [G.expectedResidual_alt w hw]
    rw [← expect_const_mul]
    congr 1
    funext ω'
    split_ifs <;> simp
  · simp only [ite_eq_right hq, expect_zero]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Column
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma avoided_drift_zero (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F b : Set V → ℝ) :
    expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
      b (roots (G.openGraph ω) S) * (F (component (G.openGraph ω) s) -
        G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) = 0 := by
  have h := G.finite_spatialMarkov w hw S ∅
    (fun W H => if s ∉ W then b W * (F (component H s) - G.expectedCluster w s F W) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.openGraph ω) S then
      b (roots (G.openGraph ω) S) * (F (component (delete (G.openGraph ω) (roots (G.openGraph ω) S)) s) -
        G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then
        b (roots (G.openGraph ω) S) * (F (component (G.openGraph ω) s) -
          G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_component _ S s hs]
  rw [hleft] at h
  erw [h]
  have hz : ∀ W : Set V, expect w (fun ω => if s ∉ W then
      b W * (F (component (delete (G.openGraph ω) W) s) - G.expectedCluster w s F W)
      else 0) = 0 := by
    intro W
    split_ifs
    · exact expect_zero w
    · rw [expect_const_mul, expect_sub, expect_const w hw]
      change b W * (G.expectedCluster w s F W - G.expectedCluster w s F W) = 0
      ring
  simp only [hz, expect_zero]

omit [Fintype V] in
lemma column_as_avoidedAverage {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i = G.avoidedAverage w (earlier x k) (x k)
      (fun U => (if x i ∈ U then 1 else 0) * F U) := by
  unfold column avoidedAverage select first
  congr 1
  funext ω
  split_ifs <;> simp_all

lemma column_update {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.openGraph ω) x k i *
        G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) := by
  rw [G.column_as_avoidedAverage]
  rw [← G.clusterUpdate_exposure w hw]
  congr 1
  funext ω
  simp only [select, first]
  split_ifs <;> simp_all

lemma column_later_residual {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) {k l : Fin n} (hkl : k < l) (F : Set V → ℝ) (i : Fin n) :
    G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i =
    expect w (fun ω => if first (G.openGraph ω) x k then
      select (G.openGraph ω) x l i *
        (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
          F (component (G.openGraph ω) (x k))) else 0) := by
  have h := G.later_cluster_residual w hw (earlier x k) (x k) (x l) F
    (fun U => if x i ∈ U then 1 else 0) (fun U => Disjoint U (earlier x l))
    (fun U hU => ⟨hU.mono_right (earlier_mono x hkl.le),
      fun hs => (Set.disjoint_left.mp hU) hs ⟨k, hkl, rfl⟩⟩)
  have hc : (fun ω : E → Prop => if Disjoint (component (G.openGraph ω) (x l)) (earlier x l) then
      (if x i ∈ component (G.openGraph ω) (x l) then 1 else 0) *
        G.expectedResidual w (earlier x k) (x k) F (component (G.openGraph ω) (x l)) else 0) =
      (fun ω => select (G.openGraph ω) x l i *
        G.expectedResidual w (earlier x k) (x k) F (component (G.openGraph ω) (x l))) := by
    funext ω
    simp only [select, first, not_mem_roots_iff_disjoint]
    split_ifs <;> simp_all
  rw [hc] at h
  unfold column
  erw [← h]
  congr 1
  funext ω
  simp only [select, first, not_mem_roots_iff_disjoint]
  split_ifs <;> simp_all

lemma column_decomposition {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i +
        ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
  have hzero := G.avoided_drift_zero w hw (earlier x k) (x k) F
    (fun W => if x i ∉ W then 1 else 0)
  have hpoint : (fun ω : E → Prop => if x k ∉ roots (G.openGraph ω) (earlier x k) then
      (if x i ∉ roots (G.openGraph ω) (earlier x k) then (1 : ℝ) else 0) *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) else 0) =
      (fun ω => select (G.openGraph ω) x k i *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) -
        ∑ l, if k < l then if first (G.openGraph ω) x k then
          select (G.openGraph ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
              F (component (G.openGraph ω) (x k))) else 0 else 0) := by
    funext ω
    by_cases hk : first (G.openGraph ω) x k
    · simp only [show x k ∉ roots (G.openGraph ω) (earlier x k) from hk,
        not_false_eq_true, ite_true, if_true]
      rw [select_truncation]
      simp only [hk, ite_true, if_true]
      have hsum : ∀ a : ℝ,
          (∑ l, if k < l then select (G.openGraph ω) x l i * a else 0) =
          (∑ l, if k < l then select (G.openGraph ω) x l i else 0) * a := by
        intro a
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs <;> simp
      rw [hsum]
      ring
    · have hk' : ¬ (x k ∉ roots (G.openGraph ω) (earlier x k)) := hk
      simp [hk', hk, select]
  rw [hpoint] at hzero
  erw [expect_sub, expect_sum] at hzero
  have hlater : (∑ l, expect w (fun ω => if k < l then if first (G.openGraph ω) x k then
          select (G.openGraph ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
              F (component (G.openGraph ω) (x k))) else 0 else 0)) =
      ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [hkl, ite_true, if_true]
      exact (G.column_later_residual w hw x hkl F i).symm
    · simp only [hkl, ite_false, if_false, expect_zero]
  erw [hlater] at hzero
  have hdiff : G.column w x k F i -
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.openGraph ω) x k i *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)))) := by
    rw [G.column_update w hw]
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  exact sub_eq_iff_eq_add'.mp (hdiff.trans (sub_eq_zero.mp hzero))

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_DensityMulExpect
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma density_mul_le_expect {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) (ω : E → A) :
    density w ω * f ω ≤ expect w f := by
  classical
  exact Finset.single_le_sum (fun ω _ => mul_nonneg (density_nonneg hw ω) (hf ω))
    (Finset.mem_univ ω)
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_UpdateKernel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma clusterUpdate_eq_sum (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) :
    G.clusterUpdate w S s F U = ∑ Z, G.updateKernel w S s U Z * F Z := by
  classical
  unfold updateKernel clusterUpdate expectedCluster
  simp_rw [← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  congr 1
  funext ω'
  simp

omit [Fintype V] in
lemma updateKernel_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U Z : Set V) : 0 ≤ G.updateKernel w S s U Z :=
  G.clusterUpdate_nonneg w hpos S s (fun _ => by split_ifs <;> norm_num) U

lemma updateKernel_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (U : Set V) : ∑ Z, G.updateKernel w S s U Z = 1 := by
  have h := G.clusterUpdate_eq_sum w S s (fun _ => 1) U
  simpa only [clusterUpdate, expectedCluster, expect_const w hw, mul_one] using h.symm

omit [Fintype V] in
lemma allClosed_weight_le_kernel (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (S : Set V) (s : V) (U : Set V) :
    density w (fun _ => False) ≤ G.updateKernel w S s U {s} := by
  unfold updateKernel clusterUpdate expectedCluster
  rw [← expect_const w hw (density w (fun _ => False))]
  apply expect_mono hpos
  intro ω
  have h := density_mul_le_expect hpos
    (f := fun ω' => if component (delete (G.openGraph ω')
      (roots (delete (G.openGraph ω) U) S)) s = {s} then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, delete_bot, component_bot, ite_true, if_true, mul_one] using h

lemma avoidedAverage_eq_sum (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) :
    G.avoidedAverage w S s F = ∑ U,
      G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) * F U := by
  classical
  unfold avoidedAverage
  simp_rw [← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  split_ifs <;> simp_all

lemma avoidedLaw_avg (w : E → Prop → ℝ) (S : Set V) (s : V) (F : Set V → ℝ) :
    FiniteMarkov.avg (G.avoidedLaw w S s) F =
      G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1) := by
  classical
  unfold FiniteMarkov.avg avoidedLaw
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [← G.avoidedAverage_eq_sum]

omit [Fintype V] in
lemma avoidedLaw_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U : Set V) : 0 ≤ G.avoidedLaw w S s U := by
  unfold avoidedLaw avoidedAverage
  apply div_nonneg <;> apply expect_nonneg hpos <;> intro ω <;> positivity

omit [Fintype V] in
lemma allClosed_weight_le_avoidance (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (hs : s ∉ S) :
    density w (fun _ => False) ≤ G.avoidedAverage w S s (fun _ => 1) := by
  unfold avoidedAverage
  have h := density_mul_le_expect hpos
    (f := fun ω => if s ∉ roots (G.openGraph ω) S then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, roots_bot, ite_eq_left hs, mul_one] using h

omit [Fintype V] in
lemma avoidance_pos (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    0 < G.avoidedAverage w S s (fun _ => 1) := by
  have hp : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  exact hp.trans_le (G.allClosed_weight_le_avoidance w hpos S s hs)

lemma avoidedLaw_mass (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    ∑ U, G.avoidedLaw w S s U = 1 := by
  have h := G.avoidedLaw_avg w S s (fun _ => 1)
  simpa only [FiniteMarkov.avg, mul_one, div_self (ne_of_gt (G.avoidance_pos w hpos hclosed S s hs))]
    using h

lemma avoidedLaw_stationary (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (Z : Set V) :
    ∑ U, G.avoidedLaw w S s U * G.updateKernel w S s U Z = G.avoidedLaw w S s Z := by
  change FiniteMarkov.avg (G.avoidedLaw w S s)
    (G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0)) = _
  rw [G.avoidedLaw_avg, G.clusterUpdate_stationary w hw]
  rfl

lemma tendsto_clusterUpdate (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (S : Set V) (s : V) (hs : s ∉ S) (F : Set V → ℝ) (U : Set V) :
    Filter.Tendsto (fun n => (G.clusterUpdate w S s)^[n] F U) Filter.atTop
      (nhds (G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1))) := by
  have hstep : G.clusterUpdate w S s = FiniteMarkov.step (G.updateKernel w S s) := by
    funext f Z
    exact G.clusterUpdate_eq_sum w S s f Z
  have ha : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  have haone : density w (fun _ => False) ≤ 1 := by
    have h := density_mul_le_expect hpos (f := fun _ => 1) (fun _ => by norm_num)
      (fun _ => False)
    simpa only [mul_one, expect_const w hw] using h
  rw [hstep, ← G.avoidedLaw_avg]
  exact FiniteMarkov.tendsto_iterate (G.updateKernel_nonneg w hpos S s)
    (G.updateKernel_mass w hw S s) ha haone
    (G.allClosed_weight_le_kernel w hw hpos S s) _ (G.avoidedLaw_nonneg w hpos S s)
    (G.avoidedLaw_mass w hpos hclosed S s hs) (G.avoidedLaw_stationary w hw S s) F U

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_LinearGroups_ClusterMatrix
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma column_zero_of_lt {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    {k i : Fin n} (hik : i < k) (F : Set V → ℝ) : G.column w x k F i = 0 := by
  unfold column
  simp only [select_zero_of_lt _ _ hik, zero_mul, expect_zero]

omit [Fintype V] in
lemma column_diag {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) :
    G.column w x k F k = G.avoidedAverage w (earlier x k) (x k) F := by
  unfold column avoidedAverage
  simp only [select_diag, first]
  congr 1
  funext ω
  split_ifs <;> simp_all

omit [Fintype V] in
lemma clusterMatrix_lower {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    (G.clusterMatrix w x).IsLowerTriangular := by
  intro i k hik
  exact G.column_zero_of_lt w x hik _

omit [Fintype V] in
lemma clusterMatrix_det_pos {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) : 0 < (G.clusterMatrix w x).det := by
  rw [Matrix.det_of_isLowerTriangular _ (G.clusterMatrix_lower w x)]
  apply Finset.prod_pos
  intro k _
  change 0 < G.column w x k (fun _ => 1) k
  rw [G.column_diag]
  exact G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx k)

omit [Fintype V] in
lemma inverseColumn_const {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (c : ℝ) :
    G.inverseColumn w x k (fun _ => c) = c • Pi.single k 1 := by
  have hc : G.column w x k (fun _ => c) = c • G.column w x k (fun _ => 1) := by
    funext i
    change expect w _ = c * expect w _
    rw [← expect_const_mul]
    congr 1
    funext ω
    ring
  have hunit : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  unfold inverseColumn
  rw [hc, Matrix.mulVec_smul]
  congr 1
  have hcol : G.column w x k (fun _ => 1) = G.clusterMatrix w x *ᵥ Pi.single k 1 := by
    ext i
    simp [Matrix.mulVec_single, clusterMatrix]
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

lemma inverseColumn_decomposition {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    G.inverseColumn w x k F =
      G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) F) +
        ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) F) else 0 := by
  have hc : G.column w x k F =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) +
        ∑ l, if k < l then G.column w x l
          (G.expectedResidual w (earlier x k) (x k) F) else 0 := by
    ext i
    simpa only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] using
      G.column_decomposition w hw x k F i
  unfold inverseColumn
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp

omit [Fintype V] in
lemma continuous_inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) : Continuous (fun F : Set V → ℝ => G.inverseColumn w x k F i) := by
  unfold inverseColumn Matrix.mulVec dotProduct column expect
  fun_prop

lemma inverseColumn_nonneg {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k : Fin n) {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) :
    ∀ i, 0 ≤ G.inverseColumn w x k F i := by
  induction k using WellFoundedGT.induction generalizing F with
  | ind k ih =>
    have hstep (f : Set V → ℝ) (hf : Monotone f) (i : Fin n) :
        G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) f) i ≤
          G.inverseColumn w x k f i := by
      have hd := congrFun (G.inverseColumn_decomposition w hw x k f) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hd
      have hr : 0 ≤ ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) f) i else 0 := by
        apply Finset.sum_nonneg
        intro l _
        split_ifs with hkl
        · exact ih l hkl (G.expectedResidual_monotone w hw hpos _ _ hf)
            (G.expectedResidual_nonneg w hw hpos _ _ hf) i
        · exact le_rfl
      linarith only [hd, hr]
    have hmono (j : ℕ) : Monotone ((G.clusterUpdate w (earlier x k) (x k))^[j] F) := by
      induction j with
      | zero => exact hF
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact G.clusterUpdate_monotone w hpos _ _ hj
    have hbound (j : ℕ) (i : Fin n) :
        G.inverseColumn w x k ((G.clusterUpdate w (earlier x k) (x k))^[j] F) i ≤
          G.inverseColumn w x k F i := by
      induction j with
      | zero => exact le_rfl
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact (hstep _ (hmono j) i).trans hj
    let m := G.avoidedAverage w (earlier x k) (x k) F /
      G.avoidedAverage w (earlier x k) (x k) (fun _ => 1)
    have hm : 0 ≤ m := by
      apply div_nonneg
      · unfold avoidedAverage
        apply expect_nonneg hpos
        intro ω
        split_ifs
        · exact le_rfl
        · exact hF0 _
      · exact le_of_lt (G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx k))
    have hlim : Filter.Tendsto
        (fun j => (G.clusterUpdate w (earlier x k) (x k))^[j] F) Filter.atTop
        (nhds (fun _ => m)) :=
      tendsto_pi_nhds.mpr (fun U => G.tendsto_clusterUpdate w hw hpos hclosed _ _
        (root_not_mem_earlier hx k) F U)
    intro i
    have hi := (G.continuous_inverseColumn w x k i).tendsto (fun _ => m) |>.comp hlim
    have hb := le_of_tendsto hi (Filter.Eventually.of_forall (fun j => hbound j i))
    rw [G.inverseColumn_const w hpos hclosed x hx] at hb
    apply le_trans _ hb
    change 0 ≤ m * (Pi.single (M := fun _ : Fin n => ℝ) k 1 i)
    apply mul_nonneg hm
    by_cases hki : k = i <;> simp [hki]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ColumnHitOthersOffdiag
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma column_hitOthers_offdiag {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) (hik : i ≠ k) :
    G.column w x k (hitOthers x k) i = G.column w x k (fun _ => 1) i := by
  unfold column
  congr 1
  funext ω
  by_cases hc : first (G.openGraph ω) x k ∧ x i ∈ component (G.openGraph ω) (x k)
  · have hh : ∃ j, j ≠ k ∧ x j ∈ component (G.openGraph ω) (x k) := ⟨i, hik, hc.2⟩
    simp [select, hitOthers, hc, hh]
  · simp [select, hc]

omit [Fintype V] in
lemma column_hitOthers_gap_pos {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k := by
  have he : G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k =
      expect w (fun ω => select (G.openGraph ω) x k k *
        (1 - hitOthers x k (component (G.openGraph ω) (x k)))) := by
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  rw [he]
  have hf (ω : E → Prop) : 0 ≤ select (G.openGraph ω) x k k *
      (1 - hitOthers x k (component (G.openGraph ω) (x k))) :=
    mul_nonneg (select_nonneg _ _ _ _) (sub_nonneg.mpr (hitOthers_le_one _ _ _))
  have hd := density_mul_le_expect hpos hf (fun _ => False)
  have hs : first (⊥ : SimpleGraph V) x k := by
    simpa only [first, roots_bot] using root_not_mem_earlier hx k
  simp only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, component_bot, hitOthers_singleton x hx, sub_zero,
    select_diag, hs, ite_true, if_true, mul_one] at hd
  have hp : 0 < density w (∅ : Set E) := Finset.prod_pos (fun e _ => hclosed e)
  simpa only [select_diag] using hp.trans_le hd

lemma inverseMatrix_offdiag_nonpos {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k i : Fin n) (hik : i ≠ k) : (G.clusterMatrix w x)⁻¹ i k ≤ 0 := by
  let a := G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k
  have ha : 0 < a := G.column_hitOthers_gap_pos w hpos hclosed x hx k
  have he : G.column w x k (fun _ => 1) =
      G.column w x k (hitOthers x k) + a • Pi.single k 1 := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [a]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj, mul_zero,
        add_zero]
      exact (G.column_hitOthers_offdiag w x k j hj).symm
  have he' := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v) he
  change G.inverseColumn w x k (fun _ => 1) = _ at he'
  rw [G.inverseColumn_const w hpos hclosed x hx, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_single_one] at he'
  have he'' := congrFun he' i
  simp only [Pi.single_eq_of_ne hik, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply] at he''
  have hp := G.inverseColumn_nonneg w hw hpos hclosed x hx k
    (hitOthers_monotone x k) (hitOthers_nonneg x k) i
  change 0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k (hitOthers x k)) i at hp
  nlinarith only [he'', hp, ha]

omit [Fintype V] in
lemma clusterMatrix_row_mass {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) :
    G.clusterMatrix w x *ᵥ (fun _ => 1) = fun _ => 1 := by
  ext i
  change (∑ k, G.column w x k (fun _ => 1) i * 1) = 1
  simp only [mul_one, column]
  erw [← expect_sum]
  simpa only [mul_one, select_mass] using expect_const w hw 1

omit [Fintype V] in
lemma inverseMatrix_row_mass {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x) :
    (G.clusterMatrix w x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have h := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v)
    (G.clusterMatrix_row_mass w hw x)
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  exact h.symm

omit [Fintype V] in
lemma clusterFunction_sum_columns {n : ℕ} (w : E → Prop → ℝ)
    (x : Fin n → V) (F : Set V → ℝ) :
    (fun i => expect w (fun ω => F (component (G.openGraph ω) (x i)))) =
      ∑ k, G.column w x k F := by
  ext i
  simp only [Finset.sum_apply, column]
  erw [← expect_sum]
  congr 1
  funext ω
  exact cluster_partition (G.openGraph ω) x F i

lemma inverse_clusterFunction_nonneg {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) (i : Fin n) :
    0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ
      (fun j => expect w (fun ω => F (component (G.openGraph ω) (x j))))) i := by
  rw [G.clusterFunction_sum_columns, Matrix.mulVec_sum, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => G.inverseColumn_nonneg w hw hpos hclosed x hx k hF hF0 i)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_LastInverseDiagonal
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma last_inverse_diagonal {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin (n+1) → V) (hx : Function.Injective x) :
    G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1) *
      (G.clusterMatrix w x)⁻¹ (Fin.last n) (Fin.last n) = 1 := by
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (G.clusterMatrix w x) hu)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_castSucc,
    clusterMatrix, column_zero_of_lt _ _ _ (Fin.castSucc_lt_last _), mul_zero,
    Finset.sum_const_zero, zero_add, column_diag] at h
  simpa only [mul_comm] using h

lemma finite_cluster_relay {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U)
    (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => F (component (G.openGraph ω) (x j.castSucc)))) :
    (1 - G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)) * a ≤
      expect w (fun ω => F (component (G.openGraph ω) (x (Fin.last n)))) := by
  let N := (G.clusterMatrix w x)⁻¹
  let y : Fin (n+1) → ℝ := fun j => expect w (fun ω => F (component (G.openGraph ω) (x j)))
  let d := G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)
  have hd : 0 < d := G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx _)
  have hdiag : d * N (Fin.last n) (Fin.last n) = 1 := G.last_inverse_diagonal w hpos hclosed x hx
  have hmass := congrFun (G.inverseMatrix_row_mass w hw hpos hclosed x hx) (Fin.last n)
  change ∑ j, N (Fin.last n) j * 1 = 1 at hmass
  simp only [mul_one, Fin.sum_univ_castSucc] at hmass
  have hzero := G.inverse_clusterFunction_nonneg w hw hpos hclosed x hx hF hF0 (Fin.last n)
  change 0 ≤ ∑ j, N (Fin.last n) j * y j at hzero
  rw [Fin.sum_univ_castSucc] at hzero
  have hs : (∑ j : Fin n, N (Fin.last n) j.castSucc * y j.castSucc) ≤
      (∑ j : Fin n, N (Fin.last n) j.castSucc) * a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonpos_left (ha j)
      (G.inverseMatrix_offdiag_nonpos w hw hpos hclosed x hx j.castSucc (Fin.last n)
        (ne_of_gt (Fin.castSucc_lt_last j)))
  have hb : (N (Fin.last n) (Fin.last n) - 1) * a ≤
      N (Fin.last n) (Fin.last n) * y (Fin.last n) := by
    have hm : (∑ j : Fin n, N (Fin.last n) j.castSucc) =
        1 - N (Fin.last n) (Fin.last n) := by linarith only [hmass]
    rw [hm] at hs
    linarith only [hzero, hs]
  change (1-d)*a ≤ y (Fin.last n)
  calc
    (1-d)*a = (d * N (Fin.last n) (Fin.last n) - d) * a := by rw [hdiag]
    _ = d * ((N (Fin.last n) (Fin.last n) - 1) * a) := by ring
    _ ≤ d * (N (Fin.last n) (Fin.last n) * y (Fin.last n)) :=
      mul_le_mul_of_nonneg_left hb hd.le
    _ = y (Fin.last n) := by rw [← mul_assoc, hdiag, one_mul]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HittingSubAvoidance
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma hitting_eq_one_sub_avoidance (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A : Set V) (s : V) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) s)) =
      1 - G.avoidedAverage w A s (fun _ => 1) := by
  conv_rhs => lhs; rw [← expect_const w hw 1]
  unfold avoidedAverage
  erw [← expect_sub]
  congr 1
  funext ω
  simp only [hitValue, component_inter_nonempty_iff]
  split_ifs <;> norm_num

lemma finite_joint_gluing_list {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    (T : Set V) (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) (x j.castSucc)))) :
    expect w (fun ω => hitValue (earlier x (Fin.last n))
        (component (G.openGraph ω) (x (Fin.last n)))) * a ≤
      expect w (fun ω => jointHitValue (earlier x (Fin.last n)) T
        (component (G.openGraph ω) (x (Fin.last n)))) := by
  rw [G.hitting_eq_one_sub_avoidance w hw]
  apply G.finite_cluster_relay w hw hpos hclosed x hx
    (jointHitValue_monotone _ _) (jointHitValue_nonneg _ _)
  intro j
  have he : (fun ω : E → Prop => jointHitValue (earlier x (Fin.last n)) T
      (component (G.openGraph ω) (x j.castSucc))) =
      (fun ω => hitValue T (component (G.openGraph ω) (x j.castSucc))) := by
    funext ω
    apply jointHitValue_eq_hitValue
    exact ⟨x j.castSucc, component_self _ _, ⟨j.castSucc, Fin.castSucc_lt_last j, rfl⟩⟩
  rw [he]
  exact ha j

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FiniteJointGluingStrict
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma finite_joint_gluing_strict (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  classical
  by_cases ho : o ∈ A
  · have hA (ω : Set E) : (component (G.openGraph ω) o ∩ A).Nonempty :=
      ⟨o, component_self _ _, ho⟩
    have hh : (fun ω : Set E => hitValue A (component (G.openGraph ω) o)) =
        (fun _ => (1 : ℝ)) := by
      funext ω
      exact ite_eq_left (hA ω)
    have hj : (fun ω : Set E => jointHitValue A T (component (G.openGraph ω) o)) =
        (fun ω => hitValue T (component (G.openGraph ω) o)) := by
      funext ω
      exact jointHitValue_eq_hitValue (hA ω)
    erw [hh, hj, expect_const w hw, one_mul]
    exact ha o ho
  · let n := Fintype.card A
    let e : Fin n ≃ A := (Fintype.equivFin A).symm
    let f : Fin n → V := fun j => e j
    let x : Fin (n+1) → V := Fin.snoc f o
    have hx : Function.Injective x := by
      apply Fin.snoc_injective_iff.mpr
      refine ⟨?_, ?_⟩
      · exact Subtype.val_injective.comp e.injective
      · rintro ⟨j, hj⟩
        exact ho (hj ▸ (e j).property)
    have hlast : x (Fin.last n) = o := Fin.snoc_last _ _
    have hearlier : earlier x (Fin.last n) = A := by
      ext v
      constructor
      · rintro ⟨j, hj, h⟩
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · have he : x i.castSucc = f i := Fin.snoc_castSucc _ _ _
          exact h ▸ he ▸ (e i).property
        · exact (lt_irrefl _ hj).elim
      · intro hv
        let i := e.symm ⟨v, hv⟩
        refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
        dsimp only [x]
        rw [Fin.snoc_castSucc]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
    have h := G.finite_joint_gluing_list w hw hpos hclosed x hx T a (by
      intro j
      simpa only [x, Fin.snoc_castSucc] using ha (f j) (e j).property)
    rwa [hearlier, hlast] at h

end CriticalPercolation.BondGraph

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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FiniteJointGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma finite_joint_gluing (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  classical
  let w' : ℝ → E → Prop → ℝ := fun t e b => (1-t) * w e b + if b then 0 else t
  have hzero : w' 0 = w := by funext e b; simp [w']
  have hcont : Continuous w' := by
    apply continuous_pi
    intro e
    apply continuous_pi
    intro b
    dsimp only [w']
    split_ifs <;> fun_prop
  let err : ℝ → ℝ := fun t => ∑ v : V,
    |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) v)) -
      expect w (fun ω => hitValue T (component (G.openGraph ω) v))|
  have herr : Continuous err := by
    apply continuous_finsetSum
    intro v _
    exact (((continuous_expect_weights _).comp hcont).sub continuous_const).abs
  have herr0 : err 0 = 0 := by simp [err, hzero]
  have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      expect (w' t) (fun ω => hitValue A (component (G.openGraph ω) o)) * (a-err t) ≤
        expect (w' t) (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
    apply G.finite_joint_gluing_strict
    · intro e
      have hs := hw e
      simp only [Fintype.sum_Prop] at hs ⊢
      dsimp only [w']
      rw [ite_eq_left True.intro, ite_eq_right (by trivial : ¬ False)]
      nlinarith
    · intro e b
      have hm := mul_nonneg (sub_nonneg.mpr ht1) (hpos e b)
      dsimp only [w']
      apply add_nonneg hm
      split_ifs <;> linarith
    · intro e
      have hm := mul_nonneg (sub_nonneg.mpr ht1) (hpos e False)
      dsimp only [w']
      rw [ite_eq_right (by trivial : ¬ False)]
      exact add_pos_of_nonneg_of_pos hm ht
    · intro v hv
      have hsingle :
          |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) v)) -
            expect w (fun ω => hitValue T (component (G.openGraph ω) v))| ≤ err t := by
        dsimp only [err]
        exact Finset.single_le_sum (f := fun u : V =>
          |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) u)) -
            expect w (fun ω => hitValue T (component (G.openGraph ω) u))|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
      have hneg := (abs_le.mp hsingle).1
      linarith [ha v hv]
  have ht : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL := ((((continuous_expect_weights
    (fun ω => hitValue A (component (G.openGraph ω) o))).comp hcont).mul
      ((continuous_const (y := a)).sub herr)).tendsto 0).comp ht
  have hR := (((continuous_expect_weights
    (fun ω => jointHitValue A T (component (G.openGraph ω) o))).comp hcont).tendsto 0).comp ht
  have hh := le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall (fun n : ℕ =>
    hbound (1/((n : ℝ)+1)) (by positivity) (by
      apply (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)))
  simpa only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hzero, herr0, sub_zero] using hh

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_RestrictVertices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma restrictVertices_adj (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).openGraph ω).Adj v w ↔
      (G.openGraph ω).Adj v.val w.val := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨e, he, ?_⟩, fun h => hne (Subtype.ext h)⟩
    have h := congrArg (Sym2.map Subtype.val) hend
    simpa only [restrictVertices, Sym2.attachWith_map_subtypeVal, Sym2.map_mk] using h
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨e, he, ?_⟩, fun h => hne (congrArg Subtype.val h)⟩
    apply Sym2.map.injective Subtype.val_injective
    simp only [restrictVertices, Sym2.attachWith_map_subtypeVal, Sym2.map_mk]
    exact hend

lemma restrictVertices_graph (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) :
    (G.restrictVertices U hU).openGraph ω = (G.openGraph ω).induce U := by
  ext v w
  exact G.restrictVertices_adj U hU ω v w

lemma adj_mem_support (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (h : (G.openGraph ω).Adj v w) : v ∈ U ∧ w ∈ U := by
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
  exact ⟨hU e v (by simp [he]), hU e w (by simp [he])⟩

lemma walk_support_subset (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (p : (G.openGraph ω).Walk v w) (hv : v ∈ U) :
    ∀ u ∈ p.support, u ∈ U := by
  induction p with
  | nil => simpa
  | @cons v w z hvw p ih =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hv
      · exact ih (G.adj_mem_support U hU hvw).2 u hu

lemma cluster_subset_support (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v : V} (hv : v ∈ U) : G.cluster ω v ⊆ U := by
  rintro w ⟨p⟩
  exact G.walk_support_subset U hU p hv w p.end_mem_support

lemma restrictVertices_reachable (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).openGraph ω).Reachable v w ↔
      (G.openGraph ω).Reachable v.val w.val := by
  rw [G.restrictVertices_graph]
  constructor
  · intro h
    exact h.map (SimpleGraph.Embedding.induce U).toHom
  · rintro ⟨p⟩
    exact ⟨p.induce U (G.walk_support_subset U hU p v.property)⟩

open CriticalPercolation.ClusterColumns CriticalPercolation.ClusterDeletion
open CriticalPercolation.FiniteProduct

lemma restrictVertices_hit_iff (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    (component ((G.restrictVertices U hU).openGraph ω) v ∩ (Subtype.val ⁻¹' A)).Nonempty ↔
      (component (G.openGraph ω) v.val ∩ A).Nonempty := by
  constructor
  · rintro ⟨w, hw, hA⟩
    exact ⟨w.val, (G.restrictVertices_reachable U hU ω v w).mp hw, hA⟩
  · rintro ⟨w, hw, hA⟩
    have hwU := G.cluster_subset_support U hU v.property hw
    exact ⟨⟨w, hwU⟩, (G.restrictVertices_reachable U hU ω v ⟨w, hwU⟩).mpr hw, hA⟩

lemma restrictVertices_hitValue (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    hitValue (Subtype.val ⁻¹' A) (component ((G.restrictVertices U hU).openGraph ω) v) =
      hitValue A (component (G.openGraph ω) v.val) := by
  simp only [hitValue, G.restrictVertices_hit_iff]

lemma restrictVertices_jointHitValue (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A T : Set V) :
    jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component ((G.restrictVertices U hU).openGraph ω) v) =
      jointHitValue A T (component (G.openGraph ω) v.val) := by
  simp only [jointHitValue, G.restrictVertices_hit_iff]

lemma finite_edge_joint_gluing [Fintype E] (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  let U : Set V := insert o (A ∪ ⋃ e, (↑(G.ends e).toFinset : Set V))
  have hUf : U.Finite :=
    (hA.union (Set.finite_iUnion fun e => (G.ends e).toFinset.finite_toSet)).insert o
  let : Fintype U := hUf.fintype
  have hU : ∀ e v, v ∈ G.ends e → v ∈ U := by
    intro e v hv
    exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨e, by simpa using hv⟩))
  let R := G.restrictVertices U hU
  let o' : U := ⟨o, Set.mem_insert _ _⟩
  have h := R.finite_joint_gluing w hw hpos o' (Subtype.val ⁻¹' A)
    (Subtype.val ⁻¹' T) a (by
      intro v hv
      have heq : (fun ω : E → Prop =>
          hitValue (Subtype.val ⁻¹' T) (component (R.openGraph ω) v)) =
          (fun ω => hitValue T (component (G.openGraph ω) v.val)) := by
        funext ω
        exact G.restrictVertices_hitValue U hU ω v T
      rw [heq]
      exact ha v.val hv)
  have heq : (fun ω : E → Prop =>
      hitValue (Subtype.val ⁻¹' A) (component (R.openGraph ω) o')) =
      (fun ω => hitValue A (component (G.openGraph ω) o)) := by
    funext ω
    exact G.restrictVertices_hitValue U hU ω o' A
  have heq' : (fun ω : E → Prop =>
      jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component (R.openGraph ω) o')) =
      (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
    funext ω
    exact G.restrictVertices_jointHitValue U hU ω o' A T
  rwa [heq, heq'] at h

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma expect_hit_eq_real [Fintype E] (q : E → unitInterval) (o : V) (A : Set V) :
    expect (fun e => bitWeight (q e))
      (fun ω => hitValue A (component (G.openGraph ω) o)) =
        (BernoulliProduct.law q).real (G.hitEvent o A) := by
  erw [← integral_law_eq_expect q (fun ω : Set E =>
    hitValue A (component (G.openGraph ω) o))]
  have he : (fun ω : Set E => hitValue A (component (G.openGraph ω) o)) =
      (G.hitEvent o A).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [hitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]

lemma expect_jointHit_eq_real [Fintype E] (q : E → unitInterval) (o : V) (A T : Set V) :
    expect (fun e => bitWeight (q e))
      (fun ω => jointHitValue A T (component (G.openGraph ω) o)) =
        (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  erw [← integral_law_eq_expect q (fun ω : Set E =>
    jointHitValue A T (component (G.openGraph ω) o))]
  have he : (fun ω : Set E => jointHitValue A T (component (G.openGraph ω) o)) =
      (G.hitEvent o A ∩ G.hitEvent o T).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [jointHitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]

lemma finite_edge_joint_gluing_law [Fintype E] (q : E → unitInterval)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  rw [← G.expect_hit_eq_real, ← G.expect_jointHit_eq_real]
  apply G.finite_edge_joint_gluing _ (fun e => bitWeight_sum (q e))
    (fun e b => bitWeight_nonneg (q e) b) o A T hA a
  intro v hv
  rw [G.expect_hit_eq_real]
  exact ha v hv

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

lemma restrictEdges_hitEvent (s : Set E) (o : V) (A : Set V) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        ((G.restrictEdges s).hitEvent o A) =
      {ω | s ∩ ω ∈ G.hitEvent o A} := by
  ext ω
  simp only [Set.mem_preimage, hitEvent, cluster, Set.mem_ofPred_eq,
    G.restrictEdges_openGraph]

lemma finite_subgraph_joint_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real {ω | s ∩ ω ∈ G.hitEvent v T}) :
    (BernoulliProduct.law q).real {ω | s ∩ ω ∈ G.hitEvent o A} * a ≤
      (BernoulliProduct.law q).real ({ω | s ∩ ω ∈ G.hitEvent o A} ∩
        {ω | s ∩ ω ∈ G.hitEvent o T}) := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have hr (B : Set (Set s)) (hB : MeasurableSet B) :
      (BernoulliProduct.law (fun e : s => q e)).real B =
        (BernoulliProduct.law q).real ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B) := by
    rw [← law_map_restrict q s]
    simp only [measureReal_def, Measure.map_apply hmeas hB]
  have h := (G.restrictEdges s).finite_edge_joint_gluing_law
    (fun e : s => q e) o A T hA a (by
      intro v hv
      rw [hr _ (.of_discrete), G.restrictEdges_hitEvent]
      exact ha v hv)
  rw [hr _ (.of_discrete), hr _ (.of_discrete), Set.preimage_inter,
    G.restrictEdges_hitEvent, G.restrictEdges_hitEvent] at h
  exact h

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

lemma hitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) = G.hitEvent o A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact G.hitEvent_mono_edges o A Set.inter_subset_right hn
  · rintro ⟨v, hv, hvA⟩
    obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hs (Set.subset_univ s)
    exact Set.mem_iUnion.mpr ⟨n, v, G.cluster_mono
      (Set.subset_inter hn hsω) o hvs, hvA⟩

lemma hitEvent_exhaustion_mono (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Monotone (fun n => {ω | K n ∩ ω ∈ G.hitEvent o A}) := by
  intro m n h ω hω
  exact G.hitEvent_mono_edges o A (Set.inter_subset_inter_left _ (K.mono h)) hω

lemma tendsto_real_hitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A})
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    (G.hitEvent_exhaustion_mono K o A)
  rw [G.hitEvent_exhaustion K o A] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma jointHitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    (⋃ n, ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
      {ω | K n ∩ ω ∈ G.hitEvent o T})) = G.hitEvent o A ∩ G.hitEvent o T := by
  calc
    _ = (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) ∩
        (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o T}) :=
      Set.iUnion_inter_of_monotone (G.hitEvent_exhaustion_mono K o A)
        (G.hitEvent_exhaustion_mono K o T)
    _ = _ := by rw [G.hitEvent_exhaustion K o A, G.hitEvent_exhaustion K o T]

lemma tendsto_real_jointHitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real
      ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩ {ω | K n ∩ ω ∈ G.hitEvent o T}))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    ((G.hitEvent_exhaustion_mono K o A).inter (G.hitEvent_exhaustion_mono K o T))
  rw [G.jointHitEvent_exhaustion K o A T] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma finite_sum_abs_sub_bound {X : Type*} [Fintype X] (f g : X → ℝ) (x : X) :
    |f x - g x| ≤ ∑ y, |f y - g y| := by
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y - g y)) (Finset.mem_univ x)

lemma countable_joint_gluing_finite [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  classical
  let : Fintype A := hA.fintype
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let err : ℕ → ℝ := fun n => ∑ v : A,
    |(BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
      (BernoulliProduct.law q).real (G.hitEvent v T)|
  have herr : Tendsto err atTop (𝓝 0) := by
    have h : Tendsto err atTop (𝓝 (∑ _v : A, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro v _
      simpa using ((G.tendsto_real_hitEvent_exhaustion q K v T).sub_const
        ((BernoulliProduct.law q).real (G.hitEvent v T))).abs
    simpa using h
  have hbound (n : ℕ) :
      (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A} * (a - err n) ≤
      (BernoulliProduct.law q).real ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
        {ω | K n ∩ ω ∈ G.hitEvent o T}) := by
    refine G.finite_subgraph_joint_gluing q (K n) (K.finite n) o A T hA (a - err n) ?_
    intro v hv
    have hs : |(BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
        (BernoulliProduct.law q).real (G.hitEvent v T)| ≤ err n := by
      exact finite_sum_abs_sub_bound
        (fun u : A => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent u T})
        (fun u : A => (BernoulliProduct.law q).real (G.hitEvent u T)) ⟨v, hv⟩
    have hneg := (abs_le.mp hs).1
    linarith [ha v hv]
  have hL := (G.tendsto_real_hitEvent_exhaustion q K o A).mul ((tendsto_const_nhds (x := a)).sub herr)
  have hR := G.tendsto_real_jointHitEvent_exhaustion q K o A T
  have h := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hbound)
  simpa only [sub_zero] using h

lemma hitEvent_iUnion {I : Type*} (o : V) (A : I → Set V) :
    G.hitEvent o (⋃ i, A i) = ⋃ i, G.hitEvent o (A i) := by
  ext ω
  simp only [hitEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.nonempty_def,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hv, i, hi⟩
    exact ⟨i, v, hv, hi⟩
  · rintro ⟨i, v, hv, hi⟩
    exact ⟨v, hv, i, hi⟩

theorem countable_joint_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  let K := (Set.to_countable A).finiteExhaustion
  have hKA (n : ℕ) : K n ⊆ A := by
    exact Set.Subset.trans (Set.subset_iUnion K n) (le_of_eq K.iUnion_eq)
  have hmono : Monotone (fun n => G.hitEvent o (K n)) := by
    intro m n h
    exact G.hitEvent_mono_target o (K.mono h)
  have hunion : (⋃ n, G.hitEvent o (K n)) = G.hitEvent o A := by
    rw [← G.hitEvent_iUnion, K.iUnion_eq]
  have hL : Tendsto (fun n => (BernoulliProduct.law q).real (G.hitEvent o (K n)))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
    have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
    rw [hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hR : Tendsto (fun n => (BernoulliProduct.law q).real
      (G.hitEvent o (K n) ∩ G.hitEvent o T))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
    have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
      (hmono.inter (monotone_const (c := G.hitEvent o T)))
    rw [← Set.iUnion_inter, hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto (hL.mul_const a) hR
    (Eventually.of_forall fun n => G.countable_joint_gluing_finite q o (K n) T
      (K.finite n) a (fun v hv => ha v (hKA n hv)))

theorem joint_gluing [Countable V] [Countable E]
    (p : unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (G.law p).real (G.hitEvent v T)) :
    (G.law p).real (G.hitEvent o A) * a ≤
      (G.law p).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  have he : BernoulliProduct.law (fun _ : E => p) = G.law p := law_const p
  simpa only [he] using G.countable_joint_gluing (fun _ => p) o A T a
    (by simpa only [he] using ha)

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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_UniformGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterMass
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ForcedDisconnectContinuity
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_HeavyHarris
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma massTailEvent_upper (o v : V) (a : ℝ≥0∞) : IsUpperSet (G.massTailEvent o v a) :=
  fun _ _ h hh => hh.trans_le (G.modularMass_mono o (G.cluster_mono h v))

lemma massTailEvent_finiteWitness (o v : V) (a : ℝ≥0∞) :
    BernoulliProduct.HasFiniteOpenWitness (G.massTailEvent o v a) := by
  intro ω hω
  change a<∑' x, if x∈G.cluster ω v then G.stabilizerWeight o x else 0 at hω
  rw [ENNReal.tsum_eq_iSup_sum,lt_iSup_iff] at hω
  obtain ⟨S,hS⟩ := hω
  let T : Set V := (S : Set V) ∩ G.cluster ω v
  obtain ⟨s,hs,hsω,hTs⟩ := G.finite_subset_cluster_finite_witness
    (S.finite_toSet.inter_of_left _) (show T⊆G.cluster ω v from Set.inter_subset_right)
  refine ⟨s,hs,hsω,lt_of_lt_of_le hS ?_⟩
  change (∑ x∈S, if x∈G.cluster ω v then G.stabilizerWeight o x else 0) ≤
    ∑' x, if x∈G.cluster s v then G.stabilizerWeight o x else 0
  apply (Finset.sum_le_sum (fun x hx => ?_)).trans (ENNReal.sum_le_tsum S)
  by_cases hxω : x∈G.cluster ω v
  · rw [ite_eq_left hxω,ite_eq_left (hTs ⟨hx,hxω⟩)]
  · simp only [ite_eq_right hxω,zero_le]

lemma measurableSet_massTailEvent [Countable V] [Countable E] (o v : V) (a : ℝ≥0∞) :
    MeasurableSet (G.massTailEvent o v a) :=
  measurableSet_lt measurable_const (G.measurable_modularClusterMass o v)

lemma heavyClusterEvent_eq_iInter_massTail (o v : V) :
    G.heavyClusterEvent o v=⋂ n : ℕ, G.massTailEvent o v n := by
  ext ω
  simp only [heavyClusterEvent,massTailEvent,Set.mem_ofPred_eq,Set.mem_iInter]
  constructor
  · intro h n
    rw [h]
    exact ENNReal.natCast_lt_top n
  · intro h
    by_contra hn
    obtain ⟨n,hnn⟩ := exists_nat_gt (G.modularMass o (G.cluster ω v)).toReal
    have hlt : (n:ℝ≥0∞)<G.modularMass o (G.cluster ω v) := h n
    have hh := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top n) hn).mpr hlt
    simp only [ENNReal.toReal_natCast] at hh
    exact (lt_irrefl _) (hh.trans hnn)

lemma massTailEvent_antitone (o v : V) : Antitone (fun n : ℕ => G.massTailEvent o v n) := by
  intro n m h ω hω
  exact lt_of_le_of_lt (show (n : ℝ≥0∞) ≤ (m : ℝ≥0∞) by exact_mod_cast h) hω

lemma tendsto_real_massTail [Countable V] [Countable E] (p : unitInterval) (o v : V) :
    Tendsto (fun n : ℕ => (G.law p).real (G.massTailEvent o v n)) atTop
      (𝓝 ((G.law p).real (G.heavyClusterEvent o v))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n : ℕ => (G.measurableSet_massTailEvent o v n).nullMeasurableSet)
    (G.massTailEvent_antitone o v) ⟨0,measure_ne_top _ _⟩
  rw [←G.heavyClusterEvent_eq_iInter_massTail] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

lemma harris_heavyClusterEvent [Countable V] [Countable E] (p : unitInterval) (o x y : V) :
    (G.law p).real (G.heavyClusterEvent o x) * (G.law p).real (G.heavyClusterEvent o y) ≤
      (G.law p).real (G.heavyClusterEvent o x ∩ G.heavyClusterEvent o y) := by
  have hlim := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n : ℕ => ((G.measurableSet_massTailEvent o x n).inter
      (G.measurableSet_massTailEvent o y n)).nullMeasurableSet)
    (show Antitone (fun n : ℕ => G.massTailEvent o x n ∩ G.massTailEvent o y n) from
      fun _ _ h => Set.inter_subset_inter (G.massTailEvent_antitone o x h)
        (G.massTailEvent_antitone o y h)) ⟨0,measure_ne_top _ _⟩
  rw [Set.iInter_inter_distrib,←G.heavyClusterEvent_eq_iInter_massTail,
    ←G.heavyClusterEvent_eq_iInter_massTail] at hlim
  apply le_of_tendsto_of_tendsto
    ((G.tendsto_real_massTail p o x).mul (G.tendsto_real_massTail p o y))
    ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim)
  apply Eventually.of_forall
  intro n
  simpa only [BernoulliProduct.law_const,BondGraph.law,measureReal_def,Function.comp_apply] using
    BernoulliProduct.harris_finiteWitness (fun _ : E => p)
      (G.massTailEvent o x n) (G.massTailEvent o y n)
      (G.massTailEvent_upper o x n) (G.massTailEvent_upper o y n)
      (G.massTailEvent_finiteWitness o x n) (G.massTailEvent_finiteWitness o y n)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_InfiniteEventSubsetHit
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
open Filter Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infiniteEvent_subset_hit_compl (o : V) (K : Set V) (hK : K.Finite) :
    G.infiniteEvent o ⊆ G.hitEvent o Kᶜ := by
  intro ω hω
  exact (hω.sdiff hK).nonempty

lemma infiniteEvent_eq_iInter_hit_compl
    (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    G.infiniteEvent o = ⋂ n, G.hitEvent o (K n)ᶜ := by
  ext ω
  constructor
  · intro hω
    exact Set.mem_iInter.mpr fun n => G.infiniteEvent_subset_hit_compl o (K n) (K.finite n) hω
  · intro hω
    change (G.cluster ω o).Infinite
    intro hfin
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hfin (Set.subset_univ _)
    obtain ⟨v, hv, hvK⟩ := Set.mem_iInter.mp hω n
    exact hvK (hn hv)

lemma tendsto_real_hit_compl [Countable V] [Countable E]
    (p : unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    Tendsto (fun n => (G.law p).real (G.hitEvent o (K n)ᶜ)) atTop
      (𝓝 ((G.law p).real (G.infiniteEvent o))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (G.measurableSet_hitEvent o (K n)ᶜ).nullMeasurableSet)
    (show Antitone (fun n => G.hitEvent o (K n)ᶜ) from
      fun _ _ h => G.hitEvent_mono_target o (Set.compl_subset_compl.mpr (K.mono h)))
    ⟨0, measure_ne_top _ _⟩
  rw [← G.infiniteEvent_eq_iInter_hit_compl K o] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_GrowthAlternatives
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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

end CriticalPercolation.BondGraph
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

omit [Fintype E] in
lemma closedPivot_iff (F : Set E → Prop) (e : E) (ω : Set E) :
    closedPivot F e ω ↔ ω e = False ∧ pivotal F e ω := by
  have hh : ¬ω e → Function.update ω e False = ω := by
    intro h
    have he : ω e = False := propext (iff_false_intro h)
    rw [← he]
    exact Function.update_eq_self _ _
  by_cases h : ω e
  · simp [closedPivot, h]
  · simp [closedPivot, pivotal, h, hh h, and_comm]

lemma probability_closedPivot (p : ℝ) (F : Set E → Prop) (e : E) :
    probability p (closedPivot F e) = (1-p) * probability p (pivotal F e) := by
  have he : (fun ω : E → Prop => if closedPivot F e ω then (1:ℝ) else 0) =
      (fun ω => if ω e = False then (if pivotal F e ω then 1 else 0) else 0) := by
    funext ω
    erw [closedPivot_iff]
    split_ifs <;> tauto
  unfold probability
  rw [he]
  have hm : expect (fun _ : E => weight p)
      (fun ω => if ω e = False then (if pivotal F e ω then 1 else 0) else 0) =
      (1-p)*expect (fun _ : E => weight p)
        (fun ω => if pivotal F e (Function.update ω e False) then 1 else 0) := by
    convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p)
      e False (fun ω => if pivotal F e ω then 1 else 0) using 1 <;>
      first | (congr 1; funext ω; split_ifs <;> rfl) | simp [weight]
  calc
    _ = (1-p)*expect (fun _ : E => weight p)
        (fun ω => if pivotal F e (Function.update ω e False) then 1 else 0) := by
      convert hm using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
    _ = _ := by
      congr 1
      congr 1
      funext ω
      simp only [pivotal, Function.update_idem]
      congr 1

theorem hasDerivAt_probability_closedPivot {p : ℝ} (hp : p ∈ Ioo 0 1)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    HasDerivAt (fun q => probability q F)
      ((∑ e, probability p (closedPivot F e)) / (1-p)) p := by
  have hd := hasDerivAt_probability hp F hF
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  simp only [probability_closedPivot, ← Finset.mul_sum]
  exact mul_div_cancel_left₀ _ (sub_pos.mpr hp.2).ne'

lemma probability_nonneg {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    0 ≤ probability p F := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun _ => 0) (g := fun ω => if F ω then 1 else 0)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 0, probability] using h

lemma probability_le_one {p : ℝ} (hp : p ∈ Icc 0 1) (F : Set E → Prop) :
    probability p F ≤ 1 := by
  have h := expect_mono (w := fun _ : E => weight p)
    (fun _ b => weight_nonneg hp b)
    (f := fun ω => if F ω then 1 else 0) (g := fun _ => 1)
    (fun _ => by split_ifs <;> norm_num)
  simpa only [expect_const _ (fun _ => weight_sum p) 1, probability] using h

end CriticalPercolation.Sharpness
end
end CurrentModule0

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Link2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule1
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
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

open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma reachesTarget_mono (o : V) (T : Set V) {ω ω' : Set E}
    (h : ω ⊆ ω') : reachesTarget G o T ω → reachesTarget G o T ω' :=
  fun ho => roots_mono (G.openGraph_mono h) T ho

lemma reachesTarget_iff_hitEvent (o : V) (T : Set V) (ω : Set E) :
    reachesTarget G o T ω ↔ ω ∈ G.hitEvent o T := by
  constructor
  · rintro ⟨t, ht, hto⟩
    exact ⟨t, hto.symm, ht⟩
  · rintro ⟨t, hot, ht⟩
    exact ⟨t, ht, hot.symm⟩

lemma openGraph_force_true (ω : Set E) (e : E) (v b : V)
    (he : G.ends e = s(v,b)) :
    G.openGraph (Function.update ω e True) = G.openGraph ω ⊔ SimpleGraph.edge v b := by
  have hs : (Function.update ω e True : Set E) = insert e ω := by
    ext j
    by_cases hje : j = e
    · subst j; erw [Function.update_self]; exact iff_of_true trivial (Set.mem_insert e ω)
    · erw [Function.update_of_ne hje]
      change j ∈ ω ↔ j ∈ insert e ω
      simp [hje]
  erw [hs]
  rw [BondGraph.openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma target_creating_iff (o : V) (T : Set V) (ω : Set E) (e : E)
    (ho : ¬ reachesTarget G o T ω) :
    reachesTarget G o T (Function.update ω e True) ↔
      boundaryReach G (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e := by
  let H := G.openGraph ω
  let R := roots H T
  have hor : o ∉ R := ho
  have hdel : component (delete H R) o = component H o :=
    delete_roots_component H T o hor
  constructor
  · intro hn
    obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective (G.ends e)
    have he : G.ends e = s(a,b) := hab.symm
    obtain ⟨t,ht,hnew⟩ := hn
    rw [openGraph_force_true G ω e a b he] at hnew
    have hh := (Wiring.reachable_sup_edge H a b o t).mp hnew.symm
    rcases hh with hold | ⟨hoa,hbt⟩ | ⟨hob,hat⟩
    · exact (ho ⟨t,ht,hold.symm⟩).elim
    · refine ⟨a,b,he,reachable_not_mem_roots hor hoa,⟨t,ht,hbt.symm⟩,?_⟩
      change a ∈ component (delete H R) o
      rw [hdel]
      exact hoa
    · refine ⟨b,a,?_,reachable_not_mem_roots hor hob,⟨t,ht,hat.symm⟩,?_⟩
      · simpa only [Sym2.eq_swap] using he
      · change b ∈ component (delete H R) o
        rw [hdel]
        exact hob
  · rintro ⟨x,y,he,hx,⟨t,ht,hty⟩,hox⟩
    refine ⟨t,ht,?_⟩
    rw [openGraph_force_true G ω e x y he]
    apply SimpleGraph.Reachable.symm
    apply (Wiring.reachable_sup_edge (G.openGraph ω) x y o t).mpr
    exact Or.inr (Or.inl ⟨hox.mono (delete_le _ _),hty.symm⟩)

lemma boundaryReach_closed (o : V) (T : Set V) (ω : Set E) (e : E)
    (h : boundaryReach G (roots (G.openGraph ω) T)
      (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e) : ¬ ω e := by
  rintro heω
  obtain ⟨x,y,he,hx,hy,_⟩ := h
  have hxy : x ≠ y := fun heq => hx (heq ▸ hy)
  have ha : (G.openGraph ω).Adj y x := by
    apply SimpleGraph.Adj.symm
    exact ⟨⟨e,heω,he⟩,hxy⟩
  exact hx (roots_closed hy ha)

end CriticalPercolation.Sharpness
end
end CurrentModule1

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BoundaryCount
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule2
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open FiniteProduct ClusterDeletion

lemma expect_exposure_finiteRange {I A B : Type*} [Fintype I] [Fintype A]
    (w : I → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (r : (I → A) → B) (D : B → Set I)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (I → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  let : Fintype (Set.range r) := (Set.finite_range r).fintype
  let r' : (I → A) → Set.range r := fun ω => ⟨r ω,ω,rfl⟩
  exact expect_exposure w hw r' (fun b => D b.val)
    (fun b ω ω' hω => by
      apply propext
      simpa only [r',Subtype.ext_iff] using (hr b.val hω).to_iff)
    (fun b => f b.val) (fun b => hf b.val)

variable {V E : Type*} [Fintype E] (G : BondGraph V E)

lemma spatialMarkov (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (T : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω => F (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T))) =
      expect w (fun ω => expect w (fun ω' => F (roots (G.openGraph ω) T)
        (delete (G.openGraph ω') (roots (G.openGraph ω) T)))) := by
  refine expect_exposure_finiteRange w hw
    (fun ω => roots (G.openGraph ω) T) G.incidentEdges
    (G.dependsOn_exact_roots T)
    (fun R ω => F R (delete (G.openGraph ω) R)) ?_
  intro R ω ω' hω
  exact congrArg (F R) (G.delete_openGraph_dependsOn R hω)

omit [Fintype E] in
lemma closedPivot_reachesTarget (o : V) (T : Set V) (ω : Set E) (e : E) :
    closedPivot (reachesTarget G o T) e ω ↔
      o ∉ roots (G.openGraph ω) T ∧
      boundaryReach G (roots (G.openGraph ω) T)
        (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e := by
  constructor
  · rintro ⟨_,ho,he⟩
    exact ⟨ho,(target_creating_iff G o T ω e ho).mp he⟩
  · rintro ⟨ho,he⟩
    exact ⟨boundaryReach_closed G o T ω e he,ho,
      (target_creating_iff G o T ω e ho).mpr he⟩

lemma sum_closedPivot_eq (p : ℝ) (o : V) (T : Set V) :
    ∑ e, probability p (closedPivot (reachesTarget G o T) e) =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          expect (fun _ : E => weight p) (fun ω' => boundaryCount G o
            (roots (G.openGraph ω) T)
            (delete (G.openGraph ω') (roots (G.openGraph ω) T))) else 0) := by
  have hs := spatialMarkov G (fun _ : E => weight p) (fun _ => weight_sum p)
    T (fun R H => if o ∉ R then boundaryCount G o R H else 0)
  unfold probability
  rw [← expect_sum]
  calc
    _ = expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryCount G o (roots (G.openGraph ω) T)
            (delete (G.openGraph ω) (roots (G.openGraph ω) T)) else 0) := by
      congr 1
      funext ω
      have he (e : E) : closedPivot (reachesTarget G o T) e ω ↔
          o ∉ roots (G.openGraph ω) T ∧ boundaryReach G (roots (G.openGraph ω) T)
            (delete (G.openGraph ω) (roots (G.openGraph ω) T)) o e :=
        closedPivot_reachesTarget G o T ω e
      simp only [he]
      by_cases ho : o ∈ roots (G.openGraph ω) T
      · simp [ho]
      · simp [ho,boundaryCount]
    _ = _ := by
      rw [hs]
      congr 1
      funext ω
      split_ifs <;> simp only [expect_zero]

lemma exposedFlux_identity (p : ℝ) (o : V) (T : Set V) :
    p * (∑ e, probability p (closedPivot (reachesTarget G o T) e)) =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryFlux G p o (roots (G.openGraph ω) T) else 0) := by
  rw [sum_closedPivot_eq, ← expect_const_mul]
  congr 1
  funext ω
  split_ifs <;> simp only [boundaryFlux,mul_zero]

theorem derivative_identity {p : ℝ} (hp : p ∈ Ioo 0 1) (o : V) (T : Set V) :
    p * (1-p) * deriv (fun q => probability q (reachesTarget G o T)) p =
      expect (fun _ : E => weight p) (fun ω =>
        if o ∉ roots (G.openGraph ω) T then
          boundaryFlux G p o (roots (G.openGraph ω) T) else 0) := by
  have hd := hasDerivAt_probability_closedPivot hp (reachesTarget G o T)
    (fun _ _ h => reachesTarget_mono G o T h)
  rw [hd.deriv, ← exposedFlux_identity]
  field_simp [(sub_pos.mpr hp.2).ne']

theorem differential_inequality {p a : ℝ} (hp : p ∈ Ioo 0 1) (o : V) (T : Set V)
    (hflux : ∀ R : Set V, T ⊆ R → o ∉ R → a ≤ boundaryFlux G p o R) :
    a * (1-probability p (reachesTarget G o T)) ≤
      p * (1-p) * deriv (fun q => probability q (reachesTarget G o T)) p := by
  rw [derivative_identity G hp o T]
  have hcomp : expect (fun _ : E => weight p)
      (fun ω => if o ∉ roots (G.openGraph ω) T then (1:ℝ) else 0) =
      1-probability p (reachesTarget G o T) := by
    calc
      _ = expect (fun _ : E => weight p) (fun ω =>
          1-(if reachesTarget G o T ω then (1:ℝ) else 0)) := by
        congr 1
        funext ω
        unfold reachesTarget
        by_cases ho : o ∈ roots (G.openGraph ω) T <;> simp [ho]
      _ = _ := by
        rw [expect_sub,expect_const _ (fun _ => weight_sum p)]
        rfl
  rw [← hcomp, ← expect_const_mul]
  apply expect_mono (fun _ b => weight_nonneg ⟨hp.1.le,hp.2.le⟩ b)
  intro ω
  by_cases ho : o ∈ roots (G.openGraph ω) T
  · simp [ho]
  · simp only [ho,not_false_eq_true,ite_true, if_true,mul_one]
    exact hflux (roots (G.openGraph ω) T) (roots_self _ _) ho

end CriticalPercolation.Sharpness
end
end CurrentModule2

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ContinuousProbability
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

variable (G : BondGraph V E)

omit [Fintype E] in
lemma boundary_event_mono (o : V) (R : Set V) (e : E) {ω ω' : Set E}
    (h : ω ⊆ ω') :
    boundaryReach G R (delete (G.openGraph ω) R) o e →
      boundaryReach G R (delete (G.openGraph ω') R) o e := by
  rintro ⟨x,y,he,hx,hy,hox⟩
  have hdel : delete (G.openGraph ω) R ≤ delete (G.openGraph ω') R := by
    intro a b hh
    exact ⟨G.openGraph_mono h hh.1,hh.2⟩
  exact ⟨x,y,he,hx,hy,hox.mono hdel⟩

lemma boundaryFlux_eq_sum (p : ℝ) (o : V) (R : Set V) :
    boundaryFlux G p o R = p * ∑ e, probability p
      (fun ω => boundaryReach G R (delete (G.openGraph ω) R) o e) := by
  simp only [boundaryFlux,boundaryCount,expect_sum,probability]

lemma boundaryFlux_monotoneOn (o : V) (R : Set V) :
    MonotoneOn (fun p : ℝ => boundaryFlux G p o R) (Icc 0 1) := by
  intro p hp q hq hpq
  simp only [boundaryFlux_eq_sum]
  apply mul_le_mul hpq _ (Finset.sum_nonneg fun e _ => probability_nonneg hp _) hq.1
  apply Finset.sum_le_sum
  intro e _
  exact probability_monotoneOn _ (fun _ _ h => boundary_event_mono G o R e h) hp hq hpq

theorem uniform_escape_lower_bound {p q : ℝ} (hp : p ∈ Ioo 0 1)
    (hpq : p < q) (hq : q < 1) (o : V) (T : Set V)
    (hflux : ∀ R : Set V, T ⊆ R → o ∉ R → 1 ≤ boundaryFlux G p o R) :
    (q-p)/(1+q-p) ≤ probability q (reachesTarget G o T) := by
  let F := reachesTarget G o T
  have hF : ∀ s t, s ⊆ t → F s → F t := fun _ _ h => reachesTarget_mono G o T h
  have hq0 : 0 < q := hp.1.trans hpq
  obtain ⟨c,hc,hderiv⟩ := exists_deriv_eq_slope
    (fun r => probability r F) hpq (continuous_probability F).continuousOn
    (fun r hr => (hasDerivAt_probability ⟨hp.1.trans hr.1,hr.2.trans hq⟩ F hF
      ).differentiableAt.differentiableWithinAt)
  have hc01 : c ∈ Ioo 0 1 := ⟨hp.1.trans hc.1,hc.2.trans hq⟩
  have hd := differential_inequality G hc01 o T (a := 1) (fun R hTR ho =>
    (hflux R hTR ho).trans (boundaryFlux_monotoneOn G o R
      ⟨hp.1.le,hp.2.le⟩ ⟨hc01.1.le,hc01.2.le⟩ hc.1.le))
  have hmono := probability_monotoneOn F hF ⟨hc01.1.le,hc01.2.le⟩
    ⟨hq0.le,hq.le⟩ hc.2.le
  have hdnonneg : 0 ≤ deriv (fun r => probability r F) c := by
    rw [(hasDerivAt_probability hc01 F hF).deriv]
    exact Finset.sum_nonneg fun e _ => probability_nonneg ⟨hc01.1.le,hc01.2.le⟩ _
  have hfactor : c*(1-c) ≤ 1 := by nlinarith [sq_nonneg c]
  have hds : c*(1-c)*deriv (fun r => probability r F) c ≤
      deriv (fun r => probability r F) c := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hdnonneg
  have hlow : 1-probability q F ≤ deriv (fun r => probability r F) c := by
    change 1*(1-probability c F) ≤ _ at hd
    linarith
  have hdiff := mul_le_mul_of_nonneg_right hlow (sub_pos.mpr hpq).le
  have heq := (eq_div_iff (sub_pos.mpr hpq).ne').mp hderiv
  have hnonneg := probability_nonneg ⟨hp.1.le,hp.2.le⟩ F
  apply (div_le_iff₀ (by linarith : 0 < 1+q-p)).mpr
  change q-p ≤ probability q F * (1+q-p)
  nlinarith

end CriticalPercolation.Sharpness
end
end CurrentModule5

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SharpnessPhi
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext e
  simp only [BondGraph.incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]

lemma incident_mono {S T : Set V} (h : S ⊆ T) : G.incidentEdges S ⊆ G.incidentEdges T := by
  rintro e ⟨v,hv,he⟩
  exact ⟨v,h hv,he⟩

lemma delete_restrict_incident {S : Set V} {K : Set E} (hK : G.incidentEdges S ⊆ K)
    (ω : Set E) : delete (G.openGraph (K ∩ ω)) Sᶜ = delete (G.openGraph ω) Sᶜ := by
  ext x y
  constructor
  · exact fun h => ⟨G.openGraph_mono inter_subset_right h.1,h.2⟩
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hx,hy⟩
    refine ⟨⟨⟨e,⟨hK ?_,he⟩,hend⟩,hne⟩,hx,hy⟩
    exact ⟨x,not_not.mp hx,by rw [hend]; simp⟩

lemma boundaryReach_incident {S : Set V} {H : SimpleGraph V} {o : V} {e : E}
    (h : boundaryReach G Sᶜ H o e) : e ∈ G.incidentEdges S := by
  obtain ⟨x,y,he,hx,_hy,_hox⟩ := h
  exact ⟨x,not_not.mp hx,by rw [he]; simp⟩

lemma boundary_measure_support (p : unitInterval) (o : V) (S : Set V) :
    Function.support (fun e => (G.law p).real
      {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e}) ⊆ G.incidentEdges S := by
  intro e he
  by_contra hn
  apply he
  have hh : {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} = ∅ := by
    ext ω
    exact iff_false_intro (fun h => hn (boundaryReach_incident G h))
  change (G.law p).real {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} = 0
  rw [hh,measureReal_empty]

lemma phi_eq_boundaryFlux (p : unitInterval) (o : V) (S : Set V)
    (K : Set E) (hK : K.Finite) (hSK : G.incidentEdges S ⊆ K) :
    letI := hK.fintype
    phi G p o S = boundaryFlux (G.restrictEdges K) (p : ℝ) o Sᶜ := by
  let := hK.fintype
  rw [phi, ← tsum_subtype_eq_of_support_subset ((boundary_measure_support G p o S).trans hSK),
    tsum_fintype, boundaryFlux_eq_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [finite_probability_restrict G p K hK]
  congr 1
  ext ω
  change boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e.val ↔
    boundaryReach (G.restrictEdges K) Sᶜ
      (delete ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)) Sᶜ) o e
  rw [G.restrictEdges_openGraph, delete_restrict_incident G hSK]
  rfl

lemma restricted_escape_le (p : unitInterval) (o : V) (T : Set V)
    (K : Set E) (hK : K.Finite) :
    letI := hK.fintype
    probability (p : ℝ) (reachesTarget (G.restrictEdges K) o T) ≤
      (G.law p).real (G.hitEvent o T) := by
  let := hK.fintype
  rw [finite_probability_restrict G p K hK]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  change reachesTarget (G.restrictEdges K) o T (Subtype.val ⁻¹' ω) at hω
  apply (reachesTarget_iff_hitEvent G o T ω).mp
  apply reachesTarget_mono G o T inter_subset_right
  change o ∈ roots (G.openGraph (K ∩ ω)) T
  simpa only [reachesTarget, G.restrictEdges_openGraph] using hω

end CriticalPercolation.Sharpness
end
end CurrentModule6

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InfiniteEscapeLowerBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule8
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {E V : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma infinite_escape_lower_bound (hl : G.LocallyFinite)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p < q) (hq : q < 1)
    (o : V) (hflux : ∀ S : Set V, S.Finite → o ∈ S → 1 ≤ phi G p o S) :
    ((q : ℝ)-p)/(1+q-p) ≤ (G.law q).real (G.infiniteEvent o) := by
  let L := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  apply ge_of_tendsto (G.tendsto_real_hit_compl q L o)
  apply Eventually.of_forall
  intro n
  let K := G.incidentEdges (L n)
  have hK : K.Finite := finite_incident G hl (L.finite n)
  let := hK.fintype
  have hf : ∀ R : Set V, (L n)ᶜ ⊆ R → o ∉ R →
      1 ≤ boundaryFlux (G.restrictEdges K) (p : ℝ) o R := by
    intro R hR ho
    have hsub : Rᶜ ⊆ L n := by
      simpa only [compl_compl] using Set.compl_subset_compl.mpr hR
    have he := phi_eq_boundaryFlux G p o Rᶜ K hK (incident_mono G hsub)
    simp only [compl_compl] at he
    rw [← he]
    exact hflux Rᶜ ((L.finite n).subset hsub) ho
  exact (uniform_escape_lower_bound (G.restrictEdges K)
    ⟨hp, (show (p : ℝ)<q from hpq).trans (show (q : ℝ)<1 from hq)⟩
    hpq hq o (L n)ᶜ hf).trans (restricted_escape_le G q o (L n)ᶜ K hK)

theorem subcritical_finite_size (hl : G.LocallyFinite)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V) :
    ∃ S : Set V, S.Finite ∧ o ∈ S ∧ phi G p o S < 1 := by
  by_cases hp0 : (p : ℝ) = 0
  · exact ⟨{o},Set.finite_singleton o,Set.mem_singleton o,by simp [phi,hp0]⟩
  have hp_pos : 0 < (p : ℝ) := lt_of_le_of_ne p.property.1 (Ne.symm hp0)
  by_contra h
  have hflux : ∀ S : Set V, S.Finite → o ∈ S → 1 ≤ phi G p o S := by
    intro S hS ho
    exact le_of_not_gt (fun hh => h ⟨S,hS,ho,hh⟩)
  let q : unitInterval := ⟨((p : ℝ)+(G.criticalProbability : ℝ))/2, by
    constructor
    · linarith [p.property.1,G.criticalProbability.property.1]
    · linarith [p.property.2,G.criticalProbability.property.2]⟩
  have hpq : p < q := by
    change (p : ℝ) < ((p : ℝ)+(G.criticalProbability : ℝ))/2
    have hh : (p : ℝ) < G.criticalProbability := hp
    linarith
  have hqc : q < G.criticalProbability := by
    change ((p : ℝ)+(G.criticalProbability : ℝ))/2 < (G.criticalProbability : ℝ)
    have hh : (p : ℝ) < G.criticalProbability := hp
    linarith
  have hq1 : q < 1 := hqc.trans_le G.criticalProbability.property.2
  have hb := infinite_escape_lower_bound G hl p q hp_pos hpq hq1 o hflux
  have hz : (G.law q).real (G.infiniteEvent o) = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
    apply measure_mono_null (show G.infiniteEvent o ⊆ G.percolates from fun _ hω => ⟨o,hω⟩)
    exact G.law_percolates_eq_zero_of_lt_critical hqc
  rw [hz] at hb
  have hd : 0 < (q : ℝ)-p := sub_pos.mpr hpq
  have hden : 0 < 1+(q : ℝ)-p := by linarith
  exact (not_le_of_gt (div_pos hd hden)) hb

end CriticalPercolation.Sharpness
end
end CurrentModule8

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DeleteImageIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule9
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma measurableSet_boundary (hl : G.LocallyFinite)
    (o : V) (S : Set V) (hS : S.Finite) (e : E) :
    MeasurableSet {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} := by
  let K := G.incidentEdges S
  have hK : K.Finite := finite_incident G hl hS
  let := hK.fintype
  have hm : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set K)) ⁻¹'
        {η | boundaryReach G Sᶜ
          (delete ((G.restrictEdges K).openGraph η) Sᶜ) o e} := by
    ext ω
    simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.restrictEdges_openGraph,
      delete_restrict_incident G (K := K) Subset.rfl]
  rw [he]
  exact hm (.of_discrete)

lemma boundary_image (φ : G.Aut) (S : Set V) (o : V) (e : E) (ω : Set E) :
    boundaryReach G (φ.vertex '' S)ᶜ
      (delete (G.openGraph (φ.edge '' ω)) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e) ↔
      boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e := by
  have himg : (φ.vertex '' S)ᶜ = φ.vertex '' Sᶜ := by
    ext v
    obtain ⟨x,rfl⟩ := φ.vertex.surjective v
    simp only [Set.mem_compl_iff,Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
  rw [himg]
  constructor
  · rintro ⟨a,b,he,ha,hb,hr⟩
    obtain ⟨x,rfl⟩ := φ.vertex.surjective a
    obtain ⟨y,rfl⟩ := φ.vertex.surjective b
    have hx : x ∉ Sᶜ := by simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using ha
    have hy : y ∈ Sᶜ := by simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using hb
    rw [φ.preserves,← Sym2.map_mk] at he
    exact ⟨x,y,Sym2.map.injective φ.vertex.injective he,hx,hy,
      (SimpleGraph.Iso.reachable_iff (φ := deleteImageIso G φ ω Sᶜ)).mp hr⟩
  · rintro ⟨x,y,he,hx,hy,hr⟩
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,?_,?_⟩
    · rw [φ.preserves,he,Sym2.map_mk]
    · simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using hx
    · exact ⟨y,hy,rfl⟩
    · exact (SimpleGraph.Iso.reachable_iff (φ := deleteImageIso G φ ω Sᶜ)).mpr hr

lemma boundary_real_image (hl : G.LocallyFinite) (φ : G.Aut) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) (e : E) :
    (G.law p).real {ω | boundaryReach G (φ.vertex '' S)ᶜ
      (delete (G.openGraph ω) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e)} =
    (G.law p).real {ω | boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e} := by
  change (G.law p _).toReal = (G.law p _).toReal
  congr 1
  calc
    _ = (G.law p).map (fun ω : Set E => φ.edge '' ω)
        {ω | boundaryReach G (φ.vertex '' S)ᶜ
          (delete (G.openGraph ω) (φ.vertex '' S)ᶜ) (φ.vertex o) (φ.edge e)} := by
      rw [G.law_map_aut p φ]
    _ = _ := by
      rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
        (measurableSet_boundary G hl _ _ (hS.image _) _)]
      congr 1
      ext ω
      exact boundary_image G φ S o e ω

lemma phi_image (hl : G.LocallyFinite) (φ : G.Aut) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) :
    phi G p (φ.vertex o) (φ.vertex '' S) = phi G p o S := by
  unfold phi
  congr 1
  rw [← φ.edge.tsum_eq]
  apply tsum_congr
  intro e
  exact boundary_real_image G hl φ p S hS o e

theorem uniform_subcritical_domains [Countable V] [Countable E] [Nonempty V]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) :
    ∃ N : ℕ, ∃ a : ℝ, a < 1 ∧ ∀ o : V,
      ∃ S : Set V, S.Finite ∧ o ∈ S ∧ S.ncard ≤ N ∧ phi G p o S ≤ a := by
  obtain ⟨R,hR,horbit⟩ := hq
  have hne : R.Nonempty := by
    obtain ⟨v⟩ := ‹Nonempty V›
    obtain ⟨r,hr,_⟩ := horbit v
    exact ⟨r,hr⟩
  choose D hD hoD hphi using subcritical_finite_size G hl p hp
  obtain ⟨r,hr,hmax⟩ := Set.exists_max_image R (fun o => phi G p o (D o)) hR hne
  let N := ∑ o ∈ hR.toFinset, (D o).ncard
  refine ⟨N,phi G p r (D r),hphi r,?_⟩
  intro o
  obtain ⟨s,hs,φ,rfl⟩ := horbit o
  refine ⟨φ.vertex '' D s,(hD s).image _,⟨s,hoD s,rfl⟩,?_,?_⟩
  · rw [Set.ncard_image_of_injective _ φ.vertex.injective]
    exact Finset.single_le_sum (f := fun o => (D o).ncard)
      (fun _ _ => Nat.zero_le _) (hR.mem_toFinset.mpr hs)
  · rw [phi_image G hl φ p (D s) (hD s) s]
    exact hmax s hs

end CriticalPercolation.Sharpness
end
end CurrentModule9

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_CutInside
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule3
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma cut_ends (S : Set V) (e : E) :
    G.ends e = s(cutInside G S e, cutOutside G S e) := by
  unfold cutInside cutOutside
  split_ifs
  · exact (G.ends e).out_eq.symm
  · exact (G.ends e).out_eq.symm.trans (Sym2.eq_swap)

lemma cut_orientation {S : Set V} {e : E} {x y : V}
    (he : G.ends e = s(x,y)) (hx : x ∈ S) (hy : y ∉ S) :
    cutInside G S e = x ∧ cutOutside G S e = y := by
  have h : s((G.ends e).out.1,(G.ends e).out.2) = s(x,y) := (G.ends e).out_eq.trans he
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · change (G.ends e).out.1 = x at h1
    change (G.ends e).out.2 = y at h2
    simp only [cutInside,cutOutside,h1,h2,ite_eq_left hx,and_self]
  · change (G.ends e).out.1 = y at h1
    change (G.ends e).out.2 = x at h2
    simp only [cutInside,cutOutside,h1,h2,ite_eq_right hy,and_self]

lemma boundaryReach_iff_cut (S : Set V) (H : SimpleGraph V) (o : V) (e : E) :
    boundaryReach G Sᶜ H o e ↔ IsCut G S e ∧ H.Reachable o (cutInside G S e) := by
  constructor
  · rintro ⟨x,y,he,hx,hy,hr⟩
    change y ∉ S at hy
    have hh := cut_orientation G he (not_not.mp hx) hy
    exact ⟨by simpa only [IsCut,hh.1,hh.2] using And.intro (not_not.mp hx) hy,
      by simpa only [hh.1] using hr⟩
  · rintro ⟨hc,hr⟩
    exact ⟨_,_,cut_ends G S e,not_not.mpr hc.1,hc.2,hr⟩

lemma internalCluster_self (S : Set V) (o : V) (ω : Set E) :
    o ∈ internalCluster G S o ω := .refl _

lemma internalCluster_subset (S : Set V) {o : V} (ho : o ∈ S) (ω : Set E) :
    internalCluster G S o ω ⊆ S := by
  intro v hv
  exact reachable_mem_of_closed (H := delete (G.openGraph ω) Sᶜ)
    (U := S) (fun {_ _} _ h => not_not.mp h.2.2) ho hv

lemma internal_adj_eq {S C : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ internalIncident G S C, e ∈ ω ↔ e ∈ ω') {x y : V} (hx : x ∈ C) :
    (delete (G.openGraph ω) Sᶜ).Adj x y ↔ (delete (G.openGraph ω') Sᶜ).Adj x y := by
  have hh (e) (he : G.ends e = s(x,y)) (hxS : x ∈ S) (hyS : y ∈ S) :
      e ∈ internalIncident G S C := by
    refine ⟨⟨x,hx,by rw [he]; simp⟩,?_⟩
    intro v hv
    rw [he,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl <;> assumption
  constructor
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hxs,hys⟩
    exact ⟨⟨⟨e,(hω e (hh e hend (not_not.mp hxs) (not_not.mp hys))).mp he,hend⟩,hne⟩,hxs,hys⟩
  · rintro ⟨⟨⟨e,he,hend⟩,hne⟩,hxs,hys⟩
    exact ⟨⟨⟨e,(hω e (hh e hend (not_not.mp hxs) (not_not.mp hys))).mpr he,hend⟩,hne⟩,hxs,hys⟩

lemma internalCluster_eq_of_incident {S C : Set V} {o : V} {ω ω' : Set E}
    (hC : internalCluster G S o ω = C)
    (hω : ∀ e ∈ internalIncident G S C, e ∈ ω ↔ e ∈ ω') :
    internalCluster G S o ω' = C := by
  change component (delete (G.openGraph ω') Sᶜ) o = C
  rw [← roots_singleton]
  exact roots_eq_of_adj_eq_incident
    (by simpa only [roots_singleton, internalCluster] using hC)
    (fun {_ _} hx => internal_adj_eq G hω hx)

lemma dependsOn_internalCluster (S C : Set V) (o : V) :
    DependsOn (fun ω : Set E => internalCluster G S o ω = C) (internalIncident G S C) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => internalCluster_eq_of_incident G h (fun e he => (hω e he).to_iff),
    fun h => internalCluster_eq_of_incident G h (fun e he => (hω e he).symm.to_iff)⟩

lemma last_exit {H : SimpleGraph V} {C : Set V} {o v : V}
    (ho : o ∈ C) (hv : v ∉ C) (hr : H.Reachable o v) :
    ∃ x ∈ C, ∃ y ∉ C, H.Adj x y ∧ (delete H C).Reachable y v := by
  have hh : ∀ z, H.Reachable v z →
      (z ∉ C ∧ (delete H C).Reachable v z) ∨
        ∃ x ∈ C, ∃ y ∉ C, H.Adj x y ∧ (delete H C).Reachable y v := by
    intro z hz
    rw [SimpleGraph.reachable_iff_reflTransGen] at hz
    induction hz with
    | refl => exact Or.inl ⟨hv,.refl _⟩
    | @tail a b _ hab ih =>
      rcases ih with ⟨ha,hva⟩ | ih
      · by_cases hb : b ∈ C
        · exact Or.inr ⟨b,hb,a,ha,hab.symm,hva.symm⟩
        · exact Or.inl ⟨hb,hva.trans (SimpleGraph.Adj.reachable ⟨hab,ha,hb⟩)⟩
      · exact Or.inr ih
  exact (hh o hr.symm).resolve_left (fun h => h.1 ho)

lemma internalCluster_exit (S : Set V) (o : V) (ho : o ∈ S) (ω : Set E) {v : V}
    (hv : v ∉ S) (hr : (G.openGraph ω).Reachable o v) :
    ∃ e : E, IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω ∧ e ∈ ω ∧
      (delete (G.openGraph ω) (internalCluster G S o ω)).Reachable (cutOutside G S e) v := by
  obtain ⟨x,hx,y,hy,hxy,hyv⟩ := last_exit (internalCluster_self G S o ω)
    (fun hc => hv (internalCluster_subset G S ho ω hc)) hr
  have hxS : x ∈ S := internalCluster_subset G S ho ω hx
  have hyS : y ∉ S := by
    intro hyS
    exact hy (hx.trans (SimpleGraph.Adj.reachable ⟨hxy,not_not.mpr hxS,not_not.mpr hyS⟩))
  obtain ⟨⟨e,he,hend⟩,_hne⟩ := hxy
  obtain ⟨hi,ho'⟩ := cut_orientation G hend hxS hyS
  exact ⟨e,by simpa only [IsCut,hi,ho'] using And.intro hxS hyS,
    by rwa [hi],he,by rwa [ho']⟩

lemma cut_not_internalIncident {S C : Set V} {e : E} (hc : IsCut G S e) :
    e ∉ internalIncident G S C := by
  intro h
  apply hc.2
  apply h.2
  rw [cut_ends G S e]
  simp

lemma delete_update_incident {C : Set V} {e : E} (he : e ∈ G.incidentEdges C)
    (ω : Set E) (b : Prop) :
    delete (G.openGraph (Function.update ω e b)) C = delete (G.openGraph ω) C := by
  apply G.delete_openGraph_dependsOn C
  intro j hj
  have hje : j ≠ e := by rintro rfl; exact hj he
  exact Function.update_of_ne hje _ _

end CriticalPercolation.Sharpness
end
end CurrentModule3

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_Leak
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule4
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype E]

lemma probability_mono_event {p : ℝ} (hp : p ∈ Icc 0 1) {F F' : Set E → Prop}
    (h : ∀ ω, F ω → F' ω) : probability p F ≤ probability p F' := by
  apply expect_mono (fun _ => weight_nonneg hp)
  intro ω
  by_cases hF : F ω
  · simp only [ite_eq_left hF,ite_eq_left (h ω hF),le_refl]
  · simp only [ite_eq_right hF]
    split_ifs <;> norm_num

variable (G : BondGraph V E)

omit [Fintype E] in
lemma leak_nonneg (S C : Set V) (e : E) (v : V) (ω : Set E) :
    0 ≤ leak G S C e v ω := by unfold leak; split_ifs <;> norm_num

omit [Fintype E] in
lemma leak_dependsOn (S C : Set V) (e : E) (v : V) :
    DependsOn (leak G S C e v) (internalIncident G S C)ᶜ := by
  intro ω ω' hω
  by_cases hc : IsCut G S e ∧ cutInside G S e ∈ C
  · have he : ω e = ω' e := hω e (cut_not_internalIncident G hc.1)
    have hg : delete (G.openGraph ω) C = delete (G.openGraph ω') C :=
      G.delete_openGraph_dependsOn C (fun j hj => hω j (fun hD => hj hD.1))
    simp only [leak,ite_eq_left hc]
    change (if ω e ∧ _ then (1:ℝ) else 0) = if ω' e ∧ _ then 1 else 0
    simp only [he,hg]
  · simp only [leak,ite_eq_right hc]

lemma leak_expect (p : ℝ) (S C : Set V) (e : E) (v : V) :
    expect (fun _ : E => weight p) (leak G S C e v) =
      if IsCut G S e ∧ cutInside G S e ∈ C then
        p * probability p (fun ω => (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v)
      else 0 := by
  by_cases hc : IsCut G S e ∧ cutInside G S e ∈ C
  · rw [ite_eq_left hc]
    have heI : e ∈ G.incidentEdges C :=
      ⟨cutInside G S e,hc.2,by rw [cut_ends G S e]; simp⟩
    calc
      _ = expect (fun _ : E => weight p) (fun ω => if ω e = True then
          (if (delete (G.openGraph ω) C).Reachable (cutOutside G S e) v then 1 else 0) else 0) := by
        congr 1
        funext ω
        simp only [leak,ite_eq_left hc]
        change (if ω e ∧ (delete (G.openGraph ω) C).Reachable
          (cutOutside G S e) v then (1:ℝ) else 0) = _
        by_cases he : ω e <;> simp [he]
      _ = weight p True * expect (fun _ : E => weight p) (fun ω =>
          if (delete (G.openGraph (Function.update ω e True)) C).Reachable
            (cutOutside G S e) v then 1 else 0) :=
        by
          convert expect_coordinate_mask (fun _ : E => weight p) (fun _ => weight_sum p)
            e True (fun ω => if (delete (G.openGraph ω) C).Reachable
              (cutOutside G S e) v then (1:ℝ) else 0) using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          funext ω
          split_ifs <;> rfl
      _ = _ := by
        simp only [weight,ite_true, if_true]
        congr 1
        unfold probability
        congr 1
        funext ω
        erw [delete_update_incident G heI]
  · rw [ite_eq_right hc]
    calc
      _ = expect (fun _ : E => weight p) (fun _ => 0) := by
        congr 1; funext ω; simp only [leak,ite_eq_right hc]
      _ = 0 := expect_const _ (fun _ => weight_sum p) 0

lemma leak_expect_le {p : ℝ} (hp : p ∈ Icc 0 1) (S C : Set V) (e : E) (v : V) :
    expect (fun _ : E => weight p) (leak G S C e v) ≤
      (if IsCut G S e ∧ cutInside G S e ∈ C then (1:ℝ) else 0) *
        (p * probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v)) := by
  rw [leak_expect]
  split_ifs
  · simp only [one_mul]
    apply mul_le_mul_of_nonneg_left _ hp.1
    exact probability_mono_event hp (fun _ h => h.mono (delete_le _ _))
  · simp

lemma boundary_probability_cut (p : ℝ) (S : Set V) (o : V) (e : E) :
    probability p (fun ω => boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e) =
      expect (fun _ : E => weight p) (fun ω =>
        if IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω then (1:ℝ) else 0) := by
  unfold probability
  congr 1
  funext ω
  simp only [boundaryReach_iff_cut,internalCluster,component,Set.mem_ofPred_eq]
  congr 1

lemma exposed_leak_le {p : ℝ} (hp : p ∈ Icc 0 1) (S : Set V) (o v : V) (e : E) :
    expect (fun _ : E => weight p) (fun ω => leak G S (internalCluster G S o ω) e v ω) ≤
      p * probability p (fun ω => boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e) *
        probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v) := by
  rw [expect_exposure_finiteRange _ (fun _ => weight_sum p)
    (fun ω => internalCluster G S o ω) (internalIncident G S)
    (fun C => dependsOn_internalCluster G S C o) (fun C => leak G S C e v)
    (fun C => leak_dependsOn G S C e v)]
  calc
    _ ≤ expect (fun _ : E => weight p) (fun ω =>
        (if IsCut G S e ∧ cutInside G S e ∈ internalCluster G S o ω then (1:ℝ) else 0) *
        (p * probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v))) :=
      expect_mono (fun _ => weight_nonneg hp) (fun _ => leak_expect_le G hp S _ e v)
    _ = _ := by rw [expect_mul_const,← boundary_probability_cut]; ring

theorem simon_lieb {p : ℝ} (hp : p ∈ Icc 0 1) (S : Set V) (o : V) (ho : o ∈ S)
    (v : V) (hv : v ∉ S) :
    probability p (fun ω => (G.openGraph ω).Reachable o v) ≤
      ∑ e, p * probability p (fun ω => boundaryReach G Sᶜ
        (delete (G.openGraph ω) Sᶜ) o e) *
          probability p (fun ω => (G.openGraph ω).Reachable (cutOutside G S e) v) := by
  have hpoint (ω : Set E) : (if (G.openGraph ω).Reachable o v then (1:ℝ) else 0) ≤
      ∑ e, leak G S (internalCluster G S o ω) e v ω := by
    by_cases hr : (G.openGraph ω).Reachable o v
    · rw [ite_eq_left hr]
      obtain ⟨e,hc,hi,he,hv'⟩ := internalCluster_exit G S o ho ω hv hr
      have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset E)) =>
        leak_nonneg G S (internalCluster G S o ω) j v ω) (Finset.mem_univ e)
      have heq : leak G S (internalCluster G S o ω) e v ω = 1 := by
        simp only [leak, ite_eq_left (And.intro hc hi), ite_eq_left (And.intro he hv')]
      rwa [heq] at hh
    · rw [ite_eq_right hr]
      exact Finset.sum_nonneg (fun _ _ => leak_nonneg G S (internalCluster G S o ω) _ v ω)
  calc
    _ ≤ expect (fun _ : E => weight p) (fun ω => ∑ e, leak G S (internalCluster G S o ω) e v ω) :=
      expect_mono (fun _ => weight_nonneg hp) hpoint
    _ = ∑ e, expect (fun _ : E => weight p) (fun ω => leak G S (internalCluster G S o ω) e v ω) :=
      expect_sum _ _
    _ ≤ _ := Finset.sum_le_sum (fun e _ => exposed_leak_le G hp S o v e)

end CriticalPercolation.Sharpness
end
end CurrentModule4

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteSumConnection
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule7
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
open ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma finite_sum_connection_le [Fintype E] {p : ℝ} (hp : p ∈ Icc 0 1)
    (A : Finset V) (S : Set V) (hS : S.Finite) (o : V) (ho : o ∈ S)
    (M : ℝ) (hM : ∀ y : V, ∑ v ∈ A,
      probability p (fun ω => (G.openGraph ω).Reachable y v) ≤ M) :
    ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable o v) ≤
      S.ncard + boundaryFlux G p o Sᶜ * M := by
  let f := fun x y => probability p (fun ω => (G.openGraph ω).Reachable x y)
  let c := fun e => p * probability p (fun ω =>
    boundaryReach G Sᶜ (delete (G.openGraph ω) Sᶜ) o e)
  have hc : ∀ e, 0 ≤ c e := fun e => mul_nonneg hp.1 (probability_nonneg hp _)
  have hout (v) (hv : v ∉ S) : f o v ≤ ∑ e, c e * f (cutOutside G S e) v :=
    simon_lieb G hp S o ho v hv
  calc
    _ ≤ ∑ v ∈ A, ((if v ∈ S then (1:ℝ) else 0) +
        ∑ e, c e * f (cutOutside G S e) v) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hv : v ∈ S
      · simp only [ite_eq_left hv]
        exact (probability_le_one hp _).trans (le_add_of_nonneg_right
          (Finset.sum_nonneg fun e _ => mul_nonneg (hc e) (probability_nonneg hp _)))
      · simpa only [ite_eq_right hv,zero_add] using hout v hv
    _ = (A.filter (· ∈ S)).card + ∑ e, c e * ∑ v ∈ A, f (cutOutside G S e) v := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [← Finset.mul_sum]
      congr 1
      simp
    _ ≤ S.ncard + (∑ e, c e) * M := by
      apply add_le_add
      · exact_mod_cast Set.ncard_le_ncard
          (show (↑(A.filter (· ∈ S)) : Set V) ⊆ S from fun v hv => (Finset.mem_filter.mp hv).2) hS
      · rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hM _) (hc e)
    _ = _ := by
      rw [boundaryFlux_eq_sum,Finset.mul_sum]

lemma restricted_boundaryFlux_le_phi (hl : G.LocallyFinite) (p : unitInterval)
    (S : Set V) (hS : S.Finite) (o : V) (K : Set E) (hK : K.Finite) :
    letI := hK.fintype
    boundaryFlux (G.restrictEdges K) (p : ℝ) o Sᶜ ≤ phi G p o S := by
  let := hK.fintype
  let F := fun e => (G.law p).real {ω | boundaryReach G Sᶜ
    (delete (G.openGraph ω) Sᶜ) o e}
  have hF : Summable F := summable_of_hasFiniteSupport
    ((finite_incident G hl hS).subset (boundary_measure_support G p o S))
  rw [boundaryFlux_eq_sum,phi]
  apply mul_le_mul_of_nonneg_left _ p.property.1
  calc
    _ ≤ ∑ e : K, F e.val := by
      apply Finset.sum_le_sum
      intro e _
      rw [finite_probability_restrict G p K hK]
      apply measureReal_mono _ (measure_ne_top _ _)
      intro ω hω
      change boundaryReach (G.restrictEdges K) Sᶜ
        (delete ((G.restrictEdges K).openGraph (Subtype.val ⁻¹' ω)) Sᶜ) o e at hω
      rw [G.restrictEdges_openGraph] at hω
      have hh : boundaryReach G Sᶜ (delete (G.openGraph (K ∩ ω)) Sᶜ) o e.val := hω
      obtain ⟨x,y,he,hx,hy,hr⟩ := hh
      have hdel : delete (G.openGraph (K ∩ ω)) Sᶜ ≤ delete (G.openGraph ω) Sᶜ :=
        fun _ _ hab => ⟨G.openGraph_mono inter_subset_right hab.1,hab.2⟩
      exact ⟨x,y,he,hx,hy,hr.mono hdel⟩
    _ ≤ ∑' e, F e := by
      simpa only [tsum_fintype,Function.comp_def] using
        (tsum_comp_le_tsum_of_inj hF (fun e => measureReal_nonneg)
          (Subtype.val_injective : Function.Injective (Subtype.val : K → E)))

end CriticalPercolation.Sharpness
end
end CurrentModule7

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_TwoPoint
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule10
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

lemma hit_singleton_eq (o v : V) :
    G.hitEvent o {v} = {ω | (G.openGraph ω).Reachable o v} := by
  ext ω
  simp only [BondGraph.hitEvent,Set.mem_ofPred_eq,Set.inter_singleton_nonempty,BondGraph.cluster]

lemma twoPoint_nonneg (p : unitInterval) (o v : V) : 0 ≤ twoPoint G p o v := measureReal_nonneg

lemma finite_contraction [Fintype E] [Nonempty V] {p : ℝ} (hp : p ∈ Icc 0 1)
    (N : ℕ) (a : ℝ) (ha : a < 1)
    (hdom : ∀ o : V, ∃ S : Set V, S.Finite ∧ o ∈ S ∧ S.ncard ≤ N ∧
      boundaryFlux G p o Sᶜ ≤ a) (A : Finset V) (o : V) :
    ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable o v) ≤ N / (1-a) := by
  let f := fun y => ∑ v ∈ A, probability p (fun ω => (G.openGraph ω).Reachable y v)
  have hb : BddAbove (Set.range f) := ⟨A.card,by
    rintro _ ⟨y,rfl⟩
    calc
      _ ≤ ∑ _v ∈ A, (1:ℝ) := Finset.sum_le_sum fun v _ => probability_le_one hp _
      _ = _ := by simp⟩
  let M := sSup (Set.range f)
  have hM : ∀ y, f y ≤ M := fun y => le_csSup hb ⟨y,rfl⟩
  have hM0 : 0 ≤ M := (Finset.sum_nonneg (fun _ _ => probability_nonneg hp _)).trans (hM o)
  have hcon : M ≤ N + a * M := by
    apply csSup_le (Set.range_nonempty f)
    rintro _ ⟨y,rfl⟩
    obtain ⟨S,hS,hy,hn,hphi⟩ := hdom y
    exact (finite_sum_connection_le G hp A S hS y hy M hM).trans
      (add_le_add (Nat.cast_le.mpr hn) (mul_le_mul_of_nonneg_right hphi hM0))
  apply (hM o).trans
  apply (le_div_iff₀ (sub_pos.mpr ha)).mpr
  nlinarith

lemma finite_probability_connection (p : unitInterval) (K : Set E) (hK : K.Finite)
    (o v : V) :
    letI := hK.fintype
    probability (p : ℝ) (fun ω => ((G.restrictEdges K).openGraph ω).Reachable o v) =
      (G.law p).real {ω | K ∩ ω ∈ G.hitEvent o {v}} := by
  let := hK.fintype
  rw [finite_probability_restrict G p K hK,hit_singleton_eq]
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq,G.restrictEdges_openGraph]

theorem subcritical_susceptibility [Countable V] [Countable E] [Nonempty V]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) :
    ∃ C : ℝ, ∀ (A : Finset V) (o : V), ∑ v ∈ A, twoPoint G p o v ≤ C := by
  obtain ⟨N,a,ha,hdom⟩ := uniform_subcritical_domains G hl hq p hp
  refine ⟨N/(1-a),?_⟩
  intro A o
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  have hf (n : ℕ) : ∑ v ∈ A, (G.law p).real {ω | K n ∩ ω ∈ G.hitEvent o {v}} ≤
      N/(1-a) := by
    let := (K.finite n).fintype
    have hd : ∀ y : V, ∃ S : Set V, S.Finite ∧ y ∈ S ∧ S.ncard ≤ N ∧
        boundaryFlux (G.restrictEdges (K n)) (p : ℝ) y Sᶜ ≤ a := by
      intro y
      obtain ⟨S,hS,hy,hn,hphi⟩ := hdom y
      exact ⟨S,hS,hy,hn,(restricted_boundaryFlux_le_phi G hl p S hS y (K n) (K.finite n)).trans hphi⟩
    have hh := finite_contraction (G.restrictEdges (K n)) p.property N a ha hd A o
    simpa only [finite_probability_connection G p (K n) (K.finite n)] using hh
  have ht : Tendsto (fun n => ∑ v ∈ A, (G.law p).real
      {ω | K n ∩ ω ∈ G.hitEvent o {v}}) atTop (𝓝 (∑ v ∈ A, twoPoint G p o v)) := by
    apply tendsto_finsetSum
    intro v _
    simpa only [BondGraph.law,BernoulliProduct.law_const,twoPoint] using
      G.tendsto_real_hitEvent_exhaustion (fun _ : E => p) K o {v}
  exact le_of_tendsto ht (Eventually.of_forall hf)

theorem summable_subcritical_twoPoint [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V) :
    Summable (twoPoint G p o) := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨C,hC⟩ := subcritical_susceptibility G hl hq p hp
  exact summable_of_sum_le (twoPoint_nonneg G p o) (fun A => hC A o)

end CriticalPercolation.Sharpness
end
end CurrentModule10

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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_TwoPointSelf
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule11
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

lemma twoPoint_self (p : unitInterval) (o : V) : twoPoint G p o o = 1 := by
  rw [twoPoint,hit_singleton_eq]
  have he : {ω | (G.openGraph ω).Reachable o o} = Set.univ := by
    ext ω; exact iff_of_true (.refl _) (Set.mem_univ ω)
  rw [he]
  simp

lemma twoPoint_image [Countable V] [Countable E] (φ : G.Aut) (p : unitInterval) (o v : V) :
    twoPoint G p (φ.vertex o) (φ.vertex v) = twoPoint G p o v := by
  unfold twoPoint
  rw [measureReal_def,measureReal_def]
  congr 1
  calc
    _ = (G.law p).map (fun ω : Set E => φ.edge '' ω) (G.hitEvent (φ.vertex o) {φ.vertex v}) := by
      rw [G.law_map_aut]
    _ = _ := by
      rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
        (G.measurableSet_hitEvent _ _)]
      congr 1
      ext ω
      simp only [Set.mem_preimage,hit_singleton_eq,Set.mem_ofPred_eq]
      exact SimpleGraph.Iso.reachable_iff (φ := BondGraph.Aut.openGraphIso G φ ω)

lemma twoPoint_mul_le [Countable V] [Countable E] (p : unitInterval) (x y z : V) :
    twoPoint G p x y * twoPoint G p y z ≤ twoPoint G p x z := by
  apply (G.joint_gluing p x {y} {z} (twoPoint G p y z) ?_).trans
    (measureReal_mono Set.inter_subset_right (measure_ne_top _ _))
  intro w hw
  have he : w = y := hw
  subst w
  exact le_refl _

lemma local_bound_propagation [Countable V] [Countable E] (p : unitInterval)
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∀ x y : V, y ∈ G.vertexBall x n → a ≤ twoPoint G p x y) :
    ∀ (k : ℕ) (x y : V), y ∈ G.vertexBall x (k*n) → a^k ≤ twoPoint G p x y := by
  intro k
  induction k with
  | zero =>
    intro x y hy
    have he : y = x := by simpa only [Nat.zero_mul,BondGraph.vertexBall,Set.mem_singleton_iff] using hy
    subst y
    rw [pow_zero,twoPoint_self]
  | succ k ih =>
    intro x y hy
    rw [Nat.succ_mul] at hy
    obtain ⟨z,hz,hy⟩ := Set.mem_iUnion₂.mp (G.vertexBall_add_cover x (k*n) n hy)
    rw [pow_succ]
    exact (mul_le_mul (ih x z hz) (hlocal z y hy) ha (twoPoint_nonneg G p x z)).trans
      (twoPoint_mul_le G p x z y)

lemma exists_lower_local_parameter [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval) (hp : 0 < p)
    (n : ℕ) (a : ℝ)
    (ha : ∀ x y : V, y ∈ G.vertexBall x n → a < twoPoint G p x y) :
    ∃ q : unitInterval, q < p ∧ ∀ x y : V, y ∈ G.vertexBall x n → a < twoPoint G q x y := by
  obtain ⟨R,hR,horbit⟩ := hq
  let := hR.fintype
  let (r : R) := (G.vertexBall_finite hl r.val n).fintype
  let I := (r : R) × G.vertexBall r.val n
  obtain ⟨q,_hhalf,hqp,hqI⟩ := BernoulliProduct.exists_lower_parameter
    (I := I) (fun i => G.hitEvent i.1.val {i.2.val})
    (fun i => G.hitEvent_isUpperSet _ _) (fun i => G.hitEvent_hasFiniteOpenWitness _ _)
    p hp (fun _ => a) (fun i => by
      simpa only [twoPoint,BondGraph.law,BernoulliProduct.law_const] using ha i.1.val i.2.val i.2.property)
  refine ⟨q,hqp,?_⟩
  intro x y hy
  obtain ⟨r,hr,φ,rfl⟩ := horbit x
  let y' := φ.vertex.symm y
  have hy' : y' ∈ G.vertexBall r n := by
    apply (BondGraph.Aut.vertexBall_mem G φ r y' n).mp
    simpa only [y',Equiv.apply_symm_apply] using hy
  have hh := hqI ⟨⟨r,hr⟩,⟨y',hy'⟩⟩
  have he : twoPoint G q (φ.vertex r) y = twoPoint G q r y' := by
    simpa only [y',Equiv.apply_symm_apply] using twoPoint_image G φ q r y'
  rw [he]
  simpa only [twoPoint,BondGraph.law,BernoulliProduct.law_const] using hh

end CriticalPercolation.Sharpness
end
end CurrentModule11

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_SubcriticalLocalRateBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule12
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma subcritical_local_rate_bound (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V)
    (γ : ℝ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∀ x y : V, y ∈ G.vertexBall x n → a ≤ twoPoint G p x y) :
    a * Real.exp (γ*n) ≤ 1 := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨C,hC⟩ := subcritical_susceptibility G hl hq p hp
  have hbound (k : ℕ) (hk : N ≤ k) : (a * Real.exp (γ*n))^k ≤ C := by
    have hkn : N ≤ k*n := hk.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hn)
    let B := G.vertexBall o (k*n)
    have hB := G.vertexBall_finite hl o (k*n)
    have hsum : (B.ncard : ℝ)*a^k ≤ C := by
      calc
        _ = ∑ _v ∈ hB.toFinset, a^k := by simp only [B,Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hB]
        _ ≤ ∑ v ∈ hB.toFinset, twoPoint G p o v := by
          apply Finset.sum_le_sum
          intro v hv
          exact local_bound_propagation G p n a ha hlocal k o v (hB.mem_toFinset.mp hv)
        _ ≤ C := hC _ o
    have hvol : Real.exp (γ*(k*n : ℕ)) ≤ (B.ncard : ℝ) := by
      calc
        _ ≤ Real.exp (Real.log (B.ncard : ℝ)) := Real.exp_le_exp.mpr (hgrowth (k*n) hkn o)
        _ = _ := Real.exp_log (Nat.cast_pos.mpr (G.vertexBall_ncard_pos hl o (k*n)))
    calc
      _ = Real.exp (γ*(k*n : ℕ))*a^k := by
        rw [mul_pow,← Real.exp_nat_mul,Nat.cast_mul,mul_comm (a^k)]
        congr 2
        ring
      _ ≤ (B.ncard : ℝ)*a^k := mul_le_mul_of_nonneg_right hvol (pow_nonneg ha k)
      _ ≤ C := hsum
  by_contra hnot
  have hrate : 1 < a * Real.exp (γ*n) := lt_of_not_ge hnot
  have ht := (tendsto_pow_atTop_atTop_of_one_lt hrate).eventually (eventually_gt_atTop C)
  obtain ⟨k,hk,hkC⟩ := ((eventually_ge_atTop N).and ht).exists
  exact (not_lt_of_ge (hbound k hk)) hkC

theorem no_uniform_critical_twoPoint (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0 < G.criticalProbability) (o : V)
    (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ)) :
    ¬ ∃ θ : ℝ, 0 < θ ∧ ∀ x y : V, θ ≤ twoPoint G G.criticalProbability x y := by
  rintro ⟨θ,hθ,hall⟩
  let a := θ/2
  have ha : 0 < a := half_pos hθ
  obtain ⟨n,hn⟩ := exists_nat_gt (1/(a*γ))
  have hnexp : 1 < a*γ*(n:ℝ) := by
    have hh := (div_lt_iff₀ (mul_pos ha hγ)).mp hn
    nlinarith
  have hn1 : 1 ≤ n := by
    by_contra hn1
    have hn0 : n=0 := by omega
    simp only [hn0,Nat.cast_zero,mul_zero] at hnexp
    linarith
  have hlarge : 1 < a*Real.exp (γ*n) := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (γ*n)) ha.le
    nlinarith
  obtain ⟨q,hqp,hqbound⟩ := exists_lower_local_parameter G hl hq
    G.criticalProbability hpc n a (fun x y _ =>
      lt_of_lt_of_le (by dsimp [a] <;> linarith) (hall x y))
  exact (not_lt_of_ge (subcritical_local_rate_bound G hl hq q hqp o γ N hgrowth n hn1
    a ha.le (fun x y h => (hqbound x y h).le))) hlarge

end CriticalPercolation.Sharpness
end
end CurrentModule12

end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularGrowth
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma Aut.pow_vertex_ball (φ : G.Aut) (x : V) (C : ℕ)
    (hx : φ.vertex x ∈ G.vertexBall x C) (n : ℕ) :
    (φ^n).vertex x ∈ G.vertexBall x (n*C) := by
  induction n with
  | zero =>
    rw [pow_zero,Nat.zero_mul]
    exact G.mem_vertexBall_self x 0
  | succ n ih =>
    have hstep := (Aut.vertexBall_mem G (φ^n) x (φ.vertex x) C).mpr hx
    have hh := G.vertexBall_add ih C hstep
    have heq : (φ^(n+1)).vertex x = (φ^n).vertex (φ.vertex x) := by rw [pow_succ]; rfl
    simpa only [Nat.add_mul,Nat.one_mul,←heq] using hh

lemma Aut.modularRatio_pow (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (x : V) (n : ℕ) :
    G.modularRatio x ((φ^n).vertex x) = (G.modularRatio x (φ.vertex x))^n := by
  induction n with
  | zero =>
    rw [pow_zero,pow_zero]
    exact G.modularRatio_self x
  | succ n ih =>
    have heq : (φ^(n+1)).vertex x = (φ^n).vertex (φ.vertex x) := by rw [pow_succ]; rfl
    rw [heq,← G.modularRatio_cocycle hc hl x ((φ^n).vertex x),Aut.modularRatio,ih,pow_succ]

lemma modularRatio_le_suborbitCard (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (x y : V) : G.modularRatio x y ≤ (G.suborbitCard x y : ℝ) := by
  apply div_le_self (Nat.cast_nonneg _)
  exact_mod_cast G.suborbitCard_pos hc hl y x

lemma modular_power_log_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (x : V) (C : ℕ) (hx : φ.vertex x ∈ G.vertexBall x C) (n : ℕ) :
    (n:ℝ)*Real.log (G.modularRatio x (φ.vertex x)) ≤
      Real.log ((G.vertexBall x (n*C)).ncard : ℝ) := by
  have hp := G.modularRatio_pos hc hl x (φ.vertex x)
  have hh : (G.modularRatio x (φ.vertex x))^n ≤ (G.vertexBall x (n*C)).ncard := by
    rw [←Aut.modularRatio_pow G hc hl φ x n]
    apply (G.modularRatio_le_suborbitCard hc hl x _).trans
    exact_mod_cast Set.ncard_le_ncard
      (G.stabilizerOrbit_subset_ball (Aut.pow_vertex_ball G φ x C hx n))
      (G.vertexBall_finite hl x (n*C))
  have hlog := Real.log_le_log (pow_pos hp n) hh
  rwa [Real.log_pow] at hlog

lemma subexponential_modularRatio_le_one (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) (φ : G.Aut) (x : V) :
    G.modularRatio x (φ.vertex x) ≤ 1 := by
  by_contra hn
  have hr : 1 < G.modularRatio x (φ.vertex x) := lt_of_not_ge hn
  have hlog : 0 < Real.log (G.modularRatio x (φ.vertex x)) := Real.log_pos hr
  obtain ⟨C₀,hC₀⟩ := G.finite_subset_vertexBall hc x (Set.finite_singleton (φ.vertex x))
  let C := C₀+1
  have hC : 0 < C := by omega
  have hx : φ.vertex x ∈ G.vertexBall x C :=
    G.vertexBall_mono x (Nat.le_succ _) (hC₀ (Set.mem_singleton _))
  let a := Real.log (G.modularRatio x (φ.vertex x))
  have hCr : (0:ℝ)<C := Nat.cast_pos.mpr hC
  obtain ⟨N,hN⟩ := hg x (a/(2*C)) (div_pos hlog (by positivity))
  let n := N+1
  have hn : 0<n := by omega
  have hnC : N ≤ n*C := (Nat.le_succ N).trans (Nat.le_mul_of_pos_right n hC)
  have hlo := G.modular_power_log_bound hc hl φ x C hx n
  have hhi := hN (n*C) hnC
  have heq : (a/(2*(C:ℝ))) * ((n*C:ℕ):ℝ) = (n:ℝ)*a/2 := by
    push_cast
    field_simp
  change (n:ℝ)*a ≤ _ at hlo
  rw [heq] at hhi
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  nlinarith [mul_pos hnr hlog]

lemma subexponential_combinatoriallyUnimodular (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) : G.CombinatoriallyUnimodular := by
  intro φ x
  have h1 := G.subexponential_modularRatio_le_one hc hl hg φ x
  have h2 := G.subexponential_modularRatio_le_one hc hl hg φ⁻¹ (φ.vertex x)
  have heq : (φ⁻¹).vertex (φ.vertex x) = x := φ.vertex.symm_apply_apply x
  rw [heq] at h2
  unfold modularRatio at h1 h2
  have hp1 : (0:ℝ)<G.suborbitCard x (φ.vertex x) := Nat.cast_pos.mpr (G.suborbitCard_pos hc hl x (φ.vertex x))
  have hp2 : (0:ℝ)<G.suborbitCard (φ.vertex x) x := Nat.cast_pos.mpr (G.suborbitCard_pos hc hl (φ.vertex x) x)
  have ha := (div_le_one hp2).mp h1
  have hb := (div_le_one hp1).mp h2
  exact_mod_cast le_antisymm ha hb

lemma exponential_of_not_combinatoriallyUnimodular [Nonempty V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬ G.CombinatoriallyUnimodular) :
    ∃ a : ℝ, 0<a ∧ ∃ N : ℕ, ∀ n≥N, ∀ v : V,
      a*n ≤ Real.log ((G.vertexBall v n).ncard : ℝ) := by
  rcases G.growth_alternative hc hl hq with hg | hg
  · exact False.elim (hu (G.subexponential_combinatoriallyUnimodular hc hl hg))
  · exact hg

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_CriticalHeavyNull
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma Aut.heavyClusterEvent_iff (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (o v : V) (ω : Set E) :
    φ.edge '' ω∈G.heavyClusterEvent o (φ.vertex v) ↔ ω∈G.heavyClusterEvent o v := by
  change G.modularMass o (G.cluster _ _)=∞ ↔ _
  rw [G.modularMass_eq_top_change_base hc hl o (φ.vertex o),←φ.cluster_image,φ.modularMass_image]
  rfl

lemma Aut.heavyClusterEvent_measure [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (φ : G.Aut) (p : unitInterval) (o v : V) :
    G.law p (G.heavyClusterEvent o (φ.vertex v))=G.law p (G.heavyClusterEvent o v) := by
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_heavyClusterEvent _ _)]
  congr 1
  ext ω
  exact φ.heavyClusterEvent_iff G hc hl o v ω

lemma heavyClusterEvent_pos_all [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (p : unitInterval) (hp : 0<p) (o v : V)
    (hv : 0<G.law p (G.heavyClusterEvent o v)) (x : V) :
    0<G.law p (G.heavyClusterEvent o x) := by
  by_contra hn
  have hz : G.law p (G.heavyClusterEvent o x)=0 := le_antisymm (le_of_not_gt hn) bot_le
  obtain ⟨S,hS,_,hSv⟩ := G.mem_cluster_finite_witness (hc x v)
  have hnull := BernoulliProduct.finite_union_preimage_null (fun _ : E => p)
    (fun _ => hp) S hS (G.heavyClusterEvent o x) (G.measurableSet_heavyClusterEvent _ _) (by
      rwa [BernoulliProduct.law_const])
  rw [BernoulliProduct.law_const] at hnull
  have hle : G.law p (G.heavyClusterEvent o v)≤0 := by
    rw [←hnull]
    apply measure_mono
    intro ω hω
    change G.modularMass o (G.cluster (S∪ω) x)=∞
    have hr := G.cluster_mono (Set.subset_union_left : S⊆S∪ω) x hSv
    rw [G.cluster_eq_of_reachable hr]
    exact top_unique (hω ▸ G.modularMass_mono o (G.cluster_mono Set.subset_union_right v))
  exact (not_lt_of_ge hle) hv

lemma uniform_heavy_probability [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : 0<p) (o v : V) (hv : 0<G.law p (G.heavyClusterEvent o v)) :
    ∃ θ : ℝ, 0<θ ∧ ∀ x, θ≤(G.law p).real (G.heavyClusterEvent o x) := by
  have hall (x : V) : 0<(G.law p).real (G.heavyClusterEvent o x) :=
    ENNReal.toReal_pos (G.heavyClusterEvent_pos_all hc p hp o v hv x).ne' (measure_ne_top _ _)
  obtain ⟨S,hS,hcover⟩ := hq
  have hne : S.Nonempty := by
    obtain ⟨s,hs,_⟩ := hcover v
    exact ⟨s,hs⟩
  obtain ⟨s,hs,hmin⟩ := Set.exists_min_image S
    (fun x => (G.law p).real (G.heavyClusterEvent o x)) hS hne
  refine ⟨(G.law p).real (G.heavyClusterEvent o s),hall s,?_⟩
  intro x
  obtain ⟨t,ht,φ,rfl⟩ := hcover x
  simp only [measureReal_def,φ.heavyClusterEvent_measure G hc hl]
  exact hmin t ht

lemma uniqueHeavy_twoPoint_lower [Countable V] [Countable E] (p : unitInterval)
    (o : V) (hu : ∀ᵐ ω ∂G.law p, ω∈G.atMostOneHeavy o) (x y : V) :
    (G.law p).real (G.heavyClusterEvent o x) * (G.law p).real (G.heavyClusterEvent o y) ≤
      CriticalPercolation.Sharpness.twoPoint G p x y := by
  apply (G.harris_heavyClusterEvent p o x y).trans
  unfold CriticalPercolation.Sharpness.twoPoint
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hu] with ω hω
  intro h
  rw [CriticalPercolation.Sharpness.hit_singleton_eq]
  exact hω x y h.1 h.2

theorem exponential_critical_heavy_null
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (o v : V)
    (γ : ℝ) (hγ : 0<γ) (N : ℕ)
    (hgrowth : ∀ n≥N, ∀ x : V, γ*n≤Real.log ((G.vertexBall x n).ncard : ℝ)) :
    G.law G.criticalProbability (G.heavyClusterEvent o v)=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  by_contra hn
  have hv : 0<G.law G.criticalProbability (G.heavyClusterEvent o v) := bot_lt_iff_ne_bot.mpr hn
  have hp : 0<G.criticalProbability := by
    by_contra hh
    have he : G.criticalProbability=0 := le_antisymm (le_of_not_gt hh) bot_le
    have hsub : G.heavyClusterEvent o v⊆G.percolates :=
      fun ω hω => ⟨v,G.infinite_of_modularMass_top o hω⟩
    have hn' := (measure_mono (μ := G.law G.criticalProbability) hsub)
    rw [he,G.law_zero_percolates] at hn'
    rw [he] at hv
    exact (not_lt_of_ge hn') hv
  obtain ⟨θ,hθ,hall⟩ := G.uniform_heavy_probability hc hl hq G.criticalProbability hp o v hv
  apply CriticalPercolation.Sharpness.no_uniform_critical_twoPoint G hl hq hp o γ hγ N hgrowth
  refine ⟨θ*θ,mul_pos hθ hθ,?_⟩
  intro x y
  exact (mul_le_mul (hall x) (hall y) hθ.le measureReal_nonneg).trans
    (G.uniqueHeavy_twoPoint_lower G.criticalProbability o
      (G.atMostOneHeavy_critical_ae hc hl hq hpc o) x y)

theorem nonunimodular_critical_mass_finite_ae
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∀ᵐ ω ∂G.law G.criticalProbability, ∀ v, G.modularMass o (G.cluster ω v)<∞ := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  let : Nonempty V := ⟨o⟩
  obtain ⟨γ,hγ,N,hgrowth⟩ := G.exponential_of_not_combinatoriallyUnimodular hc hl hq hu
  apply ae_all_iff.mpr
  intro v
  have hn := G.exponential_critical_heavy_null hc hl hq hpc o v γ hγ N hgrowth
  rw [ae_iff]
  simpa only [lt_top_iff_ne_top,not_not,heavyClusterEvent] using hn

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ContractingDomains
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_StripMoves
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FreshExitWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_DomainFreshExit
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_NestedLayerGeometry
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BlockLocalization
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_LayerExposure
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_LayerCounting
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LayerExpectation
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma subcritical_seedExpectation_bound [Countable V] [Countable E]
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (q : unitInterval) (hqc : q<G.criticalProbability) (o : V) :
    ∃ C : ℝ≥0∞, C≠∞ ∧ ∀ D : Set V, G.seedExpectation q D o≤C := by
  let C := ∑' x, ENNReal.ofReal (Sharpness.twoPoint G q o x)
  refine ⟨C,(Sharpness.summable_subcritical_twoPoint G hl hq q hqc o).tsum_ofReal_ne_top,?_⟩
  intro D
  apply ENNReal.tsum_le_tsum
  intro x
  have he : ENNReal.ofReal (Sharpness.twoPoint G q o x)=G.law q (G.hitEvent o {x}) := by
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [he]
  apply measure_mono
  intro ω hω
  rw [Sharpness.hit_singleton_eq]
  exact G.entrySeeds_subset_cluster D o ω hω

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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_LayerContradiction
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
  obtain ⟨R,θ,hθ,M,hM,hblock⟩ := G.uniform_lower_nestedLayer_blocks hc hl hq hu o
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
  obtain ⟨C,hC,hbound⟩ := G.subcritical_seedExpectation_bound hl hq q hqc o
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

theorem nonunimodular_no_percolation_at_criticality
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (hpc : G.criticalProbability<1) :
    G.law G.criticalProbability G.percolates=0 := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨o⟩ := hc.nonempty
  apply G.no_critical_percolation_of_all_light hc hl hq hu hpc o
  intro v
  exact (G.nonunimodular_critical_mass_finite_ae hc hl hq hpc hu v).mono (fun _ h => (h v).ne)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_MainSparseBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

theorem main_failure_sparse_polynomial_oai [Infinite V]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : G.criticalProbability<1)
    (hper : G.law G.criticalProbability G.percolates≠0) :
    G.SubexponentialGrowth ∧ G.CombinatoriallyUnimodular ∧
      ∃ d : ℕ, 2≤d ∧ ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d := by
  have hu : G.CombinatoriallyUnimodular := by
    by_contra hn
    exact hper (G.nonunimodular_no_percolation_at_criticality hc hl hq hn hpc)
  obtain ⟨o⟩ := hc.nonempty
  rcases G.main_all_light_or_sparse_boundary hc hl hq hpc o hper with ⟨hn,_⟩|⟨hg,hpoly⟩
  · exact False.elim (hn hu)
  · exact ⟨hg,hu,hpoly⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.main_failure_sparse_polynomial_oai.{u_1, u_2}
