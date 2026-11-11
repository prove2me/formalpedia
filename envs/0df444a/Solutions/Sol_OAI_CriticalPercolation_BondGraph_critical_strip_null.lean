-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.critical_strip_null
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:18:55.711257+00:00
-- url     : https://prove2.me/submissions/351644fe-de56-41b1-b140-87c7d9d0d6bf

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_approximate_moves_contradiction
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_atMostOneInfinite_ae
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_criticalProbability_pos

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

lemma law_zero_percolates [Countable V] [Countable E] : G.law 0 G.percolates = 0 := by
  rw [law, ProbabilityTheory.setBernoulli_zero,
    Measure.dirac_apply' _ G.measurableSet_percolates]
  simp

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
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-simp] _root_.OAI.CriticalPercolation.BernoulliProduct.mem_forceOn
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_PercolationTail
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_OpenGraphIso
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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

lemma real_law_subset (p : unitInterval) (s : Set E) (hs : s.Finite) :
    (law (fun _ : E => p)).real {ω | s ⊆ ω} = (p : ℝ) ^ s.ncard := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ⊆ ω} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' {Set.univ} := by
    ext ω
    simp [Set.subset_def, Set.eq_univ_iff_forall]
  rw [he, measureReal_def, ← Measure.map_apply hmeas (.of_discrete),
    law_map_restrict, law_const]
  change (setBernoulli (Set.univ : Set s) p).real {Set.univ} = _
  rw [setBernoulli_real_singleton p (Subset.rfl) Set.finite_univ]
  simp [Set.ncard_univ]

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

lemma measurableSet_infiniteEvent [Countable V] [Countable E] (o : V) :
    MeasurableSet (G.infiniteEvent o) := (G.measurable_infinite_cluster o).setOf

lemma Aut.preimage_infiniteEvent (φ : G.Aut) (o : V) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' (G.infiniteEvent (φ.vertex o)) =
      G.infiniteEvent o := by
  ext ω
  change (G.cluster (φ.edge '' ω) (φ.vertex o)).Infinite ↔ (G.cluster ω o).Infinite
  rw [← φ.cluster_image]
  exact Set.infinite_image_iff φ.vertex.injective.injOn

lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [BernoulliProduct.law_const, law] using
    BernoulliProduct.law_map_equiv p φ.edge

lemma Aut.infiniteEvent_measure [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (o : V) :
    G.law p (G.infiniteEvent (φ.vertex o)) = G.law p (G.infiniteEvent o) := by
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_infiniteEvent _), φ.preimage_infiniteEvent]

lemma Aut.infiniteEvent_real [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (o : V) :
    (G.law p).real (G.infiniteEvent (φ.vertex o)) = (G.law p).real (G.infiniteEvent o) := by
  simp only [measureReal_def, φ.infiniteEvent_measure]

end CriticalPercolation.BondGraph

open Filter Topology

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ExpectedResidualAlt
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_UpdateKernel
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_DensityModular
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_MonotoneIndicatorUpper
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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

lemma real_hit_singleton_pos (hconnected : G.fullGraph.Connected)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (o v : V) :
    0 < (G.law p).real (G.hitEvent o {v}) := by
  obtain ⟨s, hs, _, hsv⟩ := G.mem_cluster_finite_witness (hconnected o v)
  have hsub : {ω : Set E | s ⊆ ω} ⊆ G.hitEvent o {v} := by
    intro ω hω
    exact ⟨v, G.cluster_mono hω o hsv, rfl⟩
  have hpos : 0 < (G.law p).real {ω : Set E | s ⊆ ω} := by
    rw [law, ← BernoulliProduct.law_const (E := E) p]
    rw [BernoulliProduct.real_law_subset p s hs]
    exact pow_pos hp _
  exact lt_of_lt_of_le hpos (measureReal_mono hsub)

lemma real_infiniteEvent_transfer [Countable V] [Countable E]
    (p : unitInterval) (o v : V) :
    (G.law p).real (G.hitEvent o {v}) * (G.law p).real (G.infiniteEvent v) ≤
      (G.law p).real (G.infiniteEvent o) := by
  let K := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  have hn (n : ℕ) :
      (G.law p).real (G.hitEvent o {v}) * (G.law p).real (G.infiniteEvent v) ≤
        (G.law p).real (G.hitEvent o (K n)ᶜ) := by
    apply le_trans (G.joint_gluing p o {v} (K n)ᶜ
      ((G.law p).real (G.infiniteEvent v)) ?_)
      (measureReal_mono Set.inter_subset_right)
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact measureReal_mono (G.infiniteEvent_subset_hit_compl w (K n) (K.finite n))
  exact ge_of_tendsto (G.tendsto_real_hit_compl p K o) (Eventually.of_forall hn)

lemma real_infiniteEvent_pos_all [Countable V] [Countable E]
    (hconnected : G.fullGraph.Connected) (p : unitInterval) (hp : 0 < (p : ℝ))
    {v : V} (hv : 0 < (G.law p).real (G.infiniteEvent v)) (o : V) :
    0 < (G.law p).real (G.infiniteEvent o) :=
  lt_of_lt_of_le (mul_pos (G.real_hit_singleton_pos hconnected p hp o v) hv)
    (G.real_infiniteEvent_transfer p o v)

theorem uniform_rooted_probability
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (p : unitInterval)
    (hp : 0 < G.law p G.percolates) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ o : V, θ ≤ (G.law p).real (G.infiniteEvent o) := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  have hp0 : 0 < (p : ℝ) := by
    by_contra h
    have hz : p = 0 := Subtype.ext (le_antisymm (not_lt.mp h) p.property.1)
    subst p
    rw [G.law_zero_percolates] at hp
    exact (lt_irrefl _ hp)
  have hn : ¬ ∀ v, G.law p (G.infiniteEvent v) = 0 := by
    intro h
    exact (ne_of_gt hp) ((G.percolates_null_iff _).mpr h)
  push Not at hn
  obtain ⟨v, hv⟩ := hn
  have hvpos : 0 < (G.law p).real (G.infiniteEvent v) :=
    ENNReal.toReal_pos hv (measure_ne_top _ _)
  have hall := G.real_infiniteEvent_pos_all hconnected p hp0 hvpos
  obtain ⟨S, hS, horbit⟩ := hquasi
  have hSne : S.Nonempty := by
    obtain ⟨s, hs, _⟩ := horbit v
    exact ⟨s, hs⟩
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image S
    (fun o => (G.law p).real (G.infiniteEvent o)) hS hSne
  refine ⟨(G.law p).real (G.infiniteEvent s), hall s, ?_⟩
  intro o
  obtain ⟨t, ht, φ, rfl⟩ := horbit o
  rw [Aut.infiniteEvent_real]
  exact hmin t ht

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DirectionalTail
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
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma infiniteVertices_mono {ω τ : Set E} (h : ω⊆τ) :
    G.infiniteVertices ω⊆G.infiniteVertices τ := fun v hv => hv.mono (G.cluster_mono h v)

lemma cluster_union_unchanged (ω S : Set E) (o : V)
    (hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω o) :
    G.cluster (ω∪S) o=G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro z hz
    have hr := ((G.openGraph (ω∪S)).reachable_iff_reflTransGen o z).mp hz
    clear hz
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases he with he|he
      · have hadj : (G.openGraph ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,hend⟩,hne⟩
        exact ih.trans hadj.reachable
      · exact False.elim (hends e he x (by simp [hend]) ih)
  · exact G.cluster_mono Set.subset_union_left o

lemma infiniteVertices_union_finite_error (ω S : Set E) (hS : S.Finite) :
    (G.infiniteVertices (ω∪S)\G.infiniteVertices ω).Finite := by
  let K := ⋃ e∈S, ⋃ v∈(G.ends e).toFinset,
    {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}
  have hK : K.Finite := hS.biUnion fun e _ => (G.ends e).toFinset.finite_toSet.biUnion fun v _ => by
    by_cases hv : (G.cluster ω v).Finite
    · exact hv.subset (fun _ h => h.1)
    · have heq : {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}=(∅ : Set V) := by
        ext x
        simp [hv]
      rw [heq]
      exact Set.finite_empty
  apply hK.subset
  intro x hx
  have hfin : (G.cluster ω x).Finite := Set.not_infinite.mp hx.2
  by_contra hn
  have hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω x := by
    intro e he v hv hvc
    apply hn
    refine Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,?_,hvc.symm,?_⟩⟩
    · simpa only [Sym2.mem_toFinset] using hv
    · rwa [← G.cluster_eq_of_reachable hvc]
  exact hx.1 (by rwa [G.cluster_union_unchanged ω S x hends])

lemma directionUnbounded_mono (f : V → ℝ) : IsUpperSet (G.directionUnbounded f) := by
  intro ω τ h hω n
  obtain ⟨v,hv,hv'⟩ := hω n
  exact ⟨v,hv,G.infiniteVertices_mono h hv'⟩

lemma directionUnbounded_union_finite_iff (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω∪S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · intro h n
    have hK := (G.infiniteVertices_union_finite_error ω S hS).image f
    obtain ⟨M,hM⟩ := hK.bddAbove
    obtain ⟨N,hN⟩ := exists_nat_gt (max M n)
    obtain ⟨v,hv,hinf⟩ := h N
    refine ⟨v,lt_trans (lt_of_le_of_lt (le_max_right M n) hN) hv,?_⟩
    by_contra hnot
    have hfM := hM (Set.mem_image_of_mem f ⟨hinf,hnot⟩)
    have : M<(N : ℝ) := lt_of_le_of_lt (le_max_left M n) hN
    linarith
  · exact G.directionUnbounded_mono f Set.subset_union_left

lemma directionUnbounded_diff_finite_iff (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · exact G.directionUnbounded_mono f Set.sdiff_subset
  · intro h
    have hs : ω⊆(ω\S)∪S := fun e he => by
      by_cases hh : e∈S
      · exact Or.inr hh
      · exact Or.inl ⟨he,hh⟩
    exact (G.directionUnbounded_union_finite_iff f (ω\S) S hS).mp
      (G.directionUnbounded_mono f hs h)

lemma directionUnbounded_measurable [Countable V] [Countable E] (f : V → ℝ) :
    MeasurableSet (G.directionUnbounded f) := by
  have heq : G.directionUnbounded f=⋂ n : ℕ, ⋃ v∈{v | (n : ℝ)<f v}, G.infiniteEvent v := by
    ext ω
    simp only [directionUnbounded,infiniteVertices,infiniteEvent,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
    G.measurableSet_infiniteEvent v

lemma directionUnbounded_zero_one [Countable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) :
    BernoulliProduct.law q (G.directionUnbounded f)=0 ∨
      BernoulliProduct.law q (G.directionUnbounded f)=1 := by
  apply BernoulliProduct.zero_one_of_finite_erasure_invariant q _ (G.directionUnbounded_measurable f)
  intro S hS ω
  have heq : BernoulliProduct.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  exact G.directionUnbounded_diff_finite_iff f ω S hS

lemma directionUnbounded_positive [Countable V] [Countable E]
    (p : unitInterval) (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v)
    (theta : ℝ) (htheta : 0<theta)
    (hroot : ∀ v, theta≤(G.law p).real (G.infiniteEvent v)) :
    0<G.law p (G.directionUnbounded f) := by
  let A := fun n : ℕ => ⋃ v∈{v | (n : ℝ)<f v}, G.infiniteEvent v
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.biUnion (Set.to_countable _) fun v _ => G.measurableSet_infiniteEvent v
  have hanti : Antitone A := by
    intro n m hnm ω hω
    obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨v,(show (n : ℝ)<f v from lt_of_le_of_lt (Nat.cast_le.mpr hnm) hv),hh⟩
  have heq : (⋂ n, A n)=G.directionUnbounded f := by
    ext ω
    simp only [A,directionUnbounded,infiniteVertices,infiniteEvent,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  have ht := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0,measure_ne_top _ _⟩
  rw [heq] at ht
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hbound : ∀ n, theta≤(G.law p).real (A n) := by
    intro n
    obtain ⟨v,hv⟩ := hf n
    have hs : G.infiniteEvent v⊆A n := fun ω hω => Set.mem_iUnion₂.mpr ⟨v,hv,hω⟩
    exact (hroot v).trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs))
  have hp : 0<(G.law p).real (G.directionUnbounded f) :=
    htheta.trans_le (ge_of_tendsto hreal (Eventually.of_forall hbound))
  exact ENNReal.toReal_pos_iff.mp hp |>.1

theorem directionUnbounded_one [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    G.law p (G.directionUnbounded f)=1 := by
  obtain ⟨theta,htheta,hroot⟩ := G.uniform_rooted_probability hc hl hq p hpositive
  have hp := G.directionUnbounded_positive p f hf theta htheta hroot
  have hz := G.directionUnbounded_zero_one (fun _ => p) f
  rw [BernoulliProduct.law_const] at hz
  exact hz.resolve_left (ne_of_gt hp)

theorem unique_cluster_direction_unbounded_ae [Countable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p : ℝ)∈Set.Ioo 0 1) (hpositive : 0<G.law p G.percolates)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Infinite →
      ∀ n : ℕ, ∃ w∈G.cluster ω v, (n : ℝ)<f w := by
  have hu : ∀ᵐ ω ∂G.law p, ω∈G.directionUnbounded f := by
    rw [ae_iff]
    change G.law p (G.directionUnbounded f)ᶜ=0
    rw [measure_compl (G.directionUnbounded_measurable f) (measure_ne_top _ _),
      G.directionUnbounded_one hc hl hq p hpositive f hf,measure_univ,tsub_self]
  filter_upwards [hu,G.atMostOneInfinite_ae hc hl hq hg p hp] with ω hω huniq
  intro v hv n
  obtain ⟨w,hw,hwinf⟩ := hω n
  exact ⟨w,huniq v w hv hwinf,hw⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ConditionalGluing
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorGraph
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
    · exact (ih hw).trans (by push_cast <;> nlinarith)
    · obtain ⟨u,hu,huw⟩ := Set.mem_iUnion₂.mp hw
      calc
        |f w-f v| ≤ |f w-f u|+|f u-f v| := abs_sub_le _ _ _
        _ ≤ ρ+n*ρ := add_le_add (hf huw.symm) (ih hu)
        _ = _ := by push_cast <;> ring

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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_RelayMoves
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_OpenRay
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_CorridorNormalization
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveWitness
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_MoveExit
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_StripMoves
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripContinuity
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripLinear
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripOrigin
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_MoveTransport
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripUniform
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
  apply G.approximate_moves_contradiction hc hl hq hpc hpc1
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_StripCritical
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

theorem critical_strip_null_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
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
  have hdir := G.unique_cluster_direction_unbounded_ae hc hl hq hg G.criticalProbability
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

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.critical_strip_null_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.critical_strip_null_oai.{u_1, u_2}
