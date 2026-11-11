-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:32.588922+00:00
-- url     : https://prove2.me/submissions/9066a947-7ea9-4199-94e3-d80c8b9c5da0

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_criticalProbability_pos
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_restricted_interpolation_measure
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound

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

lemma component_delete_self (H : SimpleGraph V) (U : Set V) (s : V)
    (hs : s ∈ U) : component (delete H U) s = {s} := by
  ext v
  constructor
  · intro h
    have hadj : ∀ t, ¬ (delete H U).Adj s t := fun t ht => ht.2.1 hs
    have he : v = s := by
      rcases h with ⟨p⟩
      cases p with
      | nil => rfl
      | cons hst _ => exact (hadj _ hst).elim
    exact he
  · rintro rfl
    exact component_self _ _

end CriticalPercolation.ClusterDeletion

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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_BandScale
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InterpolationUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation

lemma interpolationConstant_pos (c : ℝ) {ε : ℝ} (hε : 0<ε) :
    0 < interpolationConstant c ε := by
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hm : 0 ≤ max 0 (Real.log (1/c)) := le_max_left _ _
  unfold interpolationConstant
  positivity

end CriticalPercolation
end
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

omit [Countable E] in
lemma tendsto_real_reachable_restrict (p : unitInterval) (u v : V)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real {ω | (G.openGraph (K n ∩ ω)).Reachable u v})
      atTop (𝓝 ((G.law p).real {ω | (G.openGraph ω).Reachable u v})) := by
  have hh := BernoulliProduct.tendsto_real_finiteWitness p (G.hitEvent u {v})
    (G.hitEvent_isUpperSet u {v}) (G.hitEvent_hasFiniteOpenWitness u {v}) K
  simpa only [law,← BernoulliProduct.law_const,hitEvent,Set.inter_singleton_nonempty,
    cluster,Set.mem_ofPred_eq] using hh

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_IncidenceDegree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_DeletedTailGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.component_bot _root_.OAI.CriticalPercolation.ClusterDeletion.delete_bot
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
namespace BondGraph
open ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

omit [Fintype V] in
lemma exterior_neighbor_mem_exitVertices (U : Set V) {u v : V}
    (hu : u∈U) (hv : v∉U) (hadj : G.fullGraph.Adj u v) :
    v∈G.exitVertices U := by
  obtain ⟨e,_,he⟩ := hadj.1
  have hemi : e∈G.incidentEdges U := ⟨u,hu,he ▸ Sym2.mem_mk_left _ _⟩
  apply Finset.mem_image.mpr
  refine ⟨e,Set.mem_toFinset.mpr hemi,?_⟩
  have hh : s((G.ends e).out.1,(G.ends e).out.2)=s(u,v) :=
    (G.ends e).out_eq.trans he
  rcases (Sym2.mk_eq_mk_iff (p := (G.ends e).out) (q := (u,v))).mp hh with hh|hh
  · have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp [exitEndpoint,h1,h2,hu]
  · have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp only [Prod.fst_swap,Prod.snd_swap] at h1 h2
    simp [exitEndpoint,h1,hv]

lemma exitVertices_card_le (U : Set V) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    (G.exitVertices U).card≤U.toFinset.card*D :=
  Finset.card_image_le.trans (G.incident_card_le U D hD)

lemma smallDamage_card_le (H : SimpleGraph V) (U : Set V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    (G.smallDamage H U s).card ≤ U.toFinset.card + U.toFinset.card*D*(s-1) := by
  let T := (G.exitVertices U).filter
    (fun w => (component (delete H U) w).toFinset.card < s)
  change (U.toFinset ∪ T.biUnion (fun w => (component (delete H U) w).toFinset)).card ≤ _
  calc
    _ ≤ U.toFinset.card + (T.biUnion (fun w => (component (delete H U) w).toFinset)).card :=
      Finset.card_union_le _ _
    _ ≤ U.toFinset.card + ∑ w∈T, (component (delete H U) w).toFinset.card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ U.toFinset.card + ∑ _w∈T, (s-1) := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro w hw
      have hh := (Finset.mem_filter.mp hw).2
      omega
    _ = U.toFinset.card + T.card*(s-1) := by simp
    _ ≤ U.toFinset.card + (G.exitVertices U).card*(s-1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)) _
    _ ≤ _ := Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (G.exitVertices_card_le U D hD)) _

lemma tail_deletion_or_damage (H : SimpleGraph V) (hH : H≤G.fullGraph)
    (U : Set V) (s : ℕ) (v : V)
    (hs : s≤(component H v).toFinset.card) :
    (v∉U ∧ s≤(component (delete H U) v).toFinset.card) ∨ v∈G.smallDamage H U s := by
  by_cases hv : v∈G.smallDamage H U s
  · exact Or.inr hv
  apply Or.inl
  have hvU : v∉U := fun hh => hv (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh))
  refine ⟨hvU,?_⟩
  by_contra! hsmall
  have hclosed : ∀ ⦃a b⦄, a∈component (delete H U) v → H.Adj a b →
      b∈component (delete H U) v := by
    intro a b ha hab
    have haU : a∉U := by
      by_contra haU
      have he := component_delete_self H U a haU
      have hav : v∈component (delete H U) a := ha.symm
      rw [he] at hav
      exact hvU ((Set.mem_singleton_iff.mp hav) ▸ haU)
    have hbU : b∉U := by
      intro hb
      have hae := G.exterior_neighbor_mem_exitVertices U hb haU (hH hab.symm)
      have he := component_eq_of_mem ha
      apply hv
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨a,Finset.mem_filter.mpr ⟨hae,?_⟩,Set.mem_toFinset.mpr ha.symm⟩
      rwa [he]
    exact ha.trans (SimpleGraph.Adj.reachable ⟨hab,haU,hbU⟩)
  have hsub : component H v ⊆ component (delete H U) v := by
    intro w hw
    exact reachable_mem_of_closed hclosed (component_self _ _) hw
  have hc := Finset.card_le_card (Set.toFinset_mono hsub)
  omega

lemma tailCount_le_exterior_add_damage (H : SimpleGraph V) (hH : H≤G.fullGraph)
    (U : Set V) (B : Finset V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    tailCount H B s ≤ exteriorTailCount H U B s +
      (U.toFinset.card + U.toFinset.card*D*(s-1) : ℕ) := by
  calc
    _ ≤ ∑ v∈B, ((if v∉U ∧ s≤(component (delete H U) v).toFinset.card then 1 else 0) +
        if v∈G.smallDamage H U s then 1 else 0) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hs : s≤(component H v).toFinset.card
      · rcases G.tail_deletion_or_damage H hH U s v hs with hv|hv
        · rw [ite_eq_left hs,ite_eq_left hv]
          split_ifs <;> norm_num
        · rw [ite_eq_left hs,ite_eq_left hv]
          split_ifs <;> norm_num
      · simp only [hs,ite_false, if_false]
        split_ifs <;> norm_num
    _ = exteriorTailCount H U B s + ((B.filter (fun v => v∈G.smallDamage H U s)).card:ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_boole]
    _ ≤ exteriorTailCount H U B s + ((G.smallDamage H U s).card:ℝ) := by
      apply add_le_add le_rfl
      exact Nat.cast_le.mpr (Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2))
    _ ≤ _ := add_le_add le_rfl (Nat.cast_le.mpr (G.smallDamage_card_le H U s D hD))

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteNearbyPair
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation
namespace FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_finset_sum {J : Type*} (w : E → A → ℝ) (S : Finset J)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j∈S, f j ω) = ∑ j∈S, expect w (f j) := by
  simp only [expect,Finset.mul_sum]
  exact Finset.sum_comm
end FiniteProduct
namespace BondGraph
open ClusterDeletion FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma expected_exteriorTailCount_lower (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (U : Set V) (B : Finset V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) (hU : U.toFinset.card < s^2) :
    expect w (fun ω => tailCount (G.openGraph ω) B s) - (s^2+D*s^3:ℕ) ≤
      expect w (fun ω => exteriorTailCount (G.openGraph ω) U B s) := by
  have hcost : U.toFinset.card + U.toFinset.card*D*(s-1)≤ s^2+D*s^3 := by
    calc _ ≤ s^2+s^2*D*s := by gcongr; omega
         _ = _ := by ring
  have hg := expect_mono hn (fun ω => G.tailCount_le_exterior_add_damage (G.openGraph ω)
    (G.openGraph_mono (Set.subset_univ _)) U B s D hD)
  rw [expect_add,expect_const w hw] at hg
  have hr : ((U.toFinset.card + U.toFinset.card*D*(s-1):ℕ):ℝ)≤(s^2+D*s^3:ℕ) :=
    Nat.cast_le.mpr hcost
  linarith

lemma finite_nearby_pair_expect (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (B : Finset V) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    expect w (fun ω => if s≤(G.cluster ω z).toFinset.card ∧
      (G.cluster ω z).toFinset.card < s^2 then 1 else 0) *
      (expect w (fun ω => tailCount (G.openGraph ω) B s) - (s^2+D*s^3:ℕ)) ≤
    ∑ y∈B, expect w (fun ω => if ω∈G.twoClusterEvent y z s then 1 else 0) := by
  let band (U : Set V) := s≤U.toFinset.card ∧ U.toFinset.card < s^2
  let T := expect w (fun ω => tailCount (G.openGraph ω) B s) - (s^2+D*s^3:ℕ)
  let F (U : Set V) (H : SimpleGraph V) := if band U then
    ∑ y∈B, (if y∉U ∧ s≤(component H y).toFinset.card then (1:ℝ) else 0) else 0
  have hsp := G.finite_spatialMarkov w hw {z} ∅ F
  simp only [delete_empty,roots_singleton] at hsp
  have hleft : expect w (fun ω => if band (G.cluster ω z) then
      exteriorTailCount (G.openGraph ω) (G.cluster ω z) B s else 0) =
      expect w (fun ω => if band (G.cluster ω z) then
        expect w (fun ω' => exteriorTailCount (G.openGraph ω') (G.cluster ω z) B s) else 0) := by
    calc
      _ = expect w (fun ω => F (component (G.openGraph ω) z)
          (delete (G.openGraph ω) (component (G.openGraph ω) z))) := rfl
      _ = _ := hsp.trans (by
        congr 1
        funext ω
        change (expect w (fun ω' => if band (G.cluster ω z) then
          exteriorTailCount (G.openGraph ω') (G.cluster ω z) B s else 0)) = _
        by_cases hb : band (G.cluster ω z)
        · simp only [ite_eq_left hb]
        · simp only [ite_eq_right hb,expect_zero])
  have hlower : expect w (fun ω => if band (G.cluster ω z) then (1:ℝ) else 0)*T ≤
      expect w (fun ω => if band (G.cluster ω z) then
        expect w (fun ω' => exteriorTailCount (G.openGraph ω') (G.cluster ω z) B s) else 0) := by
    rw [← expect_mul_const]
    apply expect_mono hn
    intro ω
    split_ifs with hb
    · simp only [one_mul]
      exact G.expected_exteriorTailCount_lower w hw hn (G.cluster ω z) B s D hD hb.2
    · simp only [zero_mul,le_refl]
  rw [← hleft] at hlower
  refine hlower.trans ?_
  rw [← expect_finset_sum]
  apply expect_mono hn
  intro ω
  by_cases hb : band (G.cluster ω z)
  · rw [ite_eq_left hb]
    apply Finset.sum_le_sum
    intro y _
    by_cases hy : y∉G.cluster {e | ω e} z ∧
        s≤(component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y).toFinset.card
    · have ht : {e | ω e}∈G.twoClusterEvent y z s := by
        refine ⟨⟨fun hh => hy.1 hh.symm,?_⟩,?_⟩
        · apply (G.clusterTail_iff_card _ y s).mpr
          have hh : component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y =
              G.cluster {e | ω e} y := component_delete_component (G.openGraph {e | ω e}) z y hy.1
          simpa only [hh] using hy.2
        · exact (G.clusterTail_iff_card _ z s).mpr hb.1
      change (if y∉G.cluster {e | ω e} z ∧
        s≤(component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y).toFinset.card
        then (1:ℝ) else 0) ≤ (if {e | ω e}∈G.twoClusterEvent y z s then 1 else 0)
      rw [ite_eq_left hy,ite_eq_left ht]
    · change (if y∉G.cluster {e | ω e} z ∧
        s≤(component (delete (G.openGraph {e | ω e}) (G.cluster {e | ω e} z)) y).toFinset.card
        then (1:ℝ) else 0) ≤ _
      rw [ite_eq_right hy]
      split_ifs <;> norm_num
  · rw [ite_eq_right hb]
    apply Finset.sum_nonneg
    intro _ _
    split_ifs <;> norm_num

lemma finite_nearby_pair (p : unitInterval) (B : Finset V) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) :
    (G.law p).real (G.clusterBand z s) *
      ((∑ y∈B, (G.law p).real (G.clusterTail y s)) - (s^2+D*s^3:ℕ)) ≤
        ∑ y∈B, (G.law p).real (G.twoClusterEvent y z s) := by
  let w := fun _ : E => BernoulliProduct.bitWeight p
  have hh := G.finite_nearby_pair_expect w (fun _ => BernoulliProduct.bitWeight_sum p)
    (fun _ => BernoulliProduct.bitWeight_nonneg p) B z s D
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v)
  have hreal (A : Set (Set E)) : expect w (fun ω => if ω∈A then 1 else 0) =
      (G.law p).real A := by
    calc
      _ = FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
          (fun ω => ω ∈ A) := by
        unfold FiniteProduct.prob
        congr 1
      _ = _ := by
        simpa only [law,← BernoulliProduct.law_const] using
          (BernoulliProduct.prob_eq_real (fun _ : E => p) A)
  have hband : expect w (fun ω => if s≤(G.cluster ω z).toFinset.card ∧
      (G.cluster ω z).toFinset.card < s^2 then 1 else 0) = (G.law p).real (G.clusterBand z s) := by
    rw [← hreal]
    congr 1
    funext ω
    congr 1
    apply propext
    change _ ↔ {e | ω e}∈G.clusterTail z s ∧ {e | ω e}∉G.clusterTail z (s^2)
    rw [G.clusterTail_iff_card,G.clusterTail_iff_card,not_le]
    rfl
  have htail : expect w (fun ω => tailCount (G.openGraph ω) B s) =
      ∑ y∈B, (G.law p).real (G.clusterTail y s) := by
    unfold tailCount
    rw [expect_finset_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← hreal]
    congr 1
    funext ω
    congr 1
    exact propext (G.clusterTail_iff_card {e | ω e} y s).symm
  rw [hband,htail] at hh
  simpa only [hreal] using hh

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_FiniteInduced
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_FiniteClusterTransport
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InfiniteInterpolation
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

lemma exists_le_of_eventually_exists_le {I : Type*} [Finite I]
    {f : I → ℕ → ℝ} {a : I → ℝ} {r : ℕ → ℝ} {b : ℝ}
    (hf : ∀ i, Tendsto (f i) atTop (𝓝 (a i))) (hr : Tendsto r atTop (𝓝 b))
    (h : ∀ᶠ n in atTop, ∃ i, r n ≤ f i n) : ∃ i, b ≤ a i := by
  by_contra! hh
  have ht : ∀ᶠ n in atTop, ∀ i, f i n < r n :=
    Filter.eventually_all.mpr (fun i => (hf i).eventually_lt hr (hh i))
  obtain ⟨n,hn,hn'⟩ := (h.and ht).exists
  obtain ⟨i,hi⟩ := hn
  exact (not_le.mpr (hn' i)) hi

namespace BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

theorem infinite_interpolation_measure
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0 < c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real (G.twoClusterEvent (x 0) (x d) s)) :
    ∃ j<d, 0 < (G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s)) ≤
        interpolationConstant (c/2) ε *
          (Real.log (1/(G.law p).real (G.twoClusterEvent (x 0) (x d) s))+Nat.clog 2 d+1) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let δ (n : ℕ) := (G.law p).real {ω | K n ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s}
  let δlim := (G.law p).real (G.twoClusterEvent (x 0) (x d) s)
  have hδt : Tendsto δ atTop (𝓝 δlim) := G.tendsto_real_twoCluster_restrict p _ _ _ K
  have hδpos : ∀ᶠ n in atTop, 0 < δ n := hδt.eventually (eventually_gt_nhds hδ)
  have hcc : c/2 < c := by linarith
  have hce : ∀ᶠ n in atTop, ∀ j k : Fin (d+1), j.val<k.val → k.val-j.val<d →
      c/2 ≤ (G.law p).real {ω | (G.openGraph (K n ∩ ω)).Reachable (x j.val) (x k.val)} := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro k
    by_cases hjk : j.val<k.val ∧ k.val-j.val<d
    · have hl := lt_of_lt_of_le hcc (hconn j k hjk.1 (by omega) hjk.2)
      filter_upwards [(G.tendsto_real_reachable_restrict p (x j) (x k) K).eventually (eventually_gt_nhds hl)]
        with n hn
      exact fun _ _ => hn.le
    · exact Filter.Eventually.of_forall (fun _ _ _ => (hjk ⟨by assumption,by assumption⟩).elim)
  let C := interpolationConstant (c/2) ε
  let r (n : ℕ) := Real.exp (-C*(Real.log (1/δ n)+Nat.clog 2 d+1))
  let b := Real.exp (-C*(Real.log (1/δlim)+Nat.clog 2 d+1))
  have hr : Tendsto r atTop (𝓝 b) := by
    have h1 : Tendsto (fun n => 1/δ n) atTop (𝓝 (1/δlim)) := tendsto_const_nhds.div hδt (ne_of_gt hδ)
    have h2 := h1.log (one_div_ne_zero (ne_of_gt hδ))
    have hh : Tendsto (fun n => -C*(Real.log (1/δ n)+Nat.clog 2 d+1)) atTop
        (𝓝 (-C*(Real.log (1/δlim)+Nat.clog 2 d+1))) :=
      tendsto_const_nhds.mul ((h2.add_const _).add_const _)
    exact (Real.continuous_exp.tendsto _).comp hh
  have he : ∀ᶠ n in atTop, ∃ j : Fin d,
      r n ≤ (G.law p).real {ω | K n ∩ ω ∈ G.twoClusterEvent (x j.val) (x (j.val+1)) s} := by
    filter_upwards [hδpos,hce] with n hnδ hnc
    obtain ⟨j,hjd,hjp,hjl⟩ := G.restricted_interpolation_measure (K n) (K.finite n) d x hd p hp
      (by linarith : 0 < c/2) hε hεp hεq (fun j k hjk hkd hdiff =>
        hnc ⟨j,by omega⟩ ⟨k,by omega⟩ hjk hdiff) s hnδ
    refine ⟨⟨j,hjd⟩,?_⟩
    apply (Real.le_log_iff_exp_le hjp).mp
    change -Real.log _ ≤ C * (Real.log (1/δ n)+Nat.clog 2 d+1) at hjl
    linarith
  obtain ⟨j,hj⟩ := exists_le_of_eventually_exists_le
    (fun j : Fin d => G.tendsto_real_twoCluster_restrict p (x j) (x (j.val+1)) s K) hr he
  have hjp := lt_of_lt_of_le (Real.exp_pos _) hj
  refine ⟨j,j.isLt,hjp,?_⟩
  have hl := (Real.le_log_iff_exp_le hjp).mpr hj
  change -C*(Real.log (1/δlim)+Nat.clog 2 d+1) ≤ _ at hl
  change -Real.log _ ≤ C * (Real.log (1/δlim)+Nat.clog 2 d+1)
  linarith

end BondGraph
end CriticalPercolation
end
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteAdjacentMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_SusceptibilityMeasure
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

namespace CriticalPercolation.BondGraph
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma induce_clusterTail_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (u : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).clusterTail u s) =
      (G.law p).real {ω | G.inducedEdges S ∩ ω ∈ G.clusterTail u.val s} := by
  have he : (G.induce S).clusterTail u s =
      {ω | Subtype.val '' ω ∈ G.clusterTail u.val s} := by
    ext ω
    exact G.induce_clusterTail S ω u s
  rw [he,G.induce_law_event S hS]

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_InfiniteNearbyPair
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma induce_clusterBand_real (S : Set V) (hS : (G.inducedEdges S).Finite)
    (p : unitInterval) (z : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).clusterBand z s) =
      (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterBand z.val s} := by
  have he : (G.induce S).clusterBand z s =
      {ω | Subtype.val '' ω∈G.clusterBand z.val s} := by
    ext ω
    simp only [clusterBand,Set.mem_sdiff,G.induce_clusterTail,Set.mem_ofPred_eq]
  rw [he,G.induce_law_event S hS]

lemma induced_nearby_pair (hlocal : G.LocallyFinite) (p : unitInterval)
    (B : Finset V) (z : V) (s D : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (S : Set V) (hS : S.Finite) (hB : ∀ y∈B, y∈S) (hz : z∈S) :
    (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterBand z s} *
      ((∑ y∈B, (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterTail y s}) - (s^2+D*s^3:ℕ)) ≤
        ∑ y∈B, (G.law p).real {ω | G.inducedEdges S∩ω∈G.twoClusterEvent y z s} := by
  let := hS.fintype
  let := (G.finite_inducedEdges hlocal hS).fintype
  have hh := (G.induce S).finite_nearby_pair p (B.subtype (·∈S)) ⟨z,hz⟩ s D
    (G.induce_incident_bound hlocal D hD S)
  simp_rw [G.induce_clusterBand_real S (G.finite_inducedEdges hlocal hS),
    G.induce_clusterTail_real S (G.finite_inducedEdges hlocal hS),
    G.induce_twoCluster_real S (G.finite_inducedEdges hlocal hS)] at hh
  rw [Finset.sum_subtype_of_mem
    (fun y => (G.law p).real {ω | G.inducedEdges S∩ω∈G.clusterTail y s}) hB,
    Finset.sum_subtype_of_mem
    (fun y => (G.law p).real {ω | G.inducedEdges S∩ω∈G.twoClusterEvent y z s}) hB] at hh
  exact hh

lemma infinite_nearby_pair_sum [Countable E]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (p : unitInterval) (B : Finset V) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) :
    (G.law p).real (G.clusterBand z s) *
      ((∑ y∈B, (G.law p).real (G.clusterTail y s)) - (s^2+D*s^3:ℕ)) ≤
        ∑ y∈B, (G.law p).real (G.twoClusterEvent y z s) := by
  let K := G.inducedBallExhaustion hconnected hlocal z
  have hband := BernoulliProduct.tendsto_real_sdiff_finiteWitness p
    (G.clusterTail z s) (G.clusterTail z (s^2))
    (G.clusterTail_isUpperSet z s) (G.clusterTail_isUpperSet z (s^2))
    (G.clusterTail_hasFiniteOpenWitness z s) (G.clusterTail_hasFiniteOpenWitness z (s^2)) K
  have htail (y : V) := BernoulliProduct.tendsto_real_finiteWitness p
    (G.clusterTail y s) (G.clusterTail_isUpperSet y s)
    (G.clusterTail_hasFiniteOpenWitness y s) K
  have hb : Tendsto (fun n => (G.law p).real {ω | K n∩ω∈G.clusterBand z s}) atTop
      (𝓝 ((G.law p).real (G.clusterBand z s))) := by
    simpa only [law,← BernoulliProduct.law_const,clusterBand] using hband
  have ht : Tendsto (fun n => ∑ y∈B, (G.law p).real {ω | K n∩ω∈G.clusterTail y s}) atTop
      (𝓝 (∑ y∈B, (G.law p).real (G.clusterTail y s))) := by
    apply tendsto_finsetSum
    intro y _
    simpa only [law,← BernoulliProduct.law_const] using htail y
  have hh := tendsto_finsetSum B (fun y _ => G.tendsto_real_twoCluster_restrict p y z s K)
  apply le_of_tendsto_of_tendsto (hb.mul (ht.sub tendsto_const_nhds)) hh
  obtain ⟨W,hW⟩ := G.finite_subset_vertexBall hconnected z B.finite_toSet
  filter_upwards [eventually_ge_atTop W] with n hn
  exact G.induced_nearby_pair hlocal p B z s D hD _ (G.vertexBall_finite hlocal z n)
    (fun y hy => G.vertexBall_mono z hn (hW hy)) (G.mem_vertexBall_self z n)

theorem exists_nearby_large_pair [Countable E]
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (p : unitInterval) (B : Finset V) (hB : B.Nonempty) (z : V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).ncard≤D) (θ : ℝ)
    (htail : ∀ y∈B, θ/2≤(G.law p).real (G.clusterTail y s))
    (hcost : (s^2+D*s^3:ℕ)≤θ/4*(B.card:ℝ)) :
    ∃ y∈B, θ/4*(G.law p).real (G.clusterBand z s) ≤
      (G.law p).real (G.twoClusterEvent y z s) := by
  have hh := G.infinite_nearby_pair_sum hconnected hlocal p B z s D hD
  have hsum : θ/4*(B.card:ℝ) ≤
      (∑ y∈B, (G.law p).real (G.clusterTail y s)) - (s^2+D*s^3:ℕ) := by
    have hs := Finset.sum_le_sum htail
    simp only [Finset.sum_const,nsmul_eq_mul] at hs
    linarith
  have hg := (mul_le_mul_of_nonneg_left hsum
    (show 0≤(G.law p).real (G.clusterBand z s) from measureReal_nonneg)).trans hh
  have hs : (∑ _y∈B, θ/4*(G.law p).real (G.clusterBand z s)) ≤
      ∑ y∈B, (G.law p).real (G.twoClusterEvent y z s) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using hg
  exact Finset.exists_le_of_sum_le hB hs

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_MinimalPair
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma walk_mem_vertexBall {u v : V} (w : G.fullGraph.Walk u v) :
    v∈G.vertexBall u w.length := by
  induction w with
  | nil => exact G.mem_vertexBall_self _ 0
  | @cons u v z h w ih =>
    have hv := G.vertexBall_step (G.mem_vertexBall_self u 0) h
    simpa only [SimpleGraph.Walk.length_cons,Nat.add_comm] using G.vertexBall_add hv w.length ih

lemma mem_vertexBall_iff_walk {u v : V} {n : ℕ} :
    v∈G.vertexBall u n ↔ ∃ w : G.fullGraph.Walk u v, w.length≤n := by
  constructor
  · intro hv
    induction n generalizing v with
    | zero =>
      have he : v=u := hv
      subst v
      exact ⟨.nil,le_rfl⟩
    | succ n ih =>
      rcases hv with hv|hv
      · obtain ⟨w,hw⟩ := ih hv
        exact ⟨w,hw.trans (Nat.le_succ _)⟩
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        obtain ⟨w,hw⟩ := ih hz
        have hzv' : G.fullGraph.Adj z v := hzv
        exact ⟨SimpleGraph.Walk.concat w hzv', by
          rw [SimpleGraph.Walk.length_concat]
          exact Nat.add_le_add_right hw 1⟩
  · rintro ⟨w,hw⟩
    exact G.vertexBall_mono u hw (G.walk_mem_vertexBall w)

lemma walk_getVert_mem_vertexBall {u v : V} (w : G.fullGraph.Walk u v)
    (j k : ℕ) (hjk : j≤k) (hk : k≤w.length) :
    w.getVert k∈G.vertexBall (w.getVert j) (k-j) := by
  have hh : ∀ n, j+n≤w.length →
      w.getVert (j+n)∈G.vertexBall (w.getVert j) n := by
    intro n
    induction n with
    | zero => intro _; simpa only [Nat.add_zero] using G.mem_vertexBall_self (w.getVert j) 0
    | succ n ih =>
      intro hn
      have hs := G.vertexBall_step (ih (by omega)) (w.adj_getVert_succ (by omega : j+n<w.length))
      simpa only [Nat.add_assoc,Nat.succ_eq_add_one] using hs
  simpa only [Nat.add_sub_of_le hjk] using hh (k-j) (by omega)

lemma twoClusterEvent_self (u : V) (s : ℕ) : G.twoClusterEvent u u s=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  exact hω.1.1 (SimpleGraph.Reachable.refl _)

lemma twoClusterEvent_antitone (u v : V) : Antitone (G.twoClusterEvent u v) := by
  intro s t hst ω hω
  exact ⟨⟨hω.1.1,G.clusterTail_antitone u hst hω.1.2⟩,G.clusterTail_antitone v hst hω.2⟩

lemma exists_minimal_pair (p : unitInterval) (s r : ℕ) (a : ℝ) (ha : 0<a)
    (hex : ∃ u v, v∈G.vertexBall u r ∧ a≤(G.law p).real (G.twoClusterEvent u v s)) :
    ∃ (u v : V) (w : G.fullGraph.Walk u v), 1≤w.length ∧ w.length ≤ r ∧
      a≤(G.law p).real (G.twoClusterEvent u v s) ∧
      ∀ x y k, k<w.length → y∈G.vertexBall x k →
        (G.law p).real (G.twoClusterEvent x y s)<a := by
  let P (n : ℕ) := ∃ u v, v∈G.vertexBall u n ∧ a≤(G.law p).real (G.twoClusterEvent u v s)
  have hP : ∃ n, P n := ⟨r,hex⟩
  let d := Nat.find hP
  obtain ⟨u,v,hv,ha'⟩ := Nat.find_spec hP
  obtain ⟨w,hw⟩ := G.mem_vertexBall_iff_walk.mp hv
  have hwd : w.length=d := le_antisymm hw (Nat.find_min' hP ⟨u,v,G.walk_mem_vertexBall w,ha'⟩)
  have hpos : 0<d := by
    by_contra! hd
    have hd0 : d=0 := Nat.eq_zero_of_le_zero hd
    have huv : v=u := by
      change v∈G.vertexBall u d at hv
      simpa only [hd0,vertexBall,Set.mem_singleton_iff] using hv
    subst v
    rw [G.twoClusterEvent_self,measureReal_empty] at ha'
    linarith
  refine ⟨u,v,w,by omega,hwd.le.trans (Nat.find_min' hP hex),ha',?_⟩
  intro x y k hk hxy
  apply lt_of_not_ge
  intro hh
  exact Nat.find_min hP (by omega) ⟨x,y,hxy,hh⟩

lemma connection_lower_of_twoCluster [Countable E] (p : unitInterval)
    (u v : V) (s : ℕ) (t a : ℝ) (ht : 0≤t)
    (hu : t≤(G.law p).real (G.clusterTail u s))
    (hv : t≤(G.law p).real (G.clusterTail v s))
    (hsep : (G.law p).real (G.twoClusterEvent u v s)≤a) :
    t^2-a≤(G.law p).real {ω | (G.openGraph ω).Reachable u v} := by
  have hh := BernoulliProduct.harris_finiteWitness (fun _ : E => p)
    (G.clusterTail u s) (G.clusterTail v s) (G.clusterTail_isUpperSet u s)
    (G.clusterTail_isUpperSet v s) (G.clusterTail_hasFiniteOpenWitness u s)
    (G.clusterTail_hasFiniteOpenWitness v s)
  rw [BernoulliProduct.law_const] at hh
  have hm : G.clusterTail u s∩G.clusterTail v s ⊆
      {ω | (G.openGraph ω).Reachable u v}∪G.twoClusterEvent u v s := by
    intro ω hω
    by_cases hc : (G.openGraph ω).Reachable u v
    · exact Or.inl hc
    · exact Or.inr ⟨⟨hc,hω.1⟩,hω.2⟩
  have hbound := (measureReal_mono hm (μ := G.law p)).trans
    (measureReal_union_le _ _)
  change (G.law p).real (G.clusterTail u s)*(G.law p).real (G.clusterTail v s) ≤
    (G.law p).real (G.clusterTail u s∩G.clusterTail v s) at hh
  have hprod : t^2≤(G.law p).real (G.clusterTail u s)*(G.law p).real (G.clusterTail v s) := by
    simpa only [pow_two] using mul_le_mul hu hv ht (ht.trans hu)
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_MinimalInterpolation
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

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

lemma maximal_interpolation_pair (p : unitInterval) (hp : (p:ℝ)∈Set.Ioo 0 1)
    (s r : ℕ) {a c t ε : ℝ} (ha : 0<a) (hc : 0 < c) (ht : 0≤t)
    (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-(p:ℝ)) (hac : a ≤ c) (hct : 2*c≤t^2)
    (htail : ∀ v, t≤(G.law p).real (G.clusterTail v s))
    (hex : ∃ u v, v∈G.vertexBall u r ∧ a≤(G.law p).real (G.twoClusterEvent u v s)) :
    ∃ u v, G.fullGraph.Adj u v ∧ 0<(G.law p).real (G.twoClusterEvent u v s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent u v s)) ≤
        max 1 (interpolationConstant (c/2) ε) * (Real.log (1/a)+Nat.clog 2 r+1) := by
  obtain ⟨u,v,w,hwpos,hwr,hδ,hmin⟩ := G.exists_minimal_pair p s r a ha hex
  have hδpos : 0<(G.law p).real (G.twoClusterEvent u v s) := ha.trans_le hδ
  have ha1 : a≤1 := hδ.trans measureReal_le_one
  have halog : 0≤Real.log (1/a) := Real.log_nonneg ((le_div_iff₀ ha).mpr (by linarith))
  have hbnon : 0≤Real.log (1/a)+(Nat.clog 2 r:ℝ)+1 := by positivity
  have hlog : -Real.log ((G.law p).real (G.twoClusterEvent u v s))≤Real.log (1/a) := by
    rw [one_div,Real.log_inv]
    exact neg_le_neg (Real.log_le_log ha hδ)
  by_cases hd : w.length=1
  · refine ⟨u,v,?_,hδpos,?_⟩
    · have hh := w.adj_getVert_succ (by omega : 0<w.length)
      simpa only [SimpleGraph.Walk.getVert_zero,← hd,Nat.zero_add,SimpleGraph.Walk.getVert_length] using hh
    · calc
        _ ≤ Real.log (1/a) := hlog
        _ ≤ Real.log (1/a)+(Nat.clog 2 r:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) (Nat.clog 2 r); linarith
        _ ≤ _ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (le_max_left 1 (interpolationConstant (c/2) ε)) hbnon
  · have hconn : ∀ j k, j<k → k≤w.length → k-j<w.length →
        c≤(G.law p).real {ω | (G.openGraph ω).Reachable (w.getVert j) (w.getVert k)} := by
      intro j k hjk hk hdiff
      have hm := hmin (w.getVert j) (w.getVert k) (k-j) hdiff
        (G.walk_getVert_mem_vertexBall w j k hjk.le hk)
      have hh := G.connection_lower_of_twoCluster p (w.getVert j) (w.getVert k) s t a ht
        (htail _) (htail _) hm.le
      linarith
    have hδ' : 0<(G.law p).real (G.twoClusterEvent (w.getVert 0) (w.getVert w.length) s) := by
      simpa only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length] using hδpos
    obtain ⟨j,hj,hjp,hjl⟩ := G.infinite_interpolation_measure w.length w.getVert (by omega) p hp
      hc hε hεp hεq hconn s hδ'
    refine ⟨w.getVert j,w.getVert (j+1),w.adj_getVert_succ hj,hjp,?_⟩
    simp only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_length,one_div,Real.log_inv] at hjl
    have hclog : (Nat.clog 2 w.length:ℝ)≤Nat.clog 2 r := Nat.cast_le.mpr (Nat.clog_mono_right 2 hwr)
    calc
      _ ≤ interpolationConstant (c/2) ε *
        (-Real.log ((G.law p).real (G.twoClusterEvent u v s))+(Nat.clog 2 w.length:ℝ)+1) := hjl
      _ ≤ interpolationConstant (c/2) ε * (Real.log (1/a)+(Nat.clog 2 r:ℝ)+1) :=
        mul_le_mul_of_nonneg_left (by linarith) (interpolationConstant_pos _ hε).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hbnon

end CriticalPercolation.BondGraph
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_AdjacentLog
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
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma adjacent_log_lower (A ε : ℝ) (hA : 0<A) (hε : 0<ε)
    (p : unitInterval) (hεp : ε≤p) (s : ℕ) (hs : 1 ≤ s) (e : E)
    (hbound : ∀ K : ℕ,
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
        A/((p:ℝ)*(2:ℝ)^K))
    (hpos : 0<(G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)) :
    Real.log s/2-Real.log (2*A/ε) ≤
      -Real.log ((G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)) := by
  let K := Nat.log 4 s
  let δ := (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)
  have hK : 4^K ≤ s := Nat.pow_log_le_self 4 (by omega)
  have hu : (s:ℝ) < (4:ℝ)^(K+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<(4:ℕ)) s
  have hp : 0<(p:ℝ) := hε.trans_le hεp
  have hm : δ≤A/(ε*(2:ℝ)^K) := by
    calc _ ≤ (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) :=
            measureReal_mono (G.twoClusterEvent_antitone _ _ hK)
         _ ≤ A/((p:ℝ)*(2:ℝ)^K) := hbound K
         _ ≤ _ := div_le_div_of_nonneg_left hA.le (by positivity)
            (mul_le_mul_of_nonneg_right hεp (by positivity))
  have hl := Real.log_le_log hpos hm
  rw [Real.log_div hA.ne' (by positivity),Real.log_mul hε.ne' (by positivity),Real.log_pow] at hl
  have hspos : (0:ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hls := Real.log_lt_log hspos hu
  rw [Real.log_pow,Nat.cast_add,Nat.cast_one] at hls
  have hlog4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hlog4] at hls
  have heq : Real.log (2*A/ε)=Real.log 2+Real.log A-Real.log ε := by
    rw [Real.log_div (by positivity) hε.ne',Real.log_mul (by norm_num) hA.ne']
  rw [heq]
  change Real.log δ ≤ _ at hl
  change Real.log s/2-_ ≤ -Real.log δ
  linarith

lemma twoClusterEvent_of_adj {u v : V} (h : G.fullGraph.Adj u v) :
    ∃ e : E, ∀ s, G.twoClusterEvent u v s =
      G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s := by
  obtain ⟨⟨e,_,he⟩,_⟩ := h
  refine ⟨e,fun s => G.twoClusterEvent_sym2 ?_ s⟩
  exact he.symm.trans (G.ends e).out_eq.symm

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
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SuperpolynomialAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Filter Set
open scoped Topology

namespace CriticalPercolation

lemma clog_two_le_log (r : ℕ) (hr : 1 ≤ r) :
    (Nat.clog 2 r:ℝ) ≤ Real.log r / Real.log 2 + 1 := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hclog : Nat.clog 2 r ≤ Nat.log 2 r+1 :=
    Nat.clog_le_of_le_pow (Nat.lt_pow_succ_log_self (by norm_num : 1<(2:ℕ)) r).le
  have hp : (2:ℝ)^(Nat.log 2 r)≤(r:ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : r≠0)
  have hlog := Real.log_le_log (by positivity : (0:ℝ)<2^(Nat.log 2 r)) hp
  rw [Real.log_pow] at hlog
  have hh : (Nat.log 2 r:ℝ)≤Real.log r/Real.log 2 := (le_div_iff₀ h2).mpr hlog
  have hc : (Nat.clog 2 r:ℝ)≤(Nat.log 2 r:ℝ)+1 := by exact_mod_cast hclog
  linarith

lemma band_log_bound {c f : ℝ} (hc : 0 < c) (s : ℕ) (hs : 2 ≤ s)
    (hf : (Real.log s)⁻¹^2≤f) :
    0 < c*f ∧ Real.log (1/(c*f)) ≤ Real.log (1/c)+2*Real.log (Real.log s) := by
  have hls : 0<Real.log s := Real.log_pos (by exact_mod_cast hs)
  have hpos : 0<(Real.log s)⁻¹^2 := pow_pos (inv_pos.mpr hls) _
  have hfp : 0<f := hpos.trans_le hf
  refine ⟨mul_pos hc hfp,?_⟩
  have hh := Real.log_le_log hpos hf
  rw [Real.log_pow,Real.log_inv] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [one_div,Real.log_inv,Real.log_mul hc.ne' hfp.ne',one_div,Real.log_inv]
  linarith

lemma deletion_cost_le_quarter (θ : ℝ) (_hθ : 0<θ) (D s : ℕ) (hs : 1 ≤ s)
    (hscale : 4*((D:ℝ)+1)≤θ*s) :
    (s^2+D*s^3:ℕ)≤θ/4*(s:ℝ)^4 := by
  have hspos : (0:ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  have h2 : (s:ℝ)^2≤(s:ℝ)^3 := by nlinarith [sq_nonneg (s:ℝ)]
  have hh := mul_le_mul_of_nonneg_right hscale (show 0≤(s:ℝ)^3 by positivity)
  push_cast
  nlinarith

lemma eventually_log_dominates (C B : ℝ) (_hC : 0≤C) :
    ∀ᶠ s : ℕ in atTop, C*(2*Real.log (Real.log s)+B)<Real.log s/4 := by
  have hl : Tendsto (fun s : ℕ => Real.log (s:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa only [pow_one,one_mul,add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hc : Tendsto (fun s : ℕ => B/Real.log s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hl
  have ht : Tendsto (fun s : ℕ => C*(2*(Real.log (Real.log s)/Real.log s)+B/Real.log s))
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := C)).mul (((tendsto_const_nhds (x := (2:ℝ))).mul (hr.comp hl)).add hc)
    simpa only [Function.comp_apply,mul_zero,zero_add] using hh
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/4)),
    hl.eventually (eventually_gt_atTop (0:ℝ))] with s hs hspos
  have he : C*(2*(Real.log (Real.log s)/Real.log s)+B/Real.log s) =
      C*(2*Real.log (Real.log s)+B)/Real.log s := by ring
  rw [he] at hs
  have hh := (div_lt_iff₀ hspos).mp hs
  linarith

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SuperpolynomialRadius
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
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma exists_volume_radius (hg : G.SuperpolynomialGrowth) (s : ℕ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ v : V, s^4≤(G.vertexBall v r).ncard := by
  obtain ⟨N,hN⟩ := hg 1
  refine ⟨N+s^4+1,by omega,?_⟩
  intro v
  have hh := hN (N+s^4+1) (by omega) v
  simpa only [pow_one] using (show s^4≤N+s^4+1 by omega).trans (by simpa only [pow_one] using hh)

lemma superpolynomial_radius_log (hg : G.SuperpolynomialGrowth)
    (M : ℕ) (hM : 1≤M) :
    ∃ C : ℝ, 0≤C ∧ ∀ s : ℕ, 1 ≤ s →
      ∃ r : ℕ, 1 ≤ r ∧ (∀ v : V, s^4≤(G.vertexBall v r).ncard) ∧
        Real.log r ≤ 4/(M:ℝ)*Real.log s+C := by
  obtain ⟨N,hN⟩ := hg M
  let C := Real.log ((N:ℝ)+2)+Real.log 2
  have hlog2 : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have hC : 0≤C := add_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) N; linarith)) hlog2
  refine ⟨C,hC,?_⟩
  intro s hs
  let H := G.exists_volume_radius hg s
  let r := Nat.find H
  obtain ⟨hr,hrV⟩ := Nat.find_spec H
  change 1 ≤ r at hr
  change ∀ v, s^4≤(G.vertexBall v r).ncard at hrV
  refine ⟨r,hr,hrV,?_⟩
  have hrpos : (0:ℝ) < r := Nat.cast_pos.mpr (by omega)
  have hspos : (0:ℝ) < s := Nat.cast_pos.mpr (by omega)
  have hlogs : 0≤Real.log s := Real.log_nonneg (by exact_mod_cast hs)
  have hMp : (0:ℝ)<M := Nat.cast_pos.mpr (by omega)
  by_cases hsmall : r≤N+2
  · have hh := Real.log_le_log hrpos (Nat.cast_le.mpr hsmall)
    simp only [Nat.cast_add,Nat.cast_ofNat] at hh
    dsimp [C]
    have hn : 0≤4/(M:ℝ)*Real.log s := mul_nonneg (by positivity) hlogs
    linarith
  · have hr2 : 2 ≤ r := by omega
    have hprev : ¬(1 ≤ r-1 ∧ ∀ v : V, s^4≤(G.vertexBall v (r-1)).ncard) :=
      Nat.find_min H (by omega)
    have hex : ∃ v : V, (G.vertexBall v (r-1)).ncard < s^4 := by
      by_contra! hn
      exact hprev ⟨by omega, hn⟩
    obtain ⟨v,hv⟩ := hex
    have hpow : (r-1)^M < s^4 := (hN (r-1) (by omega) v).trans_lt hv
    have hpredpos : (0:ℝ)<(r-1:ℕ) := Nat.cast_pos.mpr (by omega)
    have hpowreal : ((r-1:ℕ):ℝ)^M<(s:ℝ)^4 := by exact_mod_cast hpow
    have hl := Real.log_lt_log (pow_pos hpredpos _) hpowreal
    rw [Real.log_pow,Real.log_pow] at hl
    have hless : Real.log (r-1:ℕ) ≤ 4/(M:ℝ)*Real.log s := by
      apply (mul_le_mul_iff_right₀ hMp).mp
      calc
        _ ≤ 4*Real.log s := hl.le
        _ = _ := by field_simp
    have hrle : (r:ℝ)≤2*((r-1:ℕ):ℝ) := by exact_mod_cast (show r≤2*(r-1) by omega)
    have hlogr := Real.log_le_log hrpos hrle
    rw [Real.log_mul (by norm_num) hpredpos.ne'] at hlogr
    dsimp [C]
    have hn := Real.log_nonneg (show 1≤(N:ℝ)+2 by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SuperpolynomialContradiction
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma eventually_no_superpolynomial_band
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hsub : G.SubexponentialGrowth)
    (hsuper : G.SuperpolynomialGrowth) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ≤1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ s : ℕ in atTop, ∀ (p : unitInterval) (z : V), ε≤p → ε≤1-(p:ℝ) →
      (Real.log s)⁻¹^2 ≤ (G.law p).real (G.clusterBand z s) →
      (∀ v, θ/2≤(G.law p).real (G.clusterTail v s)) → False := by
  obtain ⟨A,hA,hAbound⟩ := G.subexponential_adjacent_bound hconnected hlocal hquasi hsub
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hquasi
  let c := θ^2/8
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hcθ : c≤θ/4 := by dsimp [c] <;> nlinarith
  let C := max 1 (interpolationConstant (c/2) ε)
  have hC1 : 1≤C := le_max_left _ _
  have hC : 0<C := by linarith
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M,hM⟩ := exists_nat_gt (16*C/Real.log 2+1)
  have hM1 : 1≤M := by
    have hn : 0≤16*C/Real.log 2 := by positivity
    have hh : (1:ℝ)<M := by linarith
    exact_mod_cast hh.le
  have hMp : (0:ℝ)<M := Nat.cast_pos.mpr (by omega)
  have hMs : 16*C≤(M:ℝ)*Real.log 2 := by
    have hh : 16*C/Real.log 2≤(M:ℝ) := by linarith
    exact (div_le_iff₀ hlog2).mp hh
  have hslope : C*(4/(M:ℝ)/Real.log 2)≤1/4 := by
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    rw [show C*(4/(M:ℝ)/Real.log 2)*4=16*C/((M:ℝ)*Real.log 2) by ring]
    exact (div_le_one (mul_pos hMp hlog2)).mpr hMs
  obtain ⟨R,hR,hRadius⟩ := G.superpolynomial_radius_log hsuper M hM1
  let B := Real.log (1/c)+R/Real.log 2+2+Real.log (2*A/ε)/C
  have hslow := CriticalPercolation.eventually_log_dominates C B hC.le
  have hscale : ∀ᶠ s : ℕ in atTop, 4*((D:ℝ)+1)≤θ*s := by
    have hh := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    filter_upwards [hh.eventually (eventually_ge_atTop (4*((D:ℝ)+1)/θ))] with s hs
    have := (div_le_iff₀ hθ).mp hs
    nlinarith
  filter_upwards [hslow,hscale,eventually_ge_atTop 2] with s hslow hscale hs
  intro p z hεp hεq hband htail
  have hp : (p:ℝ)∈Set.Ioo 0 1 := ⟨hε.trans_le hεp,by linarith⟩
  obtain ⟨r,hr,hrV,hrlog⟩ := hRadius s (by omega)
  let BF := G.vertexBall_finite hlocal z r
  let Bv := BF.toFinset
  have hBn : Bv.Nonempty := ⟨z,BF.mem_toFinset.mpr (G.mem_vertexBall_self z r)⟩
  have hcost : (s^2+D*s^3:ℕ)≤θ/4*(Bv.card:ℝ) := by
    calc
      _ ≤ θ/4*(s:ℝ)^4 := CriticalPercolation.deletion_cost_le_quarter θ hθ D s (by omega) hscale
      _ ≤ θ/4*(Bv.card:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := hrV z
        rw [Set.ncard_eq_toFinset_card _ BF] at hh
        exact_mod_cast hh
  obtain ⟨y,hy,hyprob⟩ := G.exists_nearby_large_pair hconnected hlocal p Bv hBn z s D hD θ
    (fun v _ => htail v) hcost
  let f := (G.law p).real (G.clusterBand z s)
  have hf : 0≤f := measureReal_nonneg
  have hf1 : f≤1 := measureReal_le_one
  obtain ⟨haf,halog⟩ := CriticalPercolation.band_log_bound hc s hs hband
  have hex : ∃ u v, v∈G.vertexBall u r ∧ c*f≤(G.law p).real (G.twoClusterEvent u v s) := by
    refine ⟨y,z,G.vertexBall_comm.mp (BF.mem_toFinset.mp hy),?_⟩
    exact (mul_le_mul_of_nonneg_right hcθ hf).trans hyprob
  obtain ⟨u,v,huv,hprob,hupper⟩ := G.maximal_interpolation_pair p hp s r haf hc
    (by positivity : 0≤θ/2) hε hεp hεq
    (by nlinarith : c*f ≤ c) (by dsimp [c]; nlinarith : 2*c≤(θ/2)^2) htail hex
  obtain ⟨e,he⟩ := G.twoClusterEvent_of_adj huv
  rw [he s] at hprob hupper
  have hlower := G.adjacent_log_lower A ε hA hε p hεp s (by omega) e (hAbound p hp e) hprob
  have hclog := CriticalPercolation.clog_two_le_log r hr
  have hlogsr : Real.log r/Real.log 2≤(4/(M:ℝ)*Real.log s+R)/Real.log 2 :=
    div_le_div_of_nonneg_right hrlog hlog2.le
  have hlogs : 0≤Real.log s := Real.log_nonneg (by exact_mod_cast (show 1 ≤ s by omega))
  have hterm : C*((4/(M:ℝ)*Real.log s+R)/Real.log 2) ≤
      Real.log s/4+C*(R/Real.log 2) := by
    have hh := mul_le_mul_of_nonneg_right hslope hlogs
    convert add_le_add hh (le_refl (C*(R/Real.log 2))) using 1 <;> first | rfl | ring
  have hupper' : -Real.log ((G.law p).real
      (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)) ≤
      C*(Real.log (1/c)+2*Real.log (Real.log s)+(Nat.clog 2 r:ℝ)+1) := by
    exact hupper.trans (mul_le_mul_of_nonneg_left (by dsimp [f] at * <;> linarith) hC.le)
  have hg := mul_le_mul_of_nonneg_left (hclog.trans (add_le_add hlogsr (le_refl 1))) hC.le
  have hB : C*(2*Real.log (Real.log s)+B) =
      C*(2*Real.log (Real.log s)+Real.log (1/c)+R/Real.log 2+2)+Real.log (2*A/ε) := by
    dsimp [B]
    field_simp
    ring
  rw [hB] at hslow
  linarith

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Growth_SuperpolynomialMain
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

theorem no_percolation_at_criticality_superpolynomial_oai
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hpc : G.criticalProbability<1)
    (hsub : G.SubexponentialGrowth) (hsuper : G.SuperpolynomialGrowth) :
    G.law G.criticalProbability G.percolates = 0 := by
  let := G.countable_vertices hconnected hlocal
  let := G.countable_bonds hconnected hlocal
  let := hconnected.nonempty
  by_contra hbad
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability hconnected hlocal hquasi
    G.criticalProbability (pos_iff_ne_zero.mpr hbad)
  have hθ1 : θ≤1 := (hroot (Classical.arbitrary V)).trans measureReal_le_one
  have hpcpos := G.criticalProbability_pos hconnected hlocal hquasi
  let ε : ℝ := min ((G.criticalProbability:ℝ)/2) (1-(G.criticalProbability:ℝ))
  have hε : 0<ε := lt_min (by positivity) (by exact sub_pos.mpr hpc)
  have hforbid := G.eventually_no_superpolynomial_band hconnected hlocal hquasi hsub hsuper θ hθ hθ1 ε hε
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

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality_superpolynomial_oai.{u_1, u_2}
