-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:35.150423+00:00
-- url     : https://prove2.me/submissions/c7bc098a-761a-4df2-ab76-7e26955f8348

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Definitions.Def_OAIQ228B001
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos

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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterObject
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

lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)

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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ProductConditioning
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
open scoped Classical ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma measurable_forceOn_joint (S : Set E) :
    Measurable (fun z : Set E × Set E => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    inferInstance (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · simpa only [forceOn,ite_eq_left he,Function.comp_def] using (measurable_set_mem e).comp measurable_fst
  · simpa only [forceOn,ite_eq_right he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd

lemma forceOn_resample_law (q : E → unitInterval) (S : Set E) :
    ((law q).prod (law q)).map (fun z : Set E × Set E => forceOn S z.1 z.2)=law q := by
  let f : Set E → Set E := forceOn Sᶜ ∅
  let g : Set E → Set E := forceOn S ∅
  have hf : Measurable f := measurable_forceOn _ _
  have hg : Measurable g := measurable_forceOn _ _
  have hfb : @Measurable (Set E) (Set E) (blockSigma S) inferInstance f := by
    have hh := measurable_forceOn_block Sᶜ (∅ : Set E)
    rw [compl_compl] at hh
    exact hh
  have hgb : @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance g :=
    measurable_forceOn_block S ∅
  have hi : IndepFun f g (law q) :=
    indep_of_indep_of_le (independent_blocks q S) hfb.comap_le hgb.comap_le
  have hm := hi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hp := congrArg (Measure.map (fun z : Set E × Set E => forceOn S z.1 z.2)) hm
  rw [Measure.map_prod_map _ _ hf hg,Measure.map_map (measurable_forceOn_joint S)
    (hf.prodMk hg),Measure.map_map (measurable_forceOn_joint S) (hf.prodMap hg)] at hp
  have he1 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ (fun ω => (f ω,g ω))=id := by
    funext ω
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  have he2 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ Prod.map f g=
      (fun z : Set E × Set E => forceOn S z.1 z.2) := by
    funext z
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  rw [he1,he2,Measure.map_id] at hp
  exact hp.symm

lemma lintegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫⁻ σ, blockProbability q S A σ ∂law q)=law q A := by
  simp_rw [blockProbability_eq_lintegral q S A hA]
  have hm : Measurable (fun z : Set E × Set E =>
      A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    (measurable_const.indicator hA).comp (measurable_forceOn_joint S)
  rw [← lintegral_prod _ hm.aemeasurable]
  have hi : Measurable (A.indicator (1 : Set E → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_map hi (measurable_forceOn_joint S),
    forceOn_resample_law,lintegral_indicator_one hA]

lemma blockSigma_eq_comap (S : Set E) :
    blockSigma S=MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      Set.instMeasurableSpace := by
  change (⨆ e∈S, MeasurableSpace.comap (fun σ : Set E => e∈σ) inferInstance)=
    MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      (⨆ e : S, MeasurableSpace.comap (fun σ : Set S => e∈σ) inferInstance)
  rw [MeasurableSpace.comap_iSup,iSup_subtype']
  congr 1
  funext e
  rw [MeasurableSpace.comap_comp]
  rfl

lemma block_event_forceOn (S : Set E) (B : Set (Set E))
    (hB : MeasurableSet[blockSigma S] B) (σ ω : Set E) :
    forceOn S σ ω∈B ↔ σ∈B := by
  rw [blockSigma_eq_comap] at hB
  obtain ⟨C,hC,rfl⟩ := hB
  have he : (Subtype.val ⁻¹' forceOn S σ ω : Set S)=Subtype.val ⁻¹' σ := by
    ext e
    simp only [mem_preimage,mem_forceOn,ite_eq_left e.property]
  change (Subtype.val ⁻¹' forceOn S σ ω)∈C ↔ (Subtype.val ⁻¹' σ)∈C
  rw [he]

lemma blockProbability_inter_block (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hB : MeasurableSet[blockSigma S] B) (σ : Set E) :
    blockProbability q S (A∩B) σ=B.indicator (blockProbability q S A) σ := by
  unfold blockProbability
  by_cases hσ : σ∈B
  · rw [Set.indicator_of_mem hσ]
    congr 1
    ext ω
    simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,and_true]
  · rw [Set.indicator_of_notMem hσ]
    have he : forceOn S σ ⁻¹' (A∩B)=∅ := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,
        and_false,Set.mem_empty_iff_false]
    rw [he,measure_empty]

lemma setLIntegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet[blockSigma S] B) :
    (∫⁻ σ in B, blockProbability q S A σ ∂law q)=law q (A∩B) := by
  have hmB := (blockSigma_le S) _ hB
  rw [← lintegral_indicator hmB]
  simp_rw [← blockProbability_inter_block q S A B hB]
  exact lintegral_blockProbability q S (A∩B) (hA.inter hmB)

end CriticalPercolation.BernoulliProduct
end
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_GraphBalls
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

lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm

lemma Aut.vertexBall_ncard (φ : G.Aut) (o : V) (n : ℕ) :
    (G.vertexBall (φ.vertex o) n).ncard = (G.vertexBall o n).ncard := by
  rw [← Aut.vertexBall_image G φ,Set.ncard_image_of_injective _ φ.vertex.injective]

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

end CriticalPercolation.BondGraph
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

end CriticalPercolation.BondGraph
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

end CriticalPercolation.BernoulliProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DescendingFan
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

lemma stabilizerWeight_le_modularMass {S : Set V} {v x : V} (hx : x∈S) :
    G.stabilizerWeight v x≤G.modularMass v S := by
  simpa only [ite_eq_left hx,modularMass] using
    (ENNReal.le_tsum x (f := fun y => if y∈S then G.stabilizerWeight v y else 0))

lemma cluster_eq_with_weightCeiling {ω : Set E} {v : V} {K : ℝ≥0∞}
    (hK : G.modularMass v (G.cluster ω v)≤K) :
    G.cluster (ω∩G.inducedEdges (G.weightCeiling v K)) v=G.cluster ω v := by
  apply Set.Subset.antisymm (G.cluster_mono Set.inter_subset_left v)
  rintro x ⟨w⟩
  apply G.walk_reachable_induced _ ω w
  intro y hy
  exact (G.stabilizerWeight_le_modularMass (w.takeUntil y hy).reachable).trans hK

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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CutEdges
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_BallIncidence
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

namespace CriticalPercolation

namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma Aut.inducedEdges_map (φ : G.Aut) {K : Set E} {S : Set V}
    (hKS : K⊆G.inducedEdges S) : φ.edge '' K ⊆ G.inducedEdges (φ.vertex '' S) := by
  rintro e ⟨a,ha,rfl⟩ v hv
  rw [φ.preserves] at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w,hKS ha w hw,rfl⟩

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_CylinderApproximation
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical symmDiff ENNReal

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma finiteCoordinateEvents_ring : IsSetRing (finiteCoordinateEvents (E := E)) where
  empty_mem := ⟨∅,@MeasurableSet.empty (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩
  union_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.union (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)
  sdiff_mem := by
    rintro A B ⟨S,hS⟩ ⟨T,hT⟩
    refine ⟨S ∪ T,?_⟩
    exact @MeasurableSet.diff (Set E) (blockSigma ((S ∪ T : Finset E) : Set E)) _ _
      (blockSigma_mono (by simp) _ hS) (blockSigma_mono (by simp) _ hT)

lemma generateFrom_finiteCoordinateEvents :
    MeasurableSpace.generateFrom (finiteCoordinateEvents (E := E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
  apply le_antisymm
  · exact MeasurableSpace.generateFrom_le fun A ⟨S,hS⟩ => blockSigma_le _ _ hS
  · change (⨆ e : E, coordinateSigma e) ≤ _
    refine iSup_le fun e => ?_
    intro A hA
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨{e},?_⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl) :
      coordinateSigma e ≤ blockSigma (({e} : Finset E) : Set E)) _ hA

lemma exists_finiteCoordinate_approx (q : E → unitInterval)
    {A : Set (Set E)} (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (S : Finset E) (B : Set (Set E)), MeasurableSet[blockSigma (S : Set E)] B ∧
      law q (B ∆ A) < ε := by
  obtain ⟨B,⟨S,hB⟩,h⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    finiteCoordinateEvents_ring (μ := law q)
    (show ∃ D : Set (Set (Set E)), D.Countable ∧ D ⊆ finiteCoordinateEvents ∧
        law q (⋃₀ D)ᶜ = 0 from
      ⟨{Set.univ},by simp,by rintro A rfl; exact ⟨∅,@MeasurableSet.univ (Set E) (blockSigma ((∅ : Finset E) : Set E))⟩,by simp⟩)
    generateFrom_finiteCoordinateEvents.symm hA hε
  exact ⟨S,B,hB,h⟩

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LevelContactMeasurability
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma finiteSetChoice_coe {E : Type*} {S : Set E} (hS : S.Finite) :
    (finiteSetChoice S : Set E)=S := by simp [finiteSetChoice,hS]

lemma finiteSetChoice_eq_iff {E : Type*} (S : Set E) (U : Finset E) :
    finiteSetChoice S=U ↔ S=(U : Set E) ∨ (¬S.Finite ∧ U=∅) := by
  by_cases hS : S.Finite
  · have hh : finiteSetChoice S=U ↔ S=(U : Set E) := by
      calc
        finiteSetChoice S=U ↔ (finiteSetChoice S : Set E)=(U : Set E) := Finset.coe_inj.symm
        _ ↔ S=(U : Set E) := by rw [finiteSetChoice_coe hS]
    simpa [hS] using hh
  · have hne : S≠(U : Set E) := fun h => hS (h ▸ U.finite_toSet)
    simp [finiteSetChoice,hS,hne,eq_comm]

lemma measurableSet_set_eq_const {Ω E : Type*} {m : MeasurableSpace Ω} [Countable E]
    (S : Ω → Set E) (hS : @Measurable Ω (Set E) m inferInstance S) (U : Set E) :
    MeasurableSet[m] {ω | S ω=U} := by
  let : MeasurableSpace Ω := m
  have he : {ω | S ω=U}={ω | ∀ e, e∈S ω ↔ e∈U} := by
    ext ω
    exact Set.ext_iff
  rw [he]
  exact (Measurable.forall (fun e => ((measurable_pi_apply e).comp hS).iff measurable_const)).setOf

lemma measurableSet_finiteSetChoice {Ω E : Type*} [MeasurableSpace Ω] [Countable E]
    (S : Ω → Set E) (hS : Measurable S) (U : Finset E) :
    MeasurableSet {ω | finiteSetChoice (S ω)=U} := by
  have hmfinite : MeasurableSet {ω | (S ω).Finite} := by
    have he : {ω | (S ω).Finite}=⋃ F : Finset E, {ω | S ω=(F : Set E)} := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
      exact ⟨fun h => ⟨h.toFinset,h.coe_toFinset.symm⟩,
        fun ⟨F,hF⟩ => hF ▸ F.finite_toSet⟩
    rw [he]
    exact MeasurableSet.iUnion (fun F => measurableSet_set_eq_const S hS _)
  simp_rw [finiteSetChoice_eq_iff]
  exact (measurableSet_set_eq_const S hS _).union
    (hmfinite.compl.inter (MeasurableSet.const _))

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularGrowth
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_UniformDescendingFan
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

lemma Aut.massTailEvent_preimage (φ : G.Aut) (v : V) (K : ℝ≥0∞) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.massTailEvent (φ.vertex v) (φ.vertex v) K=
      G.massTailEvent v v K := by
  ext ω
  change K<G.modularMass (φ.vertex v) (G.cluster (φ.edge '' ω) (φ.vertex v)) ↔ _
  rw [←φ.cluster_image,φ.modularMass_image]
  rfl

lemma Aut.massTailEvent_real [Countable V] [Countable E] (φ : G.Aut)
    (p : unitInterval) (v : V) (K : ℝ≥0∞) :
    (G.law p).real (G.massTailEvent (φ.vertex v) (φ.vertex v) K)=
      (G.law p).real (G.massTailEvent v v K) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (BernoulliProduct.measurable_image_equiv φ.edge)
    (G.measurableSet_massTailEvent _ _ _),φ.massTailEvent_preimage]

lemma uniform_massTail_small [Countable V] [Countable E]
    (hq : G.QuasiTransitive) (p : unitInterval)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞)
    (η : ℝ) (hη : 0<η) :
    ∃ K : ℕ, 1≤K ∧ ∀ v, (G.law p).real (G.massTailEvent v v K)<η := by
  have hz (v : V) : (G.law p).real (G.heavyClusterEvent v v)=0 := by
    have hn : G.law p (G.heavyClusterEvent v v)=0 := by
      simpa only [heavyClusterEvent,not_not] using ae_iff.mp (hm v)
    simp only [measureReal_def,hn,ENNReal.toReal_zero]
  obtain ⟨S,hS,hcover⟩ := hq
  have he (v : V) : ∀ᶠ K : ℕ in atTop, (G.law p).real (G.massTailEvent v v K)<η := by
    have h := G.tendsto_real_massTail p v v
    rw [hz] at h
    exact h.eventually (gt_mem_nhds hη)
  obtain ⟨K,hK,hall⟩ := ((eventually_ge_atTop 1).and
    (hS.toFinset.eventually_all.mpr (fun v _ => he v))).exists
  refine ⟨K,hK,fun v => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  rw [φ.massTailEvent_real]
  exact hall s (hS.mem_toFinset.mpr hs)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_MinimalPair
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

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularCharacter
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

lemma modularRatio_aut_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio x (φ.vertex x) = G.modularRatio o (φ.vertex o) := by
  have h1 := G.modularRatio_cocycle hc hl o x (φ.vertex x)
  rw [G.modularRatio_aut_translate hc hl o x φ] at h1
  exact (mul_left_cancel₀ (ne_of_gt (G.modularRatio_pos hc hl o x)))
    (h1.trans (mul_comm _ _))

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

lemma modularRatio_aut_weight (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) (φ : G.Aut) :
    G.modularRatio (φ.vertex x) o =
      G.modularRatio (φ.vertex o) o * G.modularRatio x o := by
  rw [←G.modularRatio_cocycle hc hl (φ.vertex x) (φ.vertex o) o,
    Aut.modularRatio,mul_comm]

lemma exists_weight_contraction (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∃ φ : G.Aut, G.modularRatio (φ.vertex o) o < 1 := by
  by_contra hn
  apply hu
  intro φ x
  have hlow : ∀ ψ : G.Aut, 1 ≤ G.modularRatio (ψ.vertex o) o := by
    intro ψ
    exact le_of_not_gt (fun h => hn ⟨ψ,h⟩)
  have h1 := hlow φ
  have h2 := hlow φ⁻¹
  have hprod : G.modularRatio (φ.vertex o) o *
      G.modularRatio ((φ⁻¹).vertex o) o = 1 := by
    have h := G.modularRatio_aut_weight hc hl o ((φ⁻¹).vertex o) φ
    have he : φ.vertex ((φ⁻¹).vertex o)=o := φ.vertex.apply_symm_apply o
    rw [he,G.modularRatio_self] at h
    exact h.symm
  have he1 : G.modularRatio (φ.vertex o) o=1 := by nlinarith
  have he2 : G.modularRatio o (φ.vertex o)=1 := by
    have h := G.modularRatio_cocycle hc hl o (φ.vertex o) o
    rw [he1,mul_one,G.modularRatio_self] at h
    exact h
  have he := G.modularRatio_aut_base hc hl o x φ
  rw [he2] at he
  unfold modularRatio at he
  have hz : (G.suborbitCard (φ.vertex x) x : ℝ)≠0 :=
    ne_of_gt (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl _ _))
  exact_mod_cast (div_eq_one_iff_eq hz).mp he

lemma uniform_weight_contraction (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∃ c : ℝ, 0 < c ∧ c<1 ∧ ∃ R : ℕ, ∀ z : V, ∃ ψ : G.Aut,
      ψ.vertex z ∈ G.vertexBall z R ∧
      ∀ y, G.modularRatio (ψ.vertex y) o=c*G.modularRatio y o := by
  obtain ⟨φ,hφ⟩ := G.exists_weight_contraction hc hl hu o
  let c := G.modularRatio (φ.vertex o) o
  obtain ⟨S,hS,hcover⟩ := hq
  have hpath : ∀ z : S, ∃ n, φ.vertex z.val ∈ G.vertexBall z.val n :=
    fun z => G.reachable_mem_vertexBall (hc _ _)
  choose n hn using hpath
  let := hS.fintype
  let R := ∑ z : S, n z
  refine ⟨c,G.modularRatio_pos hc hl _ _,hφ,R,?_⟩
  intro z
  obtain ⟨s,hs,τ,rfl⟩ := hcover z
  refine ⟨τ*φ*τ⁻¹,?_,?_⟩
  · change τ.vertex (φ.vertex (τ.vertex.symm (τ.vertex s))) ∈ _
    rw [Equiv.symm_apply_apply,Aut.vertexBall_mem]
    exact G.vertexBall_mono s (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨s,hs⟩ : S))) (hn ⟨s,hs⟩)
  · intro y
    change G.modularRatio (τ.vertex (φ.vertex (τ.vertex.symm y))) o = _
    rw [G.modularRatio_aut_weight hc hl o _ τ,
      G.modularRatio_aut_weight hc hl o _ φ]
    have ht := G.modularRatio_aut_weight hc hl o (τ.vertex.symm y) τ
    rw [Equiv.apply_symm_apply] at ht
    change _ = c * G.modularRatio y o
    rw [ht]
    ring

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

lemma InsideWalk.mono {S D : Set V} {x y : V} {n m : ℕ}
    (h : G.InsideWalk S x y n) (hSD : S ⊆ D) (hnm : n ≤ m) :
    G.InsideWalk D x y m := by
  obtain ⟨p,hp,hs⟩ := h
  exact ⟨p,hp.trans hnm,fun v hv => hSD (hs v hv)⟩

lemma InsideWalk.refl {S : Set V} {x : V} (hx : x∈S) :
    G.InsideWalk S x x 0 := by
  refine ⟨.nil,le_rfl,?_⟩
  intro v hv
  have he : v=x := by simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using hv
  exact he.symm ▸ hx

lemma InsideWalk.reverse {S : Set V} {x y : V} {n : ℕ}
    (h : G.InsideWalk S x y n) : G.InsideWalk S y x n := by
  obtain ⟨p,hp,hs⟩ := h
  refine ⟨p.reverse,by simpa only [SimpleGraph.Walk.length_reverse] using hp,?_⟩
  intro v hv
  exact hs v (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hv)

lemma InsideWalk.append {S : Set V} {x y z : V} {n m : ℕ}
    (h : G.InsideWalk S x y n) (h' : G.InsideWalk S y z m) :
    G.InsideWalk S x z (n+m) := by
  obtain ⟨p,hp,hs⟩ := h
  obtain ⟨q,hq,ht⟩ := h'
  refine ⟨p.append q,by simpa only [SimpleGraph.Walk.length_append] using Nat.add_le_add hp hq,?_⟩
  intro v hv
  exact ((SimpleGraph.Walk.mem_support_append_iff p q).mp hv).elim (hs v) (ht v)

lemma insideWalk_ball {z x : V} {R : ℕ} (hx : x∈G.vertexBall z R) :
    G.InsideWalk (G.vertexBall z R) z x R := by
  obtain ⟨p,hp⟩ := G.mem_vertexBall_iff_walk.mp hx
  refine ⟨p,hp,?_⟩
  intro v hv
  exact G.vertexBall_mono z ((p.length_takeUntil_le_length hv).trans hp)
    (G.walk_mem_vertexBall (p.takeUntil v hv))

lemma modularRatio_weight_pow (o : V) (φ : G.Aut) (c : ℝ)
    (hφ : ∀ y, G.modularRatio (φ.vertex y) o=c*G.modularRatio y o)
    (n : ℕ) (y : V) :
    G.modularRatio ((φ^n).vertex y) o=c^n*G.modularRatio y o := by
  induction n with
  | zero => simp only [pow_zero,one_mul]; rfl
  | succ n ih =>
    rw [pow_succ']
    change G.modularRatio (φ.vertex ((φ^n).vertex y)) o = _
    rw [hφ,ih,pow_succ']
    ring

lemma safeBallDomain_iterate (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (T : ℝ) (R : ℕ) (z : V) (c : ℝ) (hc0 : 0 < c) (hc1 : c≤1)
    (φ : G.Aut) (hstep : φ.vertex z∈G.vertexBall z R)
    (hφ : ∀ y, G.modularRatio (φ.vertex y) o=c*G.modularRatio y o)
    (hball : ∀ y∈G.vertexBall z R, G.modularRatio y o≤T) (n : ℕ) :
    G.InsideWalk (G.safeBallDomain o T R) z ((φ^n).vertex z) (n*R) ∧
      G.modularRatio ((φ^n).vertex z) o ≤ c^n*T := by
  have hT : 0≤T := (G.modularRatio_pos hc hl z o).le.trans
    (hball z (G.mem_vertexBall_self z R))
  have hballs (m : ℕ) : G.vertexBall ((φ^m).vertex z) R⊆G.safeBallDomain o T R := by
    intro x hx
    refine ⟨(φ^m).vertex z,hx,?_⟩
    intro y hy
    obtain ⟨a,rfl⟩ := (φ^m).vertex.surjective y
    have ha := (Aut.vertexBall_mem G (φ^m) z a R).mp hy
    rw [G.modularRatio_weight_pow o φ c hφ]
    calc
      c^m*G.modularRatio a o ≤ c^m*T :=
        mul_le_mul_of_nonneg_left (hball a ha) (pow_nonneg hc0.le m)
      _ ≤ T := mul_le_of_le_one_left hT (pow_le_one₀ hc0.le hc1)
  constructor
  · induction n with
    | zero =>
      rw [pow_zero,Nat.zero_mul]
      change G.InsideWalk (G.safeBallDomain o T R) z z 0
      exact InsideWalk.refl G (hballs 0 (G.mem_vertexBall_self z R))
    | succ n ih =>
      have hs : (φ^(n+1)).vertex z∈G.vertexBall ((φ^n).vertex z) R := by
        rw [pow_succ]
        exact (Aut.vertexBall_mem G (φ^n) z (φ.vertex z) R).mpr hstep
      have hw := (G.insideWalk_ball hs).mono G (hballs n) le_rfl
      have hh := ih.append G hw
      simpa only [Nat.add_mul,Nat.one_mul] using hh
  · rw [G.modularRatio_weight_pow o φ c hφ]
    exact mul_le_mul_of_nonneg_left (hball z (G.mem_vertexBall_self z R)) (pow_nonneg hc0.le n)

theorem safeBallDomain_uniform_descent (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hu : ¬G.CombinatoriallyUnimodular) (o : V) :
    ∃ R : ℕ, ∃ C : ℝ, 1≤C ∧
      (∀ T, {x | G.modularRatio x o≤T/C}⊆G.safeBallDomain o T R) ∧
      ∀ a : ℝ, 0<a → ∃ L : ℕ, ∀ T : ℝ, ∀ x∈G.safeBallDomain o T R,
        ∃ y, G.modularRatio y o≤a*T ∧ G.InsideWalk (G.safeBallDomain o T R) x y L := by
  obtain ⟨c,hc0,hc1,R,hcon⟩ := G.uniform_weight_contraction hc hl hq hu o
  obtain ⟨C,hC,hClow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  refine ⟨R,C,hC,hClow o,?_⟩
  intro a ha
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one ha hc1
  refine ⟨R+n*R,?_⟩
  rintro T x ⟨z,hx,hball⟩
  obtain ⟨φ,hstep,hφ⟩ := hcon z
  have hi := G.safeBallDomain_iterate hc hl o T R z c hc0 hc1.le φ hstep hφ hball n
  refine ⟨(φ^n).vertex z,?_,?_⟩
  · have hT : 0≤T := (G.modularRatio_pos hc hl z o).le.trans
      (hball z (G.mem_vertexBall_self z R))
    exact hi.2.trans (mul_le_mul_of_nonneg_right hn.le hT)
  · have hw := (G.insideWalk_ball hx).reverse G
    have hd : G.vertexBall z R⊆G.safeBallDomain o T R := fun y hy => ⟨z,hy,hball⟩
    exact (hw.mono G hd le_rfl).append G hi.1

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_DomainPercolation
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

lemma walk_finite_bond_witness {x y : V} (p : G.fullGraph.Walk x y)
    (S : Set V) (hp : ∀ v∈p.support, v∈S) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges S ∧ F.ncard≤p.length ∧
      y∈G.cluster F x := by
  induction p with
  | nil => exact ⟨∅,Set.finite_empty,Set.empty_subset _,by simp,.refl _⟩
  | @cons x y z h p ih =>
    obtain ⟨F,hF,hFS,hcard,hconn⟩ := ih (fun v hv => hp v (List.mem_cons_of_mem _ hv))
    obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
    have hex : x∈S := hp x (by simp)
    have hey : y∈S := hp y (List.mem_cons_of_mem _ p.start_mem_support)
    have heS : e∈G.inducedEdges S := by
      intro v hv
      rw [he] at hv
      exact (Sym2.mem_iff.mp hv).elim (fun he => he ▸ hex) (fun he => he ▸ hey)
    refine ⟨insert e F,hF.insert e,Set.insert_subset heS hFS,?_,?_⟩
    · exact (Set.ncard_insert_le e F).trans (by simpa only [SimpleGraph.Walk.length_cons] using Nat.add_le_add_right hcard 1)
    · have hxy : (G.openGraph (insert e F)).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert _ _,he⟩,hne⟩
      exact hxy.reachable.trans (G.cluster_mono (Set.subset_insert _ _) y hconn)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_SelectedFresh
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

lemma block_event_disjoint_forceOn (X Y : Set E) (hXY : Disjoint X Y)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma Y] A) (σ ω : Set E) :
    forceOn X σ ω∈A ↔ ω∈A := by
  have he : forceOn Y (forceOn X σ ω) ω=ω := by
    ext e
    by_cases heY : e∈Y
    · have heX : e∉X := fun h => Set.disjoint_left.mp hXY h heY
      simp only [mem_forceOn,ite_eq_left heY,ite_eq_right heX]
    · simp only [mem_forceOn,ite_eq_right heY]
  have hh := block_event_forceOn Y A hA (forceOn X σ ω) ω
  rw [he] at hh
  exact hh.symm

lemma selectedEvent_eq_iUnion (d : Set E → I) (A : I → Set (Set E)) :
    selectedEvent d A=⋃ i, ({ω | d ω=i}∩A i) := by
  ext ω
  simp only [selectedEvent,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  exact ⟨fun h => ⟨d ω,rfl,h⟩,fun ⟨i,hi,h⟩ => hi.symm ▸ h⟩

lemma measurableSet_selectedEvent [Countable I] (d : Set E → I)
    (A : I → Set (Set E)) (hd : ∀ i, MeasurableSet {ω | d ω=i})
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (selectedEvent d A) := by
  rw [selectedEvent_eq_iUnion]
  exact MeasurableSet.iUnion (fun i => (hd i).inter (hA i))

theorem blockProbability_selected (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i)) (σ : Set E) :
    blockProbability q X (selectedEvent d A) σ=law q (A (d σ)) := by
  unfold blockProbability
  congr 1
  ext ω
  change forceOn X σ ω∈A (d (forceOn X σ ω)) ↔ ω∈A (d σ)
  have hh : d (forceOn X σ ω)=d σ :=
    (block_event_forceOn X {τ | d τ=d σ} (hd _) σ ω).mpr rfl
  rw [hh]
  exact block_event_disjoint_forceOn X Y hXY (A (d σ)) (hA _) σ ω

theorem selected_fresh_bound [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, (law q).real (A (d σ)) ≤ r) :
    (law q).real (C∩selectedEvent d A) ≤ r*(law q).real C := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      blockProbability q X (selectedEvent d A) σ ≤ ENNReal.ofReal r := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : law q (selectedEvent d A∩C) ≤ ENNReal.ofReal r*law q C := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      (∫⁻ σ in C, blockProbability q X (selectedEvent d A) σ ∂law q) ≤
          ∫⁻ _ in C, ENNReal.ofReal r ∂law q :=
        setLIntegral_mono' (blockSigma_le X _ hC) hk
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_LevelCutProbability
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}

theorem selected_fresh_lower [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, r ≤ (law q).real (A (d σ))) :
    r*(law q).real C ≤ (law q).real (C∩selectedEvent d A) := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      ENNReal.ofReal r ≤ blockProbability q X (selectedEvent d A) σ := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : ENNReal.ofReal r*law q C ≤ law q (selectedEvent d A∩C) := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      _ = ∫⁻ _ in C, ENNReal.ofReal r ∂law q := by
        rw [lintegral_const,Measure.restrict_apply_univ]
      _ ≤ _ := setLIntegral_mono' (blockSigma_le X _ hC) hk
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht

lemma law_closedBlock_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N)
    (hq : ∀ e∈S, (q e : ℝ) ≤ p) :
    (1-(p : ℝ))^N ≤ (law q).real (closedBlock S) := by
  have hp0 : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.2.2
  have hp1 : 1-(p : ℝ) ≤ 1 := by linarith [p.2.1]
  rw [measureReal_def,law_closedBlock q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (1-(p : ℝ))^S.ncard := pow_le_pow_of_le_one hp0 hp1 hN
    _ = ∏ e∈hS.toFinset, (1-(p : ℝ)) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro e he; exact hp0
      · intro e he
        change 1-(p : ℝ) ≤ (bitMeasure (q e)).real {False}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,ite_false, if_false] using sub_le_sub_left (hq e (hS.mem_toFinset.mp he)) 1

end CriticalPercolation.BernoulliProduct
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SliceExploration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma cutEdges_disjoint_cluster (ω : Set E) (v : V) :
    Disjoint (G.cutEdges (G.cluster ω v)) ω := by
  apply Set.disjoint_left.mpr
  rintro e ⟨x,y,he,hx,hy⟩ hω
  have hne : x ≠ y := fun h => hx (h ▸ hy)
  exact hx (hy.trans (SimpleGraph.Adj.reachable
    (show (G.openGraph ω).Adj x y from ⟨⟨e,hω,he⟩,hne⟩)).symm)

lemma finite_cutEdges (hl : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.cutEdges S).Finite := by
  apply (G.finite_incident hl hS).subset
  rintro e ⟨x,y,he,_,hy⟩
  exact ⟨y,hy,by rw [he]; simp⟩

lemma cluster_eq_restricted_of_fresh_closed (X : Set E) (v : V) (ω : Set E)
    (h : Disjoint (G.freshClusterBoundary X v ω) ω) :
    G.cluster ω v = G.cluster (ω∩X) v := by
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hn
    apply G.not_reachable_of_cut_closed (G.cluster (ω∩X) v) ω ?_ hn
      (SimpleGraph.Reachable.refl v) hx.symm
    intro e he hω
    by_cases hX : e∈X
    · exact Set.disjoint_left.mp (G.cutEdges_disjoint_cluster (ω∩X) v) he ⟨hω,hX⟩
    · exact Set.disjoint_left.mp h ⟨he,hX⟩ hω
  · exact G.cluster_mono Set.inter_subset_left v

lemma measurable_freshClusterBoundary [Countable V] [Countable E] (X : Set E) (v : V) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (G.freshClusterBoundary X v) := by
  let : MeasurableSpace (Set E) := blockSigma X
  refine Measurable.of_eval ?_
  intro e
  exact @Measurable.and (Set E) (blockSigma X) _ _
    (.exists fun x => .exists fun y => measurable_const.and
      ((((G.measurable_reachable v x).comp (measurable_inter_block X)).not).and
        ((G.measurable_reachable v y).comp (measurable_inter_block X)))) measurable_const

lemma measurableSet_smallFreshBoundary [Countable V] [Countable E] (X : Set E) (v : V) (M : ℕ) :
    MeasurableSet[blockSigma X] (G.smallFreshBoundary X v M) := by
  have hf : MeasurableSet[blockSigma X] {ω | (G.cluster (ω∩X) v).Finite} := by
    let : MeasurableSpace (Set E) := blockSigma X
    simpa only [Function.comp_apply,Set.not_infinite] using
      (((G.measurable_infinite_cluster v).comp (measurable_inter_block X)).not).setOf
  exact hf.inter (measurableSet_Iic.preimage
    (measurable_ncard.comp (G.measurable_freshClusterBoundary X v)))

theorem smallFreshBoundary_cost [Countable V] [Countable E]
    (hl : G.LocallyFinite) (p : unitInterval) (X : Set E) (v : V) (M : ℕ)
    (H : Set (Set E)) (hH : MeasurableSet[blockSigma X] H) :
    (1-(p:ℝ))^M * (G.law p).real (H ∩ G.smallFreshBoundary X v M) ≤
      (G.law p).real (H \ G.infiniteEvent v) := by
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.freshClusterBoundary X v ω)
  let A : Finset E → Set (Set E) := fun S => closedBlock ((S : Set E)∩Xᶜ)
  have hd (S : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=S} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.freshClusterBoundary X v) (G.measurable_freshClusterBoundary X v) S
  have hA (S : Finset E) : MeasurableSet[blockSigma Xᶜ] (A S) :=
    blockSigma_mono Set.inter_subset_right _
      (measurableSet_closedBlock _ ((S.finite_toSet.subset Set.inter_subset_left).countable))
  have he (ω : Set E) (hω : ω∈G.smallFreshBoundary X v M) :
      ((d ω : Set E)∩Xᶜ)=G.freshClusterBoundary X v ω := by
    change (finiteSetChoice (G.freshClusterBoundary X v ω) : Set E)∩Xᶜ = _
    have hf : (G.freshClusterBoundary X v ω).Finite :=
      (G.finite_cutEdges hl hω.1).subset Set.sdiff_subset
    rw [finiteSetChoice_coe hf]
    exact Set.inter_eq_left.mpr (Set.sdiff_subset_compl _ _)
  have hb (ω : Set E) (hω : ω∈H∩G.smallFreshBoundary X v M) :
      (1-(p:ℝ))^M ≤ (G.law p).real (A (d ω)) := by
    change _ ≤ (G.law p).real (closedBlock ((d ω : Set E)∩Xᶜ))
    rw [he ω hω.2]
    simpa only [law,←law_const,freshClusterBoundary] using law_closedBlock_lower (fun _ : E => p) _
      ((G.finite_cutEdges hl hω.2.1).subset Set.sdiff_subset) p M hω.2.2 (fun _ _ => le_rfl)
  have hh := selected_fresh_lower (fun _ : E => p) X Xᶜ disjoint_compl_right d A hd hA
    (H∩G.smallFreshBoundary X v M) (hH.inter (G.measurableSet_smallFreshBoundary X v M))
    ((1-(p:ℝ))^M) (pow_nonneg (sub_nonneg.mpr p.2.2) _) (by
      simpa only [law,←law_const] using hb)
  simp only [law_const] at hh
  change (1-(p:ℝ))^M * (G.law p).real (H ∩ G.smallFreshBoundary X v M) ≤
    (G.law p).real (H ∩ G.smallFreshBoundary X v M ∩ selectedEvent d A) at hh
  apply hh.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro ω ⟨⟨hωH,hω⟩,hclosed⟩
  refine ⟨hωH,?_⟩
  have hc : Disjoint (G.freshClusterBoundary X v ω) ω := by
    change Disjoint ((d ω : Set E)∩Xᶜ) ω at hclosed
    rwa [he ω hω] at hclosed
  rw [infiniteEvent,Set.mem_ofPred_eq,G.cluster_eq_restricted_of_fresh_closed X v ω hc]
  exact hω.1.not_infinite

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FewOpenBonds
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder
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

lemma fewOpenBonds_probability_le (p : unitInterval) (S : Set E) (hS : S.Finite)
    (N L : ℕ) (hcard : (N+1)*L ≤ S.ncard) :
    (law (fun _ : E => p)).real {ω | (S∩ω).ncard ≤ N} ≤
      (N+1 : ℝ)*(1-(p:ℝ))^L := by
  let : Fintype S := hS.fintype
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (N+1) × Fin L) (β := S)
    (show Fintype.card (Fin (N+1) × Fin L) ≤ Fintype.card S by
      rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin]
      simpa only [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using hcard)
  let f : Fin (N+1) × Fin L → E := fun x => (e x).val
  have hf : Function.Injective f := fun x y h => e.injective (Subtype.ext h)
  let B : Fin (N+1) → Set E := fun i => Set.range (fun j : Fin L => f (i,j))
  have hBfinite (i : Fin (N+1)) : (B i).Finite := Set.finite_range _
  have hBcard (i : Fin (N+1)) : (B i).ncard = L := by
    rw [Set.ncard_range_of_injective (fun a b h => (Prod.mk.inj (hf h)).2)]
    simp
  have hcover : {ω : Set E | (S∩ω).ncard ≤ N} ⊆ ⋃ i, closedBlock (B i) := by
    intro ω hω
    by_contra hn
    have hopen : ∀ i : Fin (N+1), ∃ j : Fin L, f (i,j)∈ω := by
      intro i
      have hi : ¬ Disjoint (B i) ω := fun hh => hn (Set.mem_iUnion.mpr ⟨i,hh⟩)
      obtain ⟨b,hb,hbω⟩ := Set.not_disjoint_iff.mp hi
      obtain ⟨j,rfl⟩ := hb
      exact ⟨j,hbω⟩
    choose j hj using hopen
    have hinj : Function.Injective (fun i : Fin (N+1) => f (i,j i)) :=
      fun a b h => (Prod.mk.inj (hf h)).1
    have hsub : Set.range (fun i : Fin (N+1) => f (i,j i)) ⊆ S∩ω := by
      rintro x ⟨i,rfl⟩
      exact ⟨(e (i,j i)).property,hj i⟩
    have hh := Set.ncard_le_ncard hsub (hS.subset Set.inter_subset_left)
    rw [Set.ncard_range_of_injective hinj] at hh
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    exact Nat.not_succ_le_self N (hh.trans hω)
  have hreal : (bitMeasure p {False}).toReal = 1-(p:ℝ) := by
    simpa only [Measure.real,bitWeight,ite_false, if_false] using bitMeasure_real_singleton p False
  calc
    _ ≤ (law (fun _ : E => p)).real (⋃ i, closedBlock (B i)) := measureReal_mono hcover
    _ ≤ ∑ i, (law (fun _ : E => p)).real (closedBlock (B i)) :=
      measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin (N+1), (1-(p:ℝ))^L := by
      apply Finset.sum_congr rfl
      intro i _
      rw [measureReal_def,law_closedBlock_const p _ (hBfinite i),hBcard,
        ENNReal.toReal_pow,hreal]
    _ = _ := by simp [Nat.cast_add,Nat.cast_one]

end CriticalPercolation.BernoulliProduct
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_FrontierDivergence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma smallFreshBoundary_approx_bound (hl : G.LocallyFinite) (p : unitInterval)
    (X : Set E) (v : V) (M : ℕ) (H : Set (Set E))
    (hH : MeasurableSet[blockSigma X] H) :
    (1-(p:ℝ))^M * (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v M) ≤
      (1 + (1-(p:ℝ))^M) * (G.law p).real (H ∆ G.infiniteEvent v) := by
  have hcost := G.smallFreshBoundary_cost hl p X v M H hH
  have hcover : G.infiniteEvent v ∩ G.smallFreshBoundary X v M ⊆
      (H ∩ G.smallFreshBoundary X v M) ∪ (H ∆ G.infiniteEvent v) := by
    intro ω hω
    by_cases h : ω∈H
    · exact Or.inl ⟨h,hω.2⟩
    · exact Or.inr (Or.inr ⟨hω.1,h⟩)
  have hm := (measureReal_mono hcover (μ := G.law p)).trans
    (measureReal_union_le _ _)
  have he : (G.law p).real (H \ G.infiniteEvent v) ≤
      (G.law p).real (H ∆ G.infiniteEvent v) :=
    measureReal_mono (by intro ω hω; exact Or.inl hω)
  have hr : 0 ≤ (1-(p:ℝ))^M := pow_nonneg (sub_nonneg.mpr p.2.2) _
  nlinarith only [hcost,hm,he,hr]

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_OpenFrontierDivergence
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*} [Countable E]

lemma measurableSet_fewOpenBonds (S : Set E) (N : ℕ) :
    MeasurableSet[blockSigma S] {ω : Set E | (S∩ω).ncard ≤ N} := by
  simpa only [Set.inter_comm,Set.preimage_ofPred_eq,Set.Iic,Function.comp_apply] using
    (measurableSet_Iic.preimage (measurable_ncard.comp (measurable_inter_block S)))
end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma fewOpenFreshBoundary_probability_le (hl : G.LocallyFinite) (p : unitInterval)
    (X : Set E) (v : V) (N L : ℕ) :
    (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N) ≤
      (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v ((N+1)*L)) +
        (N+1 : ℝ)*(1-(p:ℝ))^L := by
  let M := (N+1)*L
  let C : Set (Set E) := {ω | (G.cluster (ω∩X) v).Finite ∧
    M ≤ (G.freshClusterBoundary X v ω).ncard}
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.freshClusterBoundary X v ω)
  let A : Finset E → Set (Set E) := fun S =>
    {ω | (((S : Set E)∩Xᶜ)∩ω).ncard ≤ N}
  have hC : MeasurableSet[blockSigma X] C := by
    have hf : MeasurableSet[blockSigma X] {ω | (G.cluster (ω∩X) v).Finite} := by
      let : MeasurableSpace (Set E) := blockSigma X
      simpa only [Function.comp_apply,Set.not_infinite] using
        (((G.measurable_infinite_cluster v).comp (measurable_inter_block X)).not).setOf
    exact hf.inter (measurableSet_Ici.preimage
      (measurable_ncard.comp (G.measurable_freshClusterBoundary X v)))
  have hd (S : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=S} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.freshClusterBoundary X v) (G.measurable_freshClusterBoundary X v) S
  have hA (S : Finset E) : MeasurableSet[blockSigma Xᶜ] (A S) :=
    blockSigma_mono Set.inter_subset_right _ (measurableSet_fewOpenBonds _ N)
  have he (ω : Set E) (hω : (G.cluster (ω∩X) v).Finite) :
      ((d ω : Set E)∩Xᶜ)=G.freshClusterBoundary X v ω := by
    change (finiteSetChoice (G.freshClusterBoundary X v ω) : Set E)∩Xᶜ = _
    have hf : (G.freshClusterBoundary X v ω).Finite :=
      (G.finite_cutEdges hl hω).subset Set.sdiff_subset
    rw [finiteSetChoice_coe hf]
    exact Set.inter_eq_left.mpr (Set.sdiff_subset_compl _ _)
  let r : ℝ := (N+1 : ℝ)*(1-(p:ℝ))^L
  have hr : 0 ≤ r := mul_nonneg (by positivity) (pow_nonneg (sub_nonneg.mpr p.2.2) _)
  have hb (ω : Set E) (hω : ω∈C) : (BernoulliProduct.law (fun _ : E => p)).real (A (d ω)) ≤ r := by
    change (BernoulliProduct.law (fun _ : E => p)).real
      {τ | (((d ω : Set E)∩Xᶜ)∩τ).ncard ≤ N} ≤ _
    rw [he ω hω.1]
    exact fewOpenBonds_probability_le p _
      ((G.finite_cutEdges hl hω.1).subset Set.sdiff_subset) N L hω.2
  have ht := selected_fresh_bound (fun _ : E => p) X Xᶜ disjoint_compl_right
    d A hd hA C hC r hr hb
  simp only [law_const] at ht
  change (G.law p).real (C∩selectedEvent d A) ≤ r*(G.law p).real C at ht
  have ht' : (G.law p).real (C∩selectedEvent d A) ≤ r :=
    ht.trans ((mul_le_mul_of_nonneg_left measureReal_le_one hr).trans_eq (mul_one r))
  have hsub : G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N ⊆
      (G.infiniteEvent v ∩ G.smallFreshBoundary X v M) ∪ (C∩selectedEvent d A) := by
    intro ω hω
    by_cases h : (G.freshClusterBoundary X v ω).ncard ≤ M
    · exact Or.inl ⟨hω.1,hω.2.1,h⟩
    · right
      refine ⟨⟨hω.2.1,(Nat.le_of_lt (Nat.lt_of_not_ge h))⟩,?_⟩
      change (((d ω : Set E)∩Xᶜ)∩ω).ncard ≤ N
      rw [he ω hω.2.1]
      exact hω.2.2
  exact ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
    (add_le_add_right ht' _)

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

lemma freshExitEvent_of_card (S : Set V) (v : V) (N : ℕ) (ω : Set E)
    (hf : (G.freshClusterBoundary (G.inducedEdges S) v ω∩ω).Finite)
    (hN : N≤(G.freshClusterBoundary (G.inducedEdges S) v ω∩ω).ncard) :
    ω∈G.freshExitEvent S v N := by
  exact ⟨hf.toFinset,by rwa [← Set.ncard_eq_toFinset_card _ hf],
    fun e he => hf.mem_toFinset.mp he⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_FreshExitContinuity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
variable {v : V}

omit [Countable V] [Countable E] in
lemma infinite_sdiff_freshExit_bound (hl : G.LocallyFinite) (p : unitInterval)
    (S : Set V) (v : V) (N : ℕ)
    (hf : ∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges S) v).Finite) :
    G.law p (G.infiniteEvent v\G.freshExitEvent S v N)≤
      G.law p (G.infiniteEvent v∩G.fewOpenFreshBoundary (G.inducedEdges S) v N) := by
  apply measure_mono_ae
  filter_upwards [hf] with ω hω
  rintro ⟨hi,hn⟩
  refine ⟨hi,hω,?_⟩
  by_contra h
  apply hn
  exact G.freshExitEvent_of_card S v N ω
    (((G.finite_cutEdges hl hω).subset Set.sdiff_subset).inter_of_left ω)
    (Nat.le_of_lt (Nat.lt_of_not_ge h))

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_UniformFreshBoundary
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma smallFreshBoundary_uniform_finite
    (hl : G.LocallyFinite) (p : unitInterval) (hp : (p:ℝ)<1)
    (v : V) (M : ℕ) (b : ℝ) (hb : 0<b) :
    ∃ S : Finset E, ∀ X : Set E, (S:Set E)⊆X →
      (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v M)<b := by
  let r : ℝ := (1-(p:ℝ))^M
  have hr : 0 < r := pow_pos (sub_pos.mpr hp) _
  have hδ : 0<b*r/(1+r) := div_pos (mul_pos hb hr) (by linarith)
  obtain ⟨S,H,hH,happrox⟩ := exists_finiteCoordinate_approx (fun _ : E => p)
    (G.measurableSet_infiniteEvent v) (ENNReal.ofReal_pos.mpr hδ)
  have hreal : (G.law p).real (H ∆ G.infiniteEvent v)<b*r/(1+r) := by
    have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr happrox
    simpa only [law_const,ENNReal.toReal_ofReal hδ.le,Measure.real,law] using hh
  refine ⟨S,fun X hX => ?_⟩
  have hh := G.smallFreshBoundary_approx_bound hl p X v M H (blockSigma_mono hX _ hH)
  change r*(G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v M) ≤
    (1+r)*(G.law p).real (H ∆ G.infiniteEvent v) at hh
  have hmul := mul_lt_mul_of_pos_left hreal (show 0<1+r by linarith)
  rw [mul_div_cancel₀ _ (ne_of_gt (show 0<1+r by linarith))] at hmul
  nlinarith only [hh,hmul,hr]

theorem fewOpenFreshBoundary_uniform_finite
    (hl : G.LocallyFinite) (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (v : V) (N : ℕ) (b : ℝ) (hb : 0<b) :
    ∃ S : Finset E, ∀ X : Set E, (S:Set E)⊆X →
      (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N)<b := by
  have hpow : Tendsto (fun L : ℕ => (N+1:ℝ)*(1-(p:ℝ))^L) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (sub_nonneg.mpr p.2.2) (by linarith : 1-(p:ℝ)<1)).const_mul (N+1:ℝ)
  obtain ⟨L,hL⟩ := (hpow.eventually (gt_mem_nhds (half_pos hb))).exists
  obtain ⟨S,hS⟩ := G.smallFreshBoundary_uniform_finite hl p hp1 v ((N+1)*L)
    (b/2) (half_pos hb)
  refine ⟨S,fun X hX => ?_⟩
  have ht := G.fewOpenFreshBoundary_probability_le hl p X v N L
  have hs := hS X hX
  linarith

omit [Countable V] [Countable E] in
lemma Aut.cutEdges_image (φ : G.Aut) (S : Set V) :
    φ.edge '' G.cutEdges S=G.cutEdges (φ.vertex '' S) := by
  ext e
  obtain ⟨e,rfl⟩ := φ.edge.surjective e
  constructor
  · rintro ⟨f,⟨x,y,he,hx,hy⟩,hef⟩
    have hfe : f=e := φ.edge.injective hef
    subst f
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,⟨y,hy,rfl⟩⟩
    · rw [φ.preserves,he,Sym2.map_mk]
    · simpa only [Set.mem_image_equiv,Equiv.symm_apply_apply] using hx
  · rintro ⟨x,y,he,hx,hy⟩
    obtain ⟨a,rfl⟩ := φ.vertex.surjective x
    obtain ⟨b,rfl⟩ := φ.vertex.surjective y
    refine ⟨e,⟨a,b,?_,?_,?_⟩,rfl⟩
    · rw [φ.preserves,←Sym2.map_mk] at he
      exact Sym2.map.injective φ.vertex.injective he
    · simpa only [Set.mem_image_equiv,Equiv.symm_apply_apply] using hx
    · simpa only [Set.mem_image_equiv,Equiv.symm_apply_apply] using hy

omit [Countable V] [Countable E] in
lemma Aut.freshClusterBoundary_image (φ : G.Aut) (X ω : Set E) (v : V) :
    φ.edge '' G.freshClusterBoundary X v ω =
      G.freshClusterBoundary (φ.edge '' X) (φ.vertex v) (φ.edge '' ω) := by
  unfold freshClusterBoundary
  rw [Set.image_sdiff φ.edge.injective,φ.cutEdges_image,φ.cluster_image,
    Set.image_inter φ.edge.injective]

lemma measurableSet_fewOpenFreshBoundary (X : Set E) (v : V) (N : ℕ) :
    MeasurableSet (G.fewOpenFreshBoundary X v N) := by
  have hi : Measurable (fun ω : Set E => ω∩X) :=
    (measurable_inter_block X).mono (blockSigma_le X) le_rfl
  have hf : MeasurableSet {ω : Set E | (G.cluster (ω∩X) v).Finite} := by
    simpa only [Function.comp_apply,Set.not_infinite] using
      (((G.measurable_infinite_cluster v).comp hi).not).setOf
  have hb : Measurable (fun ω : Set E => G.freshClusterBoundary X v ω∩ω) := by
    apply Measurable.of_eval
    intro e
    exact ((measurable_pi_apply e).comp
      ((G.measurable_freshClusterBoundary X v).mono (blockSigma_le X) le_rfl)).and
      (measurable_set_mem e)
  exact hf.inter (measurableSet_Iic.preimage (measurable_ncard.comp hb))

omit [Countable V] [Countable E] in
lemma Aut.fewOpenFreshBoundary_preimage (φ : G.Aut) (X : Set E) (v : V) (N : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹'
      G.fewOpenFreshBoundary (φ.edge '' X) (φ.vertex v) N =
        G.fewOpenFreshBoundary X v N := by
  ext ω
  change ((G.cluster ((φ.edge '' ω)∩(φ.edge '' X)) (φ.vertex v)).Finite ∧ _) ↔ _
  rw [←Set.image_inter φ.edge.injective,←φ.cluster_image,
    ←φ.freshClusterBoundary_image,←Set.image_inter φ.edge.injective,
    Set.finite_image_iff φ.vertex.injective.injOn,
    Set.ncard_image_of_injective _ φ.edge.injective]
  rfl

lemma Aut.infinite_fewOpen_real (φ : G.Aut) (p : unitInterval)
    (X : Set E) (v : V) (N : ℕ) :
    (G.law p).real (G.infiniteEvent (φ.vertex v) ∩
      G.fewOpenFreshBoundary (φ.edge '' X) (φ.vertex v) N) =
    (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [←G.law_map_aut p φ]
  rw [Measure.map_apply (measurable_image_equiv φ.edge)
    ((G.measurableSet_infiniteEvent _).inter (G.measurableSet_fewOpenFreshBoundary _ _ _)),
    Set.preimage_inter,φ.preimage_infiniteEvent,φ.fewOpenFreshBoundary_preimage]

theorem fewOpenFreshBoundary_uniform_ball
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (N : ℕ) (b : ℝ) (hb : 0<b) :
    ∃ R : ℕ, ∀ v : V, ∀ X : Set E, G.inducedEdges (G.vertexBall v R)⊆X →
      (G.law p).real (G.infiniteEvent v ∩ G.fewOpenFreshBoundary X v N)<b := by
  obtain ⟨S,hS,hcover⟩ := hq
  have hh (s : S) : ∃ R : ℕ, ∀ X : Set E, G.inducedEdges (G.vertexBall s.val R)⊆X →
      (G.law p).real (G.infiniteEvent s.val ∩ G.fewOpenFreshBoundary X s.val N)<b := by
    obtain ⟨F,hF⟩ := G.fewOpenFreshBoundary_uniform_finite hl p hp hp1 s N b hb
    obtain ⟨R,hR⟩ := G.finite_bonds_in_ball hc s F.finite_toSet
    exact ⟨R,fun X hX => hF X (hR.trans hX)⟩
  choose R hR using hh
  let := hS.fintype
  let L := ∑ s : S, R s
  refine ⟨L,fun v X hX => ?_⟩
  obtain ⟨s,hs,φ,rfl⟩ := hcover v
  let Y : Set E := φ.edge ⁻¹' X
  have he : φ.edge '' Y=X := Set.image_preimage_eq _ φ.edge.surjective
  rw [←he,φ.infinite_fewOpen_real]
  apply hR ⟨s,hs⟩ Y
  intro e hee
  apply hX
  have hball : G.vertexBall s (R ⟨s,hs⟩)⊆G.vertexBall s L :=
    G.vertexBall_mono s (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (⟨s,hs⟩ : S)))
  have hh := Aut.inducedEdges_map G φ (G.inducedEdges_monotone hball)
    (show φ.edge e∈φ.edge '' G.inducedEdges (G.vertexBall s (R ⟨s,hs⟩)) from ⟨e,hee,rfl⟩)
  rwa [Aut.vertexBall_image] at hh

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

lemma freshExit_in_domain_of_mass (D S : Set V) (v : V) (K : ℝ≥0∞) (N : ℕ)
    (hD : G.weightCeiling v K⊆D) :
    G.freshExitEvent S v N\G.massTailEvent v v K ⊆ G.domainFreshExitEvent D S v N := by
  rintro ω ⟨⟨F,hF,hFω⟩,hm⟩
  have hmass : G.modularMass v (G.cluster ω v)≤K := le_of_not_gt hm
  let X := G.inducedEdges S
  let C := G.inducedEdges (G.weightCeiling v K)
  have hCD : C⊆G.inducedEdges D := G.inducedEdges_monotone hD
  have hC : G.cluster ((ω∩G.inducedEdges D)∩X) v=G.cluster (ω∩X) v := by
    apply Set.Subset.antisymm (G.cluster_mono (Set.inter_subset_inter_left _ Set.inter_subset_left) v)
    have he : G.cluster ((ω∩X)∩C) v=G.cluster (ω∩X) v :=
      G.cluster_eq_with_weightCeiling
        ((G.modularMass_mono v (G.cluster_mono Set.inter_subset_left v)).trans hmass)
    rw [←he]
    apply G.cluster_mono
    intro e he
    exact ⟨⟨he.1.1,hCD he.2⟩,he.1.2⟩
  refine ⟨F,hF,fun e he => ?_⟩
  obtain ⟨⟨x,y,hexy,hx,hy⟩,heX⟩ := (hFω he).1
  have hyC : y∈G.cluster ω v := G.cluster_mono Set.inter_subset_left v hy
  have hxC : x∈G.cluster ω v := by
    by_cases heq : y=x
    · simpa only [heq] using hyC
    · exact hyC.trans (show (G.openGraph ω).Adj y x from by
        apply (SimpleGraph.fromEdgeSet_adj _).mpr
        refine ⟨⟨e,(hFω he).2,?_⟩,heq⟩
        rw [hexy,Sym2.eq_swap]).reachable
  have heD : e∈G.inducedEdges D := by
    apply hCD
    intro z hz
    rw [hexy] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact (G.stabilizerWeight_le_modularMass hxC).trans hmass
    · exact (G.stabilizerWeight_le_modularMass hyC).trans hmass
  refine ⟨⟨⟨x,y,hexy,?_,?_⟩,heX⟩,(hFω he).2,heD⟩
  · change x∉G.cluster ((ω∩G.inducedEdges D)∩X) v
    rwa [hC]
  · change y∈G.cluster ((ω∩G.inducedEdges D)∩X) v
    rwa [hC]

lemma freshExit_same_cluster {S : Set V} {x y : V} {N : ℕ} {ω : Set E}
    (hxy : y∈G.cluster (ω∩G.inducedEdges S) x) :
    ω∈G.freshExitEvent S x N ↔ ω∈G.freshExitEvent S y N := by
  simp only [freshExitEvent,Set.mem_ofPred_eq,freshClusterBoundary]
  rw [G.cluster_eq_of_reachable hxy]

lemma InsideWalk.domainFreshExit_transfer [Countable V] [Countable E]
    (p : unitInterval) {D S : Set V} {x y : V} {L : ℕ} (_ : x∈S) (hy : y∈S)
    (h : G.InsideWalk (D∩S) x y L) (N : ℕ) :
    (p:ℝ)^L*(G.law p).real (G.domainFreshExitEvent D S y N) ≤
      (G.law p).real (G.domainFreshExitEvent D S x N) := by
  obtain ⟨w,hw,hs⟩ := h
  obtain ⟨F,hF,hFS,hcard,hconn⟩ := G.walk_finite_bond_witness w (D∩S) hs
  let A : Set (Set E) := {ω | F⊆ω}
  have hA : IsUpperSet A := fun _ _ hωη hω => hω.trans hωη
  have hAw : HasFiniteOpenWitness A := fun ω hω => ⟨F,hF,hω,Set.Subset.rfl⟩
  have hH := harris_finiteWitness (fun _ : E => p) A (G.domainFreshExitEvent D S y N)
    hA (G.domainFreshExitEvent_upper hy N) hAw (G.domainFreshExitEvent_finiteWitness hy N)
  simp only [law_const] at hH
  have hsub : A∩G.domainFreshExitEvent D S y N ⊆ G.domainFreshExitEvent D S x N := by
    intro ω hω
    apply (G.freshExit_same_cluster (S := S) (x := x) (y := y) (N := N) (ω := ω∩G.inducedEdges D) ?_).mpr hω.2
    apply G.cluster_mono (ω := F) _ x hconn
    intro e he
    refine ⟨⟨hω.1 he,fun z hz => (hFS he z hz).1⟩,fun z hz => (hFS he z hz).2⟩
  have hprob : (p:ℝ)^L≤(G.law p).real A := by
    rw [law,←law_const,real_law_subset p F hF]
    exact pow_le_pow_of_le_one p.2.1 p.2.2 (hcard.trans hw)
  exact (mul_le_mul_of_nonneg_right hprob measureReal_nonneg).trans
    (hH.trans (measureReal_mono hsub))

theorem uniform_domainFreshExit_of_mass
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ θ : ℝ, 0<θ ∧ ∃ K : ℕ, 1≤K ∧ ∀ N : ℕ, ∃ R : ℕ,
      ∀ (D S : Set V) (v : V), G.weightCeiling v K⊆D → G.vertexBall v R⊆S →
      (∀ᵐ ω ∂G.law p, (G.cluster (ω∩G.inducedEdges S) v).Finite) →
      θ<(G.law p).real (G.domainFreshExitEvent D S v N) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨θ,hθ,hroot⟩ := G.uniform_rooted_probability hc hl hq p hper
  obtain ⟨K,hK,htail⟩ := G.uniform_massTail_small hq p hm (θ/4) (by positivity)
  refine ⟨θ/2,by positivity,K,hK,fun N => ?_⟩
  obtain ⟨R,hR⟩ := G.fewOpenFreshBoundary_uniform_ball hc hl hq p hp hp1 N (θ/4) (by positivity)
  refine ⟨R,fun D S v hD hS hf => ?_⟩
  have hfail : (G.law p).real (G.infiniteEvent v\G.freshExitEvent S v N)<θ/4 := by
    exact lt_of_le_of_lt
      (ENNReal.toReal_mono (measure_ne_top _ _)
        (G.infinite_sdiff_freshExit_bound hl p S v N hf))
      (hR v _ (G.inducedEdges_monotone hS))
  have hcover : G.infiniteEvent v⊆
      (G.infiniteEvent v\G.freshExitEvent S v N)∪
        (G.massTailEvent v v K∪G.domainFreshExitEvent D S v N) := by
    intro ω hω
    by_cases he : ω∈G.freshExitEvent S v N
    · right
      by_cases hm : ω∈G.massTailEvent v v K
      · exact Or.inl hm
      · exact Or.inr (G.freshExit_in_domain_of_mass D S v K N hD ⟨he,hm⟩)
    · exact Or.inl ⟨hω,he⟩
  have hprob := (measureReal_mono hcover (μ := G.law p)).trans (measureReal_union_le _ _)
  have hu := measureReal_union_le (G.massTailEvent v v K) (G.domainFreshExitEvent D S v N) (μ := G.law p)
  have hr := hroot v
  have ht := htail v
  linarith

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_LightSliceFrontier
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

lemma finite_lightUpperSlice (o v : V) (ε : ℝ) (hε : 0<ε) (ω : Set E)
    (hm : G.modularMass o (G.cluster ω v) ≠ ∞) :
    (G.cluster ω v ∩ G.modularUpperSlice o ε).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm
    (ε := ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε).ne').subset
  intro x hx
  change ENNReal.ofReal ε ≤ if x∈G.cluster ω v then G.stabilizerWeight o x else 0
  rw [ite_eq_left hx.1]
  exact ENNReal.ofReal_le_ofReal hx.2

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_NestedLayerGeometry
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma walk_support_mem_start_ball {x y : V} (w : G.fullGraph.Walk x y)
    {L : ℕ} (hw : w.length≤L) {z : V} (hz : z∈w.support) : z∈G.vertexBall x L :=
  G.vertexBall_mono x ((w.length_takeUntil_le_length hz).trans hw)
    (G.walk_mem_vertexBall (w.takeUntil z hz))

lemma finite_cluster_outside_safe
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (o : V) (T : ℝ) (hT : 0<T) (R : ℕ) (x : V)
    (hx : x∉G.safeBallDomain o T R) (ω : Set E)
    (hm : G.modularMass x (G.cluster ω x)≠∞) :
    (G.cluster (ω∩G.inducedEdges (G.safeBallDomain o T R)ᶜ) x).Finite := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hS : (G.safeBallDomain o T R)ᶜ⊆G.modularUpperSlice o (T/C) := by
    intro z hz
    change T/C≤G.modularRatio z o
    exact (lt_of_not_ge (fun h : G.modularRatio z o≤T/C => hz (hlow o T h))).le
  have hmass : G.modularMass o (G.cluster ω x)≠∞ :=
    mt (G.modularMass_eq_top_change_base hc hl o x _).mp hm
  apply (G.finite_lightUpperSlice o x (T/C) (div_pos hT hC0) ω hmass).subset
  intro z hz
  exact ⟨G.cluster_mono Set.inter_subset_left x hz,
    hS (G.cluster_induced_subset ω _ hx hz)⟩

lemma exists_layer_gap (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (o : V) (a : ℝ) (ha : 0<a) (L H R : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∀ (T : ℝ), 0<T → ∀ (x : V),
      a*T≤G.modularRatio x o →
      (∀ z∈G.vertexBall x L, z∉G.safeBallDomain o (δ*T) R) ∧
      (∀ y∈G.vertexBall x L, G.vertexBall y H⊆(G.safeBallDomain o (δ*T) R)ᶜ) := by
  obtain ⟨A,hA,hboundA⟩ := G.modularRatio_ball_weight hc hl hq L
  obtain ⟨B,hB,hboundB⟩ := G.modularRatio_ball_weight hc hl hq H
  have hA0 : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hB0 : 0<B := lt_of_lt_of_le zero_lt_one hB
  let δ : ℝ := min (1/2) (a/(2*(A*B)))
  have hδ : 0<δ := lt_min (by norm_num) (div_pos ha (by positivity))
  have hδ1 : δ<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδAB : δ*(A*B)≤a/2 := by
    have hh := (le_div_iff₀ (show 0<2*(A*B) by positivity)).mp (min_le_right (1/2) (a/(2*(A*B))))
    change δ*(2*(A*B))≤a at hh
    nlinarith
  have hδa : δ<a := by
    have hδA : δ≤δ*(A*B) := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
    linarith
  refine ⟨δ,hδ,hδ1,hδa,fun T hT x hx => ?_⟩
  have hlow (z : V) (hz : z∈G.vertexBall x L) :
      δ*T<G.modularRatio z o := by
    have hh := hboundA o x z hz
    have hz0 := G.modularRatio_pos hc hl z o
    have hAδ : δ*A≤a/2 := by nlinarith [mul_nonneg hδ.le hA0.le]
    have ht := mul_le_mul_of_nonneg_right hAδ hT.le
    nlinarith
  refine ⟨fun z hz hs => (not_le_of_gt (hlow z hz)) (G.safeBallDomain_subset o (δ*T) R hs),?_⟩
  intro y hy z hz hs
  have h1 := hboundA o x y hy
  have h2 := hboundB o y z hz
  have h3 := mul_le_mul_of_nonneg_left h2 hA0.le
  have ht := mul_le_mul_of_nonneg_right hδAB hT.le
  have hzlow : δ*T<G.modularRatio z o := by
    by_contra hh
    have hzle : G.modularRatio z o≤δ*T := le_of_not_gt hh
    have hu := mul_le_mul_of_nonneg_left hzle (mul_pos hA0 hB0).le
    nlinarith
  exact (not_le_of_gt hzlow) (G.safeBallDomain_subset o (δ*T) R hs)

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_NestedLayerBlock
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

lemma boundedDomainFreshExit_of_full_mass (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) :
    G.domainFreshExitEvent D S v N\G.massTailEvent v v M ⊆
      G.boundedDomainFreshExitEvent D S v N M := by
  intro ω hω
  exact ⟨hω.1,(G.modularMass_mono v (G.cluster_mono
    (Set.inter_subset_left.trans Set.inter_subset_left) v)).trans (le_of_not_gt hω.2)⟩

lemma real_boundedDomainFreshExit_lower [Countable V] [Countable E]
    (p : unitInterval) (D S : Set V) (v : V) (N : ℕ) (M : ℝ≥0∞) :
    (G.law p).real (G.domainFreshExitEvent D S v N)-
      (G.law p).real (G.massTailEvent v v M) ≤
      (G.law p).real (G.boundedDomainFreshExitEvent D S v N M) := by
  have he := measureReal_sdiff_add_inter (μ := G.law p)
    (s := G.domainFreshExitEvent D S v N) (G.measurableSet_massTailEvent v v M)
  have hi := measureReal_mono (μ := G.law p)
    (s₁ := G.domainFreshExitEvent D S v N ∩ G.massTailEvent v v M) Set.inter_subset_right
  have hd := measureReal_mono (μ := G.law p) (G.boundedDomainFreshExit_of_full_mass D S v N M)
  linarith

theorem uniform_nestedLayer_blocks
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∃ M : ℕ, 1≤M ∧ ∀ a : ℝ, 0<a → ∀ N : ℕ,
      ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R,
        a*T≤G.modularRatio x o →
        θ<(G.law p).real (G.boundedDomainFreshExitEvent
          (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M) := by
  let := G.countable_vertices hc hl
  let := G.countable_bonds hc hl
  obtain ⟨θ,hθ,K,hK,hfront⟩ := G.uniform_domainFreshExit_of_mass hc hl hq p hp hp1 hper hm
  obtain ⟨R,C,hC,hlow,hdesc⟩ := G.safeBallDomain_uniform_descent hc hl hq hu o
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hK0 : (0:ℝ)<K := by exact_mod_cast hK
  obtain ⟨L,hL⟩ := hdesc (1/(C*K)) (by positivity)
  let α : ℝ := (p:ℝ)^L*θ
  have hα : 0<α := mul_pos (pow_pos hp L) hθ
  obtain ⟨M,hM,htail⟩ := G.uniform_massTail_small hq p hm (α/4) (by positivity)
  refine ⟨R,α/2,by positivity,M,hM,fun a ha N => ?_⟩
  obtain ⟨H,hH⟩ := hfront N
  obtain ⟨δ,hδ,hδ1,hδa,hgap⟩ := G.exists_layer_gap hc hl hq o a ha L H R
  refine ⟨δ,hδ,hδ1,hδa,fun T hT x hx hband => ?_⟩
  obtain ⟨y,hy,hw⟩ := hL T x hx
  have hceil : G.weightCeiling y K⊆G.safeBallDomain o T R := by
    intro z hz
    apply hlow T
    have hzy : G.modularRatio z y≤(K:ℝ) := by
      apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0:ℝ)≤K)).mp
      simpa only [weightCeiling,Set.mem_ofPred_eq,stabilizerWeight,ENNReal.ofReal_natCast] using hz
    change G.modularRatio z o≤T/C
    rw [←G.modularRatio_cocycle hc hl z y o]
    have hmul := mul_le_mul_of_nonneg_right hzy (G.modularRatio_pos hc hl y o).le
    have hy' : G.modularRatio y o≤T/(C*K) := by simpa only [one_div,inv_mul_eq_div] using hy
    have ht := mul_le_mul_of_nonneg_left hy' hK0.le
    have he : (K:ℝ)*(T/(C*K))=T/C := by field_simp
    exact hmul.trans (he ▸ ht)
  obtain ⟨w,hlen,hsupport⟩ := hw
  have hyball : y∈G.vertexBall x L := G.vertexBall_mono x hlen (G.walk_mem_vertexBall w)
  have hxb : x∉G.safeBallDomain o (δ*T) R := (hgap T hT x hband).1 x (G.mem_vertexBall_self x L)
  have hyb : y∉G.safeBallDomain o (δ*T) R := (hgap T hT x hband).1 y hyball
  have hw' : G.InsideWalk ((G.safeBallDomain o T R)∩(G.safeBallDomain o (δ*T) R)ᶜ) x y L := by
    refine ⟨w,hlen,fun z hz => ⟨hsupport z hz,?_⟩⟩
    exact (hgap T hT x hband).1 z (G.walk_support_mem_start_ball w hlen hz)
  have hf : ∀ᵐ ω ∂G.law p,
      (G.cluster (ω∩G.inducedEdges (G.safeBallDomain o (δ*T) R)ᶜ) y).Finite := by
    filter_upwards [hm y] with ω hω
    exact G.finite_cluster_outside_safe hc hl hq o (δ*T) (mul_pos hδ hT) R y hyb ω hω
  have hsuccess := hH (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ y
    hceil ((hgap T hT x hband).2 y hyball) hf
  have htrans := hw'.domainFreshExit_transfer G p hxb hyb N
  have hxsuccess : α<(G.law p).real (G.domainFreshExitEvent
      (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N) :=
    (mul_lt_mul_of_pos_left hsuccess (pow_pos hp L)).trans_le htrans
  have hbound := G.real_boundedDomainFreshExit_lower p (G.safeBallDomain o T R)
    (G.safeBallDomain o (δ*T) R)ᶜ x N M
  have ht := htail x
  linarith

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_OpenRay
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

lemma cluster_subset_ball_of_mass
    (S : Set V) (v : V) (hv : v∈S) (ω : Set E) (r : ℝ≥0∞)
    (hr : ∀ x∈S, r≤G.stabilizerWeight v x) (M : ℝ≥0∞) (B : ℕ)
    (hB : M < r*(B+1)) (hm : G.modularMass v (G.cluster (ω∩G.inducedEdges S) v)≤M) :
    G.cluster (ω∩G.inducedEdges S) v⊆G.vertexBall v B := by
  intro x hx
  obtain ⟨w⟩ := hx
  let p := w.toPath
  have hF : (p.val.support.toFinset : Set V)⊆G.cluster (ω∩G.inducedEdges S) v := by
    intro y hy
    exact ⟨p.val.takeUntil y (List.mem_toFinset.mp hy)⟩
  have hmass := G.finset_weight_lower v _ p.val.support.toFinset hF r
    (fun y hy => hr y (G.cluster_induced_subset ω S hv (hF hy)))
  have hcard : p.val.support.toFinset.card=p.val.length+1 := by
    rw [List.toFinset_card_of_nodup p.property.support_nodup,p.val.length_support]
  rw [hcard,Nat.cast_add,Nat.cast_one] at hmass
  have hlen : p.val.length≤B := by
    by_contra hn
    have hnat : B+1≤p.val.length+1 := by omega
    have hle : r*(B+1) ≤ r*(p.val.length+1) := by
      gcongr
      exact_mod_cast (show B≤p.val.length by omega)
    exact (not_le_of_gt hB) (hle.trans (hmass.trans hm))
  have hh := G.openWalk_getVert_ball p.val p.val.length le_rfl
  rw [SimpleGraph.Walk.getVert_length] at hh
  exact G.vertexBall_mono v hlen hh

lemma cluster_eq_of_incident_agree (v : V) (ω η : Set E)
    (h : ∀ e∈G.incidentEdges (G.cluster ω v), e∈ω ↔ e∈η) :
    G.cluster η v=G.cluster ω v := by
  have hh := G.roots_eq_of_incident (S := {v}) (U := G.cluster ω v)
    (ω := ω) (ω' := η)
    (by simp only [ClusterDeletion.roots_singleton,ClusterDeletion.component,cluster]) h
  simpa only [ClusterDeletion.roots_singleton,ClusterDeletion.component,cluster] using hh

lemma freshClusterBoundary_subset_incident (X : Set E) (v : V) (ω : Set E) :
    G.freshClusterBoundary X v ω⊆G.incidentEdges (G.cluster (ω∩X) v) := by
  rintro e ⟨⟨x,y,he,_,hy⟩,_⟩
  exact ⟨y,hy,by rw [he]; simp⟩

lemma boundedDomainFreshExit_of_agree
    (D S : Set V) (v : V) (hv : v∈S) (r M : ℝ≥0∞) (B N : ℕ)
    (hr : ∀ x∈S, r≤G.stabilizerWeight v x) (hB : M < r*(B+1))
    (ω η : Set E)
    (hagree : ∀ e∈G.incidentEdges (G.vertexBall v B), e∈ω ↔ e∈η)
    (hω : ω∈G.boundedDomainFreshExitEvent D S v N M) :
    η∈G.boundedDomainFreshExitEvent D S v N M := by
  have hball := G.cluster_subset_ball_of_mass S v hv (ω∩G.inducedEdges D) r hr M B hB hω.2
  have hinc := G.incidentEdges_mono hball
  have heq : G.cluster ((η∩G.inducedEdges D)∩G.inducedEdges S) v =
      G.cluster ((ω∩G.inducedEdges D)∩G.inducedEdges S) v := by
    apply G.cluster_eq_of_incident_agree
    intro e he
    simp only [Set.mem_inter_iff,hagree e (hinc he)]
  refine ⟨?_,?_⟩
  swap
  · change G.modularMass v (G.cluster ((η∩G.inducedEdges D)∩G.inducedEdges S) v)≤M
    rw [heq]
    exact hω.2
  obtain ⟨F,hF,hFω⟩ := hω.1
  refine ⟨F,hF,fun e he => ?_⟩
  have hfresh := (hFω he).1
  have hei := G.freshClusterBoundary_subset_incident (G.inducedEdges S) v
    (ω∩G.inducedEdges D) hfresh
  refine ⟨?_,(hagree e (hinc hei)).mp (hFω he).2.1,(hFω he).2.2⟩
  simpa only [freshClusterBoundary,heq] using hfresh

lemma dependsOn_boundedDomainFreshExit
    (D S : Set V) (v : V) (hv : v∈S) (r M : ℝ≥0∞) (B N : ℕ)
    (hr : ∀ x∈S, r≤G.stabilizerWeight v x) (hB : M < r*(B+1)) :
    DependsOn (fun ω : Set E => ω∈G.boundedDomainFreshExitEvent D S v N M)
      (G.incidentEdges (G.vertexBall v B)) := by
  intro ω η h
  apply propext
  exact ⟨G.boundedDomainFreshExit_of_agree D S v hv r M B N hr hB ω η
    (fun e he => (h e he).to_iff),
    G.boundedDomainFreshExit_of_agree D S v hv r M B N hr hB η ω
    (fun e he => (h e he).symm.to_iff)⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_UniformLocalContinuity
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma event_eq_restrict_of_dependsOn (A : Set (Set E)) (F : Set E)
    (hA : DependsOn (fun ω : Set E => ω∈A) F) :
    A={ω | F∩ω∈A} := by
  ext ω
  exact (hA (x := ω) (y := (show Set E from F∩ω)) (fun e he =>
    propext (show e∈ω ↔ e∈F∩ω from by simp [he]))).to_iff

lemma measurableSet_of_finite_dependsOn (A : Set (Set E)) (F : Set E) (hF : F.Finite)
    (hA : DependsOn (fun ω : Set E => ω∈A) F) : MeasurableSet A := by
  rw [event_eq_restrict_of_dependsOn A F hA]
  exact measurableSet_restrict F hF A

lemma eventually_uniform_finite_events (p : unitInterval) (F : Set E) (hF : F.Finite)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p, ∀ A : Set (Set E), DependsOn (fun ω : Set E => ω∈A) F →
      |(law (fun _ : E => q)).real A-(law (fun _ : E => p)).real A|<ε := by
  let := hF.fintype
  have hh : ∀ᶠ q in 𝓝 p, ∀ B : Set (Set F),
      |(law (fun _ : F => q)).real B-(law (fun _ : F => p)).real B|<ε := by
    apply Filter.eventually_all.mpr
    intro B
    have hc : ContinuousAt (fun q : unitInterval =>
        |(law (fun _ : F => q)).real B-(law (fun _ : F => p)).real B|) p :=
      ((continuous_real_law_finite B).sub continuous_const).abs.continuousAt
    exact hc.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [hh] with q hq
  intro A hA
  have he (t : unitInterval) : (law (fun _ : E => t)).real A=
      (law (fun _ : F => t)).real {s : Set F | Subtype.val '' s∈A} := by
    conv_lhs => rw [event_eq_restrict_of_dependsOn A F hA]
    exact real_law_restrict t F hF A
  rw [he q,he p]
  exact hq _

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
open BernoulliProduct

lemma Aut.incidentEdges_image (φ : G.Aut) (S : Set V) :
    φ.edge '' G.incidentEdges S=G.incidentEdges (φ.vertex '' S) := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right]
  constructor
  · rintro ⟨v,hv,hve⟩
    exact ⟨φ.vertex v,⟨v,hv,rfl⟩,by rw [φ.preserves]; exact Sym2.mem_map.mpr ⟨v,hve,rfl⟩⟩
  · rintro ⟨u,⟨v,hv,rfl⟩,hue⟩
    refine ⟨v,hv,?_⟩
    rw [φ.preserves] at hue
    obtain ⟨w,hw,heq⟩ := Sym2.mem_map.mp hue
    simpa only [φ.vertex.injective heq] using hw

lemma dependsOn_preimage_aut (φ : G.Aut) (A : Set (Set E)) (F : Set E)
    (hA : DependsOn (fun ω : Set E => ω∈A) (φ.edge '' F)) :
    DependsOn (fun ω : Set E => φ.edge '' ω∈A) F := by
  intro ω η h
  apply hA
  rintro e ⟨f,hf,rfl⟩
  apply propext
  change φ.edge f∈φ.edge '' ω ↔ φ.edge f∈φ.edge '' η
  constructor
  · rintro ⟨a,ha,heq⟩
    have heq' : a=f := φ.edge.injective heq
    subst a
    exact ⟨f,(h f hf).to_iff.mp ha,rfl⟩
  · rintro ⟨a,ha,heq⟩
    have heq' : a=f := φ.edge.injective heq
    subst a
    exact ⟨f,(h f hf).to_iff.mpr ha,rfl⟩

lemma eventually_uniform_local_events
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (p : unitInterval)
    (B : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ q in 𝓝 p, ∀ v : V, ∀ A : Set (Set E),
      DependsOn (fun ω : Set E => ω∈A) (G.incidentEdges (G.vertexBall v B)) →
      |(G.law q).real A-(G.law p).real A|<ε := by
  obtain ⟨S,hS,horbit⟩ := hq
  have hh : ∀ᶠ q in 𝓝 p, ∀ v∈S, ∀ A : Set (Set E),
      DependsOn (fun ω : Set E => ω∈A) (G.incidentEdges (G.vertexBall v B)) →
      |(G.law q).real A-(G.law p).real A|<ε := by
    apply hS.eventually_all.mpr
    intro v hv
    simpa only [law,←law_const] using eventually_uniform_finite_events p
      (G.incidentEdges (G.vertexBall v B)) (G.finite_incident hl (G.vertexBall_finite hl v B)) ε hε
  filter_upwards [hh] with q hq
  intro v A hA
  obtain ⟨s,hs,φ,rfl⟩ := horbit v
  let A' : Set (Set E) := (fun ω : Set E => φ.edge '' ω) ⁻¹' A
  have hA' : DependsOn (fun ω : Set E => ω∈A') (G.incidentEdges (G.vertexBall s B)) := by
    apply G.dependsOn_preimage_aut φ
    simpa only [Aut.incidentEdges_image,Aut.vertexBall_image] using hA
  have hmeas : MeasurableSet A := measurableSet_of_finite_dependsOn A _
    (G.finite_incident hl (G.vertexBall_finite hl _ B)) hA
  have he (t : unitInterval) : (G.law t).real A=(G.law t).real A' := by
    simp only [Measure.real]
    conv_lhs => rw [←G.law_map_aut t φ,Measure.map_apply (measurable_image_equiv φ.edge) hmeas]
  rw [he q,he p]
  exact hq s hs A' hA'

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_LayerLocality
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
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

lemma layer_weight_lower
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (R : ℕ) (C : ℝ) (_hC : 0<C)
    (hlow : ∀ T : ℝ, {z | G.modularRatio z o≤T/C}⊆G.safeBallDomain o T R)
    (T δ : ℝ) (hT : 0<T) (x : V) (hx : x∈G.safeBallDomain o T R)
    (z : V) (hz : z∉G.safeBallDomain o (δ*T) R) :
    δ/C<G.modularRatio z x := by
  have hzlow : δ*T/C<G.modularRatio z o := lt_of_not_ge (fun hh => hz (hlow (δ*T) hh))
  have hxup := G.safeBallDomain_subset o T R hx
  have hmul : (δ/C)*T<G.modularRatio z x*T := by
    calc
      _ = δ*T/C := by ring
      _ < G.modularRatio z o := hzlow
      _ = G.modularRatio z x*G.modularRatio x o := (G.modularRatio_cocycle hc hl z x o).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hxup (G.modularRatio_pos hc hl z x).le
  exact lt_of_mul_lt_mul_right hmul hT.le

lemma uniform_nestedLayer_locality (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (o : V) (R : ℕ) (δ : ℝ) (hδ : 0<δ) (M : ℕ) :
    ∃ B : ℕ, ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R,
      x∉G.safeBallDomain o (δ*T) R → ∀ N : ℕ,
      DependsOn (fun ω : Set E => ω∈G.boundedDomainFreshExitEvent
        (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M)
        (G.incidentEdges (G.vertexBall x B)) := by
  obtain ⟨C,hC,hlow⟩ := G.safeBallDomain_low_inclusion hc hl hq R
  have hC0 : 0<C := lt_of_lt_of_le zero_lt_one hC
  have hr : 0<δ/C := div_pos hδ hC0
  obtain ⟨B,hB⟩ := exists_nat_gt ((M:ℝ)/(δ/C))
  have hBM : (M:ℝ)<(δ/C)*((B:ℝ)+1) := by
    have hh := (div_lt_iff₀ hr).mp hB
    nlinarith
  have hBM' : (M:ℝ≥0∞)<ENNReal.ofReal (δ/C)*(B+1) := by
    rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_natCast,←ENNReal.ofReal_one,
      ←ENNReal.ofReal_add (Nat.cast_nonneg B) zero_le_one,←ENNReal.ofReal_mul hr.le]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hBM
  refine ⟨B,fun T hT x hx hx' N => ?_⟩
  apply G.dependsOn_boundedDomainFreshExit _ _ x hx' (ENNReal.ofReal (δ/C)) M B N _ hBM'
  intro z hz
  exact ENNReal.ofReal_le_ofReal (G.layer_weight_lower hc hl o R C hC0
    (fun T => hlow o T) T δ hT x hx z hz).le

theorem uniform_lower_nestedLayer_blocks_oai
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∃ M : ℕ, 1≤M ∧ ∀ a : ℝ, 0<a → ∀ N : ℕ,
      ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∃ q : unitInterval, 0<(q:ℝ) ∧ q<p ∧
      ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R, a*T≤G.modularRatio x o →
        θ<(G.law q).real (G.boundedDomainFreshExitEvent
          (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M) := by
  obtain ⟨R,θ,hθ,M,hM,hblock⟩ := G.uniform_nestedLayer_blocks hc hl hq hu o p hp hp1 hper hm
  refine ⟨R,θ/2,by positivity,M,hM,fun a ha N => ?_⟩
  obtain ⟨δ,hδ,hδ1,hδa,hgood⟩ := hblock a ha N
  obtain ⟨B,hB⟩ := G.uniform_nestedLayer_locality hc hl hq o R δ hδ M
  have hcontinuity := G.eventually_uniform_local_events hl hq p B (θ/2) (by positivity)
  have hpos : ∀ᶠ q : unitInterval in 𝓝 p, 0<(q:ℝ) :=
    continuous_subtype_val.continuousAt.eventually (lt_mem_nhds hp)
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨0,hp⟩
  obtain ⟨q,hqgood,hqpos,hqp⟩ := ((hcontinuity.filter_mono nhdsWithin_le_nhds).and
    ((hpos.filter_mono nhdsWithin_le_nhds).and
      (show ∀ᶠ q in 𝓝[<] p, q<p from self_mem_nhdsWithin))).exists
  refine ⟨δ,hδ,hδ1,hδa,q,hqpos,hqp,fun T hT x hx hband => ?_⟩
  have hx' : x∉G.safeBallDomain o (δ*T) R := by
    intro hh
    have hh' : G.modularRatio x o≤δ*T := G.safeBallDomain_subset o (δ*T) R hh
    nlinarith
  have hc' := hqgood x _ (hB T hT x hx hx' N)
  have hg := hgood T hT x hx hband
  rw [abs_lt] at hc'
  linarith [hc'.1]

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_oai.{u_1, u_2}
