-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:48:58.188397+00:00
-- url     : https://prove2.me/submissions/17d53803-7243-4f3f-8104-534a9d2d8721

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_restricted_interpolation_measure_bs
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_subexponential_adjacent_bound_bs

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

namespace ClusterDeletion
variable {V : Type*}

lemma delete_le (H : SimpleGraph V) (U : Set V) : delete H U ≤ H :=
  fun _ _ h => h.1

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

lemma component_self (H : SimpleGraph V) (s : V) : s ∈ component H s :=
  SimpleGraph.Reachable.refl s

lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]

lemma component_eq_of_mem {H : SimpleGraph V} {s t : V}
    (h : t ∈ component H s) : component H t = component H s := by
  ext v
  exact ⟨fun hv => h.trans hv, fun hv => h.symm.trans hv⟩

lemma component_delete_component (H : SimpleGraph V) (s t : V)
    (h : t ∉ component H s) :
    component (delete H (component H s)) t = component H t := by
  simpa only [roots_singleton] using
    (delete_roots_component H {s} t (by simpa only [roots_singleton] using h))

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ExpectedCluster
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

end CriticalPercolation.BondGraph

open scoped BigOperators

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

lemma clusterTail_antitone (o : V) : Antitone (G.clusterTail o) := by
  rintro m n h ω ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω, h.trans hn⟩

end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_HitEventUpperSet
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InterpolationUniform
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ExhaustionEvents
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_DeletedTailGeometry
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
      · simp only [hs,if_false]
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteNearbyPair
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InfiniteInterpolation
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
    obtain ⟨j,hjd,hjp,hjl⟩ := G.restricted_interpolation_measure_bs (K n) (K.finite n) d x hd p hp
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_InfiniteNearbyPair
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_MinimalPair
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_MinimalInterpolation
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_AdjacentLog
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SuperpolynomialAlgebra
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SuperpolynomialRadius
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Growth_SuperpolynomialContradiction
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

lemma eventually_no_superpolynomial_band_bs_oai
    (hconnected : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hsub : G.SubexponentialGrowth)
    (hsuper : G.SuperpolynomialGrowth) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ≤1)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ s : ℕ in atTop, ∀ (p : unitInterval) (z : V), ε≤p → ε≤1-(p:ℝ) →
      (Real.log s)⁻¹^2 ≤ (G.law p).real (G.clusterBand z s) →
      (∀ v, θ/2≤(G.law p).real (G.clusterTail v s)) → False := by
  obtain ⟨A,hA,hAbound⟩ := G.subexponential_adjacent_bound_bs hconnected hlocal hquasi hsub
  obtain ⟨D,_,hD⟩ := G.uniform_incident_bound hquasi
  let c := θ^2/8
  have hc : 0 < c := by dsimp [c]; positivity
  have hcθ : c≤θ/4 := by dsimp [c]; nlinarith
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
    exact hupper.trans (mul_le_mul_of_nonneg_left (by dsimp [f] at *; linarith) hC.le)
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

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.eventually_no_superpolynomial_band_bs_oai.{u_1, u_2}
