-- Prove2me | solution 1 for OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:13:23.691329+00:00
-- url     : https://prove2.me/submissions/6a851fbb-c963-4a48-94f1-25a1c30e47c0

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

end BondGraph

namespace ClusterDeletion
variable {V : Type*}

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

end ClusterDeletion
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

lemma expect_comp {B : Type*} [Fintype B] [DecidableEq B]
    (w : E → A → ℝ) (φ : (E → A) → B) (f : B → ℝ) :
    expect w (fun ω => f (φ ω)) = ∑ b, distribution w φ b * f b := by
  classical
  simp only [distribution, ← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  simp

lemma distribution_nonneg {B : Type*} [DecidableEq B]
    {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    (φ : (E → A) → B) (b : B) : 0 ≤ distribution w φ b :=
  expect_nonneg hw fun _ => by split_ifs <;> norm_num

lemma distribution_mass {B : Type*} [Fintype B] [DecidableEq B]
    (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (φ : (E → A) → B) : ∑ b, distribution w φ b = 1 := by
  simpa only [mul_one] using (expect_comp w φ (fun _ => 1)).symm.trans (expect_const w hw 1)

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

lemma clusterObject_mono {ω ω' : Set E} (h : ω ⊆ ω') (S : Set V) :
    G.clusterObject ω S ≤ G.clusterObject ω' S := by
  have hr := roots_mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono (f := G.ends) h)) S
  exact ⟨hr, fun _ he => ⟨h he.1, G.incidentEdges_mono hr he.2⟩⟩

lemma eraseVertices_mono {ω ω' : Set E} (h : ω ⊆ ω') (U : Set V) :
    G.eraseVertices ω U ⊆ G.eraseVertices ω' U :=
  fun _ he => ⟨h he.1, he.2⟩

lemma eraseVertices_antitone {U U' : Set V} (h : U ⊆ U') (ω : Set E) :
    G.eraseVertices ω U' ⊆ G.eraseVertices ω U :=
  fun _ he => ⟨he.1, fun hh => he.2 (G.incidentEdges_mono h hh)⟩

lemma openGraph_eraseVertices (ω : Set E) (U : Set V) :
    G.openGraph (G.eraseVertices ω U) = delete (G.openGraph ω) U := by
  ext v w
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image,
    eraseVertices, Set.mem_sdiff, delete]
  constructor
  · rintro ⟨⟨e, ⟨he, hU⟩, heq⟩, hne⟩
    refine ⟨⟨⟨e, he, heq⟩, hne⟩, ?_, ?_⟩
    · intro hv
      exact hU ⟨v, hv, by simp [heq]⟩
    · intro hw
      exact hU ⟨w, hw, by simp [heq]⟩
  · rintro ⟨⟨⟨e, he, heq⟩, hne⟩, hv, hw⟩
    refine ⟨⟨e, ⟨he, ?_⟩, heq⟩, hne⟩
    rintro ⟨t, ht, hte⟩
    rw [heq] at hte
    rcases (by simpa using hte : t = v ∨ t = w) with rfl | rfl
    · exact hv ht
    · exact hw ht

lemma eraseVertices_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => G.eraseVertices ω U) (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext e
  change (ω e ∧ e ∉ G.incidentEdges U) ↔ (ω' e ∧ e ∉ G.incidentEdges U)
  by_cases he : e ∈ G.incidentEdges U
  · simp [he]
  · rw [(hω e he).to_iff]

lemma roots_disjoint_symm (ω : Set E) (A B : Set V) :
    Disjoint (roots (G.openGraph ω) A) B ↔ Disjoint (roots (G.openGraph ω) B) A := by
  simp only [Set.disjoint_left]
  constructor
  · rintro h a ⟨b, hb, hba⟩ ha
    exact h ⟨a, ha, hba.symm⟩ hb
  · rintro h b ⟨a, ha, hab⟩ hb
    exact h ⟨b, hb, hab.symm⟩ ha

lemma roots_disjoint_roots (ω : Set E) {A B : Set V}
    (h : Disjoint (roots (G.openGraph ω) A) B) :
    Disjoint (roots (G.openGraph ω) A) (roots (G.openGraph ω) B) := by
  rw [Set.disjoint_left] at h ⊢
  rintro v ⟨a, ha, hav⟩ ⟨b, hb, hbv⟩
  exact h ⟨a, ha, hav.trans hbv.symm⟩ hb

lemma roots_erase_roots (ω : Set E) {A B : Set V}
    (h : Disjoint (roots (G.openGraph ω) A) B) :
    roots (G.openGraph (G.eraseVertices ω (roots (G.openGraph ω) A))) B =
      roots (G.openGraph ω) B := by
  rw [G.openGraph_eraseVertices]
  ext v
  constructor
  · exact fun hv => roots_mono (delete_le _ _) _ hv
  · rintro ⟨b, hb, hbv⟩
    refine ⟨b, hb, ?_⟩
    change v ∈ component (delete (G.openGraph ω) (roots (G.openGraph ω) A)) b
    rw [delete_roots_component _ _ _ (fun hh => Set.disjoint_left.mp h hh hb)]
    exact hbv

lemma openBond_roots {ω : Set E} {S : Set V} {e : E} (he : e ∈ ω)
    {v w : V} (hv : v ∈ G.ends e) (hw : w ∈ G.ends e)
    (hr : v ∈ roots (G.openGraph ω) S) : w ∈ roots (G.openGraph ω) S := by
  by_cases hvw : v = w
  · simpa [← hvw] using hr
  · have heq : G.ends e = s(v,w) := Sym2.eq_of_ne_mem hvw hv hw (by simp) (by simp)
    exact roots_closed hr ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e, he, heq⟩, hvw⟩)

lemma clusterObject_erase_other (ω : Set E) {A B : Set V}
    (h : Disjoint (G.clusterObject ω A).1 B) :
    G.clusterObject (G.eraseVertices ω (G.clusterObject ω A).1) B = G.clusterObject ω B := by
  have hr := G.roots_erase_roots ω h
  apply Prod.ext hr
  change G.eraseVertices ω (roots (G.openGraph ω) A) ∩
    G.incidentEdges (roots (G.openGraph (G.eraseVertices ω (roots (G.openGraph ω) A))) B) =
    ω ∩ G.incidentEdges (roots (G.openGraph ω) B)
  rw [hr]
  ext e
  constructor
  · exact fun hh => ⟨hh.1.1, hh.2⟩
  · rintro ⟨he, hi⟩
    refine ⟨⟨he, ?_⟩, hi⟩
    rintro ⟨a, ha, hae⟩
    obtain ⟨b, hb, hbe⟩ := hi
    exact Set.disjoint_left.mp (G.roots_disjoint_roots ω h) ha
      (G.openBond_roots he hbe hae hb)

lemma clusterObject_exposure [Fintype V] [Fintype E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (F : ClusterObject V E → Set E → ℝ) :
    expect w (fun ω => F (G.clusterObject ω S)
      (G.eraseVertices ω (G.clusterObject ω S).1)) =
    expect w (fun ω => expect w (fun ω' => F (G.clusterObject ω S)
      (G.eraseVertices ω' (G.clusterObject ω S).1))) := by
  classical
  exact expect_exposure w hw (fun ω => G.clusterObject ω S)
    (fun C => G.incidentEdges C.1) (G.dependsOn_exact_clusterObject S)
    (fun C ω => F C (G.eraseVertices ω C.1))
    (fun C _ _ hω => congrArg (F C) (G.eraseVertices_dependsOn C.1 hω))

lemma clusterObject_avoidance_exposure [Fintype V] [Fintype E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (A B : Set V) (F : ClusterObject V E → ClusterObject V E → ℝ) :
    expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      F (G.clusterObject ω A) (G.clusterObject ω B) else 0) =
    expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      expect w (fun ω' => F (G.clusterObject ω A)
        (G.clusterObject (G.eraseVertices ω' (G.clusterObject ω A).1) B)) else 0) := by
  classical
  have he := G.clusterObject_exposure w hw A
    (fun C ω => if Disjoint C.1 B then F C (G.clusterObject ω B) else 0)
  have hl : (fun ω : E → Prop => if Disjoint (G.clusterObject ω A).1 B then
      F (G.clusterObject ω A)
        (G.clusterObject (G.eraseVertices ω (G.clusterObject ω A).1) B) else 0) =
      (fun ω => if Disjoint (G.clusterObject ω A).1 B then
        F (G.clusterObject ω A) (G.clusterObject ω B) else 0) := by
    funext ω
    split_ifs with h
    · rw [G.clusterObject_erase_other ω h]
    · rfl
  rw [hl] at he
  refine he.trans ?_
  congr 1
  funext ω
  split_ifs <;> simp [expect_zero]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_FiniteMarkovAvg
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Associated
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

namespace CriticalPercolation.FiniteMarkov
open Filter
open scoped Topology

variable {X : Type*} [Fintype X] [Preorder X]

omit [Preorder X] in
lemma avg_neg (μ : X → ℝ) (f : X → ℝ) :
    avg μ (fun x => -f x) = -avg μ f := by
  simp [avg, Finset.sum_neg_distrib]

lemma Associated.antitone {μ : X → ℝ} (h : Associated μ)
    (f g : X → ℝ) (hf : Antitone f) (hg : Antitone g) :
    avg μ f * avg μ g ≤ avg μ (fun x => f x * g x) := by
  have hh := h (fun x => -f x) (fun x => -g x) hf.neg hg.neg
  simpa only [avg_neg, neg_mul_neg] using hh

lemma Associated.cross {μ : X → ℝ} (h : Associated μ)
    (f g : X → ℝ) (hf : Monotone f) (hg : Antitone g) :
    avg μ (fun x => f x * g x) ≤ avg μ f * avg μ g := by
  have hh := h f (fun x => -g x) hf hg.neg
  simp only [avg_neg, mul_neg] at hh
  linarith

omit [Preorder X] in
lemma step_mono {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    {f g : X → ℝ} (hfg : ∀ x, f x ≤ g x) (x : X) :
    step K f x ≤ step K g x := avg_mono (hK x) hfg

lemma association_halfstep {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y)
    (hKa : ∀ x, Associated (K x)) (hLa : ∀ x, Associated (L x))
    (hLa' : ∀ f : X → ℝ, Monotone f → Antitone (step L f))
    (f g : X → ℝ) (hf : Monotone f) (hg : Monotone g) (x : X) :
    step K (step L f) x * step K (step L g) x ≤
      step K (step L (fun y => f y * g y)) x := by
  calc
    _ ≤ step K (fun y => step L f y * step L g y) x :=
      (hKa x).antitone _ _ (hLa' f hf) (hLa' g hg)
    _ ≤ _ := step_mono hK (fun y => hLa y f g hf hg) x

lemma step_antitone_of_neg {K : X → X → ℝ}
    (hK : ∀ f : X → ℝ, Monotone f → Antitone (step K f))
    {f : X → ℝ} (hf : Antitone f) : Monotone (step K f) := by
  have hh := (hK (fun x => -f x) hf.neg).neg
  change Monotone (fun x => avg (K x) f)
  simpa only [step, avg_neg, neg_neg] using hh

lemma iterate_association {K : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y)
    (hKa : ∀ x, Associated (K x))
    (hmono : ∀ f : X → ℝ, Monotone f → Monotone (step K f))
    (f g : X → ℝ) (hf : Monotone f) (hg : Monotone g) (n : ℕ) (x : X) :
    (step K)^[n] f x * (step K)^[n] g x ≤
      (step K)^[n] (fun y => f y * g y) x := by
  have hit (f : X → ℝ) (hf : Monotone f) (n : ℕ) : Monotone ((step K)^[n] f) := by
    induction n with
    | zero => exact hf
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hmono _ ih
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    calc
      _ ≤ step K (fun y => (step K)^[n] f y * (step K)^[n] g y) x :=
        hKa x _ _ (hit f hf n) (hit g hg n)
      _ ≤ _ := step_mono hK (fun y => ih y) x

omit [Preorder X] in
lemma step_compose (K L : X → X → ℝ) (f : X → ℝ) :
    step (compose K L) f = step K (step L f) := by
  funext x
  simp only [step, avg, compose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Preorder X] in
lemma compose_nonneg {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hL : ∀ x y, 0 ≤ L x y) (x z : X) :
    0 ≤ compose K L x z := Finset.sum_nonneg fun y _ => mul_nonneg (hK x y) (hL y z)

omit [Preorder X] in
lemma compose_mass {K L : X → X → ℝ}
    (hK : ∀ x, ∑ y, K x y = 1) (hL : ∀ x, ∑ y, L x y = 1) (x : X) :
    ∑ z, compose K L x z = 1 := by
  simp only [compose]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hL, mul_one, hK]

omit [Preorder X] in
lemma compose_minorization {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hKm : ∀ x, ∑ y, K x y = 1)
    {a : ℝ} {z : X} (haL : ∀ x, a ≤ L x z) (x : X) :
    a ≤ compose K L x z := by
  calc
    a = ∑ y, K x y * a := by rw [← Finset.sum_mul, hKm, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (haL y) (hK x y)

lemma compose_associated {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y)
    (hKa : ∀ x, Associated (K x)) (hLa : ∀ x, Associated (L x))
    (hLa' : ∀ f : X → ℝ, Monotone f → Antitone (step L f)) (x : X) :
    Associated (compose K L x) := by
  intro f g hf hg
  change step (compose K L) f x * step (compose K L) g x ≤
    step (compose K L) (fun y => f y * g y) x
  simp only [step_compose]
  exact association_halfstep hK hKa hLa hLa' f g hf hg x

lemma compose_monotone {K L : X → X → ℝ}
    (hKa' : ∀ f : X → ℝ, Monotone f → Antitone (step K f))
    (hLa' : ∀ f : X → ℝ, Monotone f → Antitone (step L f))
    {f : X → ℝ} (hf : Monotone f) : Monotone (step (compose K L) f) := by
  rw [step_compose]
  exact step_antitone_of_neg hKa' (hLa' f hf)

theorem stationary_associated {K : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hmass : ∀ x, ∑ y, K x y = 1)
    (hKa : ∀ x, Associated (K x))
    (hmono : ∀ f : X → ℝ, Monotone f → Monotone (step K f))
    {a : ℝ} {z : X} (ha : 0 < a) (ha_one : a ≤ 1) (haK : ∀ x, a ≤ K x z)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) : Associated μ := by
  intro f g hf hg
  have hf' := tendsto_iterate hK hmass ha ha_one haK μ hμ hμmass hstat f z
  have hg' := tendsto_iterate hK hmass ha ha_one haK μ hμ hμmass hstat g z
  have hfg' := tendsto_iterate hK hmass ha ha_one haK μ hμ hμmass hstat
    (fun x => f x * g x) z
  exact le_of_tendsto_of_tendsto (hf'.mul hg') hfg'
    (Filter.Eventually.of_forall fun n => iterate_association hK hKa hmono f g hf hg n z)

end CriticalPercolation.FiniteMarkov

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ExpectMulReal
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

lemma expect_mul_ge_real (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf : Monotone f) (hg : Monotone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω * g ω) := by
  classical
  let l := Finset.univ.inf' Finset.univ_nonempty f
  let k := Finset.univ.inf' Finset.univ_nonempty g
  have hb := expect_mul_ge w hw hpos (fun ω => f ω-l) (fun ω => g ω-k)
    (fun ω => sub_nonneg.mpr (Finset.inf'_le _ (Finset.mem_univ ω)))
    (fun ω => sub_nonneg.mpr (Finset.inf'_le _ (Finset.mem_univ ω)))
    (fun _ _ h => sub_le_sub_right (hf h) l) (fun _ _ h => sub_le_sub_right (hg h) k)
  have he : (fun ω => (f ω-l)*(g ω-k)) =
      (fun ω => f ω*g ω - l*g ω - k*f ω + l*k) := by funext ω; ring
  rw [he, expect_sub, expect_sub, expect_const w hw l, expect_const w hw k,
    expect_add, expect_sub, expect_sub, expect_const_mul, expect_const_mul,
    expect_const w hw (l*k)] at hb
  nlinarith

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ObjectKernel
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
open ClusterDeletion FiniteProduct FiniteMarkov
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma step_objectKernel (w : E → Prop → ℝ) (S : Set V) (f : ClusterObject V E → ℝ)
    (C : ClusterObject V E) :
    step (G.objectKernel w S) f C =
      expect w (fun ω => f (G.clusterObject (G.eraseVertices ω C.1) S)) := by
  exact (expect_comp w _ f).symm

omit [Fintype V] in
lemma objectKernel_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (S : Set V) (C D : ClusterObject V E) : 0 ≤ G.objectKernel w S C D :=
  distribution_nonneg hp _ D

lemma objectKernel_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (C : ClusterObject V E) : ∑ D, G.objectKernel w S C D = 1 :=
  distribution_mass w hw _

lemma objectKernel_antitone (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (S : Set V) (f : ClusterObject V E → ℝ) (hf : Monotone f) :
    Antitone (step (G.objectKernel w S) f) := by
  intro C D hCD
  simp only [G.step_objectKernel]
  apply expect_mono hp
  intro ω
  exact hf (G.clusterObject_mono (G.eraseVertices_antitone hCD.1 ω) S)

lemma objectKernel_associated (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (S : Set V) (C : ClusterObject V E) :
    Associated (G.objectKernel w S C) := by
  intro f g hf hg
  change step (G.objectKernel w S) f C * step (G.objectKernel w S) g C ≤
    step (G.objectKernel w S) (fun D => f D * g D) C
  simp only [G.step_objectKernel]
  apply expect_mul_ge_real w hw hp
  · intro ω ω' hω
    exact hf (G.clusterObject_mono (G.eraseVertices_mono hω C.1) S)
  · intro ω ω' hω
    exact hg (G.clusterObject_mono (G.eraseVertices_mono hω C.1) S)

omit [Fintype V] [Fintype E] in
lemma clusterObject_empty (S : Set V) : G.clusterObject ∅ S = (S, ∅) := by
  apply Prod.ext
  · change roots (G.openGraph ∅) S = S
    have he : G.openGraph ∅ = ⊥ := by simp [openGraph]
    rw [he]
    ext v
    simp [roots, SimpleGraph.reachable_bot]
  · exact Set.empty_inter _

omit [Fintype V] in
lemma objectKernel_minorization (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (S : Set V) (C : ClusterObject V E) :
    density w (fun _ => False) ≤ G.objectKernel w S C (S, ∅) := by
  have h := Finset.single_le_sum (f := fun ω : E → Prop =>
    density w ω * (if G.clusterObject (G.eraseVertices ω C.1) S = (S, ∅) then 1 else 0))
    (s := Finset.univ) (a := fun _ => False)
    (fun ω _ => mul_nonneg (density_nonneg hp ω) (by split_ifs <;> norm_num)) (Finset.mem_univ _)
  have he : G.eraseVertices ∅ C.1 = ∅ := Set.empty_sdiff _
  simpa only [objectKernel, distribution, expect, show (fun _ : E => False) = (∅ : Set E) from rfl,
    he, G.clusterObject_empty, ite_eq_left rfl, if_true, mul_one] using h

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_AvgDiv
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

namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]

lemma avg_div (μ : X → ℝ) (a : ℝ) (f : X → ℝ) :
    avg (fun x => μ x/a) f = avg μ f/a := by
  simp only [avg, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma stationary_of_avg (K : X → X → ℝ) (μ : X → ℝ)
    (h : ∀ f : X → ℝ, avg μ (step K f) = avg μ f) (y : X) :
    ∑ x, μ x * K x y = μ y := by
  classical
  simpa [step, avg] using h (fun x => if x = y then 1 else 0)

end CriticalPercolation.FiniteMarkov

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_ObjectAvoidMass
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
open ClusterDeletion FiniteProduct FiniteMarkov
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma avg_objectAvoidMass (w : E → Prop → ℝ) (A B : Set V)
    (f : ClusterObject V E → ℝ) :
    avg (G.objectAvoidMass w A B) f =
      expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0) := by
  rw [expect_comp w (fun ω => G.clusterObject ω A)
    (fun C => if Disjoint C.1 B then f C else 0)]
  apply Finset.sum_congr rfl
  intro C _
  simp only [objectAvoidMass]
  split_ifs <;> simp

omit [Fintype V] in
lemma objectAvoidMass_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (A B : Set V) (C : ClusterObject V E) : 0 ≤ G.objectAvoidMass w A B C := by
  unfold objectAvoidMass
  split_ifs
  · exact distribution_nonneg hp _ _
  · exact le_rfl

lemma sum_objectAvoidMass (w : E → Prop → ℝ) (A B : Set V) :
    ∑ C, G.objectAvoidMass w A B C = G.objectAvoidTotal w A B := by
  simpa only [avg, mul_one, objectAvoidTotal] using
    G.avg_objectAvoidMass w A B (fun _ => 1)

omit [Fintype V] in
lemma objectAvoidTotal_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (A B : Set V) : G.objectAvoidTotal w A B ≤ 1 := by
  rw [← expect_const w hw 1]
  apply expect_mono hp
  intro ω
  split_ifs <;> norm_num

omit [Fintype V] in
lemma objectAvoidTotal_minorization (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {A B : Set V} (hAB : Disjoint A B) :
    density w (fun _ => False) ≤ G.objectAvoidTotal w A B := by
  have h := Finset.single_le_sum (f := fun ω : E → Prop => density w ω *
    (if Disjoint (G.clusterObject ω A).1 B then 1 else 0))
    (s := Finset.univ) (a := fun _ => False)
    (fun ω _ => mul_nonneg (density_nonneg hp ω) (by split_ifs <;> norm_num)) (Finset.mem_univ _)
  simpa only [objectAvoidTotal, expect,
    show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.clusterObject_empty, ite_eq_left hAB, mul_one] using h

lemma objectAvoidMass_halfstationary (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A B : Set V) (f : ClusterObject V E → ℝ) :
    avg (G.objectAvoidMass w A B) (step (G.objectKernel w B) f) =
      avg (G.objectAvoidMass w B A) f := by
  rw [G.avg_objectAvoidMass, G.avg_objectAvoidMass]
  simp only [G.step_objectKernel]
  have he := G.clusterObject_avoidance_exposure w hw A B (fun _ D => f D)
  refine he.symm.trans ?_
  congr 1
  funext ω
  rw [show Disjoint (G.clusterObject ω A).1 B ↔ Disjoint (G.clusterObject ω B).1 A from
    G.roots_disjoint_symm ω A B]

lemma objectAvoidLaw_stationary (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A B : Set V) (D : ClusterObject V E) :
    ∑ C, G.objectAvoidLaw w A B C *
      compose (G.objectKernel w B) (G.objectKernel w A) C D = G.objectAvoidLaw w A B D := by
  apply stationary_of_avg
  intro f
  change avg (fun C => G.objectAvoidMass w A B C/G.objectAvoidTotal w A B)
    (step (compose (G.objectKernel w B) (G.objectKernel w A)) f) = _
  rw [avg_div, step_compose, G.objectAvoidMass_halfstationary w hw,
    G.objectAvoidMass_halfstationary w hw]
  exact (avg_div _ _ _).symm

theorem objectAvoidLaw_associated (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (hc : ∀ e, 0 < w e False) {A B : Set V} (hAB : Disjoint A B) :
    Associated (G.objectAvoidLaw w A B) := by
  let a := density w (fun _ => False)
  have ha : 0 < a := Finset.prod_pos fun e _ => hc e
  have hZ := G.objectAvoidTotal_minorization w hp hAB
  have hZp : 0 < G.objectAvoidTotal w A B := ha.trans_le hZ
  have ha1 : a ≤ 1 := hZ.trans (G.objectAvoidTotal_le_one w hw hp A B)
  apply stationary_associated
    (compose_nonneg (G.objectKernel_nonneg w hp B) (G.objectKernel_nonneg w hp A))
    (compose_mass (G.objectKernel_mass w hw B) (G.objectKernel_mass w hw A))
    (compose_associated (G.objectKernel_nonneg w hp B) (G.objectKernel_associated w hw hp B)
      (G.objectKernel_associated w hw hp A) (G.objectKernel_antitone w hp A))
    (fun _ hf => compose_monotone (G.objectKernel_antitone w hp B)
      (G.objectKernel_antitone w hp A) hf)
    ha ha1
    (compose_minorization (G.objectKernel_nonneg w hp B) (G.objectKernel_mass w hw B)
      (G.objectKernel_minorization w hp A))
    (G.objectAvoidLaw w A B)
  · intro C
    exact div_nonneg (G.objectAvoidMass_nonneg w hp A B C) hZp.le
  · simp only [objectAvoidLaw, ← Finset.sum_div, G.sum_objectAvoidMass, div_self hZp.ne']
  · exact G.objectAvoidLaw_stationary w hw A B

lemma avg_objectAvoidLaw (w : E → Prop → ℝ) (A B : Set V) (f : ClusterObject V E → ℝ) :
    avg (G.objectAvoidLaw w A B) f =
      (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0)) /
      G.objectAvoidTotal w A B := by
  change avg (fun C => G.objectAvoidMass w A B C/G.objectAvoidTotal w A B) f = _
  rw [avg_div, G.avg_objectAvoidMass]

theorem clusterObject_avoidance_cross (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (hc : ∀ e, 0 < w e False) {A B : Set V} (hAB : Disjoint A B)
    (f g : ClusterObject V E → ℝ) (hf : Monotone f) (hg : Monotone g) :
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      f (G.clusterObject ω A) * g (G.clusterObject ω B) else 0))/G.objectAvoidTotal w A B ≤
    ((expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0))/
      G.objectAvoidTotal w A B) *
    ((expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then g (G.clusterObject ω B) else 0))/
      G.objectAvoidTotal w A B) := by
  have hassoc := G.objectAvoidLaw_associated w hw hp hc hAB
  have hh := hassoc.cross f (step (G.objectKernel w B) g) hf
    (G.objectKernel_antitone w hp B g hg)
  rw [G.avg_objectAvoidLaw, G.avg_objectAvoidLaw, G.avg_objectAvoidLaw] at hh
  simp only [G.step_objectKernel] at hh
  have hj := G.clusterObject_avoidance_exposure w hw A B (fun C D => f C*g D)
  have hm := G.clusterObject_avoidance_exposure w hw A B (fun _ D => g D)
  simp only [expect_const_mul] at hj
  exact hj.symm ▸ hm.symm ▸ hh

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ClusterObjectAvoidanceCross
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
open ClusterDeletion FiniteProduct FiniteMarkov
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

theorem clusterObject_avoidance_cross_mul (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (hc : ∀ e, 0 < w e False) {A B : Set V} (hAB : Disjoint A B)
    (f g : ClusterObject V E → ℝ) (hf : Monotone f) (hg : Monotone g) :
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then
      f (G.clusterObject ω A) * g (G.clusterObject ω B) else 0))*G.objectAvoidTotal w A B ≤
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then f (G.clusterObject ω A) else 0)) *
    (expect w (fun ω => if Disjoint (G.clusterObject ω A).1 B then g (G.clusterObject ω B) else 0)) := by
  have hZ : 0 < G.objectAvoidTotal w A B :=
    (Finset.prod_pos fun e _ => hc e).trans_le (G.objectAvoidTotal_minorization w hp hAB)
  have hh := G.clusterObject_avoidance_cross w hw hp hc hAB f g hf hg
  have hi (F H Z : ℝ) : (F/Z)*(H/Z) = (F*H/Z)/Z := by ring
  rw [hi, div_le_div_iff_of_pos_right hZ] at hh
  exact (le_div_iff₀ hZ).mp hh

omit [Fintype V] [Fintype E] in
lemma openGraph_adj_clusterObject {ω : Set E} {S : Set V} {v t : V}
    (hv : v ∈ (G.clusterObject ω S).1) (ha : (G.openGraph ω).Adj v t) :
    (G.openGraph (G.clusterObject ω S).2).Adj v t := by
  obtain ⟨⟨e, he, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp ha
  exact (SimpleGraph.fromEdgeSet_adj _).mpr
    ⟨⟨e, ⟨he, v, hv, by simp [heq]⟩, heq⟩, hne⟩

omit [Fintype V] [Fintype E] in
lemma reachable_clusterObject {ω : Set E} {S : Set V} {v t : V} (hv : v ∈ S) :
    (G.openGraph (G.clusterObject ω S).2).Reachable v t ↔ (G.openGraph ω).Reachable v t := by
  constructor
  · intro ht
    exact ht.mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono Set.inter_subset_left))
  · intro ht
    have h := ((G.openGraph ω).reachable_iff_reflTransGen v t).mp ht
    clear ht
    induction h with
    | refl => exact .refl _
    | @tail u t h hut ih =>
      exact ih.trans (G.openGraph_adj_clusterObject
        ⟨v, hv, ((G.openGraph ω).reachable_iff_reflTransGen v u).mpr h⟩ hut).reachable

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Prob
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

lemma prob_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (P : Set E → Prop) :
    0 ≤ prob w P := expect_nonneg hp (fun _ => by split_ifs <;> norm_num)

lemma prob_mono (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {P Q : Set E → Prop} (h : ∀ ω, P ω → Q ω) : prob w P ≤ prob w Q := by
  apply expect_mono hp
  intro ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
  exact (hQ (h ω hP)).elim

lemma prob_split (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w P = prob w (fun ω => P ω ∧ Q ω) + prob w (fun ω => P ω ∧ ¬Q ω) := by
  unfold prob
  rw [← expect_add]
  congr 1
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

lemma prob_congr (w : E → Prop → ℝ) {P Q : Set E → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : prob w P = prob w Q := by
  congr 1
  funext ω
  exact propext (h ω)

lemma indicator_antitone {X : Type*} [Preorder X] {P : X → Prop}
    (h : ∀ ⦃x y⦄, x ≤ y → P y → P x) :
    Antitone (fun x => if P x then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
  exact (hx (h hxy hy)).elim

lemma indicator_monotone {X : Type*} [Preorder X] {P : X → Prop}
    (h : ∀ ⦃x y⦄, x ≤ y → P x → P y) :
    Monotone (fun x => if P x then (1 : ℝ) else 0) := by
  intro x y hxy
  by_cases hx : P x <;> by_cases hy : P y <;> simp [hx, hy]
  exact (hy (h hxy hx)).elim

lemma expect_mul_ge_antitone (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf : Antitone f) (hg : Antitone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω*g ω) := by
  have hh := expect_mul_ge_real w hw hp (fun ω => -f ω) (fun ω => -g ω) hf.neg hg.neg
  have hn (f : (E → Prop) → ℝ) : expect w (fun ω => -f ω) = -expect w f := by
    simp [expect, Finset.sum_neg_distrib]
  simpa only [hn, neg_mul_neg] using hh

lemma prob_harris_decreasing (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hp : ∀ e b, 0 ≤ w e b) (P Q : Set E → Prop)
    (hP : ∀ ⦃ω ω'⦄, ω ≤ ω' → P ω' → P ω)
    (hQ : ∀ ⦃ω ω'⦄, ω ≤ ω' → Q ω' → Q ω) :
    prob w P * prob w Q ≤ prob w (fun ω => P ω ∧ Q ω) := by
  have hh := expect_mul_ge_antitone w hw hp _ _ (indicator_antitone hP) (indicator_antitone hQ)
  change expect w _ * expect w _ ≤ _
  refine hh.trans_eq ?_
  apply congrArg (expect w)
  funext ω
  by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_IsolateThree
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

lemma isolateThree_eq_avoid (a s t : V) (ω : Set E) :
    Disjoint (G.clusterObject ω {a}).1 {s,t} ↔ G.isolateThree a s t ω := by
  simp [clusterObject, roots, Set.disjoint_insert_right, Set.disjoint_singleton_right, isolateThree]

lemma isolateThree_decreasing (a s t : V) {ω ω' : Set E} (h : ω ⊆ ω')
    (hi : G.isolateThree a s t ω') : G.isolateThree a s t ω := by
  have hG : G.openGraph ω ≤ G.openGraph ω' :=
    SimpleGraph.fromEdgeSet_mono (Set.image_mono h)
  exact ⟨fun hs => hi.1 (hs.mono hG), fun ht => hi.2 (ht.mono hG)⟩

lemma separateThree_rotate (a s t : V) (ω : Set E) :
    G.separateThree t a s ω ↔ G.separateThree a s t ω := by
  constructor
  · rintro ⟨⟨hta, hts⟩, has⟩
    exact ⟨⟨has, fun h => hta h.symm⟩, fun h => hts h.symm⟩
  · rintro ⟨⟨has, hat⟩, hst⟩
    exact ⟨⟨fun h => hat h.symm, fun h => hst h.symm⟩, has⟩

lemma isolateThree_inter (a s t : V) (ω : Set E) :
    (G.isolateThree a s t ω ∧ G.isolateThree t a s ω) ↔ G.separateThree a s t ω := by
  constructor
  · rintro ⟨ha, ht⟩
    exact ⟨ha, fun h => ht.2 h.symm⟩
  · rintro ⟨ha, hst⟩
    exact ⟨ha, (G.separateThree_rotate a s t ω).mpr ⟨ha, hst⟩ |>.1⟩

variable [Fintype V] [Fintype E]

theorem threeCluster_avoidance (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z) (hc : ∀ e, 0 < w e False)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) :
    prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair a s t) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  let f : ClusterObject V E → ℝ := fun C => if b ∈ C.1 then 1 else 0
  let g : ClusterObject V E → ℝ := fun C => if (G.openGraph C.2).Reachable s t then 1 else 0
  have hf : Monotone f := indicator_monotone (fun _ _ h hm => h.1 hm)
  have hg : Monotone g := by
    intro C D h
    dsimp only [g]
    by_cases hC : (G.openGraph C.2).Reachable s t
    · have hD : (G.openGraph D.2).Reachable s t :=
        hC.mono (SimpleGraph.fromEdgeSet_mono (Set.image_mono h.2))
      simp only [ite_eq_left hC, ite_eq_left hD, le_refl]
    · simp only [ite_eq_right hC]
      split_ifs <;> norm_num
  have hd : Disjoint ({a} : Set V) {s,t} := by simp [has, hat]
  have h := G.clusterObject_avoidance_cross_mul w hw hp hc hd f g hf hg
  have hf' (ω : Set E) : f (G.clusterObject ω {a}) =
      if (G.openGraph ω).Reachable a b then 1 else 0 := by simp [f, clusterObject, roots]
  have hg' (ω : Set E) : g (G.clusterObject ω {s,t}) =
      if (G.openGraph ω).Reachable s t then 1 else 0 := by
    simp only [g, G.reachable_clusterObject (Set.mem_insert s {t})]
  have hZ : G.objectAvoidTotal w {a} {s,t} = prob w (G.isolateThree a s t) := by
    unfold objectAvoidTotal prob
    apply congrArg (expect w)
    funext ω
    rw [G.isolateThree_eq_avoid a s t ω]
  have hfg : (expect w fun ω => if Disjoint (G.clusterObject ω {a}).1 {s,t} then
      f (G.clusterObject ω {a}) * g (G.clusterObject ω {s,t}) else 0) =
      prob w (fun ω => G.isolateThree a s t ω ∧
        (G.openGraph ω).Reachable a b ∧ (G.openGraph ω).Reachable s t) := by
    apply congrArg (expect w)
    funext ω
    rw [hf' ω, hg' ω, G.isolateThree_eq_avoid a s t ω]
    by_cases hi : G.isolateThree a s t ω <;>
      by_cases hb : (G.openGraph ω).Reachable a b <;>
      by_cases ht : (G.openGraph ω).Reachable s t <;> simp [hi,hb,ht]
  have hf'' : (expect w fun ω => if Disjoint (G.clusterObject ω {a}).1 {s,t} then
      f (G.clusterObject ω {a}) else 0) =
      prob w (fun ω => G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) := by
    apply congrArg (expect w)
    funext ω
    rw [hf' ω, G.isolateThree_eq_avoid a s t ω]
    by_cases hi : G.isolateThree a s t ω <;>
      by_cases hb : (G.openGraph ω).Reachable a b <;> simp [hi,hb]
  have hg'' : (expect w fun ω => if Disjoint (G.clusterObject ω {a}).1 {s,t} then
      g (G.clusterObject ω {s,t}) else 0) = prob w (G.joinedPair a s t) := by
    apply congrArg (expect w)
    funext ω
    rw [hg' ω, G.isolateThree_eq_avoid a s t ω]
    by_cases hi : G.isolateThree a s t ω <;>
      by_cases ht : (G.openGraph ω).Reachable s t <;> simp [hi,ht,joinedPair]
  rw [hfg,hf'',hg'',hZ] at h
  have hγ : prob w (fun ω => G.isolateThree a s t ω ∧
      (G.openGraph ω).Reachable a b ∧ (G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair]; tauto)
  have hu := prob_split w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable s t)
  have hb := prob_split w (fun ω => G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
    (fun ω => (G.openGraph ω).Reachable s t)
  have hβ : prob w (fun ω => (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧
      ¬(G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [separateThree]; tauto)
  have hγ' : prob w (fun ω => (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧
      (G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair]; tauto)
  rw [hγ] at h
  rw [hβ, hγ'] at hb
  change prob w (G.isolateThree a s t) = prob w (G.joinedPair a s t) +
    prob w (G.separateThree a s t) at hu
  rw [hu, hb] at h
  nlinarith

omit [Fintype V] in

theorem threeCluster_harris (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z) (a s t : V) :
    (prob w (G.separateThree a s t) + prob w (G.joinedPair a s t)) *
      (prob w (G.separateThree a s t) + prob w (G.joinedPair t a s)) ≤
      prob w (G.separateThree a s t) := by
  have h := prob_harris_decreasing w hw hp (G.isolateThree a s t) (G.isolateThree t a s)
    (fun _ _ hh hi => G.isolateThree_decreasing a s t hh hi)
    (fun _ _ hh hi => G.isolateThree_decreasing t a s hh hi)
  have he := prob_congr w (G.isolateThree_inter a s t)
  rw [he] at h
  have ha := prob_split w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable s t)
  have ht := prob_split w (G.isolateThree t a s) (fun ω => (G.openGraph ω).Reachable a s)
  change prob w (G.isolateThree a s t) = prob w (G.joinedPair a s t) +
    prob w (G.separateThree a s t) at ha
  change prob w (G.isolateThree t a s) = prob w (G.joinedPair t a s) +
    prob w (G.separateThree t a s) at ht
  rw [prob_congr w (G.separateThree_rotate a s t)] at ht
  rw [ha, ht] at h
  nlinarith

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProbDisjoint
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

lemma prob_disjoint_le (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (P Q R : Set E → Prop) (hP : ∀ ω, P ω → R ω) (hQ : ∀ ω, Q ω → R ω)
    (hPQ : ∀ ω, ¬(P ω ∧ Q ω)) : prob w P + prob w Q ≤ prob w R := by
  unfold prob
  rw [← expect_add]
  apply expect_mono hp
  intro ω
  by_cases hp' : P ω <;> by_cases hq' : Q ω <;> by_cases hr' : R ω <;>
    simp [hp',hq',hr']
  · exact (hPQ ω ⟨hp',hq'⟩).elim
  · exact (hr' (hP ω hp')).elim
  · exact (hr' (hP ω hp')).elim
  · exact (hr' (hQ ω hq')).elim

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ThreeClusterAvoidanceSecond
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
open FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E) [Fintype V] [Fintype E]

omit [Fintype V] in
lemma threeCluster_event_bounds (w : E → Prop → ℝ) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) :
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) ≤
      prob w (G.separateThree a s t) ∧
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) ≤
      prob w (G.separateThree a s t) + prob w (G.joinedPair a s t) -
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) -
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  constructor
  · exact prob_mono w hp (fun _ h => h.1)
  · have h1 := prob_disjoint_le w hp
      (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b)
      (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
      (G.separateThree a s t) (fun _ h => h.1) (fun _ h => h.1)
      (fun _ h => h.1.1.1.2 (h.2.2.trans h.1.2.symm))
    have h2 := prob_mono w hp (P := fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b)
      (Q := G.joinedPair a s t) (fun _ h => h.1)
    linarith

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PivotalComparison
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

namespace CriticalPercolation.DFS

lemma pivotal_comparison {u v x a s : ℝ}
    (hu : 0 < u) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (havoid : s*u ≤ x*a) (harris : (u+v)*(u+x) ≤ u) :
    (a+s)*(u+v) ≤ a := by
  have h1 := mul_le_mul_of_nonneg_right havoid (add_nonneg hu.le hv)
  have h2 := mul_le_mul_of_nonneg_left harris ha
  nlinarith

lemma tilted_increment {u v a b g : ℝ}
    (h0 : 0 < u+v) (h1 : 0 < u+v-b-g) (hc : u*g ≤ v*b) :
    a/(u+v-b-g) ≤ (v+a-g)/(u+v-b-g)-v/(u+v) := by
  have hid : (v+a-g)/(u+v-b-g)-v/(u+v)-a/(u+v-b-g) =
      (v*b-u*g)/((u+v)*(u+v-b-g)) := by
    field_simp
    ring
  have hn : 0 ≤ (v*b-u*g)/((u+v)*(u+v-b-g)) :=
    div_nonneg (sub_nonneg.mpr hc) (mul_pos h0 h1).le
  linarith

lemma converted_variance {p u v x a b g s : ℝ}
    (hp : p ∈ Set.Ioo 0 1) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hg : 0 ≤ g) (hs : 0 ≤ s)
    (hau : a ≤ u) (ha1 : a ≤ u+v-b-g)
    (havoid₁ : u*g ≤ v*b) (havoid₂ : s*u ≤ x*a)
    (harris : (u+v)*(u+x) ≤ u) :
    p*(1-p)*a*(a+s) ≤
      p*(1-p)*(u+v)*(u+v-b-g)/((1-p)*(u+v)+p*(u+v-b-g)) *
        ((v+a-g)/(u+v-b-g)-v/(u+v))^2 := by
  let U0 := u+v
  let U1 := u+v-b-g
  let U := (1-p)*U0+p*U1
  let r := (v+a-g)/U1-v/U0
  have hpq : 0 ≤ p*(1-p) := mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)
  have h0 : 0 ≤ U0 := add_nonneg hu hv
  have h1 : 0 ≤ U1 := ha.trans ha1
  have hU : 0 ≤ U := add_nonneg (mul_nonneg (sub_nonneg.mpr hp.2.le) h0)
    (mul_nonneg hp.1.le h1)
  change p*(1-p)*a*(a+s) ≤ p*(1-p)*U0*U1/U*r^2
  rcases eq_or_lt_of_le ha with hz | ha
  · rw [← hz]
    simpa only [mul_zero, zero_mul] using
      mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg hpq h0) h1) hU) (sq_nonneg r)
  · have hup : 0 < u := ha.trans_le hau
    have h0p : 0 < U0 := add_pos_of_pos_of_nonneg hup hv
    have h1p : 0 < U1 := ha.trans_le ha1
    have hUp : 0 < U := add_pos
      (mul_pos (sub_pos.mpr hp.2) h0p) (mul_pos hp.1 h1p)
    have h10 : U1 ≤ U0 := by dsimp [U1,U0]; linarith
    have hU0 : U ≤ U0 := by
      dsimp [U]
      have ht := mul_le_mul_of_nonneg_left h10 hp.1.le
      nlinarith
    have hprod : U*U1 ≤ U0^2 := by
      have hh := mul_le_mul hU0 h10 h1 h0
      nlinarith
    have hcmp : (a+s)*U0 ≤ a := pivotal_comparison hup hv ha.le havoid₂ harris
    have hr : a/U1 ≤ r := tilted_increment h0p h1p havoid₁
    have hr0 : 0 ≤ r := (div_nonneg ha.le h1).trans hr
    have hsqr : (a/U1)^2 ≤ r^2 := by
      exact pow_le_pow_left₀ (div_nonneg ha.le h1) hr 2
    have hab : 0 ≤ a*(a+s) := mul_nonneg ha.le (add_nonneg ha.le hs)
    have hbase : a*(a+s) ≤ U0*a^2/(U*U1) := by
      apply (le_div_iff₀ (mul_pos hUp h1p)).mpr
      calc
        _ ≤ (a*(a+s))*U0^2 := mul_le_mul_of_nonneg_left hprod hab
        _ ≤ U0*a^2 := by
          have hh := mul_le_mul_of_nonneg_left hcmp (mul_nonneg ha.le h0)
          nlinarith
    calc
      _ = (p*(1-p))*(a*(a+s)) := by ring
      _ ≤ (p*(1-p))*(U0*a^2/(U*U1)) := mul_le_mul_of_nonneg_left hbase hpq
      _ = (p*(1-p)*U0*U1/U)*(a/U1)^2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqr
        (div_nonneg (mul_nonneg (mul_nonneg hpq h0) h1) hU)

end CriticalPercolation.DFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ClosedThin
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

lemma continuous_prob_weights (P : Set E → Prop) :
    Continuous (fun w : E → Prop → ℝ => prob w P) := by
  unfold prob expect density
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  exact (continuous_apply (ω e)).comp (continuous_apply e)

omit [Fintype E] in
lemma closedThin_zero (w : E → Prop → ℝ) : closedThin w 0 = w := by
  funext e b
  simp [closedThin]

omit [Fintype E] in
lemma continuous_closedThin (w : E → Prop → ℝ) : Continuous (closedThin w) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro b
  dsimp only [closedThin]
  split_ifs <;> fun_prop

omit [Fintype E] in
lemma closedThin_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) (t : ℝ) (e : E) :
    ∑ b, closedThin w t e b = 1 := by
  have hh := hw e
  simp only [Fintype.sum_Prop] at hh ⊢
  dsimp only [closedThin]
  rw [ite_eq_left True.intro,ite_eq_right (by trivial : ¬False)]
  calc
    _ = (1-t)*(w e True+w e False)+t := by ring
    _ = 1 := by rw [hh]; ring

omit [Fintype E] in
lemma closedThin_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : ∀ e b, 0 ≤ closedThin w t e b := by
  intro e b
  apply add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hp e b))
  split_ifs <;> first | exact ht.1 | exact le_rfl

omit [Fintype E] in
lemma closedThin_closed_pos (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 1) (e : E) : 0 < closedThin w t e False := by
  simp only [closedThin,ite_eq_right (by trivial : ¬False)]
  exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hp e False)) ht.1

lemma prob_mul_le_of_strict (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hp : ∀ e b, 0 ≤ w e b)
    (P Q R S : Set E → Prop)
    (h : ∀ w' : E → Prop → ℝ, (∀ e, ∑ b, w' e b = 1) → (∀ e b, 0 ≤ w' e b) →
      (∀ e, 0 < w' e False) → prob w' P * prob w' Q ≤ prob w' R * prob w' S) :
    prob w P * prob w Q ≤ prob w R * prob w S := by
  have hc := continuous_closedThin w
  have hL := ((((continuous_prob_weights P).comp hc).mul
    ((continuous_prob_weights Q).comp hc)).tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hR := ((((continuous_prob_weights R).comp hc).mul
    ((continuous_prob_weights S).comp hc)).tendsto 0).comp
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (n : ℕ) : (1/((n:ℝ)+1)) ∈ Set.Ioc (0:ℝ) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by positivity : (0:ℝ) < n+1)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
  have hh := le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall (fun n : ℕ =>
    h (closedThin w (1/((n:ℝ)+1))) (closedThin_mass w hw _)
      (closedThin_nonneg w hp ⟨(hb n).1.le,(hb n).2⟩) (closedThin_closed_pos w hp (hb n))))
  simpa only [Pi.mul_apply,Function.comp_apply,closedThin_zero] using hh

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Clusters_ThreeClusterAvoidanceGeneral
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
open FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E) [Fintype V] [Fintype E]

lemma threeCluster_avoidance_general (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) :
    prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair a s t) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) :=
  prob_mul_le_of_strict w hw hp _ _ _ _ (fun w' hw' hp' hc' =>
    G.threeCluster_avoidance w' hw' hp' hc' a s t b has hat)

lemma threeCluster_avoidance_second_general (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (hat : t ≠ a) (hst : t ≠ s) :
    prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b) *
      prob w (G.separateThree a s t) ≤
    prob w (G.joinedPair t a s) *
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
  have h := G.threeCluster_avoidance_general w hw hp t a s b hat hst
  rw [prob_congr w (G.separateThree_rotate a s t),
    prob_congr w (fun ω => and_congr_left (fun _ => G.separateThree_rotate a s t ω))] at h
  exact h

theorem residual_converted_variance_general (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hparam : p ∈ Set.Ioo 0 1) :
    let u := prob w (G.separateThree a s t)
    let v := prob w (G.joinedPair a s t)
    let α := prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b)
    let β := prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
    let γ := prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b)
    let σ := prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b)
    p*(1-p)*α*(α+σ) ≤
      p*(1-p)*(u+v)*(u+v-β-γ)/((1-p)*(u+v)+p*(u+v-β-γ)) *
        ((v+α-γ)/(u+v-β-γ)-v/(u+v))^2 := by
  dsimp only
  have h1 := G.threeCluster_avoidance_general w hw hp a s t b has hat
  have h2 := G.threeCluster_avoidance_second_general w hw hp a s t b hat.symm hst.symm
  have h3 := G.threeCluster_harris w hw hp a s t
  have h4 := G.threeCluster_event_bounds w hp a s t b
  apply DFS.converted_variance hparam (prob_nonneg w hp _) (prob_nonneg w hp _)
    (prob_nonneg w hp _) (prob_nonneg w hp _) (prob_nonneg w hp _) (prob_nonneg w hp _)
    h4.1 h4.2 _ h2 h3
  simpa only [mul_comm] using h1

end CriticalPercolation.BondGraph

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

lemma wired_pivot (a s t b : V) :
    ((H ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬(H ⊔ SimpleGraph.edge a s).Reachable a t) ↔
    (¬H.Reachable a t ∧ ¬H.Reachable s t ∧ H.Reachable b t) := by
  have hs : (H ⊔ SimpleGraph.edge a s).Reachable a s := (edge_reachable a s).mono le_sup_right
  rw [reachable_sup_edge]
  constructor
  · rintro ⟨hnew,hold⟩
    have ha : ¬H.Reachable a t := fun h => hold (h.mono le_sup_left)
    have hst : ¬H.Reachable s t := fun h => hold (hs.trans (h.mono le_sup_left))
    have hb : (H ⊔ SimpleGraph.edge a s).Reachable b t := by
      rcases hnew with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact (hold h).elim
      · exact h
      · exact (hold (hs.trans h)).elim
    have hbt : H.Reachable b t := by
      rcases (reachable_sup_edge H a s b t).mp hb with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact h
      · exact (hst h).elim
      · exact (ha h).elim
    exact ⟨ha,hst,hbt⟩
  · rintro ⟨ha,hst,hbt⟩
    constructor
    · exact Or.inr (Or.inl ⟨hs,hbt.mono le_sup_left⟩)
    · intro h
      rcases (reachable_sup_edge H a s a t).mp h with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact ha h
      · exact hst h
      · exact ha h

lemma two_pivots (a s t b : V) :
    ((H ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬(H ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬(H ⊔ SimpleGraph.edge s b).Reachable a t) ↔
    (¬H.Reachable a s ∧ ¬H.Reachable a t ∧ ¬H.Reachable s t ∧ H.Reachable b t) := by
  constructor
  · rintro ⟨h,he,hf⟩
    obtain ⟨hat,hst,hbt⟩ := (wired_pivot H a s t b).mp ⟨h,he⟩
    refine ⟨?_,hat,hst,hbt⟩
    intro has
    apply hf
    exact (reachable_sup_edge H s b a t).mpr (Or.inr (Or.inl ⟨has,hbt⟩))
  · rintro ⟨has,hat,hst,hbt⟩
    obtain ⟨h,he⟩ := (wired_pivot H a s t b).mpr ⟨hat,hst,hbt⟩
    refine ⟨h,he,?_⟩
    intro hf
    rcases (reachable_sup_edge H s b a t).mp hf with h | ⟨h,_⟩ | ⟨_,h⟩
    · exact hat h
    · exact has h
    · exact hst h

lemma avoid_sup_edge (a s t b : V) :
    (¬(H ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬(H ⊔ SimpleGraph.edge s b).Reachable a t) ↔
    (¬H.Reachable a s ∧ ¬H.Reachable a t ∧ ¬H.Reachable a b) := by
  constructor
  · rintro ⟨hs,ht⟩
    refine ⟨fun h => hs (h.mono le_sup_left),fun h => ht (h.mono le_sup_left),?_⟩
    intro hb
    apply hs
    exact (reachable_sup_edge H s b a s).mpr (Or.inr (Or.inr ⟨hb,.refl _⟩))
  · rintro ⟨hs,ht,hb⟩
    constructor
    · intro h
      rcases (reachable_sup_edge H s b a s).mp h with h | ⟨h,_⟩ | ⟨h,_⟩
      · exact hs h
      · exact hs h
      · exact hb h
    · intro h
      rcases (reachable_sup_edge H s b a t).mp h with h | ⟨h,_⟩ | ⟨h,_⟩
      · exact ht h
      · exact hs h
      · exact hb h

lemma avoid_target_sup_edge (a s t b : V) :
    (¬(H ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬(H ⊔ SimpleGraph.edge s b).Reachable a t ∧
      (H ⊔ SimpleGraph.edge s b).Reachable s t) ↔
    ((¬H.Reachable a s ∧ ¬H.Reachable a t ∧ H.Reachable s t ∧ ¬H.Reachable a b) ∨
      (¬H.Reachable a s ∧ ¬H.Reachable a t ∧ ¬H.Reachable s t ∧ H.Reachable b t)) := by
  constructor
  · rintro ⟨hs,ht,hst⟩
    obtain ⟨has,hat,hab⟩ := (avoid_sup_edge H a s t b).mp ⟨hs,ht⟩
    by_cases hst' : H.Reachable s t
    · exact Or.inl ⟨has,hat,hst',hab⟩
    · refine Or.inr ⟨has,hat,hst',?_⟩
      rcases (reachable_sup_edge H s b s t).mp hst with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact (hst' h).elim
      · exact h
      · exact (hst' h).elim
  · rintro (⟨has,hat,hst,hab⟩ | ⟨has,hat,hst,hbt⟩)
    · have hh := (avoid_sup_edge H a s t b).mpr ⟨has,hat,hab⟩
      exact ⟨hh.1,hh.2,hst.mono le_sup_left⟩
    · have hab : ¬H.Reachable a b := fun h => hat (h.trans hbt)
      have hh := (avoid_sup_edge H a s t b).mpr ⟨has,hat,hab⟩
      exact ⟨hh.1,hh.2,(reachable_sup_edge H s b s t).mpr (Or.inr (Or.inl ⟨.refl _,hbt⟩))⟩

end Wiring
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProbOr
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

lemma prob_or (w : E → Prop → ℝ) (P Q : Set E → Prop)
    (hd : ∀ ω, ¬(P ω ∧ Q ω)) :
    prob w (fun ω => P ω ∨ Q ω) = prob w P + prob w Q := by
  unfold prob
  rw [← expect_add]
  apply congrArg (expect w)
  funext ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp,hq]
  exact (hd ω ⟨hp,hq⟩).elim

lemma prob_diff (w : E → Prop → ℝ) (P Q : Set E → Prop) :
    prob w (fun ω => P ω ∧ ¬Q ω) = prob w P - prob w (fun ω => P ω ∧ Q ω) := by
  have hh := prob_split w P Q
  linarith
end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ProbIsolateThree
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
open FiniteProduct
open scoped Classical

variable {V E : Type*} (G : BondGraph V E) [Fintype E]

lemma prob_isolateThree (w : E → Prop → ℝ) (a s t : V) :
    prob w (G.isolateThree a s t) =
      prob w (G.separateThree a s t) + prob w (G.joinedPair a s t) := by
  have hh := prob_split w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable s t)
  exact hh.trans (add_comm _ _)

lemma prob_wired_pivot (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t) =
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) +
    prob w (fun ω => G.joinedPair t a s ω ∧ (G.openGraph ω).Reachable t b) := by
  rw [← prob_or w _ _ (by
    intro ω ⟨h,k⟩
    exact h.1.1.1 k.1.2)]
  apply prob_congr
  intro ω
  rw [Wiring.wired_pivot]
  dsimp only [separateThree,joinedPair,isolateThree]
  have hat : (G.openGraph ω).Reachable t a ↔ (G.openGraph ω).Reachable a t := SimpleGraph.reachable_comm
  have hst : (G.openGraph ω).Reachable t s ↔ (G.openGraph ω).Reachable s t := SimpleGraph.reachable_comm
  have hbt : (G.openGraph ω).Reachable b t ↔ (G.openGraph ω).Reachable t b := SimpleGraph.reachable_comm
  simp only [hat,hst,hbt]
  tauto

lemma prob_two_pivots (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) =
    prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
  apply prob_congr
  intro ω
  rw [Wiring.two_pivots]
  dsimp only [separateThree,isolateThree]
  have hbt : (G.openGraph ω).Reachable b t ↔ (G.openGraph ω).Reachable t b := SimpleGraph.reachable_comm
  simp only [hbt]
  tauto

lemma prob_wired_avoid (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) =
    prob w (G.isolateThree a s t) -
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) -
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  rw [prob_congr w (fun ω => Wiring.avoid_sup_edge (G.openGraph ω) a s t b)]
  have hsplit := prob_split w
    (fun ω => G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b)
    (fun ω => (G.openGraph ω).Reachable s t)
  have hleft : prob w (fun ω =>
      (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧ (G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair]; tauto)
  have hright : prob w (fun ω =>
      (G.isolateThree a s t ω ∧ (G.openGraph ω).Reachable a b) ∧ ¬(G.openGraph ω).Reachable s t) =
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [separateThree]; tauto)
  rw [hleft,hright] at hsplit
  have hh := prob_diff w (G.isolateThree a s t) (fun ω => (G.openGraph ω).Reachable a b)
  have he : prob w (fun ω => ¬(G.openGraph ω).Reachable a s ∧
      ¬(G.openGraph ω).Reachable a t ∧ ¬(G.openGraph ω).Reachable a b) =
      prob w (fun ω => G.isolateThree a s t ω ∧ ¬(G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [isolateThree]; tauto)
  rw [he,hh,hsplit]
  ring

lemma prob_wired_avoid_target (w : E → Prop → ℝ) (a s t b : V) :
    prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable s t) =
    prob w (G.joinedPair a s t) +
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) -
      prob w (fun ω => G.joinedPair a s t ω ∧ (G.openGraph ω).Reachable a b) := by
  rw [prob_congr w (fun ω => Wiring.avoid_target_sup_edge (G.openGraph ω) a s t b)]
  rw [prob_or w _ _ (by intro ω ⟨h,k⟩; exact k.2.2.1 h.2.2.1)]
  have hleft : prob w (fun ω => ¬(G.openGraph ω).Reachable a s ∧
      ¬(G.openGraph ω).Reachable a t ∧ (G.openGraph ω).Reachable s t ∧
      ¬(G.openGraph ω).Reachable a b) =
      prob w (fun ω => G.joinedPair a s t ω ∧ ¬(G.openGraph ω).Reachable a b) :=
    prob_congr w (fun _ => by dsimp [joinedPair,isolateThree]; tauto)
  have hright : prob w (fun ω => ¬(G.openGraph ω).Reachable a s ∧
      ¬(G.openGraph ω).Reachable a t ∧ ¬(G.openGraph ω).Reachable s t ∧ (G.openGraph ω).Reachable b t) =
      prob w (fun ω => G.separateThree a s t ω ∧ (G.openGraph ω).Reachable t b) := by
    apply prob_congr
    intro ω
    dsimp [separateThree,isolateThree]
    have hbt : (G.openGraph ω).Reachable b t ↔ (G.openGraph ω).Reachable t b := SimpleGraph.reachable_comm
    simp only [hbt]
    tauto
  rw [hleft,hright,prob_diff]
  ring

variable [Fintype V]

theorem wired_pair_charge (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ z, w e z = 1) (hp : ∀ e z, 0 ≤ w e z)
    (a s t b : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hparam : p ∈ Set.Ioo 0 1) :
    let U0 := prob w (G.isolateThree a s t)
    let U1 := prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t)
    let R0 := prob w (G.joinedPair a s t)
    let R1 := prob w (fun ω => ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable s t)
    let de := prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t)
    let pair := prob w (fun ω =>
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t)
    p*(1-p)*pair*de ≤ p*(1-p)*U0*U1/((1-p)*U0+p*U1)*(R1/U1-R0/U0)^2 := by
  dsimp only
  rw [G.prob_wired_pivot,G.prob_two_pivots,G.prob_wired_avoid,G.prob_wired_avoid_target,
    G.prob_isolateThree]
  exact G.residual_converted_variance_general w hw hp a s t b has hat hst hparam

end CriticalPercolation.BondGraph

open scoped Classical

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ReachableReplaceTail
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

namespace CriticalPercolation.Wiring
variable {V : Type*}

lemma reachable_replace_tail (H : SimpleGraph V) (s v b x y : V)
    (hsv : H.Reachable s v) :
    (H ⊔ SimpleGraph.edge v b).Reachable x y ↔
      (H ⊔ SimpleGraph.edge s b).Reachable x y := by
  rw [reachable_sup_edge,reachable_sup_edge]
  constructor
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1.trans hsv.symm,h2⟩)
    · exact Or.inr (Or.inr ⟨h1,hsv.trans h2⟩)
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1.trans hsv,h2⟩)
    · exact Or.inr (Or.inr ⟨h1,hsv.symm.trans h2⟩)

end CriticalPercolation.Wiring

namespace CriticalPercolation.BondGraph
variable {V E : Type*}

lemma openGraph_force_true (G : BondGraph V E) (ω : Set E) (e : E) (v b : V)
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
  rw [openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

end CriticalPercolation.BondGraph

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

omit [Fintype E] [Fintype A] in
lemma pin_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (e : E) (b : A) :
    ∀ j a, 0 ≤ pin w e b j a := by
  intro j a
  by_cases h : j = e
  · subst j; simp [pin]; split_ifs <;> norm_num
  · simpa [pin,h] using hw j a

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

namespace CriticalPercolation.FiniteVariance

lemma sq_div_le_self {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hra : r ≤ a) :
    r^2/a ≤ r := by
  rcases eq_or_lt_of_le ha with hz | hp
  · have : r = 0 := by linarith
    simp [this]
  · apply (div_le_iff₀ hp).mpr
    nlinarith

lemma binary_split {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxa : x ≤ a) (hyb : y ≤ b) :
    x^2/a + y^2/b - (x+y)^2/(a+b) = a*b/(a+b)*(y/b-x/a)^2 := by
  rcases eq_or_lt_of_le ha with hz | hp
  · have hx0 : x = 0 := by linarith
    simp [← hz, hx0]
  · rcases eq_or_lt_of_le hb with hz | hq
    · have hy0 : y = 0 := by linarith
      simp [← hz, hy0]
    · have hab : a+b ≠ 0 := (add_pos hp hq).ne'
      field_simp
      ring

end CriticalPercolation.FiniteVariance

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

lemma expect_split_pin (w : E → Prop → ℝ) (e : E) (f : (E → Prop) → ℝ) :
    expect w f = w e False*expect (pin w e False) f +
      w e True*expect (pin w e True) f := by
  calc
    expect w f = expect w (fun ω => (if ω e = False then f ω else 0) +
      (if ω e = True then f ω else 0)) := by
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e False f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e True f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

lemma expect_congr_support (w : E → Prop → ℝ) (f g : Set E → ℝ)
    (h : ∀ ω, density w ω ≠ 0 → f ω = g ω) : expect w f = expect w g := by
  unfold expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hd : density w ω = 0
  · simp [hd]
  · rw [h ω hd]

lemma density_pin_support (w : E → Prop → ℝ) (e : E) (b : Prop) (ω : E → Prop)
    (h : density (pin w e b) ω ≠ 0) : ω e = b := by
  rw [density_pin] at h
  by_contra he
  simp [he] at h

lemma density_pin_old_support (w : E → Prop → ℝ) (e : E) (b : Prop) (ω : E → Prop)
    (hw : w e b ≠ 0) (h : density (pin w e b) ω ≠ 0) : density w ω ≠ 0 := by
  have hbit := density_pin_support w e b ω h
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),hbit]
  rw [density_pin,ite_eq_left hbit,one_mul] at h
  exact mul_ne_zero h hw

lemma potential_le (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b) (U R : Set E → Prop) :
    potential w U R ≤ prob w R := by
  have hU := prob_nonneg w hp U
  dsimp [potential]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hU)

lemma potential_nonneg (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (U R : Set E → Prop) (hRU : ∀ ω, R ω → U ω) : 0 ≤ potential w U R := by
  dsimp [potential]
  exact sub_nonneg.mpr (FiniteVariance.sq_div_le_self (prob_nonneg w hp U)
    (prob_nonneg w hp R) (prob_mono w hp hRU))

lemma potential_split (w : E → Prop → ℝ) (hp : ∀ e b, 0 ≤ w e b)
    (e : E) (U R : Set E → Prop) (hRU : ∀ ω, R ω → U ω)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hw0 : w e False = 1-p) (hw1 : w e True = p) :
    let U0 := prob (pin w e False) U
    let U1 := prob (pin w e True) U
    let R0 := prob (pin w e False) R
    let R1 := prob (pin w e True) R
    potential w U R - ((1-p)*potential (pin w e False) U R +
      p*potential (pin w e True) U R) =
      p*(1-p)*U0*U1/((1-p)*U0+p*U1)*(R1/U1-R0/U0)^2 := by
  dsimp only
  have hUn := fun b => prob_nonneg (pin w e b) (pin_nonneg w hp e b) U
  have hRn := fun b => prob_nonneg (pin w e b) (pin_nonneg w hp e b) R
  have hRU' := fun b => prob_mono (pin w e b) (pin_nonneg w hp e b) hRU
  have hU : prob w U = (1-p)*prob (pin w e False) U+p*prob (pin w e True) U := by
    have hh := expect_split_pin w e (fun ω => if U ω then 1 else 0)
    simpa only [prob,hw0,hw1] using hh
  have hR : prob w R = (1-p)*prob (pin w e False) R+p*prob (pin w e True) R := by
    have hh := expect_split_pin w e (fun ω => if R ω then 1 else 0)
    simpa only [prob,hw0,hw1] using hh
  have hq : 0 < 1-p := sub_pos.mpr hp1
  have hb := FiniteVariance.binary_split
    (mul_nonneg hq.le (hUn False)) (mul_nonneg hp0.le (hUn True))
    (mul_nonneg hq.le (hRn False)) (mul_nonneg hp0.le (hRn True))
    (mul_le_mul_of_nonneg_left (hRU' False) hq.le)
    (mul_le_mul_of_nonneg_left (hRU' True) hp0.le)
  have hscale : ∀ (c d : ℝ), (c*d)^2/c = c*d^2 := by
    intro c d
    by_cases hc : c = 0
    · simp [hc]
    · field_simp
  simp only [mul_div_mul_left _ _ hq.ne',mul_div_mul_left _ _ hp0.ne'] at hb
  have hx : ∀ (c d u : ℝ), (c*d)^2/(c*u) = c*d^2/u := by
    intro c d u
    rw [div_mul_eq_div_div,hscale]
  simp only [hx] at hb
  dsimp [potential]
  rw [hU,hR]
  convert hb using 1 <;> ring

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

lemma prob_congr_support (w : E → Prop → ℝ) (P Q : Set E → Prop)
    (h : ∀ ω, density w ω ≠ 0 → (P ω ↔ Q ω)) : prob w P = prob w Q := by
  apply expect_congr_support
  intro ω hω
  rw [h ω hω]

lemma prob_pin_transport (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (P : Set E → Prop) :
    prob (pin w e b) P = prob (pin w e a) (fun ω => P (Function.update ω e b)) := by
  exact expect_pin_transport w hw e a b ha hb (fun ω => if P ω then 1 else 0)

omit [Fintype E] in
lemma openPivot_force_true (F : Set E → Prop) (e : E) (ω : Set E) :
    openPivot F e (Function.update ω e True) ↔
      F (Function.update ω e True) ∧ ¬F (Function.update ω e False) := by
  unfold openPivot
  erw [Function.update_self,Function.update_idem]
  simp only [true_and]

lemma delta_eq_pivotal (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    delta w F e = prob (pin w e False)
      (fun ω => F (Function.update ω e True) ∧ ¬F ω) := by
  rw [delta,prob_pin_transport w hw e False True he0 he1]
  have hh := prob_diff (pin w e False)
    (fun ω => F (Function.update ω e True)) F
  have he : prob (pin w e False) (fun ω => F (Function.update ω e True) ∧ F ω) =
      prob (pin w e False) F := by
    apply prob_congr
    intro ω
    constructor
    · exact And.right
    · intro h
      refine ⟨hF _ _ ?_ h,h⟩
      intro j hj
      change Function.update (ω : Set E) e True j
      by_cases hje : j = e
      · subst j; erw [Function.update_self]; trivial
      · erw [Function.update_of_ne hje]; exact hj
  erw [he] at hh
  exact hh.symm

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ProbRequiresBit
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

lemma prob_requires_bit (w : E → Prop → ℝ) (e : E) (b : Prop) (P : Set E → Prop)
    (hb : ∀ ω, P ω → ω e = b) : prob w P = w e b*prob (pin w e b) P := by
  have hh := expect_prop_mask_pin w e b (fun ω => if P ω then 1 else 0)
  have he : (fun ω => if ω e = b then (if P ω then (1:ℝ) else 0) else 0) =
      fun ω => if P ω then 1 else 0 := by
    funext ω
    by_cases hp : P ω
    · simp [hp,hb ω hp]
    · simp [hp]
  erw [he] at hh
  exact hh

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_WiredEvent
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
open FiniteProduct

variable {V E : Type*} (G : BondGraph V E)

lemma wiredEvent_mono (a s t : V) :
    ∀ (ω ω' : Set E), ω ⊆ ω' → G.wiredEvent a s t ω → G.wiredEvent a s t ω' := by
  intro ω ω' h hF
  exact hF.mono (sup_le_sup_right (G.openGraph_mono h) _)

lemma earlier_pivot_iff (a s t : V) (ω : Set E) :
    (G.wiredEvent a s t ω ∧ ¬(G.openGraph ω).Reachable a t) ↔ G.joinedPair a s t ω := by
  dsimp [wiredEvent,joinedPair,isolateThree]
  constructor
  · rintro ⟨hf,hat⟩
    have hst : (G.openGraph ω).Reachable s t := by
      rcases (Wiring.reachable_sup_edge (G.openGraph ω) a s a t).mp hf with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact (hat h).elim
      · exact h
      · exact (hat h).elim
    exact ⟨⟨fun has => hat (has.trans hst),hat⟩,hst⟩
  · rintro ⟨⟨_,hat⟩,hst⟩
    exact ⟨(Wiring.reachable_sup_edge (G.openGraph ω) a s a t).mpr
      (Or.inr (Or.inl ⟨.refl _,hst⟩)),hat⟩

lemma reachable_force_rewire (e : E) (s v b x y : V) (ω : Set E)
    (he : G.ends e = s(v,b)) (hv : (G.openGraph ω).Reachable s v) :
    (G.openGraph (Function.update ω e True)).Reachable x y ↔
      ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable x y := by
  rw [G.openGraph_force_true ω e v b he]
  exact Wiring.reachable_replace_tail _ s v b x y hv

lemma wired_force_rewire (e : E) (a s t v b : V) (ω : Set E)
    (he : G.ends e = s(v,b)) (hv : (G.openGraph ω).Reachable s v) :
    G.wiredEvent a s t (Function.update ω e True) ↔
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t := by
  dsimp only [wiredEvent]
  rw [G.openGraph_force_true ω e v b he,sup_right_comm]
  exact Wiring.reachable_replace_tail _ s v b a t (hv.mono le_sup_left)

lemma phase_pair_force (e : E) (a s t v b : V) (ω : Set E)
    (he : G.ends e = s(v,b)) (hv : (G.openGraph ω).Reachable s v) (hclosed : ¬ω e) :
    (G.joinedPair a s t (Function.update ω e True) ∧
      openPivot (G.wiredEvent a s t) e (Function.update ω e True)) ↔
    (((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) := by
  erw [← G.earlier_pivot_iff,openPivot_force_true,G.wired_force_rewire e a s t v b ω he hv,
    G.reachable_force_rewire e s v b a t ω he hv]
  have hu : Function.update ω e False = ω := by
    have hb : ω e = False := propext (iff_false_intro hclosed)
    rw [← hb]
    exact Function.update_eq_self _ _
  rw [hu]
  dsimp only [wiredEvent]
  tauto

variable [Fintype E]

lemma phase_delta_rewire (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    delta w (G.wiredEvent a s t) e =
      prob (pin w e False) (fun ω =>
        ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t) := by
  rw [delta_eq_pivotal w hw e he0 he1 _ (G.wiredEvent_mono a s t)]
  apply prob_congr_support
  intro ω hω
  rw [G.wired_force_rewire e a s t v b ω he (hv ω hω)]
  rfl

lemma phase_pair_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    prob w (fun ω => G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω) =
      w e True * prob (pin w e False) (fun ω =>
        ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) := by
  rw [prob_requires_bit w e True _ (fun ω h => propext (iff_true_intro h.2.1)),
    prob_pin_transport w hw e False True he0 he1]
  congr 1
  apply prob_congr_support
  intro ω hω
  have hb := density_pin_support w e False ω hω
  exact G.phase_pair_force e a s t v b ω he (hv ω hω) (by simp only [hb,not_false_eq_true])

lemma phase_avoid_rewire (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    prob (pin w e True) (G.isolateThree a s t) =
      prob (pin w e False) (fun ω =>
        ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) := by
  rw [prob_pin_transport w hw e False True he0 he1]
  apply prob_congr_support
  intro ω hω
  dsimp only [isolateThree]
  rw [G.reachable_force_rewire e s v b a s ω he (hv ω hω),
    G.reachable_force_rewire e s v b a t ω he (hv ω hω)]

lemma phase_target_rewire (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    prob (pin w e True) (G.joinedPair a s t) =
      prob (pin w e False) (fun ω =>
        ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t ∧
          ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable s t) := by
  rw [prob_pin_transport w hw e False True he0 he1]
  apply prob_congr_support
  intro ω hω
  dsimp only [joinedPair,isolateThree]
  rw [G.reachable_force_rewire e s v b a s ω he (hv ω hω),
    G.reachable_force_rewire e s v b a t ω he (hv ω hω),
    G.reachable_force_rewire e s v b s t ω he (hv ω hω)]
  tauto

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_PhaseStepCharge
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
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma phase_step_charge (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (e : E) (a s t v b : V)
    (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (he0 : w e False = 1-p) (he1 : w e True = p)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    (1-p)*delta w (G.wiredEvent a s t) e *
      prob w (fun ω => G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω) ≤
    potential w (G.isolateThree a s t) (G.joinedPair a s t) -
      ((1-p)*potential (pin w e False) (G.isolateThree a s t) (G.joinedPair a s t) +
      p*potential (pin w e True) (G.isolateThree a s t) (G.joinedPair a s t)) := by
  have h0 : w e False ≠ 0 := by rw [he0]; exact (sub_pos.mpr hp.2).ne'
  have h1 : w e True ≠ 0 := by rw [he1]; exact hp.1.ne'
  rw [potential_split w hn e _ _ (fun _ h => h.1) hp.1 hp.2 he0 he1,
    G.phase_delta_rewire w hw e h0 h1 a s t v b he hv,
    G.phase_pair_mass w hw e h0 h1 a s t v b he hv,he1,
    G.phase_avoid_rewire w hw e h0 h1 a s t v b he hv,
    G.phase_target_rewire w hw e h0 h1 a s t v b he hv]
  have hh := G.wired_pair_charge (pin w e False) (pin_normalized w hw e False)
    (pin_nonneg w hn e False) a s t b has hat hst hp
  dsimp only at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CriticalPercolation.BondGraph

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

theorem phase_score_bound {V : Type*} [Fintype V] (G : BondGraph V E) (a s t : V)
    (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (T : SearchTree E R) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (hT : T.PhaseAdmissible G s p w) :
    expect w (fun ω => if G.joinedPair a s t ω then T.score p (G.wiredEvent a s t) w ω else 0) ≤
      potential w (G.isolateThree a s t) (G.joinedPair a s t) := by
  induction T generalizing w with
  | done r =>
    simp only [score,ite_self]
    rw [expect_const w hw 0]
    exact potential_nonneg w hn _ _ (fun _ h => h.1)
  | ask e l r ihl ihr =>
    rcases hT with ⟨he0,he1,⟨v,b,he,hv⟩,hl,hr⟩
    have hb := G.phase_step_charge w hw hn e a s t v b has hat hst hp he0 he1 he hv
    have hlb := ihl (pin w e False) (pin_normalized w hw e False) (pin_nonneg w hn e False) hl
    have hrb := ihr (pin w e True) (pin_normalized w hw e True) (pin_nonneg w hn e True) hr
    have heq : (fun ω => if G.joinedPair a s t ω then
        (.ask e l r : SearchTree E R).score p (G.wiredEvent a s t) w ω else 0) =
      (fun ω => (1-p)*delta w (G.wiredEvent a s t) e *
          (if G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω then 1 else 0) +
        if ω e then
          (if G.joinedPair a s t ω then r.score p (G.wiredEvent a s t) (pin w e True) ω else 0)
        else (if G.joinedPair a s t ω then l.score p (G.wiredEvent a s t) (pin w e False) ω else 0)) := by
      funext ω
      by_cases hR : G.joinedPair a s t ω <;>
        by_cases heP : openPivot (G.wiredEvent a s t) e ω <;>
        by_cases hx : ω e <;> simp [score,hR,heP,hx]
    erw [heq,expect_add,expect_const_mul,expect_prop_ite,he0,he1]
    have hcharge : (1-p)*delta w (G.wiredEvent a s t) e *
        (expect w (fun ω => if G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω then 1 else 0)) ≤
        potential w (G.isolateThree a s t) (G.joinedPair a s t) -
        ((1-p)*potential (pin w e False) (G.isolateThree a s t) (G.joinedPair a s t) +
        p*potential (pin w e True) (G.isolateThree a s t) (G.joinedPair a s t)) := by
      convert hb using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      unfold prob
      congr 1
      funext ω
      by_cases h : G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω <;> simp [h]
    have hh0 := mul_le_mul_of_nonneg_left hlb (sub_nonneg.mpr hp.2.le)
    have hh1 := mul_le_mul_of_nonneg_left hrb hp.1.le
    linarith! only [hcharge,hh0,hh1]

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

theorem compile_phaseAdmissible_in (G H : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (s : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (w : E → Prop → ℝ)
    (hf : Fresh w p st.read) (ht : SupportedTails H s w stack)
    (hends : ∀ e ∉ st.read, G.ends e = H.ends e) :
    (compile G order B fuel st stack).PhaseAdmissible H s p w := by
  induction fuel generalizing st stack w with
  | zero => trivial
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hhit
    · trivial
    cases stack with
    | nil => trivial
    | cons d rest =>
      dsimp only
      split_ifs with hskip
      · exact ih st rest w hf (fun d hd => ht d (List.mem_cons_of_mem _ hd)) hends
      · have hd : d.2.2 ∉ st.reached ∧ d.2.1 ∉ st.read ∧ d.1 ∈ st.reached ∧
            G.ends d.2.1 = s(d.1,d.2.2) := by
          push Not at hskip
          exact hskip
        have hbits := hf d.2.1 hd.2.1
        have h0 : w d.2.1 False ≠ 0 := by rw [hbits.1]; exact (sub_pos.mpr hp.2).ne'
        have h1 : w d.2.1 True ≠ 0 := by rw [hbits.2]; exact hp.1.ne'
        have htail : ∀ ω, density (pin w d.2.1 False) ω ≠ 0 →
            (H.openGraph ω).Reachable s d.1 := by
          intro ω hω
          exact ht d (List.mem_cons_self) ω (density_pin_old_support w _ False ω h0 hω)
        refine ⟨hbits.1,hbits.2,⟨d.1,d.2.2,(hends d.2.1 hd.2.1).symm.trans hd.2.2.2,htail⟩,?_,?_⟩
        · apply ih (st.closed d.2.1) rest (pin w d.2.1 False)
          · exact fresh_pin w p st.read hf _ False
          · intro c hc ω hω
            exact ht c (List.mem_cons_of_mem _ hc) ω (density_pin_old_support w _ False ω h0 hω)
          · intro j hj
            exact hends j (fun hh => hj (Finset.mem_insert_of_mem hh))
        · apply ih (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest) (pin w d.2.1 True)
          · exact fresh_pin w p st.read hf _ True
          · intro c hc ω hω
            have hω' := density_pin_old_support w _ True ω h1 hω
            rcases List.mem_append.mp hc with hc | hc
            · have hc0 : c.1 = d.2.2 := (of_decide_eq_true (List.mem_filter.mp hc).2).1
              rw [hc0]
              apply (ht d (List.mem_cons_self) ω hω').trans
              apply prop_openEdge_reachable H ω _ ((hends d.2.1 hd.2.1).symm.trans hd.2.2.2)
              have hb := density_pin_support w _ True ω hω
              exact of_eq_true hb
            · exact ht c (List.mem_cons_of_mem _ hc) ω hω'

          · intro j hj
            exact hends j (fun hh => hj (Finset.mem_insert_of_mem hh))

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_EraseBond
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

variable {V E : Type*} (G : BondGraph V E)

lemma eraseBond_ends_ne (f : E) (o : V) {e : E} (he : e ≠ f) :
    (G.eraseBond f o).ends e = G.ends e := by simp [eraseBond,he]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ListScore
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

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem young_phase_score_bound_bs_oai (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (f : E) (a s t : V) (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (fuel : ℕ) (st : State V E)
    (hf : f ∈ st.read) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (fresh : Fresh w p st.read) :
    let H := G.eraseBond f a
    let T := compile G order B fuel st (push G order s)
    expect w (fun ω => if H.joinedPair a s t ω then T.score p (H.wiredEvent a s t) w ω else 0) ≤
      prob w (H.joinedPair a s t) := by
  dsimp only
  apply le_trans (SearchTree.phase_score_bound (G.eraseBond f a) a s t has hat hst hp
    _ w hw hn ?_) (potential_le w hn _ _)
  apply compile_phaseAdmissible_in G (G.eraseBond f a) order B s hp fuel st _ w fresh
  · intro d hd ω _
    have hds : d.1 = s := (of_decide_eq_true (List.mem_filter.mp hd).2).1
    rw [hds]
  · intro e he
    apply (G.eraseBond_ends_ne f a _).symm
    exact fun hef => he (hef ▸ hf)

end CriticalPercolation.LazyDFS

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.LazyDFS.young_phase_score_bound_bs_oai.{u_1, u_2}
