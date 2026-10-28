-- Prove2me | solution 1 for OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:08:44.938267+00:00
-- url     : https://prove2.me/submissions/f41f2c9b-c1b6-4675-af40-baf99e7e8b2a

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_configuration_entropy_bs
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_pair_entropy_bs
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_selected_density_le_bs
import Theorems.Thm_OAI_CriticalPercolation_ExactExposure_marked_pair_bound_bs

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

lemma openBond_roots {ω : Set E} {S : Set V} {e : E} (he : e ∈ ω)
    {v w : V} (hv : v ∈ G.ends e) (hw : w ∈ G.ends e)
    (hr : v ∈ roots (G.openGraph ω) S) : w ∈ roots (G.openGraph ω) S := by
  by_cases hvw : v = w
  · simpa [← hvw] using hr
  · have heq : G.ends e = s(v,w) := Sym2.eq_of_ne_mem hvw hv hw (by simp) (by simp)
    exact roots_closed hr ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e, he, heq⟩, hvw⟩)

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

end Wiring
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_ForceFalseSubset
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

lemma force_false_subset (ω : Set E) (e : E) :
    ∀ f, Function.update ω e False f → ω f := by
  intro f hf
  by_cases he : f = e
  · subst f; erw [Function.update_self] at hf; exact hf.elim
  · erw [Function.update_of_ne he] at hf; exact hf

lemma reachable_force_false_of_not_reachable (G : BondGraph V E) (ω : Set E)
    (e : E) (r : V) (hr : r ∈ G.ends e) {x y : V}
    (hxr : ¬(G.openGraph ω).Reachable x r) (hxy : (G.openGraph ω).Reachable x y) :
    (G.openGraph (Function.update ω e False)).Reachable x y := by
  have hh := ((G.openGraph ω).reachable_iff_reflTransGen x y).mp hxy
  clear hxy
  induction hh with
  | refl => exact .refl _
  | @tail v y hpath hvy ih =>
    have hxv := ((G.openGraph ω).reachable_iff_reflTransGen x v).mpr hpath
    obtain ⟨⟨f,hf,hfe⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvy
    have hfe' : f ≠ e := by
      intro he
      subst f
      have : r = v ∨ r = y := by simpa only [hfe,Sym2.mem_iff] using hr
      rcases this with rfl | rfl
      · exact hxr hxv
      · exact hxr (hxv.trans hvy.reachable)
    apply ih.trans
    apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨⟨f,?_,hfe⟩,hne⟩
    change Function.update ω e False f
    erw [Function.update_of_ne hfe']
    exact hf

lemma target_after_open_iff (G : BondGraph V E) (ω : Set E) (B : Set V)
    (a u v : V) (f : E) (hf : G.ends f = s(u,v))
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (hva : ¬(G.openGraph ω).Reachable a v) :
    (∃ b ∈ B, (G.openGraph (Function.update ω f True)).Reachable a b) ↔
      (G.openGraph ω).Reachable a u := by
  have updated : (Function.update ω f True : Set E) = insert f ω := by
    ext bond
    by_cases equal : bond = f
    · subst bond
      erw [Function.update_self]
      exact iff_of_true trivial (Set.mem_insert f ω)
    · erw [Function.update_of_ne equal]
      change bond ∈ ω ↔ bond ∈ insert f ω
      simp [equal]
  have forced : G.openGraph (Function.update ω f True) =
      G.openGraph ω ⊔ SimpleGraph.edge u v := by
    erw [updated]
    rw [openGraph, Set.image_insert_eq, hf, ← Set.singleton_union,
      SimpleGraph.fromEdgeSet_union]
    exact sup_comm _ _
  rw [forced]
  constructor
  · rintro ⟨b,hb,hab⟩
    rcases (Wiring.reachable_sup_edge (G.openGraph ω) u v a b).mp hab with h | ⟨h,_⟩ | ⟨h,_⟩
    · exact (hn ⟨b,hb,h⟩).elim
    · exact h
    · exact (hva h).elim
  · intro hau
    obtain ⟨b,hb,hvb⟩ := hv
    exact ⟨b,hb,(Wiring.reachable_sup_edge (G.openGraph ω) u v a b).mpr
      (Or.inr (Or.inl ⟨hau,hvb⟩))⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ReachableIncidenceImp
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

lemma reachable_of_incidence_imp (G : BondGraph V E) (ω η : Set E) (a : V)
    (h : ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v) → η e → ω e)
    {b : V} (hab : (G.openGraph η).Reachable a b) : (G.openGraph ω).Reachable a b := by
  have hp := ((G.openGraph η).reachable_iff_reflTransGen a b).mp hab
  clear hab
  induction hp with
  | refl => exact .refl _
  | @tail v b _ hvb ih =>
    obtain ⟨⟨e,he,hee⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvb
    have hv : v ∈ G.ends e := by simp [hee]
    have hadj : (G.openGraph ω).Adj v b :=
      (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,h e ⟨v,hv,ih⟩ he,hee⟩,hne⟩
    exact ih.trans hadj.reachable

lemma reachable_incidence_congr (G : BondGraph V E) (ω η : Set E) (a : V)
    (h : ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v) → (ω e ↔ η e))
    (b : V) : (G.openGraph ω).Reachable a b ↔ (G.openGraph η).Reachable a b := by
  have hback : ∀ b, (G.openGraph η).Reachable a b → (G.openGraph ω).Reachable a b :=
    fun _ => G.reachable_of_incidence_imp ω η a (fun e he => (h e he).mpr)
  constructor
  · apply G.reachable_of_incidence_imp η ω a
    intro e he
    exact (h e (by obtain ⟨v,hv,har⟩ := he; exact ⟨v,hv,hback v har⟩)).mp
  · exact hback b

lemma reachable_delete_incidence_congr (G : BondGraph V E) (ω η : Set E) (a : V)
    (h : ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v) → (ω e ↔ η e))
    (e : E) (b : V) :
    (G.openGraph (Function.update ω e False)).Reachable a b ↔
      (G.openGraph (Function.update η e False)).Reachable a b := by
  apply G.reachable_incidence_congr
  intro f hf
  by_cases hfe : f = e
  · subst f; erw [Function.update_self,Function.update_self]
  · erw [Function.update_of_ne hfe,Function.update_of_ne hfe]
    obtain ⟨v,hv,har⟩ := hf
    exact h f ⟨v,hv,G.reachable_of_incidence_imp ω (Function.update ω e False) a
      (fun edge _ => force_false_subset ω e edge) har⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchTree
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

namespace CriticalPercolation

namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]

lemma compile_valid (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) :
    (compile G order B fuel st stack).Valid st.read := by
  induction fuel generalizing st stack with
  | zero => trivial
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · trivial
    · cases stack with
      | nil => trivial
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest
        · exact ⟨fun he => hd (Or.inr (Or.inl he)), ih _ _, ih _ _⟩

end LazyDFS
end CriticalPercolation

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

end CriticalPercolation.FiniteProduct

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

namespace CriticalPercolation.BondGraph
variable {V E : Type*}

lemma openGraph_force_false_of_closed (G : BondGraph V E) (ω : Set E) (e : E)
    (he : ¬ω e) : G.openGraph (Function.update ω e False) = G.openGraph ω := by
  have hu : Function.update ω e False = ω := by
    have hb : ω e = False := propext (iff_false_intro he)
    rw [← hb]
    exact Function.update_eq_self _ _
  rw [hu]

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_Variance
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

lemma prob_true (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) :
    prob w (fun _ => True) = 1 := by
  simpa only [prob, if_true] using expect_const w hw 1

lemma prob_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : prob w F ≤ 1 := by
  exact (prob_mono w hn (fun _ _ => True.intro)).trans_eq (prob_true w hw)

lemma delta_unit (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    0 ≤ delta w F e ∧ delta w F e ≤ 1 := by
  rw [delta_eq_pivotal w hw e h0 h1 F hF]
  exact ⟨prob_nonneg _ (pin_nonneg w hn e False) _,
    prob_le_one _ (pin_normalized w hw e False) (pin_nonneg w hn e False) _⟩

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CutEdgesSubsetIncident
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

lemma cutEdges_subset_incidentEdges (G : BondGraph V E) (O : Set V) :
    G.cutEdges O ⊆ G.incidentEdges O := by
  rintro e ⟨x,y,he,_,hy⟩
  exact ⟨y,hy,by simp [he]⟩

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ForceClosed
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

variable {E : Type*}

variable [Fintype E]

omit [Fintype E] in
lemma homogeneous_normalized (w : E → Prop → ℝ) (p : ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e, ∑ b, w e b = 1 := by
  intro e
  simp [Fintype.univ_Prop,h0,h1]

omit [Fintype E] in
lemma homogeneous_positive (w : E → Prop → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    ∀ e b, 0 < w e b := by
  intro e b
  by_cases hb : b
  · have : b = True := propext (iff_true_intro hb)
    rw [this,h1]; exact hp.1
  · have : b = False := propext (iff_false_intro hb)
    rw [this,h0]; exact sub_pos.mpr hp.2

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryDelta
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

lemma queryDelta_update (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop) :
    T.queryDelta F w (Function.update ω e b) e = T.queryDelta F w ω e := by
  induction T generalizing w with
  | done _ => rfl
  | ask f l r hl hr =>
    simp only [queryDelta]
    by_cases he : e = f
    · simp only [ite_eq_left he]
    · have hfe : f ≠ e := Ne.symm he
      simp only [ite_eq_right he]
      erw [Function.update_of_ne hfe]
      split_ifs <;> first | exact hr _ | exact hl _

lemma queryDelta_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) : 0 ≤ T.queryDelta F w ω e := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    simp only [queryDelta]
    split_ifs
    · exact (delta_unit w hw hn f hf0 hf1 F hF).1
    · exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
        (fresh_pin w p used hf f True)
    · exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
        (fresh_pin w p used hf f False)

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma clusterObject_cut_closed (ω : Set E) (S : Set V) :
    ∀ e ∈ G.cutEdges (G.clusterObject ω S).1, ¬(G.clusterObject ω S).2 e := by
  rintro e ⟨x,y,he,hx,hy⟩ ⟨hω,_⟩
  exact hx (G.openBond_roots hω (by simp [he] : y ∈ G.ends e)
    (by simp [he] : x ∈ G.ends e) hy)

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma contactWeight_nonneg (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Prop) (e : E) :
    0 ≤ G.contactWeight order B O a p w ω e := by
  unfold contactWeight
  split_ifs
  · apply mul_nonneg hp.1.le
    apply queryDelta_nonneg _ ∅ (LazyDFS.compile_valid G order B _ _ _) hp _ _ w
      (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
      (fun e _ => ⟨h0 e,h1 e⟩)
    rintro s t hst ⟨b,hb,hr⟩
    exact ⟨b,hb,hr.mono (G.openGraph_mono hst)⟩
  · exact le_rfl

lemma contactKernel_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (C : ClusterObject V E)
    (ω : E → Prop) (mark : Option E) :
    0 ≤ G.contactKernel order B a p w C ω mark := by
  unfold contactKernel
  by_cases ha : a ∈ C.1
  · rw [ite_eq_left ha]
    split_ifs <;> norm_num
  · rw [ite_eq_right ha]
    cases mark with
    | none => exact le_rfl
    | some e =>
      exact div_nonneg (G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e)
        (prob_nonneg w (fun e b => (homogeneous_positive w hp h0 h1 e b).le) _)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

universe uE

lemma anchors_length {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (anchors d x n h).length = n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [anchors,List.length_append,List.length_singleton,ih]

lemma firstIndex_spec {P : ℕ → Prop} (h : ∃ j, P j) : P (firstIndex P) := by
  rw [firstIndex,dite_eq_left h]
  exact Nat.find_spec h

lemma firstIndex_le {P : ℕ → Prop} {j : ℕ} (hj : P j) : firstIndex P ≤ j := by
  rw [firstIndex,dite_eq_left ⟨j,hj⟩]
  exact Nat.find_min' _ hj

variable {V E : Type*} (G : BondGraph V E)

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma density_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hr₀ : ∀ ω, 0 ≤ r₀ ω) (n : ℕ) (h : History E n)
    (ω : E → Prop) : 0 ≤ density G order d x p w r₀ n h ω := by
  induction n with
  | zero => exact hr₀ ω
  | succ n ih =>
    rw [density]
    split_ifs
    · exact mul_nonneg (ih h.1) (G.contactKernel_nonneg order _ _ hp w h0 h1 _ ω _)
    · exact le_rfl

end Density

section Seed
variable [Fintype V] [Fintype E]

lemma seed_nonneg (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) (ω : E → Prop) : 0 ≤ seed G w u v s ω := by
  unfold seed
  apply mul_nonneg (inv_nonneg.mpr hδ.le)
  split_ifs <;> norm_num

end Seed

section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma kernel_parent_exists (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0) :
    ∃ j, parentPredicate G (anchors d x n h) a ω m j := by
  by_cases ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1
  · have hm : m=none := by
      by_contra hm
      simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
      exact hk rfl
    subst m
    obtain ⟨v,⟨b,hb⟩,hr⟩ := ha
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    exact ⟨j,(v,b),hj,hr.symm⟩
  · cases m with
    | none => simp only [contactKernel,ite_eq_right ha] at hk; exact (hk rfl).elim
    | some e =>
      have he : e ∈ G.cutEdges (G.clusterObject ω (anchorSet d x n h)).1 := by
        by_contra he
        simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
        exact hk rfl
      obtain ⟨u,v,heq,-,z,⟨b,hb⟩,hr⟩ := he
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
      refine ⟨j,(z,b),hj,v,?_,hr⟩
      simp [heq]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma parent_lt_of_exists (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (h : ∃ j, parentPredicate G L a ω m j) : parent G L a ω m < L.length := by
  obtain ⟨z,hz,-⟩ := firstIndex_spec h
  exact (List.getElem?_eq_some_iff.mp hz).1

lemma density_step_support (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)
    (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    density G order d x p w r₀ n h.1 ω ≠ 0 ∧
    G.contactKernel order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
      (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2 ≠ 0 ∧
    side G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 = h.2.1 := by
  rw [density] at hr
  split_ifs at hr with hs
  · exact ⟨(mul_ne_zero_iff.mp hr).1,(mul_ne_zero_iff.mp hr).2,hs⟩
  · exact (hr rfl).elim

end ExactLaw

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySupport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*} (G : BondGraph V E)

lemma consistent_append (L : List (V × Bool)) (ω : Set E) (hL : Consistent G L ω)
    (a : V) (b : Bool) (hnew : ∀ z ∈ L, (G.openGraph ω).Reachable a z.1 → b=z.2) :
    Consistent G (L++[(a,b)]) ω := by
  intro z hz t ht hr
  rcases List.mem_append.mp hz with hz|hz <;> rcases List.mem_append.mp ht with ht|ht
  · exact hL z hz t ht hr
  · have he := List.mem_singleton.mp ht
    subst t
    exact (hnew z hz hr.symm).symm
  · have he := List.mem_singleton.mp hz
    subst z
    exact hnew t ht hr
  · have he := List.mem_singleton.mp hz
    subst z
    have he := List.mem_singleton.mp ht
    subst t
    rfl

lemma consistent_bases (u v : V) (ω : Set E) (h : ¬(G.openGraph ω).Reachable u v) :
    Consistent G [(u,true),(v,false)] ω := by
  intro z hz t ht hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz ht
  rcases hz with rfl|rfl <;> rcases ht with rfl|rfl
  · rfl
  · exact (h hr).elim
  · exact (h hr.symm).elim
  · rfl

section Kernel
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma kernel_colour_consistent (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (a : V)
    (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order (anchorSet d x n h) a p w
      (G.clusterObject ω (anchorSet d x n h)) ω m ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (z : V × Bool) (hz : z ∈ anchors d x n h) (hr : (G.openGraph ω).Reachable a z.1) :
    side G (anchors d x n h) a ω m = z.2 := by
  have ha : a ∈ (G.clusterObject ω (anchorSet d x n h)).1 := ⟨z.1,⟨z.2,hz⟩,hr.symm⟩
  have hm : m=none := by
    by_contra hm
    simp only [contactKernel,ite_eq_left ha,ite_eq_right hm] at hk
    exact hk rfl
  subst m
  have hex := kernel_parent_exists G order d x n h a p w ω none hk
  obtain ⟨t,ht,hreach⟩ := firstIndex_spec hex
  have hparent : (anchors d x n h)[parent G (anchors d x n h) a ω none]? = some t := ht
  have hside : side G (anchors d x n h) a ω none = t.2 := by
    simp only [side,hparent,Option.getD_some]
  rw [hside]
  exact hL t (List.mem_of_getElem? ht) z hz (hreach.symm.trans hr)

lemma density_consistent (order : List (LazyDFS.Dart V E))
    (d : ℕ) (x : ℕ → V) (p : ℝ) (w : E → Prop → ℝ) (s : ℕ)
    (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    Consistent G (anchors d x n h) ω := by
  induction n with
  | zero =>
    have hE : endpointEvent G (x 0) (x d) s ω := by
      by_contra hE
      simp only [density,seed,ite_eq_right hE,mul_zero] at hr
      exact hr rfl
    exact consistent_bases G _ _ ω hE.1
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w _ n h ω hr
    have hL := ih h.1 hprev
    apply consistent_append G _ ω hL
    intro z hz hzreach
    rw [←hs]
    exact kernel_colour_consistent G order d x n h.1 _ p w ω _ hk hL z hz hzreach

end Kernel

lemma endpoint_labels (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (x (interval d n h).1,true) ∈ anchors d x n h ∧
      (x (interval d n h).2,false) ∈ anchors d x n h := by
  induction n with
  | zero => constructor <;> simp [anchors,interval]
  | succ n ih =>
    have hi := ih h.1
    by_cases ht : (interval d n h.1).2 ≤ (interval d n h.1).1+1
    · constructor
      · exact List.mem_append_left _ (by simpa only [interval,bisect,ite_eq_left ht] using hi.1)
      · exact List.mem_append_left _ (by simpa only [interval,bisect,ite_eq_left ht] using hi.2)
    · cases hb : h.2.1 <;>
        simp only [interval,bisect,hb,Bool.false_eq_true,↓reduceIte,anchors,
          List.mem_append,List.mem_singleton,nextIndex,ite_eq_right ht] <;>
        simp_all only [or_true,true_or,and_self]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_AncestryForest
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest

namespace Forest
variable (F : Forest)

lemma lineage_base {n : ℕ} (h : n < 2) : F.lineage n = [n] := by
  rw [lineage, dite_eq_left h]

lemma lineage_step {n : ℕ} (h : 2 ≤ n) : F.lineage n = n :: F.lineage (F.parent n) := by
  rw [lineage, dite_eq_right (by omega : ¬n<2)]

lemma self_mem_lineage (n : ℕ) : n ∈ F.lineage n := by
  rw [lineage]
  split_ifs <;> simp

lemma mem_lineage_le {a n : ℕ} (h : a ∈ F.lineage n) : a ≤ n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a = n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      exact he.le
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact le_rfl
      · exact (ih (F.parent n) (F.parent_lt n (by omega)) h).trans
          (F.parent_lt n (by omega)).le

lemma root_base {n : ℕ} (h : n < 2) : F.root n = n := by
  rw [root, dite_eq_left h]

lemma root_step {n : ℕ} (h : 2 ≤ n) : F.root n = F.root (F.parent n) := by
  rw [root, dite_eq_right (by omega : ¬n<2)]

lemma root_lt_two (n : ℕ) : F.root n < 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simpa only [F.root_base hn] using hn
    · rw [F.root_step (by omega : 2 ≤ n)]
      exact ih _ (F.parent_lt n (by omega))

lemma root_mem_lineage (n : ℕ) : F.root n ∈ F.lineage n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < 2
    · simp [F.root_base hn,F.lineage_base hn]
    · rw [F.root_step (by omega : 2 ≤ n),F.lineage_step (by omega : 2 ≤ n)]
      exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)))

lemma root_eq_of_mem {a n : ℕ} (h : a ∈ F.lineage n) : F.root a = F.root n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · rfl
      · rw [F.root_step (by omega : 2 ≤ n)]
        exact ih _ (F.parent_lt n (by omega)) h

lemma lineage_subset_of_mem {a n : ℕ} (h : a ∈ F.lineage n) :
    F.lineage a ⊆ F.lineage n := by
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases hn : n < 2
    · have he : a=n := by simpa only [F.lineage_base hn,List.mem_singleton] using h
      rw [he]; exact List.Subset.refl _
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at h
      rcases h with rfl|h
      · exact List.Subset.refl _
      · intro b hb
        rw [F.lineage_step (by omega : 2 ≤ n)]
        exact List.mem_cons_of_mem _ (ih _ (F.parent_lt n (by omega)) h hb)

lemma parent_mem_lineage {a n : ℕ} (ha : 2 ≤ a) (h : a ∈ F.lineage n) :
    F.parent a ∈ F.lineage n := by
  apply F.lineage_subset_of_mem h
  rw [F.lineage_step ha]
  exact List.mem_cons_of_mem _ (F.self_mem_lineage _)

end Forest
end CriticalPercolation.InterpolationForest

namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

lemma mem_active {u v a : ℕ} : a ∈ F.active u v ↔
    (a ∈ F.lineage u ∨ a ∈ F.lineage v) ∧ 2 ≤ a := by
  simp [active]

lemma active_parent {u v a : ℕ} (ha : a ∈ F.active u v) :
    F.parent a < 2 ∨ F.parent a ∈ F.active u v := by
  by_cases hp : F.parent a < 2
  · exact Or.inl hp
  · apply Or.inr
    rw [mem_active] at ha ⊢
    exact ⟨ha.1.imp (F.parent_mem_lineage ha.2) (F.parent_mem_lineage ha.2),by omega⟩

lemma previous_lineage_le_parent {n a b : ℕ} (ha : a ∈ F.lineage n)
    (hb : b ∈ F.lineage n) (ha2 : 2 ≤ a) (hba : b < a) : b ≤ F.parent a := by
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
    by_cases hn : n < 2
    · have := F.mem_lineage_le ha
      omega
    · rw [F.lineage_step (by omega : 2 ≤ n),List.mem_cons] at ha hb
      rcases ha with rfl|ha <;> rcases hb with rfl|hb
      · omega
      · exact F.mem_lineage_le hb
      · have := F.mem_lineage_le ha
        have := F.parent_lt b (by omega : 2 ≤ b)
        omega
      · exact ih _ (F.parent_lt n (by omega)) ha hb ha2 hba

theorem previous_active_le_parent {u v a b : ℕ} (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) (hb : b ∈ F.active u v)
    (hside : F.root a = F.root b) (hba : b < a) : b ≤ F.parent a := by
  rw [mem_active] at ha hb
  rcases ha.1 with hau|hav <;> rcases hb.1 with hbu|hbv
  · exact F.previous_lineage_le_parent hau hbu ha.2 hba
  · exact (huv ((F.root_eq_of_mem hau).symm.trans (hside.trans (F.root_eq_of_mem hbv)))).elim
  · exact (huv ((F.root_eq_of_mem hbu).symm.trans (hside.symm.trans (F.root_eq_of_mem hav)))).elim
  · exact F.previous_lineage_le_parent hav hbv ha.2 hba

end CriticalPercolation.InterpolationForest.Forest
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryForest
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma nodeParent_old (d : ℕ) (x : ℕ → V) (ω : Set E) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : nodeParent G d x ω (n+1) h i = nodeParent G d x ω n h.1 i := by
  rw [nodeParent,ite_eq_right (by omega : i≠n+2)]

lemma node_old (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1))
    (i : ℕ) (hi : i < n+2) : node d x (n+1) h i = node d x n h.1 i := by
  change ((anchors d x n h.1 ++ [_])[i]?).getD _ = _
  rw [List.getElem?_append_left (by simpa only [anchors_length] using hi)]
  rfl

lemma node_current (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1)) :
    node d x (n+1) h (n+2) = (x (nextIndex d n h.1),h.2.1) := by
  unfold node anchors
  rw [List.getElem?_append_right (by simp [anchors_length])]
  simp only [anchors_length,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some]

lemma node_getElem? (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    (anchors d x n h)[i]? = some (node d x n h i) := by
  have hil : i<(anchors d x n h).length := by simpa only [anchors_length] using hi
  simp only [node,List.getElem?_eq_getElem hil,Option.getD_some]

lemma node_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (i : ℕ) (hi : i < n+2) :
    node d x n h i ∈ anchors d x n h := List.mem_of_getElem? (node_getElem? d x n h i hi)

lemma node_bases (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    node d x n h 0 = (x 0,true) ∧ node d x n h 1 = (x d,false) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [node_old d x n h 0 (by omega),node_old d x n h 1 (by omega)]
    exact ih h.1

section Support
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_current (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    nodeParent G d x ω (n+1) h (n+2) =
      parent G (anchors d x n h.1) (x (nextIndex d n h.1)) ω h.2.2 := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hp := parent_lt_of_exists G _ _ ω _
    (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
  rw [anchors_length] at hp
  simp only [nodeParent,if_true,ite_eq_left hp]

lemma node_colour_parent (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    (node d x n h i).2 = (node d x n h (nodeParent G d x ω n h i)).2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i=n+2
    · subst i
      rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr]
      have hp := parent_lt_of_exists G _ _ ω _
        (kernel_parent_exists G order d x n h.1 _ p w ω _ hk)
      rw [anchors_length] at hp
      rw [node_old d x n h _ hp]
      rw [← hs]
      simp only [side,node_getElem? d x n h.1 _ hp,Option.getD_some]
    · have hio : i < n+2 := by omega
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 hprev hio

lemma node_root_colour (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (i : ℕ) (hin : i < n+2) :
    (node d x n h i).2 = if (historyForest G d x ω n h).root i = 0 then true else false := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hi : i < 2
    · rw [Forest.root_base _ hi]
      have hb := node_bases d x n h
      interval_cases i <;> simp only [hb.1,hb.2,if_true,one_ne_zero,if_false]
    · have hi2 : 2 ≤ i := by omega
      rw [Forest.root_step _ hi2]
      rw [node_colour_parent G order d x p w r₀ n h ω hr i hi2 hin]
      exact ih _ (nodeParent_lt G d x ω n h i hi2)
        ((nodeParent_lt G d x ω n h i hi2).trans hin)

end Support

lemma parent_canonical (L : List (V × Bool)) (a : V) (ω : Set E) (m : Option E)
    (hex : ∃ i, parentPredicate G L a ω m i) : Canonical G L ω (parent G L a ω m) := by
  intro j z t hj hz ht hr
  have hs := firstIndex_spec hex
  obtain ⟨v,hv,hpred⟩ := hs
  have hvt : v=t := Option.some.inj (hv.symm.trans ht)
  subst v
  have hP : parentPredicate G L a ω m j := by
    refine ⟨z,hz,?_⟩
    cases m with
    | none => exact hpred.trans hr.symm
    | some e =>
      obtain ⟨u,hu,htu⟩ := hpred
      exact ⟨u,hu,hr.trans htu⟩
  have hle := firstIndex_le hP
  exact (Nat.not_le_of_gt hj) hle

lemma canonical_append (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length)
    (hC : Canonical G L ω i) : Canonical G (L++M) ω i := by
  intro j z t hj hz ht
  rw [List.getElem?_append_left (hj.trans hi)] at hz
  rw [List.getElem?_append_left hi] at ht
  exact hC j z t hj hz ht

section CanonicalSupport
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma nodeParent_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω (nodeParent G d x ω n h i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨hprev,hk,hs⟩ := density_step_support G order d x p w r₀ n h ω hr
    by_cases he : i = n+2
    · subst i
      rw [nodeParent_current G order d x p w r₀ n h ω hr]
      have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
      apply canonical_append
      · exact parent_lt_of_exists G _ _ ω _ hex
      · exact parent_canonical G _ _ ω _ hex
    · have hio : i < n+2 := by omega
      rw [nodeParent_old G d x ω n h i hio]
      apply canonical_append
      · rw [anchors_length]
        exact (nodeParent_lt G d x ω n h.1 i hi).trans hio
      · exact ih h.1 hprev hio

lemma lineage_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (j : ℕ) (hjn : j < n+2) (hj : Canonical G (anchors d x n h) ω j)
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage j) :
    Canonical G (anchors d x n h) ω i := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hj2 : j < 2
    · have he : i=j := by simpa only [Forest.lineage_base _ hj2,List.mem_singleton] using hi
      exact he ▸ hj
    · have hj2' : 2 ≤ j := by omega
      rw [Forest.lineage_step _ hj2',List.mem_cons] at hi
      rcases hi with rfl|hi
      · exact hj
      · exact ih _ (nodeParent_lt G d x ω n h j hj2')
          ((nodeParent_lt G d x ω n h j hj2').trans hjn)
          (nodeParent_canonical G order d x p w r₀ n h ω hr j hj2' hjn) hi

end CanonicalSupport

lemma owner_exists (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    ∃ i, parentPredicate G (anchors d x n h) a ω none i := by
  obtain ⟨b,hb⟩ := ha
  obtain ⟨i,hi⟩ := List.mem_iff_getElem?.mp hb
  exact ⟨i,(a,b),hi,.refl _⟩

lemma owner_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    owner G d x n h ω a < n+2 := by
  have hp := parent_lt_of_exists G _ _ ω none (owner_exists G d x n h ω a ha)
  simpa only [anchors_length,owner] using hp

lemma owner_canonical (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    Canonical G (anchors d x n h) ω (owner G d x n h ω a) :=
  parent_canonical G _ _ ω none (owner_exists G d x n h ω a ha)

lemma owner_reachable (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (ha : ∃ b, (a,b) ∈ anchors d x n h) :
    (G.openGraph ω).Reachable a (node d x n h (owner G d x n h ω a)).1 := by
  obtain ⟨z,hz,hr⟩ := firstIndex_spec (owner_exists G d x n h ω a ha)
  have he : z = node d x n h (owner G d x n h ω a) := Option.some.inj
    (hz.symm.trans (node_getElem? d x n h _ (owner_lt G d x n h ω a ha)))
  exact he ▸ hr

lemma owner_colour (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (a : V) (b : Bool) (ha : (a,b) ∈ anchors d x n h)
    (hL : Consistent G (anchors d x n h) ω) :
    (node d x n h (owner G d x n h ω a)).2 = b :=
  (hL (a,b) ha _ (node_mem d x n h _ (owner_lt G d x n h ω a ⟨b,ha⟩))
    (owner_reachable G d x n h ω a ⟨b,ha⟩)).symm

section Owners
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma terminal_roots (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
    (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).1)) = 0 ∧
    (historyForest G d x ω n h).root (owner G d x n h ω (x (interval d n h).2)) = 1 := by
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl := owner_colour G d x n h ω _ true he.1 hL
  have hr' := owner_colour G d x n h ω _ false he.2 hL
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨true,he.1⟩)] at hl
  rw [node_root_colour G order d x p w _ n h ω hr _
    (owner_lt G d x n h ω _ ⟨false,he.2⟩)] at hr'
  constructor
  · by_contra hz
    simp only [ite_eq_right hz] at hl
    cases hl
  · have hn := (historyForest G d x ω n h).root_lt_two
      (owner G d x n h ω (x (interval d n h).2))
    have hz : (historyForest G d x ω n h).root
        (owner G d x n h ω (x (interval d n h).2)) ≠ 0 := by
      intro hz
      simp only [ite_eq_left hz] at hr'
      cases hr'
    omega

end Owners

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_queryDelta_incident (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (a : V) (e : E)
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v)
    (hq : (compile G order B fuel st stack).queryDelta F w ω e ≠ 0) :
    ∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v := by
  induction fuel generalizing st stack w with
  | zero => exact (hq rfl).elim
  | succ n ih =>
    rw [compile.eq_def] at hq
    dsimp only at hq
    split_ifs at hq with hh
    · exact (hq rfl).elim
    · cases stack with
      | nil => exact (hq rfl).elim
      | cons d rest =>
        dsimp only at hq
        split_ifs at hq with hd
        · exact ih st rest w hst hq
        · have htail : d.1 ∈ st.reached := by
            by_contra ht
            exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht
            exact hd (Or.inr (Or.inr (Or.inr ht)))
          by_cases hef : e=d.2.1
          · subst e
            exact ⟨d.1,by simp [he],hst d.1 htail⟩
          · simp only [queryDelta,ite_eq_right hef] at hq
            by_cases hopen : ω d.2.1
            · rw [ite_eq_left hopen] at hq
              apply ih _ _ _ (fun v hv => ?_) hq
              rcases Finset.mem_insert.mp hv with rfl|hv
              · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
              · exact hst v hv
            · rw [ite_eq_right hopen] at hq
              exact ih (st.closed d.2.1) rest (pin w d.2.1 False) (fun v hv => hst v hv) hq

lemma search_queryDelta_incident [Fintype V] (G : BondGraph V E)
    (order : List (Dart V E)) (B : Set V) (a : V) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (e : E)
    (hq : (search G order a B).queryDelta F w ω e ≠ 0) :
    ∃ v ∈ G.ends e, (G.openGraph ω).Reachable a v := by
  apply compile_queryDelta_incident G order B _ _ _ F w ω a e _ hq
  intro v hv
  have he : v=a := Finset.mem_singleton.mp hv
  subst v
  exact .refl _

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

theorem kernel_contact_geometry (order : List (LazyDFS.Dart V E))
    (S : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) (e : E)
    (hk : G.contactKernel order S a p w (G.clusterObject ω S) ω (some e) ≠ 0) :
    a ∉ (G.clusterObject ω S).1 ∧ ¬ω e ∧ ∃ u v,
      G.ends e=s(u,v) ∧ (G.openGraph ω).Reachable a u ∧ v ∈ (G.clusterObject ω S).1 := by
  have ha : a ∉ (G.clusterObject ω S).1 := by
    intro ha
    simp only [contactKernel,ite_eq_left ha,Option.some_ne_none,if_false] at hk
    exact hk rfl
  have he : e ∈ G.cutEdges (G.clusterObject ω S).1 := by
    by_contra he
    simp only [contactKernel,ite_eq_right ha,contactWeight,ite_eq_right he,zero_div] at hk
    exact hk rfl
  have hc : ¬ω e := fun hoe => G.clusterObject_cut_closed ω S e he
    ⟨hoe,G.cutEdges_subset_incidentEdges _ he⟩
  obtain ⟨u,v,heq,hu,hv⟩ := he
  have hq : (LazyDFS.search G order a S).queryDelta
      (fun σ => ∃ b ∈ S, (G.openGraph σ).Reachable a b) w ω e ≠ 0 := by
    intro hq
    simp only [contactKernel,ite_eq_right ha,contactWeight,hq,mul_zero,ite_self,zero_div] at hk
    exact hk rfl
  obtain ⟨z,hz,hr⟩ := LazyDFS.search_queryDelta_incident G order S a _ w ω e hq
  have hzu : z=u := by
    rw [heq,Sym2.mem_iff] at hz
    rcases hz with rfl|rfl
    · rfl
    · obtain ⟨b,hb,hbv⟩ := hv
      exact (ha ⟨b,hb,hbv.trans hr.symm⟩).elim
  exact ⟨ha,hc,u,v,heq,hzu ▸ hr,hv⟩

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryMarks
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma nodeMark_old (n : ℕ) (h : History E (n+1)) (i : ℕ) (hi : i < n+2) :
    nodeMark (n+1) h i = nodeMark n h.1 i := by
  rw [nodeMark,ite_eq_right (by omega : i ≠ n+2)]

lemma nodeMark_current (n : ℕ) (h : History E (n+1)) : nodeMark (n+1) h (n+2) = h.2.2 := by
  simp only [nodeMark,if_true]

lemma canonical_append_iff (L M : List (V × Bool)) (ω : Set E) (i : ℕ) (hi : i < L.length) :
    Canonical G (L++M) ω i ↔ Canonical G L ω i := by
  constructor
  · intro hc j z t hj hz ht
    apply hc j z t hj
    · rw [List.getElem?_append_left (hj.trans hi)]
      exact hz
    · rw [List.getElem?_append_left hi]
      exact ht
  · exact canonical_append G L M ω i hi

section Marks
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma current_mark_geometry (n : ℕ) (h : History E (n+1)) (ω : E → Prop) (e : E)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) (hm : h.2.2 = some e) :
    ¬ω e ∧ ∃ u v, G.ends e = s(u,v) ∧
      (G.openGraph ω).Reachable (node d x (n+1) h (n+2)).1 u ∧
      (G.openGraph ω).Reachable (node d x (n+1) h
        (nodeParent G d x ω (n+1) h (n+2))).1 v := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  rw [hm] at hk
  obtain ⟨ha,hclosed,u,v,hev,hau,hv⟩ := kernel_contact_geometry G order _ _ p w ω e hk
  have hex := kernel_parent_exists G order d x n h.1 _ p w ω (some e) hk
  have hp := parent_lt_of_exists G _ _ ω _ hex
  rw [anchors_length] at hp
  rw [node_current,nodeParent_current G order d x p w r₀ n h ω hr,hm,
    node_old d x n h _ hp]
  obtain ⟨z,hz,hpred⟩ := firstIndex_spec hex
  have hnode : z = node d x n h.1 (parent G (anchors d x n h.1)
      (x (nextIndex d n h.1)) ω (some e)) :=
    Option.some.inj (hz.symm.trans (node_getElem? d x n h.1 _ hp))
  rw [hnode] at hpred
  obtain ⟨t,ht,hpt⟩ := hpred
  have htv : t=v := by
    rw [hev,Sym2.mem_iff] at ht
    rcases ht with rfl|rfl
    · have hmemp := node_mem d x n h.1 _ hp
      exact (ha ⟨_,⟨_,hmemp⟩,hpt.trans hau.symm⟩).elim
    · rfl
  exact ⟨hclosed,u,v,hev,hau,htv ▸ hpt⟩

lemma current_canonical_iff (n : ℕ) (h : History E (n+1)) (ω : E → Prop)
    (hr : density G order d x p w r₀ (n+1) h ω ≠ 0) :
    Canonical G (anchors d x (n+1) h) ω (n+2) ↔ h.2.2 ≠ none := by
  have hk := (density_step_support G order d x p w r₀ n h ω hr).2.1
  have hex := kernel_parent_exists G order d x n h.1 _ p w ω _ hk
  have hp := parent_lt_of_exists G _ _ ω _ hex
  rw [anchors_length] at hp
  constructor
  · intro hc hm
    obtain ⟨z,hz,hpred⟩ := firstIndex_spec hex
    have ht := node_getElem? d x (n+1) h (n+2) (by omega)
    rw [node_current] at ht
    have hpz : (anchors d x (n+1) h)[parent G (anchors d x n h.1)
        (x (nextIndex d n h.1)) ω h.2.2]? = some z := by
      change ((anchors d x n h.1 ++ [_])[_]?) = some z
      rw [List.getElem?_append_left (by simpa only [anchors_length] using hp)]
      exact hz
    rw [hm] at hpred
    exact hc _ z _ hp hpz ht hpred.symm
  · intro hm
    obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hm
    have hk' := hk
    rw [he] at hk'
    have ha := (kernel_contact_geometry G order _ _ p w ω e hk').1
    intro j z t hj hz ht hrzt
    have ht' := node_getElem? d x (n+1) h (n+2) (by omega)
    rw [node_current] at ht'
    have heqt : t = (x (nextIndex d n h.1),h.2.1) := Option.some.inj (ht.symm.trans ht')
    subst t
    change (anchors d x n h.1 ++ [_])[j]? = some z at hz
    rw [List.getElem?_append_left (by simpa only [anchors_length] using hj)] at hz
    exact ha ⟨z.1,⟨z.2,List.mem_of_getElem? hz⟩,hrzt⟩

lemma canonical_iff_nonhold (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) :
    Canonical G (anchors d x n h) ω i ↔ nodeMark n h i ≠ none := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      rw [nodeMark_current]
      exact current_canonical_iff G order d x p w r₀ n h ω hr
    · have hio : i < n+2 := by omega
      rw [nodeMark_old n h i hio]
      change Canonical G (anchors d x n h.1 ++ [_]) ω i ↔ _
      rw [canonical_append_iff G _ _ ω i (by simpa only [anchors_length] using hio)]
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hio

lemma node_mark_geometry (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2) (e : E) (hm : nodeMark n h i = some e) :
    ¬ω e ∧ ∃ u v, G.ends e = s(u,v) ∧
      (G.openGraph ω).Reachable (node d x n h i).1 u ∧
      (G.openGraph ω).Reachable (node d x n h (nodeParent G d x ω n h i)).1 v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n+2
    · subst i
      rw [nodeMark_current] at hm
      exact current_mark_geometry G order d x p w r₀ n h ω e hr hm
    · have hio : i < n+2 := by omega
      rw [nodeMark_old n h i hio] at hm
      rw [node_old d x n h i hio,nodeParent_old G d x ω n h i hio,
        node_old d x n h _ ((nodeParent_lt G d x ω n h.1 i hi).trans hio)]
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hio hm

end Marks

lemma active_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : i < n+2 := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
  · exact ((historyForest G d x ω n h).mem_lineage_le hi).trans_lt
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)

section Active
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma active_canonical (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) :
    Canonical G (anchors d x n h) ω i := by
  have he := endpoint_labels d x n h
  have hi' := (Forest.mem_active (historyForest G d x ω n h)).mp hi
  rcases hi'.1 with hi|hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨true,he.1⟩)
      (owner_canonical G d x n h ω _ ⟨true,he.1⟩) i hi
  · exact lineage_canonical G order d x p w r₀ n h ω hr _
      (owner_lt G d x n h ω _ ⟨false,he.2⟩)
      (owner_canonical G d x n h ω _ ⟨false,he.2⟩) i hi

lemma active_nonhold (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : i ∈ activeNodes G d x n h ω) : nodeMark n h i ≠ none := by
  have hi2 := (Forest.mem_active _).mp hi |>.2
  exact (canonical_iff_nonhold G order d x p w r₀ n h ω hr i hi2
    (active_lt G d x n h ω i hi)).mp (active_canonical G order d x p w r₀ n h ω hr i hi)

end Active
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryWords
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

lemma interval_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    interval d n (fromWords n b m) = interval d n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fromWords,interval,ih (Fin.init b) (Fin.init m) (Fin.init m')]

lemma nextIndex_fromWords (d n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E) :
    nextIndex d n (fromWords n b m) = nextIndex d n (fromWords n b m') := by
  simp only [nextIndex,interval_fromWords d n b m m']

lemma anchors_fromWords (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m m' : Fin n → Option E) :
    anchors d x n (fromWords n b m) = anchors d x n (fromWords n b m') := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [fromWords,anchors,ih (Fin.init b) (Fin.init m) (Fin.init m'),
      nextIndex_fromWords d n (Fin.init b) (Fin.init m) (Fin.init m')]

lemma prefix_self (n : ℕ) (h : History E n) : historyPrefix n h n = h := by
  cases n with
  | zero => cases h; rfl
  | succ n => simp only [historyPrefix,dite_true]

lemma prefix_prev (n : ℕ) (h : History E (n+1)) (k : ℕ) (hk : k ≤ n) :
    historyPrefix (n+1) h k = historyPrefix n h.1 k := by
  rw [historyPrefix,dite_eq_right (by omega : k ≠ n+1)]

lemma prefix_last (n : ℕ) (h : History E (n+1)) : historyPrefix (n+1) h n = h.1 := by
  rw [prefix_prev _ _ _ le_rfl,prefix_self]

lemma prefix_fromWords (n : ℕ) (b : Fin n → Bool) (m m' : Fin n → Option E)
    (k : ℕ) (hk : k ≤ n) :
    sides k (historyPrefix n (fromWords n b m) k) = sides k (historyPrefix n (fromWords n b m') k) := by
  induction n with
  | zero =>
    have he : k=0 := by omega
    subst k
    exact Subsingleton.elim _ _
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      simp only [prefix_self,sides_fromWords]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev _ _ _ hk',prefix_prev _ _ _ hk']
      exact ih (Fin.init b) (Fin.init m) (Fin.init m') hk'

lemma anchors_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchors d x n h = anchors d x n h' := by
  conv_lhs => rw [←fromWords_sides_marks n h]
  conv_rhs => rw [←fromWords_sides_marks n h']
  rw [hs]
  exact anchors_fromWords d x n _ _ _

lemma interval_sides (d n : ℕ) (h h' : History E n) (hs : sides n h = sides n h') :
    interval d n h = interval d n h' := by
  conv_lhs => rw [←fromWords_sides_marks n h]
  conv_rhs => rw [←fromWords_sides_marks n h']
  rw [hs]
  exact interval_fromWords d n _ _ _

lemma nextIndex_sides (d n : ℕ) (h h' : History E n) (hs : sides n h = sides n h') :
    nextIndex d n h = nextIndex d n h' := by
  simp only [nextIndex,interval_sides d n h h' hs]

section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma density_prefix_support (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) (k : ℕ) (hk : k ≤ n) :
    density G order d x p w r₀ k (historyPrefix n h k) ω ≠ 0 := by
  induction n with
  | zero =>
    have he : k=0 := by omega
    subst k
    simpa only [prefix_self] using hr
  | succ n ih =>
    by_cases he : k=n+1
    · subst k
      simpa only [prefix_self] using hr
    · have hk' : k ≤ n := by omega
      rw [prefix_prev _ _ _ hk']
      exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1 hk'

end Density
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContactPivot
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

variable {V E : Type*}

theorem contact_pivot_iff (G : BondGraph V E) (ω : Set E) (B : Set V)
    (a u v : V) (f e : E) (hf : G.ends f = s(u,v)) (hef : e ≠ f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (he : ∃ r ∈ G.ends e, (G.openGraph ω).Reachable a r) :
    openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)
      e (Function.update ω f True) ↔
      ω e ∧ ¬(G.openGraph (Function.update ω e False)).Reachable a u := by
  let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
  have hav : ¬(G.openGraph ω).Reachable a v := by
    intro h
    obtain ⟨b,hb,hvb⟩ := hv
    exact hn ⟨b,hb,h.trans hvb⟩
  have hopen : F (Function.update ω f True) :=
    (G.target_after_open_iff ω B a u v f hf hn hv hav).2 hau
  have hmon : G.openGraph (Function.update ω e False) ≤ G.openGraph ω :=
    SimpleGraph.fromEdgeSet_mono (Set.image_mono (force_false_subset ω e))
  have hn' : ¬∃ b ∈ B, (G.openGraph (Function.update ω e False)).Reachable a b := by
    rintro ⟨b,hb,h⟩
    exact hn ⟨b,hb,h.mono hmon⟩
  have hav' : ¬(G.openGraph (Function.update ω e False)).Reachable a v :=
    fun h => hav (h.mono hmon)
  have hv' : ∃ b ∈ B, (G.openGraph (Function.update ω e False)).Reachable v b := by
    obtain ⟨b,hb,hvb⟩ := hv
    obtain ⟨r,hr,har⟩ := he
    refine ⟨b,hb,G.reachable_force_false_of_not_reachable ω e r hr ?_ hvb⟩
    intro hvr
    exact hav (har.trans hvr.symm)
  have hcomm : Function.update (Function.update ω f True) e False =
      Function.update (Function.update ω e False) f True := by
    funext g
    by_cases hge : g = e
    · subst g; erw [Function.update_self,Function.update_of_ne hef,Function.update_self]
    · by_cases hgf : g = f
      · subst g; erw [Function.update_of_ne (Ne.symm hef),Function.update_self,Function.update_self]
      · erw [Function.update_of_ne hge,Function.update_of_ne hgf,
          Function.update_of_ne hgf,Function.update_of_ne hge]
  have hdelete : F (Function.update (Function.update ω f True) e False) ↔
      (G.openGraph (Function.update ω e False)).Reachable a u := by
    rw [hcomm]
    exact G.target_after_open_iff _ B a u v f hf hn' hv' hav'
  change Function.update ω f True e ∧ F (Function.update ω f True) ∧
      ¬F (Function.update (Function.update ω f True) e False) ↔ _
  erw [Function.update_of_ne hef,hdelete]
  exact and_congr_right (fun _ => and_iff_right hopen)

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Gluing_ContactExitPivot
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

variable {V E : Type*}

lemma contact_exit_pivot (G : BondGraph V E) (ω : Set E) (B : Set V)
    (a u v : V) (f : E) (hf : G.ends f = s(u,v)) (hclosed : ¬ω f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b) :
    openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)
      f (Function.update ω f True) := by
  apply (openPivot_force_true _ _ _).mpr
  constructor
  · apply (G.target_after_open_iff ω B a u v f hf hn hv ?_).mpr hau
    intro hav
    obtain ⟨b,hb,hvb⟩ := hv
    exact hn ⟨b,hb,hav.trans hvb⟩
  · rw [G.openGraph_force_false_of_closed ω f hclosed]
    exact hn

theorem contact_pivot_incidence_congr (G : BondGraph V E) (ω η : Set E) (B : Set V)
    (a u v : V) (f e : E) (hf : G.ends f = s(u,v)) (hclosed : ¬ω f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (hv' : ∃ b ∈ B, (G.openGraph η).Reachable v b)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (he : ∃ r ∈ G.ends e, (G.openGraph ω).Reachable a r) :
    openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) e (Function.update ω f True) ↔
      openPivot (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) e (Function.update η f True) := by
  have hr := G.reachable_incidence_congr ω η a h
  have hn' : ¬∃ b ∈ B, (G.openGraph η).Reachable a b := by
    rintro ⟨b,hb,hab⟩; exact hn ⟨b,hb,(hr b).mpr hab⟩
  have hau' := (hr u).mp hau
  by_cases hef : e = f
  · subst e
    have hclosed' : ¬η f := fun he => hclosed ((h f ⟨u,by simp [hf],hau⟩).mpr he)
    exact iff_of_true (G.contact_exit_pivot ω B a u v f hf hclosed hn hau hv)
      (G.contact_exit_pivot η B a u v f hf hclosed' hn' hau' hv')
  · have he' : ∃ r ∈ G.ends e, (G.openGraph η).Reachable a r := by
      obtain ⟨r,her,har⟩ := he; exact ⟨r,her,(hr r).mp har⟩
    rw [G.contact_pivot_iff ω B a u v f e hf hef hn hau hv he,
      G.contact_pivot_iff η B a u v f e hf hef hn' hau' hv' he',h e he,
      G.reachable_delete_incidence_congr ω η a h e u]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_CompileContactPrefixCongr
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

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

theorem compile_contact_prefix_congr (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V) (f : E)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (hpiv : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) →
      (openPivot F g (Function.update ω f True) ↔ openPivot F g (Function.update η f True)))
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v) :
    (compile G order B fuel st stack).queryDelta F w (Function.update ω f True) f =
      (compile G order B fuel st stack).queryDelta F w (Function.update η f True) f ∧
    (compile G order B fuel st stack).prefixScore p F w (Function.update ω f True) f =
      (compile G order B fuel st stack).prefixScore p F w (Function.update η f True) f := by
  induction fuel generalizing st stack w with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact ⟨rfl,rfl⟩
    · cases stack with
      | nil => exact ⟨rfl,rfl⟩
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest w hst
        · have htail : d.1 ∈ st.reached := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inl ht)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra ht; exact hd (Or.inr (Or.inr (Or.inr ht)))
          have hinc : ∃ r ∈ G.ends d.2.1, (G.openGraph ω).Reachable a r :=
            ⟨d.1,by simp [he],hst d.1 htail⟩
          have hp := propext (hpiv d.2.1 hinc)
          simp only [queryDelta,prefixScore,hp]
          by_cases hfe : f = d.2.1
          · simp only [ite_eq_left hfe, and_self]
          · simp only [ite_eq_right hfe]
            have hdf : d.2.1 ≠ f := Ne.symm hfe
            erw [Function.update_of_ne hdf,Function.update_of_ne hdf]
            have hb := propext (h d.2.1 hinc)
            rw [← hb]
            by_cases hopen : ω d.2.1
            · simp only [ite_eq_left hopen]
              have hs' : ∀ v ∈ (st.opened d.2.1 d.2.2).reached,
                  (G.openGraph ω).Reachable a v := by
                intro v hv
                rcases Finset.mem_insert.mp hv with rfl | hv
                · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
                · exact hst v hv
              obtain ⟨hq,hs⟩ := ih (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest)
                (pin w d.2.1 True) hs'
              exact ⟨hq,congrArg (_ + ·) hs⟩
            · simp only [ite_eq_right hopen]
              obtain ⟨hq,hs⟩ := ih (st.closed d.2.1) rest (pin w d.2.1 False) hst
              exact ⟨hq,congrArg (_ + ·) hs⟩

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]

theorem search_contact_reconstruction (G : BondGraph V E) (order : List (Dart V E))
    (ω η : Set E) (B : Set V) (a u v : V) (f : E)
    (hf : G.ends f = s(u,v)) (hclosed : ¬ω f)
    (hn : ¬∃ b ∈ B, (G.openGraph ω).Reachable a b)
    (hau : (G.openGraph ω).Reachable a u)
    (hv : ∃ b ∈ B, (G.openGraph ω).Reachable v b)
    (hv' : ∃ b ∈ B, (G.openGraph η).Reachable v b)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (p : ℝ) (w : E → Prop → ℝ) (s : ℝ) :
    let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
    let T := search G order a B
    T.queryDelta F w (Function.update ω f True) f =
      T.queryDelta F w (Function.update η f True) f ∧
    T.prefixScore p F w (Function.update ω f True) f =
      T.prefixScore p F w (Function.update η f True) f ∧
    T.reverseGuess p F w (Function.update ω f True) s f =
      T.reverseGuess p F w (Function.update η f True) s f := by
  let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
  have hup (σ : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) σ f True =
        Function.update σ f True := by
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' σ f True) (Subsingleton.elim _ _)
  have hpiv : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) →
      (openPivot F g (Function.update ω f True) ↔
        openPivot F g (Function.update η f True)) := by
    intro g hg
    simpa only [hup] using
      G.contact_pivot_incidence_congr ω η B a u v f g hf hclosed hn hau hv hv' h hg
  have hst : ∀ t ∈ (initial (E := E) a).reached, (G.openGraph ω).Reachable a t := by
    intro t ht
    have hta : t = a := Finset.mem_singleton.mp ht
    subst t
    exact .refl _
  obtain ⟨hd,hs⟩ := compile_contact_prefix_congr G order B _ _ _ p F w ω η a f h hpiv hst
  refine ⟨hd,hs,?_⟩
  change (search G order a B).reverseGuess p F w (Function.update ω f True) s f =
    (search G order a B).reverseGuess p F w (Function.update η f True) s f
  dsimp only [SearchTree.reverseGuess, search]
  erw [hd,hs,propext (hpiv f ⟨u,by simp [hf],hau⟩)]

end CriticalPercolation.LazyDFS

open scoped Classical
open Real

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_Divergence
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
open Real

namespace CriticalPercolation.FiniteEntropy
variable {X : Type*} [Fintype X]

lemma mul_log_div_ge_sub {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hs : 0 < p → 0 < r) : p - r ≤ p * Real.log (p / r) := by
  rcases eq_or_lt_of_le hp with rfl | hp
  · simp only [zero_sub, zero_mul]
    exact neg_nonpos.mpr hr
  · have hr := hs hp
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hr hp)) hp.le
    rw [Real.log_div hr.ne' hp.ne'] at h
    rw [Real.log_div hp.ne' hr.ne']
    have he : p * (r / p - 1) = r - p := by field_simp
    rw [he] at h
    nlinarith

lemma mass_sub_le_divergence (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x) - (∑ x, R x) ≤ divergence P R := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun x _ => mul_log_div_ge_sub (hP x) (hR x) (hs x)

lemma divergence_nonneg (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1) (hRsum : ∑ x, R x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) : 0 ≤ divergence P R := by
  simpa only [hPsum, hRsum, sub_self] using mass_sub_le_divergence P R hP hR hs

lemma normalizer_pos (P R : X → ℝ) (_hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    0 < ∑ x, R x * Real.exp (g x) := by
  obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
    by_contra! h
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun x _ => h x)
    linarith
  exact (mul_pos (hs x hx) (Real.exp_pos _)).trans_le
    (Finset.single_le_sum (fun y _ => mul_nonneg (hR y) (Real.exp_nonneg _)) (Finset.mem_univ x))

theorem entropy_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hPsum : ∑ x, P x = 1)
    (hs : ∀ x, 0 < P x → 0 < R x) (g : X → ℝ) :
    ∑ x, P x * g x ≤ divergence P R + Real.log (∑ x, R x * Real.exp (g x)) := by
  let Z := ∑ x, R x * Real.exp (g x)
  have hZ : 0 < Z := normalizer_pos P R hP hR hPsum hs g
  let R' := fun x => R x * Real.exp (g x) / Z
  have hR' : ∀ x, 0 ≤ R' x := fun x => div_nonneg
    (mul_nonneg (hR x) (Real.exp_nonneg _)) hZ.le
  have hs' : ∀ x, 0 < P x → 0 < R' x := fun x hx => div_pos
    (mul_pos (hs x hx) (Real.exp_pos _)) hZ
  have hRsum : ∑ x, R' x = 1 := by
    simp only [R', ← Finset.sum_div, Z, div_self hZ.ne']
  have hdiv := divergence_nonneg P R' hP hR' hPsum hRsum hs'
  have he : divergence P R' = divergence P R - (∑ x, P x * g x) + Real.log Z := by
    have hterm (x : X) : P x * Real.log (P x / R' x) =
        P x * Real.log (P x / R x) - P x * g x + P x * Real.log Z := by
      rcases eq_or_lt_of_le (hP x) with hx | hx
      · simp [← hx]
      · have hr := hs x hx
        simp only [R', Real.log_div hx.ne' (ne_of_gt (hs' x hx)),
          Real.log_div (mul_pos hr (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp,
          Real.log_div hx.ne' hr.ne']
        ring
    simp only [divergence, hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, hPsum, one_mul]
  rw [he] at hdiv
  linarith

end CriticalPercolation.FiniteEntropy

open Set Real
open scoped Topology

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryTree
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.QueryTree.nodeFintype _root_.OAI.Percolation.PointwisePerm.topology
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
open Real
open Set Real
open scoped Topology

namespace CriticalPercolation
open FiniteEntropy

universe u

namespace QueryTree
variable {E : Type u}

lemma reference_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) :
    ∀ (t : QueryTree E) (x : t.Leaf), 0 < t.reference p x := by
  intro t
  induction t with
  | stop => intro x; exact zero_lt_one
  | ask e left right hl hr =>
    intro x
    cases x with
    | inl x => exact mul_pos (sub_pos.mpr hp.2) (hl x)
    | inr x => exact mul_pos hp.1 (hr x)

lemma run_dependsOn [DecidableEq E] (t : QueryTree E) (used : Finset E) (hv : t.Valid used) :
    DependsOn t.run (↑used : Set E)ᶜ := by
  intro ω ω' hω
  induction t generalizing used with
  | stop => rfl
  | ask e left right hl hr =>
    have he : ω e = ω' e := hω e hv.1
    have hc : ∀ i ∈ (↑(insert e used) : Set E)ᶜ, ω i = ω' i := by
      intro i hi
      exact hω i (fun hu => hi (Finset.mem_insert_of_mem hu))
    simp only [run, he]
    split_ifs
    · exact congrArg Sum.inr (hr _ hv.2.2 hc)
    · exact congrArg Sum.inl (hl _ hv.2.1 hc)

end QueryTree
end CriticalPercolation

open scoped BigOperators
open Set

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_PushMass
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma pushMass_nonneg (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (y : Y) :
    0 ≤ pushMass f P y := by
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

lemma pushMass_sum (f : X → Y) (P : X → ℝ) :
    ∑ y, pushMass f P y = ∑ x, P x := by
  classical
  simp only [pushMass]
  rw [Finset.sum_comm]
  simp

omit [Fintype Y] in
lemma le_pushMass (f : X → Y) (P : X → ℝ) (hP : ∀ x, 0 ≤ P x) (x : X) :
    P x ≤ pushMass f P (f x) := by
  classical
  have := Finset.single_le_sum (s := Finset.univ)
    (f := fun z => if f z = f x then P z else 0)
    (fun z _ => by split_ifs <;> simp_all) (Finset.mem_univ x)
  simpa [pushMass] using this

lemma sum_pushMass_mul (f : X → Y) (P : X → ℝ) (g : Y → ℝ) :
    ∑ y, pushMass f P y * g y = ∑ x, P x * g (f x) := by
  classical
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

lemma log_sum_inequality (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 ≤ R x) (hs : ∀ x, 0 < P x → 0 < R x) :
    (∑ x, P x)*Real.log ((∑ x, P x)/(∑ x, R x)) ≤ divergence P R := by
  classical
  let A := ∑ x, P x
  let B := ∑ x, R x
  have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => hP x
  rcases eq_or_lt_of_le hA with hA | hA
  · have hz : ∀ x, P x = 0 := by
      intro x
      have hx := Finset.single_le_sum (fun y _ => hP y) (Finset.mem_univ x)
      dsimp [A] at hA
      linarith [hP x]
    simp [hz, divergence]
  have hB : 0 < B := by
    obtain ⟨x, hx⟩ : ∃ x, 0 < P x := by
      by_contra! hn
      have ht := Finset.sum_nonpos (s := Finset.univ) (fun x _ => hn x)
      exact (not_le_of_gt hA) ht
    exact (hs x hx).trans_le (Finset.single_le_sum (fun y _ => hR y) (Finset.mem_univ x))
  let S : X → ℝ := fun x => R x * (A/B)
  have hS : ∀ x, 0 ≤ S x := fun x => mul_nonneg (hR x) (div_pos hA hB).le
  have hpos : ∀ x, 0 < P x → 0 < S x := fun x hx => mul_pos (hs x hx) (div_pos hA hB)
  have hmass : ∑ x, S x = A := by
    simp only [S, ← Finset.sum_mul]
    change B * (A/B) = A
    field_simp
  have hb := mass_sub_le_divergence P S hP hS hpos
  have he : divergence P S = divergence P R - A*Real.log (A/B) := by
    have ht (x : X) : P x * Real.log (P x / S x) =
        P x * Real.log (P x / R x) - P x * Real.log (A/B) := by
      rcases eq_or_lt_of_le (hP x) with hz | hp
      · simp [← hz]
      · have hr := hs x hp
        simp only [S, Real.log_div hp.ne' (mul_pos hr (div_pos hA hB)).ne',
          Real.log_mul hr.ne' (div_pos hA hB).ne', Real.log_div hp.ne' hr.ne']
        ring
    simp only [divergence, ht, Finset.sum_sub_distrib, ← Finset.sum_mul, A]
  rw [hmass, he] at hb
  change A*Real.log (A/B) ≤ divergence P R
  dsimp [A] at hb ⊢
  linarith

theorem divergence_pushMass_le (f : X → Y) (P R : X → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hR : ∀ x, 0 ≤ R x)
    (hs : ∀ x, 0 < P x → 0 < R x) :
    divergence (pushMass f P) (pushMass f R) ≤ divergence P R := by
  classical
  have hf (y : Y) := log_sum_inequality
    (fun x => if f x = y then P x else 0) (fun x => if f x = y then R x else 0)
    (fun x => by split_ifs <;> simp_all) (fun x => by split_ifs <;> simp_all)
    (fun x hx => by split_ifs at hx ⊢ <;> simp_all)
  have ht (x : X) (y : Y) :
      (if f x = y then P x else 0) *
          Real.log ((if f x = y then P x else 0)/(if f x = y then R x else 0)) =
        if f x = y then P x * Real.log (P x / R x) else 0 := by
    split_ifs <;> simp
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hf y)
  simp only [divergence, ht] at hh
  rw [Finset.sum_comm] at hh
  simpa [pushMass, divergence] using hh

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BitWeight
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.QueryTree.nodeFintype _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_sum (p : ℝ) (e : E) : ∑ b, bitWeight p e b = 1 := by
  simp [bitWeight]

lemma reference_eq_product_push (p : ℝ) (t : QueryTree E)
    (used : Finset E) (hv : t.Valid used) :
    pushMass t.run (density (bitWeight p)) = t.reference p := by
  classical
  induction t generalizing used with
  | stop =>
    funext x
    have : x = PUnit.unit := Subsingleton.elim _ _
    subst x
    simp only [pushMass, run, reference]
    exact sum_density _ (bitWeight_sum p)
  | ask e left right hl hr =>
    have hi (b : Bool) : DependsOn (fun ω : E → Bool => if ω e = b then (1:ℝ) else 0)
        ({e} : Set E) := by
      intro ω ω' hω
      dsimp only
      rw [hω e (Set.mem_singleton e)]
    have hc (u : QueryTree E) (hu : u.Valid (insert e used)) (x : u.Leaf) :
        DependsOn (fun ω => if u.run ω = x then (1:ℝ) else 0) ({e} : Set E)ᶜ := by
      intro ω ω' hω
      have heq : u.run ω = u.run ω' := run_dependsOn u _ hu (fun j hj =>
        hω j (by intro hje; have hje : j = e := hje; subst j
                 exact hj (Finset.mem_insert_self _ _)))
      dsimp only
      rw [heq]
    funext x
    cases x with
    | inl x =>
      have heq : (fun ω => if (ask e left right).run ω = Sum.inl x then (1:ℝ) else 0) =
          (fun ω => (if ω e = false then (1:ℝ) else 0) *
            (if left.run ω = x then 1 else 0)) := by
        funext ω
        cases he : ω e <;> simp [run, he]
      have hm : pushMass (ask e left right).run (density (bitWeight p)) (Sum.inl x) =
          expect (bitWeight p) (fun ω => if (ask e left right).run ω = Sum.inl x then 1 else 0) := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      rw [hm, heq, expect_indep _ (bitWeight_sum p) _ (hi false)
        (hc left hv.2.1 x)]
      have hev : expect (bitWeight p) (fun ω => if ω e = false then 1 else 0) =
          bitWeight p e false := by
        convert expect_eval_indicator (bitWeight p) (bitWeight_sum p) e false using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        split_ifs <;> simp_all
      rw [hev]
      have hm' : expect (bitWeight p) (fun ω => if left.run ω = x then 1 else 0) =
          pushMass left.run (density (bitWeight p)) x := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
      rw [hm', hl _ hv.2.1]
      rfl
    | inr x =>
      have heq : (fun ω => if (ask e left right).run ω = Sum.inr x then (1:ℝ) else 0) =
          (fun ω => (if ω e = true then (1:ℝ) else 0) *
            (if right.run ω = x then 1 else 0)) := by
        funext ω
        cases he : ω e <;> simp [run, he]
      have hm : pushMass (ask e left right).run (density (bitWeight p)) (Sum.inr x) =
          expect (bitWeight p) (fun ω => if (ask e left right).run ω = Sum.inr x then 1 else 0) := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      rw [hm, heq, expect_indep _ (bitWeight_sum p) _ (hi true)
        (hc right hv.2.2 x)]
      have hev : expect (bitWeight p) (fun ω => if ω e = true then 1 else 0) =
          bitWeight p e true := by
        convert expect_eval_indicator (bitWeight p) (bitWeight_sum p) e true using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        split_ifs <;> simp_all
      rw [hev]
      have hm' : expect (bitWeight p) (fun ω => if right.run ω = x then 1 else 0) =
          pushMass right.run (density (bitWeight p)) x := by
        simp only [pushMass, expect, mul_ite, mul_one, mul_zero]
      rw [hm', hr _ hv.2.2]
      rfl

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Node
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set

namespace CriticalPercolation.QueryTree
open FiniteProduct FiniteEntropy

variable {E : Type*} [Fintype E]

omit [Fintype E] in
lemma bitWeight_pos {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (e : E) (b : Bool) :
    0 < bitWeight p e b := by
  cases b <;> simp [bitWeight, hp.1, hp.2]

end CriticalPercolation.QueryTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_State
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
lemma eligible_succ (G : BondGraph V E) (st : State V E) (h : ∃ e, eligible G st e) :
    eligible G st (Classical.choose h) := Classical.choose_spec h

lemma compile_valid (G : BondGraph V E) (n : ℕ) (st : State V E) :
    (compile G n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨(eligible_succ G st h).1, ih _, ih _⟩
    · trivial

omit [DecidableEq V] [DecidableEq E] in
lemma edge_reachable (G : BondGraph V E) (ω : E → Bool) {e : E} (he : ω e = true)
    {v t : V} (hv : v ∈ G.ends e) (ht : t ∈ G.ends e) :
    (G.openGraph {e | ω e = true}).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e,he,(Sym2.mem_and_mem_iff hne).mp ⟨hv,ht⟩⟩,hne⟩)

omit [DecidableEq V] in
lemma consistent_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool) (e : E)
    (h : Consistent G st ω) (he : ω e ≠ true) : Consistent G (closed st e) ω := by
  intro f hf hw v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact (he hw).elim
  · exact h f hf hw v hv

lemma consistent_opened (G : BondGraph V E) (st : State V E) (ω : E → Bool) (e : E)
    (h : Consistent G st ω) : Consistent G (opened G st e) ω := by
  intro f hf hw v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · exact Finset.mem_union_right _ (Sym2.mem_toFinset.mpr hv)
  · exact Finset.mem_union_left _ (h f hf hw v hv)

lemma sound_opened (G : BondGraph V E) (S : Set V) (st : State V E) (ω : E → Bool) (e : E)
    (h : Sound G S st ω) (hel : eligible G st e) (he : ω e = true) :
    Sound G S (opened G st e) ω := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact h v hv
  · obtain ⟨u,hu,hue⟩ := hel.2
    obtain ⟨s,hs,hsu⟩ := h u hu
    exact ⟨s,hs,hsu.trans (edge_reachable G ω he hue (Sym2.mem_toFinset.mp hv))⟩

lemma compile_invariants (G : BondGraph V E) (S : Set V) (n : ℕ) (st : State V E)
    (ω : E → Bool) (hc : Consistent G st ω) (hs : Sound G S st ω) :
    Consistent G ((compile G n st).run ω) ω ∧
      Sound G S ((compile G n st).run ω) ω ∧
      st.reached ⊆ ((compile G n st).run ω).reached := by
  induction n generalizing st with
  | zero => exact ⟨hc,hs,Finset.Subset.refl _⟩
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.run]
      split_ifs with he
      · obtain ⟨hc',hs',hm⟩ := ih (opened G st (Classical.choose h))
          (consistent_opened G st ω _ hc)
          (sound_opened G S st ω _ hs (eligible_succ G st h) he)
        exact ⟨hc',hs',Finset.Subset.trans Finset.subset_union_left hm⟩
      · exact ih (closed st (Classical.choose h)) (consistent_closed G st ω _ hc he) hs
    · exact ⟨hc,hs,Finset.Subset.refl _⟩

lemma compile_read (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool) :
    ((compile G n st).run ω).read = st.read ∪ ((compile G n st).reads ω).toFinset := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.run,SearchTree.reads]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.run,SearchTree.reads]
      split_ifs with he
      · rw [ih]
        simp only [opened,List.toFinset_cons]
        simp only [Finset.insert_union,Finset.union_insert]
      · rw [ih]
        simp only [closed,List.toFinset_cons]
        simp only [Finset.insert_union,Finset.union_insert]
    · simp [SearchTree.run,SearchTree.reads]

variable [Fintype E]

lemma compile_exhausted (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool)
    (hbudget : Fintype.card E ≤ n + st.read.card) :
    ¬∃ e, eligible G ((compile G n st).run ω) e := by
  induction n generalizing st with
  | zero =>
    rintro ⟨e,he,_⟩
    have hec := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ st.read,fun h => he (h ▸ Finset.mem_univ e)⟩)
    simp only [Finset.card_univ] at hec
    omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      have he := (eligible_succ G st h).1
      have hc : Fintype.card E ≤ n + (insert (Classical.choose h) st.read).card := by
        rw [Finset.card_insert_of_notMem he]
        omega
      rw [SearchTree.run]
      split_ifs
      · exact ih _ hc
      · exact ih _ hc
    · exact h

lemma compile_reads_incident (G : BondGraph V E) (n : ℕ) (st : State V E) (ω : E → Bool)
    (hc : Consistent G st ω) (hs : Sound G Set.univ st ω) :
    ∀ e ∈ (compile G n st).reads ω,
      ∃ v ∈ ((compile G n st).run ω).reached, v ∈ G.ends e := by
  induction n generalizing st with
  | zero => simp [compile,SearchTree.reads]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · dsimp only
      rw [SearchTree.reads,SearchTree.run]
      by_cases he : ω (Classical.choose h) = true
      · simp only [he,↓reduceIte,List.mem_cons]
        intro e hem
        rcases hem with rfl | hem
        · obtain ⟨v,hv,hve⟩ := (eligible_succ G st h).2
          have hm := (compile_invariants G Set.univ n (opened G st (Classical.choose h)) ω
            (consistent_opened G st ω _ hc)
            (sound_opened G Set.univ st ω _ hs (eligible_succ G st h) he)).2.2
          exact ⟨v,hm (Finset.mem_union_left _ hv),hve⟩
        · exact ih _ (consistent_opened G st ω _ hc)
            (sound_opened G Set.univ st ω _ hs (eligible_succ G st h) he) e hem
      · simp only [he,List.mem_cons]
        intro e hem
        rcases hem with rfl | hem
        · obtain ⟨v,hv,hve⟩ := (eligible_succ G st h).2
          have hm := (compile_invariants G Set.univ n (closed st (Classical.choose h)) ω
            (consistent_closed G st ω _ hc he) hs).2.2
          exact ⟨v,hm hv,hve⟩
        · exact ih _ (consistent_closed G st ω _ hc he) hs e hem
    · simp [SearchTree.reads]

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Initial2
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.QueryTree.nodeFintype _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.ExactExposure
open scoped Classical
open SearchTree

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
lemma initial_consistent (G : BondGraph V E) (S : Finset V) (ω : E → Bool) :
    Consistent G (initial S) ω := by
  intro e he
  exact (Finset.notMem_empty e he).elim

omit [DecidableEq V] [DecidableEq E] [Fintype E] in
lemma initial_sound (G : BondGraph V E) (S : Finset V) (ω : E → Bool) :
    Sound G (S : Set V) (initial S) ω := by
  intro v hv
  exact ⟨v,hv,.refl _⟩

lemma search_reached (G : BondGraph V E) (S : Finset V) (ω : E → Bool) (v : V) :
    v ∈ ((search G S).run ω).reached ↔
      ∃ a ∈ S, (G.openGraph {e | ω e = true}).Reachable a v := by
  obtain ⟨hc,hs,hm⟩ := compile_invariants G (S : Set V) (Fintype.card E) (initial S) ω
    (initial_consistent G S ω) (initial_sound G S ω)
  constructor
  · exact hs v
  · rintro ⟨a,ha,hav⟩
    have he := compile_exhausted G (Fintype.card E) (initial S) ω (by simp [initial])
    have hcl : ∀ u ∈ ((search G S).run ω).reached, ∀ t,
        (G.openGraph {e | ω e = true}).Adj u t → t ∈ ((search G S).run ω).reached := by
      intro u hu t hut
      obtain ⟨⟨e,hew,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hut
      have hread : e ∈ ((search G S).run ω).read := by
        by_contra hn
        exact he ⟨e,hn,u,hu,by simp [heq]⟩
      exact hc e hread hew t (by simp [heq])
    have hh := ((G.openGraph {e | ω e = true}).reachable_iff_reflTransGen a v).mp hav
    clear hav
    induction hh with
    | refl => exact hm ha
    | tail _ huv ih => exact hcl _ ih _ huv

lemma search_reads (G : BondGraph V E) (S : Finset V) (ω : E → Bool) (e : E) :
    e ∈ (search G S).reads ω ↔
      ∃ v ∈ G.ends e, ∃ a ∈ S, (G.openGraph {e | ω e = true}).Reachable a v := by
  have he := compile_exhausted G (Fintype.card E) (initial S) ω (by simp [initial])
  have hrd : ((search G S).run ω).read = ((search G S).reads ω).toFinset := by
    simpa only [search,initial,Finset.empty_union] using compile_read G (Fintype.card E) (initial S) ω
  constructor
  · intro hed
    have hs : Sound G Set.univ (initial S) ω := by
      intro v _
      exact ⟨v,Set.mem_univ _,.refl _⟩
    obtain ⟨v,hv,hev⟩ := compile_reads_incident G (Fintype.card E) (initial S) ω
      (initial_consistent G S ω) hs e hed
    exact ⟨v,hev,(search_reached G S ω v).mp hv⟩
  · rintro ⟨v,hve,a,ha,hav⟩
    have hv := (search_reached G S ω v).mpr ⟨a,ha,hav⟩
    have hr : e ∈ ((search G S).run ω).read := by
      by_contra hn
      exact he ⟨e,hn,v,hv,hve⟩
    rw [hrd] at hr
    exact List.mem_toFinset.mp hr

lemma pair_reads (G : BondGraph V E) (a b : V) (ω : E → Bool) (e : E) :
    e ∈ (pair G a b).reads ω ↔
      ∃ v ∈ G.ends e, (G.openGraph {e | ω e = true}).Reachable a v ∨
        (G.openGraph {e | ω e = true}).Reachable b v := by
  simp only [pair,search_reads,Finset.mem_insert,Finset.mem_singleton,exists_eq_or_imp, exists_eq_left]

end CriticalPercolation.ExactExposure

namespace CriticalPercolation
namespace SearchTree
variable {E R : Type*}

lemma bare_valid [DecidableEq E] (T : SearchTree E R) (used : Finset E) (h : T.Valid used) :
    T.bare.Valid used := by
  induction T generalizing used with
  | done _ => trivial
  | ask e l r hl hr => exact ⟨h.1,hl _ h.2.1,hr _ h.2.2⟩

lemma bare_run_eq (T : SearchTree E R) (ω η : E → Bool) (h : T.bare.run ω = T.bare.run η) :
    T.run ω = T.run η ∧ ∀ e ∈ T.reads ω, ω e = η e := by
  induction T with
  | done _ => exact ⟨rfl,by simp [reads]⟩
  | ask e l r hl hr =>
    simp only [bare,QueryTree.run] at h
    cases he : ω e <;> cases he' : η e
    · simp only [he,he',Bool.false_eq_true,↓reduceIte,Sum.inl.injEq] at h
      obtain ⟨hout,hbits⟩ := hl h
      simp only [run,reads,he,he',Bool.false_eq_true,↓reduceIte]
      refine ⟨hout,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he.trans he'.symm
      · exact hbits f hf
    · simp [he,he'] at h
    · simp [he,he'] at h
    · simp only [he,he',↓reduceIte,Sum.inr.injEq] at h
      obtain ⟨hout,hbits⟩ := hr h
      simp only [run,reads,he,he',↓reduceIte]
      refine ⟨hout,?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he.trans he'.symm
      · exact hbits f hf
end SearchTree
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.ExactExposure
open scoped Classical

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype E]

theorem pair_transcript_incidence (G : BondGraph V E) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η)
    (e : E) (he : ∃ v ∈ G.ends e, (G.openGraph {e | ω e = true}).Reachable a v ∨
      (G.openGraph {e | ω e = true}).Reachable b v) : ω e = η e :=
  (SearchTree.bare_run_eq _ ω η h).2 e ((pair_reads G a b ω e).mpr he)

end CriticalPercolation.ExactExposure

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteEntropy FiniteProduct

variable {V E I : Type*} [Fintype E] [Fintype I]

omit [Fintype I] in

theorem pair_transcript_left_cluster (G : BondGraph V E) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (v : V) :
    (G.openGraph {e | ω e = true}).Reachable a v ↔
      (G.openGraph {e | η e = true}).Reachable a v := by
  apply G.reachable_incidence_congr
  intro e he
  obtain ⟨x,hx,hr⟩ := he
  have hb := pair_transcript_incidence G a b ω η h e ⟨x,hx,Or.inl hr⟩
  exact congrArg (· = true) hb |>.to_iff

omit [Fintype I] in
lemma pair_transcript_right_cluster (G : BondGraph V E) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (v : V) :
    (G.openGraph {e | ω e = true}).Reachable b v ↔
      (G.openGraph {e | η e = true}).Reachable b v := by
  apply G.reachable_incidence_congr
  intro e he
  obtain ⟨x,hx,hr⟩ := he
  have hb := pair_transcript_incidence G a b ω η h e ⟨x,hx,Or.inr hr⟩
  exact congrArg (· = true) hb |>.to_iff

end CriticalPercolation.ExactExposure

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*}

lemma admissible_closed (G : BondGraph V E) (B : Set V) (a b : V) (hb : b ∈ B)
    (ω : E → Bool) (f : E) (h : Admissible G B a b ω f) : ¬configuration ω f := by
  obtain ⟨hn,u,v,hf,hu,hv⟩ := h
  intro hopen
  exact hn ⟨b,hb,hu.trans ((LazyDFS.prop_openEdge_reachable G _ hopen hf).trans hv.symm)⟩

variable [Fintype E]

lemma admissible_congr (G : BondGraph V E) (B : Set V) (a b : V) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (f : E) :
    Admissible G B a b ω f ↔ Admissible G B a b η f := by
  unfold Admissible
  have hl := pair_transcript_left_cluster G a b ω η h
  have hr := pair_transcript_right_cluster G a b ω η h
  simp only [configuration] at *
  simp only [hl,hr]

variable [Fintype V]

theorem pair_contact_prices (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (ω η : E → Bool)
    (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (f : E)
    (ha : Admissible G B a b ω f) (p : ℝ) (w : E → Prop → ℝ) :
    let F := fun σ : Set E => ∃ t ∈ B, (G.openGraph σ).Reachable a t
    let T := LazyDFS.search G order a B
    T.queryDelta F w (configuration ω) f = T.queryDelta F w (configuration η) f ∧
      T.prefixScore p F w (Function.update (configuration ω) f True) f =
        T.prefixScore p F w (Function.update (configuration η) f True) f := by
  obtain ⟨hn,u,v,hf,hu,hv⟩ := ha
  have hc : ¬configuration ω f := admissible_closed G B a b hb ω f ⟨hn,u,v,hf,hu,hv⟩
  have hv' : (G.openGraph (configuration η)).Reachable b v :=
    (pair_transcript_right_cluster G a b ω η h v).mp hv
  have hi : ∀ g, (∃ r ∈ G.ends g, (G.openGraph (configuration ω)).Reachable a r) →
      (configuration ω g ↔ configuration η g) := by
    rintro g ⟨r,hr,har⟩
    have hh := pair_transcript_incidence G a b ω η h g ⟨r,hr,Or.inl har⟩
    exact congrArg (· = true) hh |>.to_iff
  have hprices := LazyDFS.search_contact_reconstruction G order (configuration ω)
    (configuration η) B a u v f hf hc hn hu ⟨b,hb,hv.symm⟩ ⟨b,hb,hv'.symm⟩ hi p w 0
  dsimp only at hprices ⊢
  rw [queryDelta_update,queryDelta_update] at hprices
  exact ⟨hprices.1,hprices.2.1⟩

lemma pair_mark_congr (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω η : E → Bool) (h : (pair G a b).bare.run ω = (pair G a b).bare.run η) (f : E) :
    markWeight G order B a b p w ω f = markWeight G order B a b p w η f ∧
      markCost G order B a b p w ω f = markCost G order B a b p w η f := by
  have ha := admissible_congr G B a b ω η h f
  by_cases hf : Admissible G B a b ω f
  · have hh := pair_contact_prices G order B a b hb ω η h f hf p w
    simp only [markWeight,markCost,ite_eq_left hf,ite_eq_left (ha.mp hf)]
    exact ⟨congrArg (p * ·) hh.1,hh.2⟩
  · simp only [markWeight,markCost,ite_eq_right hf,ite_eq_right (mt ha.mpr hf),and_self]

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PrefixScoreNonneg
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
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

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma prefixScore_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) :
    0 ≤ T.prefixScore p F w ω e := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    rw [prefixScore]
    apply add_nonneg
    · split_ifs
      · have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
        have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
        exact mul_nonneg (sub_nonneg.mpr hp.2.le) (delta_unit w hw hn f hf0 hf1 F hF).1
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
          (fresh_pin w p used hf f True)
      · exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
          (fresh_pin w p used hf f False)
end CriticalPercolation.SearchTree

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*} [Fintype V] [Fintype E]

lemma mark_nonneg (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Bool) (f : E) :
    0 ≤ markWeight G order B a b p w ω f ∧ 0 ≤ markCost G order B a b p w ω f := by
  have hv : (LazyDFS.search G order a B).Valid ∅ := LazyDFS.compile_valid G order B _ _ _
  have hF : ∀ s t : Set E, s ⊆ t → (∃ v ∈ B, (G.openGraph s).Reachable a v) →
      ∃ v ∈ B, (G.openGraph t).Reachable a v := by
    rintro s t hst ⟨v,hv,hr⟩
    exact ⟨v,hv,hr.mono (G.openGraph_mono hst)⟩
  have hw := homogeneous_normalized w p h0 h1
  have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  have hf : Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  unfold markWeight markCost
  split_ifs
  · exact ⟨mul_nonneg hp.1.le (queryDelta_nonneg _ _ hv hp _ hF w hw hn hf _ f),
      prefixScore_nonneg _ _ hv hp _ hF w hw hn hf _ f⟩
  · exact ⟨le_rfl,le_rfl⟩

end CriticalPercolation.ExactExposure

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryDescriptor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest FiniteEntropy ExactExposure

variable {V E : Type*}

lemma descriptor_sides (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) : sides n h = fun i => (D i).1 := by
  funext i
  exact congrArg (fun D : FixedDescriptor n => (D i).1) hD

lemma sum_history_words [Fintype E] (n : ℕ) (f : History E n → ℝ) :
    (∑ h, f h) = ∑ b : Fin n → Bool, ∑ m : Fin n → Option E, f (fromWords n b m) := by
  rw [← (wordsEquiv (E := E) n).symm.sum_comp f,Fintype.sum_prod_type]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

lemma jointMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (z : (E → Bool) × History E n) : 0 ≤ jointMass G order d x p w s n z := by
  exact mul_nonneg (FiniteProduct.density_nonneg (fun e b => (QueryTree.bitWeight_pos hp e b).le) _)
    (density_nonneg G order d x p w _ hp h0 h1 (seed_nonneg G w _ _ s hδ) n z.2 _)

lemma fixedMass_sum (D : FixedDescriptor n) :
    (∑ z, fixedMass G order d x p w s n D z) = descriptorMass G order d x p w s n D := by
  unfold descriptorMass pushMass
  conv_rhs => rw [Fintype.sum_prod_type]
  simp_rw [sum_history_words]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  symm
  apply (Finset.sum_eq_single (fun i => (D i).1) ?_ ?_).trans
  · apply Finset.sum_congr rfl
    intro m _
    unfold fixedMass
    dsimp only
    split_ifs <;> rfl
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro m _
    have hne : descriptor G d x n (fromWords n b m) (configuration ω) ≠ D := by
      intro he
      have hs := descriptor_sides G d x n _ _ D he
      rw [sides_fromWords] at hs
      exact hb hs
    rw [ite_eq_right hne]
  · simp

lemma conditionedMass_normalized (D : FixedDescriptor n)
    (hD : 0 < descriptorMass G order d x p w s n D) :
    ∑ z, conditionedMass G order d x p w s n D z = 1 := by
  simp only [conditionedMass,← Finset.sum_div,fixedMass_sum,div_self hD.ne']

lemma conditionedMass_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (D : FixedDescriptor n) (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) : 0 ≤ conditionedMass G order d x p w s n D z := by
  apply div_nonneg _ hD.le
  unfold fixedMass
  dsimp only
  split_ifs
  · exact jointMass_nonneg G order d x p w s n hp h0 h1 hδ _
  · rfl

lemma conditionedMass_support (D : FixedDescriptor n)
    (z : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0) :
    let h := fromWords n (fun i => (D i).1) z.2
    descriptor G d x n h (configuration z.1) = D ∧
    density G order d x p w (seed G w (x 0) (x d) s) n h (configuration z.1) ≠ 0 := by
  have hf := (div_ne_zero_iff.mp hz).1
  unfold fixedMass at hf
  dsimp only at hf ⊢
  split_ifs at hf with ht
  · exact ⟨ht,(mul_ne_zero_iff.mp hf).2⟩
  · exact (hf rfl).elim

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryRaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma rawContact_nonneg (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (C : ClusterObject V E) (ω : E → Prop) (mark : Option E) :
    0 ≤ G.rawContact order B a p w C ω mark := by
  unfold rawContact
  split_ifs
  · norm_num
  · norm_num
  · cases mark with
    | none => exact le_rfl
    | some e => exact G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation

variable {V E : Type*}

lemma anchorSet_sides (d : ℕ) (x : ℕ → V) (n : ℕ) (h h' : History E n)
    (hs : sides n h = sides n h') : anchorSet d x n h = anchorSet d x n h' := by
  simp only [anchorSet,anchors_sides d x n h h' hs]

lemma scheduledAnchor_eq (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m : Fin n → Option E) (k : ℕ) (hk : k≤n) :
    scheduledAnchor (E := E) d x n b k = x (nextIndex d k (historyPrefix n (fromWords n b m) k)) := by
  rw [scheduledAnchor,nextIndex_sides d k _ _ (prefix_fromWords n b _ m k hk)]

lemma scheduledTargets_eq (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (m : Fin n → Option E) (k : ℕ) (hk : k≤n) :
    scheduledTargets (E := E) d x n b k = anchorSet d x k (historyPrefix n (fromWords n b m) k) := by
  rw [scheduledTargets,anchorSet_sides d x k _ _ (prefix_fromWords n b _ m k hk)]

lemma prefix_succ_fst (n : ℕ) (h : History E n) (k : ℕ) (hk : k<n) :
    (historyPrefix n h (k+1)).1 = historyPrefix n h k := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k=n
    · subst k; rw [prefix_self,prefix_last]
    · have hk' : k<n := by omega
      rw [prefix_prev n h (k+1) (by omega),prefix_prev n h k hk'.le]
      exact ih h.1 hk'

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedEntropy
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z I M : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma pushMass_comp (f : X → Y) (g : Y → Z) (P : X → ℝ) :
    pushMass g (pushMass f P) = pushMass (g ∘ f) P := by
  funext z
  have hh := sum_pushMass_mul f P (fun y => if g y = z then (1:ℝ) else 0)
  change (∑ y, if g y = z then pushMass f P y else 0) =
    ∑ x, if g (f x) = z then P x else 0
  simpa only [mul_ite,mul_one,mul_zero] using hh

omit [Fintype Y] in
lemma sum_pushMass_pair (P : X → ℝ) (u : X → Y) (v : X → Z) (y : Y) :
    ∑ z, pushMass (fun x => (u x,v x)) P (y,z) = pushMass u P y := by
  unfold pushMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : u x = y
  · simp [h]
  · simp [h]

omit [Fintype Y] [Fintype Z] in
lemma conditionalMass_nonneg (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (y : Y) (z : Z) : 0 ≤ conditionalMass P u v y z :=
  div_nonneg (pushMass_nonneg _ _ hP _) (pushMass_nonneg _ _ hP _)

omit [Fintype Y] in
lemma sum_conditionalMass_le_one (P : X → ℝ) (_hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (y : Y) : ∑ z, conditionalMass P u v y z ≤ 1 := by
  unfold conditionalMass
  rw [← Finset.sum_div, sum_pushMass_pair]
  by_cases h : pushMass u P y = 0
  · simp [h]
  · rw [div_self h]

omit [Fintype Y] [Fintype Z] in
lemma conditionalMass_pos (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (x : X) (hx : 0 < P x) :
    0 < conditionalMass P u v (u x) (v x) :=
  div_pos (hx.trans_le (le_pushMass _ _ hP x)) (hx.trans_le (le_pushMass _ _ hP x))

lemma divergence_as_log (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hs : ∀ x, 0 < P x → 0 < R x) :
    divergence P R = ∑ x, P x * Real.log (P x) - ∑ x, P x * Real.log (R x) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    rw [Real.log_div hx (hs x hp).ne']
    ring

variable [Fintype I] [Fintype M]

omit [Fintype Y] in

theorem conditional_marks_log {Y' : I → Type*} (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (t : (i : I) → X → Y' i) :
    (∑ i, ∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
      (fun x => x.2 i) (t i x.1) (x.2 i))) ≤
      (∑ x, P x * Real.log (P x)) -
        ∑ x, P x * Real.log (pushMass Prod.fst P x.1) := by
  let K (i : I) (ω : X) (m : M) :=
    conditionalMass P (fun x => t i x.1) (fun x => x.2 i) (t i ω) m
  let R (x : X × (I → M)) := pushMass Prod.fst P x.1 * ∏ i, K i x.1 (x.2 i)
  have hR : ∀ x, 0 ≤ R x := fun x => mul_nonneg (pushMass_nonneg _ _ hP _)
    (Finset.prod_nonneg fun i _ => conditionalMass_nonneg _ hP _ _ _ _)
  have hmass : ∑ x, R x ≤ 1 := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ ω, pushMass Prod.fst P ω * (∏ i, ∑ m, K i ω m) := by
        apply Finset.sum_congr rfl
        intro ω _
        simp only [R,← Finset.mul_sum,← Fintype.prod_sum]
      _ ≤ ∑ ω, pushMass Prod.fst P ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_of_le_one_right (pushMass_nonneg _ _ hP _)
        exact Finset.prod_le_one (fun i _ => Finset.sum_nonneg fun m _ =>
          conditionalMass_nonneg _ hP _ _ _ _) (fun i _ => sum_conditionalMass_le_one _ hP _ _ _)
      _ = 1 := (pushMass_sum _ _).trans hm
  have hs (x : X × (I → M)) (hx : 0 < P x) : 0 < R x :=
    mul_pos (hx.trans_le (le_pushMass _ _ hP x)) (Finset.prod_pos fun i _ =>
      conditionalMass_pos _ hP _ _ x hx)
  have hd : 0 ≤ divergence P R := by
    have hh := mass_sub_le_divergence P R hP hR hs
    rw [hm] at hh
    linarith
  rw [divergence_as_log P R hP hs] at hd
  have heq : ∑ x, P x * Real.log (R x) =
      (∑ x, P x * Real.log (pushMass Prod.fst P x.1)) +
        ∑ i, ∑ x, P x * Real.log (K i x.1 (x.2 i)) := by
    rw [Finset.sum_comm,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      have hs0 : 0 < pushMass Prod.fst P x.1 := hp.trans_le (le_pushMass _ _ hP x)
      have hK (i : I) : 0 < K i x.1 (x.2 i) := conditionalMass_pos _ hP _ _ x hp
      dsimp only [R]
      rw [Real.log_mul hs0.ne' (Finset.prod_pos (fun i _ => hK i)).ne',
        Real.log_prod (fun i _ => (hK i).ne'),mul_add,Finset.mul_sum]
  rw [heq] at hd
  dsimp only [K] at hd
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma divergence_pushMass_eq (f : X → Y) (P : X → ℝ) (R : Y → ℝ) :
    divergence (pushMass f P) R =
      ∑ x, P x * Real.log (pushMass f P (f x) / R (f x)) :=
  sum_pushMass_mul f P (fun y => Real.log (pushMass f P y / R y))

lemma divergence_mark_chain (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (μ : Y → ℝ) (a : Y → Z → ℝ)
    (hμ : ∀ x, 0 < P x → 0 < μ (u x))
    (ha : ∀ x, 0 < P x → 0 < a (u x) (v x)) :
    divergence (pushMass (fun x => (u x,v x)) P) (fun yz => μ yz.1 * a yz.1 yz.2) =
      divergence (pushMass u P) μ +
        ∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) / a (u x) (v x)) := by
  rw [divergence_pushMass_eq,divergence_pushMass_eq,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    have hu : 0 < pushMass u P (u x) := hp.trans_le (le_pushMass _ _ hP x)
    have huv : 0 < pushMass (fun x => (u x,v x)) P (u x,v x) :=
      hp.trans_le (le_pushMass _ _ hP x)
    have hm := hμ x hp
    have ham := ha x hp
    have hc := conditionalMass_pos P hP u v x hp
    rw [Real.log_div huv.ne' (mul_pos hm ham).ne',Real.log_mul hm.ne' ham.ne',
      Real.log_div hu.ne' hm.ne',Real.log_div hc.ne' ham.ne',conditionalMass,
      Real.log_div huv.ne' hu.ne']
    ring

lemma conditional_cost_ge (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (u : X → Y) (v : X → Z) (a : Y → Z → ℝ) (ha : ∀ y z, 0 ≤ a y z)
    (hs : ∀ x, 0 < P x → 0 < a (u x) (v x)) :
    -(∑ x, P x * Real.log (∑ z, a (u x) z)) ≤
      ∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) / a (u x) (v x)) := by
  let A (y : Y) := ∑ z, a y z
  let U := pushMass (fun x => (u x,v x)) P
  let R (yz : Y × Z) := pushMass u P yz.1 * (a yz.1 yz.2 / A yz.1)
  have hA (y : Y) : 0 ≤ A y := Finset.sum_nonneg (fun z _ => ha y z)
  have hAP (x : X) (hx : 0 < P x) : 0 < A (u x) :=
    (hs x hx).trans_le (Finset.single_le_sum (fun z _ => ha (u x) z) (Finset.mem_univ (v x)))
  have hR : ∀ yz, 0 ≤ R yz := fun yz => mul_nonneg (pushMass_nonneg _ _ hP _)
    (div_nonneg (ha _ _) (hA _))
  have hm : ∑ yz, R yz ≤ ∑ yz, U yz := by
    rw [Fintype.sum_prod_type,pushMass_sum]
    calc
      _ = ∑ y, pushMass u P y * (A y / A y) := by
        apply Finset.sum_congr rfl
        intro y _
        simp only [R,← Finset.mul_sum,← Finset.sum_div,A]
      _ ≤ ∑ y, pushMass u P y := by
        apply Finset.sum_le_sum
        intro y _
        apply mul_le_of_le_one_right (pushMass_nonneg _ _ hP _)
        by_cases hy : A y = 0
        · simp [hy]
        · rw [div_self hy]
      _ = ∑ x, P x := pushMass_sum _ _
  have hsR (yz : Y × Z) (hyz : 0 < U yz) : 0 < R yz := by
    obtain ⟨x,he,hx⟩ : ∃ x, (u x,v x) = yz ∧ 0 < P x := by
      by_contra! h
      have hh : U yz ≤ 0 := by
        apply Finset.sum_nonpos
        intro x _
        split_ifs with he
        · exact h x he
        · exact le_rfl
      linarith
    subst yz
    exact mul_pos (hx.trans_le (le_pushMass _ _ hP x))
      (div_pos (hs x hx) (hAP x hx))
  have hd : 0 ≤ divergence U R := by
    have hh := mass_sub_le_divergence U R (pushMass_nonneg _ _ hP) hR hsR
    linarith
  have hchain := divergence_mark_chain P hP u v (pushMass u P) (fun y z => a y z / A y)
    (fun x hx => hx.trans_le (le_pushMass _ _ hP x))
    (fun x hx => div_pos (hs x hx) (hAP x hx))
  change divergence U R = _ at hchain
  have hself : divergence (pushMass u P) (pushMass u P) = 0 := by
    unfold divergence
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : pushMass u P y = 0
    · simp [hy]
    · simp [hy]
  rw [hself,zero_add] at hchain
  rw [hchain] at hd
  have hlog : ∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) /
      (a (u x) (v x) / A (u x))) =
      (∑ x, P x * Real.log (conditionalMass P u v (u x) (v x) / a (u x) (v x))) +
        ∑ x, P x * Real.log (A (u x)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      have hc := conditionalMass_pos P hP u v x hp
      have ham := hs x hp
      have hA' := hAP x hp
      rw [Real.log_div hc.ne' (div_pos ham hA').ne',Real.log_div ham.ne' hA'.ne',
        Real.log_div hc.ne' ham.ne']
      ring
  rw [hlog] at hd
  dsimp only [A] at hd
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]
  {Y : I → Type*} [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (Y i)] in

theorem conditional_mark_cost_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (t : (i : I) → X → Y i) (a : (i : I) → Y i → M → ℝ) (L : ℝ)
    (ha : ∀ i x, 0 < P x → 0 < a i (t i x.1) (x.2 i))
    (hdensity : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i (t i x.1) (x.2 i)) :
    (∑ i, ∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
      (fun x => x.2 i) (t i x.1) (x.2 i) / a i (t i x.1) (x.2 i))) ≤
      L - divergence (pushMass Prod.fst P) μ := by
  have hsub := conditional_marks_log P hP hm t
  have hden : (∑ x, P x * Real.log (P x)) -
      (∑ x, P x * Real.log (μ x.1)) -
        (∑ i, ∑ x, P x * Real.log (a i (t i x.1) (x.2 i))) ≤ L := by
    have hh (x : X × (I → M)) : P x * Real.log (P x) ≤
        P x * (L + Real.log (μ x.1) + ∑ i, Real.log (a i (t i x.1) (x.2 i))) := by
      by_cases hx : P x = 0
      · simp [hx]
      · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
        have hpr : 0 < ∏ i, a i (t i x.1) (x.2 i) := Finset.prod_pos (fun i _ => ha i x hp)
        have hlog := Real.log_le_log hp (hdensity x)
        rw [Real.log_mul (mul_pos (Real.exp_pos L) (hμ x.1)).ne' hpr.ne',
          Real.log_mul (Real.exp_ne_zero L) (hμ x.1).ne',Real.log_exp,
          Real.log_prod (fun i _ => (ha i x hp).ne')] at hlog
        exact mul_le_mul_of_nonneg_left hlog (hP x)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hh x)
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum] at hh
    rw [← Finset.sum_mul,hm,one_mul,Finset.sum_comm] at hh
    linarith
  have hdiv : divergence (pushMass Prod.fst P) μ =
      (∑ x, P x * Real.log (pushMass Prod.fst P x.1)) -
        ∑ x, P x * Real.log (μ x.1) := by
    rw [divergence_pushMass_eq,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      rw [Real.log_div (hp.trans_le (le_pushMass _ _ hP x)).ne' (hμ x.1).ne']
      ring
  have hcost (i : I) : (∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
      (fun x => x.2 i) (t i x.1) (x.2 i) / a i (t i x.1) (x.2 i))) =
      (∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
        (fun x => x.2 i) (t i x.1) (x.2 i))) -
      ∑ x, P x * Real.log (a i (t i x.1) (x.2 i)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : P x = 0
    · simp [hx]
    · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
      rw [Real.log_div (conditionalMass_pos _ hP _ _ x hp).ne' (ha i x hp).ne']
      ring
  simp_rw [hcost]
  rw [Finset.sum_sub_distrib,hdiv]
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]
  {Y : I → Type*} [∀ i, Fintype (Y i)]

theorem active_contact_entropy_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (t : (i : I) → X → Y i) (a : (i : I) → Y i → M → ℝ) (L : ℝ) (S : Finset I)
    (han : ∀ i y m, 0 ≤ a i y m)
    (ha : ∀ i x, 0 < P x → 0 < a i (t i x.1) (x.2 i))
    (hdensity : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i (t i x.1) (x.2 i)) :
    (∑ i ∈ S, divergence (pushMass (fun x => (t i x.1,x.2 i)) P)
      (fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2)) ≤
      (∑ i ∈ S, divergence (pushMass (fun x => t i x.1) P) (pushMass (t i) μ)) +
        L - divergence (pushMass Prod.fst P) μ +
      ∑ i ∈ Sᶜ, ∑ x, P x * Real.log (∑ m, a i (t i x.1) m) := by
  let C (i : I) := ∑ x, P x * Real.log (conditionalMass P (fun x => t i x.1)
    (fun x => x.2 i) (t i x.1) (x.2 i) / a i (t i x.1) (x.2 i))
  have hall := conditional_mark_cost_le P hP hm μ hμ t a L ha hdensity
  change (∑ i, C i) ≤ L - divergence (pushMass Prod.fst P) μ at hall
  rw [← Finset.sum_add_sum_compl S] at hall
  have hinactive : -(∑ i ∈ Sᶜ, ∑ x, P x * Real.log (∑ m, a i (t i x.1) m)) ≤
      ∑ i ∈ Sᶜ, C i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun i _ => conditional_cost_ge P hP _ _ (a i) (han i) (ha i))
  have heq (i : I) : divergence (pushMass (fun x => (t i x.1,x.2 i)) P)
      (fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2) =
        divergence (pushMass (fun x => t i x.1) P) (pushMass (t i) μ) + C i := by
    exact divergence_mark_chain P hP _ _ _ _
      (fun x _ => (hμ x.1).trans_le (le_pushMass _ _ (fun ω => (hμ ω).le) x.1)) (ha i)
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  linarith

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]
  {Y : I → Type*} [∀ i, Fintype (Y i)]

omit [∀ i, Fintype (Y i)] in
lemma inactive_contact_log_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (a : I → X → M → ℝ) (ha : ∀ i ω m, 0 ≤ a i ω m)
    (hs : ∀ i x, 0 < P x → 0 < a i x.1 (x.2 i)) (S : Finset I) :
    (∑ i ∈ S, ∑ x, P x * Real.log (∑ m, a i x.1 m)) ≤
      ∑ x, P x * logContactMass a x.1 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  rw [← Finset.mul_sum]
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    apply mul_le_mul_of_nonneg_left _ (hP x)
    calc
      _ ≤ ∑ i ∈ S, Real.log (max 1 (∑ m, a i x.1 m)) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.log_le_log ((hs i x hp).trans_le
          (Finset.single_le_sum (fun m _ => ha i x.1 m) (Finset.mem_univ _)))
          (le_max_right _ _)
      _ ≤ logContactMass a x.1 := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun i _ _ => Real.log_nonneg (le_max_left _ _))

theorem active_inverse_cost_le (P : (X × (I → M)) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (t : (i : I) → X → Y i) (a : (i : I) → Y i → M → ℝ)
    (cost : (i : I) → Y i → M → ℝ) (L : ℝ) (S : Finset I)
    (han : ∀ i y m, 0 ≤ a i y m)
    (ha : ∀ i x, 0 < P x → 0 < a i (t i x.1) (x.2 i))
    (hc : ∀ i y m, 0 ≤ cost i y m)
    (hdensity : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i (t i x.1) (x.2 i))
    (hmoment : ∀ i ∈ S, ∑ ym : Y i × M, pushMass (t i) μ ym.1 *
      a i ym.1 ym.2 * (1 + cost i ym.1 ym.2) ≤ 4) :
    (∑ i ∈ S, ∑ x, P x * Real.log (1 + cost i (t i x.1) (x.2 i))) ≤
      (∑ i ∈ S, divergence (pushMass (fun x => t i x.1) P) (pushMass (t i) μ)) +
        L - divergence (pushMass Prod.fst P) μ +
      (∑ x, P x * logContactMass (fun i ω => a i (t i ω)) x.1) +
        (S.card : ℝ) * Real.log 4 := by
  have hactive := active_contact_entropy_le P hP hm μ hμ t a L S han ha hdensity
  have hinactive := inactive_contact_log_le P hP (fun i ω => a i (t i ω))
    (fun i ω m => han i (t i ω) m) ha Sᶜ
  have hi (i : I) (hi : i ∈ S) :
      (∑ x, P x * Real.log (1 + cost i (t i x.1) (x.2 i))) ≤
        divergence (pushMass (fun x => (t i x.1,x.2 i)) P)
          (fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2) + Real.log 4 := by
    let f : X × (I → M) → Y i × M := fun x => (t i x.1,x.2 i)
    let R : Y i × M → ℝ := fun ym => pushMass (t i) μ ym.1 * a i ym.1 ym.2
    have hR : ∀ ym, 0 ≤ R ym := fun ym => mul_nonneg
      (pushMass_nonneg _ _ (fun ω => (hμ ω).le) _) (han i _ _)
    have hs (ym : Y i × M) (h : 0 < pushMass f P ym) : 0 < R ym := by
      obtain ⟨x,hx,hfx⟩ : ∃ x, 0 < P x ∧ f x = ym := by
        by_contra! hn
        have hh : pushMass f P ym ≤ 0 := by
          unfold pushMass
          apply Finset.sum_nonpos
          intro x _
          split_ifs with he
          · exact le_of_not_gt (fun hx => hn x hx he)
          · rfl
        linarith
      subst ym
      exact mul_pos ((hμ x.1).trans_le (le_pushMass _ _ (fun ω => (hμ ω).le) x.1))
        (ha i x hx)
    have hpos (ym : Y i × M) : 0 < 1 + cost i ym.1 ym.2 := by linarith [hc i ym.1 ym.2]
    have hh := entropy_inequality (pushMass f P) R (pushMass_nonneg _ _ hP) hR
      (by rw [pushMass_sum,hm]) hs (fun ym => Real.log (1 + cost i ym.1 ym.2))
    have hm' : (∑ ym, R ym * Real.exp (Real.log (1 + cost i ym.1 ym.2))) ≤ 4 := by
      simp only [Real.exp_log (hpos _)]
      exact hmoment i hi
    have hz := normalizer_pos (pushMass f P) R (pushMass_nonneg _ _ hP) hR
      (by rw [pushMass_sum,hm]) hs (fun ym => Real.log (1 + cost i ym.1 ym.2))
    have hl := Real.log_le_log hz hm'
    rw [sum_pushMass_mul] at hh
    exact hh.trans (add_le_add_right hl _)
  have hsum := Finset.sum_le_sum (fun i hi' => hi i hi')
  simp only [Finset.sum_add_distrib,Finset.sum_const, nsmul_eq_mul] at hsum
  linarith

end CriticalPercolation.FiniteEntropy
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryConfiguration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

lemma scheduleWeight_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (n : ℕ) (b : Fin n → Bool) (i : Fin n)
    (ω : E → Prop) (m : Option E) : 0 ≤ scheduleWeight G order d x p w n b i ω m :=
  G.rawContact_nonneg order _ _ hp w h0 h1 _ ω m

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryParents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.InterpolationForest.Forest
open scoped Classical

variable (F : Forest)

lemma parent_eq_previous (u v a : ℕ) (huv : F.root u ≠ F.root v)
    (ha : a ∈ F.active u v) :
    F.parent a = ((Finset.range a).filter fun b =>
      (b<2 ∨ b ∈ F.active u v) ∧ F.root b = F.root a).sup id := by
  have ha2 := (F.mem_active.mp ha).2
  apply le_antisymm
  · apply Finset.le_sup (f := id)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (F.parent_lt a ha2),
      F.active_parent ha,(F.root_step ha2).symm⟩
  · apply Finset.sup_le
    intro b hb
    obtain ⟨hba,hb,hroot⟩ := Finset.mem_filter.mp hb
    have hba' := Finset.mem_range.mp hba
    rcases hb with hb|hb
    · have hr := F.mem_lineage_le (F.root_mem_lineage (F.parent a))
      rw [← F.root_step ha2,← hroot,F.root_base hb] at hr
      exact hr
    · exact F.previous_active_le_parent huv ha hb hroot.symm hba'
end CriticalPercolation.InterpolationForest.Forest

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

lemma activeNodes_eq_descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) :
    activeNodes G d x n h ω = descriptorActive n D := by
  ext i
  constructor
  · intro hi
    have hi2 := (Forest.mem_active _).mp hi |>.2
    have hin := active_lt G d x n h ω i hi
    let j : Fin n := ⟨i-2,by omega⟩
    have hj : j.val+2=i := by dsimp [j]; omega
    refine Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hj⟩
    rw [← hD]
    simpa only [descriptor,hj,decide_eq_true_eq] using hi
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
    have ht := (Finset.mem_filter.mp hj).2
    rw [← hD] at ht
    simpa only [descriptor,decide_eq_true_eq] using ht

lemma node_eq_descriptor (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (n : ℕ) (h : History E n) (ω : Set E) (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) (i : ℕ) :
    node d x n h i = descriptorNode (E := E) d x n D i := by
  have hs := descriptor_sides G d x n h ω D hD
  unfold node descriptorNode
  rw [anchors_sides d x n h (fromWords n (fun j => (D j).1) (fun _ => (none : Option E)))
    (hs.trans (sides_fromWords n _ _).symm)]
  rfl

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Prop)
variable (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0)

include hr in
lemma node_colour_eq_iff_root (i j : ℕ) (hi : i<n+2) (hj : j<n+2) :
    (node d x n h i).2 = (node d x n h j).2 ↔
      (historyForest G d x ω n h).root i = (historyForest G d x ω n h).root j := by
  rw [node_root_colour G order d x p w _ n h ω hr i hi,
    node_root_colour G order d x p w _ n h ω hr j hj]
  have hi2 := (historyForest G d x ω n h).root_lt_two i
  have hj2 := (historyForest G d x ω n h).root_lt_two j
  split_ifs <;> simp_all <;> omega

include hr in

theorem active_parent_eq_descriptor (D : FixedDescriptor n)
    (hD : descriptor G d x n h ω = D) (i : ℕ)
    (hi : i ∈ activeNodes G d x n h ω) :
    nodeParent G d x ω n h i = descriptorParent (E := E) d x n D i := by
  have ht := terminal_roots G order d x p w s n h ω hr
  have hne : (historyForest G d x ω n h).root
      (owner G d x n h ω (x (interval d n h).1)) ≠
      (historyForest G d x ω n h).root
      (owner G d x n h ω (x (interval d n h).2)) := by rw [ht.1,ht.2]; omega
  have he := (historyForest G d x ω n h).parent_eq_previous _ _ i hne hi
  change nodeParent G d x ω n h i = _ at he
  rw [he]
  unfold descriptorParent
  congr 1
  ext j
  simp only [Finset.mem_filter]
  by_cases hj : j ∈ Finset.range i
  · simp only [hj,true_and]
    have hji := Finset.mem_range.mp hj
    have hin := active_lt G d x n h ω i hi
    rw [← activeNodes_eq_descriptor G d x n h ω D hD,
      ← node_eq_descriptor G d x n h ω D hD j,← node_eq_descriptor G d x n h ω D hD i]
    exact and_congr_right fun _ => (node_colour_eq_iff_root G order d x p w s n h ω hr j i
      (hji.trans hin) hin).symm
  · simp only [hj,false_and]

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySwitches
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph SearchTree BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma canonical_misses_targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (i : ℕ) (hin : i < n+2) (hc : Canonical G (anchors d x n h) ω i) :
    ¬∃ b ∈ targets d x n h i, (G.openGraph ω).Reachable (node d x n h i).1 b := by
  rintro ⟨b,⟨j,hji,hjb⟩,hr⟩
  exact hc j _ _ hji (node_getElem? d x n h j (hji.trans hin))
    (node_getElem? d x n h i hin) (hjb ▸ hr.symm)

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryPrefix
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest

variable {V E : Type*}

lemma anchors_prefix_getElem (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < k+2) :
    (anchors d x k (historyPrefix n h k))[i]? = (anchors d x n h)[i]? := by
  induction n with
  | zero => have he : k=0 := by omega
            subst k
            rw [prefix_self]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; rw [prefix_self]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev n h k hk',ih h.1 hk']
      change _ = (anchors d x n h.1 ++ [_])[i]?
      rw [List.getElem?_append_left (by rw [anchors_length]; omega)]

lemma node_prefix (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i < k+2) :
    node d x k (historyPrefix n h k) i = node d x n h i := by
  simp only [node,anchors_prefix_getElem d x n h k hk i hi]

lemma nodeMark_prefix (n : ℕ) (h : History E n) (k : ℕ) (hk : k ≤ n)
    (i : ℕ) (hi : i < k+2) : nodeMark k (historyPrefix n h k) i = nodeMark n h i := by
  induction n with
  | zero => have he : k=0 := by omega
            subst k
            rw [prefix_self]
  | succ n ih =>
    by_cases he : k=n+1
    · subst k; rw [prefix_self]
    · have hk' : k ≤ n := by omega
      rw [prefix_prev n h k hk',ih h.1 hk',nodeMark_old n h i (by omega)]

lemma marks_nodeMark (n : ℕ) (h : History E n) (i : Fin n) :
    marks n h i = nodeMark n h (i.val+2) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [marks,Fin.snoc_last,Fin.val_last,nodeMark_current]
    · rw [marks,Fin.snoc_castSucc,ih h.1 j,nodeMark_old n h _ (by simp)]
      rfl

lemma targets_prefix (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k ≤ n) :
    targets d x n h (k+2) = anchorSet d x k (historyPrefix n h k) := by
  ext v
  constructor
  · rintro ⟨j,hj,hjv⟩
    refine ⟨(node d x k (historyPrefix n h k) j).2,?_⟩
    have hm := node_mem d x k (historyPrefix n h k) j hj
    rw [node_prefix d x n h k hk j hj] at hm ⊢
    have heq : node d x n h j = (v, (node d x n h j).2) := Prod.ext hjv rfl
    rw [← heq]
    exact hm
  · rintro ⟨b,hb⟩
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hb
    have hjlt : j < k+2 := by
      have ht := List.getElem?_eq_some_iff.mp hj
      simpa only [anchors_length] using ht.1
    have hnode : node d x k (historyPrefix n h k) j = (v,b) := by
      simp only [node,hj,Option.getD_some]
    exact ⟨j,hjlt,congrArg Prod.fst ((node_prefix d x n h k hk j hjlt).symm.trans hnode)⟩

lemma current_prefix_anchor (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (k : ℕ) (hk : k < n) :
    (node d x n h (k+2)).1 = x (nextIndex d k (historyPrefix n h k)) := by
  have he := node_prefix d x n h (k+1) hk (k+2) (by omega)
  rw [←he,node_current]
  have hp : (historyPrefix n h (k+1)).1 = historyPrefix n h k := by
    clear he
    induction n with
    | zero => omega
    | succ n ih =>
      by_cases hn : k=n
      · subst k; rw [prefix_self,prefix_last]
      · have hk' : k<n := by omega
        rw [prefix_prev n h (k+1) (by omega),prefix_prev n h k hk'.le]
        exact ih h.1 hk'
  rw [hp]

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryCosts
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*}

lemma representative_run (f : X → Y) (x₀ x : X) :
    f (representative f x₀ (f x)) = f x := by
  unfold representative
  rw [dite_eq_left ⟨x,rfl⟩]
  exact (show ∃ y, f y = f x from ⟨x,rfl⟩).choose_spec
end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ExactExposure ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E)

lemma markWeight_eq_raw_of_admissible (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω : E → Bool) (e : E) (ha : Admissible G B a b ω e) :
    markWeight G order B a b p w ω e =
      G.rawContact order B a p w (G.clusterObject (configuration ω) B) (configuration ω) (some e) := by
  obtain ⟨hmiss,u,v,hev,hu,hv⟩ := ha
  have hau : a ∉ roots (G.openGraph (configuration ω)) B := by
    rintro ⟨z,hz,hza⟩
    exact hmiss ⟨z,hz,hza.symm⟩
  have hcut : e ∈ G.cutEdges (roots (G.openGraph (configuration ω)) B) := by
    refine ⟨u,v,hev,?_,b,hb,hv⟩
    rintro ⟨z,hz,hzu⟩
    exact hmiss ⟨z,hz,hu.trans hzu.symm⟩
  have ha' : Admissible G B a b ω e := ⟨hmiss,u,v,hev,hu,hv⟩
  simp [markWeight,rawContact,clusterObject,contactWeight,ha',hau,hcut]

lemma markWeight_le_raw (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (e : E) :
    markWeight G order B a b p w ω e ≤
      G.rawContact order B a p w (G.clusterObject (configuration ω) B) (configuration ω) (some e) := by
  by_cases ha : Admissible G B a b ω e
  · exact (G.markWeight_eq_raw_of_admissible order B a b hb p w ω e ha).le
  · rw [markWeight,ite_eq_right ha]
    exact G.rawContact_nonneg order B a hp w h0 h1 _ _ _

lemma rawContact_ne_zero_of_kernel (order : List (LazyDFS.Dart V E))
    (B : Set V) (a : V) (p : ℝ) (w : E → Prop → ℝ)
    (C : ClusterObject V E) (ω : E → Prop) (m : Option E)
    (hk : G.contactKernel order B a p w C ω m ≠ 0) :
    G.rawContact order B a p w C ω m ≠ 0 := by
  unfold contactKernel rawContact at *
  split_ifs at *
  · exact one_ne_zero
  · exact hk
  · cases m with
    | none => exact hk
    | some e => exact (div_ne_zero_iff.mp hk).1
end CriticalPercolation.BondGraph

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

lemma descriptorParent_lt (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n)
    (i : ℕ) (hi : 0 < i) : descriptorParent (E := E) d x n D i < i := by
  unfold descriptorParent
  exact (Finset.sup_lt_iff hi).mpr (fun j hj => Finset.mem_range.mp (Finset.mem_filter.mp hj).1)

lemma scheduledAnchor_node (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    scheduledAnchor (E := E) d x n (fun j => (D j).1) i.val =
      (descriptorNode (E := E) d x n D (i.val+2)).1 :=
  (current_prefix_anchor d x n _ i.val i.isLt).symm

lemma scheduledTargets_nodes (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    scheduledTargets (E := E) d x n (fun j => (D j).1) i.val =
      {v | ∃ j < i.val+2, (descriptorNode (E := E) d x n D j).1=v} :=
  (targets_prefix d x n _ i.val i.isLt.le).symm

lemma scheduled_parent_mem (d : ℕ) (x : ℕ → V) (n : ℕ) (D : FixedDescriptor n) (i : Fin n) :
    (descriptorNode (E := E) d x n D (descriptorParent (E := E) d x n D (i.val+2))).1 ∈
      scheduledTargets (E := E) d x n (fun j => (D j).1) i.val := by
  rw [scheduledTargets_nodes]
  exact ⟨_,descriptorParent_lt d x n D _ (by omega),rfl⟩

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_active_admissible (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0)
    (i : ActiveIndex n D) :
    ∃ e, m i.val = some e ∧ Admissible G
      (scheduledTargets (E := E) d x n (fun j => (D j).1) i.val.val)
      (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i) ω e := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hi : i.val.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.property⟩,rfl⟩
  have hn := active_nonhold G order d x p w _ n h _ hr _ hi
  obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hn
  refine ⟨e,?_,?_⟩
  · have hm := marks_nodeMark n h i.val
    rw [marks_fromWords] at hm
    exact hm.trans he
  · have hc := active_canonical G order d x p w _ n h _ hr _ hi
    have hmiss := canonical_misses_targets G d x n h _ _ (by have := i.val.isLt; omega) hc
    obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w _ n h _ hr _ (by omega)
      (by have := i.val.isLt; omega) e he
    have hl : (node d x n h (i.val.val+2)).1 = activeLeft (E := E) d x n D i :=
      congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
    have hr' : (node d x n h (nodeParent G d x (configuration ω) n h (i.val.val+2))).1 =
        activeRight (E := E) d x n D i := by
      rw [active_parent_eq_descriptor G order d x p w s n h _ hr D hD _ hi]
      exact congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
    have ht : targets d x n h (i.val.val+2) =
        scheduledTargets (E := E) d x n (fun j => (D j).1) i.val.val := by
      rw [targets_prefix d x n h _ i.val.isLt.le,scheduledTargets_eq d x n _ m _ i.val.isLt.le]
    rw [hl,ht] at hmiss
    exact ⟨hmiss,u,v,hev,hl ▸ hu,hr' ▸ hv⟩

lemma supported_schedule_ne_zero (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) ≠ 0 := by
  obtain ⟨_,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hp := density_prefix_support G order d x p w _ n h _ hr (i.val+1) i.isLt
  have hk := (density_step_support G order d x p w _ i.val (historyPrefix n h (i.val+1)) _ hp).2.1
  have hm : (historyPrefix n h (i.val+1)).2.2 = m i := by
    rw [← nodeMark_current,nodeMark_prefix n h (i.val+1) i.isLt (i.val+2) (by omega)]
    rw [← marks_nodeMark,marks_fromWords]
  rw [prefix_succ_fst n h i.val i.isLt,hm] at hk
  unfold scheduleWeight
  rw [scheduledTargets_eq d x n _ m i.val i.isLt.le,scheduledAnchor_eq d x n _ m i.val i.isLt.le]
  exact G.rawContact_ne_zero_of_kernel order _ _ p w _ _ _ hk

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryTranscript
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*}

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

lemma selected_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) (m : Option E) :
    0 ≤ selectedWeight G order d x p w n D i ω m ∧
      0 ≤ selectedCost G order d x p w n D i ω m := by
  unfold selectedWeight selectedCost
  split_ifs
  · cases m with
    | none => exact ⟨le_rfl,le_rfl⟩
    | some e => exact mark_nonneg G order _ _ _ hp w h0 h1 ω e
  · exact ⟨scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m,le_rfl⟩

lemma selected_run (i : Fin n) (ω : E → Bool) (m : Option E) :
    selectedWeight G order d x p w n D i (selectedTranscript G d x n D i ω) m =
      selectedWeight G order d x p w n D i ω m ∧
    selectedCost G order d x p w n D i (selectedTranscript G d x n D i ω) m =
      selectedCost G order d x p w n D i ω m := by
  unfold selectedWeight selectedCost selectedTranscript
  split_ifs with hi
  · cases m with
    | none => exact ⟨rfl,rfl⟩
    | some e =>
      exact pair_mark_congr G order _ _ _ (scheduled_parent_mem d x n D i) p w _ ω
        (representative_run (pairQuery G d x n D i).run (fun _ => false) ω) e
  · exact ⟨rfl,rfl⟩

lemma selectedWeight_le_raw (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) (m : Option E) :
    selectedWeight G order d x p w n D i ω m ≤
      scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m := by
  unfold selectedWeight
  split_ifs
  · cases m with
    | none => exact scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ none
    | some e =>
      unfold scheduleWeight
      rw [scheduledAnchor_node]
      exact G.markWeight_le_raw order _ _ _ (scheduled_parent_mem d x n D i) hp w h0 h1 ω e
  · exact le_rfl

lemma supported_selected_eq (s : ℕ) (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    selectedWeight G order d x p w n D i ω (m i) =
      scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) := by
  unfold selectedWeight
  split_ifs with hi
  · obtain ⟨e,he,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz ⟨i,hi⟩
    dsimp only at he ha
    rw [he]
    unfold scheduleWeight
    rw [scheduledAnchor_node]
    exact G.markWeight_eq_raw_of_admissible order _ _ _ (scheduled_parent_mem d x n D i) p w ω e ha
  · rfl

lemma supported_selected_positive (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (z : (E → Bool) × (Fin n → Option E))
    (hz : 0 < conditionedMass G order d x p w s n D z) (i : Fin n) :
    0 < selectedWeight G order d x p w n D i (selectedTranscript G d x n D i z.1) (z.2 i) := by
  rw [(selected_run G order d x p w n D i z.1 (z.2 i)).1,
    supported_selected_eq G order d x p w n D s z.1 z.2 hz.ne' i]
  exact lt_of_le_of_ne (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _)
    (Ne.symm (supported_schedule_ne_zero G order d x p w s n D z.1 z.2 hz.ne' i))

lemma selected_moment (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (i : Fin n) (hi : i ∈ activeSteps n D) :
    (∑ ym : (E → Bool) × Option E,
      pushMass (selectedTranscript G d x n D i) (FiniteProduct.density (QueryTree.bitWeight p)) ym.1 *
      selectedWeight G order d x p w n D i ym.1 ym.2 *
        (1+selectedCost G order d x p w n D i ym.1 ym.2)) ≤ 4 := by
  have hi' : (D i).2.2 = true := (Finset.mem_filter.mp hi).2
  rw [Fintype.sum_prod_type]
  simp_rw [mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [sum_pushMass_mul]
  simp_rw [(selected_run G order d x p w n D i _ _).1,
    (selected_run G order d x p w n D i _ _).2]
  simp only [selectedWeight,selectedCost,ite_eq_left hi',Fintype.sum_option,zero_mul,zero_add]
  exact marked_pair_bound_bs G order horder ho _ _ _ (scheduled_parent_mem d x n D i) hp w h0 h1

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryInverseCost
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

omit [Fintype V] in
lemma pairQuery_valid (i : Fin n) : (pairQuery G d x n D i).Valid ∅ :=
  SearchTree.bare_valid _ _ (ExactExposure.compile_valid G _ _)

omit [Fintype V] in
lemma selected_entropy_le (hp : p ∈ Set.Ioo 0 1) (P : (E → Bool) → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (i : Fin n) (hi : i ∈ activeSteps n D) :
    divergence (pushMass (selectedTranscript G d x n D i) P)
      (pushMass (selectedTranscript G d x n D i) (FiniteProduct.density (QueryTree.bitWeight p))) ≤
      divergence (pushMass (pairQuery G d x n D i).run P) ((pairQuery G d x n D i).reference p) := by
  let t := pairQuery G d x n D i
  let r := representative t.run (fun _ => false)
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  have ht : selectedTranscript G d x n D i = r ∘ t.run := by
    funext ω
    exact ite_eq_left (Finset.mem_filter.mp hi).2
  rw [ht,← pushMass_comp,← pushMass_comp]
  have href := QueryTree.reference_eq_product_push p t ∅ (pairQuery_valid G d x n D i)
  rw [href]
  exact divergence_pushMass_le r (pushMass t.run P) (t.reference p)
    (pushMass_nonneg _ _ hP) (fun y => (QueryTree.reference_pos hp t y).le)
    (fun y _ => QueryTree.reference_pos hp t y)

lemma selected_contactLog_le (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (ω : E → Bool) :
    logContactMass (fun i η => selectedWeight G order d x p w n D i
      (selectedTranscript G d x n D i η)) ω ≤
      logContactMass (fun i η => scheduleWeight G order d x p w n (fun j => (D j).1)
        i (configuration η)) ω := by
  apply Finset.sum_le_sum
  intro i _
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left 1 _))
  apply max_le_max_left
  apply Finset.sum_le_sum
  intro m _
  change selectedWeight G order d x p w n D i (selectedTranscript G d x n D i ω) m ≤
    scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) m
  rw [(selected_run G order d x p w n D i ω m).1]
  exact selectedWeight_le_raw G order d x p w n D hp h0 h1 i ω m

noncomputable section Cost

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.inverseCostFinDec
theorem conditioned_inverse_cost_bs_oai (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0 < d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hconn : ∀ j, 0 < j → j < d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let Q := conditionedMass G order d x p w s n D
    let L := constructionCost G order d x p w c s n D
    (∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) ≤
      (16/(2*p*(1-p)))*(2*L+n*Real.log 4) + 2*L+2*n*Real.log 4 := by
  dsimp only
  let Q := conditionedMass G order d x p w s n D
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  let P := pushMass Prod.fst Q
  let L := constructionCost G order d x p w c s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hμ : ∀ ω, 0 < μ ω := fun ω => Finset.prod_pos fun e _ => QueryTree.bitWeight_pos hp e (ω e)
  have hh := active_inverse_cost_le Q hQ hQ1 μ hμ
    (selectedTranscript G d x n D) (selectedWeight G order d x p w n D)
    (selectedCost G order d x p w n D) L (activeSteps n D)
    (fun i ω m => (selected_nonneg G order d x p w n D hp h0 h1 i ω m).1)
    (fun i z hz => supported_selected_positive G order d x p w n D s hp h0 h1 z hz i)
    (fun i ω m => (selected_nonneg G order d x p w n D hp h0 h1 i ω m).2)
    (selected_density_le_bs G order d x p w s n D hd hp h0 h1 hc hc1 hconn hδ hD)
    (selected_moment G order d x p w n D horder ho hp h0 h1)
  simp_rw [(selected_run G order d x p w n D _ _ _).2] at hh
  have hpair : (∑ i ∈ activeSteps n D,
      divergence (pushMass (fun z => selectedTranscript G d x n D i z.1) Q)
        (pushMass (selectedTranscript G d x n D i) μ)) ≤ (16/(2*p*(1-p)))*divergence P μ := by
    calc
      _ = ∑ i ∈ activeSteps n D,
        divergence (pushMass (selectedTranscript G d x n D i) P)
          (pushMass (selectedTranscript G d x n D i) μ) := by
        simp only [P,pushMass_comp,Function.comp_def]
      _ ≤ ∑ i ∈ activeSteps n D,
        divergence (pushMass (pairQuery G d x n D i).run P) ((pairQuery G d x n D i).reference p) :=
          Finset.sum_le_sum fun i hi => selected_entropy_le G d x p n D hp P (pushMass_nonneg _ _ hQ) i hi
      _ ≤ _ := by
        rw [Finset.sum_subtype (activeSteps n D) (p := fun i => (D i).2.2 = true)
          (fun i => by simp only [activeSteps,Finset.mem_filter,Finset.mem_univ,true_and])]
        exact conditioned_pair_entropy_bs G order d x p w s n D hp h0 h1 hδ hD
  have hconf := conditioned_configuration_entropy_bs G order d x p w ho hd hp h0 h1 hc hc1 hconn s n D hδ hD
  have hlog : (∑ z, Q z * logContactMass (fun i ω => selectedWeight G order d x p w n D i
      (selectedTranscript G d x n D i ω)) z.1) ≤ L+n*Real.log 4 := by
    exact (Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
      (selected_contactLog_le G order d x p w n D hp h0 h1 z.1) (hQ z)).trans hconf.2
  have hdiv : 0 ≤ divergence P μ := by
    have he := mass_sub_le_divergence P μ (pushMass_nonneg _ _ hQ) (fun ω => (hμ ω).le) (fun ω _ => hμ ω)
    have hm : ∑ ω, μ ω = 1 := FiniteProduct.sum_density _ (QueryTree.bitWeight_sum p)
    rw [pushMass_sum,hQ1,hm,sub_self] at he
    exact he
  have hcard : ((activeSteps n D).card : ℝ) ≤ n := by
    have he : (activeSteps n D).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    simpa using (Nat.cast_le (α := ℝ)).mpr he
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hCp : 0 ≤ 16/(2*p*(1-p)) :=
    div_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hp.1.le) (sub_nonneg.mpr hp.2.le))
  have hbound := mul_le_mul_of_nonneg_left hconf.1 hCp
  have hcard' := mul_le_mul_of_nonneg_right hcard hlog4
  change _ ≤ (16/(2*p*(1-p)))*(2*L+n*Real.log 4)+2*L+2*n*Real.log 4
  linarith

end Cost
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs_oai.{u_1, u_2}
