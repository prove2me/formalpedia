-- Prove2me | solution 1 for OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T13:41:20.413721+00:00
-- url     : https://prove2.me/submissions/f883a101-0d61-4e56-bdd4-726ff6daf7f6

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

variable {X I M : Type*} [Fintype X] [Fintype I] [Fintype M]

omit [Fintype X] in
lemma exp_logContactMass (a : I → X → M → ℝ) (ω : X) :
    Real.exp (logContactMass a ω) = ∏ i, max 1 (∑ m, a i ω m) := by
  rw [logContactMass,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

end CriticalPercolation.FiniteEntropy

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_ReverseReference
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*} [Fintype M]

omit [Fintype M] in
lemma weight_nonneg (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (hk : ∀ i x m, 0 ≤ k i x m) (n : ℕ) (x : X) (m : Fin n → M) :
    0 ≤ weight k u n x m := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hk _ _ _) (ih _ _)

section Terminal
variable [Fintype X] {I : Type*} [Fintype I]

omit [Fintype M] [Fintype X] in
lemma terminalWeight_nonneg (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m)
    (x : X) (m : I → M) : 0 ≤ terminalWeight a x m :=
  Finset.prod_nonneg fun i _ => ha i x (m i)

omit [Fintype M] [Fintype X] in
lemma joint_nonneg (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m) (n : ℕ) (z) :
    0 ≤ joint μ k u a n z :=
  mul_nonneg (mul_nonneg (hμ _) (weight_nonneg k u hk _ _ _)) (terminalWeight_nonneg a ha _ _)

end Terminal
end CriticalPercolation.ReverseReference

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryInterpolation
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryInterpolation
open scoped Classical

lemma midpoint_strict {l r : ℕ} (h : l+1 < r) :
    l < midpoint l r ∧ midpoint l r < r := by
  dsimp [midpoint]
  omega

lemma bisect_bounds {l r : ℕ} (h : l < r) (b : Bool) :
    l ≤ (bisect l r b).1 ∧ (bisect l r b).1 < (bisect l r b).2 ∧
      (bisect l r b).2 ≤ r := by
  unfold bisect
  split_ifs with ht hb
  · simp [h]
  · have hm := midpoint_strict (by omega : l+1 < r)
    simp only
    omega
  · have hm := midpoint_strict (by omega : l+1 < r)
    simp only
    omega

end CriticalPercolation.BinaryInterpolation
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

lemma queryDelta_zero_used (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (e : E) (he : e ∈ used) :
    T.queryDelta F w ω e = 0 := by
  induction T generalizing used w with
  | done _ => rfl
  | ask f l r hl hr =>
    have hef : e ≠ f := fun h => hT.1 (h ▸ he)
    simp only [queryDelta,ite_eq_right hef]
    split_ifs
    · exact hr _ hT.2.2 _ (Finset.mem_insert_of_mem he)
    · exact hl _ hT.2.1 _ (Finset.mem_insert_of_mem he)

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

lemma interval_bounds {E : Type*} {d : ℕ} (hd : 0<d) (n : ℕ) (h : History E n) :
    (interval d n h).1 < (interval d n h).2 ∧ (interval d n h).2 ≤ d := by
  induction n with
  | zero => exact ⟨hd,le_rfl⟩
  | succ n ih =>
    have hi := ih h.1
    have hb := bisect_bounds hi.1 h.2.1
    exact ⟨hb.2.1,hb.2.2.trans hi.2⟩

lemma nextIndex_bounds {E : Type*} {d : ℕ} (hd : 0<d) (n : ℕ) (h : History E n) :
    (interval d n h).1 ≤ nextIndex d n h ∧ nextIndex d n h < (interval d n h).2 := by
  have hi := (interval_bounds hd n h).1
  unfold nextIndex
  split_ifs with ht
  · exact ⟨le_rfl,hi⟩
  · have hm := midpoint_strict (by omega : (interval d n h).1+1 < (interval d n h).2)
    exact ⟨hm.1.le,hm.2⟩

lemma anchors_length {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    (anchors d x n h).length = n+2 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [anchors,List.length_append,List.length_singleton,ih]

lemma anchorSet_step {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E (n+1)) :
    anchorSet d x (n+1) h = insert (x (nextIndex d n h.1)) (anchorSet d x n h.1) := by
  ext v
  constructor
  · rintro ⟨b,hb⟩
    rcases List.mem_append.mp hb with hb | hb
    · exact Or.inr ⟨b,hb⟩
    · exact Or.inl (congrArg Prod.fst (List.mem_singleton.mp hb))
  · rintro (rfl | ⟨b,hb⟩)
    · exact ⟨h.2.1,List.mem_append_right _ (List.mem_singleton_self _)⟩
    · exact ⟨b,List.mem_append_left _ hb⟩

lemma firstIndex_spec {P : ℕ → Prop} (h : ∃ j, P j) : P (firstIndex P) := by
  rw [firstIndex,dite_eq_left h]
  exact Nat.find_spec h

lemma firstIndex_le {P : ℕ → Prop} {j : ℕ} (hj : P j) : firstIndex P ≤ j := by
  rw [firstIndex,dite_eq_left ⟨j,hj⟩]
  exact Nat.find_min' _ hj

variable {V E : Type*} (G : BondGraph V E)

lemma base_left_mem {V E : Type*} (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) :
    x 0 ∈ anchorSet d x n h := by
  induction n with
  | zero => exact ⟨true,by simp [anchors]⟩
  | succ n ih => rw [anchorSet_step]; exact Or.inr (ih h.1)

lemma root_bound [Fintype E] {d : ℕ} (hd : 0<d) (x : ℕ → V)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    {c : ℝ} (hc1 : c≤1)
    (hc : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (n : ℕ) (h : History E n) :
    c ≤ prob w (fun ω => ∃ b ∈ anchorSet d x n h,
      (G.openGraph ω).Reachable (x (nextIndex d n h)) b) := by
  let j := nextIndex d n h
  have hj : j<d := (nextIndex_bounds hd n h).2.trans_le (interval_bounds hd n h).2
  by_cases hj0 : j=0
  · have he : prob w (fun ω => ∃ b ∈ anchorSet d x n h,
        (G.openGraph ω).Reachable (x j) b) = 1 := by
      calc
        _ = prob w (fun _ => True) := prob_congr w (fun ω => ⟨fun _ => True.intro,
          fun _ => ⟨x 0,base_left_mem d x n h,hj0 ▸ SimpleGraph.Reachable.refl _⟩⟩)
        _ = 1 := prob_true w hw
    exact hc1.trans_eq he.symm
  · exact (hc j (by omega) hj).trans (prob_mono w hn (fun ω hr =>
      ⟨x 0,base_left_mem d x n h,hr.symm⟩))

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

lemma canonical_distinct (L : List (V × Bool)) (ω : Set E) (i j : ℕ)
    (hi : Canonical G L ω i) (hj : Canonical G L ω j)
    (z t : V × Bool) (hz : L[i]? = some z) (ht : L[j]? = some t)
    (hr : (G.openGraph ω).Reachable z.1 t.1) : i=j := by
  rcases lt_trichotomy i j with hij|hij|hij
  · exact (hj i z t hij hz ht hr).elim
  · exact hij
  · exact (hi j t z hij ht hz hr.symm).elim

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

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma canonical_node_reachable_eq (n : ℕ) (h : History E n) (ω : Set E)
    (i j : ℕ) (hin : i < n+2) (hjn : j < n+2)
    (hi : Canonical G (anchors d x n h) ω i) (hj : Canonical G (anchors d x n h) ω j)
    (hr : (G.openGraph ω).Reachable (node d x n h i).1 (node d x n h j).1) : i=j :=
  canonical_distinct G _ ω i j hi hj _ _ (node_getElem? d x n h i hin)
    (node_getElem? d x n h j hjn) hr

lemma selected_marks_injective (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) (hin : i < n+2) (hjn : j < n+2)
    (e : E) (he : nodeMark n h i = some e) (he' : nodeMark n h j = some e) : i=j := by
  have hic := (canonical_iff_nonhold G order d x p w r₀ n h ω hr i hi hin).mpr
    (by rw [he]; exact Option.some_ne_none e)
  have hjc := (canonical_iff_nonhold G order d x p w r₀ n h ω hr j hj hjn).mpr
    (by rw [he']; exact Option.some_ne_none e)
  have hip := nodeParent_canonical G order d x p w r₀ n h ω hr i hi hin
  have hjp := nodeParent_canonical G order d x p w r₀ n h ω hr j hj hjn
  have hiplt := nodeParent_lt G d x ω n h i hi
  have hjplt := nodeParent_lt G d x ω n h j hj
  obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi hin e he
  obtain ⟨_,u',v',hev',hu',hv'⟩ := node_mark_geometry G order d x p w r₀ n h ω hr j hj hjn e he'
  rcases Sym2.eq_iff.mp (hev.symm.trans hev') with ⟨huu,hvv⟩|⟨huv,hvu⟩
  · apply canonical_node_reachable_eq G d x n h ω i j hin hjn hic hjc
    exact hu.trans (huu ▸ hu'.symm)
  · have h1 : i = nodeParent G d x ω n h j :=
      canonical_node_reachable_eq G d x n h ω i _ hin (hjplt.trans hjn) hic hjp
        (hu.trans (huv ▸ hv'.symm))
    have h2 : j = nodeParent G d x ω n h i :=
      canonical_node_reachable_eq G d x n h ω j _ hjn (hiplt.trans hin) hjc hip
        (hu'.trans (hvu.symm ▸ hv.symm))
    omega

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Modular_Mass
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

namespace CriticalPercolation.ReverseGuess

lemma step_bound {s b : ℝ} (hs : 0 ≤ s) (hb : 0 ≤ b) :
    b / (1+s+b)^2 + 1 / (1+s+b) ≤ 1 / (1+s) := by
  have ha : 0 < 1+s := by linarith
  have hab : 0 < 1+s+b := by linarith
  calc
    b / (1+s+b)^2 + 1 / (1+s+b) ≤
        b / ((1+s)*(1+s+b)) + 1 / (1+s+b) := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_left hb (mul_pos ha hab)
      nlinarith
    _ = 1 / (1+s) := by field_simp; ring

end CriticalPercolation.ReverseGuess

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_ReverseGuess
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

lemma reverseMass_eq_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) (s : ℝ) :
    T.reverseMass p F w ω s = ∑ e, T.reverseGuess p F w ω s e := by
  induction T generalizing used w s with
  | done _ => simp [reverseMass,reverseGuess,queryDelta,prefixScore]
  | ask f l r hl hr =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) /
          (1+s+(b+if e=f then 0 else T'.prefixScore p F w' ω e))^2) =
        b/(1+s+b)^2 + ∑ e, T'.reverseGuess p F w' ω (s+b) e := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) /
          (1+s+(b+if e=f then 0 else T'.prefixScore p F w' ω e))^2 =
          (if e=f then b/(1+s+b)^2 else 0) + T'.reverseGuess p F w' ω (s+b) e := by
        by_cases he : e=f
        · subst e
          simp [reverseGuess,hz,b]
        · simp only [ite_eq_right he,reverseGuess,zero_add]
          congr 2; ring
      simp only [heq,Finset.sum_add_distrib]
      simp
    rw [reverseMass]
    by_cases hf : ω f
    · simp only [ite_eq_left hf]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
      simp only [reverseGuess,queryDelta,prefixScore,ite_eq_left hf]
      rfl
    · simp only [ite_eq_right hf]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]
      simp only [reverseGuess,queryDelta,prefixScore,ite_eq_right hf]
      rfl

lemma reverseMass_bound (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ a b, a ⊆ b → F a → F b) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ T.reverseMass p F w ω s ∧ T.reverseMass p F w ω s ≤ 1/(1+s) := by
  induction T generalizing used w s with
  | done _ => exact ⟨le_rfl, div_nonneg zero_le_one (by linarith)⟩
  | ask f l r hl hr =>
    let b := if openPivot F f ω then (1-p)*delta w F f else 0
    have hf0 : w f False ≠ 0 := by rw [(hf f hT.1).1]; linarith [hp.2]
    have hf1 : w f True ≠ 0 := by rw [(hf f hT.1).2]; exact hp.1.ne'
    have hb : 0 ≤ b := by
      dsimp [b]
      split_ifs
      · exact mul_nonneg (sub_nonneg.mpr hp.2.le) (delta_unit w hw hn f hf0 hf1 F hF).1
      · exact le_rfl
    have hb' : 0 ≤ b/(1+s+b)^2 := div_nonneg hb (sq_nonneg _)
    have hs' : 0 ≤ s+b := add_nonneg hs hb
    have step {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1/(1+(s+b))) :
        0 ≤ b/(1+s+b)^2+x ∧ b/(1+s+b)^2+x ≤ 1/(1+s) := by
      refine ⟨add_nonneg hb' hx.1, ?_⟩
      calc
        _ ≤ b/(1+s+b)^2 + 1/(1+(s+b)) := add_le_add_right hx.2 _
        _ ≤ _ := by simpa only [add_assoc] using ReverseGuess.step_bound hs hb
    simp only [reverseMass]
    by_cases hbit : ω f
    · simp only [ite_eq_left hbit]
      exact step (hr _ hT.2.2 _ (pin_normalized w hw f True)
        (pin_nonneg w hn f True) (fresh_pin w p used hf f True) hs')
    · simp only [ite_eq_right hbit]
      exact step (hl _ hT.2.1 _ (pin_normalized w hw f False)
        (pin_nonneg w hn f False) (fresh_pin w p used hf f False) hs')

theorem reverseGuess_subprobability (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ a b, a ⊆ b → F a → F b) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) :
    (∀ e, 0 ≤ T.reverseGuess p F w ω 0 e) ∧ (∑ e, T.reverseGuess p F w ω 0 e) ≤ 1 := by
  constructor
  · intro e
    apply div_nonneg _ (sq_nonneg _)
    split_ifs
    · exact mul_nonneg (sub_nonneg.mpr hp.2.le)
        (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
    · exact le_rfl
  · rw [← reverseMass_eq_sum T used hT]
    simpa using (reverseMass_bound T used hT hp F hF w hw hn hf ω (s := 0) le_rfl).2

end CriticalPercolation.SearchTree

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_BitWeight
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
lemma bitWeight_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) (e : E) (b : Bool) :
    0 ≤ bitWeight p e b := by cases b <;> simp [bitWeight, hp.1, hp.2]

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
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*}

lemma admissible_closed (G : BondGraph V E) (B : Set V) (a b : V) (hb : b ∈ B)
    (ω : E → Bool) (f : E) (h : Admissible G B a b ω f) : ¬configuration ω f := by
  obtain ⟨hn,u,v,hf,hu,hv⟩ := h
  intro hopen
  exact hn ⟨b,hb,hu.trans ((LazyDFS.prop_openEdge_reachable G _ hopen hf).trans hv.symm)⟩

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

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

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

lemma contactKernel_le_raw (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (C : ClusterObject V E) (ω : E → Prop) (mark : Option E)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hroot : c ≤ prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)) :
    G.contactKernel order B a p w C ω mark ≤ c⁻¹ * G.rawContact order B a p w C ω mark := by
  unfold contactKernel rawContact
  split_ifs with ha hm
  · rw [mul_one]
    exact (one_le_inv₀ hc).mpr hc1
  · simp
  · cases mark with
    | none => simp
    | some e =>
      rw [← div_eq_inv_mul]
      exact div_le_div_of_nonneg_left (G.contactWeight_nonneg order B C.1 a hp w h0 h1 ω e) hc hroot

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

section Products
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

lemma rawProduct_nonneg (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p)
    (h1 : ∀ e, w e True = p) (n : ℕ) (h : History E n) (ω : E → Prop) :
    0 ≤ rawProduct G order d x p w n h ω := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (ih h.1) (G.rawContact_nonneg order _ _ hp w h0 h1 _ ω _)

lemma density_le_rawProduct (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (r₀ : (E → Prop) → ℝ) (hr₀ : ∀ ω, 0 ≤ r₀ ω)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (n : ℕ) (h : History E n) (ω : E → Prop) :
    density G order d x p w r₀ n h ω ≤
      r₀ ω * (c⁻¹)^n * rawProduct G order d x p w n h ω := by
  induction n with
  | zero => simp only [density,rawProduct,pow_zero,mul_one,le_refl]
  | succ n ih =>
    rw [density,rawProduct,pow_succ]
    have hr := root_bound G hd x w (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le) hc1 hconn n h.1
    have hk := G.contactKernel_le_raw order (anchorSet d x n h.1)
      (x (nextIndex d n h.1)) hp w h0 h1 (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2 hc hc1 hr
    have hpos := rawProduct_nonneg G order d x p w hp h0 h1 n h.1 ω
    have hraw := G.rawContact_nonneg order (anchorSet d x n h.1)
      (x (nextIndex d n h.1)) hp w h0 h1 (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2
    split_ifs
    · calc
        _ ≤ (r₀ ω * (c⁻¹)^n * rawProduct G order d x p w n h.1 ω) *
            (c⁻¹ * G.rawContact order (anchorSet d x n h.1) (x (nextIndex d n h.1)) p w
              (G.clusterObject ω (anchorSet d x n h.1)) ω h.2.2) :=
          mul_le_mul (ih h.1) hk (G.contactKernel_nonneg order _ _ hp w h0 h1 _ ω _)
            (mul_nonneg (mul_nonneg (hr₀ ω) (pow_nonneg (inv_nonneg.mpr hc.le) n)) hpos)
        _ = _ := by ring
    · exact mul_nonneg (mul_nonneg (hr₀ ω)
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr hc.le) n) (inv_nonneg.mpr hc.le)))
        (mul_nonneg hpos hraw)

lemma rawProduct_eq_finprod (n : ℕ) (h : History E n) (ω : E → Prop) :
    rawProduct G order d x p w n h ω =
      ∏ i : Fin n, G.rawContact order (anchorSet d x i.val (historyPrefix n h i.val))
        (x (nextIndex d i.val (historyPrefix n h i.val))) p w
        (G.clusterObject ω (anchorSet d x i.val (historyPrefix n h i.val))) ω (marks n h i) := by
  induction n with
  | zero => simp only [rawProduct,Fin.prod_univ_zero]
  | succ n ih =>
    rw [Fin.prod_univ_castSucc,rawProduct,ih h.1]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro i _
      simp only [Fin.val_castSucc,prefix_prev n h i.val i.isLt.le,marks,Fin.snoc_castSucc]
    · simp only [Fin.val_last,prefix_last,marks,Fin.snoc_last]

lemma rawProduct_words (n : ℕ) (b : Fin n → Bool) (m : Fin n → Option E) (ω : E → Prop) :
    rawProduct G order d x p w n (fromWords n b m) ω =
      ∏ i, scheduleWeight G order d x p w n b i ω (m i) := by
  rw [rawProduct_eq_finprod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [scheduleWeight,scheduledTargets_eq d x n b m i.val i.isLt.le,
    scheduledAnchor_eq d x n b m i.val i.isLt.le,marks_fromWords]

end Products
end CriticalPercolation.BinaryLaw
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

lemma density_seed_le_rawProduct (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (n : ℕ) (h : History E n) (ω : E → Prop) :
    density G order d x p w (seed G w (x 0) (x d) s) n h ω ≤
      (prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n * rawProduct G order d x p w n h ω := by
  apply (density_le_rawProduct G order d x p w hd hp h0 h1 _
    (seed_nonneg G w _ _ s hδ) hc hc1 hconn n h ω).trans
  apply mul_le_mul_of_nonneg_right _ (rawProduct_nonneg G order d x p w hp h0 h1 n h ω)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hc.le) n)
  unfold seed
  split_ifs <;> simp only [mul_one,mul_zero,le_refl,inv_nonneg.mpr hδ.le]

lemma exp_constructionCost (c : ℝ) (hc : 0 < c) (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    Real.exp (constructionCost G order d x p w c s n D) =
      (prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n /
        descriptorMass G order d x p w s n D :=
  Real.exp_log (div_pos (mul_pos (inv_pos.mpr hδ) (pow_pos (inv_pos.mpr hc) n)) hD)

theorem conditionedMass_density_le (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) :
    conditionedMass G order d x p w s n D z ≤
      Real.exp (constructionCost G order d x p w c s n D) *
        FiniteProduct.density (QueryTree.bitWeight p) z.1 *
        ∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration z.1) (z.2 i) := by
  rw [exp_constructionCost G order d x p w c hc s n D hδ hD]
  have hμ : 0 ≤ FiniteProduct.density (QueryTree.bitWeight p) z.1 :=
    FiniteProduct.density_nonneg (fun e b => (QueryTree.bitWeight_pos hp e b).le) _
  unfold conditionedMass fixedMass
  dsimp only
  split_ifs
  · have hr := density_seed_le_rawProduct G order d x p w hd hp h0 h1 hc hc1 hconn s hδ n
      (fromWords n (fun j => (D j).1) z.2) (configuration z.1)
    erw [rawProduct_words] at hr
    unfold jointMass
    dsimp only
    calc
      _ ≤ (FiniteProduct.density (QueryTree.bitWeight p) z.1 *
          ((prob w (endpointEvent G (x 0) (x d) s))⁻¹ * (c⁻¹)^n *
            ∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration z.1) (z.2 i))) /
          descriptorMass G order d x p w s n D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr hμ) hD.le
      _ = _ := by ring
  · rw [zero_div]
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (inv_nonneg.mpr hδ.le)
      (pow_nonneg (inv_nonneg.mpr hc.le) n)) hD.le) hμ)
      (Finset.prod_nonneg fun i _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _)

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

lemma switched_mono (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ) :
    ω ⊆ switched n h ω S := fun _ he => Or.inl he

lemma switched_insert (n : ℕ) (h : History E n) (ω : Set E) (S : Finset ℕ)
    (i : ℕ) (e : E) (hm : nodeMark n h i = some e) :
    switched n h ω (insert i S) = Function.update (switched n h ω S) e True := by
  apply Set.ext
  intro f
  change (ω f ∨ ∃ j ∈ insert i S, nodeMark n h j = some f) ↔
    (Function.update (switched n h ω S : E → Prop) e True) f
  by_cases hfe : f=e
  · subst f
    erw [Function.update_self]
    simp only [iff_true]
    exact Or.inr ⟨i,Finset.mem_insert_self _ _,hm⟩
  · erw [Function.update_of_ne hfe]
    constructor
    · rintro (ho|⟨j,hj,hjm⟩)
      · exact Or.inl ho
      · rcases Finset.mem_insert.mp hj with rfl|hj
        · exact (hfe (Option.some.inj (hjm.symm.trans hm))).elim
        · exact Or.inr ⟨j,hj,hjm⟩
    · rintro (ho|⟨j,hj,hjm⟩)
      · exact Or.inl ho
      · exact Or.inr ⟨j,Finset.mem_insert_of_mem hj,hjm⟩

lemma canonical_misses_targets (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n)
    (ω : Set E) (i : ℕ) (hin : i < n+2) (hc : Canonical G (anchors d x n h) ω i) :
    ¬∃ b ∈ targets d x n h i, (G.openGraph ω).Reachable (node d x n h i).1 b := by
  rintro ⟨b,⟨j,hji,hjb⟩,hr⟩
  exact hc j _ _ hji (node_getElem? d x n h j (hji.trans hin))
    (node_getElem? d x n h i hin) (hjb ▸ hr.symm)

section Contact
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma earlier_not_incident (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i j : ℕ) (hin : i < n+2) (hji : j < i) (hj : 2 ≤ j)
    (hc : Canonical G (anchors d x n h) ω i) (e : E) (hm : nodeMark n h j = some e) :
    ¬∃ v ∈ G.ends e, (G.openGraph ω).Reachable (node d x n h i).1 v := by
  obtain ⟨_,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w r₀ n h ω hr j hj
    (hji.trans hin) e hm
  rintro ⟨z,hz,hiz⟩
  rw [hev,Sym2.mem_iff] at hz
  have hp := nodeParent_lt G d x ω n h j hj
  rcases hz with rfl|rfl
  · exact hc j _ _ hji (node_getElem? d x n h j (hji.trans hin))
      (node_getElem? d x n h i hin) (hu.trans hiz.symm)
  · exact hc _ _ _ (hp.trans hji) (node_getElem? d x n h _ ((hp.trans hji).trans hin))
      (node_getElem? d x n h i hin) (hv.trans hiz.symm)

lemma switched_earlier_incidence (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hin : i < n+2) (hc : Canonical G (anchors d x n h) ω i)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 2 ≤ j ∧ j < i) :
    ∀ e, (∃ v ∈ G.ends e, (G.openGraph ω).Reachable (node d x n h i).1 v) →
      (ω e ↔ switched n h ω S e) := by
  intro e he
  constructor
  · exact Or.inl
  · rintro (ho|⟨j,hj,hjm⟩)
    · exact ho
    · exact (earlier_not_incident G order d x p w r₀ n h ω hr i j hin (hS j hj).2
        (hS j hj).1 hc e hjm he).elim

theorem switched_contact_reconstruction (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (i : ℕ) (hi : 2 ≤ i) (hin : i < n+2)
    (hc : Canonical G (anchors d x n h) ω i) (e : E) (hm : nodeMark n h i = some e)
    (S : Finset ℕ) (hS : ∀ j ∈ S, 2 ≤ j ∧ j < i) (offset : ℝ) :
    let B := targets d x n h i
    let a := (node d x n h i).1
    let F := fun σ : Set E => ∃ b ∈ B, (G.openGraph σ).Reachable a b
    let T := LazyDFS.search G order a B
    T.queryDelta F w (Function.update ω e True) e =
      T.queryDelta F w (switched n h ω (insert i S)) e ∧
    T.prefixScore p F w (Function.update ω e True) e =
      T.prefixScore p F w (switched n h ω (insert i S)) e ∧
    T.reverseGuess p F w (Function.update ω e True) offset e =
      T.reverseGuess p F w (switched n h ω (insert i S)) offset e := by
  dsimp only
  rw [switched_insert n h ω S i e hm]
  obtain ⟨hclosed,u,v,hev,hu,hv⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi hin e hm
  have hb : (node d x n h (nodeParent G d x ω n h i)).1 ∈ targets d x n h i :=
    ⟨_,nodeParent_lt G d x ω n h i hi,rfl⟩
  have hup (σ : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) σ e True =
        Function.update σ e True := by
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' σ e True) (Subsingleton.elim _ _)
  simpa only [hup] using LazyDFS.search_contact_reconstruction G order ω (switched n h ω S) _ _ u v e
    hev hclosed (canonical_misses_targets G d x n h ω i hin hc) hu
    ⟨_,hb,hv.symm⟩ ⟨_,hb,hv.symm.mono (G.openGraph_mono (switched_mono n h ω S))⟩
    (switched_earlier_incidence G order d x p w r₀ n h ω hr i hin hc S hS) p w offset

end Contact
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

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_MarkedBits
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.MarkedBits
open scoped Classical
open FiniteProduct ExactExposure

variable {E I : Type*}

variable [Fintype I]

omit [Fintype I] in
lemma opened_empty (m : I → Option E) (ω : E → Bool) : opened ∅ m ω = ω := by
  funext e
  simp [opened]

omit [Fintype I] in
lemma opened_insert (S : Finset I) (m : I → Option E) (ω : E → Bool)
    (i : I) (e : E) (hm : m i = some e) :
    opened (insert i S) m ω = Function.update (opened S m ω) e true := by
  funext f
  by_cases hf : f=e
  · subst f
    simp only [Function.update_self,opened]
    rw [ite_eq_left ⟨i,Finset.mem_insert_self _ _,hm⟩]
  · rw [Function.update_of_ne hf]
    have he : (∃ j ∈ insert i S, m j = some f) ↔ ∃ j ∈ S, m j = some f := by
      constructor
      · rintro ⟨j,hj,hjm⟩
        rcases Finset.mem_insert.mp hj with rfl|hj
        · exact (hf (Option.some.inj (hjm.symm.trans hm))).elim
        · exact ⟨j,hj,hjm⟩
      · rintro ⟨j,hj,hjm⟩
        exact ⟨j,Finset.mem_insert_of_mem hj,hjm⟩
    simp only [opened,he]

omit [Fintype I] in
lemma opened_unchanged (S : Finset I) (m : I → Option E) (ω : E → Bool)
    (e : E) (he : ∀ i ∈ S, m i ≠ some e) : opened S m ω e = ω e := by
  apply ite_eq_right
  rintro ⟨i,hi,hie⟩
  exact he i hi hie

omit [Fintype I] in

lemma close_opened_insert (S : Finset I) (m : I → Option E) (ω : E → Bool)
    (i : I) (e : E) (hm : m i = some e) (hω : ω e = false)
    (hd : ∀ j ∈ S, m j ≠ some e) :
    Function.update (opened (insert i S) m ω) e false = opened S m ω := by
  rw [opened_insert S m ω i e hm,Function.update_idem]
  rw [← hω,← opened_unchanged S m ω e hd,Function.update_eq_self]

omit [Fintype I] in
lemma density_open_likelihood [Fintype E] (p : ℝ) (ω : E → Bool) (e : E) (he : ω e = false) :
    FiniteProduct.density (QueryTree.bitWeight p) ω * p =
      FiniteProduct.density (QueryTree.bitWeight p) (Function.update ω e true) * (1-p) := by
  classical
  have hf (m : E → Bool) : FiniteProduct.density (QueryTree.bitWeight p) m =
      QueryTree.bitWeight p e (m e) * ∏ f ∈ Finset.univ.erase e, QueryTree.bitWeight p f (m f) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ e)).symm
  rw [hf ω,hf (Function.update ω e true)]
  have ht : (∏ f ∈ Finset.univ.erase e, QueryTree.bitWeight p f ((Function.update ω e true) f)) =
      ∏ f ∈ Finset.univ.erase e, QueryTree.bitWeight p f (ω f) := by
    apply Finset.prod_congr rfl
    intro f hf
    rw [Function.update_of_ne (Finset.mem_erase.mp hf).1]
  rw [ht]
  simp only [he,Function.update_self,QueryTree.bitWeight,Bool.false_eq_true,if_false,if_true]
  ring

end CriticalPercolation.MarkedBits

namespace CriticalPercolation.ReverseReference
open scoped Classical

variable {X M : Type*}

lemma recover_trajectory (u : ℕ → X → M → X) (σ : ℕ → X) (m : ℕ → M)
    (n : ℕ) (hu : ∀ i < n, u i (σ (i+1)) (m i) = σ i) :
    recover u n (σ n) (fun i => m i.val) = σ 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [recover]
    dsimp only [Fin.val_last]
    rw [hu n (Nat.lt_succ_self n)]
    exact ih (fun i hi => hu i (hi.trans (Nat.lt_succ_self n)))

lemma weight_trajectory (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (σ : ℕ → X) (m : ℕ → M) (v : ℕ → ℝ) (n : ℕ)
    (hu : ∀ i < n, u i (σ (i+1)) (m i) = σ i)
    (hk : ∀ i < n, k i (σ (i+1)) (m i) = v i) :
    weight k u n (σ n) (fun i => m i.val) = ∏ i : Fin n, v i.val := by
  induction n with
  | zero => simp [weight]
  | succ n ih =>
    rw [weight]
    dsimp only [Fin.val_last]
    rw [hk n (Nat.lt_succ_self n),hu n (Nat.lt_succ_self n)]
    change v n * weight k u n (σ n) (fun i => m i.val) = _
    rw [ih (fun i hi => hu i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hk i (hi.trans (Nat.lt_succ_self n)))]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    ring

end CriticalPercolation.ReverseReference
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReverseKernels
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.kernelsFinDec
lemma pivotGuess_subprobability (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) :
    (∀ e, 0 ≤ pivotGuess G order d x p w n D i ω e) ∧
      (∑ e, pivotGuess G order d x p w n D i ω e) ≤ 1 := by
  apply SearchTree.reverseGuess_subprobability _ ∅ (LazyDFS.compile_valid G order _ _ _ _) hp
  · rintro a b hab ⟨v,hv,hr⟩
    exact ⟨v,hv,hr.mono (G.openGraph_mono hab)⟩
  · exact homogeneous_normalized w p h0 h1
  · exact fun e b => (homogeneous_positive w hp h0 h1 e b).le
  · exact fun e _ => ⟨h0 e,h1 e⟩

lemma inverseKernel_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (j : ℕ) (ω : E → Bool) (m : Option E) : 0 ≤ inverseKernel G order d x p w n D j ω m := by
  unfold inverseKernel
  split_ifs with hj hi hm hm
  · cases m with
    | none => exact le_rfl
    | some e => exact (pivotGuess_subprobability G order d x p w n D hp h0 h1 _ ω).1 e
  · exact zero_le_one
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl

lemma contactTotal_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (i : Fin n) (ω : E → Bool) :
    0 ≤ contactTotal G order d x p w n D i ω :=
  Finset.sum_nonneg fun m _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m

lemma inactiveKernel_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (i : Fin n) (ω : E → Bool) (m : Option E) : 0 ≤ inactiveKernel G order d x p w n D i ω m := by
  unfold inactiveKernel
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m)
      (contactTotal_nonneg G order d x p w n D hp h0 h1 i ω)

lemma inverseReference_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (z) :
    0 ≤ inverseReference G order d x p w n D z :=
  ReverseReference.joint_nonneg _ (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    _ _ (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    _ (inactiveKernel_nonneg G order d x p w n D hp h0 h1) n z

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryStages
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*}

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.stagesFinDec
lemma stage_zero (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E) :
    stage n D ω m 0 = ω := by
  simp only [stage,stageIndices,Nat.not_lt_zero,Finset.filter_false,opened_empty]

lemma stageIndices_succ_active (n : ℕ) (D : FixedDescriptor n) (i : Fin n)
    (hi : i ∈ activeSteps n D) :
    stageIndices n D (i.val+1) = insert i (stageIndices n D i.val) := by
  ext j
  simp only [stageIndices,Finset.mem_filter,Finset.mem_insert]
  constructor
  · rintro ⟨hj,hji⟩
    by_cases he : j=i
    · exact Or.inl he
    · exact Or.inr ⟨hj,by have hne : j.val ≠ i.val := fun e => he (Fin.ext e); omega⟩
  · rintro (rfl|⟨hj,hji⟩)
    · exact ⟨hi,Nat.lt_succ_self _⟩
    · exact ⟨hj,Nat.lt_succ_of_lt hji⟩

lemma stageIndices_succ_inactive (n : ℕ) (D : FixedDescriptor n) (i : Fin n)
    (hi : i ∉ activeSteps n D) : stageIndices n D (i.val+1) = stageIndices n D i.val := by
  ext j
  simp only [stageIndices,Finset.mem_filter]
  constructor
  · rintro ⟨hj,hji⟩
    refine ⟨hj,?_⟩
    have he : j.val ≠ i.val := fun he => hi (Fin.ext he ▸ hj)
    omega
  · rintro ⟨hj,hji⟩
    exact ⟨hj,Nat.lt_succ_of_lt hji⟩

lemma configuration_opened (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E)
    (S : Finset (Fin n)) :
    configuration (opened S m ω) = switched n (fromWords n (fun j => (D j).1) m)
      (configuration ω) (S.image fun i => i.val+2) := by
  apply Set.ext
  intro e
  have hm (i : Fin n) : nodeMark n (fromWords n (fun j => (D j).1) m) (i.val+2) = m i := by
    rw [← marks_nodeMark,marks_fromWords]
  simp only [configuration,MarkedBits.opened,switched,Set.mem_ofPred_eq]
  simp only [Finset.mem_image,exists_exists_and_eq_and,hm]
  by_cases he : ∃ i ∈ S, m i = some e
  · simp only [he,if_true,or_true]
  · simp only [he,if_false,or_false]
    rfl

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

lemma supported_mark_closed (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) : ω e = false := by
  obtain ⟨f,hf,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hfe : f=e := Option.some.inj (hf.symm.trans he)
  subst f
  have hc := admissible_closed G _ _ _ (scheduled_parent_mem d x n D i) ω e ha
  exact Bool.eq_false_iff.mpr hc

lemma supported_marks_distinct (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i j : Fin n)
    (e : E) (hi : m i = some e) (hj : m j = some e) : i=j := by
  obtain ⟨_,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hm (j : Fin n) : nodeMark n h (j.val+2) = m j := by rw [← marks_nodeMark,marks_fromWords]
  have he := selected_marks_injective G order d x p w _ n h _ hr _ _ (by omega) (by omega)
    (by have := i.isLt; omega) (by have := j.isLt; omega) e ((hm i).trans hi) ((hm j).trans hj)
  exact Fin.ext (by omega)

lemma supported_stage_closed (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) :
    stage n D ω m i.val e = false := by
  rw [stage,opened_unchanged]
  · exact supported_mark_closed G order d x p w s n D ω m hz i hi e he
  · intro j hj hje
    have hjlt := (Finset.mem_filter.mp hj).2
    have hji := supported_marks_distinct G order d x p w s n D ω m hz j i e hje he
    subst j
    omega

lemma supported_stage_close (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) :
    Function.update (stage n D ω m (i.val+1)) e false = stage n D ω m i.val := by
  dsimp only [stage]
  rw [stageIndices_succ_active n D i hi]
  apply close_opened_insert _ m ω i e he (supported_mark_closed G order d x p w s n D ω m hz i hi e he)
  intro j hj hje
  have hjlt := (Finset.mem_filter.mp hj).2
  have hji := supported_marks_distinct G order d x p w s n D ω m hz j i e hje he
  subst j
  omega

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReversePrices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]

lemma reverseGuess_mark (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (hp : p ≠ 0) (w : E → Prop → ℝ)
    (ω : E → Bool) (e : E) (ha : Admissible G B a b ω e) :
    (LazyDFS.search G order a B).reverseGuess p
      (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
      (Function.update (configuration ω) e True) 0 e =
      ((1-p)/p) * markWeight G order B a b p w ω e /
        (1+markCost G order B a b p w ω e)^2 := by
  obtain ⟨hn,u,v,hev,hu,hv⟩ := ha
  have hc := admissible_closed G B a b hb ω e ⟨hn,u,v,hev,hu,hv⟩
  have hpi := G.contact_exit_pivot (configuration ω) B a u v e hev hc hn hu ⟨b,hb,hv.symm⟩
  have ha : Admissible G B a b ω e := ⟨hn,u,v,hev,hu,hv⟩
  simp only [reverseGuess,ite_eq_left hpi,add_zero,markWeight,markCost,ite_eq_left ha,
    queryDelta_update]
  field_simp

end CriticalPercolation.ExactExposure

namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.pricesFinDec
lemma supported_guess_price (hp : p ≠ 0) (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) (e : E) (he : m i = some e) :
    pivotGuess G order d x p w n D i (stage n D ω m (i.val+1)) e =
      ((1-p)/p) * selectedWeight G order d x p w n D i ω (m i) /
        (1+selectedCost G order d x p w n D i ω (m i))^2 := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  let h := fromWords (E := E) n (fun j => (D j).1) m
  have hin : i.val+2 ∈ activeNodes G d x n h (configuration ω) := by
    rw [activeNodes_eq_descriptor G d x n h _ D hD]
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have hc := active_canonical G order d x p w _ n h _ hr _ hin
  have hm : nodeMark n h (i.val+2) = some e := by rw [← marks_nodeMark,marks_fromWords,he]
  have ht : targets d x n h (i.val+2) = stepTargets (E := E) d x n D i := by
    change _ = scheduledTargets (E := E) d x n (fun j => (D j).1) i.val
    rw [targets_prefix d x n h _ i.isLt.le,scheduledTargets_eq d x n _ m _ i.isLt.le]
  have hl : (node d x n h (i.val+2)).1 = stepLeft (E := E) d x n D i :=
    congrArg Prod.fst (node_eq_descriptor G d x n h _ D hD _)
  have hS : ∀ j ∈ (stageIndices n D i.val).image (fun i => i.val+2), 2 ≤ j ∧ j < i.val+2 := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hj
    have hklt := (Finset.mem_filter.mp hk).2
    omega
  have hh := (switched_contact_reconstruction G order d x p w _ n h (configuration ω) hr
    (i.val+2) (by omega) (by have := i.isLt; omega) hc e hm _ hS 0).2.2
  rw [hl,ht] at hh
  unfold pivotGuess
  rw [stage,configuration_opened,stageIndices_succ_active n D i hi,Finset.image_insert]
  rw [← hh]
  obtain ⟨f,hf,ha⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hfe : f=e := Option.some.inj (hf.symm.trans he)
  subst f
  have hpr := reverseGuess_mark G order (stepTargets (E := E) d x n D i)
    (stepLeft (E := E) d x n D i) (stepRight (E := E) d x n D i)
    (scheduled_parent_mem d x n D i) p hp w ω e ha
  simpa only [selectedWeight,selectedCost,ite_eq_left (Finset.mem_filter.mp hi).2,he] using hpr

lemma supported_inverse_update (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    inverseUpdate (E := E) n D i.val (stage n D ω m (i.val+1)) (masked (activeSteps n D) m i) =
      stage n D ω m i.val := by
  unfold inverseUpdate
  rw [dite_eq_left i.isLt]
  by_cases hi : i ∈ activeSteps n D
  · obtain ⟨e,he,_⟩ := supported_active_admissible G order d x p w s n D ω m hz
      ⟨i,(Finset.mem_filter.mp hi).2⟩
    simp only [ite_eq_left hi,masked,he]
    exact supported_stage_close G order d x p w s n D ω m hz i hi e he
  · simp only [ite_eq_right hi,stage,stageIndices_succ_inactive n D i hi]

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.likelihoodFinDec
lemma inversePenalty_nonneg (i : Fin n) (ω : E → Bool) (m : Option E) :
    0 ≤ inversePenalty G order d x p w n D i ω m := by
  unfold inversePenalty
  exact mul_nonneg (by split_ifs; exact sq_nonneg _; exact zero_le_one)
    (le_trans zero_le_one (le_max_left _ _))

lemma supported_contactTotal_pos (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    0 < contactTotal G order d x p w n D i ω := by
  have hh : 0 < scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) :=
    lt_of_le_of_ne (scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _) <|
      Ne.symm (supported_schedule_ne_zero G order d x p w s n D ω m hz i)
  exact hh.trans_le (Finset.single_le_sum (fun k _ => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ k)
    (Finset.mem_univ (m i)))

lemma supported_stage_likelihood (s : ℕ) (hp : p ≠ 0) (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n)
    (hi : i ∈ activeSteps n D) :
    FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m i.val) =
      FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m (i.val+1)) * ((1-p)/p) := by
  obtain ⟨e,he,_⟩ := supported_active_admissible G order d x p w s n D ω m hz
    ⟨i,(Finset.mem_filter.mp hi).2⟩
  have hs : stage n D ω m (i.val+1) = Function.update (stage n D ω m i.val) e true := by
    unfold stage
    rw [stageIndices_succ_active n D i hi,opened_insert _ m ω i e he]
  have hh := density_open_likelihood p (stage n D ω m i.val) e
    (supported_stage_closed G order d x p w s n D ω m hz i hi e he)
  rw [← hs] at hh
  simpa only [mul_div_assoc] using (eq_div_iff hp).mpr hh

lemma supported_step_likelihood (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) (i : Fin n) :
    FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m i.val) *
        scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) ≤
      FiniteProduct.density (QueryTree.bitWeight p) (stage n D ω m (i.val+1)) *
        (inverseKernel G order d x p w n D i.val (stage n D ω m (i.val+1)) (masked (activeSteps n D) m i) *
          inactiveKernel G order d x p w n D i ω (masked (activeSteps n D)ᶜ m i) *
          inversePenalty G order d x p w n D i ω (m i)) := by
  have hμ : ∀ η : E → Bool, 0 ≤ FiniteProduct.density (QueryTree.bitWeight p) η :=
    FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩)
  have hr := scheduleWeight_nonneg G order d x p w hp h0 h1 n (fun j => (D j).1) i (configuration ω) (m i)
  have hA := supported_contactTotal_pos G order d x p w n D s hp h0 h1 ω m hz i
  by_cases hi : i ∈ activeSteps n D
  · obtain ⟨e,he,_⟩ := supported_active_admissible G order d x p w s n D ω m hz
      ⟨i,(Finset.mem_filter.mp hi).2⟩
    have hn := (selected_nonneg G order d x p w n D hp h0 h1 i ω (m i)).2
    have hc : (1+selectedCost G order d x p w n D i ω (m i))^2 ≠ 0 := by positivity
    have hg := supported_guess_price G order d x p w s n D hp.1.ne' ω m hz i hi e he
    have hb := supported_stage_likelihood G order d x p w n D s hp.1.ne' ω m hz i hi
    have hK : inverseKernel G order d x p w n D i.val (stage n D ω m (i.val+1))
        (masked (activeSteps n D) m i) =
        ((1-p)/p * selectedWeight G order d x p w n D i ω (m i) /
         (1+selectedCost G order d x p w n D i ω (m i))^2) := by
      simpa only [inverseKernel,dite_eq_left i.isLt,ite_eq_left hi,masked,he] using hg
    have hI : inactiveKernel G order d x p w n D i ω (masked (activeSteps n D)ᶜ m i) = 1 := by
      simp only [inactiveKernel,masked,Finset.mem_compl,hi,
        not_true_eq_false,if_false,if_true]
    rw [hK,hI,mul_one,supported_selected_eq G order d x p w n D s ω m hz i,
      hb,inversePenalty,ite_eq_left hi]
    have hh : ((1-p)/p * scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) /
        (1+selectedCost G order d x p w n D i ω (m i))^2) *
        ((1+selectedCost G order d x p w n D i ω (m i))^2) =
        ((1-p)/p)*scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) :=
      div_mul_cancel₀ _ hc
    have hh2 : ((1-p)/p * scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) /
        (1+selectedCost G order d x p w n D i ω (m i))^2) *
        ((1+selectedCost G order d x p w n D i ω (m i))^2 *
          max 1 (contactTotal G order d x p w n D i ω)) =
        (((1-p)/p)*scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i)) *
          max 1 (contactTotal G order d x p w n D i ω) := by
      rw [← mul_assoc,hh]
    rw [hh2]
    simpa only [mul_assoc,mul_one] using mul_le_mul_of_nonneg_left (le_max_left 1 (contactTotal G order d x p w n D i ω))
      (mul_nonneg (hμ _) (mul_nonneg (div_nonneg (sub_nonneg.mpr hp.2.le) hp.1.le) hr))
  · have hs : stage n D ω m (i.val+1) = stage n D ω m i.val := by
      unfold stage
      rw [stageIndices_succ_inactive n D i hi]
    simp only [inverseKernel,dite_eq_left i.isLt,masked,Finset.mem_compl,hi,not_false_eq_true,
      if_true,if_false,inactiveKernel,ite_eq_right hA.ne',inversePenalty,one_mul,hs]
    apply mul_le_mul_of_nonneg_left _ (hμ _)
    calc
      _ = (scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i) /
        contactTotal G order d x p w n D i ω) * contactTotal G order d x p w n D i ω :=
          (div_mul_cancel₀ _ hA.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right 1 (contactTotal G order d x p w n D i ω)) (div_nonneg hr hA.le)

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_RecursiveLikelihood
attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.ReverseReference
open scoped Classical

lemma trajectory_dominance (a r v : ℕ → ℝ) (n : ℕ)
    (hr : ∀ i < n, 0 ≤ r i) (hv : ∀ i < n, 0 ≤ v i)
    (hstep : ∀ i < n, a i * r i ≤ a (i+1) * v i) :
    a 0 * ∏ i : Fin n, r i.val ≤ a n * ∏ i : Fin n, v i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := ih (fun i hi => hr i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hv i (hi.trans (Nat.lt_succ_self n)))
      (fun i hi => hstep i (hi.trans (Nat.lt_succ_self n)))
    rw [Fin.prod_univ_castSucc,Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    calc
      _ = (a 0 * ∏ i : Fin n, r i.val) * r n := by ring
      _ ≤ (a n * ∏ i : Fin n, v i.val) * r n := mul_le_mul_of_nonneg_right hh (hr n (Nat.lt_succ_self n))
      _ = (a n*r n)*(∏ i : Fin n, v i.val) := by ring
      _ ≤ (a (n+1)*v n)*(∏ i : Fin n, v i.val) := mul_le_mul_of_nonneg_right
        (hstep n (Nat.lt_succ_self n)) (Finset.prod_nonneg fun i _ => hv i.val (i.isLt.trans (Nat.lt_succ_self n)))
      _ = _ := by ring

lemma joint_trajectory_dominance {X M : Type*} [Fintype X] [Fintype M]
    (μ : X → ℝ) (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (n : ℕ) (a : Fin n → X → M → ℝ) (σ : ℕ → X) (m : ℕ → M)
    (m' : Fin n → M) (r v : Fin n → ℝ)
    (hu : ∀ i < n, u i (σ (i+1)) (m i) = σ i)
    (hr : ∀ i, 0 ≤ r i)
    (hv : ∀ i, 0 ≤ k i.val (σ (i.val+1)) (m i.val) * a i (σ 0) (m' i) * v i)
    (hs : ∀ i : Fin n, μ (σ i.val) * r i ≤
      μ (σ (i.val+1)) * (k i.val (σ (i.val+1)) (m i.val) * a i (σ 0) (m' i) * v i)) :
    μ (σ 0) * ∏ i, r i ≤
      joint μ k u a n (σ n,(fun i => m i.val),m') * ∏ i, v i := by
  let r' : ℕ → ℝ := fun j => if hj : j<n then r ⟨j,hj⟩ else 0
  let v' : ℕ → ℝ := fun j => if hj : j<n then
    k j (σ (j+1)) (m j) * a ⟨j,hj⟩ (σ 0) (m' ⟨j,hj⟩) * v ⟨j,hj⟩ else 0
  have hh := trajectory_dominance (fun j => μ (σ j)) r' v' n
    (fun j hj => by simpa only [r',dite_eq_left hj] using hr ⟨j,hj⟩)
    (fun j hj => by simpa only [v',dite_eq_left hj] using hv ⟨j,hj⟩)
    (fun j hj => by simpa only [r',v',dite_eq_left hj] using hs ⟨j,hj⟩)
  simp only [r',v',dite_eq_left (Fin.isLt _),Finset.prod_mul_distrib] at hh
  unfold joint terminalWeight
  dsimp only
  rw [recover_trajectory u σ m n hu,
    weight_trajectory k u σ m (fun j => k j (σ (j+1)) (m j)) n hu (fun _ _ => rfl)]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CriticalPercolation.ReverseReference
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryReferenceLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits SearchTree

variable {V E : Type*} [Fintype V] [Fintype E]

variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.refLikelihoodFinDec
lemma inversePenalty_product (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E) :
    (∏ i, inversePenalty G order d x p w n D i ω (m i)) =
      Real.exp (inverseLog G order d x p w n D ω m) := by
  have hc (i : Fin n) : 0 < 1+selectedCost G order d x p w n D i ω (m i) := by
    have hn := (selected_nonneg G order d x p w n D hp h0 h1 i ω (m i)).2
    linarith
  have he (i : Fin n) : (if i ∈ activeSteps n D then
      (1+selectedCost G order d x p w n D i ω (m i))^2 else 1) =
      Real.exp (if i ∈ activeSteps n D then
        2*Real.log (1+selectedCost G order d x p w n D i ω (m i)) else 0) := by
    split_ifs
    · rw [two_mul,Real.exp_add,Real.exp_log (hc i),pow_two]
    · exact Real.exp_zero.symm
  simp only [inversePenalty,Finset.prod_mul_distrib,he,← Real.exp_sum]
  change _ * (∏ i, max 1 (∑ a, scheduleWeight G order d x p w n
    (fun j => (D j).1) i (configuration ω) a)) = _
  rw [← exp_logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1))
    (configuration ω),← Real.exp_add]
  congr 1
  simp only [inverseLog,logContactMass]
  rw [← Finset.sum_filter,← Finset.mul_sum]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

lemma supported_reference_dominance (s : ℕ) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) :
    FiniteProduct.density (QueryTree.bitWeight p) ω *
        (∏ i, scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i)) ≤
      inverseReference G order d x p w n D (recorded n D (ω,m)) *
        Real.exp (inverseLog G order d x p w n D ω m) := by
  let m' : ℕ → Option E := fun j => if hj : j<n then masked (activeSteps n D) m ⟨j,hj⟩ else none
  have hm : (fun i : Fin n => m' i.val) = masked (activeSteps n D) m := by
    funext i
    simp only [m',dite_eq_left i.isLt]
  have hu : ∀ j<n, inverseUpdate (E := E) n D j (stage n D ω m (j+1)) (m' j) = stage n D ω m j := by
    intro j hj
    simpa only [m',dite_eq_left hj] using supported_inverse_update G order d x p w s n D ω m hz ⟨j,hj⟩
  have hh := ReverseReference.joint_trajectory_dominance
    (FiniteProduct.density (QueryTree.bitWeight p) : (E → Bool) → ℝ)
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D) n
    (inactiveKernel G order d x p w n D) (stage n D ω m) m' (masked (activeSteps n D)ᶜ m)
    (fun i => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω) (m i))
    (fun i => inversePenalty G order d x p w n D i ω (m i)) hu
    (fun i => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ _)
    (fun i => mul_nonneg (mul_nonneg
      (inverseKernel_nonneg G order d x p w n D hp h0 h1 _ _ _)
      (inactiveKernel_nonneg G order d x p w n D hp h0 h1 _ _ _))
      (inversePenalty_nonneg G order d x p w n D _ _ _))
    (fun i => by
      simpa only [stage_zero,m',dite_eq_left i.isLt] using
        supported_step_likelihood G order d x p w n D s hp h0 h1 ω m hz i)
  rw [hm,stage_zero,inversePenalty_product G order d x p w n D hp h0 h1 ω m] at hh
  exact hh

lemma conditioned_reference_density_le_bs_oai (s : ℕ) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D)
    (z : (E → Bool) × (Fin n → Option E)) :
    conditionedMass G order d x p w s n D z ≤
      inverseReference G order d x p w n D (recorded n D z) *
      Real.exp (constructionCost G order d x p w c s n D + inverseLog G order d x p w n D z.1 z.2) := by
  by_cases hz : conditionedMass G order d x p w s n D z = 0
  · rw [hz]
    exact mul_nonneg (inverseReference_nonneg G order d x p w n D hp h0 h1 _) (Real.exp_pos _).le
  · have hh := mul_le_mul_of_nonneg_left
      (supported_reference_dominance G order d x p w n D s hp h0 h1 z.1 z.2 hz)
      (Real.exp_pos (constructionCost G order d x p w c s n D)).le
    calc
      _ ≤ _ := conditionedMass_density_le G order d x p w hd hp h0 h1 hc hc1 hconn s n D hδ hD z
      _ ≤ _ := by simpa only [Real.exp_add,mul_assoc,mul_left_comm,mul_comm] using hh

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BinaryLaw.conditioned_reference_density_le_bs_oai.{u_1, u_2}
