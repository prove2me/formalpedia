-- Prove2me | solution 1 for OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:07:03.372256+00:00
-- url     : https://prove2.me/submissions/789d1ff4-899b-49fd-ace0-1693fef168e8

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

lemma eraseVertices_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => G.eraseVertices ω U) (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext e
  change (ω e ∧ e ∉ G.incidentEdges U) ↔ (ω' e ∧ e ∉ G.incidentEdges U)
  by_cases he : e ∈ G.incidentEdges U
  · simp [he]
  · rw [(hω e he).to_iff]

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_FiberValue
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
open scoped Classical

variable {X Y : Type*}

lemma fiberValue_apply (f : X → Y) (g : X → ℝ)
    (hg : ∀ x x', f x = f x' → g x = g x') (x : X) : fiberValue f g (f x) = g x := by
  unfold fiberValue
  rw [dite_eq_left ⟨x,rfl⟩]
  exact hg _ x (Exists.choose_spec (show ∃ y, f y = f x from ⟨x,rfl⟩))

lemma fiberValue_nonneg (f : X → Y) (g : X → ℝ)
    (hg : ∀ x, 0 ≤ g x) (y : Y) : 0 ≤ fiberValue f g y := by
  unfold fiberValue
  split_ifs
  · exact hg _
  · exact le_rfl

end CriticalPercolation.FiniteEntropy

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

omit [DecidableEq E] in
lemma push_length (G : BondGraph V E) (order : List (Dart V E)) (v : V) :
    (push G order v).length ≤ order.length := List.length_filter_le _ _

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

variable [Fintype V]

omit [DecidableEq V] [DecidableEq E] in
lemma rank_pop (order : List (Dart V E)) (st : State V E) (d : Dart V E) (rest : List (Dart V E)) :
    rank order st rest < rank order st (d::rest) := by simp [rank]

omit [DecidableEq V] in
lemma rank_closed (order : List (Dart V E)) (st : State V E) (d : Dart V E) (rest : List (Dart V E)) :
    rank order (st.closed d.2.1) rest < rank order st (d::rest) := by simp [rank,State.closed]

lemma rank_opened (G : BondGraph V E) (order : List (Dart V E)) (st : State V E)
    (d : Dart V E) (rest : List (Dart V E)) (h : d.2.2 ∉ st.reached) :
    rank order (st.opened d.2.1 d.2.2) (push G order d.2.2 ++ rest) <
      rank order st (d::rest) := by
  have hc : st.reached.card < Fintype.card V := by
    have hh := Finset.card_le_univ (s := insert d.2.2 st.reached)
    rw [Finset.card_insert_of_notMem h] at hh
    omega
  have hp := push_length G order d.2.2
  simp only [rank,State.opened,Finset.card_insert_of_notMem h,List.length_append,List.length_cons]
  have he : Fintype.card V - (st.reached.card+1) + 1 = Fintype.card V-st.reached.card := by omega
  have hm := congrArg (fun n => n*(order.length+1)) he
  simp only [Nat.add_mul,Nat.one_mul] at hm
  omega

omit [Fintype V] in

lemma compile_mono (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) (ω : E → Bool) :
    st.reached ⊆ ((compile G order B fuel st stack).run ω).reached ∧
    st.read ⊆ ((compile G order B fuel st stack).run ω).read := by
  induction fuel generalizing st stack with
  | zero => exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩
    · cases stack with
      | nil => exact ⟨Finset.Subset.refl _,Finset.Subset.refl _⟩
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih _ _
        · rw [SearchTree.run]
          split_ifs with he
          · exact ⟨(Finset.subset_insert _ _).trans (ih (st.opened d.2.1 d.2.2) _).1,
              (Finset.subset_insert d.2.1 _).trans (ih (st.opened d.2.1 d.2.2) _).2⟩
          · exact ⟨(ih (st.closed d.2.1) rest).1,
              (Finset.subset_insert d.2.1 _).trans (ih (st.closed d.2.1) rest).2⟩

end LazyDFS
end CriticalPercolation

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Exhaustive
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

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
lemma openEdge_reachable (G : BondGraph V E) (ω : E → Bool)
    {v e t} (he : ω e = true) (heq : G.ends e = s(v,t)) :
    (G.openGraph {e | ω e = true}).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩)

omit [DecidableEq V] [DecidableEq E] in
lemma frontier_pop (G : BondGraph V E) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : Frontier G st ((v,e,t)::rest))
    (hskip : t ∈ st.reached ∨ e ∈ st.read ∨ v ∉ st.reached ∨ G.ends e ≠ s(v,t)) :
    Frontier G st rest := by
  intro u hu f y hfy hy
  rcases h u hu f y hfy hy with hf | hf
  · exact Or.inl hf
  · rcases List.mem_cons.mp hf with hd | hd
    · simp only [Prod.mk.injEq] at hd
      rcases hd with ⟨rfl,rfl,rfl⟩
      rcases hskip with ht | he | hv | heq
      · exact (hy ht).elim
      · exact Or.inl he
      · exact (hv hu).elim
      · exact (heq hfy).elim
    · exact Or.inr hd

omit [DecidableEq V] in
lemma frontier_closed (G : BondGraph V E) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : Frontier G st ((v,e,t)::rest)) : Frontier G (st.closed e) rest := by
  intro u hu f y hfy hy
  rcases h u hu f y hfy hy with hf | hf
  · exact Or.inl (Finset.mem_insert_of_mem hf)
  · rcases List.mem_cons.mp hf with hd | hd
    · simp only [Prod.mk.injEq] at hd
      rcases hd with ⟨rfl,rfl,rfl⟩
      exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr hd

lemma frontier_opened (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : Frontier G st ((v,e,t)::rest)) :
    Frontier G (st.opened e t) (push G order t ++ rest) := by
  intro u hu f y hfy hy
  rcases Finset.mem_insert.mp hu with rfl | hu
  · apply Or.inr
    apply List.mem_append_left
    apply List.mem_filter.mpr
    exact ⟨ho u f y hfy,by simpa only [decide_eq_true_eq, true_and] using hfy⟩
  · have hy' : y ∉ st.reached := fun hy' => hy (Finset.mem_insert_of_mem hy')
    rcases h u hu f y hfy hy' with hf | hf
    · exact Or.inl (Finset.mem_insert_of_mem hf)
    · rcases List.mem_cons.mp hf with hd | hd
      · simp only [Prod.mk.injEq] at hd
        rcases hd with ⟨rfl,rfl,rfl⟩
        exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (List.mem_append_right _ hd)

omit [DecidableEq V] in
lemma readConsistent_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool)
    (h : ReadConsistent G st ω) {e : E} (he : ω e = false) :
    ReadConsistent G (st.closed e) ω := by
  intro f hf hfopen v hv
  rcases Finset.mem_insert.mp hf with rfl | hf
  · simp [he] at hfopen
  · exact h f hf hfopen v hv

lemma readConsistent_opened (G : BondGraph V E) (st : State V E) (ω : E → Bool)
    (h : ReadConsistent G st ω) {v e t} (hv : v ∈ st.reached) (heq : G.ends e = s(v,t)) :
    ReadConsistent G (st.opened e t) ω := by
  intro f hf hfopen u hu
  rcases Finset.mem_insert.mp hf with rfl | hf
  · have hu' : u = v ∨ u = t := by simpa only [heq,Sym2.mem_iff] using hu
    rcases hu' with rfl | rfl
    · exact Finset.mem_insert_of_mem hv
    · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (h f hf hfopen u hu)

omit [DecidableEq V] [DecidableEq E] in
lemma empty_frontier_closed (G : BondGraph V E) (st : State V E) (ω : E → Bool)
    (hf : Frontier G st []) (hc : ReadConsistent G st ω) :
    ∀ v ∈ st.reached, ∀ t, (G.openGraph {e | ω e = true}).Adj v t → t ∈ st.reached := by
  intro v hv t ht
  obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp ht
  by_contra htr
  rcases hf v hv e t heq htr with hr | hr
  · exact htr (hc e hr he t (by simp [heq]))
  · simp at hr

variable [Fintype V]

theorem compile_success_or_closed (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (B : Set V) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (ω : E → Bool)
    (hf : Frontier G st stack) (hc : ReadConsistent G st ω) (hr : rank order st stack ≤ fuel) :
    let final := (compile G order B fuel st stack).run ω
    (∃ v ∈ final.reached, v ∈ B) ∨
      (∀ v ∈ final.reached, ∀ t, (G.openGraph {e | ω e = true}).Adj v t → t ∈ final.reached) := by
  induction fuel generalizing st stack with
  | zero =>
    have hs : stack = [] := by
      have hh : stack.length = 0 := by dsimp [rank] at hr; omega
      exact List.length_eq_zero_iff.mp hh
    subst stack
    exact Or.inr (empty_frontier_closed G st ω hf hc)
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact Or.inl hh
    · cases stack with
      | nil => exact Or.inr (empty_frontier_closed G st ω hf hc)
      | cons d rest =>
        rcases d with ⟨v,e,t⟩
        dsimp only
        split_ifs with hd
        · exact ih st rest (frontier_pop G st v e t rest hf hd) hc
            (by have hh := rank_pop order st (v,e,t) rest; omega)
        · have hdec : t ∉ st.reached ∧ e ∉ st.read ∧ v ∈ st.reached ∧ G.ends e = s(v,t) := by
            push Not at hd
            exact hd
          rw [SearchTree.run]
          split_ifs with he
          · exact ih _ _ (frontier_opened G order ho st v e t rest hf)
              (readConsistent_opened G st ω hc hdec.2.2.1 hdec.2.2.2)
              (by have hh := rank_opened G order st (v,e,t) rest hdec.1; dsimp only at hh; omega)
          · have he' : ω e = false := Bool.eq_false_iff.mpr he
            exact ih _ _ (frontier_closed G st v e t rest hf)
              (readConsistent_closed G st ω hc he')
              (by have hh := rank_closed order st (v,e,t) rest; dsimp only at hh; omega)

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_Initial
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

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

lemma compile_sound (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E)) (ω : E → Bool) (w : V)
    (hs : ∀ v ∈ st.reached, (G.openGraph {e | ω e = true}).Reachable w v) :
    ∀ v ∈ ((compile G order B fuel st stack).run ω).reached,
      (G.openGraph {e | ω e = true}).Reachable w v := by
  induction fuel generalizing st stack with
  | zero => exact hs
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact hs
    · cases stack with
      | nil => exact hs
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest hs
        · rw [SearchTree.run]
          split_ifs with he
          · apply ih
            intro u hu
            rcases Finset.mem_insert.mp hu with rfl | hu
            · have hdec : d.2.2 ∉ st.reached ∧ d.2.1 ∉ st.read ∧ d.1 ∈ st.reached ∧
                  G.ends d.2.1 = s(d.1,d.2.2) := by
                push Not at hd
                exact hd
              exact (hs d.1 hdec.2.2.1).trans (openEdge_reachable G ω he hdec.2.2.2)
            · exact hs u hu
          · exact ih (st.closed d.2.1) rest hs

omit [DecidableEq V] [DecidableEq E] in
lemma reachable_mem_of_closed (H : SimpleGraph V) (S : Finset V)
    (hc : ∀ v ∈ S, ∀ t, H.Adj v t → t ∈ S) {v t : V}
    (hr : H.Reachable v t) (hv : v ∈ S) : t ∈ S := by
  have hh : ∀ {u z : V}, H.Walk u z → u ∈ S → z ∈ S := by
    intro u z path
    induction path with
    | nil => exact id
    | cons ha _ ih => exact fun hu => ih (hc _ hu _ ha)
  exact hr.elim (fun path => hh path hv)

omit [DecidableEq E] in
lemma initial_frontier (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (w : V) : Frontier G (initial w) (push G order w) := by
  intro v hv e t he _
  have hvw : v = w := Finset.mem_singleton.mp hv
  subst v
  exact Or.inr (List.mem_filter.mpr ⟨ho w e t he,by simpa only [decide_eq_true_eq,true_and] using he⟩)

omit [DecidableEq V] [DecidableEq E] in
lemma initial_consistent (G : BondGraph V E) (w : V) (ω : E → Bool) :
    ReadConsistent G (initial w) ω := by
  intro e he
  exact (Finset.notMem_empty e he).elim

variable [Fintype V]

theorem search_decides (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (w : V) (B : Set V) (ω : E → Bool) :
    (∃ v ∈ ((search G order w B).run ω).reached, v ∈ B) ↔
      ∃ v ∈ B, (G.openGraph {e | ω e = true}).Reachable w v := by
  have hs : ∀ v ∈ (initial (E := E) w).reached,
      (G.openGraph {e | ω e = true}).Reachable w v := by
    intro v hv
    have : v = w := Finset.mem_singleton.mp hv
    subst v
    exact .refl _
  constructor
  · rintro ⟨v,hv,hB⟩
    exact ⟨v,hB,compile_sound G order B _ _ _ ω w hs v hv⟩
  · rintro ⟨v,hB,hr⟩
    rcases compile_success_or_closed G order ho B _ (initial w) (push G order w) ω
      (initial_frontier G order ho w) (initial_consistent G w ω) le_rfl with h | h
    · exact h
    · have hw : w ∈ ((search G order w B).run ω).reached :=
        (compile_mono G order B _ (initial w) (push G order w) ω).1 (Finset.mem_singleton_self _)
      exact ⟨v,reachable_mem_of_closed _ _ h hr hw,hB⟩

end CriticalPercolation.LazyDFS

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_CoordinateNeDensity
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

lemma coordinate_ne_zero_of_density (w : E → Prop → ℝ) (ω : Set E)
    (h : density w ω ≠ 0) (e : E) : w e (ω e) ≠ 0 := by
  exact (Finset.prod_ne_zero_iff.mp h) e (Finset.mem_univ e)

lemma density_pin_of_support (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop)
    (h : density w ω ≠ 0) (hb : ω e = b) : density (pin w e b) ω ≠ 0 := by
  erw [density_pin, ite_eq_left hb, one_mul]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact coordinate_ne_zero_of_density w ω h j

end CriticalPercolation.FiniteProduct

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

omit [Fintype E] in
lemma closedFresh_pin (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E)
    (hf : ClosedFresh r p C used) (e : E) (b : Prop) :
    ClosedFresh (pin r e b) p C (insert e used) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ used := by simpa only [Finset.mem_insert,not_or] using hj
  unfold pin
  simp only [Function.update,dite_eq_right hj'.1]
  exact hf j hj'.2

omit [DecidableEq E] in
lemma contact_mean_step (e : E) (l r : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1) :
    expect v ((.ask e l r : SearchTree E R).contactScore p C F w) =
      (if e ∈ C then p*delta w F e else 0) +
      v e True*expect (pin v e True) (r.contactScore p C F (pin w e True)) +
      v e False*expect (pin v e False) (l.contactScore p C F (pin w e False)) := by
  change expect v (fun ω => (if e ∈ C then p*delta w F e else 0) +
    if ω e then r.contactScore p C F (pin w e True) ω
    else l.contactScore p C F (pin w e False) ω) = _
  rw [expect_add,expect_const v hv]
  erw [expect_prop_ite]
  ring

omit [DecidableEq E] in
lemma terminal_mean_step (e : E) (l r : SearchTree E R) (F : Set E → Prop)
    (w v : E → Prop → ℝ) :
    expect v ((.ask e l r : SearchTree E R).terminalProbability F w) =
      v e True*expect (pin v e True) (r.terminalProbability F (pin w e True)) +
      v e False*expect (pin v e False) (l.terminalProbability F (pin w e False)) := by
  exact expect_prop_ite v e _ _

theorem contact_mean_terminal (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (T.contactScore p C F w) + expect v (T.terminalProbability F w) = prob w F := by
  induction T generalizing used w v with
  | done r =>
    change expect v (fun _ => 0) + expect v (fun _ => prob w F) = prob w F
    rw [expect_zero,expect_const v hv,zero_add]
  | ask e l r hl hr =>
    have he : w e False = 1-p ∧ w e True = p := hf e hT.1
    have hv' := hc e hT.1
    have hl' := hl (insert e used) hT.2.1 (pin w e False) (pin v e False)
      (pin_normalized w hw e False) (pin_normalized v hv e False)
      (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)
    have hr' := hr (insert e used) hT.2.2 (pin w e True) (pin v e True)
      (pin_normalized w hw e True) (pin_normalized v hv e True)
      (fresh_pin w p used hf e True) (closedFresh_pin v p C used hc e True)
    have hs : prob w F = w e False*prob (pin w e False) F +
        w e True*prob (pin w e True) F := expect_split_pin w e _
    rw [contact_mean_step e l r p C F w v hv,terminal_mean_step,hv'.1,hv'.2]
    rw [he.1,he.2] at hs
    by_cases heC : e ∈ C <;> simp only [heC,↓reduceIte,zero_mul,one_mul,add_zero,zero_add]
    · unfold delta
      linear_combination hl' - hs
    · linear_combination (1-p)*hl' + p*hr' - hs

omit [DecidableEq E] in
lemma terminalProbability_nonneg (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (hn : ∀ e b, 0 ≤ w e b) (ω : E → Prop) :
    0 ≤ T.terminalProbability F w ω := by
  induction T generalizing w with
  | done r => exact prob_nonneg w hn F
  | ask e l r hl hr =>
    unfold terminalProbability
    split_ifs
    · exact hr (pin w e True) (pin_nonneg w hn e True)
    · exact hl (pin w e False) (pin_nonneg w hn e False)

theorem contact_mean_le_prob (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hnw : ∀ e b, 0 ≤ w e b) (hnv : ∀ e b, 0 ≤ v e b)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (T.contactScore p C F w) ≤ prob w F := by
  have ht := contact_mean_terminal T used hT p C F w v hw hv hf hc
  have hn := expect_nonneg hnv (terminalProbability_nonneg T F w hnw)
  linarith

omit [DecidableEq E] in
lemma expect_square_add_const (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,expect_const_mul]

theorem contact_second_le_three_mean (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (C : Set E) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hnw : ∀ e b, 0 ≤ w e b) (hnv : ∀ e b, 0 ≤ v e b)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (fun ω => (T.contactScore p C F w ω)^2) ≤
      3*expect v (T.contactScore p C F w) := by
  induction T generalizing used w v with
  | done r =>
    change expect v (fun _ => (0:ℝ)^2) ≤ 3*expect v (fun _ => 0)
    rw [expect_const v hv,expect_zero]
    norm_num
  | ask e l r hl hr =>
    have he := hf e hT.1
    have hv' := hc e hT.1
    have hl' := hl (insert e used) hT.2.1 (pin w e False) (pin v e False)
      (pin_normalized w hw e False) (pin_normalized v hv e False)
      (pin_nonneg w hnw e False) (pin_nonneg v hnv e False)
      (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)
    have hr' := hr (insert e used) hT.2.2 (pin w e True) (pin v e True)
      (pin_normalized w hw e True) (pin_normalized v hv e True)
      (pin_nonneg w hnw e True) (pin_nonneg v hnv e True)
      (fresh_pin w p used hf e True) (closedFresh_pin v p C used hc e True)
    let a := if e ∈ C then p*delta w F e else 0
    have hsq : (fun ω => ((.ask e l r : SearchTree E R).contactScore p C F w ω)^2) =
        (fun ω => if ω e then (a+r.contactScore p C F (pin w e True) ω)^2
          else (a+l.contactScore p C F (pin w e False) ω)^2) := by
      funext ω
      change ((if e ∈ C then p*delta w F e else 0) +
        if ω e then r.contactScore p C F (pin w e True) ω
        else l.contactScore p C F (pin w e False) ω)^2 = _
      by_cases hω : ω e <;> simp only [hω,↓reduceIte,a]
    rw [hsq]
    erw [expect_prop_ite]
    rw [contact_mean_step e l r p C F w v hv,hv'.1,hv'.2]
    by_cases heC : e ∈ C
    · simp only [heC,↓reduceIte,zero_mul,one_mul,add_zero,zero_add]
      have haeq : a = p*delta w F e := ite_eq_left heC
      rw [← haeq]
      change expect (pin v e False) (fun ω => (a+l.contactScore p C F (pin w e False) ω)^2) ≤
        3*(a+expect (pin v e False) (l.contactScore p C F (pin w e False)))
      rw [expect_square_add_const _ (pin_normalized v hv e False)]
      have hmean := (contact_mean_le_prob l (insert e used) hT.2.1 p C F
        (pin w e False) (pin v e False) (pin_normalized w hw e False)
        (pin_normalized v hv e False) (pin_nonneg w hnw e False) (pin_nonneg v hnv e False)
        (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)).trans
          (prob_le_one _ (pin_normalized w hw e False) (pin_nonneg w hnw e False) F)
      have hd := delta_unit w hw hnw e (by rw [he.1]; exact (sub_pos.mpr hp.2).ne')
        (by rw [he.2]; exact hp.1.ne') F hF
      have ha : 0 ≤ a ∧ a ≤ 1 := by
        simp only [a,heC,↓reduceIte]
        exact ⟨mul_nonneg hp.1.le hd.1,
          (mul_le_mul_of_nonneg_left hd.2 hp.1.le).trans (by linarith [hp.2])⟩
      have hpair := mul_le_mul_of_nonneg_left hmean ha.1
      nlinarith
    · have ha : a = 0 := ite_eq_right heC
      simp only [heC,↓reduceIte,ha,zero_add]
      have hlb := mul_le_mul_of_nonneg_left hl' (sub_pos.mpr hp.2).le
      have hrb := mul_le_mul_of_nonneg_left hr' hp.1.le
      linarith

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_CutEdges
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

lemma eraseVertices_agree_of_cutClosed (G : BondGraph V E) (O : Set V) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) {v z : V} {e : E}
    (hv : v ∉ O) (he : G.ends e = s(v,z)) :
    ω e = G.eraseVertices ω O e := by
  apply propext
  constructor
  · intro hω
    refine ⟨hω,?_⟩
    rintro ⟨u,hu,hue⟩
    have : u = v ∨ u = z := by simpa only [he,Sym2.mem_iff] using hue
    rcases this with rfl | rfl
    · exact hv hu
    · exact hc e ⟨v,_,he,hv,hu⟩ hω
  · exact fun h => h.1

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ExposureLaw
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

lemma expect_eq_on (w v : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (hv : ∀ e, ∑ a, v e a = 1) (S : Set E) (f : (E → A) → ℝ)
    (hf : DependsOn f S) (heq : ∀ e ∈ S, w e = v e) :
    expect w f = expect v f := by
  obtain ⟨f',rfl⟩ := dependsOn_iff_exists_comp.mp hf
  have restrict (u : E → A → ℝ) (hu : ∀ e, ∑ a, u e a = 1) :
      expect u (fun ω => f' (fun e => ω e)) = expect (fun e : S => u e) f' := by
    have h := expect_factor u (fun e => e ∈ S) f' (fun _ => 1)
    have hc : expect (fun e : {e // e ∉ S} => u e) (fun _ => 1) = 1 :=
      expect_const (fun e : {e // e ∉ S} => u e) (fun e => hu e) 1
    simpa only [mul_one,hc] using h
  change expect w (fun ω => f' (fun e => ω e)) = expect v (fun ω => f' (fun e => ω e))
  rw [restrict w hw,restrict v hv]
  congr 1
  funext e
  exact heq e e.property

omit [Fintype E] in
lemma exposureLaw_normalized (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (hw : ∀ e, ∑ b, w e b = 1) : ∀ e, ∑ b, exposureLaw w D σ e b = 1 := by
  intro e
  by_cases he : e ∈ D
  · simp [exposureLaw,he]
  · simpa only [exposureLaw,ite_eq_right he] using hw e

omit [Fintype E] [Fintype A] in
lemma exposureLaw_nonneg (w : E → A → ℝ) (D : Set E) (σ : E → A)
    (hn : ∀ e b, 0 ≤ w e b) : ∀ e b, 0 ≤ exposureLaw w D σ e b := by
  intro e b
  unfold exposureLaw
  split_ifs <;> first | positivity | exact hn e b

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_CompileContactScoreErase
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

theorem compile_contactScore_erase (G : BondGraph V E) (order : List (Dart V E))
    (B O : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) (hs : ∀ v ∈ st.reached, v ∉ O) :
    (compile G order B fuel st stack).contactScore p (G.cutEdges O) F w ω =
      (compile G order B fuel st stack).contactScore p (G.cutEdges O) F w (G.eraseVertices ω O) := by
  induction fuel generalizing st stack w with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest w hs
        · have htail : d.1 ∈ st.reached := by
            by_contra h; exact hd (Or.inr (Or.inr (Or.inl h)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra h; exact hd (Or.inr (Or.inr (Or.inr h)))
          have hbit := G.eraseVertices_agree_of_cutClosed O ω hc (hs d.1 htail) he
          simp only [contactScore,hbit]
          congr 1
          by_cases hb : ω d.2.1
          · have hb' : G.eraseVertices ω O d.2.1 := by rwa [← hbit]
            simp only [hb',↓reduceIte]
            apply ih
            intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hv
            · exact fun hz => hc d.2.1 ⟨d.1,d.2.2,he,hs d.1 htail,hz⟩ hb
            · exact hs v hv
          · have hb' : ¬G.eraseVertices ω O d.2.1 := by rwa [← hbit]
            simp only [hb',↓reduceIte]
            exact ih _ _ _ hs

variable [Fintype V]
lemma search_contactScore_erase (G : BondGraph V E) (order : List (Dart V E))
    (B O : Set V) (a : V) (ha : a ∉ O) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (hc : ∀ e ∈ G.cutEdges O, ¬ω e) :
    (search G order a B).contactScore p (G.cutEdges O) F w ω =
      (search G order a B).contactScore p (G.cutEdges O) F w (G.eraseVertices ω O) := by
  apply compile_contactScore_erase G order B O _ _ _ p F w ω hc
  intro v hv
  have : v = a := Finset.mem_singleton.mp hv
  rwa [this]

theorem contact_expect_exterior (G : BondGraph V E) (order : List (Dart V E))
    (B O : Set V) (a : V) (ha : a ∉ O) (p : ℝ) (F : Set E → Prop)
    (w v v' : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (hv' : ∀ e, ∑ b, v' e b = 1)
    (hcut : ∀ ω, density v ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e)
    (hcut' : ∀ ω, density v' ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e)
    (heq : ∀ e ∉ G.incidentEdges O, v e = v' e) (ψ : ℝ → ℝ) :
    expect v (fun ω => ψ ((search G order a B).contactScore p (G.cutEdges O) F w ω)) =
      expect v' (fun ω => ψ ((search G order a B).contactScore p (G.cutEdges O) F w ω)) := by
  let A := (search G order a B).contactScore p (G.cutEdges O) F w
  let f := fun ω : E → Prop => ψ (A (G.eraseVertices ω O))
  have hdep : DependsOn f (G.incidentEdges O)ᶜ := by
    intro ω η hω
    have hh := G.eraseVertices_dependsOn O hω
    exact congrArg (fun x => ψ (A x)) hh
  have hvf : expect v (fun ω => ψ (A ω)) = expect v f := by
    apply expect_congr_support
    intro ω hω
    exact congrArg ψ (search_contactScore_erase G order B O a ha p F w ω (hcut ω hω))
  have hvf' : expect v' (fun ω => ψ (A ω)) = expect v' f := by
    apply expect_congr_support
    intro ω hω
    exact congrArg ψ (search_contactScore_erase G order B O a ha p F w ω (hcut' ω hω))
  exact hvf.trans ((expect_eq_on v v' hv hv' _ f hdep heq).trans hvf'.symm)

end CriticalPercolation.LazyDFS

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

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E]

theorem terminalProbability_eq_indicator (T : SearchTree E R) (F : Set E → Prop)
    (H : R → Prop) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hT : ∀ ω, density w ω ≠ 0 → (F ω ↔ H (T.run (fun e => decide (ω e)))))
    (ω : E → Prop) (hω : density w ω ≠ 0) :
    T.terminalProbability F w ω = if F ω then 1 else 0 := by
  induction T generalizing w with
  | done r =>
    change prob w F = _
    calc
      prob w F = prob w (fun _ => H r) := prob_congr_support w F _ hT
      _ = if H r then 1 else 0 := expect_const w hw _
      _ = if F ω then 1 else 0 := by rw [hT ω hω]; rfl
  | ask e l r hl hr =>
    have he := coordinate_ne_zero_of_density w ω hω e
    by_cases hb : ω e
    · have hb' : ω e = True := propext (iff_true_intro hb)
      have he' : w e True ≠ 0 := by simpa only [hb'] using he
      have hTr : ∀ η, density (pin w e True) η ≠ 0 →
          (F η ↔ H (r.run (fun j => decide (η j)))) := by
        intro η hη
        have hbit := density_pin_support w e True η hη
        have hh := hT η (density_pin_old_support w e True η he' hη)
        simpa only [run,hbit,decide_true,Bool.true_eq,if_true] using hh
      change (if ω e then r.terminalProbability F (pin w e True) ω
        else l.terminalProbability F (pin w e False) ω) = _
      rw [ite_eq_left hb]
      exact hr (pin w e True) (pin_normalized w hw e True) hTr
        (density_pin_of_support w ω e True hω hb')
    · have hb' : ω e = False := propext (iff_false_intro hb)
      have he' : w e False ≠ 0 := by simpa only [hb'] using he
      have hTl : ∀ η, density (pin w e False) η ≠ 0 →
          (F η ↔ H (l.run (fun j => decide (η j)))) := by
        intro η hη
        have hbit := density_pin_support w e False η hη
        have hh := hT η (density_pin_old_support w e False η he' hη)
        simpa only [run,hbit,decide_false,Bool.false_eq_true,if_false] using hh
      change (if ω e then r.terminalProbability F (pin w e True) ω
        else l.terminalProbability F (pin w e False) ω) = _
      rw [ite_eq_right hb]
      exact hl (pin w e False) (pin_normalized w hw e False) hTl
        (density_pin_of_support w ω e False hω hb')

variable [DecidableEq E]

theorem contact_normalization (T : SearchTree E R) (used : Finset E) (hvalid : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (H : R → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used)
    (hT : ∀ ω, density w ω ≠ 0 → (F ω ↔ H (T.run (fun e => decide (ω e)))))
    (hac : ∀ ω, density v ω ≠ 0 → density w ω ≠ 0)
    (hfail : ∀ ω, density v ω ≠ 0 → ¬F ω) :
    expect v (T.contactScore p C F w) = prob w F := by
  have ht : expect v (T.terminalProbability F w) = 0 := by
    calc
      expect v (T.terminalProbability F w) = expect v (fun _ => 0) := by
        apply expect_congr_support
        intro ω hω
        rw [terminalProbability_eq_indicator T F H w hw hT ω (hac ω hω),ite_eq_right (hfail ω hω)]
      _ = 0 := expect_zero v
  have hm := contact_mean_terminal T used hvalid p C F w v hw hv hf hc
  rw [ht,add_zero] at hm
  exact hm

end CriticalPercolation.SearchTree

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*}

variable [Fintype E]
omit [Fintype E] in
lemma forceClosed_normalized (w : E → Prop → ℝ) (C : Set E)
    (hw : ∀ e, ∑ b, w e b = 1) : ∀ e, ∑ b, forceClosed w C e b = 1 := by
  intro e
  by_cases he : e ∈ C
  · simp [forceClosed,he,Fintype.univ_Prop]
  · simpa only [forceClosed,ite_eq_right he] using hw e

omit [Fintype E] in
lemma forceClosed_nonneg (w : E → Prop → ℝ) (C : Set E)
    (hn : ∀ e b, 0 ≤ w e b) : ∀ e b, 0 ≤ forceClosed w C e b := by
  intro e b
  unfold forceClosed
  split_ifs <;> first | positivity | exact hn e b

lemma forceClosed_support (w : E → Prop → ℝ) (C : Set E) (ω : E → Prop)
    (hω : density (forceClosed w C) ω ≠ 0) : ∀ e ∈ C, ¬ω e := by
  intro e he hopen
  have h := coordinate_ne_zero_of_density (forceClosed w C) ω hω e
  simp only [forceClosed,ite_eq_left he,ite_eq_left hopen,ne_eq,not_true_eq_false] at h

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

lemma homogeneous_support (w : E → Prop → ℝ) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Prop) :
    density w ω ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  exact (homogeneous_positive w hp h0 h1 e (ω e)).ne'

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchContactMoments
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

theorem search_contact_moments (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (O B : Set V) (hB : B ⊆ O) (a : V) (ha : a ∉ O)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    let C := G.cutEdges O
    let A := (search G order a B).contactScore p C F w
    expect (forceClosed w C) A = prob w F ∧
      expect (forceClosed w C) (fun ω => (A ω)^2) ≤ 3 := by
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  let C := G.cutEdges O
  let v := forceClosed w C
  let T := search G order a B
  let H := fun st : State V E => ∃ b ∈ st.reached, b ∈ B
  have hw := homogeneous_normalized w p h0 h1
  have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  have hv := forceClosed_normalized w C hw
  have hnv := forceClosed_nonneg w C hn
  have hvalid : T.Valid ∅ := compile_valid G order B _ _ _
  have hf : Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  have hc : ClosedFresh v p C ∅ := by
    intro e _
    by_cases heC : e ∈ C <;> simp [v,forceClosed,heC,h0,h1]
  have hT : ∀ ω, density w ω ≠ 0 → (F ω ↔ H (T.run (fun e => decide (ω e)))) := by
    intro ω _
    have hs := search_decides G order ho a B (fun e => decide (ω e))
    have heq : {e | decide (ω e) = true} = ω := by
      ext e
      change decide (ω e) = true ↔ ω e
      simp
    simpa only [heq] using hs.symm
  have hac : ∀ ω, density v ω ≠ 0 → density w ω ≠ 0 :=
    fun ω _ => homogeneous_support w hp h0 h1 ω
  have hfail : ∀ ω, density v ω ≠ 0 → ¬F ω := by
    intro ω hω ⟨b,hb,hab⟩
    exact G.not_reachable_of_cut_closed O ω (forceClosed_support w C ω hω) ha (hB hb) hab
  have hnorm := contact_normalization T ∅ hvalid p C F H w v hw hv hf hc hT hac hfail
  have hmono : ∀ s t : Set E, s ⊆ t → F s → F t := by
    rintro s t hst ⟨b,hb,hab⟩
    exact ⟨b,hb,hab.mono (G.openGraph_mono hst)⟩
  have hsecond := contact_second_le_three_mean T ∅ hvalid hp C F hmono w v hw hv hn hnv hf hc
  rw [hnorm] at hsecond
  exact ⟨hnorm,hsecond.trans (by linarith [prob_le_one w hw hn F])⟩

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_ProductMeasure_ExposureLawSupport
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

variable {E A : Type*} [Fintype E]

lemma exposureLaw_support (w : E → A → ℝ) (D : Set E) (σ ω : E → A)
    (hω : density (exposureLaw w D σ) ω ≠ 0) : ∀ e ∈ D, ω e = σ e := by
  intro e he
  by_contra hb
  apply hω
  unfold density
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [exposureLaw,he,hb])

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_QueryDelta
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

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]

theorem search_contact_moments_exposure (G : BondGraph V E)
    (order : List (Dart V E)) (ho : ∀ v e z, G.ends e = s(v,z) → (v,e,z) ∈ order)
    (B O : Set V) (a : V) (ha : a ∉ O) (hB : B ⊆ O) (σ : Set E)
    (hσ : ∀ e ∈ G.cutEdges O, ¬σ e) (p : ℝ) (hp : 0 < p ∧ p < 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    let T := search G order a B
    let v := exposureLaw w (G.incidentEdges O) σ
    expect v (T.contactScore p (G.cutEdges O) F w) = prob w F ∧
    expect v (fun ω => (T.contactScore p (G.cutEdges O) F w ω)^2) ≤ 3 := by
  dsimp only
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  let v := exposureLaw w (G.incidentEdges O) σ
  let v' := forceClosed w (G.cutEdges O)
  have hw := homogeneous_normalized w p h0 h1
  have hv : ∀ e, ∑ b, v e b = 1 := exposureLaw_normalized w _ σ hw
  have hv' : ∀ e, ∑ b, v' e b = 1 := forceClosed_normalized w _ hw
  have hc : ∀ ω, density v ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e := by
    intro ω hω e he hbit
    have hh := exposureLaw_support w (G.incidentEdges O) σ ω hω e
      (G.cutEdges_subset_incidentEdges O he)
    exact hσ e he (hh ▸ hbit)
  have hc' : ∀ ω, density v' ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e :=
    fun ω hω => forceClosed_support w _ ω hω
  have heq : ∀ e ∉ G.incidentEdges O, v e = v' e := by
    intro e he
    have he' : e ∉ G.cutEdges O := fun hc => he (G.cutEdges_subset_incidentEdges O hc)
    funext b
    simp [v,v',exposureLaw,forceClosed,he,he']
  have ht := search_contact_moments G order ho O B hB a ha hp w h0 h1
  constructor
  · exact (contact_expect_exterior G order B O a ha p F w v v' hv hv' hc hc' heq id).trans ht.1
  · exact (contact_expect_exterior G order B O a ha p F w v v' hv hv' hc hc' heq
      (fun x => x^2)).le.trans ht.2

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

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

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

omit [Fintype E] [Fintype A] in
lemma freeze_self (D : Set E) (σ ω : E → A) (h : ∀ e ∈ D, σ e = ω e) :
    freeze D σ ω = ω := by
  funext e
  by_cases he : e ∈ D <;> simp [freeze,he,h]

omit [Fintype E] [Fintype A] in
lemma freeze_depends (D : Set E) (σ : E → A) {X : Type*} (f : (E → A) → X) :
    DependsOn (fun ω => f (freeze D σ ω)) Dᶜ := by
  intro ω η h
  apply congrArg f
  funext e
  by_cases he : e ∈ D
  · simp [freeze,he]
  · simp only [freeze,ite_eq_right he]
    exact h e he

lemma expect_exposureLaw (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (D : Set E) (σ : E → A) (f : (E → A) → ℝ) :
    expect (exposureLaw w D σ) f = expect w (fun ω => f (freeze D σ ω)) := by
  have hv := exposureLaw_normalized w D σ hw
  calc
    _ = expect (exposureLaw w D σ) (fun ω => f (freeze D σ ω)) := by
      unfold expect
      apply Finset.sum_congr rfl
      intro ω _
      by_cases hω : density (exposureLaw w D σ) ω = 0
      · simp only [hω,zero_mul]
      · dsimp only
        rw [freeze_self D σ ω (fun e he => (exposureLaw_support w D σ ω hω e he).symm)]
    _ = _ := expect_eq_on _ _ hv hw Dᶜ _ (freeze_depends D σ f)
      (fun e he => by funext a; have he' : e ∉ D := he; simp [exposureLaw,he'])

namespace Exposure
variable (R : Exposure E A B)

lemma disintegrate (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (f : B → (E → A) → ℝ) :
    expect w (fun ω => f (R.record ω) ω) =
      expect w (fun ω => expect (exposureLaw w (R.domain (R.record ω))
        (R.bits (R.record ω))) (f (R.record ω))) := by
  simp_rw [expect_exposureLaw w hw]
  have hh := expect_exposure w hw R.record R.domain R.atom
    (fun b ω => f b (freeze (R.domain b) (R.bits b) ω))
    (fun b => freeze_depends _ _ _)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg (expect w)
  funext ω
  rw [freeze_self _ _ _ (R.exact ω)]

lemma weighted_bound (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (hn : ∀ e a, 0 ≤ w e a) (g : B → ℝ) (hg : ∀ b, 0 ≤ g b)
    (f : B → (E → A) → ℝ) (C : ℝ)
    (hc : ∀ ω, expect (exposureLaw w (R.domain (R.record ω))
      (R.bits (R.record ω))) (f (R.record ω)) ≤ C) :
    expect w (fun ω => g (R.record ω) * f (R.record ω) ω) ≤
      C * expect w (fun ω => g (R.record ω)) := by
  rw [R.disintegrate w hw (fun b ω => g b * f b ω)]
  have he : ∀ b, expect (exposureLaw w (R.domain b) (R.bits b))
      (fun ω => g b*f b ω) = g b * expect (exposureLaw w (R.domain b) (R.bits b)) (f b) := by
    intro b
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [he]
  calc
    _ ≤ expect w (fun ω => g (R.record ω)*C) :=
      expect_mono hn (fun ω => mul_le_mul_of_nonneg_left (hc ω) (hg _))
    _ = _ := by rw [expect_mul_const]; ring

end Exposure
end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} (G : BondGraph V E)

lemma clusterObject_cut_closed (ω : Set E) (S : Set V) :
    ∀ e ∈ G.cutEdges (G.clusterObject ω S).1, ¬(G.clusterObject ω S).2 e := by
  rintro e ⟨x,y,he,hx,hy⟩ ⟨hω,_⟩
  exact hx (G.openBond_roots hω (by simp [he] : y ∈ G.ends e)
    (by simp [he] : x ∈ G.ends e) hy)

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

lemma scheduledContact_second (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) (B S : Set V) (hBS : B ⊆ S) (a : V)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (σ : Set E) :
    let C := G.clusterObject σ S
    expect (exposureLaw w (G.incidentEdges C.1) C.2)
      (fun ω => (max 1 (G.scheduledContact order B a p w C ω))^2) ≤ 4 := by
  dsimp only
  let C := G.clusterObject σ S
  let v := exposureLaw w (G.incidentEdges C.1) C.2
  have hw := homogeneous_normalized w p h0 h1
  have hv := exposureLaw_normalized w (G.incidentEdges C.1) C.2 hw
  have hn := exposureLaw_nonneg w (G.incidentEdges C.1) C.2
    (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
  by_cases ha : a ∈ C.1
  · have hh : (fun ω => (max 1 (G.scheduledContact order B a p w C ω))^2) =
        (fun _ : E → Prop => (1 : ℝ)) := by
      funext ω
      simp [scheduledContact,ha]
    change expect v _ ≤ 4
    rw [hh,expect_const _ hv]
    norm_num
  · have hB : B ⊆ C.1 := by
      intro b hb
      exact ⟨b,hBS hb,SimpleGraph.Reachable.refl b⟩
    have hm := LazyDFS.search_contact_moments_exposure G order ho B C.1 a ha hB C.2
      (G.clusterObject_cut_closed σ S) p hp w h0 h1
    let A := (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
      (fun ω => ∃ b ∈ B, (G.openGraph ω).Reachable a b) w
    have he : (fun ω => (max 1 (G.scheduledContact order B a p w C ω))^2) =
        (fun ω => (max 1 (A ω))^2) := by
      funext ω
      simp only [scheduledContact,ite_eq_right ha,A]
    change expect v _ ≤ 4
    rw [he]
    calc
      _ ≤ expect v (fun ω => 1+(A ω)^2) := expect_mono hn (fun ω => by
        by_cases hh : A ω ≤ 1
        · rw [max_eq_left hh]
          nlinarith [sq_nonneg (A ω)]
        · rw [max_eq_right (le_of_not_ge hh)]
          linarith)
      _ = 1 + expect v (fun ω => (A ω)^2) := by
        rw [expect_add v (fun _ => 1) (fun ω => (A ω)^2),expect_const v hv]
      _ ≤ 4 := by linarith [hm.2]

end CriticalPercolation.BondGraph

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_contactScore_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v) :
    (compile G order B fuel st stack).contactScore p C F w ω =
      (compile G order B fuel st stack).contactScore p C F w η := by
  induction fuel generalizing st stack w with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
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
          simp only [contactScore,←propext (h d.2.1 hinc)]
          by_cases hopen : ω d.2.1
          · simp only [ite_eq_left hopen]
            have hs' : ∀ v ∈ (st.opened d.2.1 d.2.2).reached,
                (G.openGraph ω).Reachable a v := by
              intro v hv
              rcases Finset.mem_insert.mp hv with rfl | hv
              · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
              · exact hst v hv
            exact congrArg (_ + ·) (ih _ _ _ hs')
          · simp only [ite_eq_right hopen]
            exact congrArg (_ + ·) (ih (st.closed d.2.1) rest (pin w d.2.1 False) hst)

variable [Fintype V]
lemma search_contactScore_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (p : ℝ) (C : Set E) (F : Set E → Prop) (w : E → Prop → ℝ)
    (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g)) :
    (search G order a B).contactScore p C F w ω =
      (search G order a B).contactScore p C F w η := by
  exact compile_contactScore_incidence G order B _ _ _ p C F w ω η a h
    (fun v hv => by have he : v=a := Finset.mem_singleton.mp hv; subst v; exact .refl _)

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.FiniteProduct.Exposure
variable {E A B : Type*} (R : Exposure E A B)
lemma bits_congr {ω η : E → A} (h : R.record ω = R.record η) {e : E}
    (he : e ∈ R.domain (R.record ω)) : ω e = η e := by
  rw [←R.exact ω e he,h]
  exact R.exact η e (h ▸ he)
end CriticalPercolation.FiniteProduct.Exposure

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct ClusterDeletion

variable {V E : Type*} [Fintype E] [Fintype V] (G : BondGraph V E)

omit [Fintype E] [Fintype V] in
lemma clusterObject_refines {S T : Set V} (hST : S ⊆ T) (ω η : Set E)
    (h : G.clusterObject ω T = G.clusterObject η T) :
    G.clusterObject ω S = G.clusterObject η S := by
  apply Eq.symm
  apply G.clusterObject_eq_of_incident rfl
  intro e he
  have he' : e ∈ G.incidentEdges (G.clusterObject ω T).1 := by
    rcases he with ⟨v,⟨a,ha,hav⟩,hv⟩
    exact ⟨v,⟨a,hST ha,hav⟩,hv⟩
  exact ((G.incidenceExposure T).bits_congr h he').to_iff

variable [DecidableEq V] [DecidableEq E]
lemma scheduledContact_record (order : List (LazyDFS.Dart V E))
    (B S T : Set V) (a : V) (hST : S ⊆ T) (ha : a ∈ T)
    (p : ℝ) (w : E → Prop → ℝ) (ω η : E → Prop)
    (h : G.clusterObject ω T = G.clusterObject η T) :
    G.scheduledContact order B a p w (G.clusterObject ω S) ω =
      G.scheduledContact order B a p w (G.clusterObject η S) η := by
  have hC := G.clusterObject_refines hST ω η h
  unfold scheduledContact
  rw [←hC]
  split_ifs with hhold
  · rfl
  · apply LazyDFS.search_contactScore_incidence
    rintro e ⟨v,hv,hav⟩
    exact ((G.incidenceExposure T).bits_congr h ⟨v,⟨a,ha,hav⟩,hv⟩).to_iff

end CriticalPercolation.BondGraph

namespace CriticalPercolation.FiniteProduct
open scoped Classical
open FiniteEntropy

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

theorem sequential_bound (R : ℕ → Exposure E A B) (step : ℕ → B → (E → A) → ℝ)
    (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (hn : ∀ e a, 0 ≤ w e a)
    (hs : ∀ i b ω, 0 ≤ step i b ω) (C : ℝ) (hC : 0 ≤ C)
    (hstep : ∀ i ω, expect (exposureLaw w ((R i).domain ((R i).record ω))
      ((R i).bits ((R i).record ω))) (step i ((R i).record ω)) ≤ C)
    (hpast : ∀ i n, i<n → ∀ ω η, (R n).record ω = (R n).record η →
      step i ((R i).record ω) ω = step i ((R i).record η) η) (n : ℕ) :
    expect w (fun ω => ∏ i ∈ Finset.range n, step i ((R i).record ω) ω) ≤ C^n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.prod_empty,pow_zero,expect_const _ hw,le_refl]
  | succ n ih =>
    let f : (E → A) → ℝ := fun ω => ∏ i ∈ Finset.range n, step i ((R i).record ω) ω
    let g := fiberValue (R n).record f
    have hfn : ∀ ω, 0 ≤ f ω := fun ω => Finset.prod_nonneg (fun i _ => hs i _ ω)
    have hgn : ∀ b, 0 ≤ g b := fiberValue_nonneg _ _ hfn
    have hg : ∀ ω, g ((R n).record ω) = f ω := by
      apply fiberValue_apply
      intro ω η he
      exact Finset.prod_congr rfl (fun i hi => hpast i n (Finset.mem_range.mp hi) ω η he)
    calc
      _ = expect w (fun ω => g ((R n).record ω) * step n ((R n).record ω) ω) := by
        apply congrArg (expect w)
        funext ω
        rw [hg,Finset.prod_range_succ]
      _ ≤ C * expect w (fun ω => g ((R n).record ω)) :=
        (R n).weighted_bound w hw hn g hgn (step n) C (hstep n)
      _ = C * expect w f := by simp_rw [hg]
      _ ≤ C*C^n := mul_le_mul_of_nonneg_left ih hC
      _ = C^(n+1) := by rw [pow_succ]; ring

end CriticalPercolation.FiniteProduct

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*}

lemma anchorSet_mono (S : Set V) (a : ℕ → V) {i n : ℕ} (hi : i ≤ n) :
    anchorSet S a i ⊆ anchorSet S a n := by
  rintro v (hv|⟨j,hj,rfl⟩)
  · exact Or.inl hv
  · exact Or.inr ⟨j,lt_of_lt_of_le hj hi,rfl⟩

lemma anchor_mem_anchorSet (S : Set V) (a : ℕ → V) {i n : ℕ} (hi : i<n) :
    a i ∈ anchorSet S a n := Or.inr ⟨i,hi,rfl⟩

variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem scheduled_contact_product (G : BondGraph V E)
    (order : List (LazyDFS.Dart V E)) (ho : LazyDFS.Exhaustive G order)
    (S : Set V) (a : ℕ → V) (B : ℕ → Set V) (hB : ∀ i, B i ⊆ anchorSet S a i)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (n : ℕ) :
    expect w (fun ω => ∏ i ∈ Finset.range n,
      (max 1 (G.scheduledContact order (B i) (a i) p w
        (G.clusterObject ω (anchorSet S a i)) ω))^2) ≤ 4^n := by
  apply sequential_bound (fun i => G.incidenceExposure (anchorSet S a i))
    (fun i C ω => (max 1 (G.scheduledContact order (B i) (a i) p w C ω))^2)
    w (homogeneous_normalized w p h0 h1)
    (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
    (fun _ _ _ => sq_nonneg _) 4 (by norm_num)
  · intro i ω
    exact G.scheduledContact_second order ho (B i) (anchorSet S a i) (hB i) (a i) hp w h0 h1 ω
  · intro i k hik ω η he
    congr 2
    exact G.scheduledContact_record order (B i) (anchorSet S a i) (anchorSet S a k) (a i)
      (anchorSet_mono S a hik.le) (anchor_mem_anchorSet S a hik) p w ω η he

end CriticalPercolation.BondGraph

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem scheduled_contact_exponential (G : BondGraph V E)
    (order : List (LazyDFS.Dart V E)) (ho : LazyDFS.Exhaustive G order)
    (S : Set V) (a : ℕ → V) (B : ℕ → Set V) (hB : ∀ i, B i ⊆ anchorSet S a i)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (n : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range n) :
    expect w (fun ω => Real.exp (2*∑ i ∈ I,
      Real.log (max 1 (G.scheduledContact order (B i) (a i) p w
        (G.clusterObject ω (anchorSet S a i)) ω)))) ≤ Real.exp (n*Real.log 4) := by
  let A := fun i ω => G.scheduledContact order (B i) (a i) p w
    (G.clusterObject ω (anchorSet S a i)) ω
  have hpow (ω : E → Prop) : Real.exp (2*∑ i ∈ I, Real.log (max 1 (A i ω))) =
      ∏ i ∈ I, (max 1 (A i ω))^2 := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [two_mul,Real.exp_add,Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))]
    ring
  change expect w (fun ω => Real.exp (2*∑ i ∈ I, Real.log (max 1 (A i ω)))) ≤ _
  simp_rw [hpow]
  calc
    _ ≤ expect w (fun ω => ∏ i ∈ Finset.range n, (max 1 (A i ω))^2) := by
      apply expect_mono (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
      intro ω
      apply Finset.prod_le_prod_of_subset_of_one_le hI
      · intro i _; exact sq_nonneg _
      · intro i _ _
        have hh : (1:ℝ) ≤ max 1 (A i ω) := le_max_left _ _
        nlinarith
    _ ≤ 4^n := G.scheduled_contact_product order ho S a B hB hp w h0 h1 n
    _ = Real.exp (n*Real.log 4) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<4)]

end CriticalPercolation.BondGraph

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

theorem contactScore_eq_queryDelta_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) :
    T.contactScore p C F w ω = ∑ e, if e ∈ C then p*T.queryDelta F w ω e else 0 := by
  induction T generalizing used w with
  | done _ => simp [contactScore,queryDelta]
  | ask f l r hl hr =>
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, if e ∈ C then
          p*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
        (if f ∈ C then p*delta w F f else 0) +
          ∑ e, if e ∈ C then p*T'.queryDelta F w' ω e else 0 := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if e ∈ C then
          p*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
          (if e = f then (if f ∈ C then p*delta w F f else 0) else 0) +
          (if e ∈ C then p*T'.queryDelta F w' ω e else 0) := by
        by_cases he : e = f
        · subst e; rw [hz]; simp
        · simp only [ite_eq_right he,zero_add]
      simp only [heq,Finset.sum_add_distrib]
      simp
    change (if f ∈ C then p*delta w F f else 0) +
      (if ω f then r.contactScore p C F (pin w f True) ω
       else l.contactScore p C F (pin w f False) ω) = _
    by_cases hf : ω f
    · simp only [ite_eq_left hf,queryDelta]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
    · simp only [ite_eq_right hf,queryDelta]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma sum_contactWeight (order : List (LazyDFS.Dart V E)) (B O : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (ω : E → Prop) :
    (∑ e, G.contactWeight order B O a p w ω e) =
      (LazyDFS.search G order a B).contactScore p (G.cutEdges O)
        (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω := by
  exact (contactScore_eq_queryDelta_sum _ ∅ (LazyDFS.compile_valid G order B _ _ _)
    p _ _ w ω).symm

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

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryWords
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

end CriticalPercolation.BinaryLaw
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

lemma sum_pushMass_mul (f : X → Y) (P : X → ℝ) (g : Y → ℝ) :
    ∑ y, pushMass f P y * g y = ∑ x, P x * g (f x) := by
  classical
  simp only [pushMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

end CriticalPercolation.FiniteEntropy

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PrefixScoreNonneg
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

namespace CriticalPercolation.ExactExposure
open scoped Classical
open FiniteProduct SearchTree LazyDFS

variable {V E : Type*} [Fintype V] [Fintype E]

lemma expect_configuration (w : E → Prop → ℝ) (f : Set E → ℝ) :
    expect (fun e (b : Bool) => w e (b = true)) (fun ω => f (configuration ω)) =
      expect w f := by
  let e : (E → Bool) ≃ (E → Prop) := Equiv.piCongrRight (fun _ => Equiv.propEquivBool.symm)
  have he (ω : E → Bool) : e ω = configuration ω := rfl
  unfold expect
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro ω _
  rw [he]
  rfl

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

lemma rawContact_sum (order : List (LazyDFS.Dart V E)) (B : Set V)
    (a : V) (p : ℝ) (w : E → Prop → ℝ) (C : ClusterObject V E) (ω : E → Prop) :
    (∑ mark, G.rawContact order B a p w C ω mark) =
      G.scheduledContact order B a p w C ω := by
  unfold rawContact scheduledContact
  split_ifs with ha
  · simp
  · rw [Fintype.sum_option]
    simp only [zero_add]
    exact G.sum_contactWeight order B C.1 a p w ω

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

lemma scheduledTargets_anchors (d : ℕ) (x : ℕ → V) (n : ℕ) (b : Fin n → Bool)
    (k : ℕ) (hk : k≤n) :
    scheduledTargets (E := E) d x n b k =
      BondGraph.anchorSet {x 0,x d} (scheduledAnchor (E := E) d x n b) k := by
  induction k with
  | zero =>
    ext v
    simp [scheduledTargets,anchorSet,anchors,BondGraph.anchorSet,or_comm]
  | succ k ih =>
    have hi := ih (by omega)
    unfold scheduledTargets at *
    rw [anchorSet_step,prefix_succ_fst n _ k (by omega),hi]
    ext v
    simp only [BondGraph.anchorSet,Set.mem_insert_iff,Set.mem_union,Set.mem_image,Set.mem_ofPred_eq]
    constructor
    · rintro (rfl|hv)
      · exact Or.inr ⟨k,by omega,rfl⟩
      · rcases hv with hv|⟨j,hj,hv⟩
        · exact Or.inl hv
        · exact Or.inr ⟨j,by omega,hv⟩
    · rintro (hv|⟨j,hj,hv⟩)
      · exact Or.inr (Or.inl hv)
      · by_cases he : j=k
        · subst j; exact Or.inl hv.symm
        · exact Or.inr (Or.inr ⟨j,by omega,hv⟩)

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

lemma pushMass_fst (P : X × M → ℝ) (x : X) :
    pushMass Prod.fst P x = ∑ m, P (x,m) := by
  simp only [pushMass,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

theorem marginal_density_le (P : (X × (I → M)) → ℝ) (μ : X → ℝ)
    (a : I → X → M → ℝ) (L : ℝ)
    (hd : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i x.1 (x.2 i)) (ω : X) :
    pushMass Prod.fst P ω ≤ Real.exp L * μ ω * ∏ i, ∑ m, a i ω m := by
  rw [pushMass_fst, Fintype.prod_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun m _ => hd (ω,m)

theorem entropy_exponential_domination (Q μ : X → ℝ) (hQ : ∀ x, 0 ≤ Q x)
    (hm : ∑ x, Q x = 1) (hμ : ∀ x, 0 < μ x) (ξ : X → ℝ)
    (L B : ℝ) (hd : ∀ x, Q x ≤ Real.exp L * μ x * Real.exp (ξ x))
    (hmgf : ∑ x, μ x * Real.exp (2 * ξ x) ≤ Real.exp B) :
    divergence Q μ ≤ 2*L+B ∧ (∑ x, Q x*ξ x) ≤ L+B := by
  have hlog : divergence Q μ ≤ L + ∑ x, Q x * ξ x := by
    have hh (x : X) : Q x * Real.log (Q x / μ x) ≤ Q x * (L + ξ x) := by
      by_cases hx : Q x = 0
      · simp [hx]
      · have hp : 0 < Q x := lt_of_le_of_ne (hQ x) (Ne.symm hx)
        have hr : Q x / μ x ≤ Real.exp (L + ξ x) := by
          rw [div_le_iff₀ (hμ x), Real.exp_add]
          simpa only [mul_assoc,mul_left_comm,mul_comm] using hd x
        have hl := Real.log_le_log (div_pos hp (hμ x)) hr
        rw [Real.log_exp] at hl
        exact mul_le_mul_of_nonneg_left hl (hQ x)
    have hh := Finset.sum_le_sum (s := Finset.univ) fun x _ => hh x
    simpa only [divergence, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hm, one_mul] using hh
  have hent := entropy_inequality Q μ hQ (fun x => (hμ x).le) hm
    (fun x _ => hμ x) (fun x => 2 * ξ x)
  have hmgfpos := normalizer_pos Q μ hQ (fun x => (hμ x).le) hm
    (fun x _ => hμ x) (fun x => 2 * ξ x)
  have hb := Real.log_le_log hmgfpos hmgf
  rw [Real.log_exp] at hb
  have he : (∑ x, Q x * (2 * ξ x)) = 2 * ∑ x, Q x * ξ x := by
    simp only [Finset.mul_sum]
    congr 1
    ext x
    ring
  rw [he] at hent
  constructor <;> linarith

omit [Fintype X] in
lemma exp_logContactMass (a : I → X → M → ℝ) (ω : X) :
    Real.exp (logContactMass a ω) = ∏ i, max 1 (∑ m, a i ω m) := by
  rw [logContactMass,Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

theorem contact_configuration_entropy (P : (X × (I → M)) → ℝ)
    (hP : ∀ x, 0 ≤ P x) (hm : ∑ x, P x = 1) (μ : X → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (a : I → X → M → ℝ) (ha : ∀ i ω m, 0 ≤ a i ω m) (L B : ℝ)
    (hd : ∀ x, P x ≤ Real.exp L * μ x.1 * ∏ i, a i x.1 (x.2 i))
    (hmgf : ∑ ω, μ ω * Real.exp (2 * logContactMass a ω) ≤ Real.exp B) :
    divergence (pushMass Prod.fst P) μ ≤ 2*L+B ∧
      (∑ x, P x * logContactMass a x.1) ≤ L+B := by
  have hd' (ω : X) : pushMass Prod.fst P ω ≤
      Real.exp L * μ ω * Real.exp (logContactMass a ω) := by
    rw [exp_logContactMass]
    exact (marginal_density_le P μ a L hd ω).trans
      (mul_le_mul_of_nonneg_left (Finset.prod_le_prod
        (fun i _ => Finset.sum_nonneg fun m _ => ha i ω m)
        (fun i _ => le_max_right _ _)) (mul_pos (Real.exp_pos L) (hμ ω)).le)
  have hh := entropy_exponential_domination (pushMass Prod.fst P) μ
    (pushMass_nonneg _ _ hP) (by rw [pushMass_sum,hm]) hμ (logContactMass a) L B hd' hmgf
  rw [sum_pushMass_mul] at hh
  exact hh

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

lemma scheduleWeight_sum (n : ℕ) (b : Fin n → Bool) (i : Fin n) (ω : E → Prop) :
    (∑ m, scheduleWeight G order d x p w n b i ω m) =
      G.scheduledContact order
        (BondGraph.anchorSet {x 0,x d} (scheduledAnchor (E := E) d x n b) i.val)
        (scheduledAnchor (E := E) d x n b i.val) p w
        (G.clusterObject ω (BondGraph.anchorSet {x 0,x d} (scheduledAnchor (E := E) d x n b) i.val)) ω := by
  unfold scheduleWeight
  rw [G.rawContact_sum,scheduledTargets_anchors d x n b i.val i.isLt.le]

theorem scheduleWeight_exponential (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (n : ℕ) (b : Fin n → Bool) :
    expect w (fun ω => Real.exp (2*logContactMass (scheduleWeight G order d x p w n b) ω)) ≤
      Real.exp (n*Real.log 4) := by
  let a := scheduledAnchor (E := E) d x n b
  let B := BondGraph.anchorSet {x 0,x d} a
  have he (ω : E → Prop) : logContactMass (scheduleWeight G order d x p w n b) ω =
      ∑ i ∈ Finset.range n, Real.log (max 1 (G.scheduledContact order (B i) (a i) p w
        (G.clusterObject ω (B i)) ω)) := by
    unfold logContactMass
    simp only [scheduleWeight_sum]
    exact Fin.sum_univ_eq_sum_range (fun i => Real.log (max 1 (G.scheduledContact order (B i) (a i) p w
      (G.clusterObject ω (B i)) ω))) n
  simp_rw [he]
  exact G.scheduled_contact_exponential order ho {x 0,x d} a B (fun _ => Set.Subset.refl _)
    hp w h0 h1 n (Finset.range n) (Finset.Subset.refl _)

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

lemma sum_configuration (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (f : Set E → ℝ) :
    (∑ ω : E → Bool, FiniteProduct.density (QueryTree.bitWeight p) ω * f (configuration ω)) =
      expect w f := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  have he := expect_configuration w f
  rw [← hw] at he
  refine Eq.trans ?_ he
  unfold expect
  apply Finset.sum_congr
  · ext f; simp only [Finset.mem_univ]
  · intro f _; rfl

lemma scheduleWeight_exponential_bool (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (n : ℕ) (b : Fin n → Bool) :
    (∑ ω : E → Bool, FiniteProduct.density (QueryTree.bitWeight p) ω *
      Real.exp (2*logContactMass (fun i ω => scheduleWeight G order d x p w n b i (configuration ω)) ω)) ≤
      Real.exp (n*Real.log 4) := by
  have he := sum_configuration p w h0 h1
    (fun ω => Real.exp (2*logContactMass (scheduleWeight G order d x p w n b) ω))
  change (∑ ω : E → Bool, FiniteProduct.density (QueryTree.bitWeight p) ω *
    Real.exp (2*logContactMass (scheduleWeight G order d x p w n b) (configuration ω))) ≤ _
  rw [he]
  exact scheduleWeight_exponential G order d x p w ho hp h0 h1 n b

noncomputable section EntropyFinal

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.classicalFinDecidable
theorem conditioned_configuration_entropy_bs_oai (ho : LazyDFS.Exhaustive G order)
    (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let Q := conditionedMass G order d x p w s n D
    let a := fun i ω => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω)
    divergence (pushMass Prod.fst Q) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
        2*constructionCost G order d x p w c s n D+n*Real.log 4 ∧
      (∑ z, Q z * logContactMass a z.1) ≤ constructionCost G order d x p w c s n D+n*Real.log 4 := by
  exact contact_configuration_entropy
    (conditionedMass G order d x p w s n D)
    (conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD)
    (by
      have hz := conditionedMass_normalized G order d x p w s n D hD
      refine Eq.trans ?_ hz
      apply Finset.sum_congr
      · ext z; simp only [Finset.mem_univ]
      · intro z _; rfl)
    (FiniteProduct.density (QueryTree.bitWeight p))
    (fun ω => Finset.prod_pos (fun e _ => QueryTree.bitWeight_pos hp e (ω e)))
    (fun i ω => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω))
    (fun i ω m => scheduleWeight_nonneg G order d x p w hp h0 h1 n _ i _ m)
    (constructionCost G order d x p w c s n D) (n*Real.log 4)
    (conditionedMass_density_le G order d x p w hd hp h0 h1 hc hc1 hconn s n D hδ hD)
    (scheduleWeight_exponential_bool G order d x p w ho hp h0 h1 n _)

end EntropyFinal
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs_oai.{u_1, u_2}
