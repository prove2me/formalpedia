-- Prove2me | solution 1 for OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:13:22.372647+00:00
-- url     : https://prove2.me/submissions/33a3b0e2-8450-4f13-991b-9dcb1724debc

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_LazyDFS_young_phase_score_bound_bs

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

end CriticalPercolation.LazyDFS

end
end

end OAI
end

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

lemma eraseBond_openGraph (f : E) (o : V) (ω : Set E) :
    (G.eraseBond f o).openGraph ω = G.openGraph {e | e ≠ f ∧ e ∈ ω} := by
  ext u v
  unfold openGraph
  rw [SimpleGraph.fromEdgeSet_adj,SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨e,he,hev⟩,huv⟩
    have hef : e ≠ f := by
      intro hh
      subst e
      simp only [eraseBond,Function.update_self] at hev
      have hd := (Sym2.eq_iff.mp hev)
      rcases hd with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact huv (h1.symm.trans h2)
      · exact huv (h2.symm.trans h1)
    exact ⟨⟨e,⟨hef,he⟩,(G.eraseBond_ends_ne f o hef).symm.trans hev⟩,huv⟩
  · rintro ⟨⟨e,⟨hef,he⟩,hev⟩,huv⟩
    exact ⟨⟨e,he,(G.eraseBond_ends_ne f o hef).trans hev⟩,huv⟩

lemma knownGraph_le_eraseBond (read : Finset E) (f : E) (o : V) (ω : Set E)
    (hf : f ∉ read) :
    G.openGraph {e | e ∈ read ∧ e ∈ ω} ≤ (G.eraseBond f o).openGraph ω := by
  rw [G.eraseBond_openGraph]
  apply SimpleGraph.fromEdgeSet_mono ∘ Set.image_mono
  intro e he
  exact ⟨fun hef => hf (hef ▸ he.1),he.2⟩

lemma openGraph_eq_eraseBond_sup (f : E) (o v z : V) (ω : Set E)
    (hf : f ∈ ω) (he : G.ends f = s(v,z)) :
    G.openGraph ω = (G.eraseBond f o).openGraph ω ⊔ SimpleGraph.edge v z := by
  rw [G.eraseBond_openGraph]
  have hh : ω = insert f {e | e ≠ f ∧ e ∈ ω} := by
    ext e
    by_cases h : e = f
    · subst e; simp [hf]
    · simp [h]
  conv_lhs => rw [hh]
  rw [openGraph,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _

lemma eraseBond_openGraph_force_false (f : E) (o : V) (ω : Set E) :
    (G.eraseBond f o).openGraph ω = G.openGraph (Function.update ω f False) := by
  rw [G.eraseBond_openGraph]
  congr 1
  ext e
  change (e ≠ f ∧ e ∈ ω) ↔ Function.update ω f False e
  by_cases h : e = f
  · subst e
    erw [Function.update_self]
    simp
  · erw [Function.update_of_ne h]
    change (e ≠ f ∧ e ∈ ω) ↔ e ∈ ω
    simp [h]

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ListScore
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
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma score_eq_listScore (T : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) :
    T.score p F w ω = listScore p F ω (T.reads (fun e => decide (ω e))) w := by
  induction T generalizing w with
  | done r => rfl
  | ask e l r hl hr =>
    by_cases he : ω e
    · simp only [score,he,↓reduceIte,reads,decide_true,listScore,hr]
    · simp only [score,he,↓reduceIte,reads,decide_false,Bool.false_eq_true,listScore,hl]

lemma score_eq_of_reads_eq (T T' : SearchTree E R) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E)
    (h : T.reads (fun e => decide (ω e)) = T'.reads (fun e => decide (ω e))) :
    T.score p F w ω = T'.score p F w ω := by
  rw [score_eq_listScore,score_eq_listScore,h]

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PhaseFrontier
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
lemma phaseFrontier_pop (G : BondGraph V E) (A : Set V) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : PhaseFrontier G A st ((v,e,t)::rest))
    (hskip : t ∈ st.reached ∨ e ∈ st.read ∨ v ∉ st.reached ∨ G.ends e ≠ s(v,t)) :
    PhaseFrontier G A st rest := by
  intro u hu huA f y hfy hy
  rcases h u hu huA f y hfy hy with hf | hf
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
lemma phaseFrontier_closed (G : BondGraph V E) (A : Set V) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : PhaseFrontier G A st ((v,e,t)::rest)) : PhaseFrontier G A (st.closed e) rest := by
  intro u hu huA f y hfy hy
  rcases h u hu huA f y hfy hy with hf | hf
  · exact Or.inl (Finset.mem_insert_of_mem hf)
  · rcases List.mem_cons.mp hf with hd | hd
    · simp only [Prod.mk.injEq] at hd
      rcases hd with ⟨rfl,rfl,rfl⟩
      exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr hd

lemma phaseFrontier_opened (G : BondGraph V E) (A : Set V) (order : List (Dart V E))
    (ho : Exhaustive G order) (st : State V E)
    (v : V) (e : E) (t : V) (rest : List (Dart V E))
    (h : PhaseFrontier G A st ((v,e,t)::rest)) :
    PhaseFrontier G A (st.opened e t) (push G order t ++ rest) := by
  intro u hu huA f y hfy hy
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact Or.inr (List.mem_append_left _ (List.mem_filter.mpr
      ⟨ho u f y hfy,by simpa only [decide_eq_true_eq,true_and] using hfy⟩))
  · have hy' : y ∉ st.reached := fun hy' => hy (Finset.mem_insert_of_mem hy')
    rcases h u hu huA f y hfy hy' with hf | hf
    · exact Or.inl (Finset.mem_insert_of_mem hf)
    · rcases List.mem_cons.mp hf with hd | hd
      · simp only [Prod.mk.injEq] at hd
        rcases hd with ⟨rfl,rfl,rfl⟩
        exact Or.inl (Finset.mem_insert_self _ _)
      · exact Or.inr (List.mem_append_right _ hd)

omit [DecidableEq V] [DecidableEq E] in
lemma empty_phaseFrontier_closed (G : BondGraph V E) (A : Set V) (st : State V E)
    (ω : E → Bool) (hf : PhaseFrontier G A st []) (hc : ReadConsistent G st ω) :
    ∀ v ∈ st.reached, v ∉ A → ∀ t, (G.openGraph {e | ω e = true}).Adj v t →
      t ∈ st.reached := by
  intro v hv hvA t ht
  obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp ht
  by_contra htr
  rcases hf v hv hvA e t heq htr with hr | hr
  · exact htr (hc e hr he t (by simp [heq]))
  · simp at hr

variable [Fintype V]

theorem phase_success_or_closed (G : BondGraph V E) (A : Set V) (order : List (Dart V E))
    (ho : Exhaustive G order) (B : Set V) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (ω : E → Bool)
    (hf : PhaseFrontier G A st stack) (hc : ReadConsistent G st ω) (hr : rank order st stack ≤ fuel) :
    let final := (compile G order B fuel st stack).run ω
    (∃ v ∈ final.reached, v ∈ B) ∨
      (∀ v ∈ final.reached, v ∉ A → ∀ t, (G.openGraph {e | ω e = true}).Adj v t →
        t ∈ final.reached) := by
  induction fuel generalizing st stack with
  | zero =>
    have hs : stack = [] := by
      have hh : stack.length = 0 := by dsimp [rank] at hr; omega
      exact List.length_eq_zero_iff.mp hh
    subst stack
    exact Or.inr (empty_phaseFrontier_closed G A st ω hf hc)
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · exact Or.inl hh
    · cases stack with
      | nil => exact Or.inr (empty_phaseFrontier_closed G A st ω hf hc)
      | cons d rest =>
        rcases d with ⟨v,e,t⟩
        dsimp only
        split_ifs with hd
        · exact ih st rest (phaseFrontier_pop G A st v e t rest hf hd) hc
            (by have hh := rank_pop order st (v,e,t) rest; omega)
        · have hdec : t ∉ st.reached ∧ e ∉ st.read ∧ v ∈ st.reached ∧ G.ends e = s(v,t) := by
            push Not at hd
            exact hd
          rw [SearchTree.run]
          split_ifs with he
          · exact ih _ _ (phaseFrontier_opened G A order ho st v e t rest hf)
              (readConsistent_opened G st ω hc hdec.2.2.1 hdec.2.2.2)
              (by have hh := rank_opened G order st (v,e,t) rest hdec.1; dsimp only at hh; omega)
          · have he' : ω e = false := Bool.eq_false_iff.mpr he
            exact ih _ _ (phaseFrontier_closed G A st v e t rest hf)
              (readConsistent_closed G st ω hc he')
              (by have hh := rank_closed order st (v,e,t) rest; dsimp only at hh; omega)

omit [Fintype V] in

theorem compile_append_of_success (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (young older : List (Dart V E)) (ω : E → Bool)
    (hs : ∃ v ∈ ((compile G order B fuel st young).run ω).reached, v ∈ B) :
    (compile G order B fuel st (young++older)).run ω = (compile G order B fuel st young).run ω ∧
    (compile G order B fuel st (young++older)).reads ω = (compile G order B fuel st young).reads ω := by
  induction fuel generalizing st young with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    simp only [compile.eq_def G order B (n+1) st] at hs ⊢
    by_cases hh : ∃ v ∈ st.reached, v ∈ B
    · simp [hh,SearchTree.run,SearchTree.reads]
    · simp only [hh,↓reduceIte] at hs ⊢
      cases young with
      | nil => exact (hh hs).elim
      | cons d rest =>
        simp only [List.cons_append]
        dsimp only at hs ⊢
        by_cases hd : d.2.2 ∈ st.reached ∨ d.2.1 ∈ st.read ∨ d.1 ∉ st.reached ∨
            G.ends d.2.1 ≠ s(d.1,d.2.2)
        · simp only [hd,↓reduceIte] at hs ⊢
          exact ih st rest hs
        · simp only [hd,↓reduceIte,SearchTree.run,SearchTree.reads] at hs ⊢
          by_cases he : ω d.2.1 = true
          · simp only [he,↓reduceIte] at hs ⊢
            have h := ih (st.opened d.2.1 d.2.2) (push G order d.2.2++rest) hs
            simpa only [List.append_assoc,List.cons.injEq,true_and] using h
          · simp only [he,Bool.false_eq_true,↓reduceIte] at hs ⊢
            have h := ih (st.closed d.2.1) rest hs
            simpa only [List.cons.injEq,true_and] using h

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ReachableMemPhaseClosed
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
lemma reachable_mem_of_phase_closed (H : SimpleGraph V) (A : Set V) (S : Finset V)
    (hc : ∀ v ∈ S, v ∉ A → ∀ t, H.Adj v t → t ∈ S) {z t : V}
    (ha : ∀ a ∈ A, ¬H.Reachable z a) (ht : H.Reachable z t) (hz : z ∈ S) : t ∈ S := by
  have hh : ∀ {u v : V}, H.Walk u v → H.Reachable z u → u ∈ S → v ∈ S := by
    intro u v path
    induction path with
    | nil => exact fun _ h => h
    | @cons u v y h path ih =>
      intro hzu hu
      exact ih (hzu.trans h.reachable) (hc u hu (fun hA => ha u hA hzu) v h)
  exact ht.elim (fun path => hh path (.refl _) hz)

lemma opened_phaseFrontier (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (st : State V E) (f : E) (z : V) :
    PhaseFrontier G (st.reached : Set V) (st.opened f z) (push G order z) := by
  intro v hv hvA e t het _
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact Or.inr (List.mem_filter.mpr
      ⟨ho v e t het,by simpa only [decide_eq_true_eq,true_and] using het⟩)
  · exact (hvA hv).elim

variable [Fintype V]

theorem phase_hits_of_avoiding_connection (G : BondGraph V E) (A : Set V)
    (order : List (Dart V E)) (ho : Exhaustive G order) (B : Set V)
    (fuel : ℕ) (st : State V E) (young : List (Dart V E)) (ω : E → Bool)
    (hf : PhaseFrontier G A st young) (hc : ReadConsistent G st ω)
    (hr : rank order st young ≤ fuel) (H : SimpleGraph V)
    (hH : H ≤ G.openGraph {e | ω e = true}) (z : V) (hz : z ∈ st.reached)
    (ha : ∀ a ∈ A, ¬H.Reachable z a) (ht : ∃ t ∈ B, H.Reachable z t) :
    ∃ t ∈ ((compile G order B fuel st young).run ω).reached, t ∈ B := by
  rcases phase_success_or_closed G A order ho B fuel st young ω hf hc hr with h | h
  · exact h
  · obtain ⟨t,htB,hzt⟩ := ht
    have hclosed : ∀ v ∈ ((compile G order B fuel st young).run ω).reached,
        v ∉ A → ∀ u, H.Adj v u → u ∈ ((compile G order B fuel st young).run ω).reached := by
      intro v hv hvA u hvu
      exact h v hv hvA u (hH hvu)
    exact ⟨t,reachable_mem_of_phase_closed H A _ hclosed ha hzt
      ((compile_mono G order B fuel st young ω).1 hz),htB⟩

theorem phase_no_older_reads (G : BondGraph V E) (A : Set V)
    (order : List (Dart V E)) (ho : Exhaustive G order) (B : Set V)
    (fuel : ℕ) (st : State V E) (young older : List (Dart V E)) (ω : E → Bool)
    (hf : PhaseFrontier G A st young) (hc : ReadConsistent G st ω)
    (hr : rank order st young ≤ fuel) (H : SimpleGraph V)
    (hH : H ≤ G.openGraph {e | ω e = true}) (z : V) (hz : z ∈ st.reached)
    (ha : ∀ a ∈ A, ¬H.Reachable z a) (ht : ∃ t ∈ B, H.Reachable z t) :
    (compile G order B fuel st (young++older)).reads ω =
      (compile G order B fuel st young).reads ω :=
  (compile_append_of_success G order B fuel st young older ω
    (phase_hits_of_avoiding_connection G A order ho B fuel st young ω hf hc hr H hH z hz ha ht)).2

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

lemma density_force_nonzero (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop)
    (h : density w ω ≠ 0) (hb : w e b ≠ 0) :
    density w (Function.update ω e b) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hj : j = e
  · subst j
    erw [Function.update_self]
    exact hb
  · erw [Function.update_of_ne hj]
    exact coordinate_ne_zero_of_density w ω h j

lemma density_pin_of_support (w : E → Prop → ℝ) (ω : Set E) (e : E) (b : Prop)
    (h : density w ω ≠ 0) (hb : ω e = b) : density (pin w e b) ω ≠ 0 := by
  erw [density_pin, ite_eq_left hb, one_mul]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact coordinate_ne_zero_of_density w ω h j

lemma delta_congr_support (w : E → Prop → ℝ) (e : E)
    (h0 : w e False ≠ 0) (h1 : w e True ≠ 0) (F F' : Set E → Prop)
    (hF : ∀ ω, density w ω ≠ 0 → (F ω ↔ F' ω)) : delta w F e = delta w F' e := by
  unfold delta
  congr 1
  · exact prob_congr_support _ _ _ (fun ω hω => hF ω (density_pin_old_support w e True ω h1 hω))
  · exact prob_congr_support _ _ _ (fun ω hω => hF ω (density_pin_old_support w e False ω h0 hω))

lemma openPivot_congr_support (w : E → Prop → ℝ) (e : E) (h0 : w e False ≠ 0)
    (F F' : Set E → Prop) (hF : ∀ ω, density w ω ≠ 0 → (F ω ↔ F' ω))
    (ω : Set E) (hω : density w ω ≠ 0) : openPivot F e ω ↔ openPivot F' e ω := by
  unfold openPivot
  erw [hF ω hω,hF _ (density_force_nonzero w ω e False hω h0)]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ScoreCongrSupport
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
open FiniteProduct

variable {E R : Type*} [Fintype E] [DecidableEq E]

theorem score_congr_support (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ) (hf : LazyDFS.Fresh w p used)
    (F F' : Set E → Prop) (hF : ∀ ω, density w ω ≠ 0 → (F ω ↔ F' ω))
    (ω : Set E) (hω : density w ω ≠ 0) : T.score p F w ω = T.score p F' w ω := by
  induction T generalizing used w with
  | done r => rfl
  | ask e l r hl hr =>
    have hb := hf e hT.1
    have h0 : w e False ≠ 0 := by rw [hb.1]; exact (sub_pos.mpr hp.2).ne'
    have h1 : w e True ≠ 0 := by rw [hb.2]; exact hp.1.ne'
    have hd := delta_congr_support w e h0 h1 F F' hF
    have hP := openPivot_congr_support w e h0 F F' hF ω hω
    dsimp only [score]
    erw [hP,hd]
    congr 1
    by_cases he : ω e
    · rw [ite_eq_left he,ite_eq_left he]
      apply hr (insert e used) hT.2.2 (pin w e True) (LazyDFS.fresh_pin w p used hf e True)
      · intro ω' hω'
        exact hF ω' (density_pin_old_support w e True ω' h1 hω')
      · exact density_pin_of_support w ω e True hω (propext (iff_true_intro he))
    · rw [ite_eq_right he,ite_eq_right he]
      apply hl (insert e used) hT.2.1 (pin w e False) (LazyDFS.fresh_pin w p used hf e False)
      · intro ω' hω'
        exact hF ω' (density_pin_old_support w e False ω' h0 hω')
      · exact density_pin_of_support w ω e False hω (propext (iff_false_intro he))

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_Connects
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

lemma connects_mono (a t : V) : ∀ (ω ω' : Set E), ω ⊆ ω' → G.connects a t ω → G.connects a t ω' :=
  fun _ _ h => fun hr => hr.mono (G.openGraph_mono h)

lemma eraseBond_force (f : E) (a : V) (ω : Set E) (b : Prop) :
    (G.eraseBond f a).openGraph (Function.update ω f b) = (G.eraseBond f a).openGraph ω := by
  erw [G.eraseBond_openGraph,G.eraseBond_openGraph]
  congr 1
  ext e
  change (e ≠ f ∧ Function.update ω f b e) ↔ (e ≠ f ∧ e ∈ ω)
  by_cases h : e = f
  · subst e; simp
  · erw [Function.update_of_ne h]
    rfl

lemma connects_eq_wired_deleted (f : E) (a v z t : V) (ω : Set E)
    (hf : f ∈ ω) (he : G.ends f = s(v,z))
    (hv : ((G.eraseBond f a).openGraph ω).Reachable a v) :
    G.connects a t ω ↔ (G.eraseBond f a).wiredEvent a z t ω := by
  dsimp only [connects,wiredEvent]
  rw [G.openGraph_eq_eraseBond_sup f a v z ω hf he]
  exact Wiring.reachable_replace_tail _ a v z a t hv

lemma pivot_eq_deleted_joined (f : E) (a v z t : V) (ω : Set E)
    (hf : f ∈ ω) (he : G.ends f = s(v,z))
    (hv : ((G.eraseBond f a).openGraph ω).Reachable a v) :
    openPivot (G.connects a t) f ω ↔ (G.eraseBond f a).joinedPair a z t ω := by
  unfold openPivot
  rw [G.connects_eq_wired_deleted f a v z t ω hf he hv]
  have hclose : G.connects a t (Function.update ω f False) ↔
      ((G.eraseBond f a).openGraph ω).Reachable a t := by
    dsimp only [connects]
    erw [← G.eraseBond_openGraph_force_false]
  erw [hclose]
  exact (and_iff_right hf).trans ((G.eraseBond f a).earlier_pivot_iff a z t ω)

variable [Fintype E]

lemma deleted_joined_pin_eq (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (f : E) (h0 : w f False ≠ 0) (h1 : w f True ≠ 0) (a z t : V) :
    prob (pin w f True) ((G.eraseBond f a).joinedPair a z t) =
      prob (pin w f False) ((G.eraseBond f a).joinedPair a z t) := by
  rw [prob_pin_transport w hw f False True h0 h1]
  apply prob_congr
  intro ω
  dsimp [joinedPair,isolateThree]
  erw [G.eraseBond_force]

lemma delta_eq_deleted_joined (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (f : E) (h0 : w f False ≠ 0) (h1 : w f True ≠ 0) (a v z t : V)
    (he : G.ends f = s(v,z))
    (hv : ∀ ω, density (pin w f False) ω ≠ 0 → ((G.eraseBond f a).openGraph ω).Reachable a v) :
    delta w (G.connects a t) f = prob (pin w f True) ((G.eraseBond f a).joinedPair a z t) := by
  rw [G.deleted_joined_pin_eq w hw f h0 h1 a z t,
    delta_eq_pivotal w hw f h0 h1 _ (G.connects_mono a t)]
  apply prob_congr_support
  intro ω hω
  have hf0 := density_pin_support w f False ω hω
  have hf1 : Function.update ω f True f := by
    erw [Function.update_self]
    trivial
  have hv' : ((G.eraseBond f a).openGraph (Function.update ω f True)).Reachable a v := by
    erw [G.eraseBond_force]
    exact hv ω hω
  have hopen := G.connects_eq_wired_deleted f a v z t (Function.update ω f True) hf1 he hv'
  have hgraph : G.openGraph ω = (G.eraseBond f a).openGraph ω := by
    erw [G.eraseBond_openGraph_force_false]
    have hu : Function.update ω f False = ω := by
      erw [← hf0,Function.update_eq_self]
    erw [hu]
  erw [hopen]
  dsimp only [wiredEvent,connects]
  erw [G.eraseBond_force,hgraph]
  exact (G.eraseBond f a).earlier_pivot_iff a z t ω

end CriticalPercolation.BondGraph

namespace CriticalPercolation.Wiring
variable {V : Type*}

lemma pivot_component_avoids (H : SimpleGraph V) (A B : Set V) (w a z : V)
    (ha : a ∈ A) (hA : ∀ u ∈ A, H.Reachable w u)
    (hopen : ∃ t ∈ B, (H ⊔ SimpleGraph.edge a z).Reachable w t)
    (hclosed : ¬∃ t ∈ B, H.Reachable w t) :
    (∃ t ∈ B, H.Reachable z t) ∧ ∀ u ∈ A, ¬H.Reachable z u := by
  obtain ⟨t,ht,hwt⟩ := hopen
  have hzt : H.Reachable z t := by
    rcases (reachable_sup_edge H a z w t).mp hwt with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact (hclosed ⟨t,ht,h⟩).elim
    · exact h
    · exact (hclosed ⟨t,ht,(hA a ha).trans h⟩).elim
  refine ⟨⟨t,ht,hzt⟩,?_⟩
  intro u hu hzu
  exact hclosed ⟨t,ht,(hA u hu).trans (hzu.symm.trans hzt)⟩
end CriticalPercolation.Wiring

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

lemma openGraph_delete_eq_update (G : BondGraph V E) [DecidableEq E]
    (ω : E → Bool) (f : E) :
    G.openGraph {e | e ≠ f ∧ ω e = true} =
      G.openGraph {e | Function.update ω f false e = true} := by
  congr 1
  ext e
  by_cases he : e = f
  · subst e; simp
  · simp [he]

lemma openGraph_delete_sup (G : BondGraph V E) (ω : E → Bool)
    (f : E) (a z : V) (hf : ω f = true) (he : G.ends f = s(a,z)) :
    G.openGraph {e | ω e = true} =
      G.openGraph {e | e ≠ f ∧ ω e = true} ⊔ SimpleGraph.edge a z := by
  have hh : {e | ω e = true} = insert f {e | e ≠ f ∧ ω e = true} := by
    ext e
    by_cases h : e = f
    · subst e; simp [hf]
    · simp [h]
  rw [hh,openGraph_insert G _ _ _ _ he]
end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_PrefixState
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

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V]

theorem actual_pivot_no_older_reads (G : BondGraph V E)
    (order : List (Dart V E)) (ho : Exhaustive G order) (B : Set V)
    (fuel : ℕ) (st : State V E) (older : List (Dart V E)) (ω : E → Bool)
    (w a z : V) (f : E) (ha : a ∈ st.reached) (he : G.ends f = s(a,z))
    (hf : ω f = true) (hc : ReadConsistent G st ω)
    (hr : rank order (st.opened f z) (push G order z) ≤ fuel)
    (hA : ∀ u ∈ st.reached, (G.openGraph {e | e ≠ f ∧ ω e = true}).Reachable w u)
    (hopen : ∃ t ∈ B, (G.openGraph {e | ω e = true}).Reachable w t)
    (hclosed : ¬∃ t ∈ B, (G.openGraph {e | Function.update ω f false e = true}).Reachable w t) :
    (compile G order B fuel (st.opened f z) (push G order z++older)).reads ω =
      (compile G order B fuel (st.opened f z) (push G order z)).reads ω := by
  have hopen' := hopen
  rw [G.openGraph_delete_sup ω f a z hf he] at hopen'
  rw [← G.openGraph_delete_eq_update] at hclosed
  obtain ⟨ht,havoid⟩ := Wiring.pivot_component_avoids
    (G.openGraph {e | e ≠ f ∧ ω e = true}) (st.reached : Set V) B w a z ha hA hopen' hclosed
  apply phase_no_older_reads G (st.reached : Set V) order ho B fuel (st.opened f z)
    (push G order z) older ω (opened_phaseFrontier G order ho st f z)
    (readConsistent_opened G st ω hc ha he) hr
    (G.openGraph {e | e ≠ f ∧ ω e = true})
    (SimpleGraph.fromEdgeSet_mono (Set.image_mono (fun _ h => h.2))) z
    (Finset.mem_insert_self _ _) havoid ht

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [DecidableEq V] [DecidableEq E] in
lemma prefixState_initial (G : BondGraph V E) (a : V) (w : E → Prop → ℝ) :
    PrefixState G a (initial a) w := by
  refine ⟨Finset.mem_singleton_self _,?_⟩
  intro ω _
  constructor
  · intro v hv
    have hv' : v = a := Finset.mem_singleton.mp hv
    subst v
    exact .refl _
  · intro e he
    exact (Finset.notMem_empty e he).elim

omit [DecidableEq V] in
lemma prefixState_closed (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) (hs : PrefixState G a st w) (e : E) (h0 : w e False ≠ 0) :
    PrefixState G a (st.closed e) (pin w e False) := by
  refine ⟨hs.1,?_⟩
  intro ω hω
  have hold := hs.2 ω (density_pin_old_support w e False ω h0 hω)
  constructor
  · intro v hv
    apply (hold.1 v hv).mono
    exact G.openGraph_mono (fun j hj => ⟨Finset.mem_insert_of_mem hj.1,hj.2⟩)
  · apply readConsistent_closed G st (fun j => decide (ω j)) hold.2
    have hh := density_pin_support w e False ω hω
    simp only [hh,decide_false]

lemma prefixState_opened (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) (hs : PrefixState G a st w) (e : E) (v z : V)
    (hv : v ∈ st.reached) (he : G.ends e = s(v,z)) (h1 : w e True ≠ 0) :
    PrefixState G a (st.opened e z) (pin w e True) := by
  refine ⟨Finset.mem_insert_of_mem hs.1,?_⟩
  intro ω hω
  have hold := hs.2 ω (density_pin_old_support w e True ω h1 hω)
  have hle : G.openGraph {j | j ∈ st.read ∧ j ∈ ω} ≤
      G.openGraph {j | j ∈ (st.opened e z).read ∧ j ∈ ω} :=
    G.openGraph_mono (fun j hj => ⟨Finset.mem_insert_of_mem hj.1,hj.2⟩)
  constructor
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · apply ((hold.1 v hv).mono hle).trans
      apply prop_openEdge_reachable G {j | j ∈ insert e st.read ∧ j ∈ ω} _ he
      exact ⟨Finset.mem_insert_self _ _,of_eq_true (density_pin_support w e True ω hω)⟩
    · exact (hold.1 u hu).mono hle
  · exact readConsistent_opened G st (fun j => decide (ω j)) hold.2 hv he

omit [DecidableEq V] [DecidableEq E] in
lemma prefixState_deleted (G : BondGraph V E) (a : V) (st : State V E)
    (w : E → Prop → ℝ) (hs : PrefixState G a st w) (f : E) (hf : f ∉ st.read)
    (ω : Set E) (hω : density w ω ≠ 0) :
    ∀ v ∈ st.reached, ((G.eraseBond f a).openGraph ω).Reachable a v := by
  intro v hv
  exact ((hs.2 ω hω).1 v hv).mono (G.knownGraph_le_eraseBond st.read f a ω hf)

variable [Fintype V]

theorem future_pair_bound (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (a t v z : V) (f : E)
    (st : State V E) (older : List (Dart V E)) (fuel : ℕ)
    (hv : v ∈ st.reached) (hz : z ∉ st.reached) (ht : t ∉ st.reached) (hzt : z ≠ t)
    (hf : f ∉ st.read) (he : G.ends f = s(v,z))
    (hr : rank order (st.opened f z) (push G order z) ≤ fuel)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (fresh : Fresh w p st.read) (hs : PrefixState G a st w) :
    expect (pin w f True) (fun ω => if openPivot (G.connects a t) f ω then
      (compile G order {t} fuel (st.opened f z) (push G order z++older)).score p
        (G.connects a t) (pin w f True) ω else 0) ≤ delta w (G.connects a t) f := by
  have hb := fresh f hf
  have h0 : w f False ≠ 0 := by rw [hb.1]; exact (sub_pos.mpr hp.2).ne'
  have h1 : w f True ≠ 0 := by rw [hb.2]; exact hp.1.ne'
  have haz : a ≠ z := fun h => hz (h ▸ hs.1)
  have hat : a ≠ t := fun h => ht (h ▸ hs.1)
  have hA : ∀ ω : Set E, density w ω ≠ 0 →
      ∀ u ∈ st.reached, ((G.eraseBond f a).openGraph ω).Reachable a u :=
    prefixState_deleted G a st w hs f hf
  have hd := G.delta_eq_deleted_joined w hw f h0 h1 a v z t he
    (fun ω hω => hA ω (density_pin_old_support w f False ω h0 hω) v hv)
  rw [hd]
  have hphase := young_phase_score_bound_bs G order {t} f a z t haz hat hzt hp fuel (st.opened f z)
    (Finset.mem_insert_self _ _) (pin w f True) (pin_normalized w hw f True)
    (pin_nonneg w hn f True) (fresh_pin w p st.read fresh f True)
  apply le_trans (le_of_eq ?_) hphase
  apply expect_congr_support
  intro ω hω
  change Set E at ω
  have hωold := density_pin_old_support w f True ω h1 hω
  have hopenf : ω f := of_eq_true (density_pin_support w f True ω hω)
  have hP := G.pivot_eq_deleted_joined f a v z t ω hopenf he (hA ω hωold v hv)
  erw [hP]
  by_cases hR : (G.eraseBond f a).joinedPair a z t ω
  · rw [ite_eq_left hR,ite_eq_left hR]
    have hactual := hP.mpr hR
    have hconn : ∀ η : Set E, density (pin w f True) η ≠ 0 →
        (G.connects a t η ↔ (G.eraseBond f a).wiredEvent a z t η) := by
      intro η hη
      exact G.connects_eq_wired_deleted f a v z t η
        (of_eq_true (density_pin_support w f True η hη)) he
        (hA η (density_pin_old_support w f True η h1 hη) v hv)
    apply Eq.trans (SearchTree.score_eq_of_reads_eq _ _ p (G.connects a t) (pin w f True) ω ?_)
      (SearchTree.score_congr_support _ (st.opened f z).read
        (compile_valid G order {t} fuel (st.opened f z) (push G order z)) hp
        (pin w f True) (fresh_pin w p st.read fresh f True) _ _ hconn ω hω)
    apply actual_pivot_no_older_reads G order ho {t} fuel st older (fun e => decide (ω e))
      a v z f hv he (by simp [hopenf]) (hs.2 ω hωold).2 hr
    · intro u hu
      have hh := hA ω hωold u hu
      erw [G.eraseBond_openGraph] at hh
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      simp only [decide_eq_true_eq]
      rfl
    · refine ⟨t,Set.mem_singleton _,?_⟩
      convert hactual.2.1 using 1
      all_goals try with_reducible_and_instances rfl
      simp only [BondGraph.connects,decide_eq_true_eq]
      rfl
    · rintro ⟨u,hu,hau⟩
      have hu' : u = t := Set.mem_singleton_iff.mp hu
      subst u
      apply hactual.2.2
      have hsets : {e | Function.update (fun j => decide (ω j)) f false e = true} =
          (Function.update ω f False : Set E) := by
        ext e
        change (Function.update (fun j => decide (ω j)) f false e = true) ↔ Function.update ω f False e
        by_cases hf' : e = f
        · subst e
          erw [Function.update_self,Function.update_self]
          simp
        · erw [Function.update_of_ne hf',Function.update_of_ne hf']
          simp only [decide_eq_true_eq]
      erw [hsets] at hau
      unfold BondGraph.connects
      convert hau using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      funext e
      dsimp only [Function.update]
      split_ifs <;> rfl
  · rw [ite_eq_right hR,ite_eq_right hR]

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

lemma prob_openPivot_pin (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    prob (pin w e True) (openPivot F e) = delta w F e := by
  rw [prob_pin_transport w hw e False True h0 h1,
    delta_eq_pivotal w hw e h0 h1 F hF]
  apply prob_congr_support
  intro ω hω
  erw [openPivot_force_true]
  have hh := density_pin_support w e False ω hω
  have heq : Function.update ω e False = ω := by
    erw [← hh,Function.update_eq_self]
  erw [heq]

lemma prob_openPivot (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (h0 : w e False ≠ 0) (h1 : w e True ≠ 0)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    prob w (openPivot F e) = w e True * delta w F e := by
  rw [prob_requires_bit w e True _ (fun _ h => propext (iff_true_intro h.1)),
    prob_openPivot_pin w hw e h0 h1 F hF]

lemma variance_eq_potential (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (F : Set E → Prop) : variance w F = potential w (fun _ => True) F := by
  simp only [variance,potential,prob_true w hw,div_one]

lemma variance_nonneg (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : 0 ≤ variance w F := by
  rw [variance_eq_potential w hw]
  exact potential_nonneg w hn _ _ (fun _ _ => trivial)

lemma variance_le_one (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) : variance w F ≤ 1 := by
  exact (sub_le_self _ (sq_nonneg _)).trans (prob_le_one w hw hn F)

lemma variance_split (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (F : Set E → Prop) (e : E)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (h0 : w e False = 1-p) (h1 : w e True = p) :
    variance w F = p*(1-p)*(delta w F e)^2 +
      (1-p)*variance (pin w e False) F + p*variance (pin w e True) F := by
  have hh := potential_split w hn e (fun _ => True) F (fun _ _ => trivial) hp.1 hp.2 h0 h1
  simp only [prob_true _ (pin_normalized w hw e False),
    prob_true _ (pin_normalized w hw e True),mul_one,div_one,sub_add_cancel,div_one,
    ← variance_eq_potential w hw,
    ← variance_eq_potential _ (pin_normalized w hw e False),
    ← variance_eq_potential _ (pin_normalized w hw e True)] at hh
  dsimp only [delta]
  linarith

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ScoreMeanStep
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
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma score_mean_step (e : E) (l r : SearchTree E R) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (h0 : w e False = 1-p) (h1 : w e True = p)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    expect w ((.ask e l r : SearchTree E R).score p F w) =
      p*(1-p)*(delta w F e)^2 + (1-p)*expect (pin w e False) (l.score p F (pin w e False)) +
      p*expect (pin w e True) (r.score p F (pin w e True)) := by
  have heq : (.ask e l r : SearchTree E R).score p F w =
      fun ω => (1-p)*delta w F e*(if openPivot F e ω then (1:ℝ) else 0) +
        if ω e then r.score p F (pin w e True) ω else l.score p F (pin w e False) ω := by
    funext ω
    by_cases h : openPivot F e ω <;> simp [score,h]
  rw [heq]
  erw [expect_add,expect_const_mul,expect_prop_ite,h0,h1]
  change (1-p)*delta w F e * prob w (openPivot F e) + _ = _
  rw [prob_openPivot w hw e (by rw [h0]; exact (sub_pos.mpr hp.2).ne')
    (by rw [h1]; exact hp.1.ne') F hF,h1]
  ring

variable [DecidableEq E]

theorem score_mean_le_variance (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : LazyDFS.Fresh w p used) (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    expect w (T.score p F w) ≤ variance w F := by
  induction T generalizing used w with
  | done r => exact (expect_const w hw 0).le.trans (variance_nonneg w hw hn F)
  | ask e l r hl hr =>
    have he := hf e hT.1
    have hlb := hl (insert e used) hT.2.1 (pin w e False) (pin_normalized w hw e False)
      (pin_nonneg w hn e False) (LazyDFS.fresh_pin w p used hf e False)
    have hrb := hr (insert e used) hT.2.2 (pin w e True) (pin_normalized w hw e True)
      (pin_nonneg w hn e True) (LazyDFS.fresh_pin w p used hf e True)
    rw [score_mean_step e l r hp w hw he.1 he.2 F hF,
      variance_split w hw hn F e hp he.1 he.2]
    have hlb' := mul_le_mul_of_nonneg_left hlb (sub_pos.mpr hp.2).le
    have hrb' := mul_le_mul_of_nonneg_left hrb hp.1.le
    linarith

end CriticalPercolation.SearchTree

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma pivotal_contribution_mean (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (h0 : w e False = 1-p) (h1 : w e True = p)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t) :
    expect w (fun ω => if openPivot F e ω then (1-p)*delta w F e else 0) =
      p*(1-p)*(delta w F e)^2 := by
  have heq : (fun ω => if openPivot F e ω then (1-p)*delta w F e else 0) =
      (fun ω => (1-p)*delta w F e*(if openPivot F e ω then (1:ℝ) else 0)) := by
    funext ω
    split_ifs <;> simp
  erw [heq,expect_const_mul]
  change (1-p)*delta w F e*prob w (openPivot F e) = _
  rw [prob_openPivot w hw e (by rw [h0]; exact (sub_pos.mpr hp.2).ne')
    (by rw [h1]; exact hp.1.ne') F hF,h1]
  ring

lemma score_second_step (e : E) (l r : SearchTree E R) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (h0 : w e False = 1-p) (h1 : w e True = p)
    (F : Set E → Prop) (hF : ∀ s t, s ⊆ t → F s → F t)
    (hpair : expect (pin w e True) (fun ω => if openPivot F e ω then
      r.score p F (pin w e True) ω else 0) ≤ delta w F e) :
    expect w (fun ω => ((.ask e l r : SearchTree E R).score p F w ω)^2) ≤
      3*(p*(1-p)*(delta w F e)^2) +
      (1-p)*expect (pin w e False) (fun ω => (l.score p F (pin w e False) ω)^2) +
      p*expect (pin w e True) (fun ω => (r.score p F (pin w e True) ω)^2) := by
  have hd := delta_unit w hw hn e (by rw [h0]; exact (sub_pos.mpr hp.2).ne')
    (by rw [h1]; exact hp.1.ne') F hF
  have hc0 : 0 ≤ (1-p)*delta w F e := mul_nonneg (sub_pos.mpr hp.2).le hd.1
  have hc1 : (1-p)*delta w F e ≤ 1 :=
    (mul_le_mul_of_nonneg_left hd.2 (sub_pos.mpr hp.2).le).trans (by linarith [hp.1])
  have hc2 : ((1-p)*delta w F e)^2 ≤ (1-p)*delta w F e := by nlinarith
  have hbound := expect_mono hn (fun ω => show
      ((.ask e l r : SearchTree E R).score p F w ω)^2 ≤
      (if openPivot F e ω then (1-p)*delta w F e else 0) +
      (if ω e then (r.score p F (pin w e True) ω)^2 else (l.score p F (pin w e False) ω)^2) +
      2*((1-p)*delta w F e) *
        (if ω e then (if openPivot F e ω then r.score p F (pin w e True) ω else 0) else 0) from by
    by_cases hP : openPivot F e ω
    · have he := hP.1
      simp only [score,hP,he,↓reduceIte]
      nlinarith
    · by_cases he : ω e <;> simp [score,hP,he])
  erw [expect_add,expect_add,pivotal_contribution_mean w hw e hp h0 h1 F hF,
    expect_prop_ite,expect_const_mul,expect_prop_ite,h0,h1,
    expect_const _ (pin_normalized w hw e False) 0,mul_zero,add_zero] at hbound
  have hmult := mul_le_mul_of_nonneg_left hpair (mul_nonneg (by positivity : 0 ≤ 2*((1-p)*delta w F e)) hp.1.le)
  nlinarith [hbound,hmult]

end CriticalPercolation.SearchTree

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_CompileStop
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

omit [Fintype V] [Fintype E] in
lemma compile_stop (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (hh : ∃ v ∈ st.reached, v ∈ B) :
    compile G order B fuel st stack = .done st := by
  cases fuel with
  | zero => rfl
  | succ n => rw [compile.eq_def]; exact ite_eq_left hh

theorem compile_score_second (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (a t : V) (fuel : ℕ) (st : State V E)
    (stack : List (Dart V E)) (hrank : rank order st stack ≤ fuel)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (fresh : Fresh w p st.read) (hs : PrefixState G a st w) :
    expect w (fun ω => ((compile G order {t} fuel st stack).score p (G.connects a t) w ω)^2) ≤
      3*expect w ((compile G order {t} fuel st stack).score p (G.connects a t) w) := by
  induction fuel generalizing st stack w with
  | zero =>
    change expect w (fun _ : E → Prop => (0:ℝ)^2) ≤ 3*expect w (fun _ : E → Prop => (0:ℝ))
    simp only [zero_pow (by omega : 2 ≠ 0),expect_const w hw 0,mul_zero,le_refl]
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · change expect w (fun _ : E → Prop => (0:ℝ)^2) ≤ 3*expect w (fun _ : E → Prop => (0:ℝ))
      simp only [zero_pow (by omega : 2 ≠ 0),expect_const w hw 0,mul_zero,le_refl]
    · cases stack with
      | nil =>
        change expect w (fun _ : E → Prop => (0:ℝ)^2) ≤ 3*expect w (fun _ : E → Prop => (0:ℝ))
        simp only [zero_pow (by omega : 2 ≠ 0),expect_const w hw 0,mul_zero,le_refl]
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · apply ih st rest (by have := rank_pop order st d rest; omega) w hw hn fresh hs
        · have hz : d.2.2 ∉ st.reached := fun hz => hd (Or.inl hz)
          have hf : d.2.1 ∉ st.read := fun hf => hd (Or.inr (Or.inl hf))
          have hv : d.1 ∈ st.reached := by tauto
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by tauto
          have ht : t ∉ st.reached := fun ht => hh ⟨t,ht,Set.mem_singleton t⟩
          have hb := fresh d.2.1 hf
          have h0 : w d.2.1 False ≠ 0 := by rw [hb.1]; exact (sub_pos.mpr hp.2).ne'
          have h1 : w d.2.1 True ≠ 0 := by rw [hb.2]; exact hp.1.ne'
          have hrc : rank order (st.closed d.2.1) rest ≤ n := by
            have := rank_closed order st d rest
            omega
          have hro : rank order (st.opened d.2.1 d.2.2) (push G order d.2.2++rest) ≤ n := by
            have := rank_opened G order st d rest hz
            omega
          have hrp : rank order (st.opened d.2.1 d.2.2) (push G order d.2.2) ≤ n := by
            unfold rank at hro ⊢
            simp only [List.length_append] at hro
            omega
          have hpair : expect (pin w d.2.1 True) (fun ω =>
              if openPivot (G.connects a t) d.2.1 ω then
                (compile G order {t} n (st.opened d.2.1 d.2.2) (push G order d.2.2++rest)).score p
                  (G.connects a t) (pin w d.2.1 True) ω else 0) ≤ delta w (G.connects a t) d.2.1 := by
            by_cases hzt : d.2.2 = t
            · have hstop := compile_stop G order {t} n (st.opened d.2.1 d.2.2)
                (push G order d.2.2++rest) ⟨t,by simp [State.opened,hzt],Set.mem_singleton t⟩
              simp only [hstop,score,ite_self,expect_const _ (pin_normalized w hw d.2.1 True) 0]
              exact (delta_unit w hw hn d.2.1 h0 h1 _ (G.connects_mono a t)).1
            · exact future_pair_bound G order ho a t d.1 d.2.2 d.2.1 st rest n
                hv hz ht hzt hf he hrp hp w hw hn fresh hs
          have hstep := score_second_step d.2.1
            (compile G order {t} n (st.closed d.2.1) rest)
            (compile G order {t} n (st.opened d.2.1 d.2.2) (push G order d.2.2++rest))
            hp w hw hn hb.1 hb.2 (G.connects a t) (G.connects_mono a t) hpair
          have hc := ih (st.closed d.2.1) rest hrc (pin w d.2.1 False)
            (pin_normalized w hw d.2.1 False) (pin_nonneg w hn d.2.1 False)
            (fresh_pin w p st.read fresh d.2.1 False) (prefixState_closed G a st w hs d.2.1 h0)
          have ho' := ih (st.opened d.2.1 d.2.2) (push G order d.2.2++rest) hro (pin w d.2.1 True)
            (pin_normalized w hw d.2.1 True) (pin_nonneg w hn d.2.1 True)
            (fresh_pin w p st.read fresh d.2.1 True) (prefixState_opened G a st w hs d.2.1 d.1 d.2.2 hv he h1)
          rw [score_mean_step _ _ _ hp w hw hb.1 hb.2 _ (G.connects_mono a t)]
          have hc' := mul_le_mul_of_nonneg_left hc (sub_pos.mpr hp.2).le
          have ho'' := mul_le_mul_of_nonneg_left ho' hp.1.le
          linarith

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem search_pivotal_moments (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (a t : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect w ((search G order a {t}).score p (G.connects a t) w) ≤ 1 ∧
      expect w (fun ω => ((search G order a {t}).score p (G.connects a t) w ω)^2) ≤ 3 := by
  have hw : ∀ e, ∑ b, w e b = 1 := by
    intro e
    simp [Fintype.univ_Prop,h0,h1]
  have hn : ∀ e b, 0 ≤ w e b := by
    intro e b
    by_cases hb : b
    · have : b = True := propext (iff_true_intro hb)
      rw [this,h1]; exact hp.1.le
    · have : b = False := propext (iff_false_intro hb)
      rw [this,h0]; exact (sub_pos.mpr hp.2).le
  have hf : Fresh w p (initial (E := E) a).read := fun e _ => ⟨h0 e,h1 e⟩
  have hm := score_mean_le_variance (search G order a {t}) (initial a).read
    (compile_valid G order {t} _ _ _) hp w hw hn hf _ (G.connects_mono a t)
  have hmean := hm.trans (variance_le_one w hw hn _)
  refine ⟨hmean,?_⟩
  have hs := compile_score_second G order ho a t _ (initial a) (push G order a)
    le_rfl hp w hw hn hf (prefixState_initial G a w)
  change _ ≤ 3*expect w ((search G order a {t}).score p (G.connects a t) w) at hs
  exact hs.trans (by linarith)

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_MapVertices
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
variable {V E U : Type*} (G : BondGraph V E)

lemma mapVertices_adj (f : V → U) (ω : Set E) (x y : U) :
    ((G.mapVertices f).openGraph ω).Adj x y ↔
      ∃ a b, (G.openGraph ω).Adj a b ∧ f a = x ∧ f b = y ∧ x ≠ y := by
  constructor
  · rintro ⟨⟨e,he,hends⟩,hne⟩
    obtain ⟨a,b,hab⟩ : ∃ a b, G.ends e = s(a,b) :=
      Sym2.exists.mp ⟨G.ends e,rfl⟩
    change Sym2.map f (G.ends e) = s(x,y) at hends
    rw [hab,Sym2.map_mk] at hends
    rcases Sym2.eq_iff.mp hends with ⟨hx,hy⟩ | ⟨hy,hx⟩
    · refine ⟨a,b,?_,hx,hy,hne⟩
      exact ⟨⟨e,he,hab⟩,fun hab' => hne (hx.symm.trans ((congrArg f hab').trans hy))⟩
    · refine ⟨b,a,?_,hx,hy,hne⟩
      exact ⟨⟨e,he,hab.trans Sym2.eq_swap⟩,fun hab' => hne (hx.symm.trans ((congrArg f hab').trans hy))⟩
  · rintro ⟨a,b,⟨⟨e,he,hab⟩,_⟩,hx,hy,hne⟩
    refine ⟨⟨e,he,?_⟩,hne⟩
    change Sym2.map f (G.ends e) = s(x,y)
    rw [hab,Sym2.map_mk,hx,hy]

lemma mapVertices_reachable (f : V → U) (ω : Set E) {a b : V}
    (hab : (G.openGraph ω).Reachable a b) :
    ((G.mapVertices f).openGraph ω).Reachable (f a) (f b) := by
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen a b).mp hab
  clear hab
  induction hr with
  | refl => exact .refl _
  | @tail b c _ hbc ih =>
    apply ih.trans
    by_cases h : f b = f c
    · rw [h]
    · exact ((G.mapVertices_adj f ω _ _).mpr ⟨b,c,hbc,rfl,rfl,h⟩).reachable

open scoped Classical

omit G in
lemma collapseTarget_eq_none (B : Set V) (v : V) : collapseTarget B v = none ↔ v ∈ B := by
  by_cases h : v ∈ B <;> simp [collapseTarget,h]

omit G in
lemma collapseTarget_injective_off (B : Set V) {v u : V} (hu : u ∉ B)
    (h : collapseTarget B v = collapseTarget B u) : v = u := by
  by_cases hv : v ∈ B
  · simp [collapseTarget,hv,hu] at h
  · simpa only [collapseTarget,ite_eq_right hv,ite_eq_right hu,Option.some.injEq] using h

theorem wireTargets_connection (B : Set V) (ω : Set E) (a : V) :
    ((G.wireTargets B).openGraph ω).Reachable (collapseTarget B a) none ↔
      ∃ b ∈ B, (G.openGraph ω).Reachable a b := by
  constructor
  · intro hr
    by_cases ha : a ∈ B
    · exact ⟨a,ha,.refl _⟩
    have hg := (((G.wireTargets B).openGraph ω).reachable_iff_reflTransGen _ _).mp hr.symm
    have hreach : ∀ {y : Option V},
        Relation.ReflTransGen ((G.wireTargets B).openGraph ω).Adj none y →
        ∀ v, collapseTarget B v = y → v ∉ B → ∃ b ∈ B, (G.openGraph ω).Reachable v b := by
      intro y hpath
      induction hpath with
      | refl =>
        intro v hv hn
        exact (hn ((collapseTarget_eq_none B v).mp hv)).elim
      | @tail y z _ hyz ih =>
        intro v hv hn
        obtain ⟨u,u',huu',hu,hu',_⟩ := (G.mapVertices_adj (collapseTarget B) ω y z).mp hyz
        have hu'v : u' = v := collapseTarget_injective_off B hn (hu'.trans hv.symm)
        subst u'
        by_cases huB : u ∈ B
        · exact ⟨u,huB,huu'.symm.reachable⟩
        · obtain ⟨b,hb,hub⟩ := ih u hu huB
          exact ⟨b,hb,huu'.symm.reachable.trans hub⟩
    exact hreach hg a rfl ha
  · rintro ⟨b,hb,hab⟩
    have hh := G.mapVertices_reachable (collapseTarget B) ω hab
    rw [(collapseTarget_eq_none B b).mpr hb] at hh
    exact hh

end CriticalPercolation.BondGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_TargetSearch
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
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem targetSearch_moments (G : BondGraph V E) (B : Set V)
    (order : List (Dart (Option V) E)) (ho : Exhaustive (G.wireTargets B) order)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    expect w ((targetSearch G B order a).score p F w) ≤ 1 ∧
      expect w (fun ω => ((targetSearch G B order a).score p F w ω)^2) ≤ 3 := by
  have hh := search_pivotal_moments (G.wireTargets B) order ho (collapseTarget B a) none hp w h0 h1
  have hF : (G.wireTargets B).connects (collapseTarget B a) none =
      (fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b) := by
    funext ω
    exact propext (G.wireTargets_connection B ω a)
  rw [hF] at hh
  exact hh

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma target_hit_map (B : Set V) (st : State V E) :
    (∃ v ∈ (mapState B st).reached, v ∈ ({none} : Set (Option V))) ↔
      ∃ v ∈ st.reached, v ∈ B := by
  constructor
  · rintro ⟨v,hv,hvt⟩
    have hvn : v = none := Set.mem_singleton_iff.mp hvt
    obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hv
    exact ⟨u,hu,(collapseTarget_eq_none B u).mp (heq.trans hvn)⟩
  · rintro ⟨v,hv,hvB⟩
    refine ⟨none,Finset.mem_image.mpr ⟨v,hv,?_⟩,Set.mem_singleton none⟩
    exact (collapseTarget_eq_none B v).mpr hvB

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma mapState_mem (B : Set V) (st : State V E)
    (hh : ¬∃ v ∈ st.reached, v ∈ B) (v : V) :
    collapseTarget B v ∈ (mapState B st).reached ↔ v ∈ st.reached := by
  constructor
  · intro hv
    obtain ⟨u,hu,heq⟩ := Finset.mem_image.mp hv
    have huB : u ∉ B := fun hb => hh ⟨u,hu,hb⟩
    have huv := collapseTarget_injective_off B huB heq.symm
    exact huv ▸ hu
  · intro hv
    exact Finset.mem_image.mpr ⟨v,hv,rfl⟩

omit [Fintype V] [Fintype E] in
lemma mapState_opened (B : Set V) (st : State V E) (e : E) (v : V) :
    mapState B (st.opened e v) = (mapState B st).opened e (collapseTarget B v) := by
  simp [mapState,State.opened]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma mapDart_ends (G : BondGraph V E) (B : Set V) (d : Dart V E)
    (hd : G.ends d.2.1 = s(d.1,d.2.2)) :
    (G.wireTargets B).ends (mapDart B d).2.1 = s((mapDart B d).1,(mapDart B d).2.2) := by
  change Sym2.map (collapseTarget B) (G.ends d.2.1) = _
  rw [hd]; rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma push_mapTarget (G : BondGraph V E) (B : Set V) (order : List (Dart V E))
    (hg : GoodDarts G order) (v : V) (hv : v ∉ B) :
    (push G order v).map (mapDart B) =
      push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B v) := by
  induction order with
  | nil => rfl
  | cons d rest ih =>
    have hd := hg d (List.mem_cons_self ..)
    have hd' := mapDart_ends G B d hd
    have hrest : GoodDarts G rest := fun d h => hg d (List.mem_cons_of_mem _ h)
    have heq : collapseTarget B d.1 = collapseTarget B v ↔ d.1 = v :=
      ⟨collapseTarget_injective_off B hv,fun h => congrArg (collapseTarget B) h⟩
    simp only [push,List.filter_cons,List.map_cons] at ih ⊢
    change (List.map (mapDart B) (if decide (d.1 = v ∧ G.ends d.2.1 = s(d.1,d.2.2)) then
      d :: rest.filter _ else rest.filter _)) = _
    simp only [hd,hd',and_true]
    change List.map (mapDart B) (if decide (d.1 = v) then d :: rest.filter _ else rest.filter _) =
      (if decide (collapseTarget B d.1 = collapseTarget B v) then
        mapDart B d :: (rest.map (mapDart B)).filter _ else (rest.map (mapDart B)).filter _)
    simp only [heq]
    split_ifs <;> simp only [List.map_cons,ih hrest]

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_CompileEmptyReads
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
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

lemma compile_empty_reads (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel : ℕ) (st : State V E) (ω : E → Bool) :
    (compile G order B fuel st []).reads ω = [] := by
  cases fuel with
  | zero => rfl
  | succ n =>
    rw [compile.eq_def]
    dsimp only
    split_ifs <;> rfl

variable [Fintype V]

theorem compile_reads_rank_independent (G : BondGraph V E) (order : List (Dart V E)) (B : Set V)
    (fuel fuel' : ℕ) (st : State V E) (stack : List (Dart V E)) (ω : E → Bool)
    (hr : rank order st stack ≤ fuel) (hr' : rank order st stack ≤ fuel') :
    (compile G order B fuel st stack).reads ω = (compile G order B fuel' st stack).reads ω := by
  induction fuel generalizing fuel' st stack with
  | zero =>
    have hnil : stack = [] := by
      have : stack.length = 0 := by unfold rank at hr; omega
      exact List.length_eq_zero_iff.mp this
    subst stack
    rw [compile_empty_reads,compile_empty_reads]
  | succ n ih =>
    cases fuel' with
    | zero =>
      have hnil : stack = [] := by
        have : stack.length = 0 := by unfold rank at hr'; omega
        exact List.length_eq_zero_iff.mp this
      subst stack
      rw [compile_empty_reads,compile_empty_reads]
    | succ m =>
      rw [compile.eq_def,compile.eq_def]
      dsimp only
      split_ifs with hh
      · rfl
      · cases stack with
        | nil => rfl
        | cons d rest =>
          dsimp only
          split_ifs with hd
          · have hpop := rank_pop order st d rest
            exact ih m st rest (by omega) (by omega)
          · rw [reads,reads]
            congr 1
            split_ifs with hω
            · have hopen := rank_opened G order st d rest (fun h => hd (Or.inl h))
              exact ih m _ _ (by omega) (by omega)
            · have hclosed := rank_closed order st d rest
              exact ih m _ _ (by omega) (by omega)

omit [Fintype V] [DecidableEq E] in
lemma push_goodDarts (G : BondGraph V E) (order : List (Dart V E)) (v : V) :
    GoodDarts G (push G order v) := by
  intro d hd
  have hh := (List.mem_filter.mp hd).2
  exact (of_decide_eq_true hh).2

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma goodDarts_append (G : BondGraph V E) (l r : List (Dart V E))
    (hl : GoodDarts G l) (hr : GoodDarts G r) : GoodDarts G (l++r) := by
  intro d hd
  exact (List.mem_append.mp hd).elim (hl d) (hr d)

omit [Fintype V] in

theorem compile_reads_targetWiring (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (fuel : ℕ)
    (st : State V E) (stack : List (Dart V E)) (hs : GoodDarts G stack)
    (ω : E → Bool) :
    (compile G order B fuel st stack).reads ω =
      (compile (G.wireTargets B) (order.map (mapDart B)) {none} fuel (mapState B st)
        (stack.map (mapDart B))).reads ω := by
  induction fuel generalizing st stack with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def,compile.eq_def]
    dsimp only
    simp only [target_hit_map]
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
      | cons d rest =>
        have hd := hs d (List.mem_cons_self ..)
        have hd' := mapDart_ends G B d hd
        have hr : GoodDarts G rest := fun d h => hs d (List.mem_cons_of_mem _ h)
        simp only [List.map_cons]
        have hmem := mapState_mem B st hh
        have hRead : (mapState B st).read = st.read := rfl
        have hEnds : (G.wireTargets B).ends d.2.1 =
            s(collapseTarget B d.1, collapseTarget B d.2.2) := hd'
        simp only [mapDart, hRead, hEnds, hd, ne_eq, not_true_eq_false, or_false, hmem]
        split_ifs with hbad
        · exact ih st rest hr
        · rw [reads,reads]
          congr 1
          split_ifs with hbit
          · by_cases hzB : d.2.2 ∈ B
            · have hstop := compile_stop G order B n (st.opened d.2.1 d.2.2)
                (push G order d.2.2++rest) ⟨d.2.2,Finset.mem_insert_self _ _,hzB⟩
              have hzNone := (collapseTarget_eq_none B d.2.2).mpr hzB
              have hstop' := compile_stop (G.wireTargets B) (order.map (mapDart B)) {none} n
                ((mapState B st).opened d.2.1 (collapseTarget B d.2.2))
                (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B d.2.2) ++
                  rest.map (mapDart B))
                ⟨none,by simp [State.opened,hzNone],Set.mem_singleton none⟩
              rw [hstop,hstop']; rfl
            · have hnew := ih (st.opened d.2.1 d.2.2) (push G order d.2.2++rest)
                (goodDarts_append G _ _ (push_goodDarts G order d.2.2) hr)
              rw [mapState_opened,List.map_append,push_mapTarget G B order horder d.2.2 hzB] at hnew
              exact hnew
          · exact ih (st.closed d.2.1) rest hr

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedFresh
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
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma exhaustive_mapTarget (G : BondGraph V E) (B : Set V) (order : List (Dart V E))
    (ho : Exhaustive G order) : Exhaustive (G.wireTargets B) (order.map (mapDart B)) := by
  intro v e t he
  obtain ⟨a,b,hab⟩ : ∃ a b, G.ends e = s(a,b) := Sym2.exists.mp ⟨G.ends e,rfl⟩
  change Sym2.map (collapseTarget B) (G.ends e) = s(v,t) at he
  rw [hab,Sym2.map_mk] at he
  rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact List.mem_map.mpr ⟨(a,e,b),ho a e b hab,by simp only [mapDart,ha,hb]⟩
  · exact List.mem_map.mpr ⟨(b,e,a),ho b e a (hab.trans Sym2.eq_swap),
      by simp only [mapDart,ha,hb]⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma mapState_initial (B : Set V) (a : V) :
    mapState (E := E) B (initial a) = initial (collapseTarget B a) := by
  simp [mapState,initial]

omit [Fintype E] in

theorem search_reads_targetWiring (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (a : V) (ω : E → Bool) :
    (search G order a B).reads ω =
      (search (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a) {none}).reads ω := by
  by_cases ha : a ∈ B
  · have hs := compile_stop G order B (rank order (initial a) (push G order a))
      (initial a) (push G order a) ⟨a,Finset.mem_singleton_self _,ha⟩
    have hn := (collapseTarget_eq_none B a).mpr ha
    have hs' := compile_stop (G.wireTargets B) (order.map (mapDart B)) {none}
      (rank (order.map (mapDart B)) (initial (collapseTarget B a))
        (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a)))
      (initial (collapseTarget B a))
      (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a))
      ⟨collapseTarget B a,Finset.mem_singleton_self _,by simp only [Set.mem_singleton_iff,hn]⟩
    unfold search
    rw [hs,hs']; rfl
  · let r := rank order (initial (E := E) a) (push G order a)
    let r' := rank (order.map (mapDart B)) (initial (E := E) (collapseTarget B a))
      (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a))
    have h := compile_reads_targetWiring G B order horder (max r r')
      (initial a) (push G order a) (push_goodDarts G order a) ω
    rw [mapState_initial,push_mapTarget G B order horder a ha] at h
    have h1 := compile_reads_rank_independent G order B r (max r r')
      (initial a) (push G order a) ω le_rfl (le_max_left ..)
    have h2 := compile_reads_rank_independent (G.wireTargets B) (order.map (mapDart B)) {none}
      r' (max r r') (initial (collapseTarget B a))
      (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a)) ω
      le_rfl (le_max_right ..)
    exact h1.trans (h.trans h2.symm)

theorem search_target_pivotal_moments (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (ho : Exhaustive G order)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    expect w ((search G order a B).score p F w) ≤ 1 ∧
      expect w (fun ω => ((search G order a B).score p F w ω)^2) ≤ 3 := by
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  have h := targetSearch_moments G B (order.map (mapDart B))
    (exhaustive_mapTarget G B order ho) a hp w h0 h1
  have heq : (search G order a B).score p F w =
      (targetSearch G B (order.map (mapDart B)) a).score p F w := by
    funext ω
    rw [score_eq_listScore,score_eq_listScore]
    unfold targetSearch
    rw [search_reads_targetWiring G B order horder]
  change expect w ((search G order a B).score p F w) ≤ 1 ∧ _
  rw [heq]
  exact h

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

theorem score_eq_queryDelta_sum (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E) :
    T.score p F w ω = ∑ e, if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0 := by
  induction T generalizing used w with
  | done _ => simp [score,queryDelta]
  | ask f l r hl hr =>
    have hsum (T' : SearchTree E R) (w' : E → Prop → ℝ) (hT' : T'.Valid (insert f used)) :
        (∑ e, if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
        (if openPivot F f ω then (1-p)*delta w F f else 0) +
          ∑ e, if openPivot F e ω then (1-p)*T'.queryDelta F w' ω e else 0 := by
      have hz := queryDelta_zero_used T' _ hT' F w' ω f (Finset.mem_insert_self _ _)
      have heq (e : E) : (if openPivot F e ω then
          (1-p)*(if e = f then delta w F f else T'.queryDelta F w' ω e) else 0) =
          (if e = f then (if openPivot F f ω then (1-p)*delta w F f else 0) else 0) +
          (if openPivot F e ω then (1-p)*T'.queryDelta F w' ω e else 0) := by
        by_cases he : e = f
        · subst e; rw [hz]; simp
        · simp only [ite_eq_right he,zero_add]
      simp only [heq,Finset.sum_add_distrib]
      simp
    rw [score]
    by_cases hf : ω f
    · simp only [ite_eq_left hf,queryDelta]
      rw [hr _ hT.2.2 (pin w f True),← hsum r (pin w f True) hT.2.2]
    · simp only [ite_eq_right hf,queryDelta]
      rw [hl _ hT.2.1 (pin w f False),← hsum l (pin w f False) hT.2.1]

lemma score_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) : 0 ≤ T.score p F w ω := by
  rw [score_eq_queryDelta_sum T used hT]
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr hp.2.le) (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
  · exact le_rfl

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_ClosedPivotWeight
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

theorem contact_flip_identity (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ψ : ℝ → ℝ) :
    expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
      ψ (T.score p F w (Function.update ω e True))) =
      expect w (fun ω => T.score p F w ω * ψ (T.score p F w ω)) := by
  have hsingle (e : E) :
      expect w (fun ω => T.closedPivotWeight p F w ω e *
        ψ (T.score p F w (Function.update ω e True))) =
      expect w (fun ω => (if openPivot F e ω then (1-p)*T.queryDelta F w ω e else 0) *
        ψ (T.score p F w ω)) := by
    have h := expect_closed_flip_decidable w hw e hp (h0 e) (h1 e)
      (fun ω => (if openPivot F e ω then T.queryDelta F w ω e else 0) * ψ (T.score p F w ω))
    convert h using 1
    · congr 1
      funext ω
      let σ : Set E := ω
      change T.closedPivotWeight p F w σ e * ψ (T.score p F w (Function.update σ e True)) =
        if ¬σ e then p*((if openPivot F e (Function.update σ e True) then
          T.queryDelta F w (Function.update σ e True) e else 0) *
          ψ (T.score p F w (Function.update σ e True))) else 0
      rw [queryDelta_update T F w σ e True]
      simp only [closedPivotWeight]
      by_cases hc : σ e <;>
        by_cases hpiv : openPivot F e (Function.update σ e True) <;> simp [hc,hpiv,mul_assoc]
    · congr 1
      funext ω
      by_cases hpiv : openPivot F e ω
      · simp only [ite_eq_left hpiv,ite_eq_left hpiv.1]; ring
      · simp only [ite_eq_right hpiv,mul_zero,zero_mul,ite_self]
  rw [expect_sum]
  simp_rw [hsingle]
  rw [← expect_sum]
  congr 1
  funext ω
  rw [← Finset.sum_mul]
  exact congrArg (fun x => x * ψ (T.score p F w ω))
    (score_eq_queryDelta_sum T used hT p F w ω).symm

end CriticalPercolation.SearchTree

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma prefixScore_le (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) :
    T.prefixScore p F w ω e ≤ T.score p F w ω := by
  induction T generalizing used w with
  | done _ => exact le_rfl
  | ask f l r hl hr =>
    simp only [prefixScore,score]
    apply add_le_add_right
    by_cases he : e = f
    · rw [ite_eq_left he]
      by_cases ho : ω f
      · rw [ite_eq_left ho]
        exact score_nonneg r _ hT.2.2 hp F hF _ (pin_normalized w hw f True)
          (pin_nonneg w hn f True) (fresh_pin w p used hf f True) ω
      · rw [ite_eq_right ho]
        exact score_nonneg l _ hT.2.1 hp F hF _ (pin_normalized w hw f False)
          (pin_nonneg w hn f False) (fresh_pin w p used hf f False) ω
    · rw [ite_eq_right he]
      by_cases ho : ω f
      · rw [ite_eq_left ho,ite_eq_left ho]
        exact hr _ hT.2.2 _ (pin_normalized w hw f True) (pin_nonneg w hn f True)
          (fresh_pin w p used hf f True)
      · rw [ite_eq_right ho,ite_eq_right ho]
        exact hl _ hT.2.1 _ (pin_normalized w hw f False) (pin_nonneg w hn f False)
          (fresh_pin w p used hf f False)

lemma closedPivotWeight_nonneg (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (ω : Set E) (e : E) : 0 ≤ T.closedPivotWeight p F w ω e := by
  unfold closedPivotWeight
  split_ifs
  · exact mul_nonneg hp.1.le (queryDelta_nonneg T used hT hp F hF w hw hn hf ω e)
  · exact le_rfl

theorem marked_prefix_bound (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : Fresh w p used) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
      (1 + T.prefixScore p F w (Function.update ω e True) e)) ≤
      expect w (T.score p F w) + expect w (fun ω => (T.score p F w ω)^2) := by
  calc
    _ ≤ expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
        (1 + T.score p F w (Function.update ω e True))) := by
      apply expect_mono hn
      intro ω
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (prefixScore_le T used hT hp F hF w hw hn hf _ e) 1)
        (closedPivotWeight_nonneg T used hT hp F hF w hw hn hf ω e)
    _ = expect w (fun ω => T.score p F w ω * (1 + T.score p F w ω)) :=
      contact_flip_identity T used hT hp F w hw h0 h1 (fun x => 1+x)
    _ = expect w (fun ω => T.score p F w ω + (T.score p F w ω)^2) := by
      congr 1
      funext ω
      ring
    _ = _ := expect_add w _ _

end CriticalPercolation.SearchTree

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

end CriticalPercolation.BondGraph

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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Exploration_SearchMarkedContactBound
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

theorem search_marked_contact_bound (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (ho : Exhaustive G order)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    let T := search G order a B
    expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
      (1 + T.prefixScore p F w (Function.update ω e True) e)) ≤ 4 := by
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  let T := search G order a B
  have hv : T.Valid ∅ := compile_valid G order B _ _ _
  have hF : ∀ s t, s ⊆ t → F s → F t := by
    rintro s t hst ⟨b,hb,hab⟩
    exact ⟨b,hb,hab.mono (G.openGraph_mono hst)⟩
  have hm := search_target_pivotal_moments G B order horder ho a hp w h0 h1
  have hb := marked_prefix_bound T ∅ hv hp F hF w (homogeneous_normalized w p h0 h1)
    (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
    (fun e _ => ⟨h0 e,h1 e⟩) h0 h1
  exact hb.trans (by linarith [hm.1,hm.2])

end CriticalPercolation.LazyDFS

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

lemma markWeight_closedPivot (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) (p : ℝ) (w : E → Prop → ℝ)
    (ω : E → Bool) (f : E) (ha : Admissible G B a b ω f) :
    markWeight G order B a b p w ω f =
      (LazyDFS.search G order a B).closedPivotWeight p
        (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f := by
  have hc := admissible_closed G B a b hb ω f ha
  obtain ⟨hn,u,v,hf,hu,hv⟩ := ha
  have hp := G.contact_exit_pivot (configuration ω) B a u v f hf hc hn hu ⟨b,hb,hv.symm⟩
  rw [markWeight,ite_eq_left ⟨hn,u,v,hf,hu,hv⟩,closedPivotWeight,ite_eq_left ⟨hc,hp⟩]

lemma mark_cost_le_pivotal (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (ω : E → Bool) (f : E) :
    markWeight G order B a b p w ω f * (1 + markCost G order B a b p w ω f) ≤
      (LazyDFS.search G order a B).closedPivotWeight p
        (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f *
      (1 + (LazyDFS.search G order a B).prefixScore p
        (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
        (Function.update (configuration ω) f True) f) := by
  by_cases ha : Admissible G B a b ω f
  · rw [markWeight_closedPivot G order B a b hb p w ω f ha,markCost,ite_eq_left ha]
  · rw [markWeight,ite_eq_right ha,zero_mul]
    have hv : (LazyDFS.search G order a B).Valid ∅ := LazyDFS.compile_valid G order B _ _ _
    have hF : ∀ s t : Set E, s ⊆ t → (∃ v ∈ B, (G.openGraph s).Reachable a v) →
        ∃ v ∈ B, (G.openGraph t).Reachable a v := by
      rintro s t hst ⟨v,hv,hr⟩
      exact ⟨v,hv,hr.mono (G.openGraph_mono hst)⟩
    have hw := homogeneous_normalized w p h0 h1
    have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
    have hf : Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
    have hpre := prefixScore_nonneg _ _ hv hp _ hF w hw hn hf
      (Function.update (configuration ω) f True) f
    exact mul_nonneg (closedPivotWeight_nonneg _ _ hv hp _ hF w hw hn hf _ f)
      (by linarith)

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

theorem marked_pair_bound_bs_oai (G : BondGraph V E) (order : List (LazyDFS.Dart V E))
    (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (B : Set V) (a b : V) (hb : b ∈ B) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    expect (QueryTree.bitWeight p) (fun ω => ∑ f,
      markWeight G order B a b p w ω f * (1 + markCost G order B a b p w ω f)) ≤ 4 := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  rw [hw]
  calc
    _ ≤ expect (fun e (b : Bool) => w e (b = true)) (fun ω => ∑ f,
        (LazyDFS.search G order a B).closedPivotWeight p
          (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w (configuration ω) f *
        (1 + (LazyDFS.search G order a B).prefixScore p
          (fun σ => ∃ t ∈ B, (G.openGraph σ).Reachable a t) w
            (Function.update (configuration ω) f True) f)) := by
      apply expect_mono (fun e b => (homogeneous_positive w hp h0 h1 e (b = true)).le)
      intro ω
      exact Finset.sum_le_sum fun f _ => mark_cost_le_pivotal G order B a b hb hp w h0 h1 ω f
    _ ≤ 4 := by
      let F := fun σ : Set E => ∃ t ∈ B, (G.openGraph σ).Reachable a t
      let T := LazyDFS.search G order a B
      let g := fun σ : Set E => ∑ f, T.closedPivotWeight p F w σ f *
        (1 + T.prefixScore p F w (Function.update σ f True) f)
      change expect (fun e (b : Bool) => w e (b = true)) (fun ω => g (configuration ω)) ≤ 4
      rw [expect_configuration w g]
      exact LazyDFS.search_marked_contact_bound G B order horder ho a hp w h0 h1

end CriticalPercolation.ExactExposure

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.ExactExposure.marked_pair_bound_bs_oai.{u_1, u_2}
