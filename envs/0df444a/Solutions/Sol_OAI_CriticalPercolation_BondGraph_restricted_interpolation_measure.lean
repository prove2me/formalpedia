-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:20.256192+00:00
-- url     : https://prove2.me/submissions/6ef95e74-5fb6-453f-8c1d-0f921c74134e

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_inverse_cost

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_VertexBall
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterObject
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
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
-- module Solutions.Q228_CP.CriticalPercolation_Clusters_ClusterObjectAvoidanceCross
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
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

lemma interpolation_uniform_algebra {p c ε δ : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (hc : 0 < c) (hc1 : c≤1) (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-p)
    (hδ : 0<δ) (hδ1 : δ≤1) (n : ℕ) :
    (4*(16/(2*p*(1-p)))+6)*(Real.log (1/δ)+n*(Real.log 8+Real.log (1/c))) +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 ≤
      interpolationConstant c ε * (Real.log (1/δ)+n+1) := by
  have h4 : 0 ≤ Real.log 4 := (Real.log_pos (by norm_num : (1:ℝ)<4)).le
  have h8 : 0 ≤ Real.log 8 := (Real.log_pos (by norm_num : (1:ℝ)<8)).le
  have hr : 0 ≤ Real.log (1/δ) := by
    rw [one_div,Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hδ.le hδ1)
  have hc' : 0 ≤ Real.log (1/c) := by
    rw [one_div,Real.log_inv]
    exact neg_nonneg.mpr (Real.log_nonpos hc.le hc1)
  have hK : 16/(2*p*(1-p)) ≤ 16/(2*ε*ε) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh := mul_le_mul hεp hεq hε.le hp.1.le
    nlinarith
  let A : ℝ := 4*(16/(2*ε*ε))+6
  let B : ℝ := 2*(16/(2*ε*ε))+5
  let l : ℝ := Real.log 8+max 0 (Real.log (1/c))
  let r : ℝ := Real.log (1/δ)
  let T : ℝ := r+n+1
  have hA : 0 ≤ A := by dsimp [A] <;> positivity
  have hB : 0 ≤ B := by dsimp [B] <;> positivity
  have hl : 0 ≤ l := add_nonneg h8 (le_max_left _ _)
  have hcoef : 0 ≤ A*l+B*Real.log 4 := add_nonneg (mul_nonneg hA hl) (mul_nonneg hB h4)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hrT : r≤T := by dsimp [T] <;> linarith
  have hnT : (n:ℝ)≤T := by dsimp [T,r] <;> linarith
  calc
    _ ≤ A*(r+n*(Real.log 8+Real.log (1/c)))+B*(n*Real.log 4) := by
      rw [mul_assoc _ (n:ℝ) (Real.log 4)]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right
        · dsimp [A] <;> linarith
        · exact add_nonneg hr (mul_nonneg hn (add_nonneg h8 hc'))
      · apply mul_le_mul_of_nonneg_right
        · dsimp [B] <;> linarith
        · exact mul_nonneg hn h4
    _ ≤ A*(r+n*l)+B*(n*Real.log 4) := by
      apply add_le_add ?_ le_rfl
      apply mul_le_mul_of_nonneg_left _ hA
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_max_right _ _)) hn
    _ = A*r+(A*l+B*Real.log 4)*n := by ring
    _ ≤ A*T+(A*l+B*Real.log 4)*T :=
      add_le_add (mul_le_mul_of_nonneg_left hrT hA) (mul_le_mul_of_nonneg_left hnT hcoef)
    _ = _ := by dsimp [A,B,l,r,T,interpolationConstant] <;> ring

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_RestrictVertices
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryInterpolation
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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

lemma bisect_length {l r : ℕ} (h : l+1 < r) (b : Bool) :
    (bisect l r b).2 - (bisect l r b).1 ≤ (r-l+1)/2 := by
  unfold bisect
  rw [ite_eq_right (by omega : ¬ r ≤ l+1)]
  cases b <;> simp only [Bool.false_eq_true, ↓reduceIte,midpoint] <;> omega

lemma bisect_clog {l r : ℕ} (h : l+1 < r) (b : Bool) :
    Nat.clog 2 ((bisect l r b).2 - (bisect l r b).1) + 1 ≤ Nat.clog 2 (r-l) := by
  have hh := Nat.clog_mono_right 2 (bisect_length h b)
  rw [Nat.clog_of_one_lt (by decide : 1 < 2) (by omega : 1 < r-l)]
  have he : r-l+2-1 = r-l+1 := by omega
  rw [he]
  exact Nat.add_le_add_right hh 1

lemma terminal_eq_of_adjacent {l r : ℕ} (h : r = l+1) (bs : List Bool) :
    terminal l r bs = (l,r) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa only [terminal,bisect,ite_eq_left (by omega : r ≤ l+1)] using ih

theorem terminal_adjacent {l r : ℕ} (h : l < r) (bs : List Bool)
    (hlen : Nat.clog 2 (r-l) ≤ bs.length) :
    (terminal l r bs).2 = (terminal l r bs).1 + 1 := by
  induction bs generalizing l r with
  | nil =>
    simp only [List.length_nil] at hlen
    have hh := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hlen
    simp only [pow_zero] at hh
    simp only [terminal]
    omega
  | cons b bs ih =>
    by_cases ht : r ≤ l+1
    · rw [terminal_eq_of_adjacent (by omega : r = l+1)]
      dsimp only
      omega
    · have hb := bisect_bounds h b
      have hc := bisect_clog (by omega : l+1 < r) b
      simp only [List.length_cons] at hlen
      exact ih hb.2.1 (by omega)

end CriticalPercolation.BinaryInterpolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_Link
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ForceFalseSubset
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.cluster_empty _root_.OAI.CriticalPercolation.BondGraph.empty_not_percolates _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.openGraph_empty _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ReachableIncidenceImp
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.cluster_empty _root_.OAI.CriticalPercolation.BondGraph.empty_not_percolates _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.openGraph_empty _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_FiberValue
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SearchTree
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Exhaustive
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.cluster_empty _root_.OAI.CriticalPercolation.BondGraph.empty_not_percolates _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.openGraph_empty _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Initial
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Prob
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ProbOr
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_ReachableReplaceTail
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteProductPin
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Potential
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Delta
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_CoordinateNeDensity
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Variance
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
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma prob_true (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1) :
    prob w (fun _ => True) = 1 := by
  simpa only [prob, ite_true, if_true] using expect_const w hw 1

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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClosedFresh
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
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_CutEdgesSubsetIncident
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ExposureLaw
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_CompileContactScoreErase
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ForceClosed
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
        simpa only [run,hbit,decide_true,Bool.true_eq,ite_true, if_true] using hh
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
        simpa only [run,hbit,decide_false,Bool.false_eq_true,ite_false, if_false] using hh
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SearchContactMoments
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
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_ExposureLawSupport
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryDelta
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_SequentialExposure
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
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

theorem contactKernel_normalized (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) (B S : Set V) (hBS : B ⊆ S) (a : V)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hh : 0 < prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b))
    (σ : Set E) :
    let C := G.clusterObject σ S
    expect (exposureLaw w (G.incidentEdges C.1) C.2)
      (fun ω => ∑ m, G.contactKernel order B a p w C ω m) = 1 := by
  dsimp only
  let C := G.clusterObject σ S
  let v := exposureLaw w (G.incidentEdges C.1) C.2
  have hv := exposureLaw_normalized w (G.incidentEdges C.1) C.2
    (homogeneous_normalized w p h0 h1)
  change expect v (fun ω => ∑ m, G.contactKernel order B a p w C ω m) = 1
  by_cases ha : a ∈ C.1
  · have he : (fun ω => ∑ m, G.contactKernel order B a p w C ω m) =
        (fun _ : E → Prop => (1 : ℝ)) := by
      funext ω
      simp [contactKernel,ha]
    rw [he,expect_const v hv]
  · have hB : B ⊆ C.1 := by
      intro b hb
      exact ⟨b,hBS hb,SimpleGraph.Reachable.refl b⟩
    have hm := LazyDFS.search_contact_moments_exposure G order ho B C.1 a ha hB C.2
      (G.clusterObject_cut_closed σ S) p hp w h0 h1
    have he : (fun ω => ∑ m, G.contactKernel order B a p w C ω m) =
        (fun ω => (LazyDFS.search G order a B).contactScore p (G.cutEdges C.1)
          (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b) w ω /
            prob w (fun σ => ∃ b ∈ B, (G.openGraph σ).Reachable a b)) := by
      funext ω
      simp only [contactKernel,ite_eq_right ha,Fintype.sum_option,zero_add]
      rw [←Finset.sum_div,G.sum_contactWeight]
    rw [he]
    simp_rw [div_eq_mul_inv]
    rw [expect_mul_const,hm.1,mul_inv_cancel₀ hh.ne']

end CriticalPercolation.BondGraph

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

lemma compile_queryDelta_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g))
    (hst : ∀ v ∈ st.reached, (G.openGraph ω).Reachable a v) (e : E) :
    (compile G order B fuel st stack).queryDelta F w ω e =
      (compile G order B fuel st stack).queryDelta F w η e := by
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
          simp only [queryDelta,←propext (h d.2.1 hinc)]
          by_cases hed : e = d.2.1
          · simp only [ite_eq_left hed]
          · simp only [ite_eq_right hed]
            by_cases hopen : ω d.2.1
            · simp only [ite_eq_left hopen]
              have hs' : ∀ v ∈ (st.opened d.2.1 d.2.2).reached,
                  (G.openGraph ω).Reachable a v := by
                intro v hv
                rcases Finset.mem_insert.mp hv with rfl | hv
                · exact (hst d.1 htail).trans (prop_openEdge_reachable G ω hopen he)
                · exact hst v hv
              exact ih _ _ _ hs'
            · simp only [ite_eq_right hopen]
              exact ih (st.closed d.2.1) rest (pin w d.2.1 False) hst

variable [Fintype V]
lemma search_queryDelta_incidence (G : BondGraph V E) (order : List (Dart V E))
    (B : Set V) (F : Set E → Prop) (w : E → Prop → ℝ) (ω η : Set E) (a : V)
    (h : ∀ g, (∃ r ∈ G.ends g, (G.openGraph ω).Reachable a r) → (ω g ↔ η g)) (e : E) :
    (search G order a B).queryDelta F w ω e = (search G order a B).queryDelta F w η e := by
  exact compile_queryDelta_incidence G order B _ _ _ F w ω η a h
    (fun v hv => by have he : v=a := Finset.mem_singleton.mp hv; subst v; exact .refl _) e

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E)

lemma contactKernel_record (order : List (LazyDFS.Dart V E))
    (B S T : Set V) (a : V) (hST : S ⊆ T) (ha : a ∈ T)
    (p : ℝ) (w : E → Prop → ℝ) (ω η : E → Prop)
    (h : G.clusterObject ω T = G.clusterObject η T) (mark : Option E) :
    G.contactKernel order B a p w (G.clusterObject ω S) ω mark =
      G.contactKernel order B a p w (G.clusterObject η S) η mark := by
  have hC := G.clusterObject_refines hST ω η h
  unfold contactKernel
  rw [←hC]
  by_cases hh : a ∈ (G.clusterObject ω S).1
  · simp only [ite_eq_left hh]
  · simp only [ite_eq_right hh]
    cases mark with
    | none => rfl
    | some e =>
      apply congrArg (· / _)
      unfold contactWeight
      split_ifs
      · apply congrArg (p*·)
        apply LazyDFS.search_queryDelta_incidence
        rintro g ⟨v,hv,hav⟩
        exact ((G.incidenceExposure T).bits_congr h ⟨v,⟨a,ha,hav⟩,hv⟩).to_iff
      · rfl

end CriticalPercolation.BondGraph

namespace CriticalPercolation.FiniteProduct.Exposure
open scoped Classical
open FiniteEntropy

variable {E A B : Type*} [Fintype E] [Fintype A] [Fintype B]

lemma weighted_identity (R : Exposure E A B) (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (g : (E → A) → ℝ)
    (hg : ∀ ω η, R.record ω = R.record η → g ω = g η)
    (f : B → (E → A) → ℝ)
    (hf : ∀ ω, expect (exposureLaw w (R.domain (R.record ω))
      (R.bits (R.record ω))) (f (R.record ω)) = 1) :
    expect w (fun ω => g ω * f (R.record ω) ω) = expect w g := by
  let k := fiberValue R.record g
  have hk := fiberValue_apply R.record g hg
  calc
    _ = expect w (fun ω => k (R.record ω)*f (R.record ω) ω) := by
      simp only [k,hk]
    _ = expect w (fun ω => expect (exposureLaw w (R.domain (R.record ω))
        (R.bits (R.record ω))) (fun η => k (R.record ω)*f (R.record ω) η)) :=
      R.disintegrate w hw (fun b ω => k b*f b ω)
    _ = _ := by
      simp_rw [expect_const_mul,hf,mul_one]
      simp only [k,hk]

end CriticalPercolation.FiniteProduct.Exposure

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E H : Type*} [Fintype V] [Fintype E] [Fintype H]
variable [DecidableEq V] [DecidableEq E] (G : BondGraph V E)

theorem adaptive_marked_step (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) (S B : H → Set V) (hBS : ∀ h, B h ⊆ S h)
    (a : H → V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hh : ∀ h, 0 < prob w (fun σ => ∃ b ∈ B h, (G.openGraph σ).Reachable (a h) b))
    (r : H → (E → Prop) → ℝ)
    (hr : ∀ h ω η, G.clusterObject ω (S h) = G.clusterObject η (S h) → r h ω = r h η)
    (side : H → (E → Prop) → Option E → Bool) :
    (∑ h, expect w (fun ω => ∑ m : Option E, ∑ b : Bool,
      if side h ω m = b then r h ω * G.contactKernel order (B h) (a h) p w
        (G.clusterObject ω (S h)) ω m else 0)) = ∑ h, expect w (r h) := by
  apply Finset.sum_congr rfl
  intro h _
  have he : (fun ω => ∑ m : Option E, ∑ b : Bool,
      if side h ω m = b then r h ω * G.contactKernel order (B h) (a h) p w
        (G.clusterObject ω (S h)) ω m else 0) =
      (fun ω => r h ω * ∑ m, G.contactKernel order (B h) (a h) p w
        (G.clusterObject ω (S h)) ω m) := by
    funext ω
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
    exact (Finset.mul_sum _ _ _).symm
  rw [he]
  apply (G.incidenceExposure (S h)).weighted_identity w (homogeneous_normalized w p h0 h1)
    (r h) (hr h) (fun C ω => ∑ m, G.contactKernel order (B h) (a h) p w C ω m)
  intro ω
  exact G.contactKernel_normalized order ho (B h) (S h) (hBS h) (a h) hp w h0 h1 (hh h) ω

end CriticalPercolation.BondGraph
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma parentPredicate_congr (L : List (V × Bool)) (S : Set V) (a : V)
    (hL : ∀ z ∈ L, z.1 ∈ S) (ha : a ∈ S) (ω η : Set E)
    (h : G.clusterObject ω S = G.clusterObject η S) (m : Option E) (j : ℕ) :
    parentPredicate G L a ω m j ↔ parentPredicate G L a η m j := by
  have hr (v : V) (hv : v ∈ S) (u : V) :
      (G.openGraph ω).Reachable v u ↔ (G.openGraph η).Reachable v u := by
    apply G.reachable_incidence_congr
    rintro e ⟨r,her,hvr⟩
    have hib : (G.clusterObject ω S).2 e ↔ (G.clusterObject η S).2 e := by rw [h]
    have hei : e ∈ G.incidentEdges (G.clusterObject ω S).1 := ⟨r,⟨v,hv,hvr⟩,her⟩
    have hei' : e ∈ G.incidentEdges (G.clusterObject η S).1 := h ▸ hei
    change (ω e ∧ e ∈ G.incidentEdges (G.clusterObject ω S).1) ↔
      (η e ∧ e ∈ G.incidentEdges (G.clusterObject η S).1) at hib
    simpa only [hei,hei',and_true] using hib
  unfold parentPredicate
  apply exists_congr
  intro z
  by_cases hz : L[j]? = some z
  · have hzmem : z ∈ L := List.mem_of_getElem? hz
    simp only [hz,true_and]
    cases m with
    | none => exact hr a ha z.1
    | some e => exact exists_congr (fun v => and_congr_right (fun _ => hr z.1 (hL z hzmem) v))
  · simp only [hz,false_and]

lemma side_record (L : List (V × Bool)) (S : Set V) (a : V)
    (hL : ∀ z ∈ L, z.1 ∈ S) (ha : a ∈ S) (ω η : Set E)
    (h : G.clusterObject ω S = G.clusterObject η S) (m : Option E) :
    side G L a ω m = side G L a η m := by
  have he : parentPredicate G L a ω m = parentPredicate G L a η m :=
    funext (fun j => propext (parentPredicate_congr G L S a hL ha ω η h m j))
  simp only [side,parent,he]

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

lemma density_record
    (hr₀ : ∀ ω η, G.clusterObject ω ({x 0,x d} : Set V) =
      G.clusterObject η {x 0,x d} → r₀ ω = r₀ η)
    (n : ℕ) (h : History E n) (ω η : E → Prop)
    (he : G.clusterObject ω (anchorSet d x n h) = G.clusterObject η (anchorSet d x n h)) :
    density G order d x p w r₀ n h ω = density G order d x p w r₀ n h η := by
  induction n with
  | zero =>
    apply hr₀
    convert he using 2 <;> first | (with_reducible_and_instances rfl) | (ext v <;> simp [anchorSet,anchors,or_comm])
  | succ n ih =>
    have hST : anchorSet d x n h.1 ⊆ anchorSet d x (n+1) h := by
      rw [anchorSet_step]
      exact Set.subset_insert _ _
    have ha : x (nextIndex d n h.1) ∈ anchorSet d x (n+1) h := by
      rw [anchorSet_step]
      exact Set.mem_insert _ _
    have hs := side_record G (anchors d x n h.1) _ _
      (fun z hz => hST ⟨z.2,hz⟩) ha ω η he h.2.2
    rw [density,density,hs]
    split_ifs
    · rw [ih h.1 (G.clusterObject_refines hST ω η he)]
      rw [G.contactKernel_record order _ _ _ _ hST ha p w ω η he]
    · rfl

theorem density_normalized (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hr₀ : ∀ ω η, G.clusterObject ω ({x 0,x d} : Set V) =
      G.clusterObject η {x 0,x d} → r₀ ω = r₀ η)
    (hZ : expect w r₀ = 1)
    (hh : ∀ n (h : History E n), 0 < prob w (fun σ => ∃ b ∈ anchorSet d x n h,
      (G.openGraph σ).Reachable (x (nextIndex d n h)) b)) (n : ℕ) :
    ∑ h : History E n, expect w (density G order d x p w r₀ n h) = 1 := by
  induction n with
  | zero =>
    change (∑ _h : PUnit, expect w r₀) = 1
    simpa only [Fintype.sum_unique] using hZ
  | succ n ih =>
    have hs := G.adaptive_marked_step order ho (anchorSet d x n) (anchorSet d x n)
      (fun _ => Set.Subset.rfl) (fun h => x (nextIndex d n h)) hp w h0 h1 (hh n)
      (density G order d x p w r₀ n)
      (fun h ω η he => density_record G order d x p w r₀ hr₀ n h ω η he)
      (fun h ω m => side G (anchors d x n h) (x (nextIndex d n h)) ω m)
    change (∑ h : History E n × Bool × Option E, _) = 1
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ h : History E n, expect w (fun ω => ∑ m : Option E, ∑ b : Bool,
          if side G (anchors d x n h) (x (nextIndex d n h)) ω m = b then
            density G order d x p w r₀ n h ω * G.contactKernel order (anchorSet d x n h)
              (x (nextIndex d n h)) p w (G.clusterObject ω (anchorSet d x n h)) ω m else 0) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Fintype.sum_prod_type]
        simp_rw [←expect_sum]
        congr 1
        funext ω
        exact Finset.sum_comm
      _ = ∑ h : History E n, expect w (density G order d x p w r₀ n h) := hs
      _ = 1 := ih

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

lemma reachable_record {S : Set V} {a b : V} (ha : a ∈ S) {ω η : Set E}
    (h : G.clusterObject ω S = G.clusterObject η S) :
    (G.openGraph ω).Reachable a b ↔ (G.openGraph η).Reachable a b := by
  calc
    _ ↔ (G.openGraph (G.clusterObject ω S).2).Reachable a b :=
      (G.reachable_clusterObject ha).symm
    _ ↔ (G.openGraph (G.clusterObject η S).2).Reachable a b := by rw [h]
    _ ↔ _ := G.reachable_clusterObject ha

lemma cluster_record {S : Set V} {a : V} (ha : a ∈ S) {ω η : Set E}
    (h : G.clusterObject ω S = G.clusterObject η S) : G.cluster ω a = G.cluster η a := by
  ext b
  exact reachable_record G ha h

section Seed
variable [Fintype V] [Fintype E]

omit [Fintype E] in
lemma endpointEvent_record (u v : V) (s : ℕ) (ω η : Set E)
    (h : G.clusterObject ω {u,v} = G.clusterObject η {u,v}) :
    endpointEvent G u v s ω ↔ endpointEvent G u v s η := by
  unfold endpointEvent
  rw [reachable_record G (Set.mem_insert u {v}) h,
    cluster_record G (Set.mem_insert u {v}) h,
    cluster_record G (Set.mem_insert_of_mem u (Set.mem_singleton v)) h]

lemma seed_record (w : E → Prop → ℝ) (u v : V) (s : ℕ) (ω η : E → Prop)
    (h : G.clusterObject ω {u,v} = G.clusterObject η {u,v}) :
    seed G w u v s ω = seed G w u v s η := by
  simp only [seed,endpointEvent_record G u v s ω η h]

lemma seed_normalized (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) : expect w (seed G w u v s) = 1 := by
  unfold seed
  rw [expect_const_mul]
  change (prob w (endpointEvent G u v s))⁻¹ * prob w (endpointEvent G u v s) = 1
  exact inv_mul_cancel₀ hδ.ne'

lemma seed_nonneg (w : E → Prop → ℝ) (u v : V) (s : ℕ)
    (hδ : 0 < prob w (endpointEvent G u v s)) (ω : E → Prop) : 0 ≤ seed G w u v s ω := by
  unfold seed
  apply mul_nonneg (inv_nonneg.mpr hδ.le)
  split_ifs <;> norm_num

end Seed

section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem endpoint_density_normalized (order : List (LazyDFS.Dart V E))
    (ho : LazyDFS.Exhaustive G order) {d : ℕ} (hd : 2≤d) (x : ℕ → V)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) (n : ℕ) :
    ∑ h : History E n, expect w
      (density G order d x p w (seed G w (x 0) (x d) s) n h) = 1 := by
  have hw := homogeneous_normalized w p h0 h1
  have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  apply density_normalized G order d x p w _ ho hp h0 h1
    (seed_record G w (x 0) (x d) s) (seed_normalized G w (x 0) (x d) s hδ)
  intro k h
  apply hc.trans_le
  exact root_bound G (by omega : 0<d) x w hw hn
    ((hconn 0 1 (by omega) (by omega) (by omega)).trans (prob_le_one w hw hn _))
    (fun j hj hjd => hconn 0 j hj hjd.le (by simpa using hjd)) k h

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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinarySupport
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma sideWord_length {E : Type*} (n : ℕ) (h : History E n) : (sideWord n h).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sideWord,List.length_append,List.length_singleton,ih]

lemma terminal_append (l r : ℕ) (xs ys : List Bool) :
    terminal l r (xs++ys) = terminal (terminal l r xs).1 (terminal l r xs).2 ys := by
  induction xs generalizing l r with
  | nil => rfl
  | cons b xs ih => simpa only [List.cons_append,terminal] using ih (bisect l r b).1 (bisect l r b).2

lemma interval_eq_terminal {E : Type*} (d n : ℕ) (h : History E n) :
    interval d n h = terminal 0 d (sideWord n h) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sideWord,terminal_append,interval,ih,terminal]

lemma interval_adjacent {E : Type*} {d n : ℕ} (hd : 0<d) (hJ : Nat.clog 2 d ≤ n)
    (h : History E n) : (interval d n h).2 = (interval d n h).1+1 := by
  rw [interval_eq_terminal]
  apply terminal_adjacent hd
  simpa only [Nat.sub_zero,sideWord_length] using hJ

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_AncestryForest
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryForest
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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
  simp only [nodeParent,ite_true, if_true,ite_eq_left hp]

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
      interval_cases i <;> simp only [hb.1,hb.2,ite_true, if_true,one_ne_zero,ite_false, if_false]
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_QueryGeometry
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
    simp only [contactKernel,ite_eq_left ha,Option.some_ne_none,ite_false, if_false] at hk
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryMarks
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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
  simp only [nodeMark,ite_true, if_true]

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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryWords
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_Mass
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
    _ = 1 / (1+s) := by field_simp <;> ring

end CriticalPercolation.ReverseGuess

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_ReverseGuess
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ContactPivot
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
-- module Solutions.Q228_CP.CriticalPercolation_Gluing_ContactExitPivot
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.cluster_empty _root_.OAI.CriticalPercolation.BondGraph.empty_not_percolates _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.openGraph_empty _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_CompileContactPrefixCongr
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_Divergence
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
-- module Solutions.Q228_CP.CriticalPercolation_Modular_PushMass
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_BitWeight
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Node
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_ClusterUsers
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_PrefixScoreNonneg
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryDescriptor
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma fixedDescriptor_card (n : ℕ) : Fintype.card (FixedDescriptor n) = 8^n := by
  simp only [FixedDescriptor,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]

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

lemma jointMass_normalized (ho : LazyDFS.Exhaustive G order) (hd : 2 ≤ d)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∑ z, jointMass G order d x p w s n z = 1 := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [jointMass]
  have ht := endpoint_density_normalized G order ho hd x hp w h0 h1 hc hconn s hδ n
  rw [← ht]
  apply Finset.sum_congr rfl
  intro h _
  have he := expect_configuration w
    (fun η : Set E => density G order d x p w (seed G w (x 0) (x d) s) n h η)
  rw [← hw] at he
  refine Eq.trans ?_ he
  unfold expect
  apply Finset.sum_congr
  · ext f; simp only [Finset.mem_univ]
  · intro f _; rfl

lemma descriptorMass_sum :
    (∑ D, descriptorMass G order d x p w s n D) = ∑ z, jointMass G order d x p w s n z :=
  pushMass_sum _ _

theorem exists_descriptor (hZ : ∑ z, jointMass G order d x p w s n z = 1) :
    ∃ D : FixedDescriptor n, (8:ℝ)^(- (n:ℤ)) ≤ descriptorMass G order d x p w s n D := by
  obtain ⟨D,hD,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (FixedDescriptor n))
    (descriptorMass G order d x p w s n) Finset.univ_nonempty
  have hs : 1 ≤ (8:ℝ)^n * descriptorMass G order d x p w s n D := by
    calc
      1 = ∑ D', descriptorMass G order d x p w s n D' := (descriptorMass_sum G order d x p w s n).trans hZ |>.symm
      _ ≤ ∑ _D' : FixedDescriptor n, descriptorMass G order d x p w s n D :=
        Finset.sum_le_sum (fun D' hD' => hmax D' hD')
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,fixedDescriptor_card,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  refine ⟨D,?_⟩
  rw [zpow_neg, zpow_natCast]
  rw [← one_div]
  exact (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<8) n)).mpr (by simpa only [mul_comm] using hs)

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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryRaw
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_MarkedEntropy
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

end CriticalPercolation.FiniteEntropy

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Z] in
lemma divergence_pushMass_eq (f : X → Y) (P : X → ℝ) (R : Y → ℝ) :
    divergence (pushMass f P) R =
      ∑ x, P x * Real.log (pushMass f P (f x) / R (f x)) :=
  sum_pushMass_mul f P (fun y => Real.log (pushMass f P y / R y))

end CriticalPercolation.FiniteEntropy

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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryConfiguration
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
theorem conditioned_configuration_entropy (ho : LazyDFS.Exhaustive G order)
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

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryCostBound
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
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

local instance costBoundFinDec_rcb2cc5_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
lemma constructionCost_le {c : ℝ} (hc : 0 < c)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : (8:ℝ)^(-(n:ℤ)) ≤ descriptorMass G order d x p w s n D) :
    constructionCost G order d x p w c s n D ≤
      Real.log (1/prob w (endpointEvent G (x 0) (x d) s)) + n*(Real.log 8+Real.log (1/c)) := by
  have ho : 0 < descriptorMass G order d x p w s n D :=
    (zpow_pos (by norm_num : (0:ℝ)<8) _).trans_le hD
  have hl := Real.log_le_log (zpow_pos (by norm_num : (0:ℝ)<8) _) hD
  rw [Real.log_zpow] at hl
  simp only [Int.cast_neg,Int.cast_natCast] at hl
  unfold constructionCost
  rw [Real.log_div (mul_ne_zero (inv_ne_zero hδ.ne') (pow_ne_zero _ (inv_ne_zero hc.ne'))) ho.ne',
    Real.log_mul (inv_ne_zero hδ.ne') (pow_ne_zero _ (inv_ne_zero hc.ne')),Real.log_pow]
  simp only [one_div]
  nlinarith

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryParents
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinarySwitches
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryPrefix
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryCosts
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.Aut.smul_vertex _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.stabilizerWeight_self _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk _root_.OAI.CriticalPercolation.ClusterDeletion.roots_bot
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryTranscript
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_ReverseReference
attribute [-instance] _root_.OAI.CriticalPercolation.OrderedQuery.localNodeDecidable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
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

lemma weight_sum_le (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X)
    (hk : ∀ i x m, 0 ≤ k i x m) (hs : ∀ i x, ∑ m, k i x m ≤ 1)
    (n : ℕ) (x : X) : ∑ m, weight k u n x m ≤ 1 := by
  classical
  induction n generalizing x with
  | zero => simp [weight]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n+1) => M)).sum_comp]
    simp only [Fin.snocEquiv,Equiv.coe_fn_mk,weight,Fin.snoc_last,Fin.init_snoc,Fintype.sum_prod_type]
    calc
      _ = ∑ m, k n x m * ∑ h, weight k u n (u n x m) h := by
        simp only [Finset.mul_sum]
      _ ≤ ∑ m, k n x m := Finset.sum_le_sum fun m _ => by
        simpa using mul_le_mul_of_nonneg_left (ih (u n x m)) (hk n x m)
      _ ≤ 1 := hs n x

section Terminal
variable [Fintype X] {I : Type*} [Fintype I]

omit [Fintype M] [Fintype X] in
lemma terminalWeight_nonneg (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m)
    (x : X) (m : I → M) : 0 ≤ terminalWeight a x m :=
  Finset.prod_nonneg fun i _ => ha i x (m i)

omit [Fintype X] in
lemma terminalWeight_sum (a : I → X → M → ℝ) (ha : ∀ i x, ∑ m, a i x m = 1)
    (x : X) : ∑ m, terminalWeight a x m = 1 := by
  unfold terminalWeight
  rw [← Fintype.prod_sum]
  simp only [ha,Finset.prod_const_one]

omit [Fintype M] [Fintype X] in
lemma joint_nonneg (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (a : I → X → M → ℝ) (ha : ∀ i x m, 0 ≤ a i x m) (n : ℕ) (z) :
    0 ≤ joint μ k u a n z :=
  mul_nonneg (mul_nonneg (hμ _) (weight_nonneg k u hk _ _ _)) (terminalWeight_nonneg a ha _ _)

lemma joint_marginal_le (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (k : ℕ → X → M → ℝ) (u : ℕ → X → M → X) (hk : ∀ i x m, 0 ≤ k i x m)
    (hs : ∀ i x, ∑ m, k i x m ≤ 1)
    (a : I → X → M → ℝ) (ha : ∀ i x, ∑ m, a i x m = 1) (n : ℕ) (x : X) :
    FiniteEntropy.pushMass Prod.fst (joint μ k u a n) x ≤ μ x := by
  rw [FiniteEntropy.pushMass_fst,Fintype.sum_prod_type]
  simp only [joint,← Finset.mul_sum,terminalWeight_sum a ha,mul_one]
  exact (mul_le_mul_of_nonneg_left (weight_sum_le k u hk hs n x) (hμ x)).trans_eq (mul_one _)

end Terminal
end CriticalPercolation.ReverseReference

namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype Y] [Fintype Z] in
lemma pushMass_at_supported_injection (P : X → ℝ) (e : X → Y)
    (hi : ∀ x x', P x ≠ 0 → P x' ≠ 0 → e x = e x' → x=x')
    (x : X) (hx : P x ≠ 0) : pushMass e P (e x) = P x := by
  unfold pushMass
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    split_ifs with he
    · by_contra hz
      exact hy (hi y x hz hx he)
    · rfl
  · simp

omit [Fintype Z] in
lemma divergence_reference_mono (P R S : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hR : ∀ x, 0 < P x → 0 < R x) (hRS : ∀ x, R x ≤ S x) :
    divergence P S ≤ divergence P R := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : P x = 0
  · simp [hx]
  · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
    have hr := hR x hp
    have hs : 0 < S x := hr.trans_le (hRS x)
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos hp hs) (div_le_div_of_nonneg_left hp.le hr (hRS x))) (hP x)

theorem mapped_entropy_le (P : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (e : X → Z) (hi : ∀ x x', P x ≠ 0 → P x' ≠ 0 → e x = e x' → x=x')
    (f : Z → Y) (R : Z → ℝ) (hR : ∀ z, 0 ≤ R z) (μ : Y → ℝ)
    (hμ : ∀ y, pushMass f R y ≤ μ y) (cost : X → ℝ)
    (hd : ∀ x, P x ≤ R (e x) * Real.exp (cost x)) :
    divergence (pushMass (f ∘ e) P) μ ≤ ∑ x, P x * cost x := by
  have hs (x : X) (hx : 0 < P x) : 0 < R (e x) := by
    have he := (hx.trans_le (hd x))
    exact (mul_pos_iff.mp he).resolve_right (fun h => (Real.exp_pos _).not_ge h.2.le) |>.1
  have hs' (z : Z) (hz : 0 < pushMass e P z) : 0 < R z := by
    by_contra! hn
    have ht : pushMass e P z ≤ 0 := by
      unfold pushMass
      apply Finset.sum_nonpos
      intro x _
      split_ifs with he
      · by_contra! hp
        exact (hs x hp).not_ge (he ▸ hn)
      · rfl
    linarith
  have hs'' (y : Y) (hy : 0 < pushMass f (pushMass e P) y) : 0 < pushMass f R y := by
    by_contra! hn
    have ht : pushMass f (pushMass e P) y ≤ 0 := by
      unfold pushMass
      apply Finset.sum_nonpos
      intro z _
      split_ifs with he
      · by_contra! hp
        have hz := (hs' z hp).trans_le (le_pushMass f R hR z)
        rw [he] at hz
        exact hz.not_ge hn
      · rfl
    linarith
  calc
    _ = divergence (pushMass f (pushMass e P)) μ := by rw [pushMass_comp]
    _ ≤ divergence (pushMass f (pushMass e P)) (pushMass f R) :=
      divergence_reference_mono _ _ _ (pushMass_nonneg _ _ (pushMass_nonneg _ _ hP)) hs'' hμ
    _ ≤ divergence (pushMass e P) R := divergence_pushMass_le f _ R
      (pushMass_nonneg _ _ hP) hR hs'
    _ ≤ _ := by
      rw [divergence_pushMass_eq]
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : P x = 0
      · simp [hx]
      · have hp : 0 < P x := lt_of_le_of_ne (hP x) (Ne.symm hx)
        rw [pushMass_at_supported_injection P e hi x hx]
        apply mul_le_mul_of_nonneg_left _ (hP x)
        have hr := hs x hp
        apply (Real.log_le_iff_le_exp (div_pos hp hr)).mpr
        exact (div_le_iff₀ hr).mpr (by simpa only [mul_comm] using hd x)

end CriticalPercolation.FiniteEntropy
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_MarkedBits
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

lemma masked_join (S : Finset I) (m : I → Option E) (i : I) :
    (if i ∈ S then masked S m i else masked Sᶜ m i) = m i := by
  simp only [masked,Finset.mem_compl]
  split_ifs <;> rfl

lemma masked_injective (S : Finset I) (m m' : I → Option E)
    (h1 : masked S m = masked S m') (h2 : masked Sᶜ m = masked Sᶜ m') : m=m' := by
  funext i
  rw [← masked_join S m i,← masked_join S m' i,h1,h2]

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

lemma opened_injective_closed (S : Finset I) (m : I → Option E) (ω η : E → Bool)
    (hω : ∀ i ∈ S, ∀ e, m i = some e → ω e = false)
    (hη : ∀ i ∈ S, ∀ e, m i = some e → η e = false)
    (he : opened S m ω = opened S m η) : ω=η := by
  funext e
  by_cases hm : ∃ i ∈ S, m i = some e
  · obtain ⟨i,hi,him⟩ := hm
    rw [hω i hi e him,hη i hi e him]
  · have hh := congrFun he e
    simpa only [opened,ite_eq_right hm] using hh

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
  simp only [he,Function.update_self,QueryTree.bitWeight,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryReverseKernels
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

lemma inverseKernel_sum (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (j : ℕ) (ω : E → Bool) : (∑ m, inverseKernel G order d x p w n D j ω m) ≤ 1 := by
  unfold inverseKernel
  split_ifs with hj hi
  · rw [Fintype.sum_option]
    simp only [zero_add]
    exact (pivotGuess_subprobability G order d x p w n D hp h0 h1 _ ω).2
  · simp
  · simp

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

lemma inactiveKernel_sum (i : Fin n) (ω : E → Bool) :
    (∑ m, inactiveKernel G order d x p w n D i ω m) = 1 := by
  unfold inactiveKernel
  split_ifs with hi ht
  · simp
  · simp
  · rw [← Finset.sum_div]
    exact div_self ht

lemma inverseReference_nonneg (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (z) :
    0 ≤ inverseReference G order d x p w n D z :=
  ReverseReference.joint_nonneg _ (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    _ _ (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    _ (inactiveKernel_nonneg G order d x p w n D hp h0 h1) n z

lemma inverseReference_marginal (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) (ω : E → Bool) :
    pushMass Prod.fst (inverseReference G order d x p w n D) ω ≤
      FiniteProduct.density (QueryTree.bitWeight p) ω := by
  have he := ReverseReference.joint_marginal_le
    (FiniteProduct.density (QueryTree.bitWeight p) : (E → Bool) → ℝ)
    (FiniteProduct.density_nonneg (QueryTree.bitWeight_nonneg ⟨hp.1.le,hp.2.le⟩))
    (inverseKernel G order d x p w n D) (inverseUpdate (E := E) n D)
    (inverseKernel_nonneg G order d x p w n D hp h0 h1)
    (inverseKernel_sum G order d x p w n D hp h0 h1)
    (inactiveKernel G order d x p w n D) (inactiveKernel_sum G order d x p w n D) n ω
  refine Eq.trans_le ?_ he
  unfold pushMass
  apply Finset.sum_congr
  · ext z
    simp only [Finset.mem_univ]
  · intro z _
    rfl

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryOutput
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph LazyDFS BinaryInterpolation InterpolationForest

variable {V E : Type*} (G : BondGraph V E)

lemma hasSide_mono_reachable (L : List (V × Bool)) (ω : Set E) (b : Bool) {u v : V}
    (hu : HasSide G L ω b u) (hr : (G.openGraph ω).Reachable u v) :
    HasSide G L ω b v := by
  obtain ⟨z,hz,hb,hrz⟩ := hu
  exact ⟨z,hz,hb,hrz.trans hr⟩

lemma hasSide_unique (L : List (V × Bool)) (ω : Set E) (hL : Consistent G L ω)
    {b c : Bool} {v : V} (hb : HasSide G L ω b v) (hc : HasSide G L ω c v) : b=c := by
  obtain ⟨z,hz,hzb,hzv⟩ := hb
  obtain ⟨t,ht,htc,htv⟩ := hc
  exact hzb.symm.trans ((hL z hz t ht (hzv.trans htv.symm)).trans htc)

section Output
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (order : List (Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)

lemma switched_side_adj (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) {b : Bool} {u v : V}
    (hu : HasSide G (anchors d x n h) ω b u)
    (huv : (G.openGraph (switched n h ω S)).Adj u v) :
    HasSide G (anchors d x n h) ω b v := by
  obtain ⟨⟨e,he,hev⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huv
  rcases he with he|⟨i,hi,him⟩
  · exact hasSide_mono_reachable G _ ω b hu (prop_openEdge_reachable G ω he hev)
  · obtain ⟨_,a,c,heac,ha,hc⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i
      (hS i hi).1 (hS i hi).2 e him
    have hip := nodeParent_lt G d x ω n h i (hS i hi).1
    have hcol := node_colour_parent G order d x p w r₀ n h ω hr i (hS i hi).1 (hS i hi).2
    have hA : HasSide G (anchors d x n h) ω (node d x n h i).2 a :=
      ⟨_,node_mem d x n h i (hS i hi).2,rfl,ha⟩
    have hC : HasSide G (anchors d x n h) ω (node d x n h i).2 c :=
      ⟨_,node_mem d x n h _ (hip.trans (hS i hi).2),hcol.symm,hc⟩
    rcases Sym2.eq_iff.mp (hev.symm.trans heac) with ⟨hua,hvc⟩|⟨huc,hva⟩
    · subst u; subst v
      exact (hasSide_unique G _ ω hL hu hA).symm ▸ hC
    · subst u; subst v
      exact (hasSide_unique G _ ω hL hu hC).symm ▸ hA

lemma switched_side_reachable (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (hL : Consistent G (anchors d x n h) ω)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) {b : Bool} {u v : V}
    (hu : HasSide G (anchors d x n h) ω b u)
    (huv : (G.openGraph (switched n h ω S)).Reachable u v) :
    HasSide G (anchors d x n h) ω b v := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at huv
  induction huv with
  | refl => exact hu
  | tail _ hstep ih => exact switched_side_adj G order d x p w r₀ n h ω hr hL S hS ih hstep

theorem switched_terminal_distinct (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0)
    (S : Finset ℕ) (hS : ∀ i ∈ S, 2 ≤ i ∧ i < n+2) :
    ¬(G.openGraph (switched n h ω S)).Reachable
      (x (interval d n h).1) (x (interval d n h).2) := by
  intro hreach
  have hL := density_consistent G order d x p w s n h ω hr
  have he := endpoint_labels d x n h
  have hl : HasSide G (anchors d x n h) ω true (x (interval d n h).1) :=
    ⟨_,he.1,rfl,.refl _⟩
  have hr' : HasSide G (anchors d x n h) ω false (x (interval d n h).2) :=
    ⟨_,he.2,rfl,.refl _⟩
  have hh := switched_side_reachable G order d x p w _ n h ω hr hL S hS hl hreach
  cases hasSide_unique G _ ω hL hh hr'

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma active_index_bounds (d : ℕ) (x : ℕ → V) (n : ℕ) (h : History E n) (ω : Set E) :
    ∀ i ∈ activeNodes G d x n h ω, 2 ≤ i ∧ i < n+2 := by
  intro i hi
  exact ⟨((historyForest G d x ω n h).mem_active.mp hi).2,active_lt G d x n h ω i hi⟩

lemma active_lineage_reachable (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0)
    (u : ℕ) (hu : u = owner G d x n h ω (x (interval d n h).1) ∨
      u = owner G d x n h ω (x (interval d n h).2))
    (i : ℕ) (hi : i ∈ (historyForest G d x ω n h).lineage u) (hin : i < n+2) :
    (G.openGraph (switched n h ω (activeNodes G d x n h ω))).Reachable
      (node d x n h i).1 (node d x n h ((historyForest G d x ω n h).root i)).1 := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases hib : i < 2
    · rw [Forest.root_base _ hib]
    · have hi2 : 2 ≤ i := by omega
      have hia : i ∈ activeNodes G d x n h ω := by
        apply (Forest.mem_active _).mpr
        exact ⟨hu.elim (fun e => Or.inl (e ▸ hi)) (fun e => Or.inr (e ▸ hi)),hi2⟩
      have hm := active_nonhold G order d x p w r₀ n h ω hr i hia
      obtain ⟨e,he⟩ := Option.ne_none_iff_exists'.mp hm
      obtain ⟨_,a,b,heab,ha,hb⟩ := node_mark_geometry G order d x p w r₀ n h ω hr i hi2 hin e he
      have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
      have heopen : switched n h ω (activeNodes G d x n h ω) e := Or.inr ⟨i,hia,he⟩
      have hparent := (ha.mono hmon).trans
        ((prop_openEdge_reachable G _ heopen heab).trans (hb.symm.mono hmon))
      rw [Forest.root_step _ hi2]
      exact hparent.trans (ih _ (nodeParent_lt G d x ω n h i hi2)
        ((historyForest G d x ω n h).parent_mem_lineage hi2 hi)
        ((nodeParent_lt G d x ω n h i hi2).trans hin))

theorem switched_terminal_bases (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    let η := switched n h ω (activeNodes G d x n h ω)
    (G.openGraph η).Reachable (x (interval d n h).1) (x 0) ∧
    (G.openGraph η).Reachable (x (interval d n h).2) (x d) := by
  have he := endpoint_labels d x n h
  have hrts := terminal_roots G order d x p w s n h ω hr
  have hb := node_bases d x n h
  have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
  constructor
  · have hanc := active_lineage_reachable G order d x p w _ n h ω hr _ (Or.inl rfl) _
      ((historyForest G d x ω n h).self_mem_lineage _) (owner_lt G d x n h ω _ ⟨true,he.1⟩)
    rw [hrts.1,hb.1] at hanc
    exact ((owner_reachable G d x n h ω _ ⟨true,he.1⟩).mono hmon).trans hanc
  · have hanc := active_lineage_reachable G order d x p w _ n h ω hr _ (Or.inr rfl) _
      ((historyForest G d x ω n h).self_mem_lineage _) (owner_lt G d x n h ω _ ⟨false,he.2⟩)
    rw [hrts.2,hb.2] at hanc
    exact ((owner_reachable G d x n h ω _ ⟨false,he.2⟩).mono hmon).trans hanc

lemma density_seed_support (n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w r₀ n h ω ≠ 0) : r₀ ω ≠ 0 := by
  induction n with
  | zero => exact hr
  | succ n ih => exact ih h.1 (density_step_support G order d x p w r₀ n h ω hr).1

theorem switched_endpointEvent (s n : ℕ) (h : History E n) (ω : E → Prop)
    (hr : density G order d x p w (seed G w (x 0) (x d) s) n h ω ≠ 0) :
    endpointEvent G (x (interval d n h).1) (x (interval d n h).2) s
      (switched n h ω (activeNodes G d x n h ω)) := by
  have hseed := density_seed_support G order d x p w _ n h ω hr
  have ho : endpointEvent G (x 0) (x d) s ω := by
    by_contra ho
    simp only [seed,ite_eq_right ho,mul_zero] at hseed
    exact hseed rfl
  have hb := switched_terminal_bases G order d x p w s n h ω hr
  have hmon := G.openGraph_mono (switched_mono n h ω (activeNodes G d x n h ω))
  refine ⟨switched_terminal_distinct G order d x p w s n h ω hr _
    (active_index_bounds G d x n h ω),?_,?_⟩
  · apply ho.2.1.trans
    apply Finset.card_le_card
    intro v hv
    have hv' : (G.openGraph ω).Reachable (x 0) v := (Set.mem_toFinset (s := G.cluster ω (x 0)) (a := v)).mp hv
    exact (Set.mem_toFinset (s := G.cluster (switched n h ω (activeNodes G d x n h ω)) (x (interval d n h).1)) (a := v)).mpr (hb.1.trans (hv'.mono hmon))
  · apply ho.2.2.trans
    apply Finset.card_le_card
    intro v hv
    have hv' : (G.openGraph ω).Reachable (x d) v := (Set.mem_toFinset (s := G.cluster ω (x d)) (a := v)).mp hv
    exact (Set.mem_toFinset (s := G.cluster (switched n h ω (activeNodes G d x n h ω)) (x (interval d n h).2)) (a := v)).mpr (hb.2.trans (hv'.mono hmon))

end Output
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryStages
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

lemma stage_last (n : ℕ) (D : FixedDescriptor n) (ω : E → Bool) (m : Fin n → Option E) :
    stage n D ω m n = opened (activeSteps n D) m ω := by
  unfold stage stageIndices
  rw [Finset.filter_true_of_mem (fun i _ => i.isLt)]

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
  · simp only [he,ite_true, if_true,or_true]
  · simp only [he,ite_false, if_false,or_false]
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

lemma supported_opening_injective
    (z z' : (E → Bool) × (Fin n → Option E))
    (hz : conditionedMass G order d x p w s n D z ≠ 0)
    (hz' : conditionedMass G order d x p w s n D z' ≠ 0)
    (he : (stage n D z.1 z.2 n,masked (activeSteps n D) z.2,masked (activeSteps n D)ᶜ z.2) =
      (stage n D z'.1 z'.2 n,masked (activeSteps n D) z'.2,masked (activeSteps n D)ᶜ z'.2)) : z=z' := by
  rcases z with ⟨ω,m⟩
  rcases z' with ⟨η,m'⟩
  have hm : m=m' := masked_injective (activeSteps n D) m m'
    (congrArg (fun y => y.2.1) he) (congrArg (fun y => y.2.2) he)
  subst m'
  have ho := congrArg Prod.fst he
  simp only [stage_last] at ho
  exact Prod.ext (opened_injective_closed _ m ω η
    (supported_mark_closed G order d x p w s n D ω m hz)
    (supported_mark_closed G order d x p w s n D η m hz') ho) rfl

lemma stage_endpointEvent (ω : E → Bool) (m : Fin n → Option E)
    (hz : conditionedMass G order d x p w s n D (ω,m) ≠ 0) :
    endpointEvent G
      (x (interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))).1)
      (x (interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))).2) s
      (configuration (stage n D ω m n)) := by
  obtain ⟨hD,hr⟩ := conditionedMass_support G order d x p w s n D (ω,m) hz
  rw [stage_last,configuration_opened]
  have he := switched_endpointEvent G order d x p w s n (fromWords n (fun j => (D j).1) m) _ hr
  rw [activeNodes_eq_descriptor G d x n _ _ D hD] at he
  rw [interval_fromWords d n _ m (fun _ => none)] at he
  exact he

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryReversePrices
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
        not_true_eq_false,ite_false, if_false,ite_true, if_true]
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
      ite_true, if_true,ite_false, if_false,inactiveKernel,ite_eq_right hA.ne',inversePenalty,one_mul,hs]
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_RecursiveLikelihood
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
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryReferenceLikelihood
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

lemma conditioned_reference_density_le (s : ℕ) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
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

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryOutputEntropy
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
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.outputEntropyFinDec
lemma inverseLog_expectation (Q : ((E → Bool) × (Fin n → Option E)) → ℝ) :
    (∑ z, Q z * inverseLog G order d x p w n D z.1 z.2) =
      2*(∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) +
      ∑ z, Q z * logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration z.1) := by
  simp only [inverseLog,mul_add,Finset.sum_add_distrib]
  congr 1
  simp_rw [mul_left_comm (Q _) 2,Finset.mul_sum]
  rw [Finset.sum_comm]

theorem conditioned_output_entropy (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    divergence (outputMass G order d x p w s n D) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
      (4*(16/(2*p*(1-p)))+6)*constructionCost G order d x p w c s n D +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 := by
  let Q := conditionedMass G order d x p w s n D
  let μ : (E → Bool) → ℝ := FiniteProduct.density (QueryTree.bitWeight p)
  let L := constructionCost G order d x p w c s n D
  have hQ : ∀ z, 0 ≤ Q z := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z = 1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hm := mapped_entropy_le Q hQ (recorded n D)
    (fun z z' hz hz' he => supported_opening_injective G order d x p w s n D z z' hz hz' he)
    Prod.fst (inverseReference G order d x p w n D)
    (inverseReference_nonneg G order d x p w n D hp h0 h1) μ
    (inverseReference_marginal G order d x p w n D hp h0 h1)
    (fun z => L+inverseLog G order d x p w n D z.1 z.2)
    (conditioned_reference_density_le G order d x p w n D s hd hp h0 h1 hc hc1 hconn hδ hD)
  have he : (∑ z, Q z*(L+inverseLog G order d x p w n D z.1 z.2)) =
      L + (2*(∑ i ∈ activeSteps n D, ∑ z, Q z*Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) +
      ∑ z, Q z*logContactMass (scheduleWeight G order d x p w n (fun j => (D j).1)) (configuration z.1)) := by
    simp only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,hQ1,one_mul]
    rw [inverseLog_expectation G order d x p w n D Q]
  rw [he] at hm
  have hi := conditioned_inverse_cost G order d x p w s n D horder ho hd hp h0 h1 hc hc1 hconn hδ hD
  have hl := (conditioned_configuration_entropy G order d x p w ho hd hp h0 h1 hc hc1 hconn s n D hδ hD).2
  change divergence (outputMass G order d x p w s n D) μ ≤ _ at hm
  change _ ≤ (4*(16/(2*p*(1-p)))+6)*L+(2*(16/(2*p*(1-p)))+5)*n*Real.log 4
  calc
    _ ≤ _ := hm
    _ ≤ L + (2*(((16/(2*p*(1-p)))*(2*L+n*Real.log 4))+2*L+2*n*Real.log 4) + (L+n*Real.log 4)) :=
      add_le_add (le_refl L) (add_le_add (mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 2)) hl)
    _ = _ := by ring

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_FiniteEventEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma supported_event_entropy (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (hR : ∀ x, 0 < R x) (A : Set X)
    (hs : ∀ x, P x ≠ 0 → x ∈ A) :
    0 < (∑ x, if x ∈ A then R x else 0) ∧
      Real.log (1/(∑ x, if x ∈ A then R x else 0)) ≤ divergence P R := by
  let R' : X → ℝ := fun x => if x ∈ A then R x else 0
  have hn : ∀ x, 0 ≤ R' x := by
    intro x
    unfold R'
    split_ifs
    · exact (hR x).le
    · exact le_rfl
  have hp : ∀ x, 0 < P x → 0 < R' x := by
    intro x hx
    simp only [R',ite_eq_left (hs x hx.ne')]
    exact hR x
  have ho : 0 < ∑ x, R' x := by
    have hh := normalizer_pos P R' hP hn hP1 hp (fun _ => 0)
    simpa only [Real.exp_zero,mul_one] using hh
  refine ⟨ho,?_⟩
  have hh := log_sum_inequality P R' hP hn hp
  rw [hP1,one_mul] at hh
  refine hh.trans_eq ?_
  unfold divergence
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x=0
  · simp only [hx,zero_mul]
  · simp only [R',ite_eq_left (hs x hx)]

omit [Fintype Y] in
lemma pushMass_supported (P : X → ℝ) (f : X → Y) (A : Set Y)
    (hs : ∀ x, P x ≠ 0 → f x ∈ A) (y : Y) (hy : pushMass f P y ≠ 0) : y ∈ A := by
  by_contra hn
  apply hy
  unfold pushMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : f x=y
  · rw [ite_eq_left hx]
    by_contra hp
    exact hn (hx ▸ hs x hp)
  · exact ite_eq_right hx

end CriticalPercolation.FiniteEntropy
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Entropy_BinaryEventBound
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy MarkedBits

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.eventBoundFinDec
lemma prob_bits (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (P : Set E → Prop) :
    (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) =
      prob w P := by
  have hw : QueryTree.bitWeight p = fun e (b : Bool) => w e (b = true) := by
    funext e b
    cases b <;> simp [QueryTree.bitWeight,h0,h1]
  have he := expect_configuration w (fun η => if P η then (1:ℝ) else 0)
  rw [← hw] at he
  simpa only [expect,prob,mul_ite,mul_one,mul_zero] using he

theorem conditioned_event_bound (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let t := interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))
    0 < prob w (endpointEvent G (x t.1) (x t.2) s) ∧
      -Real.log (prob w (endpointEvent G (x t.1) (x t.2) s)) ≤
      (4*(16/(2*p*(1-p)))+6)*constructionCost G order d x p w c s n D +
        (2*(16/(2*p*(1-p)))+5)*n*Real.log 4 := by
  dsimp only
  let t := interval d n (fromWords (E := E) n (fun j => (D j).1) (fun _ => none))
  let P := endpointEvent G (x t.1) (x t.2) s
  let Q := conditionedMass G order d x p w s n D
  let f : ((E → Bool) × (Fin n → Option E)) → (E → Bool) := fun z => stage n D z.1 z.2 n
  have hQ := conditionedMass_nonneg G order d x p w s n hp h0 h1 hδ D hD
  have hQ1 : ∑ z, Q z=1 := by
    have he := conditionedMass_normalized G order d x p w s n D hD
    refine Eq.trans ?_ he
    apply Finset.sum_congr
    · ext z; simp only [Finset.mem_univ]
    · intro z _; rfl
  have hh := supported_event_entropy (pushMass f Q) (FiniteProduct.density (QueryTree.bitWeight p))
    (pushMass_nonneg f Q hQ) ((pushMass_sum f Q).trans hQ1)
    (fun ω => Finset.prod_pos fun e _ => QueryTree.bitWeight_pos hp e (ω e))
    {ω | P (configuration ω)}
    (pushMass_supported Q f {ω | P (configuration ω)} (fun z hz =>
      stage_endpointEvent G order d x p w s n D z.1 z.2 hz))
  have hb := prob_bits p w h0 h1 P
  change (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) = _ at hb
  change 0 < (∑ ω : E → Bool, if P (configuration ω) then FiniteProduct.density (QueryTree.bitWeight p) ω else 0) ∧ _ at hh
  rw [hb] at hh
  have hl := conditioned_output_entropy G order d x p w s n D horder ho hd hp h0 h1 hc hc1 hconn hδ hD
  refine ⟨hh.1,?_⟩
  have he := hh.2.trans hl
  simp only [Set.mem_ofPred_eq] at he
  rw [hb] at he
  simpa only [one_div,Real.log_inv] using he

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteInterpolation
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
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E]

lemma allDarts_good (G : BondGraph V E) : LazyDFS.GoodDarts G (allDarts G) := by
  intro a ha
  simpa only [allDarts,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using ha

lemma allDarts_exhaustive (G : BondGraph V E) : LazyDFS.Exhaustive G (allDarts G) := by
  intro v e t h
  simp only [allDarts,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
  exact h

local instance interpolationFinDec_rcb2cc5_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
theorem finite_interpolation_index (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (hd : 2≤d) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∃ j<d, 0 < prob w (endpointEvent G (x j) (x (j+1)) s) ∧
      -Real.log (prob w (endpointEvent G (x j) (x (j+1)) s)) ≤
      (4*(16/(2*p*(1-p)))+6)*(Real.log (1/prob w (endpointEvent G (x 0) (x d) s)) +
          (Nat.clog 2 d)*(Real.log 8+Real.log (1/c))) +
        (2*(16/(2*p*(1-p)))+5)*(Nat.clog 2 d)*Real.log 4 := by
  let order := allDarts G
  let n := Nat.clog 2 d
  have hc1 : c≤1 := (hconn 0 1 (by omega) (by omega) (by omega)).trans
    (prob_le_one w (homogeneous_normalized w p h0 h1)
      (fun e b => (homogeneous_positive w hp h0 h1 e b).le) _)
  obtain ⟨D,hD⟩ := exists_descriptor G order d x p w s n
    (jointMass_normalized G order d x p w s n (allDarts_exhaustive G) hd hp h0 h1 hc hconn hδ)
  have hD0 : 0 < descriptorMass G order d x p w s n D :=
    (zpow_pos (by norm_num : (0:ℝ)<8) _).trans_le hD
  have he := conditioned_event_bound G order d x p w s n D (allDarts_good G)
    (allDarts_exhaustive G) (by omega) hp h0 h1 hc hc1
    (fun j hj hjd => hconn 0 j hj hjd.le (by simpa only [Nat.sub_zero] using hjd)) hδ hD0
  let h := fromWords (E := E) n (fun j => (D j).1) (fun _ => none)
  have hadj := interval_adjacent (by omega : 0<d) (le_refl (Nat.clog 2 d)) h
  have hb := interval_bounds (by omega : 0<d) n h
  refine ⟨(interval d n h).1,by omega,?_⟩
  change 0 < prob w (endpointEvent G (x (interval d n h).1) (x (interval d n h).2) s) ∧ _ at he
  rw [hadj] at he
  refine ⟨he.1,he.2.trans ?_⟩
  apply add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left (constructionCost_le G order d x p w s n D hc hδ hD)
  have : 0 < 2*p*(1-p) := mul_pos (mul_pos (by norm_num) hp.1) (sub_pos.mpr hp.2)
  positivity

end CriticalPercolation.BinaryLaw
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteInterpolationUniform
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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
open FiniteProduct BondGraph

variable {V E : Type*} [Fintype V] [Fintype E]

theorem finite_interpolation_uniform (G : BondGraph V E) (d : ℕ) (x : ℕ → V)
    (hd : 2≤d) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c ε : ℝ} (hc : 0 < c) (hε : 0<ε) (hεp : ε≤p) (hεq : ε≤1-p)
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x j) (x k)))
    (s : ℕ) (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s)) :
    ∃ j<d, 0 < prob w (endpointEvent G (x j) (x (j+1)) s) ∧
      -Real.log (prob w (endpointEvent G (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/prob w (endpointEvent G (x 0) (x d) s))+Nat.clog 2 d+1) := by
  have hw := homogeneous_normalized w p h0 h1
  have hn := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  have hc1 : c≤1 := (hconn 0 1 (by omega) (by omega) (by omega)).trans (prob_le_one w hw hn _)
  obtain ⟨j,hj,hpos,hbound⟩ := finite_interpolation_index G d x hd hp w h0 h1 hc hconn s hδ
  exact ⟨j,hj,hpos,hbound.trans
    (interpolation_uniform_algebra hp hc hc1 hε hεp hεq hδ (prob_le_one w hw hn _) _)⟩

end CriticalPercolation.BinaryLaw
end
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

lemma real_eq_expect_indicator [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = FiniteProduct.expect (fun e => bitWeight (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← integral_law_eq_expect]
  exact (integral_indicator_one (.of_discrete)).symm

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

lemma twoClusterEvent_iff_endpoint [Fintype V] (ω : Set E) (u v : V) (s : ℕ) :
    ω ∈ G.twoClusterEvent u v s ↔ BinaryLaw.endpointEvent G u v s ω := by
  simp only [twoClusterEvent, Set.mem_inter_iff, Set.mem_ofPred_eq,
    clusterTail_iff_card, BinaryLaw.endpointEvent, and_assoc]

lemma finite_endpoint_prob [Fintype V] [Fintype E] (p : unitInterval) (u v : V) (s : ℕ) :
    FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
      (BinaryLaw.endpointEvent G u v s) = (G.law p).real (G.twoClusterEvent u v s) := by
  rw [law, ← BernoulliProduct.law_const, ← BernoulliProduct.prob_eq_real]
  congr 1
  funext ω
  exact propext (G.twoClusterEvent_iff_endpoint ω u v s).symm

theorem finite_interpolation_measure [Fintype V] [Fintype E]
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0 < c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real (G.twoClusterEvent (x 0) (x d) s)) :
    ∃ j<d, 0 < (G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real (G.twoClusterEvent (x 0) (x d) s))+Nat.clog 2 d+1) := by
  have h := BinaryLaw.finite_interpolation_uniform G d x hd hp
    (fun _ : E => BernoulliProduct.bitWeight p)
    (fun _ => by simp [BernoulliProduct.bitWeight])
    (fun _ => by simp [BernoulliProduct.bitWeight]) hc hε hεp hεq
  simp_rw [G.finite_endpoint_prob p] at h
  apply h
  intro j k hj hk hjk
  change c ≤ FiniteProduct.prob (fun _ : E => BernoulliProduct.bitWeight p)
    (fun ω => ω ∈ {η | (G.openGraph η).Reachable (x j) (x k)})
  rw [BernoulliProduct.prob_eq_real, BernoulliProduct.law_const]
  exact hconn j k hj hk hjk
  exact hδ

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_FiniteClusterTransport
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

lemma restrictVertices_cluster_image (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) (ω : Set E) (u : U) :
    Subtype.val '' ((G.restrictVertices U hU).cluster ω u) = G.cluster ω u.val := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (G.restrictVertices_reachable U hU ω u a).mp ha
  · intro hv
    have hmem := G.cluster_subset_support U hU u.property hv
    exact ⟨⟨v,hmem⟩,(G.restrictVertices_reachable U hU ω u ⟨v,hmem⟩).mpr hv,rfl⟩

lemma restrictVertices_clusterTail (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) (ω : Set E) (u : U) (n : ℕ) :
    ω ∈ (G.restrictVertices U hU).clusterTail u n ↔ ω ∈ G.clusterTail u.val n := by
  change _ ↔ ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster ω u.val ∧ n≤K.ncard
  rw [← G.restrictVertices_cluster_image U hU ω u]
  exact (finite_subset_size_image Subtype.val Subtype.val_injective _ n).symm

lemma restrictVertices_twoClusterEvent (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) (ω : Set E) (u v : U) (n : ℕ) :
    ω ∈ (G.restrictVertices U hU).twoClusterEvent u v n ↔ ω ∈ G.twoClusterEvent u.val v.val n := by
  simp only [twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.restrictVertices_reachable,G.restrictVertices_clusterTail]

end BondGraph
end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_FiniteEdgeInterpolation
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
variable {V E : Type*} (G : BondGraph V E)

theorem finite_edge_interpolation_measure [Fintype E]
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0 < c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real (G.twoClusterEvent (x 0) (x d) s)) :
    ∃ j<d, 0 < (G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s)) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real (G.twoClusterEvent (x 0) (x d) s))+Nat.clog 2 d+1) := by
  let U : Set V := Set.range (fun j : Fin (d+1) => x j.val) ∪
    ⋃ e : E, {v | v ∈ G.ends e}
  have hUf : U.Finite := (Set.finite_range _).union
    (Set.finite_iUnion (fun e => by
      convert (G.ends e).toFinset.finite_toSet using 1
      all_goals try with_reducible_and_instances rfl
      ext v
      exact Sym2.mem_toFinset.symm))
  let : Fintype U := hUf.fintype
  have hU : ∀ e v, v∈G.ends e → v∈U := by
    intro e v hv
    exact Or.inr (Set.mem_iUnion.mpr ⟨e,hv⟩)
  let R := G.restrictVertices U hU
  let y (j : ℕ) : U := ⟨x (min j d),Or.inl ⟨⟨min j d,by omega⟩,rfl⟩⟩
  have hy (j : ℕ) (hj : j≤d) : (y j).val=x j := by simp only [y,min_eq_left hj]
  have hreach (j k : ℕ) (hj : j≤d) (hk : k≤d) :
      (R.law p).real {ω | (R.openGraph ω).Reachable (y j) (y k)} =
        (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)} := by
    change (G.law p).real _ = _
    congr 1
    ext ω
    exact (G.restrictVertices_reachable U hU ω (y j) (y k)).trans (by simp only [hy j hj,hy k hk,Set.mem_ofPred_eq])
  have htwo (j k : ℕ) (hj : j≤d) (hk : k≤d) :
      (R.law p).real (R.twoClusterEvent (y j) (y k) s) =
        (G.law p).real (G.twoClusterEvent (x j) (x k) s) := by
    change (G.law p).real _ = _
    congr 1
    ext ω
    exact (G.restrictVertices_twoClusterEvent U hU ω (y j) (y k) s).trans
      (by rw [hy j hj,hy k hk])
  have hconn' : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (R.law p).real {ω | (R.openGraph ω).Reachable (y j) (y k)} := by
    intro j k hj hk hjk
    rw [hreach j k (by omega) hk]
    exact hconn j k hj hk hjk
  have hδ' : 0 < (R.law p).real (R.twoClusterEvent (y 0) (y d) s) := by
    rwa [htwo 0 d (by omega) le_rfl]
  obtain ⟨j,hj,hpos,hcost⟩ := R.finite_interpolation_measure d y hd p hp hc hε hεp hεq hconn' s hδ'
  rw [htwo j (j+1) (by omega) (by omega)] at hpos hcost
  rw [htwo 0 d (by omega) le_rfl] at hcost
  exact ⟨j,hj,hpos,hcost⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Criticality_RestrictedInterpolation
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
variable {V E : Type*} (G : BondGraph V E)

lemma restrictEdges_twoClusterEvent (S : Set E) (u v : V) (s : ℕ) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set S)) ⁻¹'
      ((G.restrictEdges S).twoClusterEvent u v s) =
        {ω | S ∩ ω ∈ G.twoClusterEvent u v s} := by
  ext ω
  simp only [Set.mem_preimage,twoClusterEvent,Set.mem_inter_iff,Set.mem_ofPred_eq,
    clusterTail,cluster,G.restrictEdges_openGraph]

lemma real_law_domRestrict (p : unitInterval) (S : Set E) (hS : S.Finite)
    (A : Set (Set S)) :
    ((G.restrictEdges S).law p).real A =
      (G.law p).real ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set S)) ⁻¹' A) := by
  let := hS.fintype
  have hr := BernoulliProduct.law_map_restrict (fun _ : E => p) S
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set S)) :=
    Measurable.of_eval (fun edge => measurable_set_mem edge.val)
  simp only [BernoulliProduct.law_const] at hr
  change (setBernoulli (Set.univ : Set S) p).real A = _
  rw [← hr,Measure.real,Measure.map_apply hmeas (.of_discrete)]
  rfl

lemma restrictEdges_twoCluster_real (p : unitInterval) (S : Set E) (hS : S.Finite)
    (u v : V) (s : ℕ) :
    ((G.restrictEdges S).law p).real ((G.restrictEdges S).twoClusterEvent u v s) =
      (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent u v s} := by
  rw [G.real_law_domRestrict p S hS,G.restrictEdges_twoClusterEvent]

lemma restrictEdges_reachable_real (p : unitInterval) (S : Set E) (hS : S.Finite) (u v : V) :
    ((G.restrictEdges S).law p).real {ω | ((G.restrictEdges S).openGraph ω).Reachable u v} =
      (G.law p).real {ω | (G.openGraph (S ∩ ω)).Reachable u v} := by
  rw [G.real_law_domRestrict p S hS]
  congr 1
  ext ω
  simp only [Set.mem_preimage,Set.mem_ofPred_eq,G.restrictEdges_openGraph]

theorem restricted_interpolation_measure_oai (S : Set E) (hS : S.Finite)
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0 < c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph (S ∩ ω)).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s}) :
    ∃ j<d, 0 < (G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s} ∧
      -Real.log ((G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x j) (x (j+1)) s}) ≤
        interpolationConstant c ε *
          (Real.log (1/(G.law p).real {ω | S ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s})+Nat.clog 2 d+1) := by
  let := hS.fintype
  have h := (G.restrictEdges S).finite_edge_interpolation_measure d x hd p hp hc hε hεp hεq
  simp_rw [G.restrictEdges_twoCluster_real p S hS,G.restrictEdges_reachable_real p S hS] at h
  exact h hconn s hδ

end CriticalPercolation.BondGraph
end
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_oai.{u_1, u_2}
