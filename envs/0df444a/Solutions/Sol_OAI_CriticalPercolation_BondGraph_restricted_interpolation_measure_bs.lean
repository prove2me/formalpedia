-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T14:12:56.690657+00:00
-- url     : https://prove2.me/submissions/a809a136-e626-456b-93fc-b887ca6b66df

import Mathlib
import Definitions.Def_OAIQ078B002
import Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_event_bound_bs

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
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hl : 0 ≤ l := add_nonneg h8 (le_max_left _ _)
  have hcoef : 0 ≤ A*l+B*Real.log 4 := add_nonneg (mul_nonneg hA hl) (mul_nonneg hB h4)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hrT : r≤T := by dsimp [T]; linarith
  have hnT : (n:ℝ)≤T := by dsimp [T,r]; linarith
  calc
    _ ≤ A*(r+n*(Real.log 8+Real.log (1/c)))+B*(n*Real.log 4) := by
      rw [mul_assoc _ (n:ℝ) (Real.log 4)]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right
        · dsimp [A]; linarith
        · exact add_nonneg hr (mul_nonneg hn (add_nonneg h8 hc'))
      · apply mul_le_mul_of_nonneg_right
        · dsimp [B]; linarith
        · exact mul_nonneg hn h4
    _ ≤ A*(r+n*l)+B*(n*Real.log 4) := by
      apply add_le_add ?_ le_rfl
      apply mul_le_mul_of_nonneg_left _ hA
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_max_right _ _)) hn
    _ = A*r+(A*l+B*Real.log 4)*n := by ring
    _ ≤ A*T+(A*l+B*Real.log 4)*T :=
      add_le_add (mul_le_mul_of_nonneg_left hrT hA) (mul_le_mul_of_nonneg_left hnT hcoef)
    _ = _ := by dsimp [A,B,l,r,T,interpolationConstant]; ring

end CriticalPercolation
end
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_GraphGeometry_RestrictVertices
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

end CriticalPercolation.BondGraph

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

end CriticalPercolation.BondGraph

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
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
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

lemma density_record
    (hr₀ : ∀ ω η, G.clusterObject ω ({x 0,x d} : Set V) =
      G.clusterObject η {x 0,x d} → r₀ ω = r₀ η)
    (n : ℕ) (h : History E n) (ω η : E → Prop)
    (he : G.clusterObject ω (anchorSet d x n h) = G.clusterObject η (anchorSet d x n h)) :
    density G order d x p w r₀ n h ω = density G order d x p w r₀ n h η := by
  induction n with
  | zero =>
    apply hr₀
    convert he using 2 <;> ext v <;> simp [anchorSet,anchors,or_comm]
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

end ExactLaw

end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinarySupport
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

variable {V E : Type*} (G : BondGraph V E)

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

lemma pushMass_sum (f : X → Y) (P : X → ℝ) :
    ∑ y, pushMass f P y = ∑ x, P x := by
  classical
  simp only [pushMass]
  rw [Finset.sum_comm]
  simp

end CriticalPercolation.FiniteEntropy

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

lemma fixedDescriptor_card (n : ℕ) : Fintype.card (FixedDescriptor n) = 8^n := by
  simp only [FixedDescriptor,Fintype.card_fun,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]

section Finite
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ)

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

end Finite
end CriticalPercolation.BinaryLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ078_BS.CriticalPercolation_Entropy_BinaryCostBound
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
open FiniteProduct BondGraph BinaryInterpolation ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

local instance costBoundFinDec_r98dc1d_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteInterpolation
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
open FiniteProduct BondGraph BinaryInterpolation ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E]

lemma allDarts_good (G : BondGraph V E) : LazyDFS.GoodDarts G (allDarts G) := by
  intro a ha
  simpa only [allDarts,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using ha

lemma allDarts_exhaustive (G : BondGraph V E) : LazyDFS.Exhaustive G (allDarts G) := by
  intro v e t h
  simp only [allDarts,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and]
  exact h

local instance interpolationFinDec_r98dc1d_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
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
  have he := conditioned_event_bound_bs G order d x p w s n D (allDarts_good G)
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteInterpolationUniform
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_FiniteEdgeInterpolation
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
-- module Solutions.OAIQ078_BS.CriticalPercolation_Criticality_RestrictedInterpolation
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

theorem restricted_interpolation_measure_bs_oai (S : Set E) (hS : S.Finite)
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

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.restricted_interpolation_measure_bs_oai.{u_1, u_2}
