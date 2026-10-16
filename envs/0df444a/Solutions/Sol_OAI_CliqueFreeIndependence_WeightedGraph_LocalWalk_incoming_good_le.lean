-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.incoming_good_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:28:33.335413+00:00
-- url     : https://prove2.me/submissions/c1aca8b7-8968-40a0-80a6-f324f0003edd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/WalkEntropy.lean:L78-L143
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.incoming_good_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_stochastic

-- ---- from OAI.Combinatorics.CliqueFree.WeightedGraph ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

omit [Fintype V] in
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteEntropy ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteEntropy

variable {I : Type u} [Fintype I]

variable {J : Type v} [Fintype J]

/-- Mixing finitely many probability vectors. -/
lemma mix_isProb {a : J → ℝ} {p : J → I → ℝ} (ha : IsProb a)
    (hp : ∀ j, IsProb (p j)) : IsProb (fun i ↦ ∑ j, a j * p j i) := by
  refine ⟨fun i ↦ sum_nonneg fun j _ ↦ mul_nonneg (ha.1 j) ((hp j).1 i), ?_⟩
  rw [sum_comm]
  simp_rw [← mul_sum, fun j ↦ (hp j).2, mul_one]
  exact ha.2

end FiniteEntropy

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.EdgeState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance] OAI.CliqueFreeIndependence.WeightedGraph.edgeStateDecEq
namespace EdgeState
variable {G : SimpleGraph V}
lemma sum_eq (f : V → V → ℝ) :
    (∑ e : EdgeState G, f e.src e.dst) = ∑ u, ∑ v ∈ neighbors G u, f u v := by
  classical
  change (∑ e : {e : V × V // G.Adj e.1 e.2}, f e.val.1 e.val.2) = _
  rw [← Finset.sum_subtype (univ.filter fun e : V × V ↦ G.Adj e.1 e.2)
    (by simp) (fun e : V × V ↦ f e.1 e.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]

lemma sum_fiber (u : V) (f : V → ℝ) :
    (∑ e : EdgeState G, if e.src = u then f e.dst else 0) = ∑ v ∈ neighbors G u, f v := by
  classical
  rw [sum_eq (fun a b ↦ if a = u then f b else 0)]
  simp

end EdgeState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Reach ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

lemma subset_enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V) :
    A ⊆ enlarge G w t A := subset_union_left

lemma not_mem_enlarge (G : SimpleGraph V) (w : V → ℝ) (t : ℝ) (A : Finset V)
    {y : V} (hy : y ∉ enlarge G w t A) :
    y ∉ A ∧ mass w (A ∩ neighbors G y) < t := by
  simpa [enlarge, not_or, not_le] using hy

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteKernel ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI
lemma stochastic_one : Stochastic (1 : Kernel I) := by
  classical
  intro i
  constructor
  · intro j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  · simp [Matrix.one_apply]

lemma stochastic_mul {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q) :
    Stochastic (P * Q) := by
  intro i
  exact mix_isProb (hP i) hQ

lemma stochastic_pow {P : Kernel I} (hP : Stochastic P) (n : ℕ) : Stochastic (P ^ n) := by
  classical
  induction n with
  | zero => simpa using (stochastic_one (I := I))
  | succ n ih => simpa only [pow_succ] using stochastic_mul ih hP

lemma stochastic_lazy {P : Kernel I} (hP : Stochastic P) : Stochastic (lazy P) := by
  classical
  intro i
  constructor
  · intro j
    dsimp [lazy]
    have := (hP i).1 j
    split_ifs <;> positivity
  · change (∑ j, ((if i = j then (1 : ℝ) else 0) + P i j) / 2) = 1
    rw [← sum_div, sum_add_distrib]
    simp [(hP i).2]

omit [Fintype I] in
lemma lazy_eq (P : Kernel I) : lazy P = (1 / 2 : ℝ) • (1 + P) := by
  classical
  ext i j
  simp [lazy, Matrix.one_apply, div_eq_mul_inv, mul_comm]

lemma commute_lazy (P : Kernel I) : Commute P (lazy P) := by
  classical
  rw [lazy_eq]
  show P * ((1 / 2 : ℝ) • (1 + P)) = ((1 / 2 : ℝ) • (1 + P)) * P
  simp [mul_add, add_mul]

lemma smoothed_density {P : Kernel I} (hP : Stochastic P) {b : I → ℝ}
    (hb : ∀ i j, P i j ≤ b j) (n : ℕ) : ∀ i j, smoothed P n i j ≤ b j := by
  classical
  intro i j
  unfold smoothed
  rw [((commute_lazy P).pow_right n).eq, Matrix.mul_apply]
  have hQ := stochastic_pow (stochastic_lazy hP) n
  calc
    _ ≤ ∑ k, (lazy P ^ n) i k * b j :=
      sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (hb k j) ((hQ i).1 k)
    _ = b j := by rw [← sum_mul, (hQ i).2, one_mul]

variable {J : Type v}

omit [Fintype I] in
lemma preserves_lazy {label : I → J} {P : Kernel I} (hP : Preserves label P) :
    Preserves label (lazy P) := by
  intro i j hij
  have h : i ≠ j := fun h ↦ hij (congrArg label h)
  simp [lazy, h, hP i j hij]

end FiniteKernel

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.LocalWalk ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable (G : SimpleGraph V) (w : V → ℝ)

variable {G w}
lemma transition_fixed_src (e f : EdgeState G) (h : e.src ≠ f.src) :
    transition G w e f = 0 := by simp [transition, h]

lemma transition_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) :
    ∀ e f, transition G w e f ≤ x * vertexWeight G w f := by
  classical
  intro e f
  have hc0 : 0 < commonMass G w e.src e.dst := (one_div_pos.2 hx).trans_le (hc _ _ e.adj)
  dsimp [transition, vertexWeight]
  split_ifs
  · apply (div_le_iff₀ hc0).2
    have h := (div_le_iff₀ hx).1 (hc _ _ e.adj)
    nlinarith [mul_le_mul_of_nonneg_left h (hw f.dst).le]
  all_goals exact (mul_pos hx (hw _)).le

lemma smoothed_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v) (n : ℕ) :
    ∀ e f, smoothed (transition G w) n e f ≤ x * vertexWeight G w f := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  exact FiniteKernel.smoothed_density (transition_stochastic hw hc0) (transition_density hw hx hc) n

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WalkEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace LocalWalk
open FiniteEntropy FiniteKernel
variable {G : SimpleGraph V} {w : V → ℝ}

lemma sum_liftSet (u : V) (A : Finset V) (f : V → ℝ) :
    (∑ e ∈ liftSet (G := G) u A, f e.dst) = ∑ v ∈ A ∩ neighbors G u, f v := by
  rw [liftSet, sum_filter]
  have he : (∑ e : EdgeState G, if e.src = u ∧ e.dst ∈ A then f e.dst else 0) =
      ∑ e : EdgeState G, if e.src = u then (if e.dst ∈ A then f e.dst else 0) else 0 := by
    apply sum_congr rfl
    intro e _
    by_cases hs : e.src = u <;> by_cases hd : e.dst ∈ A <;> simp [hs, hd]
  rw [he, EdgeState.sum_fiber u (fun v ↦ if v ∈ A then f v else 0), ← sum_filter]
  congr 1
  ext v
  simp [and_comm]

lemma lazy_neighbor_density (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    (e f : EdgeState G) (h : e.dst ≠ f.dst) :
    lazy (transition G w) e f ≤ if G.Adj e.dst f.dst then x * w f.dst else 0 := by
  have hef : e ≠ f := fun he ↦ h (congrArg EdgeState.dst he)
  simp only [lazy, hef, ite_false, zero_add]
  have hp := transition_density hw hx hc e f
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hn := (transition_stochastic hw hc0 e).1 f
  by_cases hadj : G.Adj e.dst f.dst
  · rw [ite_eq_left hadj]
    change transition G w e f ≤ x * w f.dst at hp
    linarith
  · simp [transition, hadj]

lemma liftSet_adj_mass_le (hw : ∀ u, 0 ≤ w u) (u y : V) (A : Finset V) :
    (∑ z ∈ liftSet (G := G) u A, if G.Adj z.dst y then w z.dst else 0) ≤
      mass w (A ∩ neighbors G y) := by
  rw [sum_liftSet u A (fun z ↦ if G.Adj z y then w z else 0), ← sum_filter]
  have he : (A ∩ neighbors G u).filter (fun z ↦ G.Adj z y) =
      (A ∩ neighbors G y) ∩ neighbors G u := by
    ext z
    simp [G.adj_comm z y, and_assoc, and_comm]
  rw [he]
  exact mass_mono hw inter_subset_left

lemma incoming_good_le (hw : ∀ u, 0 < w u) {x : ℝ} (hx : 0 < x)
    (hc : ∀ u v, G.Adj u v → 1 / x ≤ commonMass G w u v)
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) (e : EdgeState G) (A : Finset V) :
    (∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
      ∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
      x ^ 2 * t * neighborMass G w e.src := by
  have hc0 : ∀ u v, G.Adj u v → 0 < commonMass G w u v :=
    fun u v huv ↦ (one_div_pos.2 hx).trans_le (hc u v huv)
  have hP := transition_stochastic hw hc0
  have hQ := stochastic_lazy hP
  have hpt := preserves_lazy (label := EdgeState.src) (transition_fixed_src (G := G) (w := w))
  have hrow (y : EdgeState G) (hy : y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ) :
      (∑ z ∈ liftSet (G := G) e.src A,
        smoothed (transition G w) n e z * lazy (transition G w) z y) ≤
        if y.src = e.src then x ^ 2 * t * w y.dst else 0 := by
    by_cases hsrc : y.src = e.src
    · rw [ite_eq_left hsrc]
      have hyout : y.dst ∉ enlarge G w t A := by
        intro h
        exact (mem_compl.1 hy) ((mem_liftSet _ _ _).2 ⟨hsrc, h⟩)
      have hymass := (not_mem_enlarge G w t A hyout).2.le
      calc
        _ ≤ ∑ z ∈ liftSet (G := G) e.src A,
            (if G.Adj z.dst y.dst then w z.dst else 0) * (x ^ 2 * w y.dst) := by
          apply sum_le_sum
          intro z hz
          have hzA := ((mem_liftSet _ _ _).1 hz).2
          have hzy : z.dst ≠ y.dst := by
            intro h
            apply hyout
            exact subset_enlarge G w t A (h ▸ hzA)
          have h1 := smoothed_density hw hx hc n e z
          have h2 := lazy_neighbor_density hw hx hc z y hzy
          change smoothed (transition G w) n e z ≤ x * w z.dst at h1
          have hm := mul_le_mul h1 h2 ((hQ z).1 y) (mul_pos hx (hw z.dst)).le
          by_cases hadj : G.Adj z.dst y.dst
          · simpa only [ite_eq_left hadj] using hm.trans_eq (by rw [ite_eq_left hadj]; ring)
          · simpa only [ite_eq_right hadj, mul_zero, zero_mul] using hm
        _ = (∑ z ∈ liftSet (G := G) e.src A,
            if G.Adj z.dst y.dst then w z.dst else 0) * (x ^ 2 * w y.dst) :=
          (sum_mul _ _ _).symm
        _ ≤ mass w (A ∩ neighbors G y.dst) * (x ^ 2 * w y.dst) :=
          mul_le_mul_of_nonneg_right (liftSet_adj_mass_le (fun u ↦ (hw u).le) _ _ _)
            (mul_nonneg (sq_nonneg x) (hw y.dst).le)
        _ ≤ t * (x ^ 2 * w y.dst) := mul_le_mul_of_nonneg_right hymass
          (mul_nonneg (sq_nonneg x) (hw y.dst).le)
        _ = _ := by ring
    · rw [ite_eq_right hsrc]
      apply le_of_eq
      apply sum_eq_zero
      intro z hz
      have hzs := ((mem_liftSet _ _ _).1 hz).1
      rw [hpt z y (fun h ↦ hsrc (h.symm.trans hzs)), mul_zero]
  calc
    _ ≤ ∑ y ∈ (liftSet (G := G) e.src (enlarge G w t A))ᶜ,
        if y.src = e.src then x ^ 2 * t * w y.dst else 0 := sum_le_sum hrow
    _ ≤ ∑ y : EdgeState G, if y.src = e.src then x ^ 2 * t * w y.dst else 0 := by
      apply sum_le_univ_sum_of_nonneg
      intro y
      split_ifs
      · exact mul_nonneg (mul_nonneg (sq_nonneg x) ht) (hw _).le
      · exact le_rfl
    _ = _ := by
      rw [EdgeState.sum_fiber e.src (fun y ↦ x ^ 2 * t * w y), ← mul_sum]
      rfl

end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq
open FiniteEntropy FiniteKernel


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.incoming_good_le.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.LocalWalk.incoming_good_le.{u}
