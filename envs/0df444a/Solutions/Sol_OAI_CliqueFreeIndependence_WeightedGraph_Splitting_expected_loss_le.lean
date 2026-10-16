-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.Splitting.expected_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:43:01.881917+00:00
-- url     : https://prove2.me/submissions/e6abed44-633d-4737-a99d-e7ad9151f467

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/SplittingLoss.lean:L90-L155
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.Splitting.expected_loss_le. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_transition_stochastic
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_LocalWalk_triangle_pair_sum

-- ---- from OAI.Combinatorics.CliqueFree.TriangleState ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace TriangleState
variable {G : SimpleGraph V}
omit [Fintype V] in
lemma weight_pos {w : V → ℝ} (hw : ∀ u, 0 < w u) (t : TriangleState G) :
    0 < weight w t := mul_pos (mul_pos (hw _) (hw _)) (hw _)

lemma sum_rotate (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (rotate t)) = ∑ t, weight w t * f t := by
  simpa only [rotateEquiv, Equiv.coe_fn_mk, weight_rotate] using rotateEquiv.sum_comp (fun t ↦ weight w t * f t)

lemma sum_swap (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (swap t)) = ∑ t, weight w t * f t := by
  simpa only [swapEquiv, Equiv.coe_fn_mk, weight_swap] using swapEquiv.sum_comp (fun t ↦ weight w t * f t)

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}

lemma sum_flip (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (flip t)) = ∑ t, weight w t * f t := by
  simpa only [flipEquiv, Equiv.coe_fn_mk, weight_flip] using
    flipEquiv.sum_comp (fun t ↦ weight w t * f t)

end TriangleState

namespace TriangleState
variable {G : SimpleGraph V}
lemma sum_edge_permutations (w : V → ℝ) (g : EdgeState G → ℝ) :
    (∑ t, weight w t * g t.edge12.rev) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge13) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge13.rev) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge23) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge23.rev) = (∑ t, weight w t * g t.edge12) := by
  refine ⟨sum_swap w (fun t ↦ g t.edge12), sum_flip w (fun t ↦ g t.edge12), ?_,
    sum_rotate w (fun t ↦ g t.edge12), ?_⟩
  · exact (sum_rotate w (fun t ↦ g (rotate t).edge12)).trans (sum_rotate w (fun t ↦ g t.edge12))
  · exact (sum_rotate w (fun t ↦ g (swap t).edge12)).trans (sum_swap w (fun t ↦ g t.edge12))
end TriangleState

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.WalkCoupling ----
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
lemma triangle_edge_sum [Nonempty (EdgeState G)] (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v) (f : EdgeState G → ℝ) :
    (∑ t : TriangleState G, TriangleState.weight w t * f t.edge12) =
      normalizer G w * ∑ e, law G w e * f e := by
  rw [triangle_pair_sum hw hc (fun e _ ↦ f e)]
  simp only [← sum_mul, (transition_stochastic hw hc _).2, one_mul]
end LocalWalk

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.FiniteCoupling ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteCoupling
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2
lemma sum_push (p : I → ℝ) (f : I → J) (g : J → ℝ) :
    ∑ y, push p f y * g y = ∑ i, p i * g (f i) := by
  simp only [push, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul]

lemma marginal_expectation {p : I → J → ℝ} {q : (I → J) → ℝ}
    (hm : ∀ i y, (∑ f, if f i = y then q f else 0) = p i y) (i : I) (g : J → ℝ) :
    (∑ f, q f * g (f i)) = ∑ y, p i y * g y := by
  have h := sum_push q (fun f ↦ f i) g
  simpa only [push, hm] using h.symm

lemma bad_and (p q : Prop) : bad (p ∧ q) ≤ bad p + bad q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [bad, hp, hq]

end FiniteCoupling

end CliqueFreeIndependence

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.SplittingLoss ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

attribute [local instance 10000] edgeStateDecEq

namespace Splitting
open FiniteCoupling
variable {G : SimpleGraph V}

omit [Fintype V] in
lemma bad_survives (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop)
    (t : TriangleState G) :
    bad (Survives F good t) ≤ bad (F t.edge12 = F t.edge13) +
      bad (F t.edge12.rev = F t.edge23) + bad (F t.edge13.rev = F t.edge23.rev) +
      bad (good t.edge12) + bad (good t.edge12.rev) + bad (good t.edge13) +
      bad (good t.edge13.rev) + bad (good t.edge23) + bad (good t.edge23.rev) := by
  unfold Survives
  have h1 := bad_and (F t.edge12 = F t.edge13)
    (F t.edge12.rev = F t.edge23 ∧ F t.edge13.rev = F t.edge23.rev ∧
      good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
      good t.edge23 ∧ good t.edge23.rev)
  have h2 := bad_and (F t.edge12.rev = F t.edge23)
    (F t.edge13.rev = F t.edge23.rev ∧ good t.edge12 ∧ good t.edge12.rev ∧
      good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h3 := bad_and (F t.edge13.rev = F t.edge23.rev)
    (good t.edge12 ∧ good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧
      good t.edge23 ∧ good t.edge23.rev)
  have h4 := bad_and (good t.edge12)
    (good t.edge12.rev ∧ good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h5 := bad_and (good t.edge12.rev)
    (good t.edge13 ∧ good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h6 := bad_and (good t.edge13) (good t.edge13.rev ∧ good t.edge23 ∧ good t.edge23.rev)
  have h7 := bad_and (good t.edge13.rev) (good t.edge23 ∧ good t.edge23.rev)
  have h8 := bad_and (good t.edge23) (good t.edge23.rev)
  linarith

lemma bad_mass_le {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (F : EdgeState G → EdgeState G) (good : EdgeState G → Prop) :
    (∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F good t)) ≤
      3 * (∑ t, TriangleState.weight w t * bad (F t.edge12 = F t.edge13)) +
      6 * (∑ t, TriangleState.weight w t * bad (good t.edge12)) := by
  have h := sum_le_sum (s := univ) fun t _ ↦
    mul_le_mul_of_nonneg_left (bad_survives F good t)
      (show 0 ≤ TriangleState.weight w t from
        mul_nonneg (mul_nonneg (hw t.first) (hw t.second)) (hw t.third))
  simp only [mul_add, sum_add_distrib] at h
  obtain ⟨h1,h2,h3,h4,h5⟩ := TriangleState.sum_edge_permutations w (fun e ↦ bad (good e))
  have hc2 : (∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12.rev = F t.edge23)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12 = F t.edge13) := by
    have h := TriangleState.sum_rotate w (fun t ↦ bad (F t.edge12 = F t.edge13))
    convert h using 1
    apply sum_congr rfl
    intro t _
    change _ * bad (F t.edge12.rev = F t.edge23) = _ * bad (F t.edge23 = F t.edge12.rev)
    rw [eq_comm (a := F t.edge23)]
  have hc3 : (∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge13.rev = F t.edge23.rev)) =
      ∑ t : TriangleState G, TriangleState.weight w t * bad (F t.edge12 = F t.edge13) :=
    (TriangleState.sum_rotate w (fun t ↦ bad (F (TriangleState.rotate t).edge12 = F (TriangleState.rotate t).edge13))).trans
      (TriangleState.sum_rotate w (fun t ↦ bad (F t.edge12 = F t.edge13)))
  rw [h1,h2,h3,h4,h5,hc2,hc3] at h
  linarith

open FiniteEntropy FiniteKernel LocalWalk

/-- The finite-law aggregate of all corner and incidence losses. -/
lemma expected_loss_le [Nonempty (EdgeState G)] {w : V → ℝ} (hw : ∀ u, 0 < w u)
    (hc : ∀ u v, G.Adj u v → 0 < commonMass G w u v)
    (K : Kernel (EdgeState G)) {q : (EdgeState G → EdgeState G) → ℝ}
    (hq : Law q) (hm : ∀ i y, (∑ F, if F i = y then q F else 0) = K i y)
    (hp : ∀ i j, (∑ F, if F i ≠ F j then q F else 0) ≤ 2 * tv (K i) (K j))
    (good : (EdgeState G → EdgeState G) → EdgeState G → Prop)
    (b : EdgeState G → EdgeState G → Prop)
    (hb : ∀ F e, good F e ↔ b e (F e)) :
    (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (Survives F (good F) t)) ≤
      normalizer G w *
        (6 * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) +
         6 * (∑ e, law G w e * ∑ y, K e y * bad (b e y))) := by
  have hcoup (i j : EdgeState G) : (∑ F, q F * bad (F i = F j)) ≤ 2 * tv (K i) (K j) := by
    convert hp i j using 1
    apply sum_congr rfl
    intro F _
    by_cases h : F i = F j <;> simp [bad, h]
  have hadm (e : EdgeState G) : (∑ F, q F * bad (good F e)) = ∑ y, K e y * bad (b e y) := by
    simp_rw [hb]
    exact marginal_expectation hm e (fun y ↦ bad (b e y))
  have hcorner : (∑ F, q F * ∑ t : TriangleState G,
      TriangleState.weight w t * bad (F t.edge12 = F t.edge13)) ≤
      2 * normalizer G w * (∑ e, law G w e * ∑ z, transition G w e z * tv (K e) (K z)) := by
    calc
      _ = ∑ t : TriangleState G, TriangleState.weight w t * ∑ F, q F * bad (F t.edge12 = F t.edge13) := by
        simp only [mul_sum]
        rw [sum_comm]
        congr 1
        ext t
        apply sum_congr rfl
        intro F _
        ring
      _ ≤ ∑ t : TriangleState G, TriangleState.weight w t * (2 * tv (K t.edge12) (K t.edge13)) :=
        sum_le_sum fun t _ ↦ mul_le_mul_of_nonneg_left (hcoup _ _) (TriangleState.weight_pos hw t).le
      _ = 2 * ∑ t : TriangleState G, TriangleState.weight w t * tv (K t.edge12) (K t.edge13) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro t _
        ring
      _ = _ := by
        rw [triangle_pair_sum hw hc (fun e z ↦ tv (K e) (K z))]
        ring
  have hincidence : (∑ F, q F * ∑ t : TriangleState G, TriangleState.weight w t * bad (good F t.edge12)) =
      normalizer G w * ∑ e, law G w e * ∑ y, K e y * bad (b e y) := by
    calc
      _ = ∑ t : TriangleState G, TriangleState.weight w t * ∑ F, q F * bad (good F t.edge12) := by
        simp only [mul_sum]
        rw [sum_comm]
        congr 1
        ext t
        apply sum_congr rfl
        intro F _
        ring
      _ = _ := by simp_rw [hadm]; exact triangle_edge_sum hw hc (fun e ↦ ∑ y, K e y * bad (b e y))
  have h := sum_le_sum (s := univ) fun F _ ↦
    mul_le_mul_of_nonneg_left (bad_mass_le (fun u ↦ (hw u).le) F (good F)) (hq.1 F)
  simp only [mul_add, sum_add_distrib, ← mul_assoc] at h
  have hid (a : ℝ) (f : (EdgeState G → EdgeState G) → ℝ) :
      (∑ F, q F * a * f F) = a * ∑ F, q F * f F := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro F _
    ring
  rw [hid, hid, hincidence] at h
  nlinarith

end Splitting

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
attribute [local instance 10000] edgeStateDecEq
open FiniteCoupling
open FiniteEntropy FiniteKernel LocalWalk


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.expected_loss_le.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.Splitting.expected_loss_le.{u}
