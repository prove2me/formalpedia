-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:01:36.989242+00:00
-- url     : https://prove2.me/submissions/a1c60104-0d8e-4a91-b2fb-cab1b86a9a33

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/DisjointCross.lean:L108-L151
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_disjoint. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_log_multiplier_le
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_sparse_multipliers_on
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_variational_cross_lottery

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
lemma mass_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ mass w A := sum_nonneg fun v _ ↦ hw v

omit [Fintype V] in
lemma crossMass_le_product (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v)
    (A B : Finset V) : crossMass G w A B ≤ mass w A * mass w B := by
  classical
  unfold crossMass mass
  rw [sum_mul_sum]
  exact sum_le_sum fun u _ ↦ sum_le_sum fun v _ ↦ by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hw u) (hw v)

end CliqueFreeIndependence.WeightedGraph

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
end EdgeState

lemma growth_nonneg {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) : 0 ≤ growth x s :=
  mul_nonneg hs (add_nonneg hx (le_max_left _ _))

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.DisjointCross ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
open Lottery
universe u
variable {V : Type u} [Fintype V]

lemma cross_error_le {s t x : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hslo : Real.exp (-x) ≤ s) (hsup : s ≤ Real.exp x) (htup : t ≤ Real.exp x) :
    s^2 + t^2/2 + t ≤ 3 * Real.exp (4*x) * x * s := by
  have hx0 : 0 ≤ x := by linarith
  have h1 : s ≤ Real.exp (4*x) := hsup.trans (Real.exp_le_exp.2 (by linarith))
  have hss : s^2 ≤ Real.exp (4*x)*s := by nlinarith [mul_le_mul_of_nonneg_right h1 hs]
  have hks : Real.exp (3*x) ≤ Real.exp (4*x)*s := by
    calc
      _ = Real.exp (4*x)*Real.exp (-x) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hslo (Real.exp_pos _).le
  have ht1 : t ≤ Real.exp (4*x)*s :=
    htup.trans ((Real.exp_le_exp.2 (by linarith : x ≤ 3*x)).trans hks)
  have ht2 : t^2 ≤ Real.exp (4*x)*s := by
    calc
      _ ≤ (Real.exp x)^2 := sq_le_sq₀ ht (Real.exp_pos x).le |>.2 htup
      _ = Real.exp (2*x) := by rw [sq,← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (3*x) := Real.exp_le_exp.2 (by linarith)
      _ ≤ _ := hks
  have hscale := mul_le_mul_of_nonneg_left hx (mul_nonneg (Real.exp_pos (4*x)).le hs)
  nlinarith

lemma optimizer_cross_disjoint_moderate (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hslo : Real.exp (-x) ≤ mass w S) (hsup : mass w S ≤ Real.exp x)
    (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (8 + 10*(k:ℝ) + (k:ℝ)^2)*x*mass w S := by
  have hwpos := fun v ↦ (optimizer_stationary hw v).1
  have hεhalf : Real.exp (-8*x) ≤ 1/2 := by
    have hl : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      linarith
    calc
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 1/2 := by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num
  obtain ⟨L,hp,hb,hm,he⟩ := sparse_multipliers_on k G hwpos S hfree (Real.exp_pos (-8*x)) hεhalf
  have h := variational_cross_lottery G hw S D hSD L hp (Real.exp_pos (4*x)).le hb hm he
  have hcancel : (Real.exp (4*x))^2 * Real.exp (-8*x) = 1 := by
    rw [sq,← Real.exp_add,← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  rw [hcancel,one_mul] at h
  have hlog := log_multiplier_le k hx
  have hw0 := fun v ↦ (hwpos v).le
  have hs := mass_nonneg hw0 S
  have ht := mass_nonneg hw0 D
  have hlogs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlog (Real.exp_pos (4*x)).le) hs
  have herr := cross_error_le hx hs ht hslo hsup htup
  apply (mul_le_mul_iff_right₀ (Real.exp_pos (4*x))).1
  nlinarith only [h,hlogs,herr]

end CliqueFreeIndependence.WeightedGraph

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma optimizer_cross_disjoint (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (S D : Finset V) (hSD : Disjoint S D)
    (hfree : G.CliqueFreeOn (↑S) (k+2)) {x : ℝ} (hx : 1 ≤ x)
    (hsup : mass w S ≤ Real.exp x) (htup : mass w D ≤ Real.exp x) :
    crossMass G w S D ≤ (4*((k:ℝ)+2)^2)*growth x (mass w S) := by
  have hw0 := fun v ↦ (optimizer_stationary hw v).1.le
  have hs := mass_nonneg hw0 S
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hcoeff : 8+10*(k:ℝ)+(k:ℝ)^2 ≤ 4*((k:ℝ)+2)^2 := by nlinarith
  have hcoeff0 : 0 ≤ 8+10*(k:ℝ)+(k:ℝ)^2 := by positivity
  rcases hs.eq_or_lt with hs | hs
  · have hc := crossMass_le_product G hw0 S D
    simpa [← hs] using hc
  by_cases hlo : Real.exp (-x) ≤ mass w S
  · have h := optimizer_cross_disjoint_moderate k G hw S D hSD hfree hx hlo hsup htup
    have hg : x*mass w S ≤ growth x (mass w S) := by
      unfold growth
      nlinarith [mul_nonneg hs.le (le_max_left 0 (Real.log (1/mass w S)))]
    calc
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*(x*mass w S) := by nlinarith only [h]
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*growth x (mass w S) := mul_le_mul_of_nonneg_left hg hcoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (growth_nonneg (by linarith) hs.le)
  · let y := Real.log (1/mass w S)
    have hxy : x ≤ y := by
      have hlog := Real.log_le_log hs (le_of_not_ge hlo)
      rw [Real.log_exp] at hlog
      dsimp [y]
      rw [one_div,Real.log_inv]
      linarith
    have hy : 1 ≤ y := hx.trans hxy
    have hsy : Real.exp (-y) = mass w S := by
      dsimp [y]
      rw [one_div,Real.log_inv,neg_neg,Real.exp_log hs]
    have h := optimizer_cross_disjoint_moderate k G hw S D hSD hfree hy hsy.le
      (hsup.trans (Real.exp_le_exp.2 hxy)) (htup.trans (Real.exp_le_exp.2 hxy))
    have hg : y*mass w S ≤ growth x (mass w S) := by
      unfold growth
      have hmax := le_max_right 0 y
      change y*mass w S ≤ mass w S*(x+max 0 y)
      nlinarith [mul_le_mul_of_nonneg_right hmax hs.le]
    calc
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*(y*mass w S) := by nlinarith only [h]
      _ ≤ (8+10*(k:ℝ)+(k:ℝ)^2)*growth x (mass w S) := mul_le_mul_of_nonneg_left hg hcoeff0
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff (growth_nonneg (by linarith) hs.le)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_disjoint.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_disjoint.{u}
