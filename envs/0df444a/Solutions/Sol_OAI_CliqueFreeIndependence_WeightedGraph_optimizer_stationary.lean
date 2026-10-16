-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.optimizer_stationary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:22:37.883174+00:00
-- url     : https://prove2.me/submissions/7d382273-bc2d-48c7-8d42-3003a883562c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Optimizer.lean:L179-L216
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.optimizer_stationary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer

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

lemma neighborMass_nonneg (G : SimpleGraph V) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (u : V) :
    0 ≤ neighborMass G w u := mass_nonneg hw _

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.Optimizer ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma edgeForm_self (G : SimpleGraph V) (a : V → ℝ) : edgeForm G a a = 2 * edgeMass G a := by
  simp only [edgeForm,edgeMass,crossMass]
  ring

lemma edgeForm_symm (G : SimpleGraph V) (a b : V → ℝ) : edgeForm G a b = edgeForm G b a := by
  unfold edgeForm
  rw [sum_comm]
  simp_rw [G.adj_comm,mul_comm]

lemma edgeForm_add_left (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G (a+b) c = edgeForm G a c + edgeForm G b c := by
  unfold edgeForm
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro u _
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  split_ifs <;> simp [Pi.add_apply,add_mul]

lemma edgeForm_add_right (G : SimpleGraph V) (a b c : V → ℝ) :
    edgeForm G a (b+c) = edgeForm G a b + edgeForm G a c := by
  rw [edgeForm_symm,edgeForm_add_left,edgeForm_symm _ b,edgeForm_symm _ c]

lemma edgeForm_neighbor (G : SimpleGraph V) (a b : V → ℝ) :
    edgeForm G a b = ∑ u, a u * neighborMass G b u := by
  simp only [edgeForm,neighborMass,mass,neighbors,sum_filter,mul_sum,mul_ite,mul_zero]

lemma edgeMass_add (G : SimpleGraph V) (a b : V → ℝ) :
    edgeMass G (a+b) = edgeMass G a + edgeMass G b + edgeForm G a b := by
  have h := edgeForm_self G (a+b)
  rw [edgeForm_add_left,edgeForm_add_right,edgeForm_add_right,edgeForm_self,edgeForm_self,
    edgeForm_symm G b a] at h
  linarith

lemma edgeForm_spike [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    edgeForm G (spike v t) w = t * neighborMass G w v := by
  rw [edgeForm_neighbor]
  simp [spike,ite_mul]

lemma edgeMass_spike [DecidableEq V] (G : SimpleGraph V) (v : V) (t : ℝ) :
    edgeMass G (spike v t) = 0 := by
  have h := edgeForm_self G (spike v t)
  rw [edgeForm_spike] at h
  have hn : neighborMass G (spike v t) v = 0 := by
    simp [neighborMass,mass,neighbors,spike]
  rw [hn] at h
  linarith

omit [Fintype V] in
lemma update_eq_add_spike [DecidableEq V] (w : V → ℝ) (v : V) (t : ℝ) :
    Function.update w v t = w + spike v (t-w v) := by
  funext u
  by_cases h : u = v <;> simp [Function.update,spike,h]

lemma edgeMass_update [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    edgeMass G (Function.update w v t) = edgeMass G w + (t-w v)*neighborMass G w v := by
  rw [update_eq_add_spike,edgeMass_add,edgeMass_spike,edgeForm_symm,edgeForm_spike]
  ring

lemma potential_update [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (v : V) (t : ℝ) :
    potential G (Function.update w v t) - potential G w =
      vertexPotential t - vertexPotential (w v) - (t-w v)*neighborMass G w v := by
  have hs : (∑ u, vertexPotential (Function.update w v t u)) =
      ∑ u, vertexPotential (w u) + (vertexPotential t - vertexPotential (w v)) := by
    rw [← add_sum_erase _ _ (mem_univ v), ← add_sum_erase _ _ (mem_univ v)]
    simp only [Function.update_self]
    have h : (∑ u ∈ univ.erase v, vertexPotential (Function.update w v t u)) =
        ∑ u ∈ univ.erase v, vertexPotential (w u) := by
      apply sum_congr rfl
      intro u hu
      rw [Function.update_of_ne (by simpa using (mem_erase.1 hu).1)]
    rw [h]
    ring
  unfold potential
  rw [hs,edgeMass_update]
  ring

lemma optimizer_stationary {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w) (v : V) :
    0 < w v ∧ Real.log (1/w v) = neighborMass G w v ∧ w v ≤ 1 := by
  classical
  let N := neighborMass G w v
  let a := Real.exp (-N)
  have ha : 0 < a := Real.exp_pos _
  have hN : 0 ≤ N := neighborMass_nonneg G hw.1 v
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hloga : Real.log a = -N := Real.log_exp _
  have hmax := hw.2 (Function.update w v a) (fun u ↦ by
    by_cases h : u = v
    · subst u; simpa using ha.le
    · simpa [h] using hw.1 u)
  have heq := potential_update G w v a
  have hbound : a ≤ w v * (1-Real.log (w v)-N) := by
    rw [vertexPotential,vertexPotential,hloga] at heq
    dsimp [N] at *
    nlinarith only [hmax,heq]
  have hwv : 0 < w v := by
    have h0 := hw.1 v
    by_contra hn
    have hz : w v = 0 := le_antisymm (le_of_not_gt hn) h0
    simp only [hz,zero_mul] at hbound
    linarith
  have hwa : w v = a := by
    by_contra hn
    have hdiv : a / w v ≠ 1 := by
      intro he
      exact hn ((div_eq_one_iff_eq hwv.ne').1 he).symm
    have hl := Real.log_lt_sub_one_of_pos (div_pos ha hwv) hdiv
    rw [Real.log_div ha.ne' hwv.ne',hloga] at hl
    have hh := mul_lt_mul_of_pos_left hl hwv
    have hid : w v * (a / w v - 1) = a-w v := by field_simp
    rw [hid] at hh
    nlinarith
  refine ⟨hwv,?_,hwa ▸ ha1⟩
  rw [one_div,Real.log_inv,hwa,hloga]
  simp [N]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_stationary.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_stationary.{u}
