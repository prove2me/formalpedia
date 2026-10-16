-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.optimizer_divergence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:24:17.102386+00:00
-- url     : https://prove2.me/submissions/5e190ffb-a1d1-4fc5-ab46-c8496dd8cb08

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Optimizer.lean:L218-L244
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.optimizer_divergence. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary

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

/-- Expansion around a stationary positive maximizer. -/
lemma optimizer_divergence {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    0 ≤ potential G w - potential G q ∧
      potential G w - potential G q =
        (∑ v, (q v * Real.log (q v / w v) - q v + w v)) + edgeMass G (q-w) := by
  refine ⟨sub_nonneg.2 (hw.2 q hq),?_⟩
  have hsum (v : V) : vertexPotential (w v) - vertexPotential (q v) +
      (q v-w v)*neighborMass G w v = q v*Real.log (q v/w v) - q v + w v := by
    obtain ⟨hwv,hstat,_⟩ := optimizer_stationary hw v
    rw [one_div,Real.log_inv] at hstat
    rcases (hq v).eq_or_lt with hz | hqv
    · simp [← hz,vertexPotential,hstat.symm]
      ring
    · rw [Real.log_div hqv.ne' hwv.ne']
      unfold vertexPotential
      rw [← hstat]
      ring
  have he := edgeMass_add G (q-w) w
  have hqw : q-w+w = q := sub_add_cancel _ _
  rw [hqw,edgeForm_neighbor] at he
  simp only [Pi.sub_apply] at he
  have hs := congrArg (fun f : V → ℝ ↦ ∑ v, f v) (funext hsum)
  simp only [sum_add_distrib,sum_sub_distrib] at hs
  unfold potential
  simp only [sum_add_distrib,sum_sub_distrib]
  linarith

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_divergence.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_divergence.{u}
