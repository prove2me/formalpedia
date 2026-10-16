-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.optimizer_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:26:35.91562+00:00
-- url     : https://prove2.me/submissions/18a39541-604f-439e-bf79-bbfbaef89948

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/OptimizerBounds.lean:L81-L112
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.optimizer_edge_bound. The node keeps its source
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

lemma edgeForm_neighbor (G : SimpleGraph V) (a b : V → ℝ) :
    edgeForm G a b = ∑ u, a u * neighborMass G b u := by
  simp only [edgeForm,neighborMass,mass,neighbors,sum_filter,mul_sum,mul_ite,mul_zero]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.OptimizerBounds ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma sum_log_le_log_sum {p x : V → ℝ} (hp : ∀ v, 0 ≤ p v)
    (hs : ∑ v, p v = 1) (hx : ∀ v, 0 < x v) :
    (∑ v, p v * Real.log (x v)) ≤ Real.log (∑ v, p v * x v) := by
  simpa only [smul_eq_mul] using strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := univ) (w := p) (p := x) (fun v _ ↦ hp v) hs (fun v _ ↦ hx v)

lemma card_neighbors (G : SimpleGraph V) (v : V) : (neighbors G v).card = G.degree v := by
  classical
  have he : neighbors G v = G.neighborFinset v := by ext u; simp
  rw [he, G.card_neighborFinset_eq_degree]

lemma sum_neighborMass (G : SimpleGraph V) (w : V → ℝ) :
    (∑ v, neighborMass G w v) = ∑ v, (G.degree v : ℝ) * w v := by
  classical
  simp only [neighborMass, mass, neighbors, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  simp_rw [G.adj_comm]
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul]
  rw [← card_neighbors G v]
  rfl

lemma optimizer_total_weight {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ : ℝ} (hΔ : 3 ≤ Δ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ) / Δ ≤ ∑ v, w v := by
  have hn : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hW : 0 < ∑ v, w v := sum_pos (fun v _ ↦ hwpos v) univ_nonempty
  have hp : (∑ _v : V, (Fintype.card V : ℝ)⁻¹) = 1 := by
    simp [hn.ne']
  have hj := sum_log_le_log_sum (fun _v ↦ (inv_pos.2 hn).le) hp hwpos
  simp only [← mul_sum] at hj
  have he : (∑ v, Real.log (w v)) = -∑ v, neighborMass G w v := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro v _
    have hv := (optimizer_stationary hw v).2.1
    rw [one_div, Real.log_inv] at hv
    linarith
  rw [he, sum_neighborMass] at hj
  have hd := sum_le_sum (s := univ) fun v _ ↦ mul_le_mul_of_nonneg_right (hdeg v) (hw.1 v)
  rw [← mul_sum] at hd
  have hJ : Real.log ((Fintype.card V : ℝ) / (∑ v, w v)) ≤
      Δ * (∑ v, w v) / (Fintype.card V : ℝ) := by
    rw [Real.log_div hn.ne' hW.ne']
    rw [Real.log_mul (inv_ne_zero hn.ne') hW.ne', Real.log_inv] at hj
    have hm := mul_le_mul_of_nonneg_left hd (inv_pos.2 hn).le
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hΔpos : 0 < Δ := by linarith
  have hl : 1 < Real.log Δ := (Real.lt_log_iff_exp_lt hΔpos).2
    (Real.exp_one_lt_three.trans_le hΔ)
  by_contra h
  have hlt : (∑ v, w v) < (Fintype.card V : ℝ) / Δ := lt_of_not_ge h
  have hmul : Δ * (∑ v, w v) < Fintype.card V := by
    nlinarith [(lt_div_iff₀ hΔpos).1 hlt]
  have hlog := Real.log_lt_log hΔpos ((lt_div_iff₀ hW).2 hmul)
  have hfrac : Δ * (∑ v, w v) / (Fintype.card V : ℝ) < 1 :=
    (div_lt_one hn).2 hmul
  linarith

lemma optimizer_edge_bound {G : SimpleGraph V} {w : V → ℝ} (hw : IsOptimizer G w)
    [Nonempty V] {Δ : ℝ} (hΔ : 3 ≤ Δ) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    2 * edgeMass G w ≤ Real.log Δ * (∑ v, w v) := by
  have hn : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.2 Fintype.card_pos
  have hwpos (v : V) : 0 < w v := (optimizer_stationary hw v).1
  have hW : 0 < ∑ v, w v := sum_pos (fun v _ ↦ hwpos v) univ_nonempty
  have hp : (∑ v, w v / (∑ u, w u)) = 1 := by rw [← sum_div, div_self hW.ne']
  have hj := sum_log_le_log_sum (fun v ↦ (div_pos (hwpos v) hW).le) hp
    (fun v ↦ one_div_pos.2 (hwpos v))
  have hright : (∑ v, w v / (∑ u, w u) * (1 / w v)) =
      (Fintype.card V : ℝ) / (∑ v, w v) := by
    calc
      _ = ∑ _v : V, 1 / (∑ u, w u) := by
        apply sum_congr rfl
        intro v _
        field_simp [(hwpos v).ne']
      _ = _ := by simp [div_eq_mul_inv]
  have hleft : (∑ v, w v / (∑ u, w u) * Real.log (1 / w v)) =
      2 * edgeMass G w / (∑ v, w v) := by
    rw [← edgeForm_self, edgeForm_neighbor, sum_div]
    apply sum_congr rfl
    intro v _
    rw [(optimizer_stationary hw v).2.1]
    ring
  rw [hleft, hright] at hj
  have htotal := optimizer_total_weight hw hΔ hdeg
  have hΔpos : 0 < Δ := by linarith
  have hm : (Fintype.card V : ℝ) / (∑ v, w v) ≤ Δ := by
    apply (div_le_iff₀ hW).2
    nlinarith [(div_le_iff₀ hΔpos).1 htotal]
  have hh := hj.trans (Real.log_le_log (div_pos hn hW) hm)
  exact (div_le_iff₀ hW).1 hh

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_edge_bound.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_edge_bound.{u}
