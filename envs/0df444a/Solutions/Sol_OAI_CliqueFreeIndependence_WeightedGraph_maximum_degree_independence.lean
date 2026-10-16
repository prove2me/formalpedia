-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_independence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:03:33.399335+00:00
-- url     : https://prove2.me/submissions/ae2cb879-0c00-4954-a4d3-721d61e50e7c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/MaxDegree.lean:L69-L85
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_independence. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_CliqueFree_VertexSplitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Peeling
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_maximum_degree_potential_bound

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

lemma card_neighbors (G : SimpleGraph V) (v : V) : (neighbors G v).card = G.degree v := by
  classical
  have he : neighbors G v = G.neighborFinset v := by ext u; simp
  rw [he, G.card_neighborFinset_eq_degree]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.MaxDegree ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

lemma log_le_one_add_quarter {t : ℝ} (ht : 0 < t) : Real.log t ≤ 1+t/4 := by
  have h4 : Real.log 4 ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log 4 = 2*Real.log 2 := by
      rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hh := Real.log_le_sub_one_of_pos (div_pos ht (by norm_num : (0 : ℝ) < 4))
  rw [Real.log_div ht.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hh
  linarith

lemma neighborMass_const (G : SimpleGraph V) (p : ℝ) (v : V) :
    neighborMass G (fun _ ↦ p) v = (G.degree v : ℝ)*p := by
  simp only [neighborMass,mass,sum_const,nsmul_eq_mul,card_neighbors]

lemma edgeMass_const_le (G : SimpleGraph V) {Δ : ℝ}
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) (p : ℝ) :
    edgeMass G (fun _ ↦ p) ≤ (Fintype.card V : ℝ)*Δ*p^2/2 := by
  have hs := sum_le_sum (s := univ) fun v _ ↦ mul_le_mul_of_nonneg_right (hdeg v) (sq_nonneg p)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hs
  have he := edgeForm_self G (fun _ ↦ p)
  rw [edgeForm_neighbor] at he
  simp only [neighborMass_const] at he
  have he' : (∑ u, p*((G.degree u : ℝ)*p)) = ∑ u, (G.degree u : ℝ)*p^2 := by
    apply sum_congr rfl
    intro u _
    ring
  rw [he'] at he
  nlinarith

lemma potential_const_lower (G : SimpleGraph V) {Δ : ℝ} (hΔ : 1 < Δ)
    (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ)*(Real.log Δ)^2/(4*Δ) ≤
      potential G (fun _ ↦ Real.log Δ / Δ) := by
  have hΔpos : 0 < Δ := lt_trans zero_lt_one hΔ
  have ht : 0 < Real.log Δ := Real.log_pos hΔ
  have hp : 0 < Real.log Δ / Δ := div_pos ht hΔpos
  have hlog := log_le_one_add_quarter ht
  have hhe : Δ*(Real.log Δ/Δ) = Real.log Δ := by field_simp
  have hterm : Real.log Δ/4 ≤ 1-Real.log (Real.log Δ/Δ)-Δ*(Real.log Δ/Δ)/2 := by
    rw [Real.log_div ht.ne' hΔpos.ne', hhe]
    linarith
  have hc : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hterm (mul_nonneg hc hp.le)
  have he := edgeMass_const_le G hdeg (Real.log Δ/Δ)
  simp only [potential,vertexPotential,sum_const,card_univ,nsmul_eq_mul]
  have heq : (Fintype.card V : ℝ)*(Real.log Δ)^2/(4*Δ) =
      (Fintype.card V : ℝ)*(Real.log Δ/Δ)*(Real.log Δ/4) := by ring
  rw [heq]
  nlinarith

/-- The quantitative maximum-degree independence bound. -/
lemma maximum_degree_independence (k : ℕ) {B Δ : ℝ} (hB : 0 ≤ B) (hΔ : 3 ≤ Δ)
    (htri : ∀ {U : Type u} [Fintype U] (H : SimpleGraph U) (w : U → ℝ),
      IsOptimizer H w → H.CliqueFree (k+2) → triangleMass H w ≤ B * edgeMass H w)
    (G : SimpleGraph V) (hf : G.CliqueFree (k+2)) (hdeg : ∀ v, (G.degree v : ℝ) ≤ Δ) :
    (Fintype.card V : ℝ)*Real.log Δ/(4*(3+3*B/2)*Δ) ≤ (G.indepNum : ℝ) := by
  have hΔpos : 0 < Δ := by linarith
  have ht : 0 < Real.log Δ := Real.log_pos (by linarith)
  have hD : 0 < 3+3*B/2 := by positivity
  obtain ⟨I,hI,hIp⟩ := maximum_degree_potential_bound k hB hΔ htri G hf hdeg
  have hupper := hIp (fun _ ↦ Real.log Δ/Δ) (fun _ ↦ (div_pos ht hΔpos).le)
  have hlower := potential_const_lower G (by linarith : 1 < Δ) hdeg
  have hc : (I.card : ℝ) ≤ G.indepNum := Nat.cast_le.2 hI.card_le_indepNum
  have hfinal := hupper.trans (mul_le_mul_of_nonneg_left hc (mul_pos hD ht).le)
  have hbound := hlower.trans hfinal
  apply (mul_le_mul_iff_left₀ (mul_pos hD ht)).1
  convert hbound using 1 <;> field_simp

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_independence.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.maximum_degree_independence.{u}
