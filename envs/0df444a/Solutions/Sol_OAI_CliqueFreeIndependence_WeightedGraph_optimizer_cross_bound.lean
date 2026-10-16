-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:03:34.587985+00:00
-- url     : https://prove2.me/submissions/a6cace1a-8965-48aa-ab2a-5184c7eb8b8a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/CrossBound.lean:L99-L127
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_bound. The node keeps its source
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
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_growth_mono
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_cross_disjoint
import Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_optimizer_stationary

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
lemma mass_mono {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {A B : Finset V} (hAB : A ⊆ B) :
    mass w A ≤ mass w B := sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ ↦ hw v)

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- from OAI.Combinatorics.CliqueFree.CrossBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph
attribute [local instance] Classical.decEq
universe u
variable {V : Type u} [Fintype V]

section ColoringCount
variable [DecidableEq V]

lemma bool_point_count (u : V) (b : Bool) :
    (∑ f : V → Bool, if f u = b then (1:ℝ) else 0) =
      (Fintype.card (V → Bool) : ℝ)/2 := by
  let e := Equiv.funSplitAt u Bool
  have hc : (Fintype.card (V → Bool) : ℝ) =
      2*(Fintype.card ({j : V // j ≠ u} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ ↦ (n:ℝ)) h
  calc
    _ = (Fintype.card ({j : V // j ≠ u} → Bool) : ℝ) := by
      rw [← e.symm.sum_comp (fun f : V → Bool ↦ if f u = b then (1:ℝ) else 0)]
      rw [Fintype.sum_prod_type,Fintype.sum_bool]
      cases b <;> simp [e,Equiv.funSplitAt_symm_apply]
    _ = _ := by linarith

lemma bool_pair_count (u v : V) (huv : u ≠ v) :
    (∑ f : V → Bool, if f u = false ∧ f v = true then (1:ℝ) else 0) =
      (Fintype.card (V → Bool) : ℝ)/4 := by
  let e := Equiv.funSplitAt u Bool
  have hc : (Fintype.card (V → Bool) : ℝ) =
      2*(Fintype.card ({j : V // j ≠ u} → Bool) : ℝ) := by
    have h := Fintype.card_congr e
    simpa only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat] using congrArg (fun n : ℕ ↦ (n:ℝ)) h
  have hsum := e.symm.sum_comp (fun f : V → Bool ↦
    if f u = false ∧ f v = true then (1:ℝ) else 0)
  rw [Fintype.sum_prod_type,Fintype.sum_bool] at hsum
  simp only [e,Equiv.funSplitAt_symm_apply,eq_self,dite_true,dite_eq_right huv.symm,
    Bool.true_eq_false,false_and,ite_false,true_and,sum_const_zero,zero_add] at hsum
  rw [← hsum, bool_point_count (⟨v,huv.symm⟩ : {j : V // j ≠ u}) true]
  linarith only [hc]

end ColoringCount

omit [Fintype V] in
lemma crossMass_colored (G : SimpleGraph V) (w : V → ℝ) (S D : Finset V) (f : V → Bool) :
    crossMass G w (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true) =
      ∑ u ∈ S, ∑ v ∈ D, (if f u = false ∧ f v = true then (1:ℝ) else 0) *
        (if G.Adj u v then w u*w v else 0) := by
  classical
  unfold crossMass
  rw [sum_filter]
  apply sum_congr rfl
  intro u _
  rw [sum_filter]
  by_cases hu : f u = false
  · simp only [hu,true_and,ite_true]
    apply sum_congr rfl
    intro v _
    split_ifs <;> simp
  · simp [hu]

end CliqueFreeIndependence.WeightedGraph

namespace CliqueFreeIndependence.WeightedGraph
universe u
variable {V : Type u} [Fintype V]

lemma sum_colored_cross [DecidableEq V] (G : SimpleGraph V) (w : V → ℝ) (S D : Finset V) :
    (∑ f : V → Bool, crossMass G w (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true)) =
      (Fintype.card (V → Bool) : ℝ)/4 * crossMass G w S D := by
  simp_rw [crossMass_colored]
  rw [sum_comm]
  unfold crossMass
  rw [mul_sum]
  apply sum_congr rfl
  intro u _
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro v _
  classical
  by_cases huv : G.Adj u v
  · simp only [ite_eq_left huv]
    rw [← sum_mul,bool_pair_count u v huv.ne]
  · simp [huv]

/-- Full optimizer cross mass, including overlapping sets, with an explicit constant. -/
theorem optimizer_cross_bound (k : ℕ) (G : SimpleGraph V) {w : V → ℝ}
    (hw : IsOptimizer G w) (hfree : G.CliqueFree (k+2)) :
    CrossBound G w (16*((k:ℝ)+2)^2) := by
  classical
  intro x hx S D hs ht
  have hw0 := fun v ↦ (optimizer_stationary hw v).1.le
  have hpoint (f : V → Bool) :
      crossMass G w (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true) ≤
        (4*((k:ℝ)+2)^2)*growth x (mass w S) := by
    have hSD : Disjoint (S.filter fun u ↦ f u = false) (D.filter fun v ↦ f v = true) := by
      apply disjoint_left.2
      intro v hv hv'
      have h1 := (mem_filter.1 hv).2
      have h2 := (mem_filter.1 hv').2
      rw [h1] at h2
      contradiction
    have hS := mass_mono hw0 (filter_subset (fun u ↦ f u = false) S)
    have hD := mass_mono hw0 (filter_subset (fun v ↦ f v = true) D)
    have h := optimizer_cross_disjoint k G hw _ _ hSD hfree.cliqueFreeOn hx
      (hS.trans hs) (hD.trans ht)
    exact h.trans (mul_le_mul_of_nonneg_left
      (growth_mono hx (mass_nonneg hw0 _) (mass_nonneg hw0 _) hS) (by positivity))
  have hsum := sum_le_sum (s := (univ : Finset (V → Bool))) fun f _ ↦ hpoint f
  rw [sum_colored_cross] at hsum
  simp only [sum_const,card_univ,nsmul_eq_mul] at hsum
  have hn : 0 < (Fintype.card (V → Bool) : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hn).1
  nlinarith only [hsum]

end CliqueFreeIndependence.WeightedGraph

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_bound.{u} := @_root_.OAI.CliqueFreeIndependence.WeightedGraph.optimizer_cross_bound.{u}
