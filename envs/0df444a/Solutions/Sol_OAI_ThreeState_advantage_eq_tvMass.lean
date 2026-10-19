-- Prove2me | solution 1 for OAI.ThreeState.advantage_eq_tvMass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:47:29.767841+00:00
-- url     : https://prove2.me/submissions/586597be-202a-4d0f-8c97-ca08e5453557

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Basic.lean:L206-L220
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.advantage_eq_tvMass. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic

-- ---- from OAI.Probability.ThreeState.Basic ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Three-state symmetric broadcast experiments, posterior advantage and total variation. -/

namespace ThreeState

 
 
 

 
 

 
 
 

 
 
 
end ThreeState
namespace ThreeState

lemma mass_nonneg {α : Type*} (p : PMF α) (a : α) : 0 ≤ mass p a := ENNReal.toReal_nonneg
lemma mass_summable {α : Type*} (p : PMF α) : Summable (mass p) :=
  ENNReal.summable_toReal p.tsum_coe_ne_top

lemma mass_bind {α β : Type*} (p : PMF α) (k : α → PMF β) (b : β) :
    mass (p.bind k) b = ∑' a, mass p a * mass (k a) b := by
  simp only [mass, PMF.bind_apply, ENNReal.tsum_toReal_eq
    (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) ((k a).apply_ne_top b)), ENNReal.toReal_mul]

lemma mass_uniform (i : Spin) : mass uniformSpin i = 1/3 := by
  simp [mass, uniformSpin, PMF.ofFintype_apply]

lemma mass_marginal {α : Type*} (law : Spin → PMF α) (y : α) :
    mass (marginal law) y = (∑ i : Spin, mass (law i) y)/3 := by
  simp only [marginal, mass_bind, tsum_fintype, mass_uniform]
  rw [← Finset.mul_sum]
  ring

lemma mass_eq_zero {α : Type*} (p : PMF α) (a : α) : mass p a = 0 ↔ p a = 0 := by
  simp [mass, ENNReal.toReal_eq_zero_iff, p.apply_ne_top a]

lemma marginal_zero {α : Type*} (law : Spin → PMF α) (y : α)
    (h : marginal law y = 0) (i : Spin) : law i y = 0 := by
  apply (mass_eq_zero (law i) y).mp
  have hh : mass (marginal law) y = 0 := (mass_eq_zero _ _).mpr h
  rw [mass_marginal] at hh
  have hs : ∑ j : Spin, mass (law j) y = 0 := by linarith
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mass_nonneg (law j) y)).mp hs i (by simp)

 
lemma weighted_posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    mass (marginal law) y * (posterior law y i-1/3) =
      (mass (law i) y-mass (marginal law) y)/3 := by
  classical
  by_cases h : marginal law y = 0
  · have hi := marginal_zero law y h i
    simp [mass, h, hi, posterior]
  · have hm : mass (marginal law) y ≠ 0 := mt (mass_eq_zero _ _).mp h
    simp only [posterior, ite_eq_right h]
    change mass (marginal law) y * (mass (law i) y / (3*mass (marginal law) y)-1/3) = _
    field_simp

lemma weighted_abs_posterior {α : Type*} (law : Spin → PMF α) (y : α) (i : Spin) :
    mass (marginal law) y * |posterior law y i-1/3| =
      |mass (law i) y-mass (marginal law) y|/3 := by
  calc
    mass (marginal law) y * |posterior law y i-1/3| =
        |mass (marginal law) y * (posterior law y i-1/3)| := by
      rw [abs_mul, abs_of_nonneg (mass_nonneg (marginal law) y)]
    _ = _ := by rw [weighted_posterior, abs_div]; norm_num

lemma mass_diff_summable {α : Type*} (p q : PMF α) :
    Summable (fun a => |mass p a-mass q a|) :=
  ((mass_summable p).sub (mass_summable q)).abs

lemma advantage_eq_tvMass {α : Type*} (law : Spin → PMF α) :
    advantage law = (∑ i : Spin, tvMass (law i) (marginal law))/3 := by
  have ht (y : α) : mass (marginal law) y *
      ((∑ i : Spin, |posterior law y i-1/3|)/2) =
      (∑ i : Spin, |mass (law i) y-mass (marginal law) y|)/6 := by
    rw [← mul_div_assoc, Finset.mul_sum]
    simp_rw [weighted_abs_posterior]
    rw [← Finset.sum_div]
    ring
  change (∑' y, mass (marginal law) y *
    ((∑ i : Spin, |posterior law y i-1/3|)/2)) = _
  simp_rw [ht]
  rw [tsum_div_const, Summable.tsum_finsetSum (fun i _ => mass_diff_summable (law i) (marginal law))]
  simp only [tvMass, ← Finset.sum_div]
  ring

 
end ThreeState

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState


theorem solution : type_of% @_root_.OAI.ThreeState.advantage_eq_tvMass := @_root_.OAI.ThreeState.advantage_eq_tvMass
