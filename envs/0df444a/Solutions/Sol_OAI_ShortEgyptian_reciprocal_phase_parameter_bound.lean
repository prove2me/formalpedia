-- Prove2me | solution 1 for OAI.ShortEgyptian.reciprocal_phase_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:26:55.004578+00:00
-- url     : https://prove2.me/submissions/7b026bd7-4370-4971-b9d9-e84bcc9f2bc2

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ReciprocalEstimates.lean:L96-L186
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.reciprocal_phase_parameter_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Theorems.Thm_OAI_ShortEgyptian_iterated_interval_vdc
import Theorems.Thm_OAI_ShortEgyptian_reciprocal_leaf_sqrt

-- ---- from OAI.NumberTheory.ShortEgyptian.ReciprocalEstimates ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem real_list_prod_le_pow (hs : List ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hhs : ∀ h ∈ hs, 0 ≤ h ∧ h ≤ L) : hs.prod ≤ L ^ hs.length := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    have hh := hhs h (by simp)
    have ht : ∀ x ∈ hs, 0 ≤ x ∧ x ≤ L := fun x hx => hhs x (by simp [hx])
    simp only [List.prod_cons, List.length_cons, pow_succ']
    exact mul_le_mul hh.2 (ih ht) (List.prod_nonneg (fun x hx => (ht x hx).1)) hL

theorem reciprocal_phase_parameter_bound (r L : ℕ) (Z U eps : ℝ) (p q : ℤ)
    (hL : 1 ≤ L) (hU : 1 ≤ U) (hLU : (L : ℝ) ≤ 2 * U)
    (hZ : 0 ≤ Z) (hp : U ≤ p) (hq : (q : ℝ) ≤ 2 * U)
    (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ r))
    (hconstant : 18 ≤ U * eps ^ (2 ^ r))
    (hlow : (18 / (U * eps ^ (2 ^ r))) ^ 2 ≤
      Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3)))
    (hupp : (L : ℝ) ^ r *
      (Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))) ≤
      (eps ^ (2 ^ r) / (18 * (3 : ℝ) ^ (r + 3))) ^ 2) :
    ‖∑ n ∈ Icc p q, phase (Z / n)‖ ≤ 8 * U * eps := by
  classical
  have hU0 : 0 < U := by linarith
  have hsize : ((Icc p q).card : ℝ) ≤ 2 * U := by
    by_cases hpq : p ≤ q
    · rw [Int.card_Icc]
      have hcast : (((q + 1 - p).toNat : ℕ) : ℝ) = (q + 1 - p : ℤ) := by
        exact_mod_cast (show ((q + 1 - p).toNat : ℤ) = q + 1 - p by omega)
      rw [hcast]
      push_cast
      linarith
    · rw [Icc_eq_empty_of_lt (by omega : q < p), card_empty, Nat.cast_zero]
      positivity
  have hh := iterated_interval_vdc r (fun x => Z / x) p q L (2 * U) eps
    hL (by positivity) hLU hsize heps.le heps1 hLin (by
      intro hs hlen hhs
      let vs : List ℝ := hs.map (fun h : ℤ => (h : ℝ))
      have hvlen : vs.length = r := by simpa only [vs, List.length_map] using hlen
      have hvs : ∀ h ∈ vs, 1 ≤ h ∧ h ≤ (L : ℝ) := by
        intro h hh
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hh
        obtain ⟨ha0, haL⟩ := hhs a ha
        exact ⟨by exact_mod_cast ha0, by exact_mod_cast haL.le⟩
      have hp1 : 1 ≤ vs.prod := List.one_le_prod (fun h hh => (hvs h hh).1)
      have hpL : vs.prod ≤ (L : ℝ) ^ r := by
        have hp' := real_list_prod_le_pow vs (by positivity : (0 : ℝ) ≤ L)
          (fun h hh => ⟨le_trans (by norm_num) (hvs h hh).1, (hvs h hh).2⟩)
        simpa only [hvlen] using hp'
      have hvsum : vs.sum = (hs.sum : ℝ) := by simp [vs]
      by_cases hne : p ≤ q - hs.sum
      · let c : ℝ := Z * ((r + 2).factorial * (1 / (3 * U)) ^ (r + 3))
        let lam : ℝ := vs.prod * c
        let A : ℝ := (3 : ℝ) ^ (r + 3)
        let d : ℝ := eps ^ (2 ^ r)
        have hd : 0 < d := by dsimp [d]; positivity
        have hd1 : d ≤ 1 := pow_le_one₀ heps.le heps1
        have hA : 1 ≤ A := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)
        have hc : 0 < c := lt_of_lt_of_le (by positivity) hlow
        have hlo : (18 / (U * d)) ^ 2 ≤ lam := by
          apply hlow.trans
          dsimp only [lam]
          nlinarith
        have hup : lam ≤ (d / (18 * A)) ^ 2 :=
          (mul_le_mul_of_nonneg_right hpL hc.le).trans hupp
        have hlu : lam ≤ 1 := by
          have hfrac : d / (18 * A) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
          exact hup.trans (pow_le_one₀ (by positivity) hfrac)
        have hlpos : 0 < lam := lt_of_lt_of_le (by positivity) hlo
        have hslo : 18 / (U * d) ≤ Real.sqrt lam :=
          (Real.le_sqrt (by positivity) hlpos.le).mpr hlo
        have hsup : Real.sqrt lam ≤ d / (18 * A) :=
          (Real.sqrt_le_left (by positivity)).mpr hup
        have hlamdef : lam = Z * (vs.prod * (vs.length + 2).factorial *
            (1 / (3 * U)) ^ (vs.length + 3)) := by
          dsimp only [lam, c]
          rw [hvlen]
          ring
        have hlast := reciprocal_leaf_sqrt vs (fun h hh => le_trans (by norm_num) (hvs h hh).1)
          Z U p (q - hs.sum) hZ hU hp (by rw [hvsum]; push_cast; linarith)
          hne lam hlamdef hlpos hlu
        have hs1 : 6 * A * U * Real.sqrt lam ≤ U * d / 3 := by
          have hh1 := (le_div_iff₀ (show 0 < 18 * A by positivity)).mp hsup
          have hh2 := mul_le_mul_of_nonneg_left hh1 hU0.le
          nlinarith
        have hs2 : 6 / Real.sqrt lam ≤ U * d / 3 := by
          apply (div_le_iff₀ (Real.sqrt_pos.mpr hlpos)).mpr
          have hh1 := (div_le_iff₀ (show 0 < U * d by positivity)).mp hslo
          nlinarith
        have hs3 : 6 ≤ U * d / 3 := by dsimp only [d]; linarith
        rw [hvlen] at hlast
        change ‖∑ n ∈ Icc p (q - hs.sum),
          phase (backwardDifferences vs (fun x => Z / x) n)‖ ≤ _
        change ‖∑ n ∈ Icc p (q - hs.sum),
          phase (backwardDifferences vs (fun x => Z / x) n)‖ ≤ 6 * A * U * Real.sqrt lam + 6 / Real.sqrt lam + 6 at hlast
        change _ ≤ 2 * U * d
        nlinarith
      · rw [Icc_eq_empty_of_lt (by omega : q - hs.sum < p), sum_empty, norm_zero]
        positivity)
  convert hh using 1
  ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.reciprocal_phase_parameter_bound := @_root_.OAI.ShortEgyptian.reciprocal_phase_parameter_bound
