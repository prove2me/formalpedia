-- Prove2me | solution 1 for OAI.ShortEgyptian.iterated_interval_vdc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:22:09.812948+00:00
-- url     : https://prove2.me/submissions/8b35baa3-3921-43f6-94f4-8c5d19de6850

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/IteratedDifferencing.lean:L77-L143
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.iterated_interval_vdc. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Theorems.Thm_OAI_ShortEgyptian_interval_van_der_corput

-- ---- from OAI.NumberTheory.ShortEgyptian.IteratedDifferencing ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem backwardDifferences_sub (hs : List ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    backwardDifferences hs (fun y => f y - g y) x =
      backwardDifferences hs f x - backwardDifferences hs g x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
    simp only [backwardDifferences, ih]
    ring

theorem backwardDifferences_translate (hs : List ℝ) (f : ℝ → ℝ) (h x : ℝ) :
    backwardDifferences hs (fun y => f (y + h)) x =
      backwardDifferences hs f (x + h) := by
  induction hs generalizing x with
  | nil => rfl
  | cons t hs ih =>
    simp only [backwardDifferences, ih]
    congr 2
    ring

theorem backwardDifferences_commute (hs : List ℝ) (f : ℝ → ℝ) (h x : ℝ) :
    backwardDifferences hs (fun y => f y - f (y + h)) x =
      backwardDifferences (h :: hs) f x := by
  rw [backwardDifferences_sub, backwardDifferences_translate]
  rfl

theorem interval_phase_correlation (f : ℝ → ℝ) (p q h : ℤ) (hh : 0 ≤ h) :
    ‖∑ n ∈ Icc p q,
        (if n + h ∈ Icc p q then phase (f (n + h)) else 0) *
          (starRingEnd ℂ) (if n ∈ Icc p q then phase (f n) else 0)‖ =
      ‖∑ n ∈ Icc p (q - h), phase (f n - f (n + h))‖ := by
  classical
  have hsub : Icc p (q - h) ⊆ Icc p q := Icc_subset_Icc le_rfl (by omega)
  have hEq : (∑ n ∈ Icc p q,
        (if n + h ∈ Icc p q then phase (f (n + h)) else 0) *
          (starRingEnd ℂ) (if n ∈ Icc p q then phase (f n) else 0)) =
      (starRingEnd ℂ) (∑ n ∈ Icc p (q - h), phase (f n - f (n + h))) := by
    rw [map_sum]
    rw [← Finset.sum_subset hsub (by
      intro n hn hn'
      have hn0 := mem_Icc.mp hn
      have hn1 : n + h ∉ Icc p q := by
        intro hh'
        exact hn' (mem_Icc.mpr ⟨hn0.1, by have := (mem_Icc.mp hh').2; omega⟩)
      simp only [ite_eq_right hn1, zero_mul])]
    apply sum_congr rfl
    intro n hn
    have hn0 := mem_Icc.mp hn
    have hnh : n + h ∈ Icc p q := mem_Icc.mpr ⟨by omega, by omega⟩
    rw [ite_eq_left hnh, ite_eq_left (hsub hn), ← phase_sub, ← phase_neg]
    congr 1
    ring
  rw [hEq, Complex.norm_conj]

theorem iterated_interval_vdc (r : ℕ) (f : ℝ → ℝ) (p q : ℤ)
    (L : ℕ) (U eps : ℝ) (hL : 1 ≤ L) (hU : 0 < U)
    (hLU : (L : ℝ) ≤ U) (hsize : ((Icc p q).card : ℝ) ≤ U)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hLin : 1 / (L : ℝ) ≤ eps ^ (2 ^ r))
    (hleaf : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 1 ≤ h ∧ h < L) →
      ‖∑ n ∈ Icc p (q - hs.sum),
        phase (backwardDifferences (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ ≤
          U * eps ^ (2 ^ r)) :
    ‖∑ n ∈ Icc p q, phase (f n)‖ ≤ 4 * U * eps := by
  classical
  induction r generalizing f q eps with
  | zero =>
    have hh := hleaf [] rfl (by simp)
    simp only [List.sum_nil, sub_zero, List.map_nil, backwardDifferences,
      pow_zero, pow_one] at hh
    nlinarith
  | succ r ih =>
    by_cases hpq : p ≤ q
    · let a (n : ℤ) : ℂ := if n ∈ Icc p q then phase (f n) else 0
      have hcorr (h : ℤ) (hh : 1 ≤ h) (hhL : h < L) :
          ‖∑ n ∈ Icc p q, a (n + h) * (starRingEnd ℂ) (a n)‖ ≤
          4 * U * eps ^ 2 := by
        dsimp only [a]
        simp only [Int.cast_add]
        rw [interval_phase_correlation f p q h (by omega)]
        have hexp : (eps ^ 2) ^ (2 ^ r) = eps ^ (2 ^ (r + 1)) := by
          rw [← pow_mul, pow_succ]; congr 1; omega
        apply ih (fun x => f x - f (x + h)) (q - h) (eps ^ 2)
          (le_trans (by exact_mod_cast card_le_card (Icc_subset_Icc le_rfl (by omega))) hsize)
          (sq_nonneg eps) (by nlinarith) (by simpa only [hexp] using hLin)
        intro hs hlen hhs
        have hleaf' := hleaf (h :: hs) (by simp [hlen]) (by
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact ⟨hh, hhL⟩
          · exact hhs t ht)
        simpa only [List.map_cons, List.sum_cons,
          ← backwardDifferences_commute, sub_sub, hexp] using hleaf'
      have hvd := interval_van_der_corput a p q hpq L hL (4 * U * eps ^ 2)
        (by positivity) (by intro n hn; simp only [a, ite_eq_right hn])
        (by intro n hn; simp only [a, ite_eq_left hn, phase_norm, le_refl]) hcorr
      have hsum : (∑ n ∈ Icc p q, a n) = ∑ n ∈ Icc p q, phase (f n) :=
        sum_congr rfl (fun n hn => by simp only [a, ite_eq_left hn])
      rw [hsum] at hvd
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
      have hpow : eps ^ (2 ^ (r + 1)) ≤ eps ^ 2 :=
        pow_le_pow_of_le_one heps heps1 (by
          have := Nat.one_le_two_pow (n := r)
          rw [pow_succ]; omega)
      have hi : 1 / (L : ℝ) ≤ eps ^ 2 := hLin.trans hpow
      have hcard0 : (0 : ℝ) ≤ (Icc p q).card := by positivity
      have hA : ((Icc p q).card : ℝ) + L ≤ 2 * U := by linarith
      have hdiag : (((Icc p q).card : ℝ) + L) / L * (Icc p q).card ≤
          (2 * U * U) * eps ^ 2 := by
        calc
          _ ≤ (2 * U) / L * U := mul_le_mul
            (div_le_div_of_nonneg_right hA hL0.le) hsize hcard0 (by positivity)
          _ = (2 * U * U) * (1 / (L : ℝ)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hi (by positivity)
      have hoff := mul_le_mul_of_nonneg_right hA (show 0 ≤ 4 * U * eps ^ 2 by positivity)
      have ht : 0 ≤ 4 * U * eps := by positivity
      nlinarith [sq_nonneg (4 * U * eps)]
    · have he : Icc p q = ∅ := Icc_eq_empty_of_lt (by omega)
      rw [he, sum_empty, norm_zero]
      positivity

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.iterated_interval_vdc := @_root_.OAI.ShortEgyptian.iterated_interval_vdc
