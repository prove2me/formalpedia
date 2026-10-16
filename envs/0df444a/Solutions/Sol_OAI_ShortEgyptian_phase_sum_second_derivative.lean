-- Prove2me | solution 1 for OAI.ShortEgyptian.phase_sum_second_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:12:29.961537+00:00
-- url     : https://prove2.me/submissions/df8ef25b-e4bc-4039-aa80-fc7f09c17bf2

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SecondDerivative.lean:L183-L225
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.phase_sum_second_derivative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Theorems.Thm_OAI_ShortEgyptian_phase_sum_one_bin

-- ---- from OAI.NumberTheory.ShortEgyptian.SecondDerivative ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem discrete_difference_bounds (d : ℕ → ℝ) (N : ℕ) (lam Λ : ℝ)
    (hstep : ∀ n < N, lam ≤ d (n + 1) - d n ∧ d (n + 1) - d n ≤ Λ)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :
    lam * ((j : ℝ) - i) ≤ d j - d i ∧ d j - d i ≤ Λ * ((j : ℝ) - i) := by
  have hlo : MonotoneOn (fun n : ℕ => d n - lam * n) (Set.Icc 0 N) := by
    apply monotoneOn_of_le_add_one Set.ordConnected_Icc
    intro n _ _ hn
    simp only [Set.mem_Icc] at hn
    have hs := (hstep n (by omega)).1
    push_cast
    nlinarith
  have hhi : AntitoneOn (fun n : ℕ => d n - Λ * n) (Set.Icc 0 N) := by
    apply antitoneOn_of_add_one_le Set.ordConnected_Icc
    intro n _ _ hn
    simp only [Set.mem_Icc] at hn
    have hs := (hstep n (by omega)).2
    push_cast
    nlinarith
  have h1 := hlo ⟨Nat.zero_le _, hij.trans hj⟩ ⟨Nat.zero_le _, hj⟩ hij
  have h2 := hhi ⟨Nat.zero_le _, hij.trans hj⟩ ⟨Nat.zero_le _, hj⟩ hij
  constructor <;> linarith

theorem phase_sum_second_derivative (f : ℕ → ℝ) (N : ℕ) {lam Λ β : ℝ}
    (hlam : 0 < lam) (hβ : 0 < β)
    (hstep : ∀ n < N,
      lam ≤ (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ∧
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) ≤ Λ) :
    ‖∑ n ∈ range (N + 1), phase (f n)‖ ≤
      (Λ * N + 2) * (2 * β / lam + 1 / β + 3) := by
  classical
  let d (n : ℕ) := f (n + 1) - f n
  have hbounds {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) :=
    discrete_difference_bounds d N lam Λ (by simpa only [d, Nat.add_assoc] using hstep) hij hj
  have hdmono : MonotoneOn d (Set.Icc 0 N) := by
    intro i hi j hj hij
    have hh := (hbounds hij hj.2).1
    have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
    nlinarith
  let qs := Icc ⌊d 0⌋ ⌊d N⌋
  have hqN : ⌊d 0⌋ ≤ ⌊d N⌋ := Int.floor_mono (hdmono ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, le_rfl⟩ (Nat.zero_le _))
  have hmem (n : ℕ) (hn : n ∈ range (N + 1)) : ⌊d n⌋ ∈ qs := by
    have hnN : n ≤ N := by simpa only [mem_range, Nat.lt_succ_iff] using hn
    exact mem_Icc.mpr ⟨Int.floor_mono (hdmono ⟨le_rfl, Nat.zero_le _⟩ ⟨Nat.zero_le _, hnN⟩ (Nat.zero_le _)),
      Int.floor_mono (hdmono ⟨Nat.zero_le _, hnN⟩ ⟨Nat.zero_le _, le_rfl⟩ hnN)⟩
  have hcard : (qs.card : ℝ) ≤ Λ * N + 2 := by
    have hc : (qs.card : ℝ) = (⌊d N⌋ : ℝ) + 1 - (⌊d 0⌋ : ℝ) := by
      dsimp only [qs]
      rw [Int.card_Icc]
      have hh := Int.toNat_of_nonneg (show 0 ≤ ⌊d N⌋ + 1 - ⌊d 0⌋ by omega)
      exact_mod_cast hh
    rw [hc]
    have h1 := Int.floor_le (d N)
    have h0 := Int.lt_floor_add_one (d 0)
    have hh := (hbounds (Nat.zero_le N) le_rfl).2
    simp only [Nat.cast_zero, sub_zero] at hh
    linarith
  have hper (q : ℤ) : ‖∑ n ∈ (range (N + 1)).filter (fun n => ⌊d n⌋ = q), phase (f n)‖ ≤
      2 * β / lam + 1 / β + 3 :=
    phase_sum_one_bin f N q hlam hβ (fun i j hij hj => (hbounds hij hj).1)
  rw [← Finset.sum_fiberwise_of_maps_to hmem (fun n => phase (f n))]
  calc
    _ ≤ ∑ q ∈ qs, ‖∑ n ∈ range (N + 1) with ⌊d n⌋ = q, phase (f n)‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ qs, (2 * β / lam + 1 / β + 3) := sum_le_sum (fun q _ => hper q)
    _ = (qs.card : ℝ) * (2 * β / lam + 1 / β + 3) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.phase_sum_second_derivative := @_root_.OAI.ShortEgyptian.phase_sum_second_derivative
