-- Prove2me | solution 1 for OAI.ShortEgyptian.window_spectral_tail
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:37:39.998482+00:00
-- url     : https://prove2.me/submissions/07d41f05-618f-48a8-bc24-aecdef2d990b

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/WindowSpectrum.lean:L132-L152
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.window_spectral_tail. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Theorems.Thm_OAI_ShortEgyptian_phase_sum_first_derivative

-- ---- from OAI.NumberTheory.ShortEgyptian.WindowSpectrum ----
namespace OAI

universe uα uβ

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem natWindow_sum {q L : ℕ} (hL : L ≤ q) (f : ZMod q → ℂ) :
    ∑ x ∈ natWindow q L, f x = ∑ n ∈ Finset.range L, f n :=
  Finset.sum_image (natCast_injOn_range hL)

theorem frequencyDistance_pos {q : ℕ} [NeZero q] {k : ZMod q} (hk : k ≠ 0) :
    0 < frequencyDistance k := by
  have hh := (ZMod.val_ne_zero k).mpr hk
  have hh' := ZMod.val_lt k
  unfold frequencyDistance
  omega

theorem char_nat_eq_phase {q : ℕ} [NeZero q] (k : ZMod q) (n : ℕ) :
    ZMod.stdAddChar (k * (n : ZMod q)) = phase ((k.val : ℝ) * n / q) := by
  rw [ZMod.stdAddChar_apply, ← ZMod.natCast_zmod_val k, ← Nat.cast_mul,
    ZMod.toCircle_natCast]
  simp only [ZMod.natCast_zmod_val]
  unfold phase
  congr 1
  push_cast
  ring

theorem natWindow_char_bound {q L : ℕ} [NeZero q] (hL : L ≤ q)
    (k : ZMod q) (hk : k ≠ 0) :
    ‖charSum (natWindow q L) k‖ ≤ (q : ℝ) / frequencyDistance k := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hd : (0 : ℝ) < frequencyDistance k := by exact_mod_cast frequencyDistance_pos hk
  have hkq : k.val ≤ q := (ZMod.val_lt k).le
  have hd1 : (frequencyDistance k : ℝ) ≤ k.val := by exact_mod_cast (min_le_left k.val (q - k.val))
  have hd2 : (frequencyDistance k : ℝ) ≤ (q : ℝ) - k.val := by
    exact_mod_cast (min_le_right k.val (q - k.val))
  have hh := phase_sum_first_derivative (div_pos hd hq)
    (fun n : ℕ => (k.val : ℝ) * n / q) 0 L
    (fun n _ => by push_cast; field_simp; nlinarith)
    (fun n _ => by push_cast; field_simp; nlinarith)
    (fun n _ => by push_cast; ring_nf; rfl)
  dsimp only [charSum]
  rw [natWindow_sum hL]
  simp_rw [char_nat_eq_phase]
  convert hh using 1
  field_simp

theorem sum_injective_nonneg_bound {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (f : α → β) (g : β → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hf : Set.InjOn f s) (hst : ∀ x ∈ s, f x ∈ t) :
    ∑ x ∈ s, g (f x) ≤ ∑ y ∈ t, g y := by
  classical
  rw [← Finset.sum_image hf]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hst x hx
  · intro y _ _
    exact hg y

theorem harmonic_square_tail (H Q : ℕ) (hH : 1 ≤ H) :
    ∑ n ∈ Finset.Ioc H Q, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / H := by
  by_cases hHQ : H ≤ Q
  · have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (by omega : H ≠ 0) hHQ
    simp only [← one_div] at hh
    exact hh.trans (by linarith [show (0 : ℝ) ≤ 1 / Q by positivity])
  · have hempty : Finset.Ioc H Q = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    simp only [hempty, Finset.sum_empty]
    positivity

theorem frequency_square_tail {q : ℕ} [NeZero q] (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => H < frequencyDistance k),
      (1 : ℝ) / (frequencyDistance k : ℝ) ^ 2 ≤ 2 / H := by
  classical
  let E := (Finset.univ : Finset (ZMod q)).filter (fun k => H < frequencyDistance k)
  have hdist (k : ZMod q) (hk : k ∈ E) : H < k.val ∧ H < q - k.val := by
    have hh := (Finset.mem_filter.mp hk).2
    dsimp only [frequencyDistance] at hh
    exact lt_min_iff.mp hh
  have hfirst : (∑ k ∈ E, (1 : ℝ) / (k.val : ℝ) ^ 2) ≤ 1 / H := by
    apply le_trans (sum_injective_nonneg_bound E (Finset.Ioc H q) ZMod.val
      (fun n => (1 : ℝ) / (n : ℝ) ^ 2) (fun _ => by positivity)
      (ZMod.val_injective q).injOn (fun k hk => Finset.mem_Ioc.mpr
        ⟨(hdist k hk).1, (ZMod.val_lt k).le⟩))
    exact harmonic_square_tail H q hH
  have hsecond : (∑ k ∈ E, (1 : ℝ) / ((q - k.val : ℕ) : ℝ) ^ 2) ≤ 1 / H := by
    apply le_trans (sum_injective_nonneg_bound E (Finset.Ioc H q) (fun k => q - k.val)
      (fun n => (1 : ℝ) / (n : ℝ) ^ 2) (fun _ => by positivity) ?_ ?_)
    · exact harmonic_square_tail H q hH
    · intro k _ l _ heq
      dsimp only at heq
      apply ZMod.val_injective q
      have hk := ZMod.val_lt k
      have hl := ZMod.val_lt l
      omega
    · intro k hk
      exact Finset.mem_Ioc.mpr ⟨(hdist k hk).2, Nat.sub_le _ _⟩
  have hterm (k : ZMod q) : (1 : ℝ) / (frequencyDistance k : ℝ) ^ 2 ≤
      1 / (k.val : ℝ) ^ 2 + 1 / ((q - k.val : ℕ) : ℝ) ^ 2 := by
    unfold frequencyDistance
    rcases le_total k.val (q - k.val) with hh | hh
    · rw [min_eq_left hh]
      exact le_add_of_nonneg_right (by positivity)
    · rw [min_eq_right hh]
      exact le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ ∑ k ∈ E, ((1 : ℝ) / (k.val : ℝ) ^ 2 + 1 / ((q - k.val : ℕ) : ℝ) ^ 2) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ ≤ 1 / H + 1 / H := by rw [Finset.sum_add_distrib]; exact add_le_add hfirst hsecond
    _ = _ := by ring

theorem window_spectral_tail {q L M : ℕ} [NeZero q] (hL : L ≤ q) (hM : M ≤ q)
    (H : ℕ) (hH : 1 ≤ H) :
    ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => H < frequencyDistance k),
      ‖charSum (natWindow q L) k‖ * ‖charSum (natWindow q M) k‖ ≤ 2 * (q : ℝ) ^ 2 / H := by
  classical
  calc
    _ ≤ ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => H < frequencyDistance k),
        (q : ℝ) ^ 2 * (1 / (frequencyDistance k : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro k hk
      have hd := (Finset.mem_filter.mp hk).2
      have hk0 : k ≠ 0 := by intro heq; simp [heq, frequencyDistance] at hd
      calc
        _ ≤ ((q : ℝ) / frequencyDistance k) * (q / frequencyDistance k) := by
          exact mul_le_mul (natWindow_char_bound hL k hk0) (natWindow_char_bound hM k hk0)
            (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ = (q : ℝ) ^ 2 * ∑ k ∈ (Finset.univ : Finset (ZMod q)).filter (fun k => H < frequencyDistance k),
        (1 : ℝ) / (frequencyDistance k : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (q : ℝ) ^ 2 * (2 / H) := mul_le_mul_of_nonneg_left (frequency_square_tail H hH) (sq_nonneg _)
    _ = _ := by ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.window_spectral_tail := @_root_.OAI.ShortEgyptian.window_spectral_tail
