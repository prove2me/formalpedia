-- Prove2me | solution 1 for OAI.ShortEgyptian.sum_le_divisor_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:14:07.651539+00:00
-- url     : https://prove2.me/submissions/7a9f834d-e336-4399-9f92-d719da49f684

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorCover.lean:L53-L93
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.sum_le_divisor_cover. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorCover ----
namespace OAI

universe uι

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem multiples_interval_bound (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) {d : ℕ}
    (hd : 0 < d) (hdY : (d:ℝ) ≤ Y) :
    (((Ioc N (N+⌊Y⌋₊)).filter (d ∣ ·)).card:ℝ) ≤ 2*Y/d := by
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hcard : ((Ioc N (N+⌊Y⌋₊)).filter (d ∣ ·)).card ≤
      (N+⌊Y⌋₊)/d-N/d := by
    calc
      _ ≤ (Ioc (N/d) ((N+⌊Y⌋₊)/d)).card := by
        apply card_le_card_of_injOn (fun n => n/d)
        · intro n hn
          obtain ⟨hn, hdn⟩ := mem_filter.mp hn
          have hh := mem_Ioc.mp hn
          apply mem_Ioc.mpr
          constructor
          · apply (Nat.div_lt_iff_lt_mul hd).mpr
            simpa [Nat.div_mul_cancel hdn] using hh.1
          · exact Nat.div_le_div_right hh.2
        · intro a ha b hb hab
          have ha' := (mem_filter.mp ha).2
          have hb' := (mem_filter.mp hb).2
          calc
            a = a/d*d := (Nat.div_mul_cancel ha').symm
            _ = b/d*d := congrArg (·*d) hab
            _ = b := Nat.div_mul_cancel hb'
      _ = _ := by simp
  have hdiv : (N+⌊Y⌋₊)/d-N/d ≤ ⌊Y⌋₊/d+1 := by
    rw [Nat.add_div hd, Nat.add_assoc, Nat.add_sub_cancel_left]
    apply Nat.add_le_add_left
    split_ifs <;> decide
  have hf : (⌊Y⌋₊:ℝ)/d ≤ Y/d := div_le_div_of_nonneg_right (Nat.floor_le hY) hdR.le
  have h1 : (1:ℝ) ≤ Y/d := (le_div_iff₀ hdR).mpr (by simpa using hdY)
  calc
    _ ≤ ((⌊Y⌋₊/d+1:ℕ):ℝ) := by exact_mod_cast hcard.trans hdiv
    _ ≤ Y/d+1 := by
      push_cast
      have hh : (⌊Y⌋₊/d:ℕ) ≤ (⌊Y⌋₊:ℝ)/d := Nat.cast_div_le
      linarith
    _ ≤ _ := by calc
      _ ≤ Y/d+Y/d := by linarith
      _ = 2*Y/d := by ring

theorem sum_le_divisor_cover {ι : Type uι} (I : Finset ι) (D : ι → Finset ℕ)
    (F : ι → ℕ → ℝ) (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) (w : ℕ → ℝ)
    (hF : ∀ i ∈ I, ∀ d ∈ D i, 0 ≤ F i d)
    (hD : ∀ i ∈ I, ∀ d ∈ D i, 0 < d ∧ (d:ℝ) ≤ Y)
    (hc : ∀ n ∈ Ioc N (N+⌊Y⌋₊), ∃ i ∈ I, ∃ d ∈ D i, d ∣ n ∧ w n ≤ F i d) :
    ∑ n ∈ Ioc N (N+⌊Y⌋₊), w n ≤ 2*Y * ∑ i ∈ I, ∑ d ∈ D i, F i d/d := by
  classical
  calc
    _ ≤ ∑ n ∈ Ioc N (N+⌊Y⌋₊), ∑ i ∈ I, ∑ d ∈ (D i).filter (· ∣ n), F i d := by
      apply sum_le_sum
      intro n hn
      obtain ⟨i,hi,d,hd,hdn,hw⟩ := hc n hn
      apply hw.trans
      apply (single_le_sum (s := (D i).filter (· ∣ n))
        (fun d hd' => hF i hi d (mem_filter.mp hd').1)
        (mem_filter.mpr ⟨hd,hdn⟩)).trans
      exact single_le_sum (fun j hj => sum_nonneg (fun d hd' => hF j hj d (mem_filter.mp hd').1)) hi
    _ = ∑ i ∈ I, ∑ d ∈ D i, (((Ioc N (N+⌊Y⌋₊)).filter (d ∣ ·)).card:ℝ) * F i d := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      simp_rw [sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter]
      simp
    _ ≤ ∑ i ∈ I, ∑ d ∈ D i, 2*Y/d * F i d := by
      apply sum_le_sum
      intro i hi
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (multiples_interval_bound N Y hY (hD i hi d hd).1 (hD i hi d hd).2) (hF i hi d hd)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
      apply sum_congr rfl
      intro d hd
      ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution.{uι} : type_of% @_root_.OAI.ShortEgyptian.sum_le_divisor_cover.{uι} := @_root_.OAI.ShortEgyptian.sum_le_divisor_cover.{uι}
