-- Prove2me | solution 1 for GrothendieckPD.Digits.lemma_2_5_scheme_l1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:53:47.548297+00:00
-- url     : https://prove2.me/submissions/7407caa0-ae27-4adb-a529-e10421df5421
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
import Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_coeff_l1
import Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_coeff_integrable

open MeasureTheory Filter
open GrothendieckPD.Digits

theorem solution :
    ∀ (n : ℕ) (S : GrothendieckLB.MixedScheme n),
      (Summable fun m => |schemeCoeff S m|) ∧ (∑' m, |schemeCoeff S m| ≤ 1) := by
  intro n S
  letI : IsProbabilityMeasure S.μ := S.prob
  let a : ℕ → S.Ω → ℝ := fun m ω => coeff m (S.F ω) (S.G ω)
  have ha (m : ℕ) : Integrable (a m) S.μ := lemma_2_5_coeff_integrable n m S
  have ha_bound (ω : S.Ω) : Summable (fun m => |a m ω|) ∧ ∑' m, |a m ω| ≤ 1 := by
    exact lemma_2_5_coeff_l1 n (S.F ω) (S.G ω) (S.sign_F ω) (S.sign_G ω)
  have hfin (s : Finset ℕ) : ∑ m ∈ s, |schemeCoeff S m| ≤ 1 := by
    calc
      ∑ m ∈ s, |schemeCoeff S m| = ∑ m ∈ s, |∫ ω, a m ω ∂S.μ| := by rfl
      _ ≤ ∑ m ∈ s, ∫ ω, |a m ω| ∂S.μ := by
        apply Finset.sum_le_sum
        intro m hm
        exact abs_integral_le_integral_abs
      _ = ∫ ω, ∑ m ∈ s, |a m ω| ∂S.μ := by
        rw [integral_finset_sum]
        intro m hm
        exact (ha m).abs
      _ ≤ ∫ _ω : S.Ω, (1 : ℝ) ∂S.μ := by
        apply integral_mono
        · apply integrable_finset_sum
          intro m hm
          exact (ha m).abs
        · exact integrable_const 1
        · intro ω
          exact ((ha_bound ω).1.sum_le_tsum s (fun m hm => abs_nonneg _)).trans (ha_bound ω).2
      _ = 1 := by simp
  have hs : Summable (fun m => |schemeCoeff S m|) :=
    summable_of_sum_le (fun m => abs_nonneg _) hfin
  refine ⟨hs, ?_⟩
  apply le_of_tendsto hs.hasSum.tendsto_sum_nat
  filter_upwards [] with k
  exact hfin (Finset.range k)
