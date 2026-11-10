-- Prove2me | solution 1 for GuhaBroadcast.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:57:04.749101+00:00
-- url     : https://prove2.me/submissions/018124df-637d-438b-bfa4-011d83507840

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_bobOutput
import Definitions.Def_GuhaBroadcast_bobCodeword
import Definitions.Def_GuhaBroadcast_modeMeanPhotons
import Definitions.Def_GuhaBroadcast_codewordMeanPhotons

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

open GuhaBroadcast in
theorem solution (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar))
    (βk : Fin MC → ℝ)
    (hβk : ∀ k, 0 ≤ βk k ∧ βk k ≤ 1 ∧ spectralEntropyNats (bobCodeword eta C k) =
      ENNReal.ofReal ((n : ℝ) * g (eta * βk k * codewordMeanPhotons C k)))
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ : (∑ k, (spectralEntropyNats (bobCodeword eta C k)).toReal) / (MC : ℝ) =
      (n : ℝ) * g (eta * β * Nbar)) :
    (∑ k, g (eta * βk k * codewordMeanPhotons C k)) / (MC : ℝ) = g (eta * β * Nbar) := by
  have hg : ∀ x : ℝ, 0 ≤ x → 0 ≤ g x := by
    intro x hx
    unfold g
    rcases hx.eq_or_lt with rfl | hx
    · simp
    · have h1 := Real.log_le_log hx (by linarith : x ≤ x + 1)
      have h2 := Real.log_nonneg (by linarith : (1:ℝ) ≤ x + 1)
      nlinarith [mul_le_mul_of_nonneg_left h1 hx.le]
  have hN : ∀ k, 0 ≤ codewordMeanPhotons C k := by
    intro k
    unfold codewordMeanPhotons modeMeanPhotons
    positivity
  have e : ∀ k, (spectralEntropyNats (bobCodeword eta C k)).toReal
      = (n : ℝ) * g (eta * βk k * codewordMeanPhotons C k) := by
    intro k
    rw [(hβk k).2.2, ENNReal.toReal_ofReal (mul_nonneg (Nat.cast_nonneg _)
      (hg _ (mul_nonneg (mul_nonneg (by linarith) (hβk k).1) (hN k))))]
  rw [Finset.sum_congr rfl (fun k _ => e k), ← Finset.mul_sum, mul_div_assoc] at hβ
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn.ne') hβ
