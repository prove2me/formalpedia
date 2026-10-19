-- Prove2me | solution 1 for HuWang2023.weightedMeanRedshift_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:16:52.301418+00:00
-- url     : https://prove2.me/submissions/541bd627-f59a-49f7-bc7e-92e9e2441524

import Mathlib
import Definitions.Def_HuWang2023_HubbleTension_Defs
open HuWang2023

namespace HuWangAux

lemma inner_ge_one (Ωm z : ℝ) (hΩ : 0 ≤ Ωm) (hz : 0 ≤ z) : 1 ≤ Ωm * (1 + z) ^ 3 + (1 - Ωm) := by
  have : 1 ≤ (1 + z) ^ 3 := one_le_pow₀ (by linarith)
  nlinarith

lemma flatE_pos (Ωm z : ℝ) (hΩ : 0 ≤ Ωm) (hz : 0 ≤ z) : 0 < flatE Ωm z := by
  unfold flatE
  exact Real.sqrt_pos.mpr (by linarith [inner_ge_one Ωm z hΩ hz])

lemma continuousOn_inv_flatE (Ωm : ℝ) (hΩ : 0 ≤ Ωm) :
    ContinuousOn (fun z => (flatE Ωm z)⁻¹) (Set.Ici 0) := by
  apply ContinuousOn.inv₀
  · unfold flatE; fun_prop
  · intro z hz; exact (flatE_pos Ωm z hΩ hz).ne'

lemma intervalIntegrable_inv_flatE (Ωm a b : ℝ) (hΩ : 0 ≤ Ωm) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun z => (flatE Ωm z)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply (continuousOn_inv_flatE Ωm hΩ).mono
  intro z hz
  rw [Set.mem_uIcc] at hz
  simp only [Set.mem_Ici]
  rcases hz with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith

end HuWangAux

theorem solution {ι : Type} (s : Finset ι) (z σ : ι → ℝ) (m M : ℝ)
    (hs : s.Nonempty) (hσ : ∀ n ∈ s, σ n ≠ 0) (hz : ∀ n ∈ s, z n ∈ Set.Icc m M) :
    weightedMeanRedshift s z σ ∈ Set.Icc m M := by
  unfold weightedMeanRedshift
  have hw : ∀ n ∈ s, 0 < (σ n) ^ (-2 : ℤ) := by
    intro n hn
    rw [zpow_neg, zpow_two]
    exact inv_pos.mpr (mul_self_pos.mpr (hσ n hn))
  have hW : 0 < ∑ n ∈ s, (σ n) ^ (-2 : ℤ) := Finset.sum_pos hw hs
  constructor
  · rw [le_div_iff₀ hW, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => by
      exact mul_le_mul_of_nonneg_right (hz n hn).1 (hw n hn).le
  · rw [div_le_iff₀ hW, Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn => by
      exact mul_le_mul_of_nonneg_right (hz n hn).2 (hw n hn).le
