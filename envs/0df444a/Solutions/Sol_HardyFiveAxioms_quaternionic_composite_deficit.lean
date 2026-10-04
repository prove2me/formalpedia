-- Prove2me | solution 1 for HardyFiveAxioms.quaternionic_composite_deficit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T08:07:47.942633+00:00
-- url     : https://prove2.me/submissions/ee719e24-d6a9-4bb2-bfb9-94ab60c23e37

import Mathlib
import Definitions.Def_hardy2001_signature

open HardyFiveAxioms

private lemma four_div (N : ℕ) : 4 * (N * (N - 1) / 2) = 2 * N * (N - 1) := by
  have hd : 2 ∣ N * (N - 1) := (Nat.even_mul_pred_self N).two_dvd
  calc
    4 * (N * (N - 1) / 2) = N * (N - 1) / 2 * 2 * 2 := by ring
    _ = N * (N - 1) * 2 := by rw [Nat.div_mul_cancel hd]
    _ = 2 * N * (N - 1) := by ring

private lemma closed (N : ℕ) : N + 2 * N * (N - 1) = 2 * N ^ 2 - N := by
  cases N with
  | zero => simp
  | succ k =>
      simp
      have hrhs : 2 * (k + 1) * (k + 1) - (k + 1) = (k + 1) * (2 * k + 1) := by
        rw [(Nat.sub_one_mul (2 * (k + 1)) (k + 1)).symm]
        have hone : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [hone, Nat.mul_comm]
      have hlhs : k + 1 + 2 * (k + 1) * k = (k + 1) * (2 * k + 1) := by ring
      rw [hlhs, ← hrhs, Nat.pow_two]
      have hassoc : 2 * (k + 1) * (k + 1) = 2 * ((k + 1) * (k + 1)) := by ac_rfl
      rw [hassoc]

theorem solution (NA NB : ℕ) (hA : 2 ≤ NA) (hB : 2 ≤ NB) :
    dofOfSignature [1, 4] (NA * NB) < dofOfSignature [1, 4] NA * dofOfSignature [1, 4] NB := by
  have hf : ∀ N : ℕ, dofOfSignature [1, 4] N = 2 * N ^ 2 - N := by
    intro N
    unfold dofOfSignature
    simp [List.length_cons, List.length_nil, Fin.sum_univ_two, Nat.choose_one_right,
      Nat.choose_two_right]
    have : N * (N - 1) / 2 * 4 = 4 * (N * (N - 1) / 2) := by ring
    rw [this, four_div, closed]
  rw [hf, hf, hf]
  have hsub (N : ℕ) (hN : 1 ≤ N) : ((2 * N ^ 2 - N : ℕ) : ℤ) = 2 * (N : ℤ) ^ 2 - N := by
    have : N ≤ 2 * N ^ 2 := by nlinarith
    zify [hN, this]
  have hAB : 1 ≤ NA * NB := le_trans (by decide : (1:ℕ) ≤ 4) (Nat.mul_le_mul hA hB)
  have hNA : 1 ≤ NA := by omega
  have hNB : 1 ≤ NB := by omega
  have ha : (2 : ℤ) ≤ (NA : ℤ) := by exact_mod_cast hA
  have hb : (2 : ℤ) ≤ (NB : ℤ) := by exact_mod_cast hB
  have hineq : 2 * ((NA : ℤ) * (NB : ℤ)) ^ 2 - (NA : ℤ) * NB <
      (2 * (NA : ℤ) ^ 2 - NA) * (2 * (NB : ℤ) ^ 2 - NB) := by
    have hdiff :
        (2 * (NA : ℤ) ^ 2 - NA) * (2 * (NB : ℤ) ^ 2 - NB) -
          (2 * ((NA : ℤ) * NB) ^ 2 - (NA : ℤ) * NB)
          = 2 * (NA : ℤ) * NB * ((NA : ℤ) - 1) * ((NB : ℤ) - 1) := by ring
    have hpos : 0 < 2 * (NA : ℤ) * NB * ((NA : ℤ) - 1) * ((NB : ℤ) - 1) := by
      have : 0 < (NA : ℤ) := by exact_mod_cast (show 0 < NA by omega)
      have : 0 < (NB : ℤ) := by exact_mod_cast (show 0 < NB by omega)
      have : 0 < (NA : ℤ) - 1 := by linarith
      have : 0 < (NB : ℤ) - 1 := by linarith
      positivity
    linarith
  have hlt : ((2 * (NA * NB) ^ 2 - NA * NB : ℕ) : ℤ) <
      ((((2 * NA ^ 2 - NA) * (2 * NB ^ 2 - NB) : ℕ) : ℤ)) := by
    rw [hsub _ hAB, Nat.cast_mul, Nat.cast_mul, hsub _ hNA, hsub _ hNB]
    simpa [Nat.cast_mul] using hineq
  exact_mod_cast hlt

