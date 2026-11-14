-- Prove2me | solution 1 for LatticePrepro.params_spec
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:50:08.442211+00:00
-- url     : https://prove2.me/submissions/7cb3c966-3c54-4d4f-81d8-b7bb4047d808

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

lemma momentAxes_spec {δ : ℝ} (hδ1 : δ < 1) :
    1 ≤ momentAxes δ ∧ δ * (momentAxes δ + 1) < momentAxes δ := by
  refine ⟨by unfold momentAxes; omega, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hm : δ / (1 - δ) < momentAxes δ := by
    unfold momentAxes
    push_cast
    linarith [Nat.le_ceil (δ / (1 - δ))]
  rw [div_lt_iff₀ h1δ] at hm
  nlinarith

/-- Parameter choice: given `0 ≤ δ < 1`, with `m = momentAxes δ`, `k = gapExp p δ` and
`C = sizeExp p δ`, for every `S ≥ 1` and `g = (S+1)^k`, any `n ≥ 1` with
`n^m ≤ (8 p^4 m (S+1))^{(m+7) m} g^{m+1}` satisfies `64 · n^δ ≤ g` and `4 n ≤ (S+1)^C`. -/
private lemma params_spec (p : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S n : ℕ) (hS : 1 ≤ S)
    (hn : 1 ≤ n)
    (hbound : n ^ momentAxes δ ≤ (8 * p ^ 4 * momentAxes δ * (S + 1)) ^
      ((momentAxes δ + 7) * momentAxes δ) * ((S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1)) :
    64 * (n : ℝ) ^ δ ≤ ((S + 1) ^ gapExp p δ : ℕ) ∧ 4 * n ≤ (S + 1) ^ sizeExp p δ := by
  obtain ⟨hm1, hmδ⟩ := momentAxes_spec hδ1
  set m := momentAxes δ with hm
  set a : ℕ := prefactorExp p m with ha
  set η : ℝ := m - δ * (m + 1) with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set k : ℕ := gapExp p δ with hk
  have hkdef : k = ⌈(6 * m + a : ℝ) / η⌉₊ + 1 := rfl
  have hC : sizeExp p δ = a + k * (m + 1) + 2 := rfl
  rw [hC]
  have hS2 : (2 : ℝ) ≤ (S + 1 : ℕ) := by exact_mod_cast (by omega : 2 ≤ S + 1)
  have hS1R : (1 : ℝ) ≤ (S + 1 : ℕ) := by linarith
  have hS0R : (0 : ℝ) < (S + 1 : ℕ) := by linarith
  -- the prefactor is at most `(S+1)^a` (in exponent form)
  have hX : 8 * p ^ 4 * m * (S + 1) ≤ (S + 1) ^ (8 * p ^ 4 * m + 1) := by
    calc 8 * p ^ 4 * m * (S + 1) ≤ 2 ^ (8 * p ^ 4 * m) * (S + 1) := by
          gcongr
          exact (Nat.lt_two_pow_self).le
      _ ≤ (S + 1) ^ (8 * p ^ 4 * m) * (S + 1) := by
          gcongr
          omega
      _ = (S + 1) ^ (8 * p ^ 4 * m + 1) := by ring
  have hn' : n ^ m ≤ (S + 1) ^ (a + k * (m + 1)) := by
    calc n ^ m ≤ (8 * p ^ 4 * m * (S + 1)) ^ ((m + 7) * m) * ((S + 1) ^ k) ^ (m + 1) := hbound
      _ ≤ ((S + 1) ^ (8 * p ^ 4 * m + 1)) ^ ((m + 7) * m) * ((S + 1) ^ k) ^ (m + 1) := by
          gcongr
      _ = (S + 1) ^ (a + k * (m + 1)) := by
          rw [ha, prefactorExp, ← pow_mul, ← pow_mul, ← pow_add]
  constructor
  · -- `64 n^δ ≤ (S+1)^k`, by raising both sides to the `m`-th power
    set T : ℝ := ((S + 1 : ℕ) : ℝ) with hT
    have hT1 : (1 : ℝ) ≤ T := hS1R
    have hT0 : (0 : ℝ) < T := hS0R
    have hT2 : (2 : ℝ) ≤ T := hS2
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn'R : ((n : ℝ) ^ m) ≤ T ^ (a + k * (m + 1)) := by rw [hT]; exact_mod_cast hn'
    have hkη : (6 * m + a : ℝ) ≤ k * η := by
      have h1 : (6 * m + a : ℝ) / η ≤ ⌈(6 * m + a : ℝ) / η⌉₊ := Nat.le_ceil _
      have h2 : (⌈(6 * m + a : ℝ) / η⌉₊ : ℝ) ≤ k := by rw [hkdef]; push_cast; linarith
      calc (6 * m + a : ℝ) = (6 * m + a : ℝ) / η * η := by field_simp
        _ ≤ k * η := by gcongr; linarith
    have hexp : (6 * m : ℝ) + ((a + k * (m + 1) : ℕ) : ℝ) * δ ≤ ((k * m : ℕ) : ℝ) := by
      have : δ * (a : ℝ) ≤ a := by nlinarith
      rw [hη] at hkη
      push_cast
      nlinarith
    have e1 : (64 * (n : ℝ) ^ δ) ^ m = 64 ^ m * ((n : ℝ) ^ m) ^ δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (by positivity), ← Real.rpow_natCast_mul (by positivity),
        mul_comm δ (m : ℝ)]
    have e2 : (64 : ℝ) ^ m ≤ T ^ (6 * m) := by
      calc (64 : ℝ) ^ m = (2 ^ 6) ^ m := by norm_num
        _ ≤ (T ^ 6) ^ m := by gcongr
        _ = T ^ (6 * m) := by rw [← pow_mul]
    have key : (64 * (n : ℝ) ^ δ) ^ m ≤ (((S + 1) ^ k : ℕ) : ℝ) ^ m := by
      calc (64 * (n : ℝ) ^ δ) ^ m = 64 ^ m * ((n : ℝ) ^ m) ^ δ := e1
        _ ≤ T ^ (6 * m) * (T ^ (a + k * (m + 1))) ^ δ := by gcongr
        _ = T ^ ((6 * m : ℕ) : ℝ) * T ^ (((a + k * (m + 1) : ℕ) : ℝ) * δ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast_mul hT0.le]
        _ = T ^ (((6 * m : ℕ) : ℝ) + ((a + k * (m + 1) : ℕ) : ℝ) * δ) := by
            rw [Real.rpow_add hT0]
        _ ≤ T ^ (((k * m : ℕ) : ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le hT1
            push_cast at hexp ⊢
            exact hexp
        _ = (((S + 1) ^ k : ℕ) : ℝ) ^ m := by
            rw [Real.rpow_natCast, hT]; push_cast; ring_nf
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).mp key
  · -- `4 n ≤ (S+1)^C`
    have hnn : n ≤ n ^ m := Nat.le_self_pow (by omega) n
    calc 4 * n ≤ (S + 1) ^ 2 * (S + 1) ^ (a + k * (m + 1)) := by
          apply Nat.mul_le_mul
          · calc 4 = 2 ^ 2 := by norm_num
              _ ≤ (S + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
          · exact hnn.trans hn'
      _ = (S + 1) ^ (a + k * (m + 1) + 2) := by ring

end LatticePrepro

open LatticePrepro
theorem solution (p : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (S n : ℕ) (hS : 1 ≤ S)
    (hn : 1 ≤ n)
    (hbound : n ^ momentAxes δ ≤ (8 * p ^ 4 * momentAxes δ * (S + 1)) ^
      ((momentAxes δ + 7) * momentAxes δ) * ((S + 1) ^ gapExp p δ) ^ (momentAxes δ + 1)) :
    64 * (n : ℝ) ^ δ ≤ ((S + 1) ^ gapExp p δ : ℕ) ∧ 4 * n ≤ (S + 1) ^ sizeExp p δ :=
  @LatticePrepro.params_spec p δ hδ0 hδ1 S n hS hn hbound
