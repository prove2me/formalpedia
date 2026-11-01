-- Prove2me | solution 1 for InhomMJPStrong.J1.eq_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:37:35.479209+00:00
-- url     : https://prove2.me/submissions/1439e8eb-a874-4b8a-8317-50441107a202

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model
import Theorems.Thm_InhomMJPStrong_J1_doob_step
import Theorems.Thm_InhomMJPStrong_J1_erlang_central_moment

open MeasureTheory ProbabilityTheory
open InhomMJPStrong.J1

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : Real.exp 2 ≤ (n : ℝ))
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1)
    (g : ℕ → Ω → ℝ) (hgIndep : iIndepFun g P)
    (hgLaw : ∀ i, HasLaw (g i) (expMeasure (n : ℝ)) P)
    (C : ℝ) (hC : 1 ≤ C) :
    let m := gridSize n eps
    let beta := 2 * C * Real.log (n : ℝ) *
      (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)
    P {ω | beta ≤
      maxGap (fun l => arrival (fun i => g i ω) l)
        (fun l => (l : ℝ) / (n : ℝ)) m} ≤
      ENNReal.ofReal
        (2 * Real.sqrt ((n : ℝ) ^ (1 + eps)) / C ^ Real.log (n : ℝ)) := by
  intro m beta
  have he2 : (4 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp 2
    have h1 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h2 : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
    nlinarith
  have hn4 : 4 ≤ n := by exact_mod_cast (le_trans he2 hn)
  have hnpos : (0:ℝ) < n := by linarith
  set L := Real.log (n : ℝ) with hL
  have hL2 : 2 ≤ L := by rw [hL, Real.le_log_iff_exp_le hnpos]; exact hn
  set k := ⌊L⌋₊ with hk
  have hkL : (k:ℝ) ≤ L := Nat.floor_le (by linarith)
  have hLk : L - 1 < k := Nat.sub_one_lt_floor L
  set ρ := (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hnpos _
  have hβ : beta = 2 * C * L * ρ := rfl
  have hCpos0 : 0 < C := by linarith
  have hβpos : 0 < beta := by rw [hβ]; positivity
  set s := Real.sqrt ((n : ℝ) ^ (1 + eps)) with hs
  have hsρ : s = n * ρ := by
    rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le, hρ]
    conv_lhs => rw [show (1 + eps) * (1 / 2) = 1 + (-(1:ℝ) / 2 + eps / 2) by ring]
    rw [Real.rpow_add hnpos, Real.rpow_one]
  set r := Real.sqrt (m : ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrs : r ≤ s := Real.sqrt_le_sqrt (Nat.floor_le (by positivity))
  -- the two milestone bounds
  have hD := doob_step P n (by omega) eps heps heps1 g hgIndep hgLaw beta hβpos k
  have hE := erlang_central_moment P n hn4 eps heps heps1 g hgIndep hgLaw k
  dsimp only at hD hE
  obtain ⟨hE1, hE2⟩ := hE
  refine le_trans hD (ENNReal.ofReal_le_ofReal ?_)
  set x := 2 * (k:ℝ) * r / n with hx
  have hx0 : 0 ≤ x := by positivity
  have hxβ : x ≤ beta / C := by
    have : 0 < C := by linarith
    rw [hx, hβ, div_le_iff₀ hnpos]
    have h1 : r ≤ n * ρ := hsρ ▸ hrs
    calc 2 * (k:ℝ) * r ≤ 2 * L * (n * ρ) := by
          apply mul_le_mul (by linarith) h1 hr0 (by linarith)
      _ = 2 * C * L * ρ / C * n := by field_simp
  have hCpos : 0 < C := by linarith
  have hbound : (x / beta) ^ (2 * k) ≤ (1 / C) ^ (2 * k) := by
    apply pow_le_pow_left₀ (div_nonneg hx0 hβpos.le)
    rw [div_le_iff₀ hβpos]; calc x ≤ beta / C := hxβ
      _ = 1 / C * beta := by ring
  have hCk : C ^ L ≤ C ^ (2 * k) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hC
    push_cast; linarith
  have hCLpos : 0 < C ^ L := Real.rpow_pos_of_pos hCpos _
  calc (∫ ω, (arrival (fun i => g i ω) m - (m:ℝ) / n) ^ (2 * k) ∂P) / beta ^ (2 * k)
      ≤ (2 * r * x ^ (2 * k)) / beta ^ (2 * k) := by
        apply div_le_div_of_nonneg_right (le_trans hE1 hE2) (by positivity)
    _ = 2 * r * (x / beta) ^ (2 * k) := by rw [mul_div_assoc, ← div_pow]
    _ ≤ 2 * s * (1 / C) ^ (2 * k) := by
        apply mul_le_mul (by linarith) hbound (by positivity) (by positivity)
    _ = 2 * s / C ^ (2 * k) := by rw [one_div_pow]; ring
    _ ≤ 2 * s / C ^ L := by
        apply div_le_div_of_nonneg_left (by positivity) hCLpos hCk
