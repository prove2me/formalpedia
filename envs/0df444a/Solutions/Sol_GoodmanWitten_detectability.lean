-- Prove2me | solution 1 for GoodmanWitten.detectability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:55:38.699163+00:00
-- url     : https://prove2.me/submissions/c8c8f535-6f8a-45ee-b86d-df776c1d3bc6

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

namespace GWGoal

lemma coherent_closed (A m Y N : ℝ) (hA : 0 < A) (hm : 0 < m) :
    eventRatePerKgDay A (coherentCrossSection m (nucleusMass A) Y N) 1e-24 2e7 m =
      6.0e26 * 1e-24 * 2e7 * secondsPerDay * fermiConstant ^ 2 * hbarc ^ 2 / (2 * gramsPerGeV) *
        (nucleusMass A) ^ 2 * Y ^ 2 * N ^ 2 * m / (A * Real.pi * (m + nucleusMass A) ^ 2) := by
  unfold eventRatePerKgDay coherentCrossSection elasticCrossSection coherentAmpSq targetNucleiPerKg
  have hpi := Real.pi_pos
  have hn : 0 < nucleusMass A := by unfold nucleusMass nucleonMass; positivity
  have hg : 0 < gramsPerGeV := by unfold gramsPerGeV; norm_num
  field_simp

lemma photino_closed (A Q MQ : ℝ) (hA : 0 < A) (hMQ : 0 < MQ) :
    eventRatePerKgDay A (photinoCrossSection (nucleusMass A) (nucleusMass A) Q MQ 1)
      1e-24 2e7 (nucleusMass A) =
      6.0e26 * 1e-24 * 2e7 * secondsPerDay * 16 * Real.pi * fineStructure ^ 2 * hbarc ^ 2 *
        nucleonMass * Q ^ 4 / MQ ^ 4 / gramsPerGeV := by
  unfold eventRatePerKgDay photinoCrossSection elasticCrossSection photinoAmpSq quarkChargeSq
    targetNucleiPerKg nucleusMass
  have hpi := Real.pi_pos
  have hn : 0 < nucleonMass := by unfold nucleonMass; norm_num
  have hg : 0 < gramsPerGeV := by unfold gramsPerGeV; norm_num
  field_simp
  ring

lemma strong_closed (A MX : ℝ) (hA : 0 < A) (hMX : 0 < MX) :
    strongEventRate A MX 1 1e-24 2e7 =
      6.0e26 * secondsPerDay * 4 * Real.pi * 1.25 ^ 2 * 1e-26 * 1e-24 * 2e7 / gramsPerGeV /
        A ^ ((1 : ℝ) / 3) / MX := by
  unfold strongEventRate eventRatePerKgDay strongCrossSection nuclearRadius targetNucleiPerKg
  set r := A ^ ((1 : ℝ) / 3) with hr
  have h : A = r ^ 3 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num
  have hg : 0 < gramsPerGeV := by unfold gramsPerGeV; norm_num
  have h3 : 0 < r := Real.rpow_pos_of_pos hA _
  rw [mul_pow, mul_pow, h]
  field_simp
  ring

lemma cube_root_eq (a : ℝ) (ha : 0 ≤ a) : (a ^ 3) ^ ((1 : ℝ) / 3) = a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num

end GWGoal

open GWGoal in
theorem solution :
    (∀ s m : ℝ, 0.2 ≤ s → s ≤ 0.25 → 1 ≤ m → m ≤ 1e7 →
      1 ≤ eventRatePerKgDay 207
        (coherentCrossSection m (nucleusMass 207) 1 (effectiveNeutronNumber 125 82 s))
        1e-24 2e7 m) ∧
    (∀ A Q MQ : ℝ, 0 < A → (Q = 2 / 3 ∧ MQ = 100 ∨ Q = 1 / 3 ∧ MQ = 50) →
      1 ≤ eventRatePerKgDay A (photinoCrossSection (nucleusMass A) (nucleusMass A) Q MQ 1)
          1e-24 2e7 (nucleusMass A) ∧
        eventRatePerKgDay A (photinoCrossSection (nucleusMass A) (nucleusMass A) Q MQ 1)
          1e-24 2e7 (nucleusMass A) < 10) ∧
    (∀ A : ℝ, 27 ≤ A → A ≤ 207 →
      ∃ Mstar : ℝ, 1.5e13 ≤ Mstar ∧ Mstar ≤ 4.5e13 ∧
        ∀ MX : ℝ, 0 < MX → (1 ≤ strongEventRate A MX 1 1e-24 2e7 ↔ MX ≤ Mstar)) := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  refine ⟨fun s m hs1 hs2 hm1 hm2 => ?_, fun A Q MQ hA hQ => ?_, fun A hA1 hA2 => ?_⟩
  · -- coherent scattering on lead
    rw [coherent_closed 207 m _ _ (by norm_num) (by linarith)]
    set M := nucleusMass 207 with hM
    have hMv : M = 207 * 0.9383 := by rw [hM]; unfold nucleusMass nucleonMass; rfl
    set Nb := effectiveNeutronNumber 125 82 s with hNb
    have hN1 : 108.6 ≤ Nb := by rw [hNb]; unfold effectiveNeutronNumber; nlinarith
    have hN2 : 108.6 ^ 2 ≤ Nb ^ 2 := pow_le_pow_left₀ (by norm_num) hN1 2
    have hMp : 0 < M := by rw [hMv]; norm_num
    -- m/(m+M)^2 is minimized at m = 1e7 on [1, 1e7]
    have hf : (m + M) ^ 2 * 1e7 ≤ m * (1e7 + M) ^ 2 := by
      have h1 : 0 ≤ (1e7 - m) * (1e7 * m - M ^ 2) := by
        apply mul_nonneg (by linarith)
        rw [hMv]; nlinarith
      nlinarith
    rw [le_div_iff₀ (by positivity), one_mul]
    unfold secondsPerDay fermiConstant hbarc gramsPerGeV
    rw [hMv] at hf ⊢
    have hpos : 0 < (m + 207 * 0.9383) ^ 2 := by positivity
    have step1 : 207 * Real.pi * (m + 207 * 0.9383) ^ 2 ≤
        207 * 3.141593 * (m * (1e7 + 207 * 0.9383) ^ 2 / 1e7) := by
      apply mul_le_mul (by nlinarith) (by rw [le_div_iff₀ (by norm_num)]; linarith)
        (by positivity) (by norm_num)
    have step2 : 207 * 3.141593 * (m * (1e7 + 207 * 0.9383) ^ 2 / 1e7) ≤
        6.0e26 * 1e-24 * 2e7 * 86400 * 1.1663787e-5 ^ 2 * 1.97326980e-14 ^ 2 /
          (2 * 1.78266192e-24) * (207 * 0.9383) ^ 2 * 1 ^ 2 * 108.6 ^ 2 * m := by
      have : (207 : ℝ) * 3.141593 * ((1e7 + 207 * 0.9383) ^ 2 / 1e7) ≤
          6.0e26 * 1e-24 * 2e7 * 86400 * 1.1663787e-5 ^ 2 * 1.97326980e-14 ^ 2 /
            (2 * 1.78266192e-24) * (207 * 0.9383) ^ 2 * 1 ^ 2 * 108.6 ^ 2 := by norm_num
      nlinarith
    have step3 : 6.0e26 * 1e-24 * 2e7 * 86400 * 1.1663787e-5 ^ 2 * 1.97326980e-14 ^ 2 /
          (2 * 1.78266192e-24) * (207 * 0.9383) ^ 2 * 1 ^ 2 * 108.6 ^ 2 * m ≤
        6.0e26 * 1e-24 * 2e7 * 86400 * 1.1663787e-5 ^ 2 * 1.97326980e-14 ^ 2 /
          (2 * 1.78266192e-24) * (207 * 0.9383) ^ 2 * 1 ^ 2 * Nb ^ 2 * m := by
      have hm0 : 0 ≤ m := by linarith
      gcongr
    linarith
  · -- photino scattering
    have hMQ : 0 < MQ := by rcases hQ with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> norm_num
    rw [photino_closed A Q MQ hA hMQ]
    have hq : Q ^ 4 / MQ ^ 4 = (2 / 3) ^ 4 / 100 ^ 4 := by
      rcases hQ with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
    have e : 6.0e26 * 1e-24 * 2e7 * secondsPerDay * 16 * Real.pi * fineStructure ^ 2 * hbarc ^ 2 *
        nucleonMass * Q ^ 4 / MQ ^ 4 / gramsPerGeV =
        6.0e26 * 1e-24 * 2e7 * secondsPerDay * 16 * Real.pi * fineStructure ^ 2 * hbarc ^ 2 *
        nucleonMass * (Q ^ 4 / MQ ^ 4) / gramsPerGeV := by ring
    rw [e, hq]
    unfold secondsPerDay fineStructure hbarc nucleonMass gramsPerGeV
    constructor
    · rw [le_div_iff₀ (by norm_num)]; nlinarith
    · rw [div_lt_iff₀ (by norm_num)]; nlinarith
  · -- strongly interacting particles
    have hA : 0 < A := by linarith
    set K := 6.0e26 * secondsPerDay * 4 * Real.pi * 1.25 ^ 2 * 1e-26 * 1e-24 * 2e7 / gramsPerGeV
      with hK
    set r := A ^ ((1 : ℝ) / 3) with hr
    have hr1 : 3 ≤ r := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 27) hA1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have e : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
        rw [show (27 : ℝ) = 3 ^ 3 by norm_num]; exact cube_root_eq 3 (by norm_num)
      rw [e] at h; exact h
    have hr2 : r ≤ 6 := by
      have h := Real.rpow_le_rpow hA.le (by linarith : A ≤ 216) (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have e : (216 : ℝ) ^ ((1 : ℝ) / 3) = 6 := by
        rw [show (216 : ℝ) = 6 ^ 3 by norm_num]; exact cube_root_eq 6 (by norm_num)
      rw [e] at h; exact h
    have hK1 : 1.13e14 ≤ K := by
      rw [hK]; unfold secondsPerDay gramsPerGeV
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    have hK2 : K ≤ 1.15e14 := by
      rw [hK]; unfold secondsPerDay gramsPerGeV
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    refine ⟨K / r, ?_, ?_, fun MX hMX => ?_⟩
    · rw [le_div_iff₀ (by linarith)]; nlinarith
    · rw [div_le_iff₀ (by linarith)]; nlinarith
    · rw [strong_closed A MX hA hMX, ← hK, ← hr, le_div_iff₀ hMX, one_mul]
