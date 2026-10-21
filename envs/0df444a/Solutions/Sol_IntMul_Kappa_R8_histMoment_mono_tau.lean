-- Prove2me | solution 1 for IntMul.Kappa.R8.histMoment_mono_tau
-- status  : ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:08:26.508973+00:00
-- url     : https://prove2.me/submissions/427163f5-11f9-4cb7-b704-607ccecb1547

import Definitions.Def_IntMul_KappaFramework

set_option autoImplicit false
set_option relaxedAutoImplicit false

open IntMul.Kappa

theorem solution (h : List (ℕ × ℕ)) (m : ℕ) (τ₁ τ₂ : ℝ)
    (hm : 0 < m)
    (hw : ∀ p ∈ h, 0 < p.1 ∧ p.1 ≤ m)
    ( _hτ : 0 ≤ τ₁) (hle : τ₁ ≤ τ₂) :
    histMoment h m τ₂ ≤ histMoment h m τ₁ := by
  unfold histMoment
  refine List.sum_le_sum ?_
  intro p hp
  obtain ⟨hw0, hwm⟩ := hw p hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hwR : (0 : ℝ) < p.1 := by exact_mod_cast hw0
  have hbase : (0 : ℝ) < (p.1 : ℝ) / m ∧ (p.1 : ℝ) / m ≤ 1 := by
    constructor
    · exact div_pos hwR hmR
    · exact (div_le_one hmR).mpr (by exact_mod_cast hwm)
  have hpow : ((p.1 : ℝ) / m) ^ τ₂ ≤ ((p.1 : ℝ) / m) ^ τ₁ :=
    Real.rpow_le_rpow_of_exponent_ge hbase.1 hbase.2 hle
  have hn : (0 : ℝ) ≤ p.2 := by exact_mod_cast (Nat.zero_le _)
  exact mul_le_mul_of_nonneg_left hpow hn

