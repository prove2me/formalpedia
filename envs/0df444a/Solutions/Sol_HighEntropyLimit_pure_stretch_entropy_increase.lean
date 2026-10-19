-- Prove2me | solution 1 for HighEntropyLimit.pure_stretch_entropy_increase
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:38:42.745721+00:00
-- url     : https://prove2.me/submissions/784a20df-de51-46e1-9323-8daedc5faec0

import Mathlib
import Definitions.Def_HighEntropyLimit_phase_space_stretch

open MeasureTheory HighEntropyLimit

theorem solution (lam : ℝ) (hlam : 1 < lam) (ρ : ℝ × ℝ → ℝ)
    (hρ_nonneg : ∀ z, 0 ≤ ρ z) (hρ_int : Integrable ρ) (hρ_norm : ∫ z, ρ z = 1)
    (hρ_ent : Integrable (fun z => ρ z * Real.log (ρ z))) :
    gibbsEntropy (pureStretch lam ρ) = gibbsEntropy ρ + Real.log lam := by
  unfold gibbsEntropy pureStretch
  try simp only
  have hl : 0 < lam := by linarith
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hl
  set s := Real.sqrt lam with hsdef
  have hss : s * s = lam := Real.mul_self_sqrt hl.le
  let k : ℝ × ℝ → ℝ := fun w => lam⁻¹ * (ρ w * Real.log (ρ w) - Real.log lam * ρ w)
  have hk : ∀ w, lam⁻¹ * ρ w * Real.log (lam⁻¹ * ρ w) = k w := by
    intro w
    simp only [k]
    rcases eq_or_ne (ρ w) 0 with h0 | h0
    · simp [h0]
    · rw [Real.log_mul (inv_ne_zero hl.ne') h0, Real.log_inv]; ring
  have h1 : ∀ z : ℝ × ℝ, lam⁻¹ * ρ (s⁻¹ • z) * Real.log (lam⁻¹ * ρ (s⁻¹ • z)) = k (s⁻¹ • z) :=
    fun z => hk _
  simp_rw [h1]
  rw [Measure.integral_comp_smul, Module.finrank_prod, Module.finrank_self]
  simp only [k, smul_eq_mul]
  rw [integral_const_mul, integral_sub hρ_ent (hρ_int.const_mul _), integral_const_mul, hρ_norm]
  rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
  rw [show s ^ (1 + 1) = lam by rw [← hss]; ring]
  field_simp
  ring
