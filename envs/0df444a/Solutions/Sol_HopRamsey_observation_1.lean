-- Prove2me | solution 1 for HopRamsey.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:37:04.065892+00:00
-- url     : https://prove2.me/submissions/c4c27122-52cd-4fa3-b6ab-2c1fb1ff36a9

import Definitions.Def_HopRamsey_Fig2Params

namespace HopRamsey.Obs1Aux
open HopRamsey

theorem radius_closed (L : ℕ) (hL : 1 ≤ L) (Δ : ℝ) :
    ∀ ℓ : ℕ, ℓ ≤ L →
      radius L Δ ℓ = Δ * (2 ^ (ℓ + 1) - 1) / 2 ^ (L + 4) + ℓ * Δ / (8 * L) := by
  intro ℓ
  induction ℓ with
  | zero => intro _; simp [radius]; ring
  | succ ℓ ih =>
    intro hℓ
    rw [radius, ih (by omega)]
    have hp : (2:ℝ) ^ (L - (ℓ + 1) + 4) * 2 ^ (ℓ + 1) = 2 ^ (L + 4) := by
      rw [← pow_add]; congr 1; omega
    have h2 : (0:ℝ) < 2 ^ (L - (ℓ + 1) + 4) := by positivity
    have hL' : (0:ℝ) < L := by exact_mod_cast hL
    have e : Δ / 2 ^ (L - (ℓ + 1) + 4) = Δ * 2 ^ (ℓ + 1) / 2 ^ (L + 4) := by
      rw [← hp]; field_simp
    rw [e]; push_cast; field_simp; ring

end HopRamsey.Obs1Aux

open HopRamsey HopRamsey.Obs1Aux in
theorem solution (L : ℕ) (hL : 1 ≤ L) (Δ : ℝ) (hΔ : 0 < Δ) :
    radius L Δ L = Δ / 4 - Δ / 2 ^ (L + 4) ∧ radius L Δ L < Δ / 4 := by
  have h := radius_closed L hL Δ L le_rfl
  have hL' : (0:ℝ) < L := by exact_mod_cast hL
  have hp : (0:ℝ) < 2 ^ (L + 4) := by positivity
  have e : radius L Δ L = Δ / 4 - Δ / 2 ^ (L + 4) := by
    rw [h]; field_simp; ring
  refine ⟨e, ?_⟩
  rw [e]; have : 0 < Δ / 2 ^ (L + 4) := by positivity
  linarith
