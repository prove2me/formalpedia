-- Prove2me | solution 1 for GravityNonRenorm.flat_bh_entropy_eq32
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T12:44:21.914992+00:00
-- url     : https://prove2.me/submissions/a2312290-5dc9-4ec4-adb4-7310fdb9de11

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm

theorem fbh32_sphereArea_pos (k : ℕ) : 0 < sphereArea k := by
  unfold sphereArea
  have : 0 < Real.Gamma (((k : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  positivity

theorem fbh32_main (d : ℕ) (hd : 4 ≤ d) (G M : ℝ) (hG : 0 < G) (hM : 0 < M) :
    flatBHEntropy d G M =
      sphereArea (d - 2) / (4 * G) *
        (omega (d - 2) * G * M) ^ (((d : ℝ) - 2) / ((d : ℝ) - 3)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 4 := ⟨d - 4, by omega⟩
  have e2 : n + 4 - 2 = n + 2 := by omega
  have e3 : n + 4 - 3 = n + 1 := by omega
  have hω : 0 < omega (n + 2) := by
    unfold omega
    have := fbh32_sphereArea_pos (n + 2)
    have : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    positivity
  set c := omega (n + 2) * G * M with hc
  have hc0 : 0 < c := by positivity
  set r0 : ℝ := c ^ (((n + 1 : ℕ) : ℝ)⁻¹) with hr0
  have hr0pos : 0 < r0 := by positivity
  have hr0pow : r0 ^ (n + 1) = c := Real.rpow_inv_natCast_pow hc0.le (by omega)
  have hset : {r : ℝ | 0 < r ∧ schwarzschildF (n + 4) G M r = 0} = {r0} := by
    ext r
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, schwarzschildF, e2, e3]
    constructor
    · rintro ⟨hr, hf⟩
      have hp : r ^ (n + 1) ≠ 0 := by positivity
      have h1 : c / r ^ (n + 1) = 1 := by rw [hc]; linarith
      have h2 : r ^ (n + 1) = c := ((div_eq_one_iff_eq hp).1 h1).symm
      rw [hr0, ← h2, Real.pow_rpow_inv_natCast hr.le (by omega)]
    · rintro rfl
      refine ⟨hr0pos, ?_⟩
      rw [← hc, hr0pow, div_self hc0.ne']
      ring
  unfold flatBHEntropy bekensteinHawkingEntropy flatHorizonRadius
  rw [hset, csSup_singleton, e2, ← hc]
  have hexp : r0 ^ (n + 2) = c ^ ((((n + 4 : ℕ) : ℝ) - 2) / (((n + 4 : ℕ) : ℝ) - 3)) := by
    rw [hr0, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    congr 1
    push_cast
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    rw [show (n : ℝ) + 4 - 2 = n + 2 by ring, show (n : ℝ) + 4 - 3 = n + 1 by ring]
    field_simp
  rw [hexp]
  ring

end GravityNonRenorm

open GravityNonRenorm in
theorem solution (d : ℕ) (hd : 4 ≤ d) (G M : ℝ) (hG : 0 < G) (hM : 0 < M) :
    flatBHEntropy d G M =
      sphereArea (d - 2) / (4 * G) *
        (omega (d - 2) * G * M) ^ (((d : ℝ) - 2) / ((d : ℝ) - 3)) :=
  fbh32_main d hd G M hG hM
