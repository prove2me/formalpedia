-- Prove2me | solution 1 for GroverWiki.phaseOracle_diffusion_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:06:58.869811+00:00
-- url     : https://prove2.me/submissions/0b0873e7-57b2-4d3b-9997-3036b29e2b6c

import Mathlib
import Definitions.Def_GroverWiki_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) :
    phaseOracle f ∈ unitaryGroup (Fin N) ℂ ∧ diffusion N ∈ unitaryGroup (Fin N) ℂ := by
  have hsign (x : Fin 2) :
      (-1 : ℂ) ^ (x : ℕ) * ((-1 : ℂ) ^ (x : ℕ)) = 1 := by
    fin_cases x <;> norm_num
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [phaseOracle, Matrix.mul_apply, Matrix.diagonal, hsign]
    · simp [phaseOracle, Matrix.mul_apply, Matrix.diagonal, hij]
      intro hji
      exact hij hji.symm
  · rw [Matrix.mem_unitaryGroup_iff]
    by_cases hN : N = 0
    · subst N
      ext i j
      exact Fin.elim0 i
    · let u : Fin N → ℂ := uniformState N
      let P : Matrix (Fin N) (Fin N) ℂ := vecMulVec u (star u)
      have hnorm : ∑ k : Fin N, star (u k) * u k = 1 := by
        simp [u, uniformState, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, hN]
        field_simp
        norm_cast
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
        norm_num
        exact hN
      have hPstar : star P = P := by
        ext i j
        simp [P, Matrix.vecMulVec, star_mul]
      have hPid : P * P = P := by
        ext i j
        simp only [Matrix.mul_apply, P, Matrix.vecMulVec]
        calc
          ∑ k, u i * star (u k) * (u k * star (u j))
              = ∑ k, (u i * (star (u k) * u k)) * star (u j) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  ring
          _ = (∑ k, u i * (star (u k) * u k)) * star (u j) := by
                rw [← Finset.sum_mul]
          _ = (u i * (∑ k, star (u k) * u k)) * star (u j) := by
                rw [← Finset.mul_sum]
          _ = u i * star (u j) := by rw [hnorm]; ring
      simp only [diffusion]
      change ((2 : ℂ) • P - 1) * star ((2 : ℂ) • P - 1) = 1
      rw [star_sub, star_smul, star_one, hPstar]
      simp [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hPid]
      ext i j
      change (2 : ℂ) * (2 * P i j - P i j) -
        (2 * P i j - (1 : Matrix (Fin N) (Fin N) ℂ) i j) =
        (1 : Matrix (Fin N) (Fin N) ℂ) i j
      ring
