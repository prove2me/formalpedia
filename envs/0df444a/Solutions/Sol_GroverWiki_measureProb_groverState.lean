-- Prove2me | solution 1 for GroverWiki.measureProb_groverState
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T19:51:42.766162+00:00
-- url     : https://prove2.me/submissions/d228362b-1eac-4847-bdcf-1368a7d20173

import Mathlib
import Definitions.Def_GroverWiki_Defs
import Theorems.Thm_GroverWiki_groverIteration_rotation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (r : ℕ) :
    measureProb (groverState f r) ω =
      Real.sin ((r + 1 / 2) * (2 * Real.arcsin (1 / Real.sqrt N))) ^ 2 := by
  classical
  have hNp : 0 < N := lt_of_le_of_lt (Nat.zero_le ω.val) ω.isLt
  let t : ℝ := Real.arcsin (1 / Real.sqrt N)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNp)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNp
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := by
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
  have hx1 : 1 / Real.sqrt (N : ℝ) ≤ 1 := (div_le_one hs).2 hs1
  have hsin : Real.sin t = 1 / Real.sqrt N := by
    exact Real.sin_arcsin (by linarith [one_div_pos.mpr hs]) hx1
  have hinit : uniformState N =
      (Real.cos t : ℂ) • perpState ω + (Real.sin t : ℂ) • ket ω := by
    by_cases hN1 : N = 1
    · subst N
      ext i
      have hi : i = ω := Subsingleton.elim _ _
      subst i
      simp [t, uniformState, perpState, ket]
    · have hN2 : 2 ≤ N := by omega
      have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      have ht : Real.sqrt ((N : ℝ) - 1) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (by linarith))
      have he : 1 - (1 / Real.sqrt (N : ℝ)) ^ 2 = ((N : ℝ) - 1) / N := by
        field_simp
        nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
      have hcos : Real.cos t = Real.sqrt ((N : ℝ) - 1) / Real.sqrt N := by
        dsimp [t]
        rw [Real.cos_arcsin, he, Real.sqrt_div (by linarith : (0 : ℝ) ≤ (N : ℝ) - 1)]
      ext i
      by_cases hi : i = ω
      · subst i
        simp [uniformState, perpState, ket, hsin, div_eq_mul_inv, Complex.ofReal_inv]
      · simp [uniformState, perpState, ket, hi, Ne.symm hi, hcos,
          Complex.ofReal_div, Complex.ofReal_inv]
        have htc : (Real.sqrt ((N : ℝ) - 1) : ℂ) ≠ 0 := by exact_mod_cast ht
        field_simp
  have hrot (φ : ℝ) : groverIteration f *ᵥ
      ((Real.cos φ : ℂ) • perpState ω + (Real.sin φ : ℂ) • ket ω) =
      (Real.cos (φ + 2 * t) : ℂ) • perpState ω +
        (Real.sin (φ + 2 * t) : ℂ) • ket ω := by
    by_cases hN1 : N = 1
    · subst N
      have hf : ∀ i : Fin 1, f i = 1 := fun i => (hω i).2 (Subsingleton.elim _ _)
      have hω0 : ω = 0 := Subsingleton.elim _ _
      subst ω
      have ht1 : t = Real.pi / 2 := by simp [t]
      have hang1 : φ + 2 * t = φ + Real.pi := by rw [ht1]; ring
      rw [hang1, Real.cos_add_pi, Real.sin_add_pi]
      ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [groverIteration, diffusion, phaseOracle, uniformState, perpState, ket,
        Matrix.mulVec, dotProduct, Matrix.mul_apply, vecMulVec, hf] <;> ring
    · exact GroverWiki.groverIteration_rotation (by omega) f ω hω φ
  have hstate (k : ℕ) : groverState f k =
      (Real.cos ((2 * k + 1) * t) : ℂ) • perpState ω +
        (Real.sin ((2 * k + 1) * t) : ℂ) • ket ω := by
    induction k with
    | zero => simpa [groverState] using hinit
    | succ k ih =>
      have hstep : groverState f (k + 1) = groverIteration f *ᵥ groverState f k := by
        simp [groverState, pow_succ', Matrix.mulVec_mulVec]
      rw [hstep, ih, hrot]
      have hang : (2 * (k : ℝ) + 1) * t + 2 * t = (2 * (k + 1 : ℕ) + 1) * t := by
        push_cast
        ring
      rw [hang]
  have hang : (2 * (r : ℝ) + 1) * t = (r + 1 / 2) * (2 * t) := by ring
  have hperp : perpState ω ω = 0 := by simp [perpState]
  have hket : ket ω ω = 1 := by simp [ket]
  have hcoord : (groverState f r) ω = (Real.sin ((2 * (r : ℝ) + 1) * t) : ℂ) := by
    rw [hstate]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hperp, hket,
      mul_zero, mul_one, zero_add]
  change ‖(groverState f r) ω‖ ^ 2 = _
  rw [hcoord]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, hang]
  rfl
