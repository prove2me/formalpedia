-- Prove2me | solution 1 for MomentSearch.rakhmanov_midpoint_nodal_envelope
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:25:40.457593+00:00
-- url     : https://prove2.me/submissions/25a9a3df-3d4d-42d0-88a2-65006f877d3c

import Mathlib
import Theorems.Thm_MomentSearch_gamma_half_shift_stirling_bounds
import Theorems.Thm_MomentSearch_midpoint_nodal_gamma_identities

theorem solution :
    ∀ N : ℕ, 0 < N →
      let ζ : ℕ → ℝ := fun j => -1 + (2 * (j : ℝ) - 1) / (N : ℝ)
      let w : ℝ → ℝ := fun z => Real.exp (-(N : ℝ) / 2 *
        ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)))
      let T := Lagrange.nodal (Finset.Icc 1 N) ζ
      let b : ℝ := Real.pi * N / 2
      ∃ c : ℝ, 0 < c ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1,
          |T.eval x| ≤ 2 * c * |Real.cos (b * (x + 1))| / w x) ∧
        (∀ j ∈ Finset.Icc 1 N,
          c * b / w (ζ j) ≤ |T.derivative.eval (ζ j)|) := by
  intro N hN ζ w T b
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let a : ℝ := (N : ℝ) / 2
  let E : ℝ := Real.exp ((N : ℝ) * Real.log a - N)
  let c : ℝ := (2 / (N : ℝ)) ^ N * E
  let G (x : ℝ) : ℝ := (2 / (N : ℝ)) ^ N / Real.pi *
    (Real.Gamma (a * (1 + x) + 1 / 2) * Real.Gamma (a * (1 - x) + 1 / 2))
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c, E]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hW (x : ℝ) : 0 < w x := Real.exp_pos _
  have hG (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      c ≤ G x * w x ∧ G x * w x ≤ 2 * c := by
    let u : ℝ := a * (1 + x)
    let v : ℝ := a * (1 - x)
    have hu : 0 ≤ u := mul_nonneg ha.le (by linarith [hx.1])
    have hv : 0 ≤ v := mul_nonneg ha.le (by linarith [hx.2])
    let U := Real.exp (u * Real.log u - u)
    let V := Real.exp (v * Real.log v - v)
    have hU : 0 ≤ U := (Real.exp_pos _).le
    have hV : 0 ≤ V := (Real.exp_pos _).le
    have log_scale (t : ℝ) :
        (a * t) * Real.log (a * t) =
          (a * t) * Real.log a + a * (t * Real.log t) := by
      by_cases ht : t = 0
      · simp [ht]
      · rw [Real.log_mul ha.ne' ht]
        ring
    have hexp : U * V * w x = E := by
      change Real.exp (u * Real.log u - u) * Real.exp (v * Real.log v - v) *
        Real.exp (-(N : ℝ) / 2 * ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x))) = _
      rw [← Real.exp_add, ← Real.exp_add]
      dsimp [u, v, E]
      rw [log_scale (1 + x), log_scale (1 - x)]
      dsimp [a]
      congr 1
      ring
    obtain ⟨hlu, huu⟩ := MomentSearch.gamma_half_shift_stirling_bounds u hu
    obtain ⟨hlv, huv⟩ := MomentSearch.gamma_half_shift_stirling_bounds v hv
    have hgv : 0 ≤ Real.Gamma (v + 1 / 2) := (mul_nonneg (Real.sqrt_nonneg _) hV).trans hlv
    have hlprod : Real.pi * (U * V) ≤ Real.Gamma (u + 1 / 2) * Real.Gamma (v + 1 / 2) := by
      calc
        _ = (Real.sqrt Real.pi * U) * (Real.sqrt Real.pi * V) := by
          rw [show (Real.sqrt Real.pi * U) * (Real.sqrt Real.pi * V) =
            (Real.sqrt Real.pi) ^ 2 * (U * V) by ring, Real.sq_sqrt Real.pi_pos.le]
        _ ≤ _ := mul_le_mul hlu hlv (mul_nonneg (Real.sqrt_nonneg _) hV)
          ((mul_nonneg (Real.sqrt_nonneg _) hU).trans hlu)
    have huprod : Real.Gamma (u + 1 / 2) * Real.Gamma (v + 1 / 2) ≤
        (2 * Real.pi) * (U * V) := by
      calc
        _ ≤ (Real.sqrt (2 * Real.pi) * U) * (Real.sqrt (2 * Real.pi) * V) :=
          mul_le_mul huu huv hgv (mul_nonneg (Real.sqrt_nonneg _) hU)
        _ = _ := by
          rw [show (Real.sqrt (2 * Real.pi) * U) * (Real.sqrt (2 * Real.pi) * V) =
            (Real.sqrt (2 * Real.pi)) ^ 2 * (U * V) by ring, Real.sq_sqrt (by positivity)]
    let S : ℝ := (2 / (N : ℝ)) ^ N / Real.pi
    have hS : 0 ≤ S := by dsimp [S]; positivity
    have hL := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlprod hS) (hW x).le
    have hU' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huprod hS) (hW x).le
    have h₁ : S * (Real.pi * (U * V)) * w x = c := by
      calc
        _ = (S * Real.pi) * (U * V * w x) := by ring
        _ = c := by rw [hexp]; dsimp [c, S]; field_simp [Real.pi_ne_zero]
    have h₂ : S * (2 * Real.pi * (U * V)) * w x = 2 * c := by
      calc
        _ = 2 * (S * (Real.pi * (U * V)) * w x) := by ring
        _ = _ := by rw [h₁]
    rw [h₁] at hL
    rw [h₂] at hU'
    exact ⟨hL, hU'⟩
  obtain ⟨hident, hderiv⟩ := MomentSearch.midpoint_nodal_gamma_identities N hN
  refine ⟨c, hc, ?_, ?_⟩
  · intro x hx
    have he : |T.eval x| = G x * |Real.cos (b * (x + 1))| := hident x hx
    rw [he]
    apply (le_div_iff₀ (hW x)).2
    calc
      _ = (G x * w x) * |Real.cos (b * (x + 1))| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hG x hx).2 (abs_nonneg _)
  · intro j hj
    have hmem := Finset.mem_Icc.mp hj
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hmem.1
    have hjN : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmem.2
    have hz : ζ j ∈ Set.Icc (-1 : ℝ) 1 := by
      change -1 ≤ -1 + (2 * (j : ℝ) - 1) / (N : ℝ) ∧
        -1 + (2 * (j : ℝ) - 1) / (N : ℝ) ≤ 1
      constructor
      · have h : 0 ≤ (2 * (j : ℝ) - 1) / (N : ℝ) := div_nonneg (by linarith) hNr.le
        linarith
      · have h : (2 * (j : ℝ) - 1) / (N : ℝ) ≤ 2 :=
          (div_le_iff₀ hNr).2 (by linarith)
        linarith
    have he : |T.derivative.eval (ζ j)| = G (ζ j) * b := hderiv j hj
    rw [he]
    apply (div_le_iff₀ (hW _)).2
    calc
      c * b ≤ (G (ζ j) * w (ζ j)) * b := mul_le_mul_of_nonneg_right (hG _ hz).1 hb.le
      _ = _ := by ring
