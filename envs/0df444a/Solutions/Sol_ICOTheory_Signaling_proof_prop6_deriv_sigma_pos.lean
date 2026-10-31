-- Prove2me | solution 1 for ICOTheory.Signaling.proof_prop6_deriv_sigma_pos
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T21:06:46.326549+00:00
-- url     : https://prove2.me/submissions/c09c42db-a6f3-468d-ac75-dc59340e47b2

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar
open ICOTheory.Signaling

theorem solution{μH μL σ γ : ℝ} (hμ : μL < μH) (hσ : 0 < σ) (hγ : 0 < γ) :
    0 < deriv (fun s => alphaStar μH μL s γ) σ := by
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 4 * μH - 4 * μL := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; linarith
  have hx : 0 < σ ^ 2 * γ := by positivity
  have hin : 0 < A * (A + 2 * σ ^ 2 * γ) := by positivity
  have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * σ) σ := by
    simpa using hasDerivAt_pow 2 σ
  have h1 : HasDerivAt (fun s : ℝ => A * (A + 2 * s ^ 2 * γ)) (A * (2 * (2 * σ) * γ)) σ :=
    (((hpow.const_mul 2).mul_const γ).const_add A).const_mul A
  have h2 := h1.sqrt hin.ne'
  have h4 : HasDerivAt (fun s : ℝ => s ^ 2 * γ) (2 * σ * γ) σ := hpow.mul_const γ
  have h3 : HasDerivAt (fun s : ℝ => A + s ^ 2 * γ) (2 * σ * γ) σ := h4.const_add A
  have h5 := (h3.sub h2).div h4 hx.ne'
  have hfun : (fun s => alphaStar μH μL s γ) =
      ((fun s : ℝ => A + s ^ 2 * γ) - fun y : ℝ => Real.sqrt (A * (A + 2 * y ^ 2 * γ))) /
        fun s : ℝ => s ^ 2 * γ := by
    funext s; simp only [Pi.div_apply, Pi.sub_apply]; unfold alphaStar; rw [hAdef]
  rw [hfun, h5.deriv]
  set S := Real.sqrt (A * (A + 2 * σ ^ 2 * γ)) with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr hin
  have hS2 : S ^ 2 = A * (A + 2 * σ ^ 2 * γ) := Real.sq_sqrt hin.le
  have key : S < A + σ ^ 2 * γ := by nlinarith
  apply div_pos _ (by positivity)
  have e : A * (2 * (2 * σ) * γ) / (2 * S) = 2 * σ * γ * A / S := by
    field_simp <;> ring
  rw [e]
  set u := 2 * σ * γ * A / S with hudef
  have hu : u * S = 2 * σ * γ * A := div_mul_cancel₀ _ hS.ne'
  have hpos : 0 < S * ((2 * σ * γ - u) * (σ ^ 2 * γ) - (A + σ ^ 2 * γ - S) * (2 * σ * γ)) := by
    have : S * ((2 * σ * γ - u) * (σ ^ 2 * γ) - (A + σ ^ 2 * γ - S) * (2 * σ * γ)) =
        2 * σ * γ * A * (A + σ ^ 2 * γ - S) := by
      linear_combination (-(σ ^ 2 * γ)) * hu + (2 * σ * γ) * hS2
    rw [this]
    exact mul_pos (by positivity) (by linarith)
  exact (mul_pos_iff_of_pos_left hS).mp hpos
