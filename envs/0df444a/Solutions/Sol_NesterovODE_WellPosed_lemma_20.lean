-- Prove2me | solution 1 for NesterovODE.WellPosed.lemma_20
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:39:44.691184+00:00
-- url     : https://prove2.me/submissions/019c33d2-aa45-4b7c-ba48-b52ceff71260

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting
set_option autoImplicit false
open NesterovODE.WellPosed

theorem solution {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (a t B : ℝ) (X V Y W : ℝ → E n)
    (hf : IsFL f L) (hX : IsLocalSolution f x₀ a X V)
    (hY : IsLocalSolution f x₀ a Y W)
    (ht₀ : 0 < t) (hta : t < a)
    (hB : ∀ u : ℝ, 0 ≤ u → u < t → ‖V u - W u‖ ≤ B) :
    ‖gradient f (X t) - gradient f (Y t)‖ ≤ (L : ℝ) * t * B := by
  obtain ⟨-, -, -, hLip⟩ := hf
  obtain ⟨-, hX0, hV0, hXd0, hXc0, hXd⟩ := hX
  obtain ⟨-, hY0, hW0, hYd0, hYc0, hYd⟩ := hY
  have hcont : ContinuousOn (fun u => X u - Y u) (Set.Icc 0 t) := by
    intro u hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · subst h0
      have h1 : ContinuousWithinAt X (Set.Icc 0 t) 0 :=
        hXd0.continuousWithinAt.mono (fun v hv => hv.1)
      have h2 : ContinuousWithinAt Y (Set.Icc 0 t) 0 :=
        hYd0.continuousWithinAt.mono (fun v hv => hv.1)
      exact h1.sub h2
    · have hua : u < a := lt_of_le_of_lt hu.2 hta
      have h1 := (hXd u hpos hua).1.continuousAt
      have h2 := (hYd u hpos hua).1.continuousAt
      exact (h1.sub h2).continuousWithinAt
  have hder : ∀ u ∈ Set.Ico (0:ℝ) t,
      HasDerivWithinAt (fun u => X u - Y u) (V u - W u) (Set.Ici u) u := by
    intro u hu
    rcases hu.1.eq_or_lt with h0 | hpos
    · subst h0
      exact hXd0.sub hYd0
    · have hua : u < a := lt_trans hu.2 hta
      exact ((hXd u hpos hua).1.sub (hYd u hpos hua).1).hasDerivWithinAt
  have key : ‖X t - Y t‖ ≤ B * t := by
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun u => X u - Y u) (f' := fun u => V u - W u) (a := 0) (b := t)
      (B := fun u => B * u) (B' := fun _ => B) hcont hder
      (by simp [hX0, hY0]) (fun x => by simpa using (hasDerivAt_id x).const_mul B)
      (fun x hx => hB x hx.1 hx.2) (x := t) ⟨ht₀.le, le_rfl⟩
    simpa using this
  have hL := hLip.dist_le_mul (X t) (Y t)
  have hL2 := hLip.dist_le_mul (X t) (Y t)
  rw [dist_eq_norm, dist_eq_norm] at hL
  calc ‖gradient f (X t) - gradient f (Y t)‖ ≤ (L : ℝ) * ‖X t - Y t‖ := hL
    _ ≤ (L : ℝ) * (B * t) := mul_le_mul_of_nonneg_left key L.2
    _ = (L : ℝ) * t * B := by ring
