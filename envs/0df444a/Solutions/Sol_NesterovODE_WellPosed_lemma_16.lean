-- Prove2me | solution 1 for NesterovODE.WellPosed.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:44:14.839728+00:00
-- url     : https://prove2.me/submissions/f6d21c06-66d2-4611-9503-24856e978110

import Mathlib
import Definitions.Def_NesterovODE_WellPosed_Setting
set_option autoImplicit false
open NesterovODE.WellPosed

theorem solution {n : ℕ} (f : E n → ℝ) (L : NNReal) (x₀ : E n)
    (δ : ℝ) (X V : ℝ → E n) (u B : ℝ)
    (hf : IsFL f L) (hX : IsSmoothedSolution f δ x₀ X V)
    (hu : 0 < u) (hB : ∀ v : ℝ, 0 < v → v ≤ u → ‖V v‖ / v ≤ B) :
    ‖gradient f (X u) - gradient f x₀‖ ≤
      (1 / 2 : ℝ) * (L : ℝ) * B * u ^ 2 := by
  obtain ⟨-, -, -, hLip⟩ := hf
  obtain ⟨-, hX0, hV0, hXd⟩ := hX
  have hcont : ContinuousOn (fun v => X v - x₀) (Set.Icc 0 u) := by
    intro v hv
    exact ((hXd v hv.1).1.continuousWithinAt.mono (fun w hw => hw.1)).sub_const x₀
  have hder : ∀ v ∈ Set.Ico (0:ℝ) u,
      HasDerivWithinAt (fun v => X v - x₀) (V v) (Set.Ici v) v := by
    intro v hv
    have := (hXd v hv.1).1
    have h2 : HasDerivWithinAt (fun v => X v - x₀) (V v) (Set.Ici (0:ℝ)) v := this.sub_const x₀
    exact h2.mono (fun w hw => le_trans hv.1 hw)
  have hbd : ∀ v ∈ Set.Ico (0:ℝ) u, ‖V v‖ ≤ B * v := by
    intro v hv
    rcases hv.1.eq_or_lt with h0 | hpos
    · subst h0; simp [hV0]
    · have := hB v hpos hv.2.le
      rwa [div_le_iff₀ hpos] at this
  have key : ‖X u - x₀‖ ≤ B / 2 * u ^ 2 := by
    have := image_norm_le_of_norm_deriv_right_le_deriv_boundary
      (f := fun v => X v - x₀) (f' := fun v => V v) (a := 0) (b := u)
      (B := fun v => B / 2 * v ^ 2) (B' := fun v => B * v) hcont hder
      (by simp [hX0])
      (fun x => by
        have := ((hasDerivAt_pow 2 x).const_mul (B / 2))
        refine this.congr_deriv ?_
        simp; ring)
      hbd (x := u) ⟨hu.le, le_rfl⟩
    simpa using this
  have hL := hLip.dist_le_mul (X u) x₀
  rw [dist_eq_norm, dist_eq_norm] at hL
  calc ‖gradient f (X u) - gradient f x₀‖ ≤ (L : ℝ) * ‖X u - x₀‖ := hL
    _ ≤ (L : ℝ) * (B / 2 * u ^ 2) := mul_le_mul_of_nonneg_left key L.2
    _ = (1 / 2 : ℝ) * (L : ℝ) * B * u ^ 2 := by ring
