-- Prove2me | solution 1 for MonotoneCompStatics.LinearPerturb.theorem10_converse_step
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:48:06.453171+00:00
-- url     : https://prove2.me/submissions/4396cc12-030c-4e29-b3c9-d2d5fda65224

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_MonotoneCompStatics_Monotonicity_QuasiSupermodularOn

theorem solution {n : ℕ} (g : (Fin n → ℝ) → ℝ)
    (h : ∀ p : Fin n → ℝ, MonotoneCompStatics.Monotonicity.QuasiSupermodularOn (fun x => g x + p ⬝ᵥ x) Set.univ) :
    Supermodularity.Monotonicity.SupermodularOn g Set.univ := by
  classical
  intro x hx y hy
  by_cases hxy : x ≤ y
  · simp only [sup_eq_right.mpr hxy, inf_eq_left.mpr hxy]
    linarith
  · have hex : ∃ i, y i < x i := by
      by_contra hn
      apply hxy
      intro i
      exact le_of_not_gt (fun hi => hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hex
    let c := (g (x ⊓ y) - g x) / (x i - y i)
    let p : Fin n → ℝ := Pi.single i c
    have dot (z : Fin n → ℝ) : p ⬝ᵥ z = c * z i := by
      simp [p, dotProduct, Pi.single_apply]
    have hci : c * (x i - y i) = g (x ⊓ y) - g x := by
      dsimp [c]
      exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hi))
    have hinf : (x ⊓ y) i = y i := min_eq_right hi.le
    have hsup : (x ⊔ y) i = x i := max_eq_left hi.le
    have hh := (h p (x := x) (by simp) (y := y) (by simp)).1
    simp only [dot, hinf, hsup] at hh
    have heq : g (x ⊓ y) + c * y i ≤ g x + c * x i := by
      nlinarith [hci]
    have hout := hh heq
    nlinarith [hci]

#print axioms solution
