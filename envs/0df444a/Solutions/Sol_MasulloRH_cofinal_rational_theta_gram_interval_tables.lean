-- Prove2me | solution 1 for MasulloRH.cofinal_rational_theta_gram_interval_tables
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:03:38.059559+00:00
-- url     : https://prove2.me/submissions/b2cd9554-8eeb-4521-ad52-9bb4009c4eab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_cofinal_exact_theta_gram_margin
import Theorems.Thm_MasulloRH_finite_rational_complex_gram_certificate

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem solution :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
      (R : Fin (m+1) → Fin (m+1) → ℚ × ℚ) (η : ℚ), 0 ≤ η ∧
      let δ : ℝ := 1/(16*((n:ℝ)+1))
      let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse n)
        (fun i x => theta (x-(y i:ℝ)))
      let d : Fin (m+1) → ℂ := Fin.cons 1
        (fun i => -(((a i).1:ℂ)+((a i).2:ℂ)*Complex.I))
      let Q : Fin (m+1) → Fin (m+1) → ℂ :=
        fun i j => ((R i j).1:ℂ)+((R i j).2:ℂ)*Complex.I
      (∀ i j, ‖(∫ x : ℝ, (Real.exp (2*(3/4)*x+2*(1/4-δ)*|x|):ℂ) *
        conj (u i x) * u j x) - Q i j‖ ≤ (η:ℝ)) ∧
      (∑ i, ∑ j, conj (d i)*d j*Q i j).re +
        (η:ℝ) * (∑ i, (|(d i).re|+|(d i).im|))^2 < δ/2 := by
  intro N
  obtain ⟨n, hn, m, a, y, hmargin⟩ := MasulloRH.cofinal_exact_theta_gram_margin N
  let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
  let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n)
    (fun i x => theta (x - (y i : ℝ)))
  let d : Fin (m + 1) → ℂ := Fin.cons 1
    (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
  let G : Fin (m + 1) → Fin (m + 1) → ℂ := fun i j =>
    ∫ x : ℝ,
      (Real.exp (2 * (3 / 4) * x + 2 * (1 / 4 - δ) * |x|) : ℂ) *
        conj (u i x) * u j x
  have hG : (∑ i, ∑ j, conj (d i) * d j * G i j).re < δ / 2 := hmargin
  obtain ⟨R, η, hη, hentry, hcertificate⟩ :=
    MasulloRH.finite_rational_complex_gram_certificate d G (δ / 2) hG
  exact ⟨n, hn, m, a, y, R, η, hη, hentry, hcertificate⟩

