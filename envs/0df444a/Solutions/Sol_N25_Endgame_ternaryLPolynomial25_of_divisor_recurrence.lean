-- Prove2me | solution 1 for N25.Endgame.ternaryLPolynomial25_of_divisor_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:06.220184+00:00
-- url     : https://prove2.me/submissions/c0ce8542-5217-462b-b556-d3ceaf4113bb

import Theorems.Thm_N25_Endgame_ternaryLPolynomial25_reconstruction
import Definitions.Def_N25_GenusFourNumerator

set_option autoImplicit false

namespace N25.Endgame

/-- The first four effective-divisor recurrences identify the ternary numerator.
The numbers `N₁` through `N₄` are fixed-place counts. The coefficient hypotheses
are the first four coefficients of the full curve-zeta identity.
-/
theorem _root_.solution
    (L : Polynomial ℤ) (A : ℕ → ℤ) (N₁ N₂ N₃ N₄ : ℤ)
    (hN₁ : N₁ = 5) (hN₂ : N₂ = 5) (hN₃ : N₃ = 20) (hN₄ : N₄ = 89)
    (hdegree : L.natDegree ≤ 8) (hzero : L.coeff 0 = 1)
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * 3 ^ i = 3 ^ 4 * L.coeff i)
    (hA₀ : A 0 = 1)
    (hA₁ : A 1 = N₁ * A 0)
    (hA₂ : 2 * A 2 = N₁ * A 1 + N₂ * A 0)
    (hA₃ : 3 * A 3 = N₁ * A 2 + N₂ * A 1 + N₃ * A 0)
    (hA₄ : 4 * A 4 = N₁ * A 3 + N₂ * A 2 + N₃ * A 1 + N₄ * A 0)
    (hc₁ : L.coeff 1 = A 1 - 4 * A 0)
    (hc₂ : L.coeff 2 = A 2 - 4 * A 1 + 3 * A 0)
    (hc₃ : L.coeff 3 = A 3 - 4 * A 2 + 3 * A 1)
    (hc₄ : L.coeff 4 = A 4 - 4 * A 3 + 3 * A 2) :
    L = ternaryLPolynomial25 := by
  rw [hN₁] at hA₁ hA₂ hA₃ hA₄
  rw [hN₂] at hA₂ hA₃ hA₄
  rw [hN₃] at hA₃ hA₄
  rw [hN₄] at hA₄
  have h₁ : L.coeff 1 = 1 := by omega
  have h₂ : L.coeff 2 = -2 := by omega
  have h₃ : L.coeff 3 = -5 := by omega
  have h₄ : L.coeff 4 = 1 := by omega
  apply ternaryLPolynomial25_reconstruction L hdegree hzero
  · norm_num [CountNewtonFourEquations, NewtonFourEquations, h₁, h₂, h₃, h₄]
  · exact hrec

end N25.Endgame
