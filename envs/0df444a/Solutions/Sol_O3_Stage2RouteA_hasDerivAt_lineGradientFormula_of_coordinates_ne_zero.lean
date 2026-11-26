-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_lineGradientFormula_of_coordinates_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:36:14.572854+00:00
-- url     : https://prove2.me/submissions/d979d4ec-58c8-4163-aaab-1bb6f3572c0d

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePower
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePowerPair_of_coordinates_ne_zero
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution
    {p : ℝ} (hp : 1 < p) {d : ℕ} (x h : Point d) (t : ℝ)
    (hzvec : x + t • h ≠ 0)
    (hz : ∀ i : Fin d, (x + t • h) i ≠ 0) :
    HasDerivAt (lineGradientFormula p x h)
      ((2 - p) * (linePower p x h t) ^ (2 / p - 2) *
          (linePowerPair p x h t) ^ (2 : ℕ) +
        (p - 1) * (linePower p x h t) ^ (2 / p - 1) *
          weightedSquareSum p x h t) t := by
  have hp0 : p ≠ 0 := by linarith
  have hS : linePower p x h t ≠ 0 :=
    (lpPower_pos_of_ne_zero hzvec).ne'
  have hcoeff := (hasDerivAt_linePower hp x h t).rpow_const
    (Or.inl hS) (p := 2 / p - 1)
  have hpair := hasDerivAt_linePowerPair_of_coordinates_ne_zero
    (p := p) x h t hz
  have hprod := hcoeff.mul hpair
  have hraw :
      linePowerDerivative p x h t * (2 / p - 1) *
          linePower p x h t ^ (2 / p - 1 - 1) * linePowerPair p x h t +
        linePower p x h t ^ (2 / p - 1) *
          ((p - 1) * weightedSquareSum p x h t) =
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
          linePowerPair p x h t ^ (2 : ℕ) +
        (p - 1) * linePower p x h t ^ (2 / p - 1) *
          weightedSquareSum p x h t := by
    have hexp : 2 / p - 1 - 1 = 2 / p - 2 := by ring
    rw [hexp, linePowerDerivative]
    unfold linePowerPair
    field_simp
  rw [← hraw]
  change HasDerivAt
    ((fun s : ℝ ↦ linePower p x h s ^ (2 / p - 1)) * linePowerPair p x h)
    (linePowerDerivative p x h t * (2 / p - 1) *
        linePower p x h t ^ (2 / p - 1 - 1) * linePowerPair p x h t +
      linePower p x h t ^ (2 / p - 1) *
        ((p - 1) * weightedSquareSum p x h t)) t
  exact hprod
end O3.Stage2RouteA
