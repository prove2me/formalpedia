-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_lineGradientFormula_above_two_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:36:44.461572+00:00
-- url     : https://prove2.me/submissions/68cb6d2c-b27d-45c2-a074-771f3f942a06

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePower
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_linePowerPair_above_two
import Theorems.Thm_O3_lpPower_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution
    {q : ℝ} (hq : 2 < q) {d : ℕ} (x h : Point d) (t : ℝ)
    (hzvec : x + t • h ≠ 0) :
    HasDerivAt (lineGradientFormula q x h)
      ((2 - q) * (linePower q x h t) ^ (2 / q - 2) *
          (linePowerPair q x h t) ^ (2 : ℕ) +
        (q - 1) * (linePower q x h t) ^ (2 / q - 1) *
          weightedSquareSum q x h t) t := by
  have hq0 : q ≠ 0 := by linarith
  have hS : linePower q x h t ≠ 0 :=
    (lpPower_pos_of_ne_zero hzvec).ne'
  have hcoeff := (hasDerivAt_linePower (by linarith : 1 < q) x h t).rpow_const
    (Or.inl hS) (p := 2 / q - 1)
  have hpair := hasDerivAt_linePowerPair_above_two (q := q) hq x h t
  have hprod := hcoeff.mul hpair
  have hraw :
      linePowerDerivative q x h t * (2 / q - 1) *
          linePower q x h t ^ (2 / q - 1 - 1) * linePowerPair q x h t +
        linePower q x h t ^ (2 / q - 1) *
          ((q - 1) * weightedSquareSum q x h t) =
      (2 - q) * linePower q x h t ^ (2 / q - 2) *
          linePowerPair q x h t ^ (2 : ℕ) +
        (q - 1) * linePower q x h t ^ (2 / q - 1) *
          weightedSquareSum q x h t := by
    have hexp : 2 / q - 1 - 1 = 2 / q - 2 := by ring
    rw [hexp, linePowerDerivative]
    unfold linePowerPair
    field_simp
  rw [← hraw]
  change HasDerivAt
    ((fun s : ℝ ↦ linePower q x h s ^ (2 / q - 1)) * linePowerPair q x h)
    (linePowerDerivative q x h t * (2 / q - 1) *
        linePower q x h t ^ (2 / q - 1 - 1) * linePowerPair q x h t +
      linePower q x h t ^ (2 / q - 1) *
        ((q - 1) * weightedSquareSum q x h t)) t
  exact hprod
end O3.Stage2RouteA
