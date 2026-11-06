-- Prove2me | solution 1 for OAI.PoissonChildCRT.child_row_label_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:32.074468+00:00
-- url     : https://prove2.me/submissions/1853b080-a527-4750-9925-4ec6647b63e2

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonChildCRT_inverse_as_row_and_label

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open OAI.PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
namespace OAI.PoissonChildCRT
theorem _root_.solution (hχ : χ ^ 6 = 1)
    (d e k J C v : ℕ) :
    (χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4
      = χ ((d * e * k : ℕ) : ZMod n) *
        (χ ((J * C * e * v : ℕ) : ZMod n)) ^ 4 := by
  rw [inverse_as_row_and_label n χ hχ e]
  simp only [Nat.cast_mul, map_mul]
  ring
end OAI.PoissonChildCRT
