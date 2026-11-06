-- Prove2me | solution 1 for OAI.PoissonChildCRT.inverse_as_row_and_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:34.80327+00:00
-- url     : https://prove2.me/submissions/4597a718-ee3b-4bb0-92cd-90e552f1f14d

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier

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
theorem _root_.solution (hχ : χ ^ 6 = 1) (e : ℕ) :
    (χ (e : ZMod n))⁻¹ = χ (e : ZMod n) * (χ (e : ZMod n)) ^ 4 := by
  by_cases he : IsUnit (e : ZMod n)
  · have h6 : (χ (e : ZMod n)) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, he]
    apply inv_eq_of_mul_eq_one_right
    calc
      χ (e : ZMod n) * (χ (e : ZMod n) * χ (e : ZMod n) ^ 4)
          = (χ (e : ZMod n)) ^ 6 := by ring
      _ = 1 := h6
  · have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ he
    simp [hz]
end OAI.PoissonChildCRT
