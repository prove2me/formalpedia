-- Prove2me | solution 1 for OAI.PoissonChildCRT.mask_absorb_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:22.706204+00:00
-- url     : https://prove2.me/submissions/25d36328-f1cc-4fc9-b877-226216076df5

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
theorem _root_.solution (e : ℕ) :
    mask n e * χ (e : ZMod n) = χ (e : ZMod n) := by
  by_cases he : n.Coprime e
  · simp [mask, he]
  · have hnu : ¬ IsUnit (e : ZMod n) := by
      intro hu
      exact he ((ZMod.isUnit_iff_coprime e n).mp hu).symm
    have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [mask, he, hz]
end OAI.PoissonChildCRT
