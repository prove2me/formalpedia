-- Prove2me | solution 2 for OAI.PoissonChildCRT.mask_absorb_char
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:11:13.595241+00:00
-- url     : https://prove2.me/submissions/f00674ca-fe96-4652-a1d5-635058cb8394

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

theorem solution (e : ℕ) :
    mask n e * χ (e : ZMod n) = χ (e : ZMod n) := by
  by_cases h : n.Coprime e
  · simp [mask, h]
  · have he : ¬ IsUnit (e : ZMod n) := by
      rw [ZMod.isUnit_iff_coprime]
      exact fun h' ↦ h h'.symm
    simp [mask, h, MulChar.map_nonunit χ he]
