-- Prove2me | solution 1 for OAI.PoissonChildCRT.mask_absorb_inv_char
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:27:20.787175+00:00
-- url     : https://prove2.me/submissions/c6d33639-ef73-421b-bdec-124ce5c45f87

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
    mask n e * (χ (e : ZMod n))⁻¹ = (χ (e : ZMod n))⁻¹ := by
  by_cases h : n.Coprime e
  · simp [mask, h]
  · have hn : ¬IsUnit (e : ZMod n) := by
      simpa [ZMod.isUnit_iff_coprime, Nat.coprime_comm] using h
    simp [mask, h, χ.map_nonunit hn]
