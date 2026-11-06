-- Prove2me | solution 1 for OAI.GaussCRT.gauss_shift_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:37.187304+00:00
-- url     : https://prove2.me/submissions/03a7de59-1a1b-4024-9732-21530fa54c7c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open Finset Complex
open scoped Classical
open OAI.GaussCRT
namespace OAI.GaussCRT
theorem _root_.solution (m n r : ℕ) [NeZero m]
    (χ : MulChar (ZMod m) ℂ)
    (hr : ((n * r : ℕ) : ZMod m) = 1) :
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by
  have hrprod : (n : ZMod m) * (r : ZMod m) = 1 := by
    simpa only [Nat.cast_mul] using hr
  have hur : IsUnit (r : ZMod m) :=
    IsUnit.of_mul_eq_one_right (n : ZMod m) hrprod
  have hcharprod : χ (n : ZMod m) * χ (r : ZMod m) = 1 := by
    rw [← map_mul, hrprod, map_one]
  have hshift := gaussSum_mulShift χ (ZMod.stdAddChar (N := m)) hur.unit
  have hshift' : χ (r : ZMod m) *
      gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
      gaussSum χ (ZMod.stdAddChar (N := m)) := by
    simpa only [hur.unit_spec] using hshift
  calc
    gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) =
        (χ (n : ZMod m) * χ (r : ZMod m)) *
          gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m)) := by
            rw [hcharprod, one_mul]
    _ = χ (n : ZMod m) *
          (χ (r : ZMod m) *
            gaussSum χ ((ZMod.stdAddChar (N := m)).mulShift (r : ZMod m))) := by ring
    _ = χ (n : ZMod m) * gaussSum χ (ZMod.stdAddChar (N := m)) := by rw [hshift']
end OAI.GaussCRT
