-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_cubicChar_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:19:43.114201+00:00
-- url     : https://prove2.me/submissions/4856b5e4-66b7-4271-8027-d65f34fc35f8

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ActualEisensteinCubic_cubicChar_pow_three


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
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open ShortDraftCusp
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) :
    cubicChar P hgood (-1 : O ⧸ P) = 1 := by
  let χ := cubicChar P hgood
  have hcube : χ (-1 : O ⧸ P) ^ 3 = 1 := by
    rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
    exact MulChar.one_apply isUnit_neg_one
  have hminus : (-1 : O ⧸ P) ^ 3 = -1 := by ring
  calc
    χ (-1 : O ⧸ P) = χ ((-1 : O ⧸ P) ^ 3) := by rw [hminus]
    _ = χ (-1 : O ⧸ P) ^ 3 := by rw [map_pow]
    _ = 1 := hcube
end OAI.ActualEisensteinCubic
