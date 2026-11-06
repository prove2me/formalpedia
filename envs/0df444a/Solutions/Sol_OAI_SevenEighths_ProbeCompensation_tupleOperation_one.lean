-- Prove2me | solution 1 for OAI.SevenEighths.ProbeCompensation.tupleOperation_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:10:18.757814+00:00
-- url     : https://prove2.me/submissions/23bdb9b6-f228-47bb-9912-f21be0253bfd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Compensation

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeCompensation
namespace OAI.SevenEighths.ProbeCompensation
theorem _root_.solution {α : Type*} [CommMonoid α]
    (p : Fin 1 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z =
      star (η (p 0)) * F (p 0) X Y (Z * q (p 0)) -
      ((q (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * F 1 (X / q (p 0)) (Y / q (p 0)) Z := by
  have hp : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  simp only [tupleOperation, hp]
  simp [hq, hη]
  ring
end OAI.SevenEighths.ProbeCompensation
