-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_quadratic_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:23:26.605539+00:00
-- url     : https://prove2.me/submissions/8a5bede0-b71c-4306-9cb8-3a09f6fb9e72

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_rational_trace
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (m : ℕ) (hm : m ≠ 0)
    (a b : ZMod m) :
    letI : NeZero m := ⟨hm⟩
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      breveE_period_coordinates (m : O) (by exact_mod_cast hm)
    ψ ((rationalCoordEquiv m hm (a,b)) ^ 2) =
      ZMod.stdAddChar (2*a*b - b^2) := by
  let : NeZero m := ⟨hm⟩
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    breveE_period_coordinates (m : O) (by exact_mod_cast hm)
  let A : ℤ := ZMod.cast a
  let B : ℤ := ZMod.cast b
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval (ZMod.cast a) (ZMod.cast b) ^ 2) /
      (eisEmbedding (m : O) * eisLam)) = _
  rw [pow_two, ActualEisensteinCoordinates.eval_mul]
  rw [eisEmbedding_eval, map_natCast]
  change ShortDraftTrace.breveE
    ((((A*A-B*B : ℤ) : ℂ) + ((A*B+B*A-B*B : ℤ) : ℂ) * omega3) /
      ((m : ℂ) * eisLam)) = _
  have hdiv (X : ℂ) : X / ((m : ℂ) * eisLam) = (X / eisLam) / m := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hdiv, breveE_rational_trace]
  congr 1
  dsimp [A, B]
  push_cast
  ring
end OAI.ActualEisensteinCubic
