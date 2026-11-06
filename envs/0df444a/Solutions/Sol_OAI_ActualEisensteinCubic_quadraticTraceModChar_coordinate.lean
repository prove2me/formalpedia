-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.quadraticTraceModChar_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:26:26.950754+00:00
-- url     : https://prove2.me/submissions/0d5ed1a1-2043-4fea-ae3d-3994636e2552

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_eisenstein_coord_norm_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_breveE_quadratic_coordinate
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_eval
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
open EisensteinEmbedding ConcreteTraceCRT Complex
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (a b x y : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let z : O := ActualEisensteinCoordinates.eval x y
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc)
      (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) =
      Complex.exp (2 * Real.pi * Complex.I *
        ((-b*x*x + 2*a*x*y + (b-a)*y*y : ℤ) : ℂ) /
        ((a*a-a*b+b*b : ℤ) : ℂ)) := by
  have hq : a*a-a*b+b*b ≠ 0 := by
    intro h
    obtain ⟨ha,hb⟩ := eisenstein_coord_norm_zero a b h
    subst a
    subst b
    exact hc (by simp [ActualEisensteinCoordinates.eval])
  change ShortDraftTrace.breveE
    (eisEmbedding (ActualEisensteinCoordinates.eval x y ^ 2) /
      (eisEmbedding (ActualEisensteinCoordinates.eval a b) * eisLam)) = _
  rw [map_pow, eisEmbedding_eval, eisEmbedding_eval]
  exact breveE_quadratic_coordinate a b x y hq
end OAI.ActualEisensteinCubic
