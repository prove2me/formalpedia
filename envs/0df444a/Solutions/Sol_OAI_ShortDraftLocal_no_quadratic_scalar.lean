-- Prove2me | solution 1 for OAI.ShortDraftLocal.no_quadratic_scalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:01.127577+00:00
-- url     : https://prove2.me/submissions/b9bf48ac-01b7-4302-ba29-a498e8464335

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open OAI.ShortDraftLocal
namespace OAI.ShortDraftLocal
theorem _root_.solution {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : χ ≠ χ ^ 3) (c : ℂ) (hc : c ≠ 0) :
    ¬ ∃ d : ℂ, ∀ x : F, c * χ x = d * (χ ^ 3) x := by
  rintro ⟨d, hd⟩
  have hcd : c = d := by
    have h := hd 1
    simpa using h
  apply hχ
  ext x
  have h := hd x
  rw [← hcd] at h
  exact mul_left_cancel₀ hc h
end OAI.ShortDraftLocal
