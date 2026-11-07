-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberMellin_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:50:54.826123+00:00
-- url     : https://prove2.me/submissions/27ae5826-a526-4162-8a3b-ae9847980ea8

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftMellin_inverse_mellin_analytic_of_flat
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
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    (weight : Ideal O → ℂ) (σ : ℝ) (hσpos : 0 < σ)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => normFiberExpSum weight D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => normFiberExpSum weight D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b)) :
    AnalyticOnNhd ℂ (normFiberMellin weight) {s : ℂ | σ < s.re} := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => normFiberExpSum weight D⁻¹) (-s)) U :=
    ShortDraftMellin.inverse_mellin_analytic_of_flat _ σ hlocal htop hflat
  have hGamma : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hGamma0 : ∀ s ∈ U, Complex.Gamma s ≠ 0 := by
    intro s hs
    exact Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hs)
  exact hM.div hGamma hGamma0
end OAI.ShortDraftHeckeBridge
