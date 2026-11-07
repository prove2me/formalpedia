-- Prove2me | solution 1 for OAI.CompactMellinBridge.finiteEulerFactor_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:36.307521+00:00
-- url     : https://prove2.me/submissions/51ebc614-8231-4285-871f-5fdf8425efdc

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale

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
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ShortDraftHeckeBridge.O))
    (hprime : ∀ P ∈ S, Prime P) (σ : ℝ) :
    AnalyticOnNhd ℂ (finiteEulerFactor χ S)
      {s : ℂ | σ < s.re} := by
  have hE : Differentiable ℂ (finiteEulerFactor χ S) := by
    unfold finiteEulerFactor
    apply Differentiable.fun_finsetProd
    intro P hPS
    have hN : Ideal.absNorm P ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr (hprime P hPS).1
    have hNc : (Ideal.absNorm P : ℂ) ≠ 0 := by exact_mod_cast hN
    have hcpow : Differentiable ℂ
        (fun s : ℂ => ((Ideal.absNorm P : ℂ) ^ (-s))) :=
      (differentiable_id.neg).const_cpow (Or.inl hNc)
    exact (differentiable_const (1 : ℂ)).sub
      ((differentiable_const (χ (Ideal.absNorm P))).mul hcpow)
  exact (Complex.analyticOnNhd_iff_differentiableOn
    (Complex.isOpen_re_gt σ)).2 hE.differentiableOn
end OAI.CompactMellinBridge
