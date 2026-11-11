-- Prove2me | solution 1 for OAI.CubicGammaExponential.inverse_cubic_Gamma_pair_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:47:11.640776+00:00
-- url     : https://prove2.me/submissions/6bf32ab7-b0dc-4cad-a496-1854005a61ff

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BesselMellinTransform
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_VerticalContourShift
import Theorems.Thm_OAI_CubicGammaExponential_inverse_Gamma_strip_exp_bound_complex

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
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open OAI.CubicGammaExponential
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding
namespace OAI.CubicGammaExponential
theorem _root_.solution (a b : ℝ) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖(Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹‖≤
        C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨C1,hC1,h1⟩:=inverse_Gamma_strip_exp_bound_complex (a+1/3) (b+1/3)
  obtain ⟨C2,hC2,h2⟩:=inverse_Gamma_strip_exp_bound_complex (a+2/3) (b+2/3)
  refine ⟨C1*C2,mul_pos hC1 hC2,?_⟩
  intro s hs
  have hb1:=h1 (s+1/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  have hb2:=h2 (s+2/3) (by norm_num;constructor <;> linarith [hs.1,hs.2])
  norm_num at hb1 hb2
  rw [mul_inv_rev,norm_mul,norm_inv,norm_inv]
  calc
    _ ≤ (C2*Real.exp (Real.pi*|s.im|))*(C1*Real.exp (Real.pi*|s.im|)) :=
      mul_le_mul hb2 hb1 (by positivity) (by positivity)
    _ = C1*C2*Real.exp (2*Real.pi*|s.im|) := by
      rw [show 2*Real.pi*|s.im|=Real.pi*|s.im|+Real.pi*|s.im| by ring,Real.exp_add]
      ring
end OAI.CubicGammaExponential
