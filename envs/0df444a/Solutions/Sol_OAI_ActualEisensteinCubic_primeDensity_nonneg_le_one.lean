-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.primeDensity_nonneg_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:14.699887+00:00
-- url     : https://prove2.me/submissions/027ba2d7-8ca9-4af4-a482-ae0caaf6d88c

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ActiveConductor

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
open OAI.ActualEisensteinCubic
open EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    0 ≤ (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ∧
      (∏ i ∈ S, (1 - (1 : ℝ) / Ideal.absNorm (P i))) ≤ 1 := by
  have hfactor (i : ι) : 0 ≤ 1 - (1 : ℝ) / Ideal.absNorm (P i) ∧
      1 - (1 : ℝ) / Ideal.absNorm (P i) ≤ 1 := by
    have hnorm : (1 : ℝ) ≤ Ideal.absNorm (P i) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne (P i)))
    constructor
    · exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hnorm)
    · have : 0 ≤ (1 : ℝ) / Ideal.absNorm (P i) := by positivity
      linarith
  exact ⟨Finset.prod_nonneg (fun i _ => (hfactor i).1),
    Finset.prod_le_one (fun i _ => (hfactor i).1) (fun i _ => (hfactor i).2)⟩
end OAI.ActualEisensteinCubic
