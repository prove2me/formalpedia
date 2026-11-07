-- Prove2me | solution 1 for OAI.TwoPassProfiles.first_profile_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:55:47.037234+00:00
-- url     : https://prove2.me/submissions/a9b8863c-b2d6-4525-83c1-890efa57c60a

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_TwoPassProfiles_first_profile_logshape
import Theorems.Thm_OAI_TwoPassProfiles_first_logsum

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
open OAI.TwoPassProfiles
namespace OAI.TwoPassProfiles
theorem _root_.solution
    (K y d f E t c x₁ x₂ : ℝ)
    (hK : 0 < K) (hy : 0 < y) (hd : 0 < d)
    (hf : 0 < f) (hE : 0 < E) (ht : 0 < t)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    K * y / (d * f ^ 2 * E * t ^ 2 * c * x₁ * x₂) =
      Real.exp (∑ j : Fin 9,
        firstCoeff j * firstLogs K y d f E t c x₁ x₂ j) := by
  rw [first_logsum, ← first_profile_logshape K y d f E t c x₁ x₂
    hK hy hd hf hE ht hc hx₁ hx₂]
  exact (Real.exp_log (by positivity)).symm
end OAI.TwoPassProfiles
