-- Prove2me | solution 1 for OAI.SmoothMobiusCorrection.primeCharacterTerm_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:50:37.38363+00:00
-- url     : https://prove2.me/submissions/788cce0f-0f11-46d6-b884-517a113363d1

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Theorems.Thm_OAI_QRH_b83dbbd_SmoothMobiusCorrection_prime_norm_two_le
import Theorems.Thm_OAI_SmoothMobiusCorrection_norm_primeNormPower

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SmoothMobiusCorrection
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
open scoped BigOperators Classical
open ActualEisensteinCubic
open Filter
namespace OAI.SmoothMobiusCorrection
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q) (P : PrimeIdeal)
    (s : ℂ) (σ : ℝ) (hs : σ≤s.re) :
    ‖primeCharacterTerm χ P s‖≤(Ideal.absNorm P.val:ℝ)^(-σ) := by
  rw [primeCharacterTerm,norm_mul,norm_primeNormPower]
  have hn1 : (1:ℝ)≤Ideal.absNorm P.val := by exact_mod_cast (by have:=prime_norm_two_le P;omega)
  calc
    _ ≤ 1*(Ideal.absNorm P.val:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_right (χ.norm_le_one _) (by positivity)
    _ ≤ _ := by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hs)
end OAI.SmoothMobiusCorrection
