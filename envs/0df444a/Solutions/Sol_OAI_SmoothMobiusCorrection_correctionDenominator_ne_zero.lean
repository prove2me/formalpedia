-- Prove2me | solution 1 for OAI.SmoothMobiusCorrection.correctionDenominator_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T18:02:41.996646+00:00
-- url     : https://prove2.me/submissions/afe67676-7d0e-4010-8af4-9d4e96090ec2

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_MobiusEulerCorrection
import Theorems.Thm_OAI_SmoothMobiusCorrection_primeDensity_norm_le_one
import Theorems.Thm_OAI_SmoothMobiusCorrection_primeCharacterTerm_norm_lt_one
import Theorems.Thm_OAI_SmoothMobiusCorrection_one_sub_ne_zero

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
    (s : ℂ) (hs : 0<s.re) : 1-primeDensity P*primeCharacterTerm χ P s≠0 := by
  apply one_sub_ne_zero
  rw [norm_mul]
  calc
    _ ≤ 1*‖primeCharacterTerm χ P s‖ :=
      mul_le_mul_of_nonneg_right (primeDensity_norm_le_one P) (norm_nonneg _)
    _ < 1 := by rw [one_mul];exact primeCharacterTerm_norm_lt_one χ P s hs
end OAI.SmoothMobiusCorrection
