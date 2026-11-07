-- Prove2me | solution 1 for OAI.CompactScaleBridge.realCompactOutsideSum_bound_of_fixedTestPrimeMS
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:46:28.538384+00:00
-- url     : https://prove2.me/submissions/ce7d9154-185f-4fba-a70d-940abdb766d7

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Theorems.Thm_OAI_CompactScaleBridge_FixedTestPrimeMS_bound
import Theorems.Thm_OAI_CompactScaleBridge_real_to_integer_compact_bound
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
open OAI.CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O))
    (hSbad : ∀ P : Ideal O, P.IsMaximal → goodLambda ∈ P → P ∈ S)
    (W : ℝ → ℂ) (LipC ε : ℝ) (m₀ : ℕ)
    (hL : 0 ≤ LipC)
    (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hε : 0 ≤ ε) (hW : ∀ y : ℝ, ‖W y‖ ≤ 1)
    (hMS : ∀ m : ℕ, m₀ ≤ m → FixedTestPrimeMS χ S hSbad W m ε)
    (D : ℝ) (hD : max 1 (m₀ : ℝ) ≤ D) :
    ‖realCompactOutsideSum χ S W D‖ ≤
      (640 * LipC + 384 * (4 : ℝ) ^ ((23 / 24 : ℝ) + ε)) *
        D ^ ((23 / 24 : ℝ) + ε) := by
  let m := Nat.ceil D
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hD
  have hDpos : 0 < D := by linarith
  have hmLower : D ≤ (m : ℝ) := Nat.le_ceil D
  have hmUpper : (m : ℝ) ≤ D + 1 :=
    (Nat.ceil_lt_add_one (by linarith : 0 ≤ D)).le
  have hmPos : 0 < m := by
    have h : (0 : ℝ) < m := lt_of_lt_of_le hDpos hmLower
    exact_mod_cast h
  have hm₀ : m₀ ≤ m := by
    have h : (m₀ : ℝ) ≤ m :=
      ((le_max_right _ _).trans hD).trans hmLower
    exact_mod_cast h
  have hInt := FixedTestPrimeMS.bound χ S hSbad W m ε
    (hMS m hm₀) hmPos hε hW
  have hReal := real_to_integer_compact_bound χ S W LipC D m
    hL hLip hD1 hmLower hmUpper
  let α : ℝ := (23 / 24 : ℝ) + ε
  have hα : 0 ≤ α := by dsimp [α]; linarith
  have hsize : ((2 * m : ℕ) : ℝ) ≤ 4 * D := by
    push_cast
    nlinarith
  have hpower : ((2 * m : ℕ) : ℝ) ^ α ≤ (4 * D) ^ α :=
    Real.rpow_le_rpow (by positivity) hsize hα
  have hDpower : 1 ≤ D ^ α := Real.one_le_rpow hD1 hα
  have hLnonneg : 0 ≤ 640 * LipC := by positivity
  change ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
      baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)‖ ≤ _
  calc
    ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)‖ =
      ‖((∑ I ∈ outsideIdealsUpTo S (2 * m),
          baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
        (∑ I ∈ outsideIdealsUpTo S (2 * m),
          baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))) +
        (∑ I ∈ outsideIdealsUpTo S (2 * m),
          baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ := by
            rw [sub_add_cancel]
    _ ≤ 640 * LipC + 384 * ((2 * m : ℕ) : ℝ) ^ α := by
      calc
        _ ≤ ‖(∑ I ∈ outsideIdealsUpTo S (2 * m),
              baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
              (∑ I ∈ outsideIdealsUpTo S (2 * m),
                baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ +
            ‖∑ I ∈ outsideIdealsUpTo S (2 * m),
                baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ :=
              norm_add_le _ _
        _ ≤ 640 * LipC + 384 * ((2 * m : ℕ) : ℝ) ^ α :=
          add_le_add hReal hInt
    _ ≤ 640 * LipC + 384 * (4 * D) ^ α := by gcongr
    _ = 640 * LipC + 384 * ((4 : ℝ) ^ α * D ^ α) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hDpos.le]
    _ ≤ (640 * LipC + 384 * (4 : ℝ) ^ α) * D ^ α := by
      have hconst : 640 * LipC ≤ 640 * LipC * D ^ α :=
        by simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hDpower hLnonneg)
      nlinarith
end OAI.CompactScaleBridge
