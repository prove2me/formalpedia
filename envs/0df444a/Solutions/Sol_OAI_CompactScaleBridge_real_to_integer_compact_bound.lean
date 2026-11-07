-- Prove2me | solution 1 for OAI.CompactScaleBridge.real_to_integer_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:10.186566+00:00
-- url     : https://prove2.me/submissions/916db766-730d-4daa-b99b-4a32ef1f5b26

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_CompactScaleBridge_outsideIdealsUpTo_card_le
import Theorems.Thm_OAI_ConcretePrimeRowBridge_baseChangeWeight_norm_le_one
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace FiniteSFactor
private theorem baseChangeWeight_norm_le_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (I : Ideal O) :
    ‖ShortDraftHeckeBridge.baseChangeWeight χ I‖ ≤ 1 := by
  have hμ : ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
    by_cases hsq : Squarefree I
    · simp [hsq.moebius_eq]
    · simp [UniqueFactorizationMonoid.moebius_of_not_squarefree hsq]
  have hχ : ‖χ (Ideal.absNorm I)‖ ≤ 1 := χ.norm_le_one _
  rw [ShortDraftHeckeBridge.baseChangeWeight, norm_mul]
  calc
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ * ‖χ (Ideal.absNorm I)‖ ≤
        1 * ‖χ (Ideal.absNorm I)‖ :=
      mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
    _ ≤ 1 := by simpa using hχ
end FiniteSFactor
open Filter
namespace CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge
end CompactScaleBridge
end
end OAI
end

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
open ConcretePrimeRowBridge ShortDraftHeckeBridge
namespace OAI.CompactScaleBridge
theorem _root_.solution
    {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal O)) (W : ℝ → ℂ)
    (LipC D : ℝ) (m : ℕ)
    (hL : 0 ≤ LipC) (hLip : ∀ x y : ℝ, ‖W x - W y‖ ≤ LipC * |x - y|)
    (hD : 1 ≤ D) (hmLower : D ≤ (m : ℝ))
    (hmUpper : (m : ℝ) ≤ D + 1) :
    ‖(∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ outsideIdealsUpTo S (2 * m),
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ ≤
      640 * LipC := by
  classical
  let F := outsideIdealsUpTo S (2 * m)
  have hDpos : 0 < D := by linarith
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le hDpos hmLower
  have hcardNat : F.card ≤ 64 * (2 * m + 1) :=
    outsideIdealsUpTo_card_le S (2 * m)
  have hcard : (F.card : ℝ) ≤ 320 * D := by
    have hcardReal : (F.card : ℝ) ≤ 64 * (2 * (m : ℝ) + 1) := by
      exact_mod_cast hcardNat
    nlinarith
  have hpoint (I : Ideal O) (hIF : I ∈ F) :
      ‖baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
        baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ ≤
      2 * LipC / D := by
    let n : ℝ := Ideal.absNorm I
    have hn0 : 0 ≤ n := by positivity
    have hn : n ≤ 2 * (m : ℝ) := by
      have hh : Ideal.absNorm I ≤ 2 * m :=
        (mem_outsideIdealsUpTo.mp hIF).2.1
      have hh' : (Ideal.absNorm I : ℝ) ≤ (2 * m : ℕ) := by
        exact_mod_cast hh
      simpa only [n, Nat.cast_mul, Nat.cast_ofNat] using hh'
    have hgap : 0 ≤ (m : ℝ) - D := sub_nonneg.mpr hmLower
    have hgap1 : (m : ℝ) - D ≤ 1 := by linarith
    have hnum : n * ((m : ℝ) - D) ≤ 2 * (m : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) hgap,
        mul_nonneg hn0 (sub_nonneg.mpr hgap1)]
    have hxy : n / (m : ℝ) ≤ n / D := by
      apply (div_le_div_iff₀ hmpos hDpos).2
      nlinarith [mul_nonneg hn0 hgap]
    have hdiff : n / D - n / (m : ℝ) ≤ 2 / D := by
      have haux : n * ((m : ℝ) - D) / (D * (m : ℝ)) ≤ 2 / D := by
        apply (div_le_div_iff₀ (mul_pos hDpos hmpos) hDpos).2
        nlinarith [mul_le_mul_of_nonneg_right hnum hDpos.le]
      have hfactor : n / D - n / (m : ℝ) =
          n * ((m : ℝ) - D) / (D * (m : ℝ)) := by
        field_simp
      rw [hfactor]
      exact haux
    have habs : |n / D - n / (m : ℝ)| ≤ 2 / D := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hxy)]
    have hW := hLip (n / D) (n / (m : ℝ))
    have hwNorm := baseChangeWeight_norm_le_one χ I
    calc
      ‖baseChangeWeight χ I * W (n / D) -
          baseChangeWeight χ I * W (n / (m : ℝ))‖ =
          ‖baseChangeWeight χ I‖ *
            ‖W (n / D) - W (n / (m : ℝ))‖ := by
              rw [← mul_sub, norm_mul]
      _ ≤ 1 * (LipC * |n / D - n / (m : ℝ)|) :=
        mul_le_mul hwNorm hW (norm_nonneg _) (by positivity)
      _ ≤ 1 * (LipC * (2 / D)) := by
        gcongr
      _ = 2 * LipC / D := by ring
  calc
    ‖(∑ I ∈ F, baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D)) -
      (∑ I ∈ F, baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ =
        ‖∑ I ∈ F,
          (baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
            baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ)))‖ := by
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ I ∈ F,
          ‖baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / D) -
            baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ) / (m : ℝ))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _I ∈ F, (2 * LipC / D) := by
      apply Finset.sum_le_sum
      exact hpoint
    _ = (F.card : ℝ) * (2 * LipC / D) := by simp [mul_comm]
    _ ≤ 640 * LipC := by
      have hcoef : 0 ≤ 2 * LipC / D := by positivity
      calc
        (F.card : ℝ) * (2 * LipC / D) ≤
            (320 * D) * (2 * LipC / D) :=
          mul_le_mul_of_nonneg_right hcard hcoef
        _ = 640 * LipC := by
          field_simp
          ring
end OAI.CompactScaleBridge
