-- Prove2me | solution 1 for OAI.QuadraticInitialBound.quadratic_matrix_norm_reverse_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:22:18.517374+00:00
-- url     : https://prove2.me/submissions/cd7c7085-98db-4250-832c-9b5a6d9a661f

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_FiniteSieveOperator_operator_conjTranspose_norm
import Theorems.Thm_OAI_FiniteSieveOperator_separated_phase_norm_le
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_CubicReflectionKernel_logSchwartz_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_halfEulerIterateCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperFourierRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRealRayCLM_apply
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_FiniteRayExpansion_norm_char_le_one
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_nonunit
import Theorems.Thm_OAI_FiniteRayExpansion_zeroExtendUnits_unit
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_QuadraticGaussRay_residueQuotientFour_mk
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticRow_star
import Theorems.Thm_OAI_QuadraticInitialBound_quadraticSymbol_reciprocity_characters
import Theorems.Thm_OAI_QuadraticInitialBound_sieveCutoff_apply
import Theorems.Thm_OAI_RayFourExpansion_crossCoeff_sum_norm_le
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.CubicReflectionKernel.logSchwartz_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.halfEulerIterateCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperFourierRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.paperRealRayCLM_apply
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_nonunit
attribute [local simp] OAI.FiniteRayExpansion.zeroExtendUnits_unit
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply
attribute [local simp] OAI.QuadraticGaussRay.residueQuotientFour_mk
attribute [local simp] OAI.QuadraticInitialBound.sieveCutoff_apply



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
open scoped BigOperators Classical
open OAI.QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT RayFourExpansion
namespace OAI.QuadraticInitialBound
theorem _root_.solution
    {ι m n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (rows : m → Finset ι) (cols : n → Finset ι) :
    ‖FiniteSieveOperator.operator (quadraticMatrix p hg rows cols)‖ ≤
      512 * ‖FiniteSieveOperator.operator (quadraticMatrix p hg cols rows)‖ := by
  let A := quadraticMatrix p hg rows cols
  let B := (quadraticMatrix p hg cols rows).conjTranspose
  let c : RayCharacter × RayCharacter → ℂ := fun k => crossCoeff k.1 k.2
  let l : RayCharacter × RayCharacter → m → ℂ := fun k i =>
    rayCharacter k.2 (∏ s ∈ rows i, p s)
  let r : RayCharacter × RayCharacter → n → ℂ := fun k j =>
    rayCharacter k.1 (∏ s ∈ cols j, p s)
  have hB (i : m) (j : n) : B i j = quadraticSymbol p hg (rows i) (cols j) := by
    change star (quadraticSymbol p hg (rows i) (cols j)) = _
    exact quadraticRow_star _ _ _ _
  have hl (k : RayCharacter × RayCharacter) (i : m) : ‖l k i‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one k.2 _
  have hr (k : RayCharacter × RayCharacter) (j : n) : ‖r k j‖ ≤ 1 :=
    FiniteRayExpansion.norm_char_le_one k.1 _
  have hA (i : m) (j : n) : A i j = ∑ k, c k * (l k i * B i j * r k j) := by
    rw [hB, Fintype.sum_prod_type]
    change quadraticSymbol p hg (cols j) (rows i) = _
    rw [quadraticSymbol_reciprocity_characters p hp hcop hg hc]
    apply Finset.sum_congr rfl
    intro χ _
    apply Finset.sum_congr rfl
    intro η _
    dsimp [c, l, r]
    ring
  have hmass : (∑ k, ‖c k‖) ≤ 512 := by
    simpa only [c, Fintype.sum_prod_type] using crossCoeff_sum_norm_le
  calc
    _ ≤ (∑ k, ‖c k‖) * ‖FiniteSieveOperator.operator B‖ :=
      FiniteSieveOperator.separated_phase_norm_le A B c l r hl hr hA
    _ ≤ 512 * ‖FiniteSieveOperator.operator B‖ :=
      mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    _ = _ := by
      change 512 * ‖FiniteSieveOperator.operator
        (quadraticMatrix p hg cols rows).conjTranspose‖ = _
      rw [FiniteSieveOperator.operator_conjTranspose_norm]
end OAI.QuadraticInitialBound
