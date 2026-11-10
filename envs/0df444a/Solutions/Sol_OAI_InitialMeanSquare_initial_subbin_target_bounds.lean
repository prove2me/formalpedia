-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_subbin_target_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:04:43.942666+00:00
-- url     : https://prove2.me/submissions/4fcbe7c3-3824-496e-a598-b85ac716fa66

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Theorems.Thm_OAI_ActualEisensteinCubic_primeSubsetGenerator_ne_zero
import Theorems.Thm_OAI_InitialMeanSquare_initialLogIndex_eq_second
import Theorems.Thm_OAI_InitialMeanSquare_initial_log_target_bounds
import Theorems.Thm_OAI_InitialMeanSquare_sourceIdealTarget_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportedSector_mem


set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (OAI.InitialMeanSquare.O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hp
namespace OAI.InitialMeanSquare
theorem _root_.solution (F R : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (Z M : ℝ) (j : SecondLogIndex)
    (s : Finset (SecondExpansionData ι)) (hs : s ⊆ secondLogSector p ∅ F K R Z M j) :
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
  apply sourceIdealTarget_bounds
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have hx' := hs hx
  obtain ⟨hxsec,hj⟩ := Finset.mem_filter.mp hx'
  have hk := (secondSupportedSector_mem p F K R Z M x hxsec).2.2.2.1
  have hji : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have ht := initial_log_target_bounds p hp x hk
  rw [hji] at ht
  refine ⟨?_,ht.1,?_⟩
  · exact mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  · exact ht.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num))
      (normLogScale_pos _).le)
end OAI.InitialMeanSquare
