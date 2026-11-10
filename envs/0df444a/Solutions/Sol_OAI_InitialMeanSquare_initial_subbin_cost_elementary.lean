-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_subbin_cost_elementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:23:56.214355+00:00
-- url     : https://prove2.me/submissions/aa10aaa9-b09d-45b6-a8c4-0d59c8a84eeb

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Theorems.Thm_OAI_InitialMeanSquare_initial_subbin_density_elementary
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_InitialMeanSquare_initial_log_mass
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos


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
include hc hinj
namespace OAI.InitialMeanSquare
theorem _root_.solution (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
    ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  have hb := initial_subbin_density_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    A Vmax Cs hZ hH hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  have h := mul_le_mul_of_nonneg_left hb hpref
  apply h.trans_eq
  rw [initial_log_mass Z (primeProductNorm p R) hR.ne',mul_pow]
  have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
  rw [he]
  have hz := hZ.ne'
  have hr := hR.ne'
  field_simp
end OAI.InitialMeanSquare
