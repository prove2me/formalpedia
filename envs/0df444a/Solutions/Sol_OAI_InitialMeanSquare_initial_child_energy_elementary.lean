-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_child_energy_elementary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:10:46.021458+00:00
-- url     : https://prove2.me/submissions/254dd11c-1df1-48e7-9d62-9da7ed326c73

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Theorems.Thm_OAI_InitialMeanSquare_initialElementaryConstant_nonneg
import Theorems.Thm_OAI_SecondPassIntegration_childEnergy_elementary_normalized
import Theorems.Thm_OAI_SecondPassIntegration_childEnergy_subunit


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
theorem _root_.solution (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X lengthScale K A Vmax a b : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV : ∀ t,‖V t‖ ≤ Vmax) (hs : ∀ t,V t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (tn rn : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      initialElementaryConstant A Vmax*K*X^2*lengthScale := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · have hb := childEnergy_elementary_normalized p hp hcop hg hc hinj F Ψ hΨ m T V
      X lengthScale K A Vmax a b hX hL hK hA hVmax hV hs hT tn rn
    have hXL : 0 < X*lengthScale := mul_pos hX (zero_lt_one.trans_le hL)
    have hb' := (div_le_iff₀ hXL).mp hb
    rw [max_eq_right hscale] at hb'
    convert hb' using 1 <;> first | rfl | (unfold initialElementaryConstant; field_simp)

  · rw [childEnergy_subunit p hp hcop hg F Ψ m T V X A hX hs
      (lt_of_not_ge hscale) a b tn rn]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)
end OAI.InitialMeanSquare
