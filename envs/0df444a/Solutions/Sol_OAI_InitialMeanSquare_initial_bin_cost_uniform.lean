-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_bin_cost_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T23:08:56.820685+00:00
-- url     : https://prove2.me/submissions/a90c352e-c6c2-4ad7-9d6e-955352541a6b

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Theorems.Thm_OAI_InitialMeanSquare_initialSquarefreeBinCost_of_density_bound
import Theorems.Thm_OAI_InitialMeanSquare_initial_bin_row_scale_le
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
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
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels
namespace OAI.InitialMeanSquare
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M Kmax ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hKmax : 1 ≤ Kmax) (hε : 0 ≤ ε)
    (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) (J N : ℕ)
    (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      (H*Real.exp 4*Cchild*Cₛ*(Kmax*Real.exp 2)^ε)/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by
  have hb := initialSquarefreeBinCost_of_density_bound p hp hcop hg F R Ψ m ray K
    Z H M ε Cₛ Cchild hZ hH hCₛ j windows B J N hB hdec hdensity
  have hR := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hden : 1 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
    apply one_le_pow₀
    have hnon : 0 ≤ H*secondLogK j*(primeProductNorm p R)^2/Z^2 := by positivity
    linarith
  have hnum : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
      ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε := by positivity
  have hrow : (secondLogK j*Real.exp 2)^ε ≤ (Kmax*Real.exp 2)^ε :=
    Real.rpow_le_rpow (mul_pos hk (Real.exp_pos 2)).le
    (mul_le_mul_of_nonneg_right (initial_bin_row_scale_le (Z*Real.exp M) Kmax hKmax j hj)
      (Real.exp_pos 2).le) hε
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε :=
      hb.trans (div_le_self hnum hden)
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(Kmax*Real.exp 2)^ε :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by ring
end OAI.InitialMeanSquare
