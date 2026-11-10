-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalChildBudget_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T07:56:53.106472+00:00
-- url     : https://prove2.me/submissions/c1a44a47-d4f4-4de2-9eb3-a21ff02f12c9

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_LogarithmicLoss
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PooledRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Theorems.Thm_OAI_SecondPassArithmetic_globalChildBudget_density

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
open OAI.SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side) =
    (∫ t : ℝ,firstLogDensity 0 t)*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp_rw [globalChildBudget_density]
  exact integral_mul_const _ _
end OAI.SecondPassArithmetic
