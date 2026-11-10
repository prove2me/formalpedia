-- Prove2me | solution 1 for OAI.InitialMeanSquare.mobiusRow_initial_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:18:28.000604+00:00
-- url     : https://prove2.me/submissions/46302323-5981-43e5-9783-5e55415d3333

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Theorems.Thm_OAI_InitialMeanSquare_mobiusRow_initial_normalization

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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
omit [DecidableEq ι]
namespace OAI.InitialMeanSquare
theorem _root_.solution (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ : O →* ℂ) (m : O) (z : O) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ‖mobiusRow p hg F Ψ m
      (normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))) z‖^2 =
      ‖mobiusRow p hg F Ψ m (fun T => W (primeProductNorm p T/Z)) z‖^2/Z := by
  rw [mobiusRow_initial_normalization p hg hp F Ψ m z Z hZ W a b ha hs hW,
    norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hZ), mul_pow, inv_pow, Real.sq_sqrt hZ.le]
  ring
end OAI.InitialMeanSquare
