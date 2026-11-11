-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedCubeFamily_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:56:02.302506+00:00
-- url     : https://prove2.me/submissions/771edc62-9880-4048-b908-eaeb342910ba

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopenedFibers
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCubeFamily_admissible
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCubeFamily_cube_norms
import Theorems.Thm_OAI_SecondPassArithmetic_cubeCoordinates_radical_bound
import Theorems.Thm_OAI_SecondPassArithmetic_cube_coordinates_parity_count
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_mono


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (_hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (Q : Finset (ι →₀ ℕ)) (B : ℝ),1 ≤ B →
      (∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) →
      ((reopenedCubeFamily Q).card : ℝ) ≤ C*B^(2+ε) := by
  obtain ⟨C,hC,hcount⟩ := cube_coordinates_parity_count ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Q B hB hQ
  have hBp := zero_lt_one.trans_le hB
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hactive (b : CubeCoordinates ι) (hbf : b ∈ reopenedCubeFamily Q) :
      ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖ ≤ B := by
    have hn : primeProductNorm p (cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) ≤ B^2 :=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hBp.le (hb b hbf).1 (hb b hbf).2)
    change ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2 ≤ B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  have h := hcount p hp hinj (reopenedCubeFamily Q) B B hB hBp.le
    (reopenedCubeFamily_admissible Q) (fun b hb' => (hb b hb').1)
    (fun b hb' => (hb b hb').2) hactive
  apply h.trans_eq
  calc
    C*B^(1+ε)*B = C*(B^(1+ε)*B^(1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = C*B^((1+ε)+1) := by rw [Real.rpow_add hBp (1+ε) (1 : ℝ)]
    _ = C*B^(2+ε) := by congr 2; ring
end OAI.SecondPassArithmetic
