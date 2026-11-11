-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedSourceBlocks_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:08:10.670091+00:00
-- url     : https://prove2.me/submissions/ae13f13d-4caf-45c7-96dd-c64c1c1ab324

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopenedFibers
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCubeFamily_admissible
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCubeFamily_cube_norms
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceBlocks_admissible
import Theorems.Thm_OAI_SecondPassArithmetic_canonicalSourceBlocks_cube_norms


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
variable {ι : Type*} [DecidableEq ι]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (p : ι → ActualEisensteinCubic.O) (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (B : ℝ) (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ q ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q),GlobalCubeAdmissible q ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2 ≤ B := by
  intro q hq
  exact ⟨canonicalSourceBlocks_admissible pool _ (reopenedCubeFamily_admissible Q) q hq,
    canonicalSourceBlocks_cube_norms p pool _ B
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).1)
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).2) q hq⟩
end OAI.SecondPassArithmetic
