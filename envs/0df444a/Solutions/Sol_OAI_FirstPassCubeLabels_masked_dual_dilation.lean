-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.masked_dual_dilation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:39.732731+00:00
-- url     : https://prove2.me/submissions/56851b48-f28f-4552-81b8-ae68e3f19f14

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Theorems.Thm_OAI_FirstPassCubeLabels_radical_mask_absorbs
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_self_pair


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
open scoped BigOperators Classical
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
variable {ι κ : Type*} (P : ι → Ideal OAI.FirstPassCubeLabels.O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution (p : κ → O) (B : Finset κ) (v : κ → ℕ) (z : O) (c : ℂ) :
    rowCoprimeMask P S (cubeRadical p B) * c * star (finiteSquarefreeRow P hg S z) =
      (rowCoprimeMask P S (cubeRadical p B) * c *
        finiteSquarefreeRow P hg S (primeProduct p B v)) *
      star (finiteSquarefreeRow P hg S (z * primeProduct p B v)) := by
  rw [finiteSquarefreeRow_mul, star_mul]
  calc
    _ = (rowCoprimeMask P S (cubeRadical p B) *
        rowCoprimeMask P S (primeProduct p B v)) * c *
        star (finiteSquarefreeRow P hg S z) := by rw [radical_mask_absorbs P hg S]
    _ = _ := by rw [← finiteSquarefreeRow_self_pair P hg S (primeProduct p B v)]; ring
end OAI.FirstPassCubeLabels
