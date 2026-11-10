-- Prove2me | solution 1 for OAI.CompletedGauss.completedRowFiber_energy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:15:05.465554+00:00
-- url     : https://prove2.me/submissions/e6be186c-3bd8-4f10-9885-c9c2fdbf00a3

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Theorems.Thm_OAI_CompletedGauss_rowResidualPart_injective_on_fiber
import Theorems.Thm_OAI_CompletedGauss_completedRowFiber_residual_range

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
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace OAI.CompletedGauss
theorem _root_.solution (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (f : Ideal O→ℂ) :
    (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)≤
      ∑J : idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))),‖f J.val‖^2 := by
  let U := (completedRowFiber S Q A T).image (fun I => rowResidualPart I Q)
  have he : (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)=∑J∈U,‖f J‖^2 := by
    rw [Finset.sum_image (rowResidualPart_injective_on_fiber S Q A T (fun I hI => (hS I hI).1))]
  rw [he,Finset.sum_coe_sort (s := idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ)))) (f := fun J : Ideal O => ‖f J‖^2)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact completedRowFiber_residual_range S Q A T hbad K hS I hI
  · intro _ _ _
    exact sq_nonneg _
end OAI.CompletedGauss
