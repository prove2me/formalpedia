-- Prove2me | solution 1 for OAI.SecondPassArithmetic.residualPairWeight_support_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:58:59.839769+00:00
-- url     : https://prove2.me/submissions/69a93d00-f490-46a2-8de2-4cf44a0bba9f

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SmoothSummands
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_LatticeEnvelopes
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_SupportNorms
import Theorems.Thm_OAI_SecondPassArithmetic_normalizedColumn_subset_norm_bound
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_mono
import Theorems.Thm_OAI_SecondPassArithmetic_residualPairWeight_test_ne_zero


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
open scoped BigOperators Classical SchwartzMap
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (Ψ : O →* ℂ) (m c d : O) (g : 𝓢(ℝ, ℂ)) (M X : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M) (G E S T : Finset ι) (hEG : E ⊆ G)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p X V)) (G∪U)) S T ≠ 0) :
    primeProductNorm p G ≤ X*Real.exp M ∧ primeProductNorm p E ≤ X*Real.exp M ∧
      primeProductNorm p S ≤ X*Real.exp M ∧ primeProductNorm p T ≤ X*Real.exp M := by
  obtain ⟨hS,hT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hG := normalizedColumn_subset_norm_bound p hp g M X hX hgM G S G Finset.subset_union_left hS
  exact ⟨hG, (primeProductNorm_mono p hp hEG).trans hG,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G S S Finset.subset_union_right hS,
    normalizedColumn_subset_norm_bound p hp g M X hX hgM G T T Finset.subset_union_right hT⟩
end OAI.SecondPassArithmetic
