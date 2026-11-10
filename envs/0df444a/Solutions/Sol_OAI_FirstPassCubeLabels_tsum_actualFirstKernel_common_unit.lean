-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.tsum_actualFirstKernel_common_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T15:31:47.231988+00:00
-- url     : https://prove2.me/submissions/12426986-361b-4950-b079-aa5997a8aeb6

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_BranchScaling
import Theorems.Thm_OAI_FirstPassCubeLabels_actualFirstKernel_common_unit

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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.FirstPassCubeLabels.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
namespace OAI.FirstPassCubeLabels
theorem _root_.solution (F B:Finset ι) (hFB:Disjoint F B)
    (v:ι→ℕ) (ε₁ ε₂:ι→Bool) (C₁ C₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ) (X₁ X₂ K:ℝ) (u:Oˣ) (c f d:O) :
    (∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ ((u:O)*c) f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ ((u:O)*c) f) W V₁ V₂ X₁ X₂ K d h) =
    blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)*
    ∑'h:O,actualFirstKernel p hp hcop hg F B v ε₁ ε₂
      (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
      (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d h := by
  let F₀ : O→ℂ := actualFirstKernel p hp hcop hg F B v ε₁ ε₂
    (originalLabelColumn p hg B ε₁ ε₂ true C₁ c f)
    (originalLabelColumn p hg B ε₁ ε₂ false C₂ c f) W V₁ V₂ X₁ X₂ K d
  let q := blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
    (fun i=>(conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) ((u:O)^2)
  calc
    _ = ∑'h:O,q*F₀ ((u:O)^2*h) := by
      apply tsum_congr
      intro h
      exact actualFirstKernel_common_unit p hp hcop hg F B hFB v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K u c f d h
    _ = q*∑'h:O,F₀ ((u:O)^2*h) := tsum_mul_left
    _ = q*∑'h:O,F₀ h := by
      exact congrArg (fun z:ℂ=>q*z) ((unitSquareRowEquiv u).tsum_eq F₀)
end OAI.FirstPassCubeLabels
