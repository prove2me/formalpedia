-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalStateCondition_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:41:59.066724+00:00
-- url     : https://prove2.me/submissions/f3df78a1-7260-45f6-a9ff-397c29bacb35

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UniformPolynomialHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UnitRows
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_firstCore
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_secondMinus
import Theorems.Thm_OAI_CanonicalCoefficientClass_IsBaseRayTwist_secondPlus
import Theorems.Thm_OAI_SecondPassArithmetic_canonical_retained_unpadded_closure
import Theorems.Thm_OAI_SecondPassArithmetic_globalCanonicalLabels_coprime


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
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open CanonicalCoefficientClass (IsBaseRayTwist)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
include hp
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (base : ActualEisensteinCubic.O→*ℂ) (bad : Ideal ActualEisensteinCubic.O) (Z η : ℝ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (X F K : ℝ)
    (hstate : CanonicalStateCondition base bad Z η Ψ m labels X F K)
    (hpbad : ∀i,IsCoprime (Ideal.span {p i}) bad)
    (source : Finset (GlobalSecondData ι)) (side : Bool)
    (q : Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j : GlobalLogIndex)
    (hq : q∈globalBinTriples p source side j)
    (a : RayCharacter) (r : FirstCoreIndex) (ray : SecondRayIndex) (B : ℝ)
    (hZ : 1<Z) (hZbig : Real.exp 9000≤Z) (hη : 0≤η) (hηsmall : η≤(1:ℝ)/1000)
    (hB : 0<B) (hprogress : Z^((1:ℝ)/1000)≤(Real.exp 1*B)*F)
    (hk : ∀x∈source,x.source.frequency≠0)
    (hb₁ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Real.exp 1*B)
    (hb₂ : ∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Real.exp 1*B)
    (hretained : globalBinRadial (X/B^3)
      (globalPooledRowScale K (X/B^3) (Real.exp 1*B) F j) j≤Z^η) :
    let X':=globalPooledColumnScale (X/B^3) j
    let F':=globalPooledLabelScale j
    let K':=globalLogRep j 8*Real.exp 1
    let labels':=globalCanonicalLabels p source side q j
    let m':=fixedTripleMask m q
    fixedDepthRank Z K'+1≤fixedDepthRank Z K ∧
    CanonicalStateCondition base bad Z η (secondRayMinus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' ∧
    CanonicalStateCondition base bad Z η (secondRayPlus (firstCoreTwist side a Ψ r) ray)
      m' labels' X' F' K' := by
  obtain ⟨hXc,hFc,hKc,hrank,hKglobal,hmass,hinvariant,hm,hlabels⟩ :=
    canonical_retained_unpadded_closure p hp source side q j hq Z ((1:ℝ)/20) η X B F K m
      hZ hZbig hη hηsmall hstate.column_pos hB hstate.label_ge_one hstate.row_ge_one
      hstate.mask_ne_zero hprogress hstate.row_le_global hstate.mass_le hstate.invariant
      hk hb₁ hb₂ hretained
  have hbad := globalCanonicalLabels_coprime p bad hpbad source side q j
  have hbnd : ∀I∈globalCanonicalLabels p source side q j,
      I≠⊥ ∧ Squarefree I ∧ IsCoprime I bad ∧ (Ideal.absNorm I:ℝ)≤globalPooledLabelScale j := by
    intro I hI
    exact ⟨(hlabels I hI).1,(hlabels I hI).2.1,hbad I hI,(hlabels I hI).2.2⟩
  refine ⟨hrank,?_,?_⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondMinus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant,hbnd⟩
  · exact ⟨(hstate.coefficient.firstCore side a r).secondPlus ray,
      hm,hXc,hFc,hKc,hKglobal,hmass,hinvariant,hbnd⟩
end OAI.SecondPassArithmetic
