-- Prove2me | solution 1 for OAI.SecondPassArithmetic.full_uniform_globalArithmeticBin_twisted_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T05:15:18.636924+00:00
-- url     : https://prove2.me/submissions/4e46da35-46ee-4ede-b93e-41cb7f33e1a7

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ArithmeticBins
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_UniformTransfer
import Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_globalSecondRawSource_twisted_transfer
import Theorems.Thm_OAI_SecondPassArithmetic_globalArithmeticBinSource_squarefree
import Theorems.Thm_OAI_SecondPassArithmetic_globalArithmeticTargets_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_globalBinRadial_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalLogRep_pos
import Theorems.Thm_OAI_SecondPassArithmetic_globalPooledLabelScale_ge_one
import Theorems.Thm_OAI_SecondPassArithmetic_globalSecondOuterWeight_bin_bound
import Theorems.Thm_OAI_SecondPassArithmetic_outerWindow_global_bound


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
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open SecondPassFiber (newLabel newRow)
open SecondPassIntegration (tupleSourceSum densityChildEnergy)
open JointLogSeparation (outerWindow)
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (ε : ℝ) (hε : 0 < ε)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7 → ℝ → ℂ) (M : Fin 7 → ℝ)
    (hM : ∀ i,0 ≤ M i) (hV : ∀ i x,V i x ≠ 0 → |x| ≤ M i)
    (hVc : ∀ i,HasCompactSupport (V i)) (hVs : ∀ i,Continuous (V i)) (A J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2), ∀ (θ₁ θ₂ : ℝ), ∀ (s : Finset (GlobalSecondData ι)) (side : Bool)
      (q : Ideal O × Ideal O × Ideal O) (j : GlobalLogIndex)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex) (ell Y : ℝ),
      0 < ell → 0 < Y → q.1 ≠ ⊥ → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      ‖globalArithmeticBinSource p hp hcop hg s side q j F Ψ m ray (JointLogSeparation.frequencyTwist A₁ θ₁) (JointLogSeparation.frequencyTwist A₂ θ₂) W V ell Y‖ ≤
      C*(1+‖θ₁‖)^(J+2)*(1+‖θ₂‖)^(J+2)*globalPooledOuterBound ray ell Y j*
        (globalPooledLabelScale j*Ideal.absNorm q.1)^ε/(1+globalBinRadial ell Y j)^A *
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (V 5) (V 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J := by
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := full_uniform_globalSecondRawSource_twisted_transfer ε hε A₁ A₂ W V M hM hV A J
  obtain ⟨Cw,hCw,hwglobal⟩ := outerWindow_global_bound V hVc hVs
  refine ⟨Cₐ*Cₛ*Cw,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc
  have htrans := htrans p hp hcop hg hinj
  intro θ₁ θ₂ s side q j F Ψ m ray ell Y hell hY hq hΨ hs hk
  rw [globalArithmeticBinSource_squarefree p hp hcop hg s side q j hs]
  let t := globalSquarefreeBin p s side q j
  let T := globalArithmeticTargets p s side q j
  have ht (x : GlobalSecondData ι) (hx : x∈t) : x∈s ∧ globalSecondFixedTriple p x=q ∧ globalScaleIndex p side x=j :=
    Finset.mem_filter.mp (Finset.mem_filter.mp hx).1
  have hbound := globalArithmeticTargets_bounds p hp s side q j hk
  have hB : 0 ≤ globalPooledOuterBound ray ell Y j := by
    have h0 := (globalLogRep_pos j 0).le
    have h1 := (globalLogRep_pos j 1).le
    have h2 := (globalLogRep_pos j 2).le
    have h3 := (globalLogRep_pos j 3).le
    unfold globalPooledOuterBound
    positivity
  have hw : ∀ x∈t,‖globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x‖*
      ‖JointLogSeparation.outerWindow V (globalBinZ p ell side j x) (globalBinUd p j x)
        (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)‖ ≤ globalPooledOuterBound ray ell Y j*Cw := by
    intro x hx
    have hh := globalSecondOuterWeight_bin_bound p hp hcop hg hinj hc Ψ hΨ m ray ell Y hell hY.le side x (hk x (ht x hx).1)
    rw [(ht x hx).2.2] at hh
    exact mul_le_mul hh (hwglobal _ _ _ _ _) (norm_nonneg _) hB
  have hh := htrans (globalBinRadial ell Y j) (globalBinRadial_pos ell Y hell hY j) θ₁ θ₂ t T q
    (globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side) (globalPooledOuterBound ray ell Y j*Cw)
    (globalPooledLabelScale j) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) m
    (globalBinZ p ell side j) (globalBinUd p j) (globalBinUe p j) (globalBinUv p j) (globalBinKap p j)
    (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) hq (mul_nonneg hB hCw)
    (zero_le_one.trans (globalPooledLabelScale_ge_one j))
    (fun x hx => hs x (ht x hx).1) (fun x hx => (ht x hx).2.1)
    (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩)
    (fun a ha => (hbound a ha).1) (fun a ha => (hbound a ha).2.1) hw
  convert hh using 1 ; ring
end OAI.SecondPassArithmetic
