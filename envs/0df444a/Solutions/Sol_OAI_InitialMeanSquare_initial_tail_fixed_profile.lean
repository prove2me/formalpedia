-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_tail_fixed_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:45:23.645118+00:00
-- url     : https://prove2.me/submissions/db544a55-6107-43ca-a81f-3fe85f002af4

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Theorems.Thm_OAI_InitialMeanSquare_initial_tail_polynomial
import Theorems.Thm_OAI_InitialMeanSquare_initialTailHeight_pos
import Theorems.Thm_OAI_InitialMeanSquare_conjugateProfile_support_bound
import Theorems.Thm_OAI_InitialMeanSquare_star_normalizedColumn


set_option autoImplicit false
open OAI
noncomputable section
open OAI.InitialMeanSquare
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
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.InitialMeanSquare
theorem _root_.solution (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (fun S => star (normalizedColumn p (fun V => g (columnLog p Z V)) S)) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M (initialTailHeight Z Y M))‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_tail_polynomial (conjugateProfile g) W M
    (conjugateProfile_support_bound g M hgM) 2
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y hZ hY
  simp_rw [star_normalizedColumn]
  apply (h p hp hg hinj hc F Ψ hΨ m c d Z Y (initialTailHeight Z Y M) hZ hY
    (initialTailHeight_pos Z Y M hZ hY).le).trans
  have hth := initialTailHeight_pos Z Y M hZ hY
  apply (div_le_iff₀ (by positivity : 0<(1+initialTailHeight Z Y M)^2)).mpr
  have hh : (1+Z*Real.exp M)^4*(1+(1+Z*Real.exp M)^3/Y)^2≤(1+initialTailHeight Z Y M)^2 := by
    have hp := initialTailHeight_pos Z Y M hZ hY
    calc
      _ = (initialTailHeight Z Y M)^2 := by unfold initialTailHeight; ring
      _ ≤ _ := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hh (show 0≤C*Y by positivity)
  nlinarith
end OAI.InitialMeanSquare
