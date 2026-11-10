-- Prove2me | solution 1 for OAI.InitialMeanSquare.initial_diagonal_fixed_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:37:07.104812+00:00
-- url     : https://prove2.me/submissions/2aa52e97-0504-42a9-bb3a-140e7ec5be6f

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_DiagonalDensity
import Theorems.Thm_OAI_InitialMeanSquare_conjugateProfile_support_bound
import Theorems.Thm_OAI_InitialMeanSquare_star_normalizedColumn
import Theorems.Thm_OAI_SecondPassArithmetic_full_uniform_normalized_second_mass
import Theorems.Thm_OAI_SecondPassArithmetic_truncatedSecondZero_norm_le


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
open FirstPassCubeLabels (normalizedColumn columnLog)
open EisensteinSchwartzPoisson (paperRadialFourier)
namespace OAI.InitialMeanSquare
theorem _root_.solution (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ m c d
        (fun S => star (normalizedColumn p (fun T => g (columnLog p Z T)) S)) W Y K‖≤C*Y := by
  obtain ⟨C₀,hC₀,h₀⟩ := full_uniform_normalized_second_mass (conjugateProfile g) M
    (conjugateProfile_support_bound g M hgM)
  refine ⟨‖paperRadialFourier W 0‖*C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d Z Y hZ hY K hK
  simp_rw [star_normalizedColumn]
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d _ W Y K hK).trans
  rw [abs_of_pos hY]
  have hh := h₀ p hp hg hinj F Ψ hΨ m c d Z hZ
  calc
    _ ≤ Y*‖paperRadialFourier W 0‖*C₀ := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (‖paperRadialFourier W 0‖*C₀+1)*Y := by nlinarith
end OAI.InitialMeanSquare
