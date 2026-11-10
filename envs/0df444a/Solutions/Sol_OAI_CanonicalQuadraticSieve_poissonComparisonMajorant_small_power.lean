-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.poissonComparisonMajorant_small_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:19:38.159015+00:00
-- url     : https://prove2.me/submissions/52aa7ffd-cd20-4f68-b28c-9a1ab072fa92

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PoissonConstants
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_SelectedExponents
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poissonComparisonMajorant_selected_power


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
open OAI.CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ (η : ℝ) (hη : 0<η), η≤1 ∧ 259*η≤ρ ∧
    ∃ (l A : ℕ), 4≤η*l ∧ 4≤η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0≤CD → 0≤CS → 0≤CT → 0≤CP →
      ∀ (B C1 : ℝ), 1≤B → 1≤C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0<Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
          1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1≤selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤
          Cfinal*(M*X)^ρ*poissonShape M X α := by
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : 259*η≤ρ := by
    have hh : η≤ρ/600 := min_le_right _ _
    linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith
  refine ⟨η,hη,hη1,hηρ,l,l,horder,horder,?_⟩
  intro sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  obtain ⟨Cfinal,hCf,hbound⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l l horder horder sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  refine ⟨Cfinal,hCf,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  apply (hbound C M X q G hC hBC hCC hM hX hq hqX hG hGN hK).trans
  have hP : 1≤M*X := by nlinarith
  have hshape : 0≤poissonShape M X α := by unfold poissonShape; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hηρ) hCf.le) hshape
end OAI.CanonicalQuadraticSieve
