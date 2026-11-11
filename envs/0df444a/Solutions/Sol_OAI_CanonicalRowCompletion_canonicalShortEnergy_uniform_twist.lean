-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.canonicalShortEnergy_uniform_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:46:18.899467+00:00
-- url     : https://prove2.me/submissions/003b3203-3c57-4883-ab59-0d64b866f4c1

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ClosedRecursion
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_FredholmAlternative
import Theorems.Thm_OAI_CanonicalRowCompletion_rowFamilyEnergy_le_rectangle
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_CompletedUnitRows_short_completed_elements_uniform_twist
import Theorems.Thm_OAI_SecondPassArithmetic_mem_firstFrequencyDisk


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
open OAI.CanonicalRowCompletion
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.CanonicalRowCompletion
theorem _root_.solution
    (a b : ℝ) (ha : 0<a) (ε ρ q levelBound : ℝ)
    (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃d : ℕ,∀W : ℝ→ℂ,Function.support W⊆Set.Icc a b → ContDiff ℝ ∞ W →
    ∃C : ℝ,0≤C ∧ ∀(θ : ℝ) (rays : ℕ) (Z K X F : ℝ),1≤Z → 1≤K → 1≤F →
      F≤Z^((1:ℝ)/1000) → ∀G : Ideal ActualEisensteinCubic.O,G≠0 → (∀P∈fixedBadPrimes,P∣G) →
      (2*K)*(Ideal.absNorm G:ℝ)≤X*F*Z^(-((1:ℝ)/40)) →
    ∀(labels : Finset (Ideal ActualEisensteinCubic.O)),labels⊆idealRange F →
    ∀(Ψ : ActualEisensteinCubic.O→*ℂ),(∀x,‖Ψ x‖≤1) → ∀(mask : ActualEisensteinCubic.O) (lengthScale : ℂ),
      (∀u : ActualEisensteinCubic.Oˣ,∀f : idealRange F,∀H∈shortCubeRange (Z^((1:ℝ)/1000)),
        HasExactCompletedDyadicModels rays (((firstFrequencyDisk (2*K)).erase 0).image (fun z=>Ideal.span {z})) (2*K)
          (X/(Ideal.absNorm H:ℝ)^3) ρ q levelBound f.val (G*f.val)
          (CompletedHeight.normTwistedSource W θ) (CompletedUnitRows.unitRowFamily Ψ mask u f) lengthScale) →
      rowFamilyEnergy labels (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ)
        mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000))) K≤
      (C*(1+‖θ‖)^d)*(rays:ℝ)^2*‖lengthScale‖^2*((2*K)*(Ideal.absNorm G:ℝ)*F)^ε*(K*F)*Z^ε := by
  obtain ⟨d,hbound⟩:=CompletedUnitRows.short_completed_elements_uniform_twist a b ha ε ρ q levelBound hε hρ hq hlevel
  refine ⟨d,?_⟩
  intro W hs hW
  obtain ⟨C,hC,h⟩:=hbound W hs hW
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 rowMajorant*C,by positivity,?_⟩
  intro θ rays Z K X F hZ hK hF hFZ G hG hbad hmargin labels hlabels Ψ hΨ mask lengthScale hmodels
  have hK0 : 0<K:=zero_lt_one.trans_le hK
  have hF0 : 0<F:=zero_lt_one.trans_le hF
  have hT : ∀z∈(firstFrequencyDisk (2*K)).erase 0,
      z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤2*K := by
    intro z hz
    refine ⟨(Finset.mem_erase.mp hz).1,?_⟩
    rw [←eisEmbedding_norm_sq_eq_absNorm_span]
    exact (mem_firstFrequencyDisk (2*K) z).mp (Finset.mem_erase.mp hz).2
  have hshort:=h θ rays Z (2*K) X F hZ (by linarith) hF hFZ G hG hbad hmargin
    ((firstFrequencyDisk (2*K)).erase 0) hT Ψ hΨ mask lengthScale hmodels
  have hsum := (div_le_iff₀ hF0).mp hshort
  have hrect:=rowFamilyEnergy_le_rectangle labels F K hK0 hlabels
    (fun I z=>shortCompletedSum (rowTwist (normHeightTwist Ψ θ) mask (idealGenerator I) z) W X (Z^((1:ℝ)/1000)))
  exact hrect.trans ((mul_le_mul_of_nonneg_left hsum (apply_nonneg _ _)).trans_eq (by ring))
end OAI.CanonicalRowCompletion
