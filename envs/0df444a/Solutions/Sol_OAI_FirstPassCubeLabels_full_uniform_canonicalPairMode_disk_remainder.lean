-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.full_uniform_canonicalPairMode_disk_remainder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T00:05:54.273623+00:00
-- url     : https://prove2.me/submissions/b2fb83f4-b179-470f-8019-185e2187167d

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_HighRadialBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PaddedPassage
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceRemainders
import Theorems.Thm_OAI_FirstPassCubeLabels_full_uniform_canonicalPairMode_remainder
import Theorems.Thm_OAI_FirstPassCubeLabels_firstFrequencyDisk_uniform
import Theorems.Thm_OAI_SecondPassArithmetic_columnLog_norm_upper
import Theorems.Thm_OAI_SecondPassArithmetic_outside_firstFrequencyDisk


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
open scoped BigOperators Classical SchwartzMap
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      Disjoint N Q → Disjoint N B → Disjoint Q B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K P M₁ M₂ : ℝ),0<X₁ → 0<X₂ → 0<K → 0≤P →
      columnLog p X₁ N≤M₁ → columnLog p X₂ Q≤M₂ → ∀(d : O),d≠0 →
      let S := (N∪Q)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ Q)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ Q‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 scale)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N Q B v ε₁ ε₂ hNQ hNB hQB C₁ C₂ W V₁ V₂ X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP hN hQ d hd
  apply hb p hp hcop hg hc N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K _ hK
    (div_nonneg hP (Real.exp_pos _).le) d hd
  intro h hh
  exact firstFrequencyDisk_uniform p hp N Q B v ε₁ ε₂ hNQ hNB hQB d hd
    X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hN hQ h hh
end OAI.FirstPassCubeLabels
