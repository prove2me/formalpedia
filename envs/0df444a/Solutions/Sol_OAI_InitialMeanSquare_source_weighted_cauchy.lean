-- Prove2me | solution 1 for OAI.InitialMeanSquare.source_weighted_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T09:47:17.156183+00:00
-- url     : https://prove2.me/submissions/edfca484-83b3-409a-acbc-5390475b871d

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_SourceTransfer
import Theorems.Thm_OAI_InitialMeanSquare_source_weighted_energy_pushforward
import Theorems.Thm_OAI_ConcretePrimeRowBridge_span_idealGenerator
import Theorems.Thm_OAI_DescentWeightedCauchy_weighted_cauchy


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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic IdealMobiusDivisorSum
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
namespace OAI.InitialMeanSquare
theorem _root_.solution (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (r : O) (s : Finset (SecondExpansionData ι)) (t : Finset (O×O))
      (w : SecondExpansionData ι→ℂ) (P Q : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,InSecondQuotientSector p r x) →
      (∀x∈s,sourceObservation p x∈t) → (∀y∈t,y.1≠0) →
      (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      ‖∑x∈s,w x*P (sourceObservation p x)*star (Q (sourceObservation p x))‖≤
        A*C*K^ε*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by
  obtain ⟨C,hC,hpool⟩ := source_weighted_energy_pushforward ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p _ hinj r s t w P Q A K hA hK hs hmap ht hnorm hw
  have hP := hpool p hinj r s t w P A K hA hK hs hmap ht hnorm hw
  have hQ := hpool p hinj r s t w Q A K hA hK hs hmap ht hnorm hw
  have hD : 0≤A*C*K^ε := by positivity
  apply (DescentWeightedCauchy.weighted_cauchy s w (fun x => P (sourceObservation p x))
    (fun x => Q (sourceObservation p x))).trans
  calc
    _ ≤ Real.sqrt (A*C*K^ε*∑y∈t,‖P y‖^2)*Real.sqrt (A*C*K^ε*∑y∈t,‖Q y‖^2) := by gcongr
    _ = _ := by
      rw [Real.sqrt_mul hD,Real.sqrt_mul hD]
      calc
        _ = (Real.sqrt (A*C*K^ε))^2*Real.sqrt (∑y∈t,‖P y‖^2)*Real.sqrt (∑y∈t,‖Q y‖^2) := by ring
        _ = _ := by rw [Real.sq_sqrt hD]
end OAI.InitialMeanSquare
