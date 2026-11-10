-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.HasSieveExponent.annular_energy_from_scalar_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:14:00.944794+00:00
-- url     : https://prove2.me/submissions/26f544f1-b671-4265-aa82-900fdad3915e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting
import Theorems.Thm_OAI_CanonicalQuadraticSieve_gcdPool_admissible
import Theorems.Thm_OAI_CanonicalQuadraticSieve_annularHighEnergy_gcd_reduction
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_annular_small_gcd_complete
import Theorems.Thm_OAI_CanonicalQuadraticSieve_HasSieveExponent_high_kernel
import Theorems.Thm_OAI_CanonicalQuadraticSieve_gcdRaySupport_weighted_sum_bound
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poissonComparisonMajorant_energy_factor
import Theorems.Thm_OAI_DivisorBlockCauchy_divisorConstant_pos
import Theorems.Thm_OAI_IdealCoprimeSieveOperator_supportConstant_pos


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy
namespace OAI.CanonicalQuadraticSieve
namespace HasSieveExponent
theorem _root_.solution {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_gcd_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  classical
  let S := (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H)
  have hb (D : Ideal O) (hD : D∈S) (c : EisensteinEPrimaryPhase.Coord) :
      ‖annularRayGcdBlock M N K D c a‖ ≤
        (C/6)*∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D hadm.1 (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0≤∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 by positivity)
    change _ ≤ C*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hbound
    have hn : ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖=6*‖annularRayGcdBlock M N K D c a‖ := by
      rw [norm_mul]
      norm_num
    rw [hn] at hh
    change _≤_*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hh
    nlinarith
  have hs := gcdRaySupport_weighted_sum_bound ε hε S (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) a N (C/6) (by positivity)
    (fun J hJ => (mem_idealRange.mp J.property).2)
    (fun D c => ‖annularRayGcdBlock M N K D c a‖) hb
  have hNH : 1≤N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_gcd_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hsupp := (supportConstant_pos ε hε).le
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/6)*(divisorConstant ε hε*N^ε)*∑J,‖a J‖^2 +
      (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
        (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
      gcongr
    _ = _ := by ring
end HasSieveExponent
end OAI.CanonicalQuadraticSieve
