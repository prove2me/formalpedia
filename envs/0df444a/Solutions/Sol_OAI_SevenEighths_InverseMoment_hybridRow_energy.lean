-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.hybridRow_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:24:31.379453+00:00
-- url     : https://prove2.me/submissions/e03a8bfb-b4af-4b8e-bac0-9f32bcc15bd9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B008
import Theorems.Thm_OAI_SevenEighths_CubicSieve_sieveNorm_sharp
import Theorems.Thm_OAI_SevenEighths_InverseMoment_hybrid_original_quotient_block

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RamifiedTracePhase
namespace OAI

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

namespace ActualEisensteinCubic

theorem finiteSquarefreeRow_sixth_power
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    finiteSquarefreeRow P hgood S (a ^ 6) =
      if ∃ i ∈ S, a ∈ P i then 0 else 1 := by
  classical
  simp only [finiteSquarefreeRow]
  by_cases hex : ∃ i ∈ S, a ∈ P i
  · obtain ⟨i, hi, hai⟩ := hex
    rw [if_pos ⟨i, hi, hai⟩]
    apply Finset.prod_eq_zero hi
    rw [canonicalSextic_sixth_power_mask]
    simp [hai]
  · rw [if_neg hex]
    apply Finset.prod_eq_one
    intro i hi
    rw [canonicalSextic_sixth_power_mask]
    simp [show a ∉ P i by intro hai; exact hex ⟨i, hi, hai⟩]

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CoefficientCancellation
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_ideal_moebius_le_one (I : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius I : ℂ)‖ ≤ 1 := by
  unfold UniqueFactorizationMonoid.moebius
  split_ifs <;> simp

end QuadraticInitialBound

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CubeLabels
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section
open scoped BigOperators Classical

open scoped BigOperators Classical
open UniqueFactorizationMonoid
namespace QuadraticSquarefreeKernel

open ActualEisensteinCubic QuadraticInitialBound CompletedGauss

theorem quadraticRow_square {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset ι) (a : O) :
    quadraticRow P hg S (a ^ 2) = rowCoprimeMask P S a := by
  have heq : quadraticRow P hg S (a ^ 2) = finiteSquarefreeRow P hg S (a ^ 6) := by
    simp only [quadraticRow, finiteSquarefreeRow, map_pow, ← Finset.prod_pow, ← pow_mul]
  rw [heq, finiteSquarefreeRow_sixth_power]
  rfl

end QuadraticSquarefreeKernel
end

namespace QuadraticMainBoundary
open scoped BigOperators Classical
open UniqueFactorizationMonoid
open QuadraticSquarefreeKernel

theorem norm_pos {I : Ideal O} (hI : I ≠ 0) : 0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_one_le {I : Ideal O} (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

theorem norm_le_of_dvd {I J : Ideal O} (hJ : J ≠ 0) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ Ideal.absNorm J := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_iff_ne_zero.mpr (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

end QuadraticMainBoundary

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

theorem idealSupport_singleton_univ (D : Ideal O) :
    idealSupport {D} D = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro P
  apply (mem_idealSupport_iff {D} D P).mpr
  obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
  have hID : I = D := Finset.mem_singleton.mp hI
  simpa only [hID] using hP

theorem singleton_rowCoprimeMask_eq_idealZeroMask (D : Ideal O) (z : O) :
    rowCoprimeMask (fun P : primePool {D} => P.val) Finset.univ z = idealZeroMask D z := by
  have he : (∃ P ∈ (Finset.univ : Finset (primePool {D})), z ∈ P.val) ↔
      ∃ P ∈ UniqueFactorizationMonoid.normalizedFactors D, z ∈ P := by
    constructor
    · rintro ⟨P, _, hz⟩
      obtain ⟨I, hI, hP⟩ := mem_primePool_iff.mp P.property
      have hID : I = D := Finset.mem_singleton.mp hI
      exact ⟨P.val, hID ▸ hP, hz⟩
    · rintro ⟨P, hP, hz⟩
      have hp : P ∈ primePool {D} := mem_primePool_iff.mpr ⟨D, Finset.mem_singleton_self D, hP⟩
      exact ⟨⟨P, hp⟩, Finset.mem_univ _, hz⟩
  simp only [rowCoprimeMask, idealZeroMask, he]

theorem canonical_quadraticRow_squared (D : Ideal O) (hD : Admissible D) (z : O) :
    quadraticRow D z * quadraticRow D z = idealZeroMask D z := by
  let F : Finset (Ideal O) := {D}
  have hF : ∀ I ∈ F, Admissible I := by
    intro I hI
    have hID := Finset.mem_singleton.mp hI
    simpa only [hID] using hD
  rw [quadraticRow_eq_pool F hF D (Finset.mem_singleton_self D)]
  rw [← QuadraticSquarefreeKernel.quadraticRow_mul _ _ _ z z, ← pow_two,
    QuadraticSquarefreeKernel.quadraticRow_square, idealSupport_singleton_univ]
  exact singleton_rowCoprimeMask_eq_idealZeroMask D z

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.SquareParts
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge QuadraticSquarefreeKernel

theorem canonical_quadraticRow_square_argument (D : Ideal O) (hD : Admissible D) (a : O) :
    quadraticRow D (a ^ 2) = idealZeroMask D a := by
  rw [pow_two, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_squared D hD]

theorem canonical_quadraticRow_primary_squarefree (D : Ideal O) (hD : Admissible D)
    (A B : Ideal O) :
    quadraticRow D (primaryGenerator (A ^ 2 * B)) =
      idealZeroMask D (primaryGenerator A) * quadraticRow D (primaryGenerator B) := by
  rw [primaryGenerator_mul]
  have hpow : primaryGenerator (A ^ 2) = primaryGenerator A ^ 2 := map_pow primaryGeneratorHom A 2
  rw [hpow, canonical_quadraticRow_argument_mul D hD, canonical_quadraticRow_square_argument D hD]

end

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.RamifiedNormWeights
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss

theorem idealZeroMask_span_eq (D : Ideal O) (x y : O) (hxy : Ideal.span {x} = Ideal.span {y}) :
    idealZeroMask D x = idealZeroMask D y := by
  have hm (P : Ideal O) : x ∈ P ↔ y ∈ P := by
    constructor
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
    · intro h
      exact (Ideal.span_singleton_le_iff_mem P).mp (hxy.symm ▸ (Ideal.span_singleton_le_iff_mem P).mpr h)
  unfold idealZeroMask
  simp_rw [hm]

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

theorem divisorDyadicBin_bounds (S : Finset (Ideal O)) (N : ℝ)
    (hS : ∀ D ∈ S, 1 ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ N)
    (j : Fin (columnDyadicLength N+1)) (D : Ideal O) (hD : D ∈ divisorDyadicBin S N j) :
    divisorDyadicScale j.val ≤ (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ 2 * divisorDyadicScale j.val := by
  obtain ⟨hDS,hj⟩ := Finset.mem_filter.mp hD
  have hd := hS D hDS
  have hb := divisorDyadicLabel_bounds N D hd.1 hd.2
  rw [hj] at hb
  refine ⟨max_le hd.1 hb.1.le, ?_⟩
  have hm : (2 : ℝ)^j.val/2 ≤ divisorDyadicScale j.val := le_max_right _ _
  linarith [hb.2]

theorem sum_divisorDyadicBins {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (N : ℝ) (f : Ideal O → A) :
    (∑ D ∈ S, f D) = ∑ j : Fin (columnDyadicLength N+1), ∑ D ∈ divisorDyadicBin S N j, f D := by
  simp only [divisorDyadicBin,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  simp

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem idealZeroMask_generator_eq_one (I G : Ideal O) (hcop : IsCoprime I G) :
    idealZeroMask I (idealGenerator G) = 1 := by
  apply if_neg
  rintro ⟨P,hP,hgen⟩
  have hPG : P ∣ G := by
    apply Ideal.dvd_iff_le.mpr
    rw [← span_idealGenerator G]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgen)
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).not_isUnit
    (hcop.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) hPG)

end

open ActualEisensteinCubic

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.CommonMasks
namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

theorem idealZeroMask_generator_eq_indicator (D B : Ideal O) (hD : D≠0) :
    idealZeroMask D (idealGenerator B) = if IsCoprime B D then 1 else 0 := by
  classical
  by_cases hc : IsCoprime B D
  · rw [if_pos hc,idealZeroMask_generator_eq_one D B hc.symm]
  · rw [if_neg hc]
    apply if_pos
    by_contra hn
    apply hc
    apply IsCoprime.symm
    apply ideals_coprime_of_relprime
    apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hD).mpr
    intro P hPD hPB hp
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors D :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hD).mpr ⟨hp,hPD⟩
    have hgen : idealGenerator B∈P := by
      apply (Ideal.span_singleton_le_iff_mem P).mp
      rw [span_idealGenerator]
      exact Ideal.dvd_iff_le.mp hPB
    exact hn ⟨P,hfac,hgen⟩

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
namespace OAI

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
open ActualEisensteinCubic ShortDraftLatticeCount
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

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.IdealMasks
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

theorem ideal_coprime_mobius (K P : Ideal ActualEisensteinCubic.O) (hK : K ≠ 0) :
    (if IsCoprime K P then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors K, if R ∣ P then (moebius R : ℂ) else 0 := by
  let G := K ⊔ P
  have hG : G ≠ 0 := by
    intro hz
    apply hK
    exact le_antisymm (show K ≤ 0 from hz ▸ (le_sup_left : K ≤ G)) bot_le
  have hdiv : (idealDivisors K).filter (fun R => R ∣ P) = idealDivisors G := by
    ext R
    simp only [Finset.mem_filter, mem_idealDivisors hK, mem_idealDivisors hG,
      Ideal.dvd_iff_le, G, sup_le_iff]
  rw [← Finset.sum_filter, hdiv, sum_moebius_divisors G hG]
  simp only [Ideal.isCoprime_iff_sup_eq, G]

theorem idealZeroMask_primary_indicator
    (D B : Ideal ActualEisensteinCubic.O) (hD : D ≠ 0)
    (hB : CompletedGauss.primaryGenerator B ≠ 0) :
    CanonicalQuadraticSieve.idealZeroMask D (CompletedGauss.primaryGenerator B) =
      if IsCoprime B D then 1 else 0 := by
  have he : Ideal.span {CompletedGauss.primaryGenerator B} =
      Ideal.span {ConcretePrimeRowBridge.idealGenerator B} := by
    rw [(CompletedGauss.primaryGenerator_spec B hB).1,
      ConcretePrimeRowBridge.span_idealGenerator]
  rw [CanonicalQuadraticSieve.idealZeroMask_span_eq D _ _ he,
    CanonicalQuadraticSieve.idealZeroMask_generator_eq_indicator D B hD]

theorem hybrid_quadratic_square_mask
    (k n b c m h t : Ideal ActualEisensteinCubic.O)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) =
      (if IsCoprime k (c * t) then 1 else 0) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) := by
  have he : n * b = (c * t) ^ 2 * (m * h) := by rw [hn, hb]; ring
  rw [he, CanonicalQuadraticSieve.canonical_quadraticRow_primary_squarefree k hk,
    idealZeroMask_primary_indicator k (c * t) hk.1 hct]
  rw [isCoprime_comm]

theorem hybrid_double_mask_mobius
    (k P c : Ideal ActualEisensteinCubic.O) (hk : k ≠ 0) :
    (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ R ∈ idealDivisors k, ∑ r ∈ idealDivisors k,
        if R ∣ P ∧ r ∣ c then (moebius R : ℂ) * (moebius r : ℂ) else 0 := by
  have hsplit : (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      (if IsCoprime k P then 1 else 0) * (if IsCoprime k c then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hP : IsCoprime k P <;> by_cases hc : IsCoprime k c <;> simp [hP, hc]
  rw [hsplit, ideal_coprime_mobius k P hk, ideal_coprime_mobius k c hk,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro R hR
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hP : R ∣ P <;> by_cases hc : r ∣ c <;> simp [hP, hc]

theorem hybrid_column_decomposition
    (n b : Ideal ActualEisensteinCubic.O) (hn : Squarefree n) (hb : b ≠ 0) :
    ∃ c m h t : Ideal ActualEisensteinCubic.O,
      n = c * m ∧ b = (c * h) * t ^ 2 ∧
      Squarefree c ∧ Squarefree m ∧ Squarefree h ∧
      IsRelPrime c m ∧ IsRelPrime c h ∧ IsCoprime m h ∧ t ≠ 0 := by
  let g := QuadraticSquarefreeKernel.squarefreePart b
  let t := QuadraticSquarefreeKernel.squarePart b
  let c := gcd n g
  let m := CanonicalQuadraticSieve.idealQuotient c n
  let h := CanonicalQuadraticSieve.idealQuotient c g
  have hg : Squarefree g := QuadraticSquarefreeKernel.squarefree_squarefreePart b
  have hcn : c ∣ n := gcd_dvd_left n g
  have hcg : c ∣ g := gcd_dvd_right n g
  have hc : c ≠ 0 := ne_zero_of_dvd_ne_zero hn.ne_zero hcn
  have hnm : n = c * m := (CanonicalQuadraticSieve.idealQuotient_mul hcn).symm
  have hgh : g = c * h := (CanonicalQuadraticSieve.idealQuotient_mul hcg).symm
  have hbgt : b = g * t ^ 2 := by
    rw [mul_comm]
    exact (QuadraticSquarefreeKernel.squarePart_sq_mul_squarefreePart b).symm
  obtain ⟨hcm, hcs, hms⟩ := squarefree_mul_iff.mp (hnm ▸ hn)
  obtain ⟨hch, _, hhs⟩ := squarefree_mul_iff.mp (hgh ▸ hg)
  have hmh : IsCoprime m h :=
    (CanonicalQuadraticSieve.gcd_eq_iff_quotient_coprime c n g hc hcn hcg).mp rfl
  exact ⟨c, m, h, t, hnm, by rw [hbgt, hgh], hcs, hms, hhs, hcm, hch, hmh,
    QuadraticSquarefreeKernel.squarePart_ne_zero hb⟩

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Gcd
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CanonicalQuadraticSieve (idealQuotient totalQuotient gcdPool)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubic_admissible_of_dvd {I D : Ideal O} (hI : Admissible I) (hD : D ∣ I) :
    Admissible D := by
  refine ⟨hI.1.squarefree_of_dvd hD, ?_⟩
  obtain ⟨J, he⟩ := hD
  have hp := hI.2
  rw [he, primaryGenerator_mul] at hp
  exact (mul_ne_zero_iff.mp hp).1

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Decomposition
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem HybridColumnData.residual_product_squarefree (d : HybridColumnData) :
    Squarefree (d.residualN * d.residualB) := by
  have hm := (squarefree_mul_iff.mp d.n_squarefree).2.2
  have hh := (squarefree_mul_iff.mp d.g_squarefree).2.2
  exact squarefree_mul_iff.mpr ⟨d.residual_coprime.isRelPrime, hm, hh⟩

theorem HybridColumnData.primary_factors (d : HybridColumnData)
    (hn : CompletedGauss.primaryGenerator (d.common * d.residualN) ≠ 0)
    (hb : CompletedGauss.primaryGenerator ((d.common * d.residualB) * d.square ^ 2) ≠ 0) :
    CompletedGauss.primaryGenerator d.common ≠ 0 ∧
    CompletedGauss.primaryGenerator d.residualN ≠ 0 ∧
    CompletedGauss.primaryGenerator d.residualB ≠ 0 ∧
    CompletedGauss.primaryGenerator d.square ≠ 0 ∧
    CompletedGauss.primaryGenerator (d.common * d.square) ≠ 0 := by
  rw [CompletedGauss.primaryGenerator_mul] at hn
  have hpow : CompletedGauss.primaryGenerator (d.square ^ 2) =
      CompletedGauss.primaryGenerator d.square ^ 2 :=
    map_pow CompletedGauss.primaryGeneratorHom d.square 2
  rw [CompletedGauss.primaryGenerator_mul, CompletedGauss.primaryGenerator_mul, hpow] at hb
  have hc := (mul_ne_zero_iff.mp hn).1
  have hm := (mul_ne_zero_iff.mp hn).2
  have hch := (mul_ne_zero_iff.mp hb).1
  have hh := (mul_ne_zero_iff.mp hch).2
  have ht : CompletedGauss.primaryGenerator d.square ≠ 0 := by
    intro hz
    apply (mul_ne_zero_iff.mp hb).2
    simp [hz]
  refine ⟨hc, hm, hh, ht, ?_⟩
  rw [CompletedGauss.primaryGenerator_mul]
  exact mul_ne_zero hc ht

theorem HybridColumnData.residual_norm_bounds (d : HybridColumnData)
    (N B C T : ℝ) (hN : 0 ≤ N) (_hB : 0 ≤ B) (hC : 0 < C) (hT : 0 < T)
    (hn : (Ideal.absNorm (d.common * d.residualN) : ℝ) ≤ N)
    (hb : (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B)
    (hc : C ≤ (Ideal.absNorm d.common : ℝ))
    (ht : T ≤ (Ideal.absNorm d.square : ℝ)) :
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  have hn' := hn
  have hb' := hb
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hn' hb'
  have hm : (Ideal.absNorm d.residualN : ℝ) ≤ N / C := by
    apply (le_div_iff₀ hC).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualN : ℝ) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hc
          (Nat.cast_nonneg (Ideal.absNorm d.residualN))
      _ ≤ N := hn'
  have hh : (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) := by
    apply (le_div_iff₀ (mul_pos hC (sq_pos_of_pos hT))).mpr
    calc
      _ ≤ (Ideal.absNorm d.common : ℝ) * (Ideal.absNorm d.residualB : ℝ) *
          (Ideal.absNorm d.square : ℝ) ^ 2 := by
        calc
          _ = C * (Ideal.absNorm d.residualB : ℝ) * T ^ 2 := by ring
          _ ≤ _ := by gcongr
      _ ≤ B := hb'
  refine ⟨hm, hh, ?_⟩
  calc
    _ = (Ideal.absNorm d.residualN : ℝ) * (Ideal.absNorm d.residualB : ℝ) := by
      rw [map_mul, Nat.cast_mul]
    _ ≤ (N / C) * (B / (C * T ^ 2)) :=
      mul_le_mul hm hh (Nat.cast_nonneg _) (div_nonneg hN hC.le)
    _ = N * B / (C ^ 2 * T ^ 2) := by ring

theorem HybridColumnData.toOriginal_bijective : Function.Bijective HybridColumnData.toOriginal := by
  constructor
  · intro d e he
    exact reconstruct_injective (congrArg Subtype.val he)
  · intro p
    obtain ⟨c, m, h, t, hn, hb, hcs, hms, hhs, hcm, hch, hmh, ht⟩ :=
      hybrid_column_decomposition p.val.1 p.val.2 p.property.1 p.property.2
    refine ⟨⟨c, m, h, t, ?_, ?_, hmh, ht⟩, ?_⟩
    · exact hn ▸ p.property.1
    · exact squarefree_mul_iff.mpr ⟨hch, hcs, hhs⟩
    · apply Subtype.ext
      exact Prod.ext hn.symm hb.symm

theorem hybrid_finite_column_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0)
    (f : Ideal Eis × Ideal Eis → A) :
    (∑ p ∈ S, f p) = ∑ d ∈ hybridColumnSupport S, f d.reconstruct := by
  symm
  apply Finset.sum_preimage
  intro p hp hn
  obtain ⟨d, hd⟩ := HybridColumnData.toOriginal_bijective.surjective ⟨p, hS p hp⟩
  exact (hn ⟨d, congrArg Subtype.val hd⟩).elim

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Fibers
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

theorem finite_expansion_energy {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
  have hlocal (k : κ) (hk : k ∈ rows) :
      ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        C * ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
    have hb : ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        ((active k).card : ℝ) * ∑ i ∈ active k, ‖w k i * F k i‖ ^ 2 := by
      calc
        _ ≤ (∑ i ∈ active k, ‖w k i * F k i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_mul_sq_le_sq_mul_sq (active k) (fun _ => (1 : ℝ))
              (fun i => ‖w k i * F k i‖)
    have hsum : (∑ i ∈ active k, ‖w k i * F k i‖ ^ 2) ≤
        ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw k hk i hi)
    exact hb.trans (mul_le_mul (hcard k hk) hsum
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (le_trans (Nat.cast_nonneg _) (hcard k hk)))
  calc
    _ ≤ ∑ k ∈ rows, C * ∑ i ∈ active k, ‖F k i‖ ^ 2 :=
      Finset.sum_le_sum hlocal
    _ = C * ∑ k ∈ rows, ∑ i ∈ active k, ‖F k i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ k ∈ rows, ∑ i ∈ terms, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hsub k hk hi, hi⟩, And.right⟩
    _ = _ := by rw [Finset.sum_comm]

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Hybrid
namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid IdealMobiusDivisorSum

local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_mul_left (R P n : Ideal Eis) :
    inverseCubicKernel (R * P) n = inverseCubicKernel R n * inverseCubicKernel P n := by
  simp only [inverseCubicKernel, CubicJacobiGlobal.idealSymbol_mul, map_mul, star_mul]
  ring

theorem inverseCubicKernel_mul_right (P n m : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0) :
    inverseCubicKernel P (n * m) = inverseCubicKernel P n * inverseCubicKernel P m := by
  change star (CubicSieve.idealNumeratorHom P hP (n * m)) =
    star (CubicSieve.idealNumeratorHom P hP n) * star (CubicSieve.idealNumeratorHom P hP m)
  rw [map_mul, star_mul]
  ring

theorem inverseCubicKernel_quotients (R P' r c' m : Ideal Eis)
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    inverseCubicKernel (R * P') ((r * c') * m) =
      inverseCubicKernel R ((r * c') * m) * inverseCubicKernel P' r *
        inverseCubicKernel P' (c' * m) := by
  rw [inverseCubicKernel_mul_left, mul_assoc r c' m,
    inverseCubicKernel_mul_right P' r (c' * m) hP']
  ring

theorem inverseCubicKernel_eq_zero_of_not_coprime (P n : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hn : CompletedGauss.primaryGenerator n ≠ 0) (hcop : ¬ IsCoprime P n) :
    inverseCubicKernel P n = 0 := by
  have hc := CubicSieve.idealSymbol_cube_mask P (CompletedGauss.primaryGenerator n) hP
  rw [(CompletedGauss.primaryGenerator_spec n hn).1, if_neg hcop] at hc
  have hz := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hc
  simp only [inverseCubicKernel, hz, star_zero]

theorem hybrid_cubic_column_mask
    (P n b c m h t : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) =
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [inverseCubicKernel_eq_zero_of_not_coprime P n hP hngen hPn]
    simp

theorem hybrid_original_kernel_decomposition
    (k P n b c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) *
      inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) *
      (if IsCoprime k P then 1 else 0) =
    (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) *
      CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  have hm : ((if IsCoprime k P then (1 : ℂ) else 0) *
      (if IsCoprime k (c * t) then 1 else 0)) =
      (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hkp : IsCoprime k P <;> by_cases hkc : IsCoprime k c <;>
      by_cases hkt : IsCoprime k t <;> simp [hkp, hkc, hkt]
  calc
    _ = ((if IsCoprime k P then 1 else 0) * (if IsCoprime k (c * t) then 1 else 0)) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
        (inverseCubicKernel P n * (if IsCoprime P b then 1 else 0)) := by
      rw [hybrid_quadratic_square_mask k n b c m h t hk hn hb hct]
      ring
    _ = _ := by rw [hm, hybrid_cubic_column_mask P n b c m h t hP hngen hn hb]; ring

theorem hybrid_kernel_quotients (R r k' P' c' m h : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel (R * P') ((r * c') * m) =
    (CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel R ((r * c') * m)) *
      inverseCubicKernel P' r *
      CanonicalQuadraticSieve.quadraticRow k'
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P' (c' * m) := by
  rw [CanonicalQuadraticSieve.quadraticRow_mul (R * r) k' hk,
    inverseCubicKernel_quotients R P' r c' m hP']
  ring

theorem normalized_ideal_product_weight (R P : Ideal Eis) (z : ℂ) :
    z / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        (z / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hybrid_extracted_block_identity
    (R r k' P' c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    a (R * P') / (Real.sqrt (Ideal.absNorm (R * P') : ℝ) : ℂ) *
      beta (r * c) m h *
      (CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
          (CompletedGauss.primaryGenerator (m * h)) *
        inverseCubicKernel (R * P') ((r * c) * m)) *
      (if IsCoprime P' (h * t) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
      hybridColumnCoefficient R r beta c m h *
      CanonicalQuadraticSieve.quadraticRow k' (CompletedGauss.primaryGenerator (m * h)) *
      hybridCubicCoefficient R r h t a P' * inverseCubicKernel P' (c * m) := by
  rw [normalized_ideal_product_weight, hybrid_kernel_quotients R r k' P' c m h hk hP']
  simp only [hybridColumnCoefficient, hybridCubicCoefficient, div_eq_mul_inv]
  ring

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Quotients
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem sum_quotientSupport {A : Type*} [AddCommMonoid A]
    (D : Ideal Eis) (S : Finset (Ideal Eis)) (f : Ideal Eis → A) :
    (∑ I ∈ S with D ∣ I, f I) = ∑ J ∈ quotientSupport D S, f (D * J) := by
  rw [quotientSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro I hI
    rw [idealQuotient_mul (Finset.mem_filter.mp hI).2]
  · intro I hI J hJ he
    exact idealQuotient_injective_on D (Finset.mem_filter.mp hI).2
      (Finset.mem_filter.mp hJ).2 he

theorem quotientSupport_cubic_admissible (D : Ideal Eis) (hD : D ≠ 0)
    (S : Finset (Ideal Eis)) (hS : ∀ I ∈ S, CubicSieve.Admissible I)
    (J : Ideal Eis) (hJ : J ∈ quotientSupport D S) :
    CubicSieve.Admissible J :=
  CubicSieve.cubic_admissible_of_dvd
    (hS (D * J) ((mem_quotientSupport D J hD S).mp hJ)) (dvd_mul_left _ _)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DivisorExtraction
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem inverseCubicKernel_divisor_overlap_zero (R r P c m : Ideal Eis)
    (hP : primaryGenerator P ≠ 0) (hcm : primaryGenerator (c * m) ≠ 0)
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    inverseCubicKernel P (c * m) = 0 := by
  apply inverseCubicKernel_eq_zero_of_not_coprime P (c * m) hP hcm
  intro hcop
  have hPc := hcop.of_isCoprime_of_dvd_right (dvd_mul_right c m)
  exact hRr ((hPc.of_isCoprime_of_dvd_left hRP).of_isCoprime_of_dvd_right hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal Eis)) (hrows : ∀ k ∈ rows, k ≠ 0)
    (R r : Ideal Eis) (hRr : IsCoprime R r) (F : Ideal Eis → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal Eis) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DivisorSum
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybridDivisorPool_bounds (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K)
    (D : Ideal Eis) (hD : D ∈ hybridDivisorPool rows) :
    D ≠ 0 ∧ (Ideal.absNorm D : ℝ) ≤ K := by
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  have hdiv := (mem_idealDivisors (hrows k hk).1).mp hDk
  exact ⟨ne_zero_of_dvd_ne_zero (hrows k hk).1 hdiv,
    (QuadraticMainBoundary.norm_le_of_dvd (hrows k hk).1 hdiv).trans (hrows k hk).2⟩

theorem hybridDivisorPairPool_subset (rows : Finset (Ideal Eis)) :
    hybridDivisorPairPool rows ⊆ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows) := by
  intro D hD
  obtain ⟨k, hk, hDk⟩ := Finset.mem_biUnion.mp hD
  exact Finset.mem_product.mpr
    ⟨Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).1⟩,
      Finset.mem_biUnion.mpr ⟨k, hk, (Finset.mem_product.mp hDk).2⟩⟩

theorem hybrid_divisor_pair_inverse_norm_sum
    (rows : Finset (Ideal Eis)) (K : ℝ)
    (hrows : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) :
    (∑ D ∈ hybridDivisorPairPool rows,
      1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ))) ≤
      (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
  have hb := hybridDivisorPool_bounds rows K hrows
  have hsum := finite_inverse_norm_sum (hybridDivisorPool rows) K
    (fun D hD => (hb D hD).1) (fun D hD => (hb D hD).2)
  calc
    _ ≤ ∑ D ∈ (hybridDivisorPool rows) ×ˢ (hybridDivisorPool rows),
        1 / ((Ideal.absNorm D.1 : ℝ) * (Ideal.absNorm D.2 : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (hybridDivisorPairPool_subset rows)
      intro D hD hn
      positivity
    _ = (∑ D ∈ hybridDivisorPool rows, 1 / (Ideal.absNorm D : ℝ)) ^ 2 := by
      rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro R hR
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ _ := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => by positivity) hsum 2

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Reconstruction
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem supportedHybridRow_product (nset bset Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    supportedHybridRow (nset ×ˢ bset) Pset a beta k = hybridRow Pset nset bset a beta k := by
  simp only [supportedHybridRow, hybridRow, hybridInner, Finset.sum_product,
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem supportedHybridRow_reconstruct
    (S : Finset (Ideal Eis × Ideal Eis)) (Pset : Finset (Ideal Eis))
    (hS : ∀ p ∈ S, Squarefree p.1 ∧ p.2 ≠ 0 ∧
      primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ)
    (k : Ideal Eis) (hk : Admissible k) :
    supportedHybridRow S Pset a beta k =
      ∑ d ∈ hybridColumnSupport S, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d := by
  unfold supportedHybridRow
  rw [hybrid_finite_column_reindex S (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdS := (mem_hybridColumnSupport S d).mp hd
  have hdprim := hS d.reconstruct hdS
  have hct := (d.primary_factors hdprim.2.2.1 hdprim.2.2.2).2.2.2.2
  apply Finset.sum_congr rfl
  intro P hPP
  unfold reconstructedHybridTerm
  exact congrArg
    (fun z : ℂ => a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
      beta (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2) * z)
    (hybrid_original_kernel_decomposition k P
    (d.common * d.residualN) ((d.common * d.residualB) * d.square ^ 2)
    d.common d.residualN d.residualB d.square hk (hP P hPP) hdprim.2.2.1 rfl rfl hct)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SieveComposition
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators
noncomputable section

theorem bounded_finset_coefficient_sum_sq {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by
  classical
  have h := finite_expansion_energy ({()} : Finset Unit) s
    (fun _ => s) (fun _ => b) (fun _ => f) (s.card : ℝ)
    (by simp) (by simpa using hb) (by simp)
  simpa using h

theorem bounded_coefficient_sum_sq {C : Type*} [Fintype C]
    (b f : C → ℂ) (hb : ∀ c, ‖b c‖ ≤ 1) :
    ‖∑ c, b c * f c‖ ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  classical
  simpa using bounded_finset_coefficient_sum_sq Finset.univ b f (by simpa using hb)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Dyadic
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_dyadic_reindex {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (f : HybridColumnData → A) :
    (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ j : Fin (columnDyadicLength B + 1),
        ∑ i : Fin (columnDyadicLength N + 1),
          ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
            ∑ d ∈ hybridCommonBlock S N i t, f d := by
  have ht : (∑ d ∈ hybridColumnSupport S, f d) =
      ∑ t ∈ hybridSquarePool S, ∑ d ∈ hybridColumnSupport S with d.square = t, f d := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (fun d hd => Finset.mem_image.mpr ⟨d, hd, rfl⟩) f
  rw [ht, sum_divisorDyadicBins (hybridSquarePool S) B]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  have hi := Finset.sum_fiberwise
    ((hybridColumnSupport S).filter fun d => d.square = t)
    (fun d => divisorDyadicLabel N d.common) f
  simpa only [Finset.filter_filter, hybridCommonBlock] using hi.symm

theorem hybridSquarePool_bounds (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (t : Ideal Eis) (ht : t ∈ hybridSquarePool S) :
    1 ≤ (Ideal.absNorm t : ℝ) ∧ (Ideal.absNorm t : ℝ) ≤ B := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
  have hb0 : (d.common * d.residualB) * d.square ^ 2 ≠ 0 :=
    mul_ne_zero d.g_squarefree.ne_zero (pow_ne_zero _ d.square_ne_zero)
  refine ⟨QuadraticMainBoundary.norm_one_le d.square_ne_zero, ?_⟩
  apply (QuadraticMainBoundary.norm_le_of_dvd hb0 ?_).trans
    (hS d.reconstruct ((mem_hybridColumnSupport S d).mp hd))
  exact dvd_mul_of_dvd_right (dvd_pow_self d.square (by norm_num : 2 ≠ 0)) _

theorem hybridSquarePool_bin_count (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) :
    ((divisorDyadicBin (hybridSquarePool S) B j).card : ℝ) ≤
      256 * divisorDyadicScale j.val := by
  have hscale := divisorDyadicScale_ge_one j.val
  have hb := divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B hS) j
  have hc := DescentFiberCost.finite_ideal_count_real
    (divisorDyadicBin (hybridSquarePool S) B j) (2 * divisorDyadicScale j.val)
    (by linarith) (fun t ht hz => by
      have hp := (hb t ht).1
      simp [hz] at hp
      linarith) (fun t ht => (hb t ht).2)
  linarith

theorem hybridCommonBlock_bounds
    (S : Finset (Ideal Eis × Ideal Eis)) (N B : ℝ) (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B)
    (i : Fin (columnDyadicLength N + 1)) (j : Fin (columnDyadicLength B + 1))
    (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j)
    (d : HybridColumnData) (hd : d ∈ hybridCommonBlock S N i t) :
    let C := divisorDyadicScale i.val
    let T := divisorDyadicScale j.val
    C ≤ (Ideal.absNorm d.common : ℝ) ∧ (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧
    (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
    (Ideal.absNorm d.residualB : ℝ) ≤ B / (C * T ^ 2) ∧
    (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ N * B / (C ^ 2 * T ^ 2) := by
  obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
  have hs := hS d.reconstruct ((mem_hybridColumnSupport S d).mp hdS)
  have hc1 := QuadraticMainBoundary.norm_one_le d.common_ne_zero
  have hcn : (Ideal.absNorm d.common : ℝ) ≤ N :=
    (QuadraticMainBoundary.norm_le_of_dvd d.n_squarefree.ne_zero (dvd_mul_right _ _)).trans hs.1
  have hcb := divisorDyadicLabel_bounds N d.common hc1 hcn
  rw [hdi] at hcb
  have hcLow : divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) :=
    max_le hc1 hcb.1.le
  have hcHigh : (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val := by
    have hh : (2 : ℝ) ^ i.val / 2 ≤ divisorDyadicScale i.val := le_max_right _ _
    linarith [hcb.2]
  have htLow := (divisorDyadicBin_bounds (hybridSquarePool S) B
    (hybridSquarePool_bounds S B (fun p hp => (hS p hp).2)) j t ht).1
  rw [← hdt] at htLow
  refine ⟨hcLow, hcHigh, ?_⟩
  exact d.residual_norm_bounds N B (divisorDyadicScale i.val) (divisorDyadicScale j.val)
    hN hB (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val]) hs.1 hs.2 hcLow htLow

theorem hybrid_square_dyad_energy
    (S : Finset (Ideal Eis × Ideal Eis)) (B : ℝ)
    (hS : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B)
    (j : Fin (columnDyadicLength B + 1)) (rows : Finset (Ideal Eis))
    (F : Ideal Eis → Ideal Eis → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      (∑ k ∈ rows, ‖F t k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j, F t k‖ ^ 2) ≤
      (256 * divisorDyadicScale j.val) ^ 2 * E := by
  let Tset := divisorDyadicBin (hybridSquarePool S) B j
  have hc := hybridSquarePool_bin_count S B hS j
  calc
    _ ≤ (Tset.card : ℝ) * ∑ t ∈ Tset, ∑ k ∈ rows, ‖F t k‖ ^ 2 := by
      calc
        _ ≤ ∑ k ∈ rows, (Tset.card : ℝ) * ∑ t ∈ Tset, ‖F t k‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          simpa using bounded_finset_coefficient_sum_sq Tset (fun _ => 1) (fun t => F t k)
            (by simp)
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (Tset.card : ℝ) * ∑ _t ∈ Tset, E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hF) (Nat.cast_nonneg _)
    _ = (Tset.card : ℝ) ^ 2 * E := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) hE

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Grid
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

section FiniteGrid
variable {M H C A : Type*} [DecidableEq M] [DecidableEq H] [DecidableEq C] [AddCommMonoid A]

theorem finite_triple_support_reindex (T : Finset ((M × H) × C))
    (f : (M × H) × C → A) :
    (∑ u ∈ T, f u) = ∑ p ∈ T.image Prod.fst,
      ∑ c ∈ gridCommonSupport T p.1, if (p, c) ∈ T then f (p, c) else 0 := by
  have hp := Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image Prod.fst) (g := Prod.fst)
    (fun u hu => Finset.mem_image.mpr ⟨u, hu, rfl⟩) f
  rw [← hp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun u _ => u.2)
  · intro u hu
    obtain ⟨huT, hup⟩ := Finset.mem_filter.mp hu
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨huT, congrArg Prod.fst hup⟩, rfl⟩
    · simpa only [← hup, Prod.eta] using huT
  · intro u hu v hv he
    apply Prod.ext
    · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
    · exact he
  · intro c hc
    have hpc := (Finset.mem_filter.mp hc).2
    exact ⟨(p, c), Finset.mem_filter.mpr ⟨hpc, rfl⟩, rfl⟩
  · intro u hu
    have hup := (Finset.mem_filter.mp hu).2
    simp only [← hup, Prod.eta]

end FiniteGrid

theorem HybridColumnData.gridIndex_injective_on_square (t : Ideal Eis) :
    Set.InjOn HybridColumnData.gridIndex {d | d.square = t} := by
  intro d hd e he hg
  have hm : d.residualN = e.residualN := congrArg (fun u => u.1.1) hg
  have hh : d.residualB = e.residualB := congrArg (fun u => u.1.2) hg
  have hc : d.common = e.common := congrArg Prod.snd hg
  have ht : d.square = e.square := hd.trans he.symm
  cases d
  cases e
  cases hc
  cases hm
  cases hh
  cases ht
  rfl

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ExtractedGrid
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

theorem sum_quotientGridSupport {A : Type*} [AddCommMonoid A]
    (r : Ideal Eis) (T : Grid) (f : (Ideal Eis × Ideal Eis) × Ideal Eis → A) :
    (∑ u ∈ T, if r ∣ u.2 then f u else 0) =
      ∑ u ∈ quotientGridSupport r T, f (u.1, r * u.2) := by
  rw [← Finset.sum_filter, quotientGridSupport, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    rw [idealQuotient_mul (Finset.mem_filter.mp hu).2]
  · intro u hu v hv he
    apply Prod.ext
    · simpa only using congrArg Prod.fst he
    · exact idealQuotient_injective_on r (Finset.mem_filter.mp hu).2
        (Finset.mem_filter.mp hv).2 (congrArg Prod.snd he)

theorem quotientGridSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (p : Ideal Eis × Ideal Eis) (c : Ideal Eis)
    (hu : (p, c) ∈ quotientGridSupport r (hybridGridSupport D)) :
    ∃ d ∈ D, (d.residualN, d.residualB) = p ∧ d.common = r * c := by
  have hm := (mem_quotientGridSupport r hr (hybridGridSupport D) p c).mp hu
  obtain ⟨d, hd, he⟩ := Finset.mem_image.mp hm
  exact ⟨d, hd, congrArg Prod.fst he, congrArg Prod.snd he⟩

theorem quotientGridCommonSupport_origin (r : Ideal Eis) (hr : r ≠ 0)
    (D : Finset HybridColumnData) (m c : Ideal Eis)
    (hc : c ∈ gridCommonSupport (quotientGridSupport r (hybridGridSupport D)) m) :
    ∃ d ∈ D, d.residualN = m ∧ d.common = r * c := by
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hc
  obtain ⟨huQ, hum⟩ := Finset.mem_filter.mp hu
  obtain ⟨d, hd, hp, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 huQ
  refine ⟨d, hd, (congrArg Prod.fst hp).trans hum, ?_⟩
  simpa only [he] using hdc

theorem extractedGridCoefficient_norm_le_one (T : Grid) (R t : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (hb : ∀ u ∈ T, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1)
    (c m h : Ideal Eis) : ‖extractedGridCoefficient T R t beta c m h‖ ≤ 1 := by
  unfold extractedGridCoefficient
  split_ifs with hu hcop
  · simpa using hb ((m, h), c) hu
  · simp
  · simp

theorem gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hQ : quotientGridSupport r T = ∅) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport, hQ]
  exact Finset.sum_empty

theorem gridDivisorHybridBlock_extract
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hR : R ≠ 0) (hr : r ≠ 0)
    (hk : Admissible ((R * r) * k))
    (hP : ∀ P ∈ Pset, CubicSieve.Admissible P) :
    gridDivisorHybridBlock T Pset a beta t ((R * r) * k) R r =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        ∑ p ∈ (quotientGridSupport r T).image Prod.fst,
          quadraticRow k (primaryGenerator (p.1 * p.2)) *
            ∑ c ∈ gridCommonSupport (quotientGridSupport r T) p.1,
              hybridColumnCoefficient R r (extractedGridCoefficient T R t beta) c p.1 p.2 *
                ∑ P ∈ quotientSupport R Pset,
                  hybridCubicCoefficient R r p.2 t a P * inverseCubicKernel P (c * p.1) := by
  have hmask (P h : Ideal Eis) :
      (if IsCoprime (R * P) (h * t) then (1 : ℂ) else 0) =
      (if IsCoprime R (h * t) then 1 else 0) *
        (if IsCoprime P (h * t) then 1 else 0) := by
    simp only [IsCoprime.mul_left_iff]
    split_ifs <;> simp_all
  unfold gridDivisorHybridBlock
  rw [sum_quotientGridSupport]
  have hinner (u : (Ideal Eis × Ideal Eis) × Ideal Eis) :
      (∑ P ∈ Pset, if R ∣ P then
        a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (quadraticRow ((R * r) * k) (primaryGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel P ((r * u.2) * u.1.1)) *
              (if IsCoprime P (u.1.2 * t) then 1 else 0) else 0) =
      ∑ P ∈ quotientSupport R Pset,
        a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) * beta (r * u.2) u.1.1 u.1.2 *
          (quadraticRow ((R * r) * k) (primaryGenerator (u.1.1 * u.1.2)) *
            inverseCubicKernel (R * P) ((r * u.2) * u.1.1)) *
              (if IsCoprime (R * P) (u.1.2 * t) then 1 else 0) := by
    rw [← Finset.sum_filter]
    exact sum_quotientSupport R Pset _
  simp_rw [hinner]
  rw [finite_triple_support_reindex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hu : (p, c) ∈ quotientGridSupport r T
  · have huc := (mem_quotientGridSupport r hr T p c).mp hu
    simp only [hu, ite_true]
    apply Finset.sum_congr rfl
    intro P hPP
    have hpgen := (quotientSupport_cubic_admissible R hR Pset hP P hPP).2
    have hid := hybrid_extracted_block_identity R r k P c p.1 p.2 t hk hpgen a
      (extractedGridCoefficient T R t beta)
    simp only [extractedGridCoefficient, huc, ite_true] at hid
    rw [hmask]
    calc
      _ = a (R * P) / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) *
          (beta (r * c) p.1 p.2 * (if IsCoprime R (p.2 * t) then 1 else 0)) *
          (quadraticRow ((R * r) * k) (primaryGenerator (p.1 * p.2)) *
            inverseCubicKernel (R * P) ((r * c) * p.1)) *
          (if IsCoprime P (p.2 * t) then 1 else 0) := by ring
      _ = _ := by rw [hid]; ring
  · have huc : (p, r * c) ∉ T := (mem_quotientGridSupport r hr T p c).not.mp hu
    simp [hu, hybridColumnCoefficient, extractedGridCoefficient, huc]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.DyadicBlock
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_extracted_dyadic_block_nonempty (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (quotientGridSupport r (hybridGridSupport D)).Nonempty →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_original_quotient_block ε hε
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta hQ
  let Q := quotientGridSupport r (hybridGridSupport D)
  let X := N * B / (C ^ 2 * T ^ 2)
  let A := 2 * C / (Ideal.absNorm r : ℝ)
  let H := B / (C * T ^ 2)
  have hC0 : 0 < C := by linarith
  have hT0 : 0 < T := by linarith
  have hnr : 0 < (Ideal.absNorm r : ℝ) := QuadraticMainBoundary.norm_pos hr
  have hnorm (d : HybridColumnData) (hd : d ∈ D) :
      (Ideal.absNorm d.residualN : ℝ) ≤ N / C ∧
      (Ideal.absNorm d.residualB : ℝ) ≤ H ∧
      (Ideal.absNorm (d.residualN * d.residualB) : ℝ) ≤ X := by
    have hd' := hD d hd
    apply d.residual_norm_bounds N B C T (by linarith) (by linarith) hC0 hT0
      (hn _ hd'.2.2.2.1).2 hd'.2.2.2.2 hd'.2.1
    simpa only [hd'.1] using ht
  have hcBound (d : HybridColumnData) (hd : d ∈ D) (c : Ideal Eis)
      (hdc : d.common = r * c) : c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A := by
    have hcz : c ≠ 0 := by
      intro hz
      apply d.common_ne_zero
      simp [hdc, hz]
    refine ⟨hcz, (le_div_iff₀ hnr).mpr ?_⟩
    have hdcN := (hD d hd).2.2.1
    rw [hdc, map_mul, Nat.cast_mul] at hdcN
    simpa only [mul_comm] using hdcN
  have hpair (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst) :
      Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X ∧
      p.2 ≠ 0 ∧ (Ideal.absNorm p.2 : ℝ) ≤ H := by
    obtain ⟨u, hu, hup⟩ := Finset.mem_image.mp hp
    obtain ⟨d, hd, he, hdc⟩ := quotientGridSupport_origin r hr D u.1 u.2 hu
    have he' : (d.residualN, d.residualB) = p := he.trans hup
    have hm := congrArg Prod.fst he'
    have hh := congrArg Prod.snd he'
    have hdB : d.residualB ≠ 0 :=
      ne_zero_of_dvd_ne_zero d.g_squarefree.ne_zero (dvd_mul_left _ _)
    exact ⟨by simpa only [← hm, ← hh] using d.residual_product_squarefree,
      by simpa only [← hm, ← hh] using (hnorm d hd).2.2,
      by simpa only [← hh] using hdB,
      by simpa only [← hh] using (hnorm d hd).2.1⟩
  have hcset (p : Ideal Eis × Ideal Eis) (hp : p ∈ Q.image Prod.fst)
      (c : Ideal Eis) (hc : c ∈ gridCommonSupport Q p.1) :
      c ≠ 0 ∧ (Ideal.absNorm c : ℝ) ≤ A ∧ (r * c) * p.1 ∈ nset := by
    obtain ⟨d, hd, hm, hdc⟩ := quotientGridCommonSupport_origin r hr D p.1 c hc
    have hc' := hcBound d hd c hdc
    exact ⟨hc'.1, hc'.2, by simpa only [hdc, hm] using (hD d hd).2.2.2.1⟩
  obtain ⟨u₀, hu₀⟩ := hQ
  have hp₀ : u₀.1 ∈ Q.image Prod.fst := Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩
  have hc₀ : u₀.2 ∈ gridCommonSupport Q u₀.1.1 :=
    Finset.mem_image.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀, rfl⟩, rfl⟩
  have hX : 1 ≤ X :=
    (QuadraticMainBoundary.norm_one_le (hpair u₀.1 hp₀).1.ne_zero).trans (hpair u₀.1 hp₀).2.1
  have hH : 1 ≤ H :=
    (QuadraticMainBoundary.norm_one_le (hpair u₀.1 hp₀).2.2.1).trans (hpair u₀.1 hp₀).2.2.2
  have hA : 1 ≤ A :=
    (QuadraticMainBoundary.norm_one_le (hcset u₀.1 hp₀ u₀.2 hc₀).1).trans
      (hcset u₀.1 hp₀ u₀.2 hc₀).2.1
  have hbGrid : ∀ u ∈ hybridGridSupport D, ‖beta u.2 u.1.1 u.1.2‖ ≤ 1 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact hbeta d hd
  have he := hblock K X N L A H hK hX hN hA hH R r t hR hr rows nset Pset
    (Q.image Prod.fst) (gridCommonSupport Q) a
    (extractedGridCoefficient (hybridGridSupport D) R t beta)
    hrows hn hP ha (fun p hp => ⟨(hpair p hp).1, (hpair p hp).2.1⟩)
    (fun p hp => (hpair p hp).2.2) hcset
    (fun p _ c _ => extractedGridCoefficient_norm_le_one _ R t beta hbGrid (r * c) p.1 p.2)
  have hrow (k : Ideal Eis) (hk : k ∈ quotientSupport (R * r) rows) :=
    gridDivisorHybridBlock_extract (hybridGridSupport D) Pset a beta t k R r hR hr
      (hrows _ ((mem_quotientSupport (R * r) k (mul_ne_zero hR hr) rows).mp hk)).1
      (fun P hP' => (hP P hP').1)
  have he' : (∑ k ∈ quotientSupport (R * r) rows,
      ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₁ * (K * X * N) ^ ε * (K + X) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
    calc
      _ = _ := Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
      _ ≤ _ := he
  have hXupper : X ≤ N * B := by
    apply div_le_self (by positivity : 0 ≤ N * B)
    have hC2 : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    exact one_le_mul_of_one_le_of_one_le hC2 hT2
  apply he'.trans
  calc
    _ ≤ C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * A * H /
        (Ideal.absNorm R : ℝ) * CubicSieve.sieveNorm N (2 * L) := by
      have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
      gcongr
    _ = _ := by
      dsimp only [A, H]
      field_simp

theorem hybrid_extracted_dyadic_block (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (R r t : Ideal Eis), R ≠ 0 → r ≠ 0 → T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ quotientSupport (R * r) rows,
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t ((R * r) * k) R r‖ ^ 2) ≤
      C₀ * (K * (N * B) * N) ^ ε * (K + N * B) * B /
        ((Ideal.absNorm R : ℝ) * (Ideal.absNorm r : ℝ) * T ^ 2) *
          CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := hybrid_extracted_dyadic_block_nonempty ε hε
  refine ⟨C₀, hC₀, ?_⟩
  intro K N B L C T hK hN hB hC hT R r t hR hr ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  by_cases hQ : (quotientGridSupport r (hybridGridSupport D)).Nonempty
  · exact he K N B L C T hK hN hB hC hT R r t hR hr ht
      rows nset Pset D a beta hrows hn hP ha hD hbeta hQ
  · have hQ' := Finset.not_nonempty_iff_eq_empty.mp hQ
    simp only [gridDivisorHybridBlock_eq_zero_of_quotientGrid_empty _ _ _ _ _ _ _ _ hQ',
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
    positivity

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.MaskedGrid
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum UniqueFactorizationMonoid
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "Grid" => Finset ((Ideal Eis × Ideal Eis) × Ideal Eis)

theorem maskedGridHybridRow_mobius (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k : Ideal Eis) (hk : k ≠ 0) :
    maskedGridHybridRow T Pset a beta t k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) *
          gridDivisorHybridBlock T Pset a beta t k D.1 D.2 := by
  have hm (P c : Ideal Eis) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold maskedGridHybridRow
  simp_rw [hm, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  unfold gridDivisorHybridBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hrc : D.2 ∣ u.2
  · simp only [hrc, ite_true, and_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hRP : D.1 ∣ P <;> simp [hRP]
  · simp [hrc]

theorem gridDivisorHybridBlock_zero_of_not_coprime
    (T : Grid) (Pset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ)
    (t k R r : Ideal Eis) (hRr : ¬ IsCoprime R r)
    (hP : ∀ P ∈ Pset, primaryGenerator P ≠ 0)
    (hT : ∀ u ∈ T, primaryGenerator (u.2 * u.1.1) ≠ 0) :
    gridDivisorHybridBlock T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hrc : r ∣ u.2
  · simp only [hrc, ite_true]
    apply Finset.sum_eq_zero
    intro P hPP
    by_cases hRP : R ∣ P
    · simp only [hRP, ite_true]
      rw [inverseCubicKernel_divisor_overlap_zero R r P u.2 u.1.1
        (hP P hPP) (hT u hu) hRP hrc hRr]
      simp
    · simp only [hRP, ite_false]
  · simp only [hrc, ite_false]

theorem maskedGridHybridRow_divisor_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℝ, 1 ≤ K →
    ∀ (rows : Finset (Ideal Eis)) (T : Grid) (Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (t : Ideal Eis),
      (∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∑ k ∈ rows, ‖maskedGridHybridRow T Pset a beta t k‖ ^ 2) ≤
        C * K ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖gridDivisorHybridBlock T Pset a beta t k D.1 D.2‖ ^ 2 else 0 := by
  obtain ⟨C, hC, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro K hK rows T Pset a beta t hrows
  have he (k : Ideal Eis) (hk : k ∈ rows) :=
    maskedGridHybridRow_mobius T Pset a beta t k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (fun k D => gridDivisorHybridBlock T Pset a beta t k D.1 D.2) (C ^ 2 * K ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.1)
        (QuadraticInitialBound.norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k (hrows k hk).1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * K ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * K ^ ε := by
        rw [mul_pow, pow_two (K ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < K)]
        congr 1
        congr 1
        ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.FixedSquare
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_fixed_square_grid_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L C T : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ C → 1 ≤ T →
    ∀ (t : Ideal Eis), T ≤ (Ideal.absNorm t : ℝ) →
    ∀ (rows nset Pset : Finset (Ideal Eis)) (D : Finset HybridColumnData)
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) →
      (∀ d ∈ D, d.square = t ∧ C ≤ (Ideal.absNorm d.common : ℝ) ∧
        (Ideal.absNorm d.common : ℝ) ≤ 2 * C ∧ d.common * d.residualN ∈ nset ∧
        (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B) →
      (∀ d ∈ D, ‖beta d.common d.residualN d.residualB‖ ≤ 1) →
      (∑ k ∈ rows, ‖maskedGridHybridRow (hybridGridSupport D) Pset a beta t k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hblock⟩ := hybrid_extracted_dyadic_block ε hε
  obtain ⟨C₂, hC₂, hmask⟩ := maskedGridHybridRow_divisor_energy ε hε
  refine ⟨C₁ * C₂ * 256 ^ 2, by positivity, ?_⟩
  intro K N B L C T hK hN hB hC hT t ht rows nset Pset D a beta
    hrows hn hP ha hD hbeta
  have hr0 : ∀ k ∈ rows, k ≠ 0 ∧ (Ideal.absNorm k : ℝ) ≤ K :=
    fun k hk => ⟨(hrows k hk).1.1, (hrows k hk).2⟩
  let E := C₁ * (K * (N * B) * N) ^ ε * (K + N * B) * B / T ^ 2 *
    CubicSieve.sieveNorm N (2 * L)
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hTprim : ∀ u ∈ hybridGridSupport D, primaryGenerator (u.2 * u.1.1) ≠ 0 := by
    intro u hu
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hu
    exact (hn _ (hD d hd).2.2.2.1).1.2
  have hterm (v : Ideal Eis × Ideal Eis) (hv : v ∈ hybridDivisorPairPool rows) :
      (∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) := by
    have hp := Finset.mem_product.mp (hybridDivisorPairPool_subset rows hv)
    have hR := (hybridDivisorPool_bounds rows K hr0 v.1 hp.1).1
    have hr := (hybridDivisorPool_bounds rows K hr0 v.2 hp.2).1
    by_cases hcop : IsCoprime v.1 v.2
    · rw [double_divisor_row_reindex rows (fun k hk => (hr0 k hk).1) v.1 v.2 hcop]
      have he := hblock K N B L C T hK hN hB hC hT v.1 v.2 t hR hr ht
        rows nset Pset D a beta hrows hn hP ha hD hbeta
      convert (preTransparency := .instances) he using 1
      dsimp only [E]
      field_simp
    · simp only [gridDivisorHybridBlock_zero_of_not_coprime _ _ _ _ _ _ _ _ hcop
          (fun P hPP => (hP P hPP).1.2) hTprim,
        norm_zero, zero_pow (by norm_num : 2 ≠ 0), ite_self, Finset.sum_const_zero]
      exact mul_nonneg hE (by positivity)
  have he := hmask K hK rows (hybridGridSupport D) Pset a beta t hr0
  have hsum : (∑ v ∈ hybridDivisorPairPool rows,
      ∑ k ∈ rows, if v ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
        ‖gridDivisorHybridBlock (hybridGridSupport D) Pset a beta t k v.1 v.2‖ ^ 2 else 0) ≤
      E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2 := by
    calc
      _ ≤ ∑ v ∈ hybridDivisorPairPool rows,
          E * (1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = E * ∑ v ∈ hybridDivisorPairPool rows,
          1 / ((Ideal.absNorm v.1 : ℝ) * (Ideal.absNorm v.2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hybrid_divisor_pair_inverse_norm_sum rows K hr0) hE
  apply he.trans
  calc
    _ ≤ C₂ * K ^ ε * (E * (256 * (columnDyadicLength K + 1 : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp only [E]; ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SourceHybrid
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem reconstructed_fixed_square_grid
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) :
    (∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d) =
      (if IsCoprime k t then 1 else 0) *
        maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k := by
  unfold maskedGridHybridRow hybridGridSupport
  rw [Finset.sum_image]
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro P hP
    simp only [reconstructedHybridTerm, HybridColumnData.gridIndex,
      sourceGridCoefficient, hD d hd]
    ac_rfl
  · intro d hd e he hg
    exact HybridColumnData.gridIndex_injective_on_square t (hD d hd) (hD e he) hg

theorem reconstructed_fixed_square_energy_le
    (D : Finset HybridColumnData) (t : Ideal Eis) (hD : ∀ d ∈ D, d.square = t)
    (rows Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ)
    (beta : Ideal Eis → Ideal Eis → ℂ) :
    (∑ k ∈ rows, ‖∑ d ∈ D, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤
      ∑ k ∈ rows,
        ‖maskedGridHybridRow (hybridGridSupport D) Pset a (sourceGridCoefficient beta t) t k‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  rw [reconstructed_fixed_square_grid D t hD Pset a beta k]
  by_cases hkt : IsCoprime k t
  · simp only [hkt, ite_true, one_mul, le_refl]
  · simp only [hkt, ite_false, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact sq_nonneg _

theorem finite_double_row_energy {I J : Type*} [Fintype I] [Fintype J]
    (rows : Finset (Ideal Eis)) (F : I → J → Ideal Eis → ℂ) (E : ℝ) (_hE : 0 ≤ E)
    (hF : ∀ i j, (∑ k ∈ rows, ‖F i j k‖ ^ 2) ≤ E) :
    (∑ k ∈ rows, ‖∑ i, ∑ j, F i j k‖ ^ 2) ≤
      ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) ^ 2 * E := by
  have hk (k : Ideal Eis) :
      ‖∑ i, ∑ j, F i j k‖ ^ 2 ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
          ∑ i, ∑ j, ‖F i j k‖ ^ 2 := by
    simpa only [one_mul, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul] using
      bounded_coefficient_sum_sq (fun _ : I × J => 1) (fun u => F u.1 u.2 k) (by simp)
  calc
    _ ≤ ∑ k ∈ rows, ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ‖F i j k‖ ^ 2 := Finset.sum_le_sum (fun k _ => hk k)
    _ = ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) *
        ∑ i, ∑ j, ∑ k ∈ rows, ‖F i j k‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ((Fintype.card I : ℝ) * (Fintype.card J : ℝ)) * ∑ _i : I, ∑ _j : J, E := by
      gcongr with i hi j hj
      exact hF i j
    _ = _ := by simp; ring

theorem supportedHybridRow_energy_log (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C₀ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
        CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2 *
          (columnDyadicLength N + 1 : ℝ) ^ 2 * (columnDyadicLength B + 1 : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁, hfixed⟩ := hybrid_fixed_square_grid_energy ε hε
  refine ⟨256 ^ 2 * C₁, by positivity, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  let nset := S.image Prod.fst
  let E := C₁ * K ^ ε * (K * (N * B) * N) ^ ε * (K + N * B) * B *
    CubicSieve.sieveNorm N (2 * L) * (columnDyadicLength K + 1 : ℝ) ^ 2
  let F (j : Fin (columnDyadicLength B + 1)) (i : Fin (columnDyadicLength N + 1))
      (k : Ideal Eis) : ℂ :=
    ∑ t ∈ divisorDyadicBin (hybridSquarePool S) B j,
      ∑ d ∈ hybridCommonBlock S N i t, ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hnset : ∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    exact ⟨⟨(hS p hp).1, (hS p hp).2.1⟩, (hS p hp).2.2.2.1⟩
  have hBsup : ∀ p ∈ S, (Ideal.absNorm p.2 : ℝ) ≤ B := fun p hp => (hS p hp).2.2.2.2
  have hlen : ∀ p ∈ S, (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B :=
    fun p hp => (hS p hp).2.2.2
  have hlabel (j : Fin (columnDyadicLength B + 1))
      (i : Fin (columnDyadicLength N + 1)) :
      (∑ k ∈ rows, ‖F j i k‖ ^ 2) ≤ 256 ^ 2 * E := by
    let Td := divisorDyadicScale j.val
    have hTd : 0 < Td := by dsimp only [Td]; linarith [divisorDyadicScale_ge_one j.val]
    have htEnergy (t : Ideal Eis) (ht : t ∈ divisorDyadicBin (hybridSquarePool S) B j) :
        (∑ k ∈ rows, ‖∑ d ∈ hybridCommonBlock S N i t,
          ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d‖ ^ 2) ≤ E / Td ^ 2 := by
      let D := hybridCommonBlock S N i t
      have hD (d : HybridColumnData) (hd : d ∈ D) :
          d.square = t ∧ divisorDyadicScale i.val ≤ (Ideal.absNorm d.common : ℝ) ∧
          (Ideal.absNorm d.common : ℝ) ≤ 2 * divisorDyadicScale i.val ∧
          d.common * d.residualN ∈ nset ∧
          (Ideal.absNorm ((d.common * d.residualB) * d.square ^ 2) : ℝ) ≤ B := by
        obtain ⟨hdS, hdt, hdi⟩ := Finset.mem_filter.mp hd
        have hdorig := (mem_hybridColumnSupport S d).mp hdS
        have hb := hybridCommonBlock_bounds S N B (by linarith) (by linarith) hlen i j t ht d hd
        exact ⟨hdt, hb.1, hb.2.1, Finset.mem_image.mpr ⟨d.reconstruct, hdorig, rfl⟩,
          hBsup d.reconstruct hdorig⟩
      have hβ : ∀ d ∈ D, ‖sourceGridCoefficient beta t d.common d.residualN d.residualB‖ ≤ 1 := by
        intro d hd
        have hdo := (mem_hybridColumnSupport S d).mp (Finset.mem_filter.mp hd).1
        simpa only [sourceGridCoefficient, ← (hD d hd).1, HybridColumnData.reconstruct] using
          hbeta d.reconstruct hdo
      have hfix := hfixed K N B L (divisorDyadicScale i.val) Td hK hN hB
        (divisorDyadicScale_ge_one i.val) (divisorDyadicScale_ge_one j.val) t
        (divisorDyadicBin_bounds (hybridSquarePool S) B (hybridSquarePool_bounds S B hBsup) j t ht).1
        rows nset Pset D a (sourceGridCoefficient beta t) hrows hnset hP ha hD hβ
      apply (reconstructed_fixed_square_energy_le D t (fun d hd => (hD d hd).1) rows Pset a beta).trans
      convert (preTransparency := .instances) hfix using 1 ; dsimp only [E] ; ring
    have he := hybrid_square_dyad_energy S B hBsup j rows
      (fun t k => ∑ d ∈ hybridCommonBlock S N i t,
        ∑ P ∈ Pset, reconstructedHybridTerm a beta k P d)
      (E / Td ^ 2) (div_nonneg hE (sq_nonneg _)) htEnergy
    calc
      _ ≤ (256 * Td) ^ 2 * (E / Td ^ 2) := he
      _ = 256 ^ 2 * E := by field_simp
  have hrow (k : Ideal Eis) (hk : k ∈ rows) :
      supportedHybridRow S Pset a beta k = ∑ j, ∑ i, F j i k := by
    rw [supportedHybridRow_reconstruct S Pset
      (fun p hp => ⟨(hS p hp).1,
        primaryGenerator_ne_zero_ideal p.2 (hS p hp).2.2.1,
        (hS p hp).2.1, (hS p hp).2.2.1⟩)
      (fun P hPP => (hP P hPP).1.2) a beta k (hrows k hk).1]
    exact hybrid_dyadic_reindex S N B _
  calc
    _ = ∑ k ∈ rows, ‖∑ j, ∑ i, F j i k‖ ^ 2 :=
      Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hrow k hk))
    _ ≤ ((Fintype.card (Fin (columnDyadicLength B + 1)) : ℝ) *
        (Fintype.card (Fin (columnDyadicLength N + 1)) : ℝ)) ^ 2 * (256 ^ 2 * E) :=
      finite_double_row_energy rows F (256 ^ 2 * E) (by positivity) hlabel
    _ = _ := by simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, E]; ring

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.HybridBound
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

private theorem hybrid_log_cost_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
      K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2 ≤ C * (K * N * B) ^ ε := by
  let δ := ε / 9
  let A := 2 + 1 / (δ * Real.log 2)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  refine ⟨A ^ 6, pow_pos hA 6, ?_⟩
  intro K N B hK hN hB
  let Q := K * N * B
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hK hN) hB
  have hQ0 : 0 < Q := by linarith
  have hKQ : K ≤ Q :=
    (le_mul_of_one_le_right (by linarith : 0 ≤ K) hN).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hNQ : N ≤ Q :=
    (le_mul_of_one_le_left (by linarith : 0 ≤ N) hK).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ K * N) hB)
  have hBQ : B ≤ Q := le_mul_of_one_le_left (by linarith)
    (one_le_mul_of_one_le_of_one_le hK hN)
  have hquad : K * (N * B) * N ≤ Q ^ 2 := by
    calc
      _ = Q * N := by dsimp only [Q]; ring
      _ ≤ Q * Q := mul_le_mul_of_nonneg_left hNQ hQ0.le
      _ = _ := by ring
  have hlog (Y : ℝ) (hY : 1 ≤ Y) (hYQ : Y ≤ Q) :
      (columnDyadicLength Y + 1 : ℝ) ≤ A * Q ^ δ := by
    exact (columnDyadicLength_small_power δ hδ Y hY).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hYQ hδ.le) hA.le)
  have hpow2 : (Q ^ 2) ^ δ = (Q ^ δ) ^ 2 := by
    rw [← Real.rpow_natCast_mul hQ0.le 2 δ]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    ring
  have hpow9 : (Q ^ δ) ^ 9 = Q ^ ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
    congr 1
    dsimp only [δ]
    ring
  calc
    _ ≤ Q ^ δ * (Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 * (A * Q ^ δ) ^ 2 := by
      have hbase := Real.rpow_le_rpow (by positivity : 0 ≤ K * (N * B) * N) hquad hδ.le
      rw [hpow2] at hbase
      gcongr
      · exact hlog K hK hKQ
      · exact hlog N hN hNQ
      · exact hlog B hB hBQ
    _ = A ^ 6 * (Q ^ δ) ^ 9 := by ring
    _ = _ := by rw [hpow9]

theorem supportedHybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows : Finset (Ideal Eis)) (S : Finset (Ideal Eis × Ideal Eis))
      (Pset : Finset (Ideal Eis)) (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ p ∈ S, Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ p ∈ S, ‖beta p.1 p.2‖ ≤ 1) →
      (∑ k ∈ rows, ‖supportedHybridRow S Pset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C₀, hC₀, he⟩ := supportedHybridRow_energy_log (ε / 9) (by positivity)
  obtain ⟨C₁, hC₁, hlogs⟩ := hybrid_log_cost_bound ε hε
  refine ⟨C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hb := he K N B L hK hN hB rows S Pset a beta hrows hS hP ha hbeta
  have hs : 0 ≤ CubicSieve.sieveNorm N (2 * L) := sq_nonneg _
  apply hb.trans
  calc
    _ = C₀ * (K ^ (ε / 9) * (K * (N * B) * N) ^ (ε / 9) *
        (columnDyadicLength K + 1 : ℝ) ^ 2 * (columnDyadicLength N + 1 : ℝ) ^ 2 *
          (columnDyadicLength B + 1 : ℝ) ^ 2) *
        (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by ring
    _ ≤ C₀ * (C₁ * (K * N * B) ^ ε) * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hlogs K N B hK hN hB) hC₀.le)
            (by positivity)) (by linarith)) hs
    _ = _ := by ring

theorem hybridRow_energy_sieve_norm (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B) ^ ε * (K + N * B) * B * CubicSieve.sieveNorm N (2 * L) := by
  obtain ⟨C, hC, he⟩ := supportedHybridRow_energy_sieve_norm ε hε
  refine ⟨C, hC, ?_⟩
  intro K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta
  have hprod : ∀ p ∈ nset ×ˢ bset,
      Squarefree p.1 ∧ primaryGenerator p.1 ≠ 0 ∧ primaryGenerator p.2 ≠ 0 ∧
        (Ideal.absNorm p.1 : ℝ) ≤ N ∧ (Ideal.absNorm p.2 : ℝ) ≤ B := by
    intro p hp
    obtain ⟨hpn, hpb⟩ := Finset.mem_product.mp hp
    exact ⟨(hn p.1 hpn).1.1, (hn p.1 hpn).1.2, (hb p.2 hpb).1,
      (hn p.1 hpn).2, (hb p.2 hpb).2⟩
  have hh := he K N B L hK hN hB rows (nset ×ˢ bset) Pset a beta hrows hprod hP ha
    (fun p hp => hbeta p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2)
  simpa only [supportedHybridRow_product] using hh

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Sharp
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open CanonicalQuadraticSieve CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem hybrid_sharp_cubic_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      (K * N * B) ^ (ε / 2) * CubicSieve.sieveNorm N (2 * L) ≤
        C * (K * N * B * L) ^ ε * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := CubicSieve.sieveNorm_sharp (ε / 2) (by positivity)
  refine ⟨2 * C * (2 : ℝ) ^ (ε / 2), by positivity, ?_⟩
  intro K N B L hK hN hB hL
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < N := by linarith
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  let Q := K * N * B * L
  have hQ0 : 0 < Q := by dsimp only [Q]; positivity
  have hKNB : K * N * B ≤ Q := le_mul_of_one_le_right (by positivity) hL
  have hNL : N * L ≤ Q := by
    have hKB : 1 ≤ K * B := one_le_mul_of_one_le_of_one_le hK hB
    have hh := le_mul_of_one_le_left (by positivity : 0 ≤ N * L) hKB
    convert (preTransparency := .instances) hh using 1 ; dsimp only [Q] ; ring
  have hdouble (t : ℝ) : (N * (2 * L)) ^ t = (2 : ℝ) ^ t * (N * L) ^ t := by
    rw [show N * (2 * L) = 2 * (N * L) by ring, Real.mul_rpow (by norm_num) (by positivity)]
  have h23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one _
  have hshape : N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ) ≤
      2 * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
    rw [hdouble]
    have hh := mul_le_mul_of_nonneg_right h23 (Real.rpow_nonneg (by positivity : 0 ≤ N * L) (2 / 3 : ℝ))
    linarith
  have hcost : (K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2) ≤ Q ^ ε := by
    calc
      _ ≤ Q ^ (ε / 2) * Q ^ (ε / 2) := by
        exact mul_le_mul (Real.rpow_le_rpow (by positivity) hKNB (by positivity))
          (Real.rpow_le_rpow (by positivity) hNL (by positivity))
          (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hQ0.le _)
      _ = _ := by rw [← Real.rpow_add hQ0]; congr 1; ring
  have hh := hb N (2 * L) hN (by linarith)
  calc
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (N + 2 * L + (N * (2 * L)) ^ (2 / 3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by positivity) _)
    _ ≤ (K * N * B) ^ (ε / 2) *
        (C * (N * (2 * L)) ^ (ε / 2) * (2 * (N + L + (N * L) ^ (2 / 3 : ℝ)))) := by
      gcongr
    _ = (2 * C * (2 : ℝ) ^ (ε / 2)) *
        ((K * N * B) ^ (ε / 2) * (N * L) ^ (ε / 2)) * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
      rw [hdouble]
      ring
    _ ≤ _ := by gcongr

theorem hybridRow_energy_oai (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
    ∀ (rows nset bset Pset : Finset (Ideal Eis))
      (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ),
      (∀ k ∈ rows, Admissible k ∧ (Ideal.absNorm k : ℝ) ≤ K) →
      (∀ n ∈ nset, CubicSieve.Admissible n ∧ (Ideal.absNorm n : ℝ) ≤ N) →
      (∀ b ∈ bset, primaryGenerator b ≠ 0 ∧ (Ideal.absNorm b : ℝ) ≤ B) →
      (∀ P ∈ Pset, CubicSieve.Admissible P ∧ L ≤ (Ideal.absNorm P : ℝ) ∧
        (Ideal.absNorm P : ℝ) ≤ 2 * L) →
      (∀ P ∈ Pset, ‖a P‖ ≤ 1) → (∀ n ∈ nset, ∀ b ∈ bset, ‖beta n b‖ ≤ 1) →
      (∑ k ∈ rows, ‖hybridRow Pset nset bset a beta k‖ ^ 2) ≤
      C * (K * N * B * L) ^ ε * (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  obtain ⟨C0, hC0, he⟩ := hybridRow_energy_sieve_norm (ε / 2) (by positivity)
  obtain ⟨C1, hC1, hc⟩ := hybrid_sharp_cubic_factor ε hε
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro K N B L hK hN hB hL rows nset bset Pset a beta hrows hn hb hP ha hbeta
  apply (he K N B L hK hN hB rows nset bset Pset a beta hrows hn hb hP ha hbeta).trans
  have hh := mul_le_mul_of_nonneg_left (hc K N B L hK hN hB hL)
    (show 0 ≤ C0 * (K + N * B) * B by positivity)
  convert (preTransparency := .instances) hh using 1 <;> ring

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.InverseMoment.hybridRow_energy_oai := @OAI.SevenEighths.InverseMoment.hybridRow_energy_oai
