-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.actual_second_deleted_mode_branch_energy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T01:58:32.550724+00:00
-- url     : https://prove2.me/submissions/8ac04cf2-96a7-4fef-84d7-d12385937320

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.SecondPoissonScale
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

namespace ActualEisensteinCubic

theorem prime_product_moebius
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (hprime : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) :
    (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ) =
      (-1 : ℂ) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, UniqueFactorizationMonoid.moebius_one, Int.cast_one, Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
    have hcop : IsCoprime (P i) (∏ j ∈ S, P j) := by
      apply IsCoprime.prod_right
      intro j hj
      apply Ideal.isCoprime_of_isMaximal
      exact hinj.ne (by intro h; subst j; exact hi hj)
    rw [Finset.prod_insert hi, hcop.isRelPrime.moebius_mul,
      (hprime i).irreducible.moebius_eq, Int.cast_mul, Int.cast_neg,
      Int.cast_one, ih, Finset.card_insert_of_notMem hi, pow_succ]
    ring

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.IdealGenerators
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

namespace ActualEisensteinCubic

theorem primeSubsetGenerator_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (E : Finset ι) :
    primeSubsetGenerator P E ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  change (∏ i ∈ E, P i) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))

open ConcreteTraceCRT

open ConcreteTraceCRT EisensteinSchwartzPoisson

end ActualEisensteinCubic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.ActiveGaussFactorization
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

open scoped BigOperators Classical

namespace FiniteGaussPhase

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem norm_angularFactor (a : O) (ha : a ≠ 0) : ‖angularFactor a‖ = 1 := by
  rw [angularFactor, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha))

end FiniteGaussPhase

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.RayCharacters
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

namespace FirstCauchyArithmetic

section
open ActualEisensteinCubic CoprimeMobiusExtension

theorem supportMobius_sq {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hprime : ∀ i, Prime (P i)) (hinj : Function.Injective P) (S : Finset ι) :
    supportMobius P S * supportMobius P S = 1 := by
  rw [supportMobius, prime_product_moebius P hprime hinj, ← mul_pow]
  norm_num

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime_dvd_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    P i ∣ ∏ j ∈ S, P j ↔ i ∈ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hd⟩ := ((family_prime P i).dvd_finsetProd_iff P).mp h
    have he : P i = P j := associated_iff_eq.mp
      ((family_prime P i).associated_of_dvd (family_prime P j) hd)
    exact hinj he ▸ hj
  · exact fun hi => Finset.dvd_prod_of_mem P hi

theorem family_product_injective {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) : Function.Injective (fun S : Finset ι => ∏ i ∈ S, P i) := by
  intro S T h
  change (∏ i ∈ S, P i) = (∏ i ∈ T, P i) at h
  ext i
  rw [← family_prime_dvd_product_iff P hinj S i, h, family_prime_dvd_product_iff P hinj T i]

end FirstCauchyArithmetic

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
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.ReflectedKernel
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

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped BigOperators Classical

namespace DescentWeightedCauchy

theorem weighted_cauchy_sq {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ^ 2 ≤
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have hnorm : ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      ∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖ := by
    simpa only [norm_mul, norm_star] using
      norm_sum_le s (fun i => w i * U i * star (V i))
  calc
    _ ≤ (∑ i ∈ s, ‖w i‖ * ‖U i‖ * ‖V i‖) ^ 2 :=
      sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => by positivity)) |>.mpr hnorm
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i _ => by positivity) (fun i _ => by positivity)
      (fun i _ => by ring_nf; exact le_rfl)

theorem weighted_cauchy {ι : Type*} (s : Finset ι)
    (w U V : ι → ℂ) :
    ‖∑ i ∈ s, w i * U i * star (V i)‖ ≤
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by
  have h1 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have h2 : 0 ≤ ∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hs := weighted_cauchy_sq s w U V
  have he1 := Real.sq_sqrt h1
  have he2 := Real.sq_sqrt h2
  have hp : (Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      Real.sqrt (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2)) ^ 2 =
      (∑ i ∈ s, ‖w i‖ * ‖U i‖ ^ 2) *
      (∑ i ∈ s, ‖w i‖ * ‖V i‖ ^ 2) := by rw [mul_pow, he1, he2]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp (hp ▸ hs)

end DescentWeightedCauchy

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Arithmetic.SquarefreeDivisors
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    finiteSquarefreeRow P hg S (a ^ m) = finiteSquarefreeRow P hg S a ^ m := by
  simp only [finiteSquarefreeRow, map_pow, Finset.prod_pow]

theorem row_sixth (a : O) :
    finiteSquarefreeRow P hg S a ^ 6 = rowCoprimeMask P S a := by
  rw [← row_pow, finiteSquarefreeRow_sixth_power]
  rfl

include hg

theorem row_zero_of_mask_zero (a : O) (h : rowCoprimeMask P S a = 0) :
    finiteSquarefreeRow P hg S a = 0 := by
  have hq := row_sixth P hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

end Rows

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) + bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) : 0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega

section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

theorem cube_product_decomposition (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have h := multiplicity_decomposition (v j) (ε₁ j) (ε₂ j) (hv j hj)
  omega

theorem jLabel_eq_squarefree_mul_j2 (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases hp : parity (v j) <;> cases ε₁ j <;> cases ε₂ j <;>
    simp [bit, retained, evenDouble, hp]

theorem cube_pair_product_decomposition
    (p : κ → O) (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v₁ j + v₂ j) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      j2Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun j => v₁ j + v₂ j) := by
  rw [← cube_product_decomposition p B (fun j => v₁ j + v₂ j) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

end Reassembly

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Mellin.UniformKernelBounds
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
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open MixedCrossSeparation (crossSymbol quadraticCrossPhase columnPrimeCoprime)
open FiniteGaussPhase (canonicalProductGauss canonicalProductGauss_cross_factors)
open MixedGaussConversion (localGauss)

theorem canonicalProductGauss_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ S, e i ≠ 0) :
    canonicalProductGauss (fun i : S => p i.val) (fun i => hp i.val)
      (columnPrimeCoprime p hcop S) (fun i => hg i.val) (fun i => e i.val) =
      gaussBlock p hp hg S e := by
  let : DecidableEq S := fun a b => Classical.propDecidable (a = b)
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  have hin (i : S) :
      (∏ k ∈ (Finset.univ : Finset S).erase i,
        (canonicalSextic (Ideal.span {p i.val}) (hg i.val) ^ e i.val)
          (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) =
      ∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val := by
    apply Finset.prod_bij (fun k _ => k.val)
    · intro k hk
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h), k.property⟩
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro k hk
      refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h),
        Finset.mem_univ _⟩
    · intro k hk
      exact MulChar.pow_apply' _ (he i.val i.property) _
  calc
    _ = ∏ i : S, (∏ k ∈ S.erase i.val, crossSymbol p hg i.val k ^ e i.val) *
        localGauss (p i.val) (hp i.val) (hg i.val) (e i.val) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hin i]
      rfl
    _ = _ := Finset.prod_coe_sort S (fun i =>
      (∏ k ∈ S.erase i, crossSymbol p hg i k ^ e i) * localGauss (p i) (hp i) (hg i) (e i))

theorem columnCoefficient_eq_gaussBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) :
    MixedCrossSeparation.columnCoefficient p hp hcop hg S =
      star (FiniteGaussPhase.angularFactor (∏ i ∈ S, p i)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  unfold MixedCrossSeparation.columnCoefficient FiniteGaussPhase.canonicalProductCoefficient
  rw [Finset.prod_coe_sort]
  rw [canonicalProductGauss_eq_gaussBlock p hp hcop hg S (fun _ => 2) (fun _ _ => by decide)]

theorem gaussBlock_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← canonicalProductGauss_eq_gaussBlock p hp hcop hg S e he]
  exact FiniteGaussPhase.norm_canonicalProductGauss
    (fun i : S => p i.val) (fun i => hp i.val) (columnPrimeCoprime p hcop S)
    (fun i => hg i.val) (fun i => hc i.val) (fun i => e i.val)
    (fun i => he i.val i.property) (fun i => he6 i.val i.property)

end FirstPassCubeLabels

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.GaussSum.ReflectionBrackets
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

open scoped BigOperators Classical SchwartzMap
namespace ActualEisensteinCubic
open ConcreteTraceCRT ConcretePrimeRowBridge ActualEisensteinCoordinates EisensteinSchwartzPoisson

theorem primeSubsetGenerator_norm_sq {ι : Type*} (P : ι → Ideal O) (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 = (Ideal.absNorm (∏ i ∈ E, P i) : ℝ) := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ)) (span_idealGenerator _)

end ActualEisensteinCubic

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
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

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open MixedCrossSeparation (columnCoefficient columnG convertedColumnBlock quadraticCrossPhase
  columnPrimeCoprime )
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)

theorem columnCoefficient_norm_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    ‖columnCoefficient p hp hcop hg S‖ = 1 := by
  rw [FirstPassCubeLabels.columnCoefficient_eq_gaussBlock, norm_mul, norm_star,
    FiniteGaussPhase.norm_angularFactor _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)),
    FirstPassCubeLabels.gaussBlock_norm_one p hp hcop hg hc S (fun _ => 2)
      (fun _ _ => by decide) (fun _ _ => by decide), one_mul]

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Fourier.FrequencyTwists
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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open RayFourExpansion (RayCharacter gCoeff crossCoeff)

lemma secondRayMinus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayMinus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayMinus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

lemma secondRayPlus_norm_le (Ψ : O →* ℂ) (z : SecondRayIndex) (a : O) :
    ‖secondRayPlus Ψ z a‖ ≤ ‖Ψ a‖ := by
  simp only [secondRayPlus, MonoidHom.mul_apply, norm_mul, conjugateRayMonoid_apply, rayMonoid_apply, norm_star]
  calc
    _ ≤ 1 * (1 * ‖Ψ a‖) := by
      gcongr <;> exact FiniteRayExpansion.norm_char_le_one _ _
    _ = _ := by ring

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPreColumn_norm_le
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (m c d e k : O) (S : Finset ι) :
    ‖secondPreColumn p hp hcop hg Ψ m c d e k (fun _ => 1) S‖ ≤ ‖Ψ (∏ i ∈ S, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) S m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondPreColumn, norm_mul, norm_pow, norm_star, norm_one,
    columnCoefficient_norm_one p hp hcop hg hc S]
  calc
    _ ≤ 1 * ‖Ψ (∏ i ∈ S, p i)‖ * 1 * 1 ^ 4 * 1 * 1 * 1 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg S _
    _ = _ := by ring

theorem secondCommonWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O) (S : Finset ι) :
    ‖secondCommonWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k₁ k₂ S‖ ≤
      ‖Ψ₁ (∏ i ∈ S, p i)‖ * ‖Ψ₂ (∏ i ∈ S, p i)‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) S‖ = 1 := by
    have h := congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj S)
    simp only [norm_mul, norm_one] at h
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) S)]
  simp only [secondCommonWeight, norm_mul, norm_star, hmu, one_mul]
  exact mul_le_mul (secondPreColumn_norm_le p hp hcop hg hc Ψ₁ _ _ _ _ _ S)
    (secondPreColumn_norm_le p hp hcop hg hc Ψ₂ _ _ _ _ _ S) (norm_nonneg _) (norm_nonneg _)

end

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ChildTransfer
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
include hg

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] hg in
theorem secondMaskQuotient_spec (E G : Finset ι) (hEG : E ⊆ G) :
    (∏ i ∈ G, p i) = primeSubsetGenerator (fun i => Ideal.span {p i}) E *
      secondMaskQuotient p E G hEG :=
  Classical.choose_spec (poisson_mask_generator_dvd p E G hEG)

end

open ActualEisensteinCubic

theorem secondMaskQuotient_span {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (E G : Finset ι) (hEG : E ⊆ G) :
    Ideal.span {secondMaskQuotient p E G hEG} =
      ∏ i ∈ G \ E, Ideal.span {p i} := by
  have hE : (∏ i ∈ E, Ideal.span {p i}) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have he : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E} =
      ∏ i ∈ E, Ideal.span {p i} := by
    rw [primeSubsetGenerator, ConcretePrimeRowBridge.span_idealGenerator]
  apply mul_left_cancel₀ hE
  calc
    _ = Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) E *
        secondMaskQuotient p E G hEG} := by rw [← he, Ideal.span_singleton_mul_span_singleton]
    _ = Ideal.span {∏ i ∈ G, p i} := by rw [← secondMaskQuotient_spec]
    _ = ∏ i ∈ G, Ideal.span {p i} := FiniteGaussPhase.span_finset_prod G p
    _ = _ := by simpa only [mul_comm] using
      (Finset.prod_sdiff (f := fun i => Ideal.span {p i}) hEG).symm

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open FirstPassCubeLabels (cubeCoreCoefficient cubeOddSupport coreRayCoefficient coreRayTwist
  coreRayCharacter dilatedCoreRow dilatedRayColumn afterDilationLabel b0Label jLabel)
open FirstCauchyArithmetic (supportMobius supportRay supportConjugateSum)
open RayFourExpansion (RayCharacter)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyBlocks
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

open scoped BigOperators Classical

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct cubeRadical aLabel jLabel j2Label squarefreeLabel b0Label
  bit retained parity b0Exponent)

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

end

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ConjugateProfiles
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

open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform

open scoped BigOperators Classical
namespace SecondPassArithmetic

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] in
theorem secondInputCoefficient_norm_le (Ψ : O →* ℂ) (m c d : O) (G : Finset ι) :
    ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) G‖ ≤ ‖Ψ (∏ i ∈ G, p i)‖ := by
  have hm : ‖rowCoprimeMask (fun i => Ideal.span {p i}) G m‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [secondInputCoefficient, norm_mul, norm_pow,  mul_one]
  calc
    _ ≤ ‖Ψ (∏ i ∈ G, p i)‖ * 1 * 1 ^ 4 * 1 := by
      gcongr <;> first | exact hm | exact finiteSquarefreeRow_norm_le_one _ hg G _
    _ = _ := by ring

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FrequencyCutoffs
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm )
open ConcreteTraceCRT (eisEmbedding)

theorem mem_secondFrequencyCutoff (scale H : ℝ) (k : O)
    (hk : ‖eisEmbedding k‖^2 ≤ H/scale) : k ∈ secondFrequencyCutoff scale H := by
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hk
  exact_mod_cast hk.trans (Nat.le_ceil (H/scale))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (columnLog jLabel b0Label )
open JointLogSeparation (tripleCoefficient)

end SecondPassArithmetic

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalDifference
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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeProductNorm_eq_ideal_norm (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    FiniteGaussPhase.span_finset_prod]

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.SupportNorms
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
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)
open FirstPassCubeLabels (columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem primeSubsetGenerator_norm_eq_productNorm (E : Finset ι) :
    ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖ ^ 2 = primeProductNorm p E := by
  rw [primeSubsetGenerator_norm_sq, primeProductNorm_eq_ideal_norm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SeedDefects
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

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.GlobalEncoding
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
namespace SecondPassArithmetic
open ActualEisensteinCubic

section
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj

theorem primeIdealProduct_emultiplicity (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [if_pos hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))

theorem primeIdealProduct_exponents_eq
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : (∏ i ∈ B, P i ^ v i) = ∏ i ∈ C, P i ^ w i) : v = w := by
  funext i
  have he := congrArg (fun I => emultiplicity (P i) I) heq
  rw [primeIdealProduct_emultiplicity P hinj,primeIdealProduct_emultiplicity P hinj] at he
  have hB : (if i ∈ B then (v i : ℕ∞) else 0) = (v i : ℕ∞) := by
    by_cases h : i ∈ B <;> simp [h,hv i]
  have hC : (if i ∈ C then (w i : ℕ∞) else 0) = (w i : ℕ∞) := by
    by_cases h : i ∈ C <;> simp [h,hw i]
  rw [hB,hC] at he
  exact_mod_cast he

end

theorem primeProduct_span_exponents_eq {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (B C : Finset ι) (v w : ι → ℕ)
    (hv : ∀ i, i ∉ B → v i = 0) (hw : ∀ i, i ∉ C → w i = 0)
    (heq : Ideal.span {FirstPassCubeLabels.primeProduct p B v} =
      Ideal.span {FirstPassCubeLabels.primeProduct p C w}) : v = w := by
  apply primeIdealProduct_exponents_eq (fun i => Ideal.span {p i}) hinj B C v w hv hw
  simpa only [FirstPassCubeLabels.primeProduct,FiniteGaussPhase.span_finset_prod,
    ←Ideal.span_singleton_pow] using heq

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel b0Label jLabel cubeActiveSupport primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

namespace CubeCoordinates
variable {ι : Type*} [DecidableEq ι]

theorem support_pos (x : CubeCoordinates ι) (i : ι) (hi : i ∈ x.support) :
    0 < x.leftExponent i+x.rightExponent i := by
  simp only [support,Finset.mem_union,Finsupp.mem_support_iff] at hi
  omega

theorem left_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.leftExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv))

theorem right_off (x : CubeCoordinates ι) (i : ι) (hi : i ∉ x.support) :
    x.rightExponent i=0 := by
  by_contra hv
  exact hi (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv))

theorem aLabel_left (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.leftBit = ∏ i ∈ x.leftDivisor,p i := by
  simp only [aLabel,primeProduct,leftBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.leftDivisor)=x.leftDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.1 hi)
  rw [he]

theorem aLabel_right (p : ι → O) (x : CubeCoordinates ι) (hx : x.Admissible) :
    aLabel p x.support x.rightBit = ∏ i ∈ x.rightDivisor,p i := by
  simp only [aLabel,primeProduct,rightBit,FirstPassCubeLabels.bit,decide_eq_true_eq]
  simp_rw [apply_ite, pow_one, pow_zero]
  rw [← Finset.prod_filter]
  have he : x.support.filter (fun i => i ∈ x.rightDivisor)=x.rightDivisor := by
    ext i
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hi => hx.2 hi)
  rw [he]

end CubeCoordinates

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct aLabel)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.PrincipalNormalization
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
namespace SecondPassArithmetic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel cubeRadical)
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem secondChildColumn_zero_of_mask_label_mem (Ψ : O →* ℂ) (m f y : O)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hmf : m*f ∈ Ideal.span {p i}) :
    secondChildColumn p hp hcop hg Ψ m f y H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hmf with hm|hf
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondChildColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S f=0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i∈S,f ∈ Ideal.span {p i} from ⟨i,hi,hf⟩)]
    have hr := FirstPassCubeLabels.row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S f hz
    simp only [secondChildColumn,hr,zero_pow (by decide : (4 : ℕ) ≠ 0),mul_zero,zero_mul]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Marks
namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeSlot_residual_list (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq σ] in
theorem primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothTests
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

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct aLabel squarefreeLabel b0Label j2Label cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

variable (hp : ∀ i,p i≠0)
include hp

variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem cubeDivisorKey_injective_on_product {x y : CubeCoordinates ι}
    (hx : x.Admissible) (hy : y.Admissible)
    (hprod : cubeProductIdeal p x=cubeProductIdeal p y)
    (hk : cubeDivisorKey p x=cubeDivisorKey p y) : x=y := by
  have h1 := congrFun hk 0
  have hA1 := congrFun hk 1
  have hA2 := congrFun hk 2
  change Ideal.span {primeProduct p x.support x.leftExponent}=
    Ideal.span {primeProduct p y.support y.leftExponent} at h1
  have h2 : Ideal.span {primeProduct p x.support x.rightExponent}=
    Ideal.span {primeProduct p y.support y.rightExponent} := by
    apply mul_left_cancel₀ ((Ideal.span_singleton_eq_bot.not).mpr (primeProduct_ne_zero p hp x.support x.leftExponent))
    simpa only [cubeProductIdeal,h1] using hprod
  have hv1 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.leftExponent y.leftExponent x.left_off y.left_off h1
  have hv2 := primeProduct_span_exponents_eq p hinj x.support y.support
    x.rightExponent y.rightExponent x.right_off y.right_off h2
  change Ideal.span {aLabel p x.support x.leftBit}=Ideal.span {aLabel p y.support y.leftBit} at hA1
  change Ideal.span {aLabel p x.support x.rightBit}=Ideal.span {aLabel p y.support y.rightBit} at hA2
  rw [CubeCoordinates.aLabel_left p x hx,CubeCoordinates.aLabel_left p y hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA1
  rw [CubeCoordinates.aLabel_right p x hx,CubeCoordinates.aLabel_right p y hy,
    FiniteGaussPhase.span_finset_prod,FiniteGaussPhase.span_finset_prod] at hA2
  exact CubeCoordinates.ext (Finsupp.ext (congrFun hv1)) (Finsupp.ext (congrFun hv2))
    (FirstCauchyArithmetic.family_product_injective _ hinj hA1)
    (FirstCauchyArithmetic.family_product_injective _ hinj hA2)

end SecondPassArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.Canonical
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_restore_lists
    (pool B : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hB : ∀ i ∈ B, m * f ∈ Ideal.span {p i}) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots (fun i => lists i \ B) a W X =
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a W X := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_congr rfl
  intro U hU
  by_cases hd : Disjoint B U
  · have he : U \ B = U := Finset.sdiff_eq_self_of_disjoint hd.symm
    simp only [secondChildColumn, ← primeMark_residual_lists, he]
  · obtain ⟨i, hiB, hiU⟩ := Finset.not_disjoint_iff.mp hd
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB),
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k _ U i hiU (hB i hiB)]

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

theorem fiber_energy_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D E : κ → ℝ) (hp : ∀ i ∈ s, p i ∈ t)
    (hE : ∀ j ∈ t, 0 ≤ E j)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ∑ i ∈ s, w i * E (p i) ≤ ∑ j ∈ t, D j * E j := by
  calc
    ∑ i ∈ s, w i * E (p i) =
        ∑ j ∈ t, ∑ i ∈ s with p i = j, w i * E (p i) :=
      (Finset.sum_fiberwise_of_maps_to hp _).symm
    _ = ∑ j ∈ t, (∑ i ∈ s with p i = j, w i) * E j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ t, D j * E j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD j hj) (hE j hj)

end

end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialFibers
namespace OAI

namespace SevenEighths.InverseInitialFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical
noncomputable section

lemma divisor_ne_zero {J : ℕ} {x : InitialTuple J} {t f : Ideal O} {k : O}
    (hx : Valid x t f k) (hf : f ≠ 0) : x.divisor ≠ 0 := by
  intro hz
  have he := hx.label_eq
  rw [hz, zero_mul] at he
  exact hf he.symm

theorem valid_key_injective {J : ℕ} (t f : Ideal O) (k : O) (hf : f ≠ 0)
    {x y : InitialTuple J} (hx : Valid x t f k) (hy : Valid y t f k)
    (hd : x.divisor = y.divisor) (ha : x.assigned = y.assigned) : x = y := by
  have hd0 := divisor_ne_zero hx hf
  have hc : x.common = y.common := by rw [← hx.common_eq, ← hy.common_eq, hd]
  have hs : x.residual = y.residual := by
    apply mul_left_cancel₀ hd0
    exact hx.label_eq.trans (by simpa only [hd] using hy.label_eq.symm)
  have hg : primaryGenerator x.divisor ≠ 0 := hx.divisor_good
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ hg
    exact hx.row_eq.trans (by simpa only [hd] using hy.row_eq.symm)
  exact InitialTuple.ext hc hd hs hr ha

lemma divisors_mul_image (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    idealDivisors (I*J) =
      ((idealDivisors I) ×ˢ (idealDivisors J)).image (fun p => p.1*p.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hI hJ), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨A, B, hA, hB, hab⟩ := exists_dvd_and_dvd_of_dvd_mul hD
    exact ⟨(A,B), Finset.mem_product.mpr
      ⟨(mem_idealDivisors hI).mpr hA, (mem_idealDivisors hJ).mpr hB⟩, hab.symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hI).mp (Finset.mem_product.mp hp).1)
      ((mem_idealDivisors hJ).mp (Finset.mem_product.mp hp).2)

lemma divisor_card_mul_le (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0) :
    (idealDivisors (I*J)).card ≤ (idealDivisors I).card * (idealDivisors J).card := by
  rw [divisors_mul_image I J hI hJ, ← Finset.card_product]
  exact Finset.card_image_le

theorem valid_tuple_card_le {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card * (idealDivisors (t*f)).card^J := by
  let D := idealDivisors f
  let E := idealDivisors (t*f)
  let encode (x : T) : D × (Fin J → E) :=
    (⟨x.val.divisor, (mem_idealDivisors hf).mpr (divisor_dvd (hT x.val x.property))⟩,
      fun i => ⟨(x.val.assigned i).val,
        (mem_idealDivisors (mul_ne_zero ht hf)).mpr ((hT x.val x.property).assigned_dvd i)⟩)
  have hi : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    apply valid_key_injective t f k hf (hT x.val x.property) (hT y.val y.property)
    · exact congrArg Subtype.val (congrArg Prod.fst hxy)
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : E => z.val) (congrFun (congrArg Prod.snd hxy) i)
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, D, E] using Fintype.card_le_of_injective encode hi

theorem valid_tuple_card_le_separated {J : ℕ} (T : Finset (InitialTuple J))
    (t f : Ideal O) (k : O) (ht : t ≠ 0) (hf : f ≠ 0)
    (hT : ∀ x ∈ T, Valid x t f k) :
    T.card ≤ (idealDivisors f).card^(J+1) * (idealDivisors t).card^J := by
  apply (valid_tuple_card_le T t f k ht hf hT).trans
  calc
    _ ≤ (idealDivisors f).card *
        ((idealDivisors t).card * (idealDivisors f).card)^J :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (divisor_card_mul_le t f ht hf) J)
    _ = _ := by rw [mul_pow, pow_succ]; ring

lemma divisor_card_pos (I : Ideal O) (hI : I ≠ 0) : 1 ≤ (idealDivisors I).card := by
  apply Finset.one_le_card.mpr
  exact ⟨1, (mem_idealDivisors hI).mpr (one_dvd I)⟩

end
end SevenEighths.InverseInitialFibers

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.SecondFibers
namespace OAI

namespace SevenEighths.InverseSecondFibers

open ActualEisensteinCubic
open CompletedGauss (primaryGenerator primaryGenerator_mul)
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open InverseInitialFibers (divisor_card_mul_le divisor_card_pos)
open scoped BigOperators Classical
noncomputable section

lemma core_dvd_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 4) :
    x.core ⟨i.val, by omega⟩ ∣ f := by
  have hJ : x.core 0 ∣ f := by
    rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  fin_cases i
  · exact hJ
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  · rw [← hx.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · exact (show x.core 3 ∣ x.core 0 from ⟨x.cubeResidual, hx.j_split.symm⟩).trans hJ

lemma common_label_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 1 * x.core 0 ∣ f := by
  refine ⟨x.core 2 * x.commonResidual, ?_⟩
  rw [← hx.label]
  ring

lemma cube_product_dvd_square {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 * x.secondCube ∣ (γ.q0 * x.core 0)^2 := by
  refine ⟨x.core 3, ?_⟩
  rw [hx.b_split, ← hx.j_split]
  ring

lemma cube_radical_dvd {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    (x.core 4 * x.secondCube).radical ∣ γ.q0 * x.core 0 := by
  apply Ideal.dvd_iff_le.mpr
  have hle := Ideal.radical_mono (Ideal.dvd_iff_le.mp (cube_product_dvd_square hx))
  rw [Ideal.radical_pow (γ.q0 * x.core 0) (by decide : (2 : ℕ) ≠ 0)] at hle
  exact Ideal.le_radical.trans hle

lemma cube_factor_dvd_target {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) :
    x.core 4 ∣ (γ.q0 * f)^2 :=
  (dvd_mul_right _ _).trans ((cube_product_dvd_square hx).trans
    (pow_dvd_pow_of_dvd (mul_dvd_mul_left _ (core_dvd_label hx 0)) 2))

lemma core_dvd_outer_label {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k) (i : Fin 3) :
    x.core ⟨i.val+5, by omega⟩ ∣ γ.q0 * f := by
  have hrad : (x.core 4 * x.secondCube).radical ∣ γ.q0 * f :=
    (cube_radical_dvd hx).trans (mul_dvd_mul_left _ (core_dvd_label hx 0))
  fin_cases i
  · exact hx.a1.trans hrad
  · exact hx.a2.trans hrad
  · apply hx.d.trans
    apply (mul_dvd_mul_left (x.core 1) (cube_radical_dvd hx)).trans
    convert (preTransparency := .instances) mul_dvd_mul_left γ.q0 (common_label_dvd hx) using 1
    ring

lemma core_ne_zero {Jo Jn : ℕ} {x : SecondTuple Jo Jn}
    {γ : OuterTriple} {f : Ideal O} {k : O} (hx : Valid x γ f k)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (i : Fin 8) : x.core i ≠ 0 := by
  have hd : x.core i ∣ (γ.q0*f)^2 := by
    by_cases hi : i.val < 4
    · exact (core_dvd_label hx ⟨i.val, hi⟩).trans
        ((dvd_mul_left _ _).trans (dvd_pow_self _ (by decide : 2 ≠ 0)))
    · by_cases hi4 : i.val = 4
      · have he : i = 4 := Fin.ext hi4
        simpa only [he] using cube_factor_dvd_target hx
      · have he : (⟨(i.val-5)+5, by omega⟩ : Fin 8) = i := by
          apply Fin.ext
          dsimp
          omega
        exact (he ▸ core_dvd_outer_label hx ⟨i.val-5, by omega⟩).trans
          (dvd_pow_self _ (by decide : 2 ≠ 0))
  intro hz
  rw [hz, zero_dvd_iff] at hd
  exact (pow_ne_zero 2 (mul_ne_zero hq hf)) hd

theorem valid_key_injective {Jo Jn : ℕ} (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) {x y : SecondTuple Jo Jn}
    (hx : Valid x γ f k) (hy : Valid y γ f k)
    (hc : x.core = y.core) (ho : x.oldAssigned = y.oldAssigned)
    (hn : x.newAssigned = y.newAssigned) : x = y := by
  have hcore (i : Fin 8) : x.core i = y.core i := congrFun hc i
  have hv : x.commonResidual = y.commonResidual := by
    apply mul_left_cancel₀ (mul_ne_zero
      (mul_ne_zero (core_ne_zero hx hf hq 0) (core_ne_zero hx hf hq 1))
      (core_ne_zero hx hf hq 2))
    exact hx.label.trans (by simpa only [hcore] using hy.label.symm)
  have hj : x.cubeResidual = y.cubeResidual := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 3)
    exact hx.j_split.trans (by simpa only [hcore] using hy.j_split.symm)
  have hb : x.secondCube = y.secondCube := by
    apply mul_left_cancel₀ (core_ne_zero hx hf hq 4)
    exact hx.b_split.trans (by simpa only [hcore, hj] using hy.b_split.symm)
  have hg : x.extractedCommon = y.extractedCommon := by
    rw [← hx.extracted_eq, ← hy.extracted_eq, hcore]
  have hr : x.frequency = y.frequency := by
    apply mul_left_cancel₀ (mul_ne_zero hx.generator_d hx.generator_d2)
    exact hx.row_eq.trans (by simpa only [hcore] using hy.row_eq.symm)
  exact SecondTuple.ext (hx.outer_eq.trans hy.outer_eq.symm) hc hv hj hb hg hr ho hn

theorem valid_tuple_card_le {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^4 * (idealDivisors ((γ.q0*f)^2)).card *
      (idealDivisors (γ.q0*f)).card^3 *
      (idealDivisors (γ.q0*f*γ.quotient)).card^Jo *
      (idealDivisors (f*γ.residual)).card^Jn := by
  let D := idealDivisors f
  let E := idealDivisors ((γ.q0*f)^2)
  let F := idealDivisors (γ.q0*f)
  let A := idealDivisors (γ.q0*f*γ.quotient)
  let B := idealDivisors (f*γ.residual)
  let Target := (Fin 4 → D) × E × (Fin 3 → F) × (Fin Jo → A) × (Fin Jn → B)
  let encode (x : T) : Target :=
    (fun i => ⟨x.val.core ⟨i.val, by omega⟩,
      (mem_idealDivisors hf).mpr (core_dvd_label (hT x.val x.property) i)⟩,
    ⟨x.val.core 4, (mem_idealDivisors (pow_ne_zero 2 (mul_ne_zero hq hf))).mpr
      (cube_factor_dvd_target (hT x.val x.property))⟩,
    (fun i => ⟨x.val.core ⟨i.val+5, by omega⟩,
      (mem_idealDivisors (mul_ne_zero hq hf)).mpr (core_dvd_outer_label (hT x.val x.property) i)⟩),
    (fun i => ⟨(x.val.oldAssigned i).val,
      (mem_idealDivisors (mul_ne_zero (mul_ne_zero hq hf) ht)).mpr
        ((hT x.val x.property).old_dvd i)⟩),
    (fun i => ⟨(x.val.newAssigned i).val,
      (mem_idealDivisors (mul_ne_zero hf hr)).mpr ((hT x.val x.property).new_dvd i)⟩))
  have hi : Function.Injective encode := by
    intro x y he
    apply Subtype.ext
    apply valid_key_injective γ f k hf hq (hT x.val x.property) (hT y.val y.property)
    · funext i
      fin_cases i
      · exact congrArg (fun z : Target => (z.1 0).val) he
      · exact congrArg (fun z : Target => (z.1 1).val) he
      · exact congrArg (fun z : Target => (z.1 2).val) he
      · exact congrArg (fun z : Target => (z.1 3).val) he
      · exact congrArg (fun z : Target => z.2.1.val) he
      · exact congrArg (fun z : Target => (z.2.2.1 0).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 1).val) he
      · exact congrArg (fun z : Target => (z.2.2.1 2).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.1 i).val) he
    · funext i
      apply Subtype.ext
      exact congrArg (fun z : Target => (z.2.2.2.2 i).val) he
  simpa only [Target, D, E, F, A, B, Fintype.card_coe, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin, Nat.mul_assoc] using Fintype.card_le_of_injective encode hi

lemma divisor_card_sq_le (I : Ideal O) (hI : I ≠ 0) :
    (idealDivisors (I ^2)).card ≤ (idealDivisors I).card^2 := by
  simpa only [pow_two] using divisor_card_mul_le I I hI hI

theorem valid_tuple_card_le_separated {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) :
    T.card ≤ (idealDivisors f).card^(9+Jo+Jn) * (idealDivisors γ.q0).card^(5+Jo) *
      (idealDivisors γ.quotient).card^Jo * (idealDivisors γ.residual).card^Jn := by
  let df := (idealDivisors f).card
  let dq := (idealDivisors γ.q0).card
  let dt := (idealDivisors γ.quotient).card
  let dr := (idealDivisors γ.residual).card
  have hqf : (idealDivisors (γ.q0*f)).card ≤ dq*df := divisor_card_mul_le _ _ hq hf
  have hsq : (idealDivisors ((γ.q0*f)^2)).card ≤ (dq*df)^2 :=
    (divisor_card_sq_le _ (mul_ne_zero hq hf)).trans (Nat.pow_le_pow_left hqf 2)
  have hold : (idealDivisors (γ.q0*f*γ.quotient)).card ≤ dq*df*dt :=
    (divisor_card_mul_le _ _ (mul_ne_zero hq hf) ht).trans (Nat.mul_le_mul_right _ hqf)
  have hnew : (idealDivisors (f*γ.residual)).card ≤ df*dr := divisor_card_mul_le _ _ hf hr
  apply (valid_tuple_card_le T γ f k hf hq ht hr hT).trans
  calc
    _ ≤ df^4 * (dq*df)^2 * (dq*df)^3 * (dq*df*dt)^Jo * (df*dr)^Jn := by
      gcongr
    _ = _ := by
      dsimp [df, dq, dt, dr]
      simp only [mul_pow, pow_add]
      ring

theorem valid_tuple_card_le_slot_cap {Jo Jn : ℕ} (T : Finset (SecondTuple Jo Jn))
    (γ : OuterTriple) (f : Ideal O) (k : O)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (hT : ∀ x ∈ T, Valid x γ f k) (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    T.card ≤ (idealDivisors f).card^(9+4*K) * (idealDivisors γ.q0).card^(5+2*K) *
      (idealDivisors γ.quotient).card^(2*K) * (idealDivisors γ.residual).card^(2*K) := by
  apply (valid_tuple_card_le_separated T γ f k hf hq ht hr hT).trans
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (pow_le_pow_right₀ (divisor_card_pos f hf) (by omega))
    (pow_le_pow_right₀ (divisor_card_pos γ.q0 hq) (by omega)))
    (pow_le_pow_right₀ (divisor_card_pos γ.quotient ht) ho))
    (pow_le_pow_right₀ (divisor_card_pos γ.residual hr) hn)

end
end SevenEighths.InverseSecondFibers

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.TripleMass
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma tripleDivisorWeight_nonneg (K : ℕ) (γ : OuterTriple) :
    0 ≤ tripleDivisorWeight K γ := by unfold tripleDivisorWeight; positivity

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCauchy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondOuterPhase_norm (h y : Fin 6 → ℝ) : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,logPhase_norm,mul_one]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondGenerator
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma secondUnitFrequency_injective (u v : Eisˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (Units.ne_zero (u^4*v)) hab

lemma secondUnitFrequency_norm (u v : Eisˣ) (k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding k‖ :=
  GaussGeneratorTransport.norm_eisEmbedding_unit_mul (u^4*v) k

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryGenerator L ∧
      d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Inversion.InitialArithmetic
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open MixedCrossSeparation (columnCoefficient)
open SevenEighths.InverseMoment SevenEighths.InverseInitialFibers
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i≠0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, λ₀∉Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_ne_zero (S : Finset ι) : sourceIdeal p S≠0 :=
  Ideal.span_singleton_eq_bot.not.mpr (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_union (S T : Finset ι) (hst : Disjoint S T) :
    sourceIdeal p (S∪T)=sourceIdeal p S*sourceIdeal p T := by
  simp only [sourceIdeal,Finset.prod_union hst,Ideal.span_singleton_mul_span_singleton]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_dvd (E G : Finset ι) (hEG : E⊆G) : sourceIdeal p E∣sourceIdeal p G := by
  refine ⟨sourceIdeal p (G\E),?_⟩
  rw [←sourceIdeal_union p E (G\E) (by exact Finset.disjoint_left.mpr (fun i hi hj=>(Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hEG]

omit [DecidableEq ι] in
theorem source_prime_dvd (S : Finset ι) (i : ι) (hi : i∈S) :
    (sourcePrime p i).val∣sourceIdeal p S := by
  apply Ideal.dvd_iff_le.mpr
  apply Ideal.span_singleton_le_span_singleton.mpr
  exact Finset.dvd_prod_of_mem p hi

theorem sourceIdeal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (sourceIdeal p) := by
  intro S T he
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod] at he
  exact FirstCauchyArithmetic.family_product_injective _ hinj he

end SevenEighths.InverseInitialArithmetic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSourceTuples
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

theorem originalSecondTuple_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) (hx : SecondOriginalValid x) :
    Valid (originalSecondTuple p u v x)
      (secondChild (originalSecondTuple p u v x)).1
      (secondChild (originalSecondTuple p u v x)).2.1
      (secondChild (originalSecondTuple p u v x)).2.2 := by
  have hproduct : sourceIdeal p x.divisor * sourceIdeal p (x.common \ x.divisor) =
      sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common \ x.divisor)
      (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
      Finset.union_sdiff_of_subset hx.second_subset]
  refine ⟨rfl,rfl,hx.j_split,hx.b_split,hx.a1,hx.a2,hx.first_divisor,?_,hx.first_generator,?_,rfl,?_,?_⟩
  · exact hproduct
  · change primaryGenerator (sourceIdeal p x.divisor) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · intro i
    apply (hx.old_support i).trans
    change x.q0*x.J*x.C*x.quotient ∣
      x.q0*(x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*x.quotient
    refine ⟨sourceIdeal p x.divisor*sourceIdeal p x.overlap,?_⟩
    ring
  · intro i
    change (sourcePrime p (x.newAssigned i)).val ∣
      (x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*sourceIdeal p (x.common \ x.divisor)
    have hslot : (sourcePrime p (x.newAssigned i)).val ∣
        sourceIdeal p x.common*sourceIdeal p x.overlap := by
      rcases Finset.mem_union.mp (hx.new_support i) with hi|hi
      · exact dvd_mul_of_dvd_left (source_prime_dvd p x.common _ hi) _
      · exact dvd_mul_of_dvd_right (source_prime_dvd p x.overlap _ hi) _
    apply hslot.trans
    refine ⟨x.J*x.C,?_⟩
    rw [←hproduct]
    ring

theorem originalSecondTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) :
    Function.Injective (originalSecondTuple (Jo:=Jo) (Jn:=Jn) p u v) := by
  intro x y hxy
  have hi := sourceIdeal_injective p hinj
  have hcore (i : Fin 8) := congrArg (fun z : SecondTuple Jo Jn => z.core i) hxy
  apply SecondOriginalSource.ext
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.q0) hxy
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.quotient) hxy
  · exact hcore 0
  · exact hcore 1
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hcore 7
  · exact congrArg SecondTuple.cubeResidual hxy
  · exact congrArg SecondTuple.secondCube hxy
  · exact hi (congrArg SecondTuple.extractedCommon hxy)
  · exact hi (hcore 2)
  · exact hi (congrArg SecondTuple.commonResidual hxy)
  · exact secondUnitFrequency_injective u v (congrArg SecondTuple.frequency hxy)
  · exact congrArg SecondTuple.oldAssigned hxy
  · funext i
    apply hinj
    exact congrArg (fun z : SecondTuple Jo Jn => (z.newAssigned i).val) hxy

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.CubeSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

lemma sourceIdeal_isRadical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (S : Finset ι) :
    (sourceIdeal p S).IsRadical := by
  change (Ideal.span {∏ i ∈ S,p i}).IsRadical
  rw [FiniteGaussPhase.span_finset_prod]
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _ _ => by simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Ideal.mul_eq_inf_of_isCoprime]
    · exact (inferInstance : (Ideal.span {p a}).IsPrime).isRadical.inf ih
    · apply IsCoprime.prod_right
      intro b hb
      exact hcop (fun he => ha (he.symm ▸ hb))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

theorem cubeSupport_dvd_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p B ∣
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  apply Ideal.dvd_iff_le.mpr
  apply (sourceIdeal_isRadical p hcop B).radical_le_iff.mpr
  apply Ideal.dvd_iff_le.mp
  rw [Ideal.span_singleton_mul_span_singleton,←primeProduct_add]
  exact cubeRadical_span_dvd_product p B _ hv

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_cubeSupport (B : Finset ι) (ε : ι → Bool) :
    Ideal.span {aLabel p B ε} ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  unfold aLabel primeProduct
  change (∏ i ∈ B,p i^bit (ε i)) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases hh : ε i <;> simp [bit]

theorem firstMask_dvd_cube_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B C D : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p D ∣ sourceIdeal p C *
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  have hd := InverseInitialArithmetic.sourceIdeal_dvd p D (C∪B) hD
  rw [sourceIdeal_union p C B hCB] at hd
  exact hd.trans (mul_dvd_mul_left _ (cubeSupport_dvd_radical p hcop B v₁ v₂ hv))

theorem cubeSecondSource_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣
      Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} *
      Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂} * sourceIdeal p C * t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) := by
  constructor
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} = _
    rw [Ideal.span_singleton_mul_span_singleton,←jLabel_eq_squarefree_mul_j2]
    rfl
  · have hb := congrArg (fun a : Eis => (Ideal.span {a} : Ideal Eis))
      (cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv)
    simpa only [cubeSecondSource,pow_two,←Ideal.span_singleton_mul_span_singleton] using hb
  · exact (aLabel_dvd_cubeSupport p B ε₁).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact (aLabel_dvd_cubeSupport p B ε₂).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact firstMask_dvd_cube_radical p hcop B C D hCB hD v₁ v₂ hv
  · change primaryGenerator (sourceIdeal p D) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · exact hE
  · exact hold
  · exact hnew

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem oldSlot_dvd_reconstructed_support
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (P t : Ideal Eis)
    (hP : P ∣ sourceIdeal p B*sourceIdeal p C*t) :
    P ∣ Ideal.span {b0Label p B v ε₁ ε₂}*
      Ideal.span {jLabel p B v ε₁ ε₂}*sourceIdeal p C*t := by
  have hb := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv)
  change sourceIdeal p B ∣ Ideal.span {jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂} at hb
  rw [←Ideal.span_singleton_mul_span_singleton,mul_comm (Ideal.span {jLabel p B v ε₁ ε₂})] at hb
  exact hP.trans (mul_dvd_mul_right (mul_dvd_mul_right hb _) _)

theorem cubeSecondSource_valid_original_slots (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣ sourceIdeal p B*sourceIdeal p C*t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) :=
  cubeSecondSource_valid p hp hpr hcop B C D G E V hCB hD hE v₁ v₂ ε₁ ε₂ hv t k
    oldAssigned newAssigned
    (fun i => oldSlot_dvd_reconstructed_support p B C _ ε₁ ε₂ hv _ t (hold i)) hnew

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSourceEncoding
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_injective)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

theorem markedSecondOriginal_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} :
    Set.InjOn (markedSecondOriginal (Jo:=Jo) (Jn:=Jn) p) {x | x.cube.Admissible} := by
  intro x hx y hy hxy
  have hc : x.cube = y.cube := by
    apply cubeDivisorKey_injective_on_product p hp hinj hx hy
    · simpa only [markedSecondOriginal,cubeSecondSource,cubeProductIdeal] using
        congrArg (fun z : SecondOriginalSource ι Jo Jn => z.b1*z.b2) hxy
    · funext i
      fin_cases i
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.b1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A2 hxy
  apply MarkedSecondSource.ext hc
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.C hxy)
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.dK hxy)
  · apply SecondExpansionData.ext
    · exact congrArg SecondOriginalSource.common hxy
    · exact congrArg SecondOriginalSource.divisor hxy
    · exact congrArg SecondOriginalSource.overlap hxy
    · exact congrArg SecondOriginalSource.frequency hxy
  · exact congrArg SecondOriginalSource.quotient hxy
  · exact congrArg SecondOriginalSource.oldAssigned hxy
  · exact congrArg SecondOriginalSource.newAssigned hxy

theorem markedSecondTuple_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : Eisˣ) :
    Set.InjOn (fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x))
      {x | x.cube.Admissible} := by
  intro x hx y hy he
  exact markedSecondOriginal_injOn p hp hinj hx hy
    (originalSecondTuple_injective p hinj u v he)

theorem markedSecondOriginal_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap) :
    SecondOriginalValid (markedSecondOriginal p x) :=
  cubeSecondSource_valid_original_slots p hp hpr hcop x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap hCB hD hE
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.cube.support_pos
    x.quotient x.second.frequency x.oldAssigned x.newAssigned hold hnew

theorem actual_marked_second_source_fiber (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (ha : ∀ x ∈ source, x.cube.Admissible)
    (hCB : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support)
    (hD : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v (markedSecondOriginal p x)) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let encode := fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x)
  let S := source.filter (fun x => secondChild (encode x) = (γ,f,k))
  have hvalid : ∀ x ∈ source,
      Valid (encode x) (secondChild (encode x)).1 (secondChild (encode x)).2.1 (secondChild (encode x)).2.2 := by
    intro x hx
    exact originalSecondTuple_valid p hp hpr u v (markedSecondOriginal p x)
      (markedSecondOriginal_valid p hp hpr hcop x (hCB x hx) (hD x hx) (hE x hx) (hold x hx) (hnew x hx))
  have hv : ∀ y ∈ S.image encode, Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using hvalid x hxs
  have hi : Set.InjOn encode (S : Set (MarkedSecondSource ι Jo Jn)) := by
    intro x hx y hy he
    exact markedSecondTuple_injOn p hp hinj u v
      (ha x (Finset.mem_filter.mp hx).1) (ha y (Finset.mem_filter.mp hy).1) he
  have hb := valid_tuple_card_le_slot_cap (S.image encode) γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_iff.mpr hi] at hb
  exact hb

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ActualSecondEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers IdealMobiusDivisorSum
open InverseInitialArithmetic (sourceIdeal sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

theorem actualSecondChild_nonzero (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0) :
    (actualSecondChild p u v x).2.1 ≠ 0 ∧
    (actualSecondChild p u v x).1.q0 ≠ 0 ∧
    (actualSecondChild p u v x).1.quotient ≠ 0 ∧
    (actualSecondChild p u v x).1.residual ≠ 0 := by
  have hj : Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hb : Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  change _ ≠ 0 ∧ _ ≠ 0 ∧ x.quotient ≠ 0 ∧ _ ≠ 0
  refine ⟨?_,hb,ht,sourceIdeal_ne_zero p hp _⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)) (sourceIdeal_ne_zero p hp _)

theorem actual_second_fiber_weight (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (c : SecondChild)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) :
    ∑ x ∈ source with actualSecondChild p u v x = c, w x ≤ secondDivisorWeight K c := by
  by_cases he : (source.filter (fun x => actualSecondChild p u v x = c)).Nonempty
  · obtain ⟨x,hx⟩ := he
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hf,hq,ht,hr⟩ := actualSecondChild_nonzero p hp u v x (hs.quotient_nonzero x hx)
    rw [he] at hf hq ht hr
    have hcard := actual_marked_second_source_fiber p hp hpr hcop hinj u v source
      hs.admissible hs.common_disjoint hs.first_divisor hs.second_divisor hs.old_support hs.new_support
      c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
    calc
      _ ≤ ∑ _x ∈ source with actualSecondChild p u v _x = c, (1 : ℝ) :=
        Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
      _ = ((source.filter (fun x => actualSecondChild p u v x = c)).card : ℝ) := by simp
      _ ≤ _ := by
        dsimp only [secondDivisorWeight,actualSecondChild]
        exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.sum_empty]
    unfold secondDivisorWeight
    positivity

theorem actual_second_energy_projection (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : SecondChild → ℂ) :
    ∑ x ∈ source, w x * ‖F (actualSecondChild p u v x)‖^2 ≤
      ∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ := by
  have hm : ∀ x ∈ source, actualSecondChild p u v x ∈
      actualSecondTriples p u v source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,Finset.mem_product.mpr (hchild x hx)⟩
  have hb := fiber_energy_bound source (actualSecondTriples p u v source ×ˢ (labels ×ˢ rows))
    (actualSecondChild p u v) w (secondDivisorWeight K) (fun c => ‖F c‖^2) hm
    (fun _ _ => sq_nonneg _) (fun c _ => actual_second_fiber_weight p hp hpr hcop hinj u v source hs c K ho hn w hw)
  apply hb.trans_eq
  simp only [Finset.sum_product,secondDivisorWeight,tripleDivisorWeight,secondLabelEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem actual_second_weighted_count (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x * F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  apply (DescentWeightedCauchy.weighted_cauchy source w (F ∘ actualSecondChild p u v)
    (G ∘ actualSecondChild p u v)).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw F))
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.ChildCutoff
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma mem_childFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ childFrequencyBall a R ↔ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding a‖^2 := sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero ha))
  simp only [childFrequencyBall, Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_,h⟩⟩
  apply mem_secondFrequencyCutoff
  apply (le_div_iff₀ hn).mpr
  simpa only [map_mul, norm_mul, mul_pow, mul_comm] using h

lemma mem_nonzeroChildFrequencyBall (a : Eis) (ha : a ≠ 0) (R : ℝ) (k : Eis) :
    k ∈ nonzeroChildFrequencyBall a R ↔
      0 < ‖eisEmbedding (a*k)‖^2 ∧ ‖eisEmbedding (a*k)‖^2 ≤ R := by
  have hn : 0 < ‖eisEmbedding (a*k)‖^2 ↔ k ≠ 0 := by
    rw [sq_pos_iff, norm_ne_zero_iff]
    constructor
    · intro h hk; apply h; simp [hk]
    · intro hk; exact ConcreteTraceCRT.eisEmbedding_ne_zero (mul_ne_zero ha hk)
  simp only [nonzeroChildFrequencyBall, Finset.mem_erase,
    mem_childFrequencyBall a ha, hn]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondFixedFamily
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_extracted_support_killed
    (B C G E V A : Finset ι) (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) (m : Eis) :
    ∀ i ∈ A,
      ((m*b0Label p B v ε₁ ε₂)*secondMaskQuotient p E G hEG)*
        (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*
          primeSubsetGenerator (fun j => Ideal.span {p j}) E*∏ j ∈ V,p j) ∈ Ideal.span {p i} := by
  let r := secondMaskQuotient p E G hEG
  let e := primeSubsetGenerator (fun j => Ideal.span {p j}) E
  let T := ((m*b0Label p B v ε₁ ε₂)*r)*
    (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*e*∏ j ∈ V,p j)
  have hb : (∏ j ∈ B,p j) ∣ T := by
    apply (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv).trans
    refine ⟨m*r*(∏ j ∈ C,p j)*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hc : (∏ j ∈ C,p j) ∣ T := by
    refine ⟨m*b0Label p B v ε₁ ε₂*r*jLabel p B v ε₁ ε₂*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hg' : (∏ j ∈ G,p j) ∣ T := by
    rw [secondMaskQuotient_spec p E G hEG]
    refine ⟨m*b0Label p B v ε₁ ε₂*(∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂*∏ j ∈ V,p j,?_⟩
    dsimp [T,r,e]
    ring
  intro i hi
  apply Ideal.mem_span_singleton.mpr
  change p i ∣ T
  rcases Finset.mem_union.mp (hA hi) with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.dvd_prod_of_mem p hi).trans hb
    · exact (Finset.dvd_prod_of_mem p hi).trans hc
  · exact (Finset.dvd_prod_of_mem p hi).trans hg'

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondCanonicalChild
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem primaryGenerator_primeProduct
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (S : Finset ι) (v : ι → ℕ) :
    primaryGenerator (Ideal.span {primeProduct p S v}) = primeProduct p S v := by
  apply primaryGenerator_span _ (primeProduct_ne_zero p hp S v)
  unfold primeProduct
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have hpow : ConcretePrimeRowBridge.goodLambda^2 ∣ p i^v i-1 := by
      simpa only [one_pow] using (hpr i).trans (sub_dvd_pow_sub_pow (p i) 1 (v i))
    have he : p i^v i*(∏ j ∈ S,p j^v j)-1 =
        (p i^v i-1)*(∏ j ∈ S,p j^v j)+((∏ j ∈ S,p j^v j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hpow _) ih

theorem actual_second_puncture_span
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) :
    Ideal.span {((m*b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
      secondExpansionQuotient p x.second)} =
    Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} := by
  change Ideal.span {(m*b0Label p _ _ _ _)*secondExpansionQuotient p x.second} =
    Ideal.span {(m*primaryGenerator (Ideal.span {b0Label p _ _ _ _}))*
      primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor))}
  rw [show primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr,secondExpansionQuotient_of_subset p x.second hE]
  simp only [←Ideal.span_singleton_mul_span_singleton,secondMaskQuotient_span,
    FiniteGaussPhase.span_finset_prod]

theorem actual_second_generator_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    ∃ u v : Eisˣ,
      actualSecondRawLabel p x = (u:Eis)*primaryGenerator (actualSecondChild p u v x).2.1 ∧
      primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor =
        (v:Eis)*(primaryGenerator (sourceIdeal p x.firstDivisor)*primaryGenerator (sourceIdeal p x.second.divisor)) := by
  let L := (markedSecondOriginal p x).J * sourceIdeal p x.firstCommon *
    sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap
  have hs (S : Finset ι) : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) S} = sourceIdeal p S := by
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,sourceIdeal]
    exact (FiniteGaussPhase.span_finset_prod S p).symm
  have hl : Ideal.span {actualSecondRawLabel p x} = L := by
    unfold actualSecondRawLabel L
    simp only [←Ideal.span_singleton_mul_span_singleton,hs,sourceIdeal,markedSecondOriginal,cubeSecondSource]
    ring
  have hgp (S : Finset ι) : primaryGenerator (sourceIdeal p S) ≠ 0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hL : primaryGenerator L ≠ 0 := by
    dsimp only [L]
    rw [primaryGenerator_mul,primaryGenerator_mul,primaryGenerator_mul]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (hgp _)) (hgp _)) (hgp _)
    change primaryGenerator (Ideal.span {jLabel p _ _ _ _}) ≠ 0
    rw [show primaryGenerator (Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _]
    exact primeProduct_ne_zero p hp _ _
  obtain ⟨u,v,hu,hv⟩ := exists_second_generator_sectors (actualSecondRawLabel p x)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor)
    L (sourceIdeal p x.firstDivisor) (sourceIdeal p x.second.divisor)
    hl (hs _) (hs _) hL (hgp _) (hgp _)
  exact ⟨u,v,hu,hv⟩

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SlotAssignments
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

theorem slotAssignmentWeight_norm_le_one (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (q : ∀ i ∈ I, ι)
    (hq : q ∈ I.pi (fun i => L i ∩ A))
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) : ‖slotAssignmentWeight I a q‖ ≤ 1 := by
  rw [slotAssignmentWeight,norm_prod]
  apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
  intro i _
  exact ha i.val i.property _ (Finset.mem_inter.mp (Finset.mem_pi.mp hq i.val i.property)).1

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSource
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)

omit [DecidableEq ι] in
theorem attachSecondSlots_injective {Jo Jn : ℕ} :
    Function.Injective (fun q : MarkedSecondSource ι Jo 0 × (Fin Jn → ι) => attachSecondSlots q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · apply MarkedSecondSource.ext
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.cube) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstCommon) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstDivisor) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.second) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.quotient) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.oldAssigned) h
    · funext i; exact Fin.elim0 i
  · exact congrArg MarkedSecondSource.newAssigned h

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPairedSlots_injective {Jo : ℕ} (J₁ J₂ : Finset σ) :
    Function.Injective (attachPairedSlots (ι:=ι) (Jo:=Jo) J₁ J₂) := by
  intro q r h
  have he := @attachSecondSlots_injective ι Jo (J₁.card+J₂.card)
    (q.1,pairedSlotAssignment J₁ J₂ q.2) (r.1,pairedSlotAssignment J₁ J₂ r.2) h
  exact Prod.ext (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.2) he))

theorem mem_assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) :
    x ∈ assignedSecondSource source J₁ J₂ L₁ L₂ ↔
      ∃ y ∈ source, ∃ q₁ ∈ J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap)),
      ∃ q₂ ∈ J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap)),
        attachPairedSlots J₁ J₂ (y,(q₁,q₂)) = x := by
  constructor
  · intro hx
    obtain ⟨⟨y,q₁,q₂⟩,hmem,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hy,hq⟩ := Finset.mem_product.mp hmem
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine ⟨y,hy,q₁,Finset.mem_pi.mpr ?_,q₂,Finset.mem_pi.mpr ?_,rfl⟩
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · rintro ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(y,(q₁,q₂)),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,Finset.mem_product.mpr ⟨?_,?_⟩⟩,?_⟩,rfl⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q₁ hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q₂ hq₂ k)).2

theorem assignedSecondSource_conditions (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    ActualSecondSourceConditions p (assignedSecondSource source J₁ J₂ L₁ L₂) := by
  have hmem : ∀ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      ∃ y ∈ source, ∃ q, attachPairedSlots J₁ J₂ (y,q)=x ∧
        ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ y.second.sourceCommon∪y.second.overlap := by
    intro x hx
    obtain ⟨⟨y,q⟩,hmem,he⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hmem
    exact ⟨y,(Finset.mem_product.mp hmem).1,q,he,hq⟩
  constructor
  all_goals
    intro x hx
    obtain ⟨y,hy,q,rfl,hq⟩ := hmem x hx
  · exact hs.admissible y hy
  · exact hs.common_disjoint y hy
  · exact hs.first_divisor y hy
  · exact hs.second_divisor y hy
  · exact hs.old_support y hy
  · exact hq
  · exact hs.quotient_nonzero y hy

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2

theorem assignedSecondSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card) → ℂ) :
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂, F x =
      ∑ y ∈ source, ∑ q ∈
        (J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap))) ×ˢ
        (J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap))),
          F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [assignedSecondSource,Finset.sum_image (fun q _ r _ h => attachPairedSlots_injective J₁ J₂ h),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem assignedSecondCoefficient_norm_le_one {Jo : ℕ}
    (source : Finset (MarkedSecondSource ι Jo 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card))
    (hx : x ∈ assignedSecondSource source J₁ J₂ L₁ L₂) :
    ‖assignedSecondCoefficient J₁ J₂ a₁ a₂ x‖ ≤ 1 := by
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  rw [assignedSecondCoefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ (q₁,q₂)
    (Finset.mem_product.mpr ⟨hq₁,hq₂⟩) ha₁ ha₂

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondMarkedEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondChild_erase {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondWeights
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondSignedSourceWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) :
    ‖secondSignedSourceWeight p hp hcop hg Ψ m c d z x‖ ≤ 1 := by
  have hinput : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d x.sourceCommon).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one
    (∏ i ∈ x.divisor,Ideal.span {p i})
  have hcommon := secondCommonWeight_norm_le p hp hcop hg hinj hc
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency) x.overlap
  have hc1 : ‖secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap‖ ≤ 1 := by
    apply hcommon.trans
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((secondRayMinus_norm_le Ψ z _).trans (hΨ _))).trans
      ((secondRayPlus_norm_le Ψ z _).trans (hΨ _))
  simp only [secondSignedSourceWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖))]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hinput).trans hμ)).trans hc1

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSquarefree
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourcePrime sourceIdeal_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem sourceIdeal_squarefree (S : Finset ι) : Squarefree (sourceIdeal p S) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (sourcePrime p i).property.squarefree

include hcop in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_coprime_of_disjoint (S T : Finset ι) (hST : Disjoint S T) :
    IsCoprime (sourceIdeal p S) (sourceIdeal p T) := by
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (fun he => Finset.disjoint_left.mp hST hi (he.symm ▸ hj))

omit [DecidableEq ι] in
lemma prime_span_coprime_of_not_mem (i : ι) (c : Eis) (hc : c ∉ Ideal.span {p i}) :
    IsCoprime (Ideal.span {p i}) (Ideal.span {c} : Ideal Eis) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he := (inferInstance : (Ideal.span {p i}).IsMaximal).eq_of_le hne le_sup_left
  apply hc
  rw [he]
  exact (show Ideal.span {c} ≤ (Ideal.span {p i} : Ideal Eis) ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (by simp))

omit [DecidableEq ι] in
theorem sourceIdeal_coprime_of_not_mem (S : Finset ι) (c : Eis)
    (hc : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (sourceIdeal p S) (Ideal.span {c} : Ideal Eis) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact IsCoprime.prod_left (fun i hi => prime_span_coprime_of_not_mem p i c (hc i hi))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem jLabel_span_dvd_source (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {jLabel p B v ε₁ ε₂} : Ideal Eis) ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i^bit (retained (parity (v i)) (ε₁ i) (ε₂ i))) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases retained (parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit]

omit [DecidableEq ι] in
theorem secondInputCoefficient_zero_of_label_mem (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S) (hc : c ∈ Ideal.span {p i}) :
    secondInputCoefficient p hg Ψ m c d H S = 0 := by
  have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
    simp only [rowCoprimeMask,if_pos (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
  have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
  simp only [secondInputCoefficient,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondPreColumn_zero_of_mask_label_mem (Ψ : Eis →* ℂ) (m c d e k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hc : m*c ∈ Ideal.span {p i}) : secondPreColumn p hp hcop hg Ψ m c d e k H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hc with hm|hc
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m = 0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i ∈ S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondPreColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
      simp only [rowCoprimeMask,if_pos (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
    have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
    simp only [secondPreColumn,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondSignedSourceWeight_nonzero_masks
    (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondSignedSourceWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (sourceIdeal p x.sourceCommon) (Ideal.span {c}) ∧
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.sourceCommon * Ideal.span {c}) := by
  constructor
  · apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    have hz := secondInputCoefficient_zero_of_label_mem p hg Ψ m c d (fun _ => 1) x.sourceCommon i hi hc
    apply hw
    simp only [secondSignedSourceWeight,hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      Complex.ofReal_zero,zero_mul]
  · change IsCoprime (sourceIdeal p x.overlap) (Ideal.span {∏ i ∈ x.sourceCommon,p i} * Ideal.span {c})
    rw [Ideal.span_singleton_mul_span_singleton]
    apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
    let r := secondExpansionQuotient p x
    have her : e*r = ∏ j ∈ x.sourceCommon,p j := by
      dsimp only [r]
      rw [secondExpansionQuotient_of_subset p x hE]
      exact (secondMaskQuotient_spec p _ _ hE).symm
    have hmc : (m*(e*r))*c ∈ Ideal.span {p i} := by
      rw [her,mul_assoc]
      exact Ideal.mul_mem_left _ m hc
    have hz := secondPreColumn_zero_of_mask_label_mem p hp hcop hg (secondRayPlus Ψ z)
      (m*(e*r)) c d e (-x.frequency) (fun _ => 1) x.overlap i hi hmc
    dsimp only [e,r] at hz
    apply hw
    simp only [secondSignedSourceWeight,secondCommonWeight,hz,mul_zero]

theorem actualSecondSignedWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ‖actualSecondSignedWeight p hp hcop hg Ψ m z x‖ ≤ 1 :=
  secondSignedSourceWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ _ _ _ z x.second

theorem actual_second_nonzero_weight_squarefree
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m z x ≠ 0) (u v : Eisˣ) :
    Squarefree (actualSecondChild p u v x).2.1 := by
  let J : Ideal Eis := Ideal.span {jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}
  let C := sourceIdeal p x.firstCommon
  let E := sourceIdeal p x.second.divisor
  let G := sourceIdeal p x.second.sourceCommon
  let V := sourceIdeal p x.second.overlap
  have hj : J ∣ sourceIdeal p x.cube.support := jLabel_span_dvd_source p _ _ _ _
  have hJ : Squarefree J := (sourceIdeal_squarefree p hcop x.cube.support).squarefree_of_dvd hj
  have hC : Squarefree C := sourceIdeal_squarefree p hcop _
  have hG : Squarefree G := sourceIdeal_squarefree p hcop _
  have hV : Squarefree V := sourceIdeal_squarefree p hcop _
  have hJC : IsCoprime J C :=
    (sourceIdeal_coprime_of_disjoint p hcop x.cube.support x.firstCommon hCB.symm).of_isCoprime_of_dvd_left hj
  have hdg : E ∣ G := sourceIdeal_dvd p _ _ hE
  have hcspan : Ideal.span {(∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} = C*J :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  obtain ⟨hgmask,hvmask⟩ := secondSignedSourceWeight_nonzero_masks p hp hcop hg Ψ _ _ _ z x.second hE hw
  rw [hcspan] at hgmask hvmask
  change IsCoprime G (C*J) at hgmask
  change IsCoprime V (G*(C*J)) at hvmask
  have heJC : IsCoprime E (J*C) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : J*C*E ∣ G*(C*J) := by
    obtain ⟨r,hr⟩ := hdg
    refine ⟨r,?_⟩
    rw [hr]
    ring
  have hvJCE := hvmask.of_isCoprime_of_dvd_right hdiv
  change Squarefree (J*C*E*V)
  exact squarefree_mul_iff.mpr ⟨hvJCE.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨heJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime,hJ,hC⟩,hG.squarefree_of_dvd hdg⟩,hV⟩

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

theorem assignedSecondSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S ⊆ T)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSecondSource S J₁ J₂ L₁ L₂ ⊆ assignedSecondSource T J₁ J₂ L₁ L₂ := by
  intro x hx
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,he⟩ := (mem_assignedSecondSource S J₁ J₂ L₁ L₂ x).mp hx
  exact (mem_assignedSecondSource T J₁ J₂ L₁ L₂ x).mpr ⟨y,hST hy,q₁,hq₁,q₂,hq₂,he⟩

theorem actualSecondTriples_mono {Jo Jn : ℕ} (u v : Eisˣ)
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (hST : S ⊆ T) :
    actualSecondTriples p u v S ⊆ actualSecondTriples p u v T :=
  Finset.image_subset_image hST

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondParentLists
namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_parent_deleted_prime_killed {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (_hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (m : O) (i : ι)
    (hi : i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient) :
    actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x∈Ideal.span {p i} := by
  rcases hi with hi|hi
  · have hv : ∀ j∈x.cube.support,0<x.cube.leftExponent j+x.cube.rightExponent j := by
      intro j hj
      simp only [CubeCoordinates.support,Finset.mem_union,Finsupp.mem_support_iff] at hj
      omega
    have hk := actual_second_extracted_support_killed p
      x.cube.support x.firstCommon x.second.sourceCommon x.second.divisor x.second.overlap
      (x.cube.support∪x.firstCommon) hE Finset.subset_union_left
      (fun j=>x.cube.leftExponent j+x.cube.rightExponent j) x.cube.leftBit x.cube.rightBit hv
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) i hi
    simpa only [actualSecondRawInheritedPuncture,actualSecondRawLabel,
      secondExpansionQuotient_of_subset p x.second hE] using hk
  · have hq : ConcretePrimeRowBridge.idealGenerator x.quotient∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp hi)
      have hmem : ConcretePrimeRowBridge.idealGenerator x.quotient∈
          Ideal.span {ConcretePrimeRowBridge.idealGenerator x.quotient} := Ideal.subset_span (by simp)
      simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hmem
    unfold actualSecondRawInheritedPuncture
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq)))

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondModeParentLists
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseInitialArithmetic CompletedGauss InverseSecondFibers JointLogSeparation
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
theorem actual_second_canonical_label_span
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Oˣ) :
    Ideal.span {actualSecondRawLabel p x}=
      Ideal.span {primaryGenerator (actualSecondChild p u v x).2.1} := by
  obtain ⟨u₀,v₀,hl,hv⟩ := actual_second_generator_sectors p hp hpr x
  rw [hl,←Ideal.span_singleton_mul_span_singleton]
  simp only [Ideal.span_singleton_eq_top.mpr (Units.isUnit u₀),Ideal.top_mul]
  rfl

theorem secondCanonicalPolynomial_parent_lists_restore
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (u v : Oˣ)
    (deleted : Finset ι)
    (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : OuterTriple→O→*ℂ) (m : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : OuterTriple→ℝ→ℂ) (X : ℝ) (k : O) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots (fun j=>lists j\deleted) a W X ((actualSecondChild p u v x).1,
        (actualSecondChild p u v x).2.1,k) =
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots lists a W X ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,k) := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  intro i hi
  have hk := actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)
  have he : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}=
      Ideal.span {actualSecondInheritedPuncture m (actualSecondChild p u v x).1*
        primaryGenerator (actualSecondChild p u v x).2.1} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      actual_second_canonical_label_span p hp hpr x u v]
    congr 1
    exact actual_second_puncture_span p hp hpr x hE u v
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient)
  have hk' : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}≤Ideal.span {p i} :=
    Ideal.span_le.mpr (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl; exact hk)
  rw [he] at hk'
  exact hk' (Ideal.subset_span (by simp))

theorem secondModeBranch_parent_lists_restore
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (u v : Oˣ)
    (deleted₁ deleted₂ : Finset ι)
    (hd₁ : ∀ i∈deleted₁,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (hd₂ : ∀ i∈deleted₂,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (G E V B X : ℝ) (t : Frequency×(Fin 6→ℝ)) :
    secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂
      (fun i=>lists₁ i\deleted₁) (fun i=>lists₂ i\deleted₂) a₁ a₂ ω₁ ω₂ G E V B X t =
    secondModeOuter p x Ψ m z G E V B X t *
      (star (primeMark J₁ (fun i=>lists₁ i\deleted₁) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (fun i=>lists₂ i\deleted₂) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
      secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x) := by
  unfold secondModeBranch secondModeLeft secondModeRight
  rw [secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₁ hd₁,
    secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₂ hd₂]

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] in
theorem actualSecondMultiplier_ne_zero {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    actualSecondMultiplier p x ≠ 0 := by
  apply mul_ne_zero
  · exact primeSubsetGenerator_ne_zero _ _
  · exact primeSubsetGenerator_ne_zero _ _

include hp in

theorem actual_second_row_norm_sq
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    ‖eisEmbedding (actualSecondChild p u v x).2.2‖^2 =
      ‖eisEmbedding (actualSecondMultiplier p x*x.second.frequency)‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.firstDivisor)*
      primaryGenerator (sourceIdeal p x.second.divisor)*secondUnitFrequency u v x.second.frequency)‖^2 = _
  rw [sourceIdeal_gen p hp hpr,sourceIdeal_gen p hp hpr]
  simp only [map_mul,norm_mul,mul_pow,secondUnitFrequency_norm,actualSecondMultiplier,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in

theorem actual_second_row_ball
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) (R : ℝ) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R ↔
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x),
    mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,actual_second_row_norm_sq p hp hpr]

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondVaryingLists
namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
lemma varyingAssignedGate_attach {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i∈J₁,ι)×(∀ i∈J₂,ι)) :
    varyingAssignedGate J₁ J₂ L₁ L₂ (attachPairedSlots J₁ J₂ (x,q)) ↔
      q.1∈J₁.pi (L₁ x) ∧ q.2∈J₂.pi (L₂ x) := by
  simp only [varyingAssignedGate,attachPairedSlots,erase_attachSecondSlots]
  simp only [attachSecondSlots,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,Finset.mem_pi]

theorem varyingAssignedSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S⊆T)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :
    varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂⊆
      varyingAssignedSource T J₁ J₂ base₁ base₂ L₁ L₂ := by
  exact Finset.filter_subset_filter _ (assignedSecondSource_mono hST J₁ J₂ base₁ base₂)

theorem varyingAssignedSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card)→ℂ) :
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,F x =
      ∑ y∈source,∑ q∈(J₁.pi (fun i=>L₁ y i∩(y.second.sourceCommon∪y.second.overlap)))×ˢ
        (J₂.pi (fun i=>L₂ y i∩(y.second.sourceCommon∪y.second.overlap))),F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [varyingAssignedSource,Finset.sum_filter,assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_product,varyingAssignedGate_attach,Finset.mem_pi,Finset.mem_inter]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
    exact ⟨fun i hi=>⟨h₃ i hi,(h₁ i hi).2⟩,fun i hi=>⟨h₄ i hi,(h₂ i hi).2⟩⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨⟨fun i hi=>⟨hL₁ y hy i hi (h₁ i hi).1,(h₁ i hi).2⟩,
      fun i hi=>⟨hL₂ y hy i hi (h₂ i hi).1,(h₂ i hi).2⟩⟩,
      fun i hi=>(h₁ i hi).1,fun i hi=>(h₂ i hi).1⟩

theorem varyingAssignedSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ) (w P : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈source,w y*(star (primeMark J₁ (L₁ y) a₁ (y.second.sourceCommon∪y.second.overlap))*
      primeMark J₂ (L₂ y) a₂ (y.second.sourceCommon∪y.second.overlap))*P y) =
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x)*P (eraseSecondSlots x) := by
  rw [varyingAssignedSource_sum source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_varying_lists_weighted_count
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {Jo : ℕ} (u v : Oˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈base₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈base₂ i,‖a₂ i q‖≤1)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hchild : ∀ x∈source,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows)
    (K : ℕ) (ho : Jo≤2*K) (hJ₁ : J₁.card≤K) (hJ₂ : J₂.card≤K)
    (w : MarkedSecondSource ι Jo 0→ℂ) (hw : ∀ x∈source,‖w x‖≤1) (F G : SecondChild→ℂ) :
    ‖∑ x∈source,w x*(star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap))*
      primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap))*
      F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x))‖ ≤
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ)*
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) := by
  let S := varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂
  have hsub : S⊆assignedSecondSource source J₁ J₂ base₁ base₂ := Finset.filter_subset _ _
  have hs' : ActualSecondSourceConditions p S :=
    (assignedSecondSource_conditions p source hs J₁ J₂ base₁ base₂).mono p hsub
  have herase : ∀ x∈S,eraseSecondSlots x∈source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ base₁ base₂ x).mp (hsub hx)
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card)=>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hw' : ∀ x∈S,‖w' x‖≤1 := by
    intro x hx
    rw [show w' x=w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ base₁ base₂ a₁ a₂ ha₁ ha₂ x (hsub hx))
  have hc' : ∀ x∈S,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := varyingAssignedSource_sum_marks source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂ a₁ a₂ w
    (fun x=>F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end SevenEighths.InverseMoment

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondVaryingSupported
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_varying_lists_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ → Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ base₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ base₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_varying_lists_weighted_count p hp hpr hcop hinj u v S
    (hs.mono p hsub) J₁ J₂ base₁ base₂ L₁ L₂
    (fun x hx=>hL₁ x (hsub hx)) (fun x hx=>hL₂ x (hsub hx)) a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (varyingAssignedSource_mono hsub J₁ J₂ base₁ base₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Descent.SecondDeletedModeEnergy
namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_branch_energy_oai
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  let phase := fun x => w x * secondModeOuter p x Ψ m z G E V B X t
  have hphase : ∀ x ∈ source,‖phase x‖ ≤ 1 := by
    intro x hx
    simpa only [phase,norm_mul,secondModeOuter,secondOuterPhase_norm,mul_one] using hw x hx
  have hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
    intro x hx
    exact ⟨hlabels x hx,(actual_second_row_ball p hp hpr x u v R).mp (hrows x hx)⟩
  have he := actual_second_supported_varying_lists_energy p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*ConcretePrimeRowBridge.idealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)
    (fun _ _ _ _=>Finset.sdiff_subset) (fun _ _ _ _=>Finset.sdiff_subset) a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [secondModeBranch_parent_lists_restore p hp hcop hg hpr x (hs.admissible x hx)
    (hs.second_divisor x hx) u v (deleted₁ x) (deleted₂ x) (hd₁ x hx) (hd₂ x hx)]
  dsimp only [phase]
  ring

end
end SevenEighths.InverseMoment

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.InverseMoment.actual_second_deleted_mode_branch_energy_oai.{u_1, u_2} := @OAI.SevenEighths.InverseMoment.actual_second_deleted_mode_branch_energy_oai.{u_1, u_2}
