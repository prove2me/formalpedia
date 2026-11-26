-- Prove2me | solution 1 for LinearDynamics.guarded_periodic_linear_readout
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T19:24:45.564661+00:00
-- url     : https://prove2.me/submissions/68388184-6696-41b4-baba-772b37c71f72

import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

namespace PvsNP.GuardedAffineBlock

open scoped BigOperators
open Polynomial

section Linear

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A linear observation on an orbit vanishes everywhere once it vanishes
on the first `finrank K V` states. -/
theorem orbit_probe_zero_of_prefix (step : Module.End K V) (probe : V →ₗ[K] K)
    (start : V) (zeros : ∀ i < Module.finrank K V, probe ((step ^ i) start) = 0) :
    ∀ i : ℕ, probe ((step ^ i) start) = 0 := by
  let d := Module.finrank K V
  let p := step.charpoly
  have deg : p.natDegree = d := step.charpoly_natDegree
  have top : p.coeff d = 1 := deg ▸ step.charpoly_monic.coeff_natDegree
  have expanded : (∑ i ∈ Finset.range (d + 1), p.coeff i • step ^ i) = 0 := by
    have relation := step.aeval_self_charpoly
    change aeval step p = 0 at relation
    nth_rw 1 [p.as_sum_range] at relation
    simpa only [map_sum, aeval_monomial, deg, Algebra.smul_def] using relation
  have recurrence (offset : ℕ) :
      (∑ i ∈ Finset.range (d + 1), p.coeff i * probe ((step ^ (i + offset)) start)) = 0 := by
    have applied := congrArg (fun e : Module.End K V => probe (e ((step ^ offset) start)))
      expanded
    simpa only [LinearMap.sum_apply, LinearMap.zero_apply, map_sum, map_zero,
      LinearMap.smul_apply, map_smul, smul_eq_mul, pow_add, Module.End.mul_apply]
      using applied
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases small : t < d
    · exact zeros t small
    have bound : d ≤ t := Nat.le_of_not_gt small
    have ends : d + (t - d) = t := Nat.add_sub_of_le bound
    have triangular := recurrence (t - d)
    rw [Finset.sum_range_succ] at triangular
    have earlier :
        (∑ i ∈ Finset.range d, p.coeff i * probe ((step ^ (i + (t - d))) start)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have prior : i + (t - d) < t := by
        have := Finset.mem_range.mp hi
        omega
      rw [ih _ prior, mul_zero]
    simpa only [earlier, zero_add, top, one_mul, ends] using triangular

end Linear

end PvsNP.GuardedAffineBlock

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace PvsNP.PeriodicAffineReadout

/-- Compose the first k phases in chronological order. -/
def prefixProduct {M : Type*} [Monoid M] (phase : ℕ → M) : ℕ → M
  | 0 => 1
  | k+1 => phase k * prefixProduct phase k

/-- First apply the full-period product, then the remaining prefix. -/
def readout {M : Type*} [Monoid M] (phase : ℕ → M) (period t : ℕ) : M :=
  prefixProduct phase (t % period) * (prefixProduct phase period) ^ (t / period)

@[simp] theorem readout_zero {M : Type*} [Monoid M] (phase : ℕ → M) (period : ℕ) :
    readout phase period 0 = 1 := by
  simp [readout,prefixProduct]

theorem readout_at_phase {M : Type*} [Monoid M] (phase : ℕ → M)
    {period : ℕ} (positive : 0 < period) (q r : ℕ) (phaseIn : r < period) :
    readout phase period (r + period*q) = prefixProduct phase r * (prefixProduct phase period)^q := by
  simp [readout,Nat.add_mul_div_left _ _ positive,Nat.mod_eq_of_lt phaseIn,
    Nat.div_eq_of_lt phaseIn]

theorem readout_succ {M : Type*} [Monoid M] (phase : ℕ → M)
    {period : ℕ} (positive : 0 < period) (t : ℕ) :
    readout phase period (t+1) = phase (t % period) * readout phase period t := by
  let q := t / period
  let r := t % period
  have modulus : r < period := Nat.mod_lt _ positive
  have expanded : r + period*q = t := Nat.mod_add_div _ _
  have rewriteT : t + 1 = r+1+period*q := by omega
  by_cases within : r+1 < period
  · rw [rewriteT,readout_at_phase phase positive q (r+1) within]
    change phase r * prefixProduct phase r * (prefixProduct phase period)^q =
      phase r * (prefixProduct phase r * (prefixProduct phase period)^q)
    exact mul_assoc _ _ _
  · have boundary : r+1 = period := by omega
    have full : t+1 = 0 + period*(q+1) := by
      rw [rewriteT,boundary,Nat.mul_succ]
      omega
    rw [full, readout_at_phase phase positive (q+1) 0 positive]
    change 1 * (prefixProduct phase period)^(q+1) =
      phase r * (prefixProduct phase r * (prefixProduct phase period)^q)
    have next : prefixProduct phase period = phase r * prefixProduct phase r := by
      rw [← boundary]
      rfl
    rw [one_mul,pow_succ',next,mul_assoc]

section Linear

open scoped BigOperators

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- A checked relation among the first powers applied to the initial
state supplies a recurrence for every linear observation. -/
theorem probe_zero_of_vector_recurrence (periodMap : Module.End K W) (start : W)
    (degree : ℕ) (coefficient : ℕ → K)
    (recurrence : (periodMap^degree) start =
      ∑ i ∈ Finset.range degree, coefficient i • (periodMap^i) start)
    (probe : W →ₗ[K] K)
    (zeros : ∀ i < degree, probe ((periodMap^i) start) = 0) :
    ∀ i : ℕ, probe ((periodMap^i) start) = 0 := by
  have atOffset (offset : ℕ) :
      probe ((periodMap^(offset+degree)) start) =
        ∑ i ∈ Finset.range degree, coefficient i * probe ((periodMap^(offset+i)) start) := by
    have mapped := congrArg (fun x => probe ((periodMap^offset) x)) recurrence
    simpa only [pow_add,Module.End.mul_apply,map_sum,map_smul,smul_eq_mul] using mapped
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    by_cases early : t < degree
    · exact zeros t early
    have suffix : t-degree+degree = t := Nat.sub_add_cancel (by omega)
    have relation := atOffset (t-degree)
    rw [suffix] at relation
    rw [relation]
    apply Finset.sum_eq_zero
    intro i inside
    have small := Finset.mem_range.mp inside
    rw [ih _ (by omega),mul_zero]


/-- A bound at which a zero prefix determines any linear observation of
the whole period orbit. -/
def ProbesExtend (periodMap : Module.End K W) (start : W) (degree : ℕ) : Prop :=
  ∀ probe : W →ₗ[K] K,
    (∀ i < degree, probe ((periodMap^i) start) = 0) →
    ∀ i : ℕ, probe ((periodMap^i) start) = 0

theorem probes_zero_from_prefix (phase : ℕ → Module.End K W) (probe : ℕ → W →ₗ[K] K)
    {period : ℕ} (positive : 0 < period) (start : W) (duration degree : ℕ)
    (propagate : ProbesExtend (prefixProduct phase period) start degree)
    (checked : ∀ i < min duration (period*degree),
      probe (i%period) (readout phase period i start) = 0) :
    ∀ t < duration, probe (t%period) (readout phase period t start) = 0 := by
  intro t before
  let q := t/period
  let r := t%period
  have residue : r < period := Nat.mod_lt _ positive
  have packed : r+period*q = t := Nat.mod_add_div _ _
  have inPhase (j : ℕ) : r+period*j < period*(j+1) := by
    rw [Nat.mul_succ]
    omega
  by_cases firstCycles : q < degree
  · apply checked t (Nat.lt_min.mpr ⟨before,?_⟩)
    rw [← packed]
    exact (inPhase q).trans_le (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt firstCycles))
  · have late : degree ≤ q := Nat.le_of_not_gt firstCycles
    let observe := (probe r).comp (prefixProduct phase r)
    have observation (i : ℕ) :
        probe r (readout phase period (r+period*i) start) =
          observe (((prefixProduct phase period)^i) start) := by
      rw [readout_at_phase _ positive _ _ residue]
      rfl
    have small : ∀ i < degree, observe (((prefixProduct phase period)^i) start) = 0 := by
      intro i early
      have total : r+period*i < duration := by
        have lt := Nat.mul_lt_mul_of_pos_left (early.trans_le late) positive
        rw [← packed] at before
        omega
      have prefixTime : r+period*i < period*degree :=
        (inPhase i).trans_le (Nat.mul_le_mul_left _ (Nat.succ_le_of_lt early))
      have verdict := checked _ (Nat.lt_min.mpr ⟨total,prefixTime⟩)
      rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt residue,observation] at verdict
      exact verdict
    change probe r (readout phase period t start) = 0
    rw [← packed,observation]
    exact propagate observe small q

/-- In dimension d, check no more than d full periods of prescribed
guards. The period product then gives every actual state through the horizon. -/
theorem guarded_linear_periodic_readout [FiniteDimensional K W]
    (phase : ℕ → Module.End K W) (probe : ℕ → W →ₗ[K] K)
    {period : ℕ} (positive : 0 < period) (step : W → W) (start : W) (duration : ℕ)
    (onBranch : ∀ r < period, ∀ x : W, probe r x = 0 → step x = phase r x)
    (checked : ∀ i < min duration (period*Module.finrank K W),
      probe (i%period) (readout phase period i start) = 0) :
    ∀ t ≤ duration, readout phase period t start = step^[t] start := by
  have propagate : ProbesExtend (prefixProduct phase period) start (Module.finrank K W) := by
    intro observation zeros
    exact GuardedAffineBlock.orbit_probe_zero_of_prefix _ _ _ zeros
  have guards := probes_zero_from_prefix phase probe positive start duration _ propagate checked
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro late
    have early : t < duration := Nat.lt_of_succ_le late
    rw [readout_succ phase positive,Module.End.mul_apply,Function.iterate_succ_apply',
      ← ih early.le,onBranch _ (Nat.mod_lt _ positive) _ (guards t early)]

end Linear

end PvsNP.PeriodicAffineReadout

theorem solution {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (phase : ℕ → Module.End K V) (probe : ℕ → V →ₗ[K] K)
    (p : ℕ) (positive : 0 < p) (step : V → V) (start : V) (T : ℕ)
    (onBranch : ∀ r < p, ∀ x : V, probe r x = 0 → step x = phase r x) :
    let product : ℕ → Module.End K V :=
      Nat.rec 1 (fun r acc => phase r * acc)
    let readout := fun t : ℕ => (product (t % p) * (product p) ^ (t / p)) start
    (∀ t < min T (p * Module.finrank K V), probe (t % p) (readout t) = 0) →
    ∀ t ≤ T, readout t = step^[t] start := by
  have sameProduct (n : ℕ) :
      (Nat.rec (1 : Module.End K V) (fun r acc => phase r * acc) n) =
        PvsNP.PeriodicAffineReadout.prefixProduct phase n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change phase n * Nat.rec (1 : Module.End K V) (fun r acc => phase r * acc) n =
        phase n * PvsNP.PeriodicAffineReadout.prefixProduct phase n
      rw [ih]
  dsimp only
  simp only [sameProduct]
  exact PvsNP.PeriodicAffineReadout.guarded_linear_periodic_readout phase probe positive step start T onBranch

#print axioms solution
