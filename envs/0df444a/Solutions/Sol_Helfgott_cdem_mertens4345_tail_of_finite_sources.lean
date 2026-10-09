-- Prove2me | solution 1 for Helfgott.cdem_mertens4345_tail_of_finite_sources
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T03:20:34.36632+00:00
-- url     : https://prove2.me/submissions/ad8da01e-91bf-4de0-a3cf-40e53b93d83c

import Theorems.Thm_Helfgott_cdem_prefix_199330
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Data.Real.Basic

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem cdem4345_assembled_finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
open Nat ArithmeticFunction Finset
open scoped BigOperators zeta
namespace Helfgott

lemma cdem4345_assembled_cdem_moebius_divisor_sum (q : ℕ) :
    (∑ d ∈ q.divisors, (moebius d : ℝ)) = if q = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f q)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [coe_mul_zeta_apply, intCoe_apply, one_apply] using h

theorem cdem4345_assembled_cdem_moebius_floor_nat (B : ℕ) (hB : 1 ≤ B) :
    (∑ n ∈ Icc 1 B, (moebius n : ℝ) * (B/n : ℕ)) = 1 := by
  have h := cdem4345_assembled_finite_positive_divisor_reindex B (fun d _ => (moebius d : ℝ))
  have hright : (∑ d ∈ Icc 1 B, ∑ _r ∈ Icc 1 (B/d), (moebius d : ℝ)) =
      ∑ d ∈ Icc 1 B, (moebius d : ℝ) * (B/d : ℕ) := by
    apply sum_congr rfl
    intro d hd
    simp [Nat.card_Icc, mul_comm]
  rw [hright] at h
  rw [← h]
  simp_rw [cdem4345_assembled_cdem_moebius_divisor_sum]
  simp [hB]

theorem cdem4345_assembled_cdem_moebius_floor_real (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ) * (⌊x/(n : ℝ)⌋₊ : ℝ)) = 1 := by
  simp_rw [Nat.floor_div_natCast]
  exact cdem4345_assembled_cdem_moebius_floor_nat ⌊x⌋₊
    ((Nat.le_floor_iff (by linarith)).2 (by simpa using hx))

end Helfgott
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

/-!
# Cohen--Dress--El Marraki Lemma 4: the signed finite Abel core

This file starts the theorem-level formalization of Lemma 4 in Cohen--Dress--El Marraki,
*Explicit estimates for summatory functions linked to the Moebius mu-function* (2007).
The same elementary argument occurs as Lemma 4 of Dress--El Marraki (1993).

The important point is that the increments `G(k) - G(k-1)` remain **signed** in the
`6 / pi^2` main term.  Absolute values are introduced only for the squarefree-counting
remainder.  Replacing the signed increments by their absolute values in both terms loses
the constant needed by the paper.

The auxiliary sequence in the paper has the explicit override `Gseq 0 = 0`.  This is not
the raw value of `|1 - F(0)|`, which is `1` for a floor sum.  The override is recorded as a
hypothesis of the Abel identity below.

No analytic or computational input occurs in this file.  In particular, none of the
theorems assumes an unbounded Mertens or squarefree-counting conclusion.
-/

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- The signed coefficient called `u` in CDEM Lemma 4, before instantiating the concrete
floor sum.  Written this way, its endpoint term is visibly
`(maxG - Gseq N) / (N+1)`. -/
noncomputable def cdem4345_assembled_signedMainWeight (N : ℕ) (Gseq : ℕ → ℝ) (maxG : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 N, (Gseq k - Gseq (k - 1)) / (k : ℝ))
    + (maxG - Gseq N) / (N + 1 : ℕ)

/-- The absolute-variation coefficient called `v` in CDEM Lemma 4, before instantiating
the concrete floor sum.  Only the increments in this remainder coefficient are replaced
by their absolute values. -/
noncomputable def cdem4345_assembled_absoluteRemainderWeight (N : ℕ) (Gseq : ℕ → ℝ) (maxG : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 N, |Gseq k - Gseq (k - 1)| / Real.sqrt k)
    + (maxG - Gseq N) / Real.sqrt (N + 1)

/-- The paper's displayed definitions

`u = uN + maxG/(N+1)` and `v = vN + maxG/sqrt(N+1)`

are exactly `cdem4345_assembled_signedMainWeight` and `cdem4345_assembled_absoluteRemainderWeight`. -/
theorem cdem4345_assembled_paper_weights_eq
    (N : ℕ) (Gseq : ℕ → ℝ) (maxG : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (Gseq k - Gseq (k - 1)) / (k : ℝ))
          - Gseq N / (N + 1 : ℕ) + maxG / (N + 1 : ℕ)
        = cdem4345_assembled_signedMainWeight N Gseq maxG
      ∧
    (∑ k ∈ Finset.Icc 1 N, |Gseq k - Gseq (k - 1)| / Real.sqrt k)
          - Gseq N / Real.sqrt (N + 1) + maxG / Real.sqrt (N + 1)
        = cdem4345_assembled_absoluteRemainderWeight N Gseq maxG := by
  unfold cdem4345_assembled_signedMainWeight cdem4345_assembled_absoluteRemainderWeight
  constructor <;> ring

/-- **Signed Abel/remainder bound (CDEM Lemma 4, finite analytic core).**

Suppose the sampled squarefree-counting values `Qseq k` have main term
`mainCoeff * x / k` and remainder at most
`errorCoeff * sqrt(x) / sqrt(k)`.  Then the Abel-transformed sum is bounded by

`mainCoeff * x * u + errorCoeff * sqrt(x) * v`.

The main coefficient multiplies the signed increments `Gseq k - Gseq (k-1)`.
Absolute values occur only in `v`, where they bound the squarefree remainder.

This theorem is deliberately stated for a sampled sequence.  A later wrapper supplies
`Qseq k = Q(x/k)` and derives its hypothesis from the squarefree remainder estimate and
the guard `x >= (N+1) * x_b`. -/
theorem cdem4345_assembled_signed_abel_remainder_bound
    (N : ℕ) (Gseq Qseq : ℕ → ℝ)
    (mainCoeff errorCoeff x maxG : ℝ)
    (hGN_nonneg : 0 ≤ Gseq N)
    (hGN_le : Gseq N ≤ maxG)
    (hQ : ∀ k ∈ Finset.Icc 1 (N + 1),
      |Qseq k - mainCoeff * x / (k : ℝ)|
        ≤ errorCoeff * Real.sqrt x / Real.sqrt k) :
    (∑ k ∈ Finset.Icc 1 N,
        (Gseq k - Gseq (k - 1)) * Qseq k)
        + (maxG - Gseq N) * Qseq (N + 1)
      ≤ mainCoeff * x * cdem4345_assembled_signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt x * cdem4345_assembled_absoluteRemainderWeight N Gseq maxG := by
  have bound_product (d : ℝ) (k : ℕ) (hk : k ∈ Finset.Icc 1 (N + 1)) :
      d * Qseq k
        ≤ d * (mainCoeff * x / (k : ℝ))
            + |d| * (errorCoeff * Real.sqrt x / Real.sqrt k) := by
    have hrem :
        d * (Qseq k - mainCoeff * x / (k : ℝ))
          ≤ |d| * (errorCoeff * Real.sqrt x / Real.sqrt k) := by
      calc
        d * (Qseq k - mainCoeff * x / (k : ℝ))
            ≤ |d * (Qseq k - mainCoeff * x / (k : ℝ))| := le_abs_self _
        _ = |d| * |Qseq k - mainCoeff * x / (k : ℝ)| := abs_mul _ _
        _ ≤ |d| * (errorCoeff * Real.sqrt x / Real.sqrt k) :=
          mul_le_mul_of_nonneg_left (hQ k hk) (abs_nonneg d)
    calc
      d * Qseq k
          = d * (mainCoeff * x / (k : ℝ))
              + d * (Qseq k - mainCoeff * x / (k : ℝ)) := by ring
      _ ≤ d * (mainCoeff * x / (k : ℝ))
              + |d| * (errorCoeff * Real.sqrt x / Real.sqrt k) :=
        add_le_add_right hrem _

  have hsum :
      (∑ k ∈ Finset.Icc 1 N,
          (Gseq k - Gseq (k - 1)) * Qseq k)
        ≤ ∑ k ∈ Finset.Icc 1 N,
            ((Gseq k - Gseq (k - 1)) * (mainCoeff * x / (k : ℝ))
              + |Gseq k - Gseq (k - 1)|
                  * (errorCoeff * Real.sqrt x / Real.sqrt k)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact bound_product (Gseq k - Gseq (k - 1)) k
      (by simp only [Finset.mem_Icc] at hk ⊢; omega)

  have hgap : 0 ≤ maxG - Gseq N := sub_nonneg.mpr hGN_le
  have hend := bound_product (maxG - Gseq N) (N + 1) (by simp)
  rw [abs_of_nonneg hgap] at hend
  have hend' :
      (maxG - Gseq N) * Qseq (N + 1)
        ≤ (maxG - Gseq N) * (mainCoeff * x / (N + 1 : ℕ))
          + (maxG - Gseq N)
              * (errorCoeff * Real.sqrt x / Real.sqrt (N + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hend

  have hmain_sum :
      (∑ k ∈ Finset.Icc 1 N,
          (Gseq k - Gseq (k - 1)) * (mainCoeff * x / (k : ℝ)))
        = mainCoeff * x
            * ∑ k ∈ Finset.Icc 1 N, (Gseq k - Gseq (k - 1)) / (k : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

  have herr_sum :
      (∑ k ∈ Finset.Icc 1 N,
          |Gseq k - Gseq (k - 1)|
            * (errorCoeff * Real.sqrt x / Real.sqrt k))
        = errorCoeff * Real.sqrt x
            * ∑ k ∈ Finset.Icc 1 N,
                |Gseq k - Gseq (k - 1)| / Real.sqrt k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

  calc
    (∑ k ∈ Finset.Icc 1 N,
        (Gseq k - Gseq (k - 1)) * Qseq k)
          + (maxG - Gseq N) * Qseq (N + 1)
      ≤ (∑ k ∈ Finset.Icc 1 N,
          ((Gseq k - Gseq (k - 1)) * (mainCoeff * x / (k : ℝ))
            + |Gseq k - Gseq (k - 1)|
                * (errorCoeff * Real.sqrt x / Real.sqrt k)))
          + ((maxG - Gseq N) * (mainCoeff * x / (N + 1 : ℕ))
            + (maxG - Gseq N)
                * (errorCoeff * Real.sqrt x / Real.sqrt (N + 1))) :=
        add_le_add hsum hend'
    _ = mainCoeff * x * cdem4345_assembled_signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt x * cdem4345_assembled_absoluteRemainderWeight N Gseq maxG := by
      rw [Finset.sum_add_distrib, hmain_sum, herr_sum]
      unfold cdem4345_assembled_signedMainWeight cdem4345_assembled_absoluteRemainderWeight
      ring

/-- **Finite Abel identity used by CDEM Lemma 4.**

The left side is the hyperbola-grouped squarefree sum, with the complementary range
bounded by `maxG`.  The right side exposes the signed differences of `Gseq`.  The
assumption `Gseq 0 = 0` records the paper's explicit auxiliary-sequence override. -/
theorem cdem4345_assembled_finite_abel_identity
    (N : ℕ) (Gseq Qseq : ℕ → ℝ) (maxG : ℝ)
    (hG0 : Gseq 0 = 0) :
    (∑ k ∈ Finset.Icc 1 N, Gseq k * (Qseq k - Qseq (k + 1)))
        + maxG * Qseq (N + 1)
      = (∑ k ∈ Finset.Icc 1 N,
          (Gseq k - Gseq (k - 1)) * Qseq k)
          + (maxG - Gseq N) * Qseq (N + 1) := by
  induction N generalizing maxG with
  | zero => simp [hG0]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      have hprev := ih (maxG := Gseq (N + 1))
      calc
        (∑ k ∈ Finset.Icc 1 N, Gseq k * (Qseq k - Qseq (k + 1)))
              + Gseq (N + 1) * (Qseq (N + 1) - Qseq (N + 1 + 1))
              + maxG * Qseq (N + 1 + 1)
            = ((∑ k ∈ Finset.Icc 1 N, Gseq k * (Qseq k - Qseq (k + 1)))
                + Gseq (N + 1) * Qseq (N + 1))
                + (maxG - Gseq (N + 1)) * Qseq (N + 1 + 1) := by ring
        _ = ((∑ k ∈ Finset.Icc 1 N,
                (Gseq k - Gseq (k - 1)) * Qseq k)
              + (Gseq (N + 1) - Gseq N) * Qseq (N + 1))
                + (maxG - Gseq (N + 1)) * Qseq (N + 1 + 1) := by rw [hprev]
        _ = (∑ k ∈ Finset.Icc 1 N,
                (Gseq k - Gseq (k - 1)) * Qseq k)
              + (Gseq (N + 1) - Gseq (N + 1 - 1)) * Qseq (N + 1)
              + (maxG - Gseq (N + 1)) * Qseq (N + 1 + 1) := by
            simp only [Nat.add_sub_cancel]

/-- CDEM's grouped squarefree expression satisfies the signed main/remainder estimate.
This simply composes `cdem4345_assembled_finite_abel_identity` with `cdem4345_assembled_signed_abel_remainder_bound`; it is kept
as a separate theorem so later arithmetic work only has to identify the hyperbola-grouped
sum with this left-hand side. -/
theorem cdem4345_assembled_grouped_squarefree_bound
    (N : ℕ) (Gseq Qseq : ℕ → ℝ)
    (mainCoeff errorCoeff x maxG : ℝ)
    (hG0 : Gseq 0 = 0)
    (hGN_nonneg : 0 ≤ Gseq N)
    (hGN_le : Gseq N ≤ maxG)
    (hQ : ∀ k ∈ Finset.Icc 1 (N + 1),
      |Qseq k - mainCoeff * x / (k : ℝ)|
        ≤ errorCoeff * Real.sqrt x / Real.sqrt k) :
    (∑ k ∈ Finset.Icc 1 N, Gseq k * (Qseq k - Qseq (k + 1)))
        + maxG * Qseq (N + 1)
      ≤ mainCoeff * x * cdem4345_assembled_signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt x * cdem4345_assembled_absoluteRemainderWeight N Gseq maxG := by
  rw [cdem4345_assembled_finite_abel_identity N Gseq Qseq maxG hG0]
  exact cdem4345_assembled_signed_abel_remainder_bound N Gseq Qseq mainCoeff errorCoeff x maxG
    hGN_nonneg hGN_le hQ

/-! ## The fundamental Möbius--floor identity -/

/-- A finite CDEM floor sum.  The denominators are real, not silently coerced naturals:
this covers the paper's nonintegral periodizing denominator. -/
noncomputable def cdem4345_assembled_floorSum {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, coeff i * (⌊y / denominator i⌋₊ : ℝ)

/-- The nonnegative floor-sum error `G(y)=|1-F(y)|` in CDEM Lemma 4. -/
noncomputable def cdem4345_assembled_floorError {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) (y : ℝ) : ℝ :=
  |1 - cdem4345_assembled_floorSum s coeff denominator y|

/-- The exact guard which makes a real denominator harmless for the unit-step table up
to `N`.  An integral denominator is constant on every half-open unit interval.  A
nonintegral denominator is also harmless if it is at least `N+1`, because its floor term
vanishes throughout the tabulated range `[1,N+1)`.

This is the guard needed for the paper's large nonintegral periodizing denominator; it
must not be silently treated as an integer. -/
def cdem4345_assembled_UnitStepDenominatorGuard (N : ℕ) (a : ℝ) : Prop :=
  (∃ d : ℕ, 1 ≤ d ∧ a = d) ∨ (N + 1 : ℕ) ≤ a

/-- A single guarded floor term is constant on every tabulated unit interval. -/
theorem cdem4345_assembled_floor_div_constant_on_unit_of_guard
    (N k : ℕ) (a y : ℝ)
    (hk : k ∈ Finset.Icc 1 N)
    (hy_lower : (k : ℝ) ≤ y)
    (hy_upper : y < k + 1)
    (ha : cdem4345_assembled_UnitStepDenominatorGuard N a) :
    ⌊y / a⌋₊ = ⌊(k : ℝ) / a⌋₊ := by
  rcases ha with ⟨d, hd, rfl⟩ | ha_large
  · have hy0 : 0 ≤ y := (Nat.cast_nonneg k).trans hy_lower
    have hyfloor : ⌊y⌋₊ = k :=
      (Nat.floor_eq_iff hy0).2 ⟨hy_lower, by simpa using hy_upper⟩
    rw [Nat.floor_div_natCast, Nat.floor_div_natCast, hyfloor, Nat.floor_natCast]
  · have ha_pos : 0 < a := by
      have : (0 : ℝ) < (N + 1 : ℕ) := by positivity
      exact this.trans_le ha_large
    have hk_mem : 1 ≤ k ∧ k ≤ N := Finset.mem_Icc.mp hk
    have hkN : k + 1 ≤ N + 1 := Nat.add_le_add_right hk_mem.2 1
    have hkN_real : ((k + 1 : ℕ) : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hkN
    have hy_a : y < a := by
      have hy_upper' : y < ((k + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hy_upper
      exact hy_upper'.trans_le (hkN_real.trans ha_large)
    have hk_a : (k : ℝ) < a := by
      calc
        (k : ℝ) < (k + 1 : ℕ) := by norm_num
        _ ≤ (N + 1 : ℕ) := by exact_mod_cast hkN
        _ ≤ a := ha_large
    rw [Nat.floor_eq_zero.mpr ((div_lt_one ha_pos).2 hy_a),
      Nat.floor_eq_zero.mpr ((div_lt_one ha_pos).2 hk_a)]

/-- Under the explicit integer-or-inactive guard, the complete CDEM floor sum is
constant on `[k,k+1)` for every `1 ≤ k ≤ N`. -/
theorem cdem4345_assembled_floorSum_constant_on_unit_of_guards
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N k : ℕ) (y : ℝ)
    (hk : k ∈ Finset.Icc 1 N)
    (hy_lower : (k : ℝ) ≤ y)
    (hy_upper : y < k + 1)
    (hdenom : ∀ i ∈ s, cdem4345_assembled_UnitStepDenominatorGuard N (denominator i)) :
    cdem4345_assembled_floorSum s coeff denominator y = cdem4345_assembled_floorSum s coeff denominator k := by
  unfold cdem4345_assembled_floorSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [cdem4345_assembled_floor_div_constant_on_unit_of_guard N k (denominator i) y hk hy_lower hy_upper
    (hdenom i hi)]

/-- Consequently the CDEM error `G(y)=|1-F(y)|` has the same unit-step property. -/
theorem cdem4345_assembled_floorError_constant_on_unit_of_guards
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N k : ℕ) (y : ℝ)
    (hk : k ∈ Finset.Icc 1 N)
    (hy_lower : (k : ℝ) ≤ y)
    (hy_upper : y < k + 1)
    (hdenom : ∀ i ∈ s, cdem4345_assembled_UnitStepDenominatorGuard N (denominator i)) :
    cdem4345_assembled_floorError s coeff denominator y = cdem4345_assembled_floorError s coeff denominator k := by
  unfold cdem4345_assembled_floorError
  rw [cdem4345_assembled_floorSum_constant_on_unit_of_guards s coeff denominator N k y hk hy_lower hy_upper
    hdenom]

/-- A scaled form of the PNTA Möbius--floor identity.

For a real denominator `a ≥ 1` which is active at height `x` (`a ≤ x`),

`sum_{n≤x} mu(n) floor((x/n)/a) = 1`.

The upper summation limit is `floor x`, rather than `floor (x/a)`.  Terms in the
difference vanish because `a ≥ 1`.  No integrality assumption on `a` is used. -/
theorem cdem4345_assembled_sum_mobius_scaled_floor
    (x a : ℝ) (ha : 1 ≤ a) (hax : a ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ) * (⌊(x / n) / a⌋₊ : ℝ) = 1 := by
  have hx : 1 ≤ x := ha.trans hax
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have ha0 : 0 < a := one_pos.trans_le ha
  have hy : 1 ≤ x / a := (le_div_iff₀ ha0).2 (by simpa using hax)
  have hy0 : 0 ≤ x / a := zero_le_one.trans hy
  have hfloor : ⌊x / a⌋₊ ≤ ⌊x⌋₊ := by
    exact Nat.floor_mono (div_le_self hx0 ha)
  have hsub : Finset.Icc 1 ⌊x / a⌋₊ ⊆ Finset.Icc 1 ⌊x⌋₊ := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr ⟨hn'.1, hn'.2.trans hfloor⟩
  have hzero : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      n ∉ Finset.Icc 1 ⌊x / a⌋₊ →
      (ArithmeticFunction.moebius n : ℝ) * (⌊(x / n) / a⌋₊ : ℝ) = 0 := by
    intro n hn hnsmall
    have hn' := Finset.mem_Icc.mp hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn'.1
    have hnlarge : ⌊x / a⌋₊ < n := by
      have : ¬n ≤ ⌊x / a⌋₊ := by
        intro hnle
        exact hnsmall (Finset.mem_Icc.mpr ⟨hn'.1, hnle⟩)
      omega
    have hyn : x / a < (n : ℝ) := by
      calc
        x / a < (⌊x / a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
        _ ≤ (n : ℝ) := by exact_mod_cast hnlarge
    have hquot : x / a / (n : ℝ) < 1 := (div_lt_one (by positivity)).2 hyn
    have hrewrite : (x / (n : ℝ)) / a = (x / a) / (n : ℝ) := by
      field_simp
    rw [hrewrite, Nat.floor_eq_zero.mpr hquot, Nat.cast_zero, mul_zero]
  calc
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ) * (⌊(x / n) / a⌋₊ : ℝ))
        = ∑ n ∈ Finset.Icc 1 ⌊x / a⌋₊,
            (ArithmeticFunction.moebius n : ℝ) * (⌊(x / n) / a⌋₊ : ℝ) :=
          (Finset.sum_subset hsub hzero).symm
    _ = ∑ n ∈ Finset.Icc 1 ⌊x / a⌋₊,
          (ArithmeticFunction.moebius n : ℝ) * (⌊(x / a) / n⌋₊ : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn' := Finset.mem_Icc.mp hn
        have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn'.1))
        have ha_ne : a ≠ 0 := ne_of_gt ha0
        congr 2
        field_simp
    _ = 1 := Helfgott.cdem4345_assembled_cdem_moebius_floor_real (x / a) hy

/-- **Fundamental Möbius--floor identity (CDEM Lemma 4, step 1).**

If every denominator in the finite floor sum is at least `1` and no larger than `x`, then

`sum_{n≤x} mu(n) (1 - F(x/n)) = sum_{n≤x} mu(n) - sum_i c_i`.

The upper guard `denominator i ≤ x` is essential.  In the CDEM data one periodizing
denominator is nonintegral and extremely large; below it this theorem cannot be applied
to the full coefficient table.  Such an inactive term must instead be omitted explicitly
(and its coefficient charged to the finite `w` endpoint), exactly as the paper remarks.
This theorem does not use or hide an integrality assumption on denominators. -/
theorem cdem4345_assembled_mobius_floor_fundamental_identity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ) (x : ℝ)
    (hdenom_one : ∀ i ∈ s, 1 ≤ denominator i)
    (hdenom_active : ∀ i ∈ s, denominator i ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ)
          * (1 - cdem4345_assembled_floorSum s coeff denominator (x / n)))
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
          - ∑ i ∈ s, coeff i := by
  have hinner : ∀ i ∈ s,
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.moebius n : ℝ)
            * (coeff i * (⌊(x / n) / denominator i⌋₊ : ℝ))) = coeff i := by
    intro i hi
    calc
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.moebius n : ℝ)
            * (coeff i * (⌊(x / n) / denominator i⌋₊ : ℝ)))
          = coeff i * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius n : ℝ)
                * (⌊(x / n) / denominator i⌋₊ : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            ring
      _ = coeff i := by
        rw [cdem4345_assembled_sum_mobius_scaled_floor x (denominator i)
          (hdenom_one i hi) (hdenom_active i hi), mul_one]
  calc
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ)
          * (1 - cdem4345_assembled_floorSum s coeff denominator (x / n)))
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
          - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ∑ i ∈ s, (ArithmeticFunction.moebius n : ℝ)
                * (coeff i * (⌊(x / n) / denominator i⌋₊ : ℝ)) := by
        unfold cdem4345_assembled_floorSum
        simp_rw [mul_sub, mul_one, Finset.mul_sum]
        rw [Finset.sum_sub_distrib]
    _ = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
          - ∑ i ∈ s, ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              (ArithmeticFunction.moebius n : ℝ)
                * (coeff i * (⌊(x / n) / denominator i⌋₊ : ℝ)) := by
        rw [Finset.sum_comm]
    _ = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
          - ∑ i ∈ s, coeff i := by
        rw [Finset.sum_congr rfl hinner]

/-- Taking absolute values in the fundamental identity replaces `|mu(n)|` by the
squarefree weight.  No cancellation is discarded later in the `Q` main term: that sign
is recovered by the finite Abel identity above. -/
theorem cdem4345_assembled_abs_mobius_floor_fundamental_le_squarefree_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ) (x : ℝ)
    (hdenom_one : ∀ i ∈ s, 1 ≤ denominator i)
    (hdenom_active : ∀ i ∈ s, denominator i ≤ x) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
        - ∑ i ∈ s, coeff i|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)|
            * cdem4345_assembled_floorError s coeff denominator (x / n) := by
  rw [← cdem4345_assembled_mobius_floor_fundamental_identity s coeff denominator x hdenom_one hdenom_active]
  calc
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ)
          * (1 - cdem4345_assembled_floorSum s coeff denominator (x / n))|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)
            * (1 - cdem4345_assembled_floorSum s coeff denominator (x / n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)|
            * cdem4345_assembled_floorError s coeff denominator (x / n) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [abs_mul]
        rfl

/-! ## The hyperbola partition -/

/-- **Exact hyperbola grouping by the value of `floor (x/n)`.**

This is the finite partition used in CDEM Lemma 4.  It is extracted from the same
partition already used by PNTA's `sum_mobius_floor_tail_isLittleO`, but is stated here
for arbitrary real weights.  The interval `(floor(x/K), floor x]` is partitioned into
the fibers where `floor(x/n)=k`, `1 ≤ k < K`.

Taking `K=N+1`, `weight n=|mu(n)|`, and `stepWeight k=G(k)` gives the grouped term

`sum_{k=1}^N G(k) (Q(x/k)-Q(x/(k+1)))`.
-/
theorem cdem4345_assembled_hyperbola_grouping_floor
    (x : ℝ) (K : ℕ) (hK : 0 < K) (hx : 1 ≤ x)
    (weight stepWeight : ℕ → ℝ) :
    (∑ n ∈ Finset.Ioc ⌊x / K⌋₊ ⌊x⌋₊,
        weight n * stepWeight ⌊x / (n : ℝ)⌋₊)
      = ∑ k ∈ Finset.Ico 1 K, stepWeight k
          * ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊, weight n := by
  have hpartition :
      Finset.Ioc ⌊x / (K : ℝ)⌋₊ ⌊x⌋₊
        = Finset.biUnion (Finset.Ico 1 K)
            (fun k => Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_biUnion, Finset.mem_Ico]
    constructor
    · intro hn
      refine ⟨⌊x / n⌋₊, ?_, ?_, ?_⟩
      all_goals generalize_proofs at *
      · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;>
          try linarith [show (n : ℝ) ≥ 1 by norm_cast; linarith]
        exact ⟨by
          rw [le_div_iff₀ (Nat.cast_pos.mpr <| by linarith)]
          nlinarith [Nat.floor_le (show 0 ≤ x by linarith), Nat.lt_floor_add_one x,
            show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2], by
          rw [Nat.floor_lt (by positivity)] at *
          rw [div_lt_iff₀ (by positivity)] at *
          norm_num at *
          linarith⟩
      · rw [Nat.floor_lt', div_lt_iff₀] <;> norm_num <;>
          try linarith [Nat.lt_floor_add_one (x / n)]
        nlinarith [Nat.lt_floor_add_one (x / n),
          show (n : ℝ) ≥ 1 by norm_cast; linarith,
          div_mul_cancel₀ x (show (n : ℝ) ≠ 0 by norm_cast; linarith)]
      · refine Nat.le_floor ?_
        rw [le_div_iff₀] <;> norm_num
        · exact le_trans
            (mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) (Nat.cast_nonneg _))
            (by rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr <| by linarith)])
        · exact Nat.floor_pos.mpr (by
            rw [le_div_iff₀ (Nat.cast_pos.mpr <| pos_of_gt hn.1)]
            nlinarith [Nat.floor_le (show 0 ≤ x by positivity), Nat.lt_floor_add_one x,
              show (n : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn.2,
              div_mul_cancel₀ x (show (K : ℝ) ≠ 0 by positivity)])
    · field_simp
      rintro ⟨a, ⟨ha₁, ha₂⟩, ha₃, ha₄⟩
      refine ⟨lt_of_le_of_lt ?_ ha₃, ha₄.trans ?_⟩
      · gcongr
        norm_cast
      · exact Nat.floor_mono <| div_le_self (by positivity) <| mod_cast ha₁
  rw [hpartition, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hfloor : ⌊x / (n : ℝ)⌋₊ = k := by
      have hk' : 1 ≤ k ∧ k < K := Finset.mem_Ico.mp hk
      have hn' : ⌊x / (k + 1 : ℝ)⌋₊ < n ∧ n ≤ ⌊x / (k : ℝ)⌋₊ :=
        Finset.mem_Ioc.mp hn
      have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk'.1
      have hnpos : 0 < n := by
        exact lt_of_le_of_lt (Nat.zero_le _) hn'.1
      have hn_upper : (n : ℝ) ≤ x / (k : ℝ) :=
        (Nat.le_floor_iff (by positivity)).mp hn'.2
      have hn_lower : x / (k + 1 : ℝ) < (n : ℝ) :=
        (Nat.floor_lt (by positivity)).mp hn'.1
      apply (Nat.floor_eq_iff (by positivity)).mpr
      constructor
      · apply (le_div_iff₀ (Nat.cast_pos.mpr hnpos)).mpr
        have hmul := (le_div_iff₀ (Nat.cast_pos.mpr hkpos)).mp hn_upper
        nlinarith
      · apply (div_lt_iff₀ (Nat.cast_pos.mpr hnpos)).mpr
        have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 1)).mp hn_lower
        nlinarith
    rw [hfloor]
    ring
  · intro k hk l hl hkl
    simp_all +decide [Finset.disjoint_left]
    field_simp
    intro a ha₁ ha₂ ha₃
    contrapose! hkl
    rw [Nat.le_floor_iff (by positivity), Nat.floor_lt (by positivity)] at *
    rw [div_lt_iff₀ (by positivity), le_div_iff₀ (by norm_cast; linarith)] at *
    exact Nat.le_antisymm
      (Nat.le_of_lt_succ <| by
        rw [← @Nat.cast_lt ℝ]
        push_cast
        nlinarith)
      (Nat.le_of_lt_succ <| by
        rw [← @Nat.cast_lt ℝ]
        push_cast
        nlinarith)

/-- The squarefree counting function in the exact weighted form needed by Lemma 4.
The `n=0` term is included only to make interval subtraction literal; it vanishes because
`mu(0)=0`. -/
noncomputable def cdem4345_assembled_squarefreeCount (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), |(ArithmeticFunction.moebius n : ℝ)|

/-- Removing the vanishing `n=0` term recovers the usual interval definition of `Q`. -/
theorem cdem4345_assembled_squarefreeCount_eq_sum_Icc (y : ℝ) :
    cdem4345_assembled_squarefreeCount y
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |(ArithmeticFunction.moebius n : ℝ)| := by
  unfold cdem4345_assembled_squarefreeCount
  rw [show Finset.range (⌊y⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊y⌋₊) by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega,
      Finset.sum_insert (by simp)]
  simp

/-- The complementary small-`n` range is bounded by `maxG * Q(x/(N+1))`.
This is the only use of the global `G≤maxG` bound in the hyperbola split. -/
theorem cdem4345_assembled_floorError_small_n_le_max
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x maxG : ℝ) (hx : 0 ≤ x)
    (hmax : ∀ y : ℝ, 0 ≤ y → cdem4345_assembled_floorError s coeff denominator y ≤ maxG) :
    (∑ n ∈ Finset.Icc 1 ⌊x / (N + 1 : ℕ)⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * cdem4345_assembled_floorError s coeff denominator (x / n))
      ≤ maxG * cdem4345_assembled_squarefreeCount (x / (N + 1 : ℕ)) := by
  rw [cdem4345_assembled_squarefreeCount_eq_sum_Icc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  rw [mul_comm maxG]
  exact mul_le_mul_of_nonneg_left
    (hmax (x / n) (div_nonneg hx (Nat.cast_nonneg n))) (abs_nonneg _)

/-- A hyperbola fiber is the difference of two squarefree counts. -/
theorem cdem4345_assembled_squarefreeCount_sub_eq_sum_fiber
    (x : ℝ) (k : ℕ) (hx : 0 ≤ x) (hk : 1 ≤ k) :
    cdem4345_assembled_squarefreeCount (x / k) - cdem4345_assembled_squarefreeCount (x / (k + 1 : ℕ))
      = ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℕ)⌋₊ ⌊x / k⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)| := by
  have hdiv : x / (k + 1 : ℕ) ≤ x / k := by
    gcongr
    norm_cast
    omega
  have hfloor : ⌊x / (k + 1 : ℕ)⌋₊ ≤ ⌊x / k⌋₊ := Nat.floor_mono hdiv
  rw [← Finset.Ico_add_one_add_one_eq_Ioc]
  unfold cdem4345_assembled_squarefreeCount
  exact (Finset.sum_Ico_eq_sub (f := fun n => |(ArithmeticFunction.moebius n : ℝ)|)
    (Nat.add_le_add_right hfloor 1)).symm

/-- Hyperbola grouping for the actual CDEM error function `G(y)=|1-F(y)|`.

The integer-or-inactive denominator guard is threaded explicitly: it is what permits
replacing `G(x/n)` by `G(floor(x/n))` on the grouped range. -/
theorem cdem4345_assembled_floorError_hyperbola_grouping
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hdenom : ∀ i ∈ s, cdem4345_assembled_UnitStepDenominatorGuard N (denominator i)) :
    (∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * cdem4345_assembled_floorError s coeff denominator (x / n))
      = ∑ k ∈ Finset.Icc 1 N, cdem4345_assembled_floorError s coeff denominator k
          * ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊,
              |(ArithmeticFunction.moebius n : ℝ)| := by
  have hreplace :
      (∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)|
            * cdem4345_assembled_floorError s coeff denominator (x / n))
        = ∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
            |(ArithmeticFunction.moebius n : ℝ)|
              * cdem4345_assembled_floorError s coeff denominator ⌊x / (n : ℝ)⌋₊ := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' : ⌊x / (N + 1 : ℕ)⌋₊ < n ∧ n ≤ ⌊x⌋₊ := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by
      exact lt_of_le_of_lt (Nat.zero_le _) hn'.1
    have hk : ⌊x / (n : ℝ)⌋₊ ∈ Finset.Icc 1 N := by
      apply Finset.mem_Icc.mpr
      constructor
      · apply (Nat.le_floor_iff (by positivity)).mpr
        apply (le_div_iff₀ (Nat.cast_pos.mpr hnpos)).mpr
        have hn_le_x : (n : ℝ) ≤ x :=
          (Nat.le_floor_iff (by positivity)).mp hn'.2
        simpa using hn_le_x
      · rw [← Nat.lt_add_one_iff]
        apply (Nat.floor_lt (by positivity)).mpr
        apply (div_lt_iff₀ (Nat.cast_pos.mpr hnpos)).mpr
        have hn_lower : x / ((N + 1 : ℕ) : ℝ) < (n : ℝ) :=
          (Nat.floor_lt (by positivity)).mp hn'.1
        have hmul :=
          (div_lt_iff₀ (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))).mp hn_lower
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hmul
    have hy0 : 0 ≤ x / (n : ℝ) := by positivity
    have hy_lower : (⌊x / (n : ℝ)⌋₊ : ℝ) ≤ x / (n : ℝ) := Nat.floor_le hy0
    have hy_upper : x / (n : ℝ) < (⌊x / (n : ℝ)⌋₊ : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    rw [cdem4345_assembled_floorError_constant_on_unit_of_guards s coeff denominator N
      ⌊x / (n : ℝ)⌋₊ (x / (n : ℝ)) hk hy_lower hy_upper hdenom]
  rw [hreplace]
  have hgroup := cdem4345_assembled_hyperbola_grouping_floor x (N + 1) (Nat.succ_pos N) hx
    (fun n => |(ArithmeticFunction.moebius n : ℝ)|)
    (fun k => cdem4345_assembled_floorError s coeff denominator k)
  rw [Finset.Ico_add_one_right_eq_Icc] at hgroup
  exact hgroup

/-- The same grouping in the paper's displayed `Q(x/k)-Q(x/(k+1))` notation. -/
theorem cdem4345_assembled_floorError_hyperbola_grouping_squarefreeCount
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hdenom : ∀ i ∈ s, cdem4345_assembled_UnitStepDenominatorGuard N (denominator i)) :
    (∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * cdem4345_assembled_floorError s coeff denominator (x / n))
      = ∑ k ∈ Finset.Icc 1 N, cdem4345_assembled_floorError s coeff denominator k
          * (cdem4345_assembled_squarefreeCount (x / k) - cdem4345_assembled_squarefreeCount (x / (k + 1 : ℕ))) := by
  rw [cdem4345_assembled_floorError_hyperbola_grouping s coeff denominator N x hx hdenom]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  rw [cdem4345_assembled_squarefreeCount_sub_eq_sum_fiber x k (zero_le_one.trans hx) hk'.1]
  norm_num [Nat.cast_add, Nat.cast_one]

/-- **CDEM Lemma 4, hyperbola/absolute-value step.**

After replacing `|mu(n)|` by squarefree increments, split at `x/(N+1)`.  The
large-`n` part is grouped exactly by `floor(x/n)`; only the complementary small-`n`
part uses the global bound `G≤maxG`. -/
theorem cdem4345_assembled_floorError_squarefree_sum_le_grouped
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x maxG : ℝ) (hx : 1 ≤ x)
    (hdenom : ∀ i ∈ s, cdem4345_assembled_UnitStepDenominatorGuard N (denominator i))
    (hmax : ∀ y : ℝ, 0 ≤ y → cdem4345_assembled_floorError s coeff denominator y ≤ maxG) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * cdem4345_assembled_floorError s coeff denominator (x / n))
      ≤ (∑ k ∈ Finset.Icc 1 N, cdem4345_assembled_floorError s coeff denominator k
          * (cdem4345_assembled_squarefreeCount (x / k) - cdem4345_assembled_squarefreeCount (x / (k + 1 : ℕ))))
        + maxG * cdem4345_assembled_squarefreeCount (x / (N + 1 : ℕ)) := by
  have hfloor : ⌊x / (N + 1 : ℕ)⌋₊ ≤ ⌊x⌋₊ := by
    apply Nat.floor_mono
    exact div_le_self (zero_le_one.trans hx) (by norm_num)
  have hsets :
      Finset.Icc 1 ⌊x⌋₊
        = Finset.Icc 1 ⌊x / (N + 1 : ℕ)⌋₊
            ∪ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisjoint :
      Disjoint (Finset.Icc 1 ⌊x / (N + 1 : ℕ)⌋₊)
        (Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    have hn₁' := Finset.mem_Icc.mp hn₁
    have hn₂' := Finset.mem_Ioc.mp hn₂
    omega
  rw [hsets, Finset.sum_union hdisjoint,
    cdem4345_assembled_floorError_hyperbola_grouping_squarefreeCount s coeff denominator N x hx hdenom]
  have hsmall := cdem4345_assembled_floorError_small_n_le_max s coeff denominator N x maxG
    (zero_le_one.trans hx) hmax
  linarith

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A global triangle bound for normalized CDEM floor sums

If the affine part of a finite floor sum cancels exactly,

```text
sum_i c_i / a_i = 0,
```

then for nonnegative `y`

```text
sum_i c_i floor(y/a_i) = -sum_i c_i fract(y/a_i).
```

Consequently its CDEM error is globally bounded by
`1 + sum_i |c_i|`.  This replaces the missing period table in the
reproducible Mobius-prefix construction: it is a theorem for every
nonnegative real argument, not a computational certificate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- Exact fractional-part expansion of a normalized finite floor sum. -/
theorem cdem4345_assembled_floorSum_eq_neg_fract_sum_of_normalized
    {iota : Type*} [DecidableEq iota]
    (s : Finset iota) (coeff denominator : iota -> Real) (y : Real)
    (hy : 0 <= y)
    (hdenom : ∀ i ∈ s, 0 < denominator i)
    (hnormalized : ∑ i ∈ s, coeff i / denominator i = 0) :
    cdem4345_assembled_floorSum s coeff denominator y =
      -∑ i ∈ s, coeff i * Int.fract (y / denominator i) := by
  have hterm : ∀ i ∈ s,
      coeff i * (⌊y / denominator i⌋₊ : Real) =
        y * (coeff i / denominator i) -
          coeff i * Int.fract (y / denominator i) := by
    intro i hi
    have ht : 0 <= y / denominator i := div_nonneg hy (hdenom i hi).le
    have hfloor : (⌊y / denominator i⌋₊ : Real) =
        y / denominator i - Int.fract (y / denominator i) := by
      rw [show (⌊y / denominator i⌋₊ : Real) =
          (⌊y / denominator i⌋ : Int) by
        rw [← Int.floor_toNat]
        exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr ht)]
      linarith [Int.fract_add_floor (y / denominator i)]
    rw [hfloor]
    ring
  unfold cdem4345_assembled_floorSum
  calc
    ∑ i ∈ s, coeff i * (⌊y / denominator i⌋₊ : Real) =
        ∑ i ∈ s, (y * (coeff i / denominator i) -
          coeff i * Int.fract (y / denominator i)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = y * (∑ i ∈ s, coeff i / denominator i) -
        ∑ i ∈ s, coeff i * Int.fract (y / denominator i) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = -∑ i ∈ s, coeff i * Int.fract (y / denominator i) := by
      rw [hnormalized, mul_zero, zero_sub]

/-- A normalized finite floor sum has the global bound
`G(y) <= 1 + sum_i |c_i|` throughout the nonnegative half-line. -/
theorem cdem4345_assembled_floorError_global_le_one_add_sum_abs_of_normalized
    {iota : Type*} [DecidableEq iota]
    (s : Finset iota) (coeff denominator : iota -> Real)
    (hdenom : ∀ i ∈ s, 0 < denominator i)
    (hnormalized : ∑ i ∈ s, coeff i / denominator i = 0) :
    forall y : Real, 0 <= y ->
      cdem4345_assembled_floorError s coeff denominator y <= 1 + ∑ i ∈ s, |coeff i| := by
  intro y hy
  rw [cdem4345_assembled_floorError, cdem4345_assembled_floorSum_eq_neg_fract_sum_of_normalized s coeff denominator y hy
    hdenom hnormalized]
  have hsum :
      |∑ i ∈ s, coeff i * Int.fract (y / denominator i)| <=
        ∑ i ∈ s, |coeff i| := by
    calc
      |∑ i ∈ s, coeff i * Int.fract (y / denominator i)| <=
          ∑ i ∈ s, |coeff i * Int.fract (y / denominator i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ i ∈ s, |coeff i| := by
        apply Finset.sum_le_sum
        intro i hi
        have hfractabs : |Int.fract (y / denominator i)| =
            Int.fract (y / denominator i) :=
          abs_of_nonneg (Int.fract_nonneg _)
        rw [abs_mul, hfractabs]
        exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  calc
    |1 - -∑ i ∈ s, coeff i * Int.fract (y / denominator i)| =
        |1 + ∑ i ∈ s, coeff i * Int.fract (y / denominator i)| := by ring_nf
    _ <= |(1 : Real)| + |∑ i ∈ s, coeff i * Int.fract (y / denominator i)| :=
      abs_add_le _ _
    _ <= 1 + ∑ i ∈ s, |coeff i| := by
      simpa only [abs_one] using add_le_add_right hsum 1

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000

/-!
# Cohen--Dress--El Marraki Lemma 4: pointwise comparison

This adaptation composes the signed finite Abel core into the pointwise inequality
used by the 2007 paper. It contains no historical numerical row or computational
assumption. Every coefficient table, denominator guard and global floor-error bound
is an explicit argument, as are the squarefree remainder estimates at the sampled
arguments. The Mobius-floor identity is independently proved from Mathlib.
-/

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- The paper's overridden Abel sequence: `Gseq(0)=0`, while `Gseq(k)=G(k)` for
positive `k`. -/
noncomputable def cdem4345_assembled_errorSeq {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else cdem4345_assembled_floorError s coeff denominator k

@[simp] theorem errorSeq_zero {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) :
    cdem4345_assembled_errorSeq s coeff denominator 0 = 0 := by
  simp [cdem4345_assembled_errorSeq]

theorem cdem4345_assembled_errorSeq_eq_floorError {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) {k : ℕ} (hk : k ≠ 0) :
    cdem4345_assembled_errorSeq s coeff denominator k = cdem4345_assembled_floorError s coeff denominator k := by
  simp [cdem4345_assembled_errorSeq, hk]

/-- **Pointwise CDEM Lemma 4.**

All six elementary steps are now composed: the Möbius--floor identity, absolute-value
squarefree replacement, hyperbola grouping, signed Abel transformation, squarefree
main/remainder separation, and the coefficient-sum endpoint `w`.

The squarefree input is sampled at exactly the finite set `k=1,...,N+1`. A caller
can derive these samples from a genuine squarefree remainder theorem. -/
theorem cdem4345_assembled_lemma4_pointwise
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N X : ℕ) (mainCoeff errorCoeff maxG : ℝ)
    (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hdenom_one : ∀ i ∈ s, 1 ≤ denominator i)
    (hdenom_active : ∀ i ∈ s, denominator i ≤ (X : ℝ))
    (hdenom_step : ∀ i ∈ s, cdem4345_assembled_UnitStepDenominatorGuard N (denominator i))
    (hmax : ∀ y : ℝ, 0 ≤ y → cdem4345_assembled_floorError s coeff denominator y ≤ maxG)
    (hQ : ∀ k ∈ Finset.Icc 1 (N + 1),
      |cdem4345_assembled_squarefreeCount ((X : ℝ) / k) - mainCoeff * (X : ℝ) / (k : ℝ)|
        ≤ errorCoeff * Real.sqrt (X : ℝ) / Real.sqrt k) :
    |(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ))|
      ≤ mainCoeff * (X : ℝ) * cdem4345_assembled_signedMainWeight N (cdem4345_assembled_errorSeq s coeff denominator) maxG
          + errorCoeff * Real.sqrt (X : ℝ)
              * cdem4345_assembled_absoluteRemainderWeight N (cdem4345_assembled_errorSeq s coeff denominator) maxG
          + |∑ i ∈ s, coeff i| := by
  let Gseq : ℕ → ℝ := cdem4345_assembled_errorSeq s coeff denominator
  let Qseq : ℕ → ℝ := fun k => cdem4345_assembled_squarefreeCount ((X : ℝ) / k)
  have hfund := cdem4345_assembled_abs_mobius_floor_fundamental_le_squarefree_sum
    s coeff denominator (X : ℝ) hdenom_one hdenom_active
  have hfund' :
      |(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ)) - ∑ i ∈ s, coeff i|
        ≤ ∑ n ∈ Finset.Icc 1 X,
            |(ArithmeticFunction.moebius n : ℝ)|
              * cdem4345_assembled_floorError s coeff denominator ((X : ℝ) / n) := by
    simpa [Nat.floor_natCast] using hfund
  have hhyper := cdem4345_assembled_floorError_squarefree_sum_le_grouped
    s coeff denominator N (X : ℝ) maxG (by exact_mod_cast hX)
    hdenom_step hmax
  have hGN_nonneg : 0 ≤ Gseq N := by
    rw [show Gseq N = cdem4345_assembled_floorError s coeff denominator N by
      exact cdem4345_assembled_errorSeq_eq_floorError s coeff denominator (by omega)]
    exact abs_nonneg _
  have hGN_le : Gseq N ≤ maxG := by
    rw [show Gseq N = cdem4345_assembled_floorError s coeff denominator N by
      exact cdem4345_assembled_errorSeq_eq_floorError s coeff denominator (by omega)]
    exact hmax N (by positivity)
  have habel := cdem4345_assembled_grouped_squarefree_bound N Gseq Qseq mainCoeff errorCoeff (X : ℝ) maxG
    (by simp [Gseq]) hGN_nonneg hGN_le hQ
  have hgroup_eq :
      (∑ k ∈ Finset.Icc 1 N, cdem4345_assembled_floorError s coeff denominator k
          * (cdem4345_assembled_squarefreeCount ((X : ℝ) / k)
              - cdem4345_assembled_squarefreeCount ((X : ℝ) / (k + 1 : ℕ))))
          + maxG * cdem4345_assembled_squarefreeCount ((X : ℝ) / (N + 1 : ℕ))
        = (∑ k ∈ Finset.Icc 1 N, Gseq k * (Qseq k - Qseq (k + 1)))
          + maxG * Qseq (N + 1) := by
    apply congrArg (fun z : ℝ => z + maxG * cdem4345_assembled_squarefreeCount ((X : ℝ) / (N + 1 : ℕ)))
    apply Finset.sum_congr rfl
    intro k hk
    rw [show Gseq k = cdem4345_assembled_floorError s coeff denominator k by
      exact cdem4345_assembled_errorSeq_eq_floorError s coeff denominator
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1))]
  have hanalytic :
      (∑ n ∈ Finset.Icc 1 X,
          |(ArithmeticFunction.moebius n : ℝ)|
            * cdem4345_assembled_floorError s coeff denominator ((X : ℝ) / n))
        ≤ mainCoeff * (X : ℝ) * cdem4345_assembled_signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt (X : ℝ) * cdem4345_assembled_absoluteRemainderWeight N Gseq maxG := by
    calc
      (∑ n ∈ Finset.Icc 1 X,
          |(ArithmeticFunction.moebius n : ℝ)|
            * cdem4345_assembled_floorError s coeff denominator ((X : ℝ) / n))
        ≤ (∑ k ∈ Finset.Icc 1 N, cdem4345_assembled_floorError s coeff denominator k
            * (cdem4345_assembled_squarefreeCount ((X : ℝ) / k)
                - cdem4345_assembled_squarefreeCount ((X : ℝ) / (k + 1 : ℕ))))
            + maxG * cdem4345_assembled_squarefreeCount ((X : ℝ) / (N + 1 : ℕ)) := by
          simpa [Nat.floor_natCast] using hhyper
      _ = (∑ k ∈ Finset.Icc 1 N, Gseq k * (Qseq k - Qseq (k + 1)))
            + maxG * Qseq (N + 1) := hgroup_eq
      _ ≤ mainCoeff * (X : ℝ) * cdem4345_assembled_signedMainWeight N Gseq maxG
            + errorCoeff * Real.sqrt (X : ℝ)
                * cdem4345_assembled_absoluteRemainderWeight N Gseq maxG := habel
  have htriangle :
      |(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ))|
        ≤ |(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ)) - ∑ i ∈ s, coeff i|
            + |∑ i ∈ s, coeff i| := by
    calc
      |(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ))|
        = |((∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ)) - ∑ i ∈ s, coeff i)
            + ∑ i ∈ s, coeff i| := by ring_nf
      _ ≤ |(∑ n ∈ Finset.Icc 1 X, (ArithmeticFunction.moebius n : ℝ)) - ∑ i ∈ s, coeff i|
            + |∑ i ∈ s, coeff i| := abs_add_le _ _
  exact htriangle.trans <| (add_le_add_left (hfund'.trans hanalytic) _)


end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A reproducible CDEM coefficient table

For natural numbers `K < A`, take the denominator support

```text
{1,...,K} union {A}.
```

The first block has coefficient `mu(d)`.  Put

```text
S_K = sum_{d=1}^K mu(d)/d
```

and give the final term coefficient `-A*S_K`.  Its denominator is the integer
`A`, so the complete table has exact affine cancellation.  If `A>N`, the
periodizer is inactive at every integer sampled by an aggregate certificate
through `N`.  No coefficient file from the 2007 paper is used.

The global floor-error bound is derived from
`cdem4345_assembled_floorError_global_le_one_add_sum_abs_of_normalized`; only the two explicitly
bounded aggregate sums through `N` remain certificate-shaped.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- `S_K = sum_{d<=K} mu(d)/d`, represented exactly in `Real`. -/
noncomputable def cdem4345_assembled_mobiusPrefixReciprocal (K : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : Real) / d

/-- The absolute coefficient mass of the Mobius prefix. -/
noncomputable def cdem4345_assembled_mobiusPrefixMass (K : Nat) : Real :=
  ∑ d ∈ Finset.Icc 1 K, |(ArithmeticFunction.moebius d : Real)|

/-- Denominator labels for the Mobius prefix and its one periodizer. -/
def cdem4345_assembled_reproducibleSupport (K A : Nat) : Finset Nat := Finset.Icc 1 K ∪ {A}

/-- Prefix coefficients are `mu(d)`; the coefficient at `A` is `-A*S_K`. -/
noncomputable def cdem4345_assembled_reproducibleCoeff (K A d : Nat) : Real :=
  if d = A then -(A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K
  else (ArithmeticFunction.moebius d : Real)

/-- Every support label is also its (integral) denominator. -/
noncomputable def cdem4345_assembled_reproducibleDenominator (d : Nat) : Real := d

/-- The theorem-level global triangle bound for this table. -/
noncomputable def cdem4345_assembled_reproducibleMaxG (K A : Nat) : Real :=
  1 + cdem4345_assembled_mobiusPrefixMass K + |(A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K|

/-- Exact endpoint coefficient sum charged by CDEM Lemma 4. -/
noncomputable def cdem4345_assembled_reproducibleCoeffTotal (K A : Nat) : Real :=
  (∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : Real)) -
    (A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K

theorem cdem4345_assembled_reproducibleSupport_disjoint (K A : Nat) (hKA : K < A) :
    Disjoint (Finset.Icc 1 K) ({A} : Finset Nat) := by
  simp only [Finset.disjoint_singleton_right, Finset.mem_Icc, not_and]
  intro _
  omega

theorem cdem4345_assembled_reproducibleCoeff_prefix {K A d : Nat} (hKA : K < A)
    (hd : d ∈ Finset.Icc 1 K) :
    cdem4345_assembled_reproducibleCoeff K A d = (ArithmeticFunction.moebius d : Real) := by
  unfold cdem4345_assembled_reproducibleCoeff
  rw [if_neg]
  intro h
  subst d
  have hdK := (Finset.mem_Icc.mp hd).2
  omega

@[simp] theorem reproducibleCoeff_periodizer (K A : Nat) :
    cdem4345_assembled_reproducibleCoeff K A A = -(A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K := by
  simp [cdem4345_assembled_reproducibleCoeff]

@[simp] theorem reproducibleDenominator_apply (d : Nat) :
    cdem4345_assembled_reproducibleDenominator d = (d : Real) := rfl

/-- The periodizer makes the affine coefficient sum exactly zero. -/
theorem cdem4345_assembled_reproducible_normalized (K A : Nat) (hKA : K < A) :
    ∑ d ∈ cdem4345_assembled_reproducibleSupport K A,
        cdem4345_assembled_reproducibleCoeff K A d / cdem4345_assembled_reproducibleDenominator d = 0 := by
  have hApos : (0 : Real) < A := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le K) hKA)
  rw [cdem4345_assembled_reproducibleSupport, Finset.sum_union (cdem4345_assembled_reproducibleSupport_disjoint K A hKA)]
  rw [Finset.sum_singleton]
  have hprefix :
      (∑ d ∈ Finset.Icc 1 K,
        cdem4345_assembled_reproducibleCoeff K A d / cdem4345_assembled_reproducibleDenominator d) =
        cdem4345_assembled_mobiusPrefixReciprocal K := by
    unfold cdem4345_assembled_mobiusPrefixReciprocal
    apply Finset.sum_congr rfl
    intro d hd
    rw [cdem4345_assembled_reproducibleCoeff_prefix hKA hd, reproducibleDenominator_apply]
  rw [hprefix, reproducibleCoeff_periodizer, reproducibleDenominator_apply]
  field_simp [ne_of_gt hApos]
  ring

theorem cdem4345_assembled_reproducible_denominator_pos (K A : Nat) (hKA : K < A) :
    ∀ d ∈ cdem4345_assembled_reproducibleSupport K A, 0 < cdem4345_assembled_reproducibleDenominator d := by
  intro d hd
  rw [cdem4345_assembled_reproducibleSupport, Finset.mem_union, Finset.mem_Icc,
    Finset.mem_singleton] at hd
  rw [reproducibleDenominator_apply]
  rcases hd with hd | rfl
  · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd.1)
  · exact_mod_cast (lt_of_le_of_lt (Nat.zero_le K) hKA)

theorem cdem4345_assembled_reproducible_denominator_one (K A : Nat) (hKA : K < A) :
    ∀ d ∈ cdem4345_assembled_reproducibleSupport K A, 1 <= cdem4345_assembled_reproducibleDenominator d := by
  have hAone : 1 <= A := by omega
  intro d hd
  rw [cdem4345_assembled_reproducibleSupport, Finset.mem_union, Finset.mem_Icc,
    Finset.mem_singleton] at hd
  rw [reproducibleDenominator_apply]
  rcases hd with hd | rfl
  · exact_mod_cast hd.1
  · exact_mod_cast hAone

/-- Exact trace of the endpoint coefficient sum. -/
theorem cdem4345_assembled_reproducible_coeff_total (K A : Nat) (hKA : K < A) :
    ∑ d ∈ cdem4345_assembled_reproducibleSupport K A, cdem4345_assembled_reproducibleCoeff K A d =
      cdem4345_assembled_reproducibleCoeffTotal K A := by
  rw [cdem4345_assembled_reproducibleSupport, Finset.sum_union (cdem4345_assembled_reproducibleSupport_disjoint K A hKA),
    Finset.sum_singleton]
  unfold cdem4345_assembled_reproducibleCoeffTotal
  rw [reproducibleCoeff_periodizer]
  have hsum :
      (∑ d ∈ Finset.Icc 1 K, cdem4345_assembled_reproducibleCoeff K A d) =
        ∑ d ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius d : Real) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact cdem4345_assembled_reproducibleCoeff_prefix hKA hd
  rw [hsum]
  ring

/-- Exact trace of the absolute coefficient mass. -/
theorem cdem4345_assembled_reproducible_coeff_mass (K A : Nat) (hKA : K < A) :
    ∑ d ∈ cdem4345_assembled_reproducibleSupport K A, |cdem4345_assembled_reproducibleCoeff K A d| =
      cdem4345_assembled_mobiusPrefixMass K + |(A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K| := by
  rw [cdem4345_assembled_reproducibleSupport, Finset.sum_union (cdem4345_assembled_reproducibleSupport_disjoint K A hKA),
    Finset.sum_singleton]
  unfold cdem4345_assembled_mobiusPrefixMass
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    rw [cdem4345_assembled_reproducibleCoeff_prefix hKA hd]
  · rw [reproducibleCoeff_periodizer]
    have heq : -(A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K =
        -((A : Real) * cdem4345_assembled_mobiusPrefixReciprocal K) := by ring
    rw [heq, abs_neg]

/-- Global floor-error control with no period or breakpoint table. -/
theorem cdem4345_assembled_reproducible_globalMax (K A : Nat) (hKA : K < A) :
    forall y : Real, 0 <= y ->
      cdem4345_assembled_floorError (cdem4345_assembled_reproducibleSupport K A) (cdem4345_assembled_reproducibleCoeff K A)
          cdem4345_assembled_reproducibleDenominator y <= cdem4345_assembled_reproducibleMaxG K A := by
  intro y hy
  have h := cdem4345_assembled_floorError_global_le_one_add_sum_abs_of_normalized
    (cdem4345_assembled_reproducibleSupport K A) (cdem4345_assembled_reproducibleCoeff K A) cdem4345_assembled_reproducibleDenominator
    (cdem4345_assembled_reproducible_denominator_pos K A hKA) (cdem4345_assembled_reproducible_normalized K A hKA) y hy
  rw [cdem4345_assembled_reproducible_coeff_mass K A hKA] at h
  simpa only [cdem4345_assembled_reproducibleMaxG, add_assoc] using h

/-- All table denominators satisfy the unit-step guard, because they are integers. -/
theorem cdem4345_assembled_reproducible_denominator_step (K A N : Nat) (hKA : K < A) :
    ∀ d ∈ cdem4345_assembled_reproducibleSupport K A,
      cdem4345_assembled_UnitStepDenominatorGuard N (cdem4345_assembled_reproducibleDenominator d) := by
  intro d hd
  left
  have hd1R := cdem4345_assembled_reproducible_denominator_one K A hKA d hd
  rw [reproducibleDenominator_apply] at hd1R
  have hd1 : 1 <= d := by exact_mod_cast hd1R
  exact ⟨d, hd1, reproducibleDenominator_apply d⟩

theorem cdem4345_assembled_reproducible_denominator_le_A (K A : Nat) (hKA : K < A) :
    ∀ d ∈ cdem4345_assembled_reproducibleSupport K A, cdem4345_assembled_reproducibleDenominator d <= (A : Real) := by
  intro d hd
  rw [cdem4345_assembled_reproducibleSupport, Finset.mem_union, Finset.mem_Icc,
    Finset.mem_singleton] at hd
  rw [reproducibleDenominator_apply]
  rcases hd with hd | rfl
  · exact_mod_cast hd.2.trans hKA.le
  · exact le_rfl

theorem cdem4345_assembled_reproducible_denominator_le_tau (K A : Nat) (tau : Real)
    (hKA : K < A) (hAtau : (A : Real) <= tau) :
    ∀ d ∈ cdem4345_assembled_reproducibleSupport K A, cdem4345_assembled_reproducibleDenominator d <= tau := by
  intro d hd
  exact (cdem4345_assembled_reproducible_denominator_le_A K A hKA d hd).trans hAtau

/-- The floor sum formed only from the Mobius prefix. -/
noncomputable def cdem4345_assembled_mobiusPrefixFloorSum (K : Nat) (y : Real) : Real :=
  ∑ d ∈ Finset.Icc 1 K,
    (ArithmeticFunction.moebius d : Real) * (⌊y / (d : Real)⌋₊ : Real)

/-- The added denominator contributes zero below `A`. -/
theorem cdem4345_assembled_reproducible_periodizer_inactive (A : Nat) {y : Real}
    (hy : 0 <= y) (hyA : y < A) :
    ⌊y / cdem4345_assembled_reproducibleDenominator A⌋₊ = 0 := by
  rw [reproducibleDenominator_apply]
  have hApos : (0 : Real) < A := lt_of_le_of_lt hy hyA
  exact Nat.floor_eq_zero.mpr ((div_lt_one hApos).2 hyA)

/-- Below the added denominator, the full table is exactly the Mobius-prefix table. -/
theorem cdem4345_assembled_reproducible_floorSum_eq_prefix (K A : Nat) (hKA : K < A)
    {y : Real} (hy : 0 <= y) (hyA : y < A) :
    cdem4345_assembled_floorSum (cdem4345_assembled_reproducibleSupport K A) (cdem4345_assembled_reproducibleCoeff K A)
        cdem4345_assembled_reproducibleDenominator y = cdem4345_assembled_mobiusPrefixFloorSum K y := by
  unfold cdem4345_assembled_floorSum cdem4345_assembled_mobiusPrefixFloorSum
  rw [cdem4345_assembled_reproducibleSupport,
    Finset.sum_union (cdem4345_assembled_reproducibleSupport_disjoint K A hKA), Finset.sum_singleton]
  have hprefix :
      (∑ x ∈ Finset.Icc 1 K,
        cdem4345_assembled_reproducibleCoeff K A x * (↑⌊y / cdem4345_assembled_reproducibleDenominator x⌋₊ : Real)) =
      ∑ d ∈ Finset.Icc 1 K,
        (ArithmeticFunction.moebius d : Real) * (↑⌊y / (d : Real)⌋₊ : Real) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [cdem4345_assembled_reproducibleCoeff_prefix hKA hd, reproducibleDenominator_apply]
  rw [hprefix, cdem4345_assembled_reproducible_periodizer_inactive A hy hyA, Nat.cast_zero, mul_zero, add_zero]

/-! ## Explicitly bounded aggregate certificate shapes -/

/-- A bounded computation of the signed Abel weight through the displayed `N`. -/
def cdem4345_assembled_ReproducibleSignedMainCertificate (K A N : Nat) (bound : Real) : Prop :=
  cdem4345_assembled_signedMainWeight N
      (cdem4345_assembled_errorSeq (cdem4345_assembled_reproducibleSupport K A) (cdem4345_assembled_reproducibleCoeff K A)
        cdem4345_assembled_reproducibleDenominator)
      (cdem4345_assembled_reproducibleMaxG K A) <= bound

/-- A bounded computation of the absolute remainder weight through the displayed `N`. -/
def cdem4345_assembled_ReproducibleAbsoluteRemainderCertificate (K A N : Nat) (bound : Real) : Prop :=
  cdem4345_assembled_absoluteRemainderWeight N
      (cdem4345_assembled_errorSeq (cdem4345_assembled_reproducibleSupport K A) (cdem4345_assembled_reproducibleCoeff K A)
        cdem4345_assembled_reproducibleDenominator)
      (cdem4345_assembled_reproducibleMaxG K A) <= bound

end MathExtras.CohenDressElMarraki
end

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators
namespace Helfgott

lemma cdem4345_assembled_reciprocal_integer_rounding_error (Q n : ℕ) (a : ℤ)
    (hQ : 0 < Q) (hn : 0 < n) (ha : |a| ≤ 1) :
    |(a : ℝ) / (n : ℝ) - (a : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)| ≤
      1 / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have har : |(a : ℝ)| ≤ 1 := by exact_mod_cast ha
  have hf : |(Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ)| ≤ 1 := by
    simpa only [Nat.floor_div_eq_div] using
      (Nat.abs_sub_floor_le (a := (Q : ℝ) / (n : ℝ)) (by positivity))
  have he : (a : ℝ) / (n : ℝ) - (a : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ) =
      (a : ℝ) * ((Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ)) / (Q : ℝ) := by
    field_simp
  rw [he, abs_div, abs_mul, abs_of_pos hQr]
  exact div_le_div_of_nonneg_right
    (by nlinarith [abs_nonneg (a : ℝ), abs_nonneg ((Q : ℝ) / (n : ℝ) - ((Q / n : ℕ) : ℝ))]) hQr.le

theorem cdem4345_assembled_moebius_reciprocal_rounded_sum_error (Q N : ℕ) (hQ : 0 < Q) :
    |(∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) -
      (((∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) : ℤ) : ℝ) / (Q : ℝ)| ≤
      (N : ℝ) / (Q : ℝ) := by
  have he : (∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) -
      (((∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) : ℤ) : ℝ) / (Q : ℝ) =
      ∑ n ∈ Finset.Icc 1 N,
        (((moebius n : ℤ) : ℝ) / (n : ℝ) -
          ((moebius n : ℤ) : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)) := by
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  rw [he]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        |((moebius n : ℤ) : ℝ) / (n : ℝ) -
          ((moebius n : ℤ) : ℝ) * ((Q / n : ℕ) : ℝ) / (Q : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, 1 / (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact cdem4345_assembled_reciprocal_integer_rounding_error Q n (moebius n) hQ
        (by have := (Finset.mem_Icc.mp hn).1; omega) abs_moebius_le_one
    _ = (N : ℝ) / (Q : ℝ) := by simp [Nat.card_Icc, div_eq_mul_inv]

theorem cdem4345_assembled_moebius_reciprocal_of_rounded_sum (Q N : ℕ) (S : ℤ) (hQ : 0 < Q)
    (hS : S = ∑ n ∈ Finset.Icc 1 N, (moebius n : ℤ) * (Q / n : ℕ)) :
    |∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)| ≤
      ((S.natAbs : ℝ) + (N : ℝ)) / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have he := cdem4345_assembled_moebius_reciprocal_rounded_sum_error Q N hQ
  rw [← hS] at he
  have ht := abs_add_le
    ((∑ n ∈ Finset.Icc 1 N, ((moebius n : ℤ) : ℝ) / (n : ℝ)) - (S : ℝ) / (Q : ℝ))
    ((S : ℝ) / (Q : ℝ))
  rw [sub_add_cancel, abs_div, abs_of_pos hQr] at ht
  have habs : |(S : ℝ)| = (S.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [habs] at ht
  exact ht.trans (by rw [add_div]; linarith [he])

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

lemma cdem4345_assembled_cdem_sum_icc_eq_ico {A : Type*} [AddCommMonoid A]
    (f : ℕ → A) (hf : f 0 = 0) (K : ℕ) :
    (∑ n ∈ Icc 1 K, f n) = ∑ n ∈ Ico 0 (K+1), f n := by
  have hsplit := Finset.sum_Ico_consecutive f
    (by norm_num : 0 ≤ 1) (by omega : 1 ≤ K+1)
  have hzero : (∑ n ∈ Ico 0 1, f n) = 0 := by simp [hf]
  rw [hzero, zero_add] at hsplit
  rw [← Finset.Ico_succ_right_eq_Icc]
  exact hsplit

theorem cdem4345_assembled_cdem_prefix_of_integer_totals (g : ℕ → ℤ)
    (hg : ∀ n ≤ 199330, g n = moebius n)
    (hM : (∑ n ∈ Ico 0 199331, g n) = (-6 : ℤ))
    (hS : (∑ n ∈ Ico 0 199331, (g n).natAbs) = 121174)
    (hF : (∑ n ∈ Ico 0 199331, g n * (5000000000 / n : ℕ)) = (112 : ℤ))
    (hR : (∑ n ∈ Ico 0 199331, g n *
      (100000000000000000000000000000000 / n : ℕ)) =
      (2098595765597847108232803 : ℤ)) :
    (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) ∧
    (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 ∧
    (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) ∧
    (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Icc 1 199330, ((moebius n : ℤ) : ℝ) / (n : ℝ)) ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ) := by
  have hsum {A : Type} [AddCommMonoid A] (f : ℤ → ℕ → A)
      (hf : f 0 0 = 0) :
      (∑ n ∈ Icc 1 199330, f (moebius n) n) =
        ∑ n ∈ Ico 0 199331, f (g n) n := by
    rw [cdem4345_assembled_cdem_sum_icc_eq_ico (fun n => f (moebius n) n) (by simpa using hf)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hg n (by have := Finset.mem_Ico.mp hn; omega)]
  have hMa : (∑ n ∈ Icc 1 199330, moebius n) = (-6 : ℤ) := by
    rw [hsum (A := ℤ) (fun a _ => a) rfl]
    exact hM
  have hSa : (∑ n ∈ Icc 1 199330, (moebius n).natAbs) = 121174 := by
    rw [hsum (A := ℕ) (fun a _ => a.natAbs) rfl]
    exact hS
  have hFa : (∑ n ∈ Icc 1 199330, moebius n * (5000000000 / n : ℕ)) = (112 : ℤ) := by
    rw [hsum (A := ℤ) (fun a n => a * (5000000000 / n : ℕ)) (by simp)]
    exact hF
  have hRa : (∑ n ∈ Icc 1 199330, moebius n *
      (100000000000000000000000000000000 / n : ℕ)) =
      (2098595765597847108232803 : ℤ) := by
    rw [hsum (A := ℤ) (fun a n => a * (100000000000000000000000000000000 / n : ℕ)) (by simp)]
    exact hR
  have herr := cdem4345_assembled_moebius_reciprocal_rounded_sum_error
    100000000000000000000000000000000 199330 (by norm_num)
  rw [hRa] at herr
  have htwo := abs_le.mp herr
  refine ⟨hMa, hSa, hFa, ?_, ?_⟩ <;>
    norm_num only [Int.cast_ofNat, Nat.cast_ofNat] at htwo <;>
    linarith [htwo.1, htwo.2]

lemma cdem4345_assembled_cdem_endpoint_reciprocal_sqrt :
    1 / Real.sqrt (5000000001 : ℝ) ≤
      (14142135622317 / 1000000000000000000 : ℝ) := by
  have hs0 : (0 : ℝ) < Real.sqrt 5000000001 := Real.sqrt_pos.mpr (by norm_num)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5000000001)
  have hbound : (1000000000000000000 / 14142135622317 : ℝ) ≤
      Real.sqrt 5000000001 := by
    nlinarith [Real.sqrt_nonneg (5000000001 : ℝ)]
  apply (div_le_iff₀ hs0).2
  nlinarith [hbound]

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
open Real
namespace Helfgott

theorem cdem4345_assembled_cdem_fixed_point_arithmetic (S U V : ℝ)
    (hSL : (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤ S)
    (hSU : S ≤ (20985957655978471142885 / 1000000000000000000000000000000 : ℝ))
    (hU : U ≤ (324880457633740 / 1000000000000000000 : ℝ))
    (hV : V ≤ (48710223109607260068028 / 1000000000000000000 : ℝ)) :
    0 ≤ S ∧ S ≤ (21 / 1000000000 : ℝ) ∧
    |(-6 : ℝ) - 5000000001*S| ≤ 112 ∧
    U + ((1+121174+|5000000001*S|)-111)/5000000001 ≤ (7/20000 : ℝ) ∧
    V + ((1+121174+|5000000001*S|)-111)/Real.sqrt 5000000001 ≤ 48712 := by
  have hS0 : 0 ≤ S := by linarith [hSL]
  have hS21 : S ≤ (21 / 1000000000 : ℝ) := by linarith [hSU]
  have hAS0 : (0 : ℝ) ≤ 5000000001*S := by positivity
  have hG : (1+121174+|5000000001*S| : ℝ) ≤ 121281 := by
    rw [abs_of_nonneg hAS0]
    linarith [hS21]
  have hcoeff : |(-6 : ℝ) - 5000000001*S| ≤ 112 := by
    rw [abs_of_nonpos (by linarith [hAS0])]
    linarith [hS21]
  refine ⟨hS0, hS21, hcoeff, ?_, ?_⟩
  · have ht : ((1+121174+|5000000001*S|)-111)/5000000001 ≤
        (121170/5000000001 : ℝ) := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith [hG]
    linarith [ht, hU]
  · have hs0 : (0 : ℝ) ≤ Real.sqrt 5000000001 := Real.sqrt_nonneg _
    have ht : ((1+121174+|5000000001*S|)-111)/Real.sqrt 5000000001 ≤
        121170/Real.sqrt 5000000001 := by
      apply div_le_div_of_nonneg_right _ hs0
      linarith [hG]
    have hs := cdem4345_assembled_cdem_endpoint_reciprocal_sqrt
    have ht2 : (121170 : ℝ)/Real.sqrt 5000000001 ≤
        (121170*14142135622317/1000000000000000000 : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 121170)
      simpa only [mul_one_div, mul_div_assoc] using hm
    linarith [ht, ht2, hV]
end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott
open MathExtras.CohenDressElMarraki

/-- The explicitly sampled prefix error, including the required zero override. -/
noncomputable def cdem4345_assembled_cdemRawPrefixError (k : ℕ) : ℝ :=
  if k = 0 then 0 else
    |1 - ∑ d ∈ Icc 1 199330,
      (moebius d : ℝ)*((k/d : ℕ) : ℝ)|

lemma cdem4345_assembled_cdem_raw_error_eq_table (k : ℕ) (hk : k ≤ 5000000000) :
    cdem4345_assembled_cdemRawPrefixError k =
      cdem4345_assembled_errorSeq (cdem4345_assembled_reproducibleSupport 199330 5000000001)
        (cdem4345_assembled_reproducibleCoeff 199330 5000000001) cdem4345_assembled_reproducibleDenominator k := by
  by_cases hk0 : k = 0
  · subst k
    simp [cdem4345_assembled_cdemRawPrefixError]
  · rw [cdem4345_assembled_cdemRawPrefixError, if_neg hk0,
      cdem4345_assembled_errorSeq_eq_floorError _ _ _ hk0, cdem4345_assembled_floorError,
      cdem4345_assembled_reproducible_floorSum_eq_prefix 199330 5000000001 (by norm_num)
        (by positivity) (by exact_mod_cast (show k < 5000000001 by omega))]
    unfold cdem4345_assembled_mobiusPrefixFloorSum
    simp only [Nat.floor_div_eq_div]

theorem cdem4345_assembled_cdem_abel_weights_of_raw_finite_bounds
    (hSL : (20985957655978471021715 / 1000000000000000000000000000000 : ℝ) ≤
      cdem4345_assembled_mobiusPrefixReciprocal 199330)
    (hSU : cdem4345_assembled_mobiusPrefixReciprocal 199330 ≤
      (20985957655978471142885 / 1000000000000000000000000000000 : ℝ))
    (hMass : cdem4345_assembled_mobiusPrefixMass 199330 = 121174)
    (hFloor : (∑ d ∈ Icc 1 199330,
      (moebius d : ℝ)*((5000000000/d : ℕ) : ℝ)) = 112)
    (hU : (∑ k ∈ Icc 1 5000000000,
      (cdem4345_assembled_cdemRawPrefixError k-cdem4345_assembled_cdemRawPrefixError (k-1))/(k : ℝ)) ≤
      (324880457633740 / 1000000000000000000 : ℝ))
    (hV : (∑ k ∈ Icc 1 5000000000,
      |cdem4345_assembled_cdemRawPrefixError k-cdem4345_assembled_cdemRawPrefixError (k-1)|/Real.sqrt k) ≤
      (48710223109607260068028 / 1000000000000000000 : ℝ)) :
    cdem4345_assembled_ReproducibleSignedMainCertificate 199330 5000000001 5000000000 (7/20000 : ℝ) ∧
    cdem4345_assembled_ReproducibleAbsoluteRemainderCertificate 199330 5000000001 5000000000 (48712 : ℝ) := by
  let G := cdem4345_assembled_errorSeq (cdem4345_assembled_reproducibleSupport 199330 5000000001)
    (cdem4345_assembled_reproducibleCoeff 199330 5000000001) cdem4345_assembled_reproducibleDenominator
  have he (k : ℕ) (hk : k ≤ 5000000000) : cdem4345_assembled_cdemRawPrefixError k = G k :=
    cdem4345_assembled_cdem_raw_error_eq_table k hk
  have hGN : G 5000000000 = 111 := by
    rw [← he 5000000000 (by omega), cdem4345_assembled_cdemRawPrefixError]
    norm_num only [show (5000000000 : ℕ) ≠ 0 by norm_num, if_false]
    rw [hFloor]
    norm_num
  have hU' : (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
      (324880457633740 / 1000000000000000000 : ℝ) := by
    convert hU using 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkN := (Finset.mem_Icc.mp hk).2
    rw [he k hkN, he (k-1) (by omega)]
  have hV' : (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
      (48710223109607260068028 / 1000000000000000000 : ℝ) := by
    convert hV using 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkN := (Finset.mem_Icc.mp hk).2
    rw [he k hkN, he (k-1) (by omega)]
  have h := cdem4345_assembled_cdem_fixed_point_arithmetic (cdem4345_assembled_mobiusPrefixReciprocal 199330)
    (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ))
    (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) hSL hSU hU' hV'
  constructor
  · change cdem4345_assembled_signedMainWeight 5000000000 G (cdem4345_assembled_reproducibleMaxG 199330 5000000001) ≤ _
    unfold cdem4345_assembled_signedMainWeight cdem4345_assembled_reproducibleMaxG
    rw [hMass, hGN]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    simpa only [show (1+121174 : ℝ) = 121175 by norm_num] using h.2.2.2.1
  · change cdem4345_assembled_absoluteRemainderWeight 5000000000 G (cdem4345_assembled_reproducibleMaxG 199330 5000000001) ≤ _
    unfold cdem4345_assembled_absoluteRemainderWeight cdem4345_assembled_reproducibleMaxG
    rw [hMass, hGN]
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    simpa only [show (1+121174 : ℝ) = 121175 by norm_num] using h.2.2.2.2

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott
open MathExtras.CohenDressElMarraki

theorem cdem4345_assembled_cdem_fixedpoint_of_two_finite_abel_bounds
    (hU : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
        (324880457633740 / 1000000000000000000 : ℝ))
    (hV : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
        (48710223109607260068028 / 1000000000000000000 : ℝ))
    : 0 ≤ cdem4345_assembled_mobiusPrefixReciprocal 199330 ∧
      cdem4345_assembled_mobiusPrefixReciprocal 199330 ≤ (21/1000000000 : ℝ) ∧
      (∑ d ∈ Icc 1 199330, (moebius d : ℝ)) = -6 ∧
      cdem4345_assembled_ReproducibleSignedMainCertificate 199330 5000000001 5000000000 (7/20000 : ℝ) ∧
      cdem4345_assembled_ReproducibleAbsoluteRemainderCertificate 199330 5000000001 5000000000 (48712 : ℝ) := by
  rcases cdem_prefix_199330 with ⟨hMZ, hMassN, hFloorZ, hSL, hSU, hResidue, hSqrt⟩
  have hMass : cdem4345_assembled_mobiusPrefixMass 199330 = 121174 := by
    unfold cdem4345_assembled_mobiusPrefixMass
    have he : (∑ n ∈ Icc 1 199330, |(moebius n : ℝ)|) =
        ((∑ n ∈ Icc 1 199330, (moebius n).natAbs : ℕ) : ℝ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      rcases moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num
    rw [he, hMassN]
    norm_num
  have hFloor : (∑ d ∈ Icc 1 199330,
      (moebius d : ℝ)*((5000000000/d : ℕ) : ℝ)) = 112 := by
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hFloorZ
    push_cast at hcast
    exact hcast
  have hWeights := cdem4345_assembled_cdem_abel_weights_of_raw_finite_bounds hSL hSU hMass hFloor hU hV
  have hS0 : 0 ≤ cdem4345_assembled_mobiusPrefixReciprocal 199330 := by
    change 0 ≤ ∑ d ∈ Icc 1 199330, (moebius d : ℝ)/(d : ℝ)
    linarith [hSL]
  have hS1 : cdem4345_assembled_mobiusPrefixReciprocal 199330 ≤ (21/1000000000 : ℝ) := by
    change (∑ d ∈ Icc 1 199330, (moebius d : ℝ)/(d : ℝ)) ≤ _
    linarith [hSU]
  have hM : (∑ d ∈ Icc 1 199330, (moebius d : ℝ)) = -6 := by
    exact_mod_cast hMZ
  exact ⟨hS0, hS1, hM, hWeights.1, hWeights.2⟩

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott
open MathExtras.CohenDressElMarraki

theorem cdem4345_assembled_cdem_mertens_tail_of_finite_table (b threshold : ℝ) (D X : ℕ)
    (hb : 0 ≤ b) (ht : 0 ≤ threshold) (hD : 1 ≤ D)
    (htau : threshold * 5000000001 < (10000000000000000 : ℝ))
    (hQfull : ∀ y : ℝ, threshold < y →
      |cdem4345_assembled_squarefreeCount y - (6/Real.pi^2)*y| ≤ b*Real.sqrt y)
    (hnumeric : (427/2000000 + b*48712/100000000 +
      112/10000000000000000 : ℝ) ≤ 1/(D : ℝ))
    (hX : 10000000000000000 ≤ X)
    (hS0 : 0 ≤ cdem4345_assembled_mobiusPrefixReciprocal 199330)
    (hS1 : cdem4345_assembled_mobiusPrefixReciprocal 199330 ≤ (21/1000000000 : ℝ))
    (hM : (∑ n ∈ Icc 1 199330, (moebius n : ℝ)) = -6)
    (hU : cdem4345_assembled_ReproducibleSignedMainCertificate 199330 5000000001 5000000000
      (7/20000 : ℝ))
    (hV : cdem4345_assembled_ReproducibleAbsoluteRemainderCertificate 199330 5000000001 5000000000
      (48712 : ℝ)) :
    |∑ n ∈ Icc 1 X, (moebius n : ℝ)| ≤ (X : ℝ)/(D : ℝ) := by
  let s := cdem4345_assembled_reproducibleSupport 199330 5000000001
  let c := cdem4345_assembled_reproducibleCoeff 199330 5000000001
  let a := cdem4345_assembled_reproducibleDenominator
  let maxG := cdem4345_assembled_reproducibleMaxG 199330 5000000001
  let G := cdem4345_assembled_errorSeq s c a
  let U := cdem4345_assembled_signedMainWeight 5000000000 G maxG
  let V := cdem4345_assembled_absoluteRemainderWeight 5000000000 G maxG
  have hKA : (199330 : ℕ) < 5000000001 := by norm_num
  have hXR : (10000000000000000 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hX1 : 1 ≤ X := by omega
  have hdenom_one : ∀ d ∈ s, 1 ≤ a d :=
    cdem4345_assembled_reproducible_denominator_one 199330 5000000001 hKA
  have hdenom_active : ∀ d ∈ s, a d ≤ (X : ℝ) := by
    intro d hd
    exact (cdem4345_assembled_reproducible_denominator_le_A 199330 5000000001 hKA d hd).trans
      (by norm_num; exact_mod_cast (show 5000000001 ≤ X by omega))
  have hdenom_step : ∀ d ∈ s, cdem4345_assembled_UnitStepDenominatorGuard 5000000000 (a d) :=
    cdem4345_assembled_reproducible_denominator_step 199330 5000000001 5000000000 hKA
  have hmax : ∀ y : ℝ, 0 ≤ y → cdem4345_assembled_floorError s c a y ≤ maxG :=
    cdem4345_assembled_reproducible_globalMax 199330 5000000001 hKA
  have hQ : ∀ k : ℕ, k ∈ Icc 1 (5000000000+1) →
      |cdem4345_assembled_squarefreeCount ((X : ℝ)/k) - (6/Real.pi^2)*(X : ℝ)/(k : ℝ)| ≤
      b*Real.sqrt (X : ℝ)/Real.sqrt k := by
    intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hk2 := (Finset.mem_Icc.mp hk).2
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkR : (k : ℝ) ≤ 5000000001 := by exact_mod_cast hk2
    have hy : threshold < (X : ℝ)/k := by
      rw [lt_div_iff₀ hkpos]
      calc
        threshold*(k : ℝ) ≤ threshold*5000000001 :=
          mul_le_mul_of_nonneg_left hkR ht
        _ < 10000000000000000 := htau
        _ ≤ (X : ℝ) := hXR
    have hs := hQfull ((X : ℝ)/k) hy
    simpa only [Real.sqrt_div hX0, mul_div_assoc] using hs
  have hpoint := cdem4345_assembled_lemma4_pointwise s c a 5000000000 X (6/Real.pi^2) b maxG
    (by norm_num) hX1 hdenom_one hdenom_active hdenom_step hmax hQ
  have hUbound : U ≤ (7/20000 : ℝ) := hU
  have hVbound : V ≤ (48712 : ℝ) := hV
  have hpi : (6/Real.pi^2 : ℝ) ≤ 61/100 := by
    rw [div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
    have hp := Real.pi_gt_d2
    norm_num at hp ⊢
    nlinarith [sq_nonneg (Real.pi-314/100)]
  have hmain : (6/Real.pi^2)*U ≤ (427/2000000 : ℝ) := by
    by_cases hU0 : 0 ≤ U
    · calc
        _ ≤ (61/100 : ℝ)*U := mul_le_mul_of_nonneg_right hpi hU0
        _ ≤ (61/100 : ℝ)*(7/20000 : ℝ) :=
          mul_le_mul_of_nonneg_left hUbound (by norm_num)
        _ = _ := by norm_num
    · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hU0)).trans
        (by norm_num)
  have hcoeff : |∑ d ∈ s, c d| ≤ (112 : ℝ) := by
    rw [cdem4345_assembled_reproducible_coeff_total 199330 5000000001 hKA]
    unfold cdem4345_assembled_reproducibleCoeffTotal
    rw [hM]
    norm_num only [Nat.cast_ofNat]
    have hp0 : (0 : ℝ) ≤ 5000000001*cdem4345_assembled_mobiusPrefixReciprocal 199330 := by positivity
    have hp1 : (5000000001 : ℝ)*cdem4345_assembled_mobiusPrefixReciprocal 199330 ≤ 106 := by
      have hm := mul_le_mul_of_nonneg_left hS1
        (by norm_num : (0 : ℝ) ≤ 5000000001)
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hsqrt_lower : (100000000 : ℝ) ≤ Real.sqrt (X : ℝ) := by
    calc
      _ = Real.sqrt ((100000000 : ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [hXR])
  have hsqrt_upper : Real.sqrt (X : ℝ) ≤ (X : ℝ)/100000000 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 100000000)]
    calc
      _ ≤ Real.sqrt (X : ℝ)*Real.sqrt (X : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt_lower (Real.sqrt_nonneg _)
      _ = _ := by simpa only [pow_two] using Real.sq_sqrt hX0
  have hmain_scaled : (6/Real.pi^2)*(X : ℝ)*U ≤ (427/2000000 : ℝ)*(X : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hmain hX0
    nlinarith [hm]
  have hrem_scaled : b*Real.sqrt (X : ℝ)*V ≤
      (b*48712/100000000 : ℝ)*(X : ℝ) := by
    calc
      _ ≤ b*Real.sqrt (X : ℝ)*48712 :=
        mul_le_mul_of_nonneg_left hVbound (by positivity)
      _ ≤ b*((X : ℝ)/100000000)*48712 := by
        have hm := mul_le_mul_of_nonneg_left hsqrt_upper hb
        nlinarith [hm]
      _ = _ := by ring
  have hcoeff_scaled : |∑ d ∈ s, c d| ≤
      (112/10000000000000000 : ℝ)*(X : ℝ) := by
    apply hcoeff.trans
    have hm := mul_le_mul_of_nonneg_left hXR
      (by norm_num : (0 : ℝ) ≤ 112/10000000000000000)
    norm_num at hm ⊢
    exact hm
  calc
    _ ≤ (6/Real.pi^2)*(X : ℝ)*U + b*Real.sqrt (X : ℝ)*V + |∑ d ∈ s, c d| := hpoint
    _ ≤ (427/2000000 : ℝ)*(X : ℝ) +
        (b*48712/100000000 : ℝ)*(X : ℝ) +
        (112/10000000000000000 : ℝ)*(X : ℝ) :=
      add_le_add (add_le_add hmain_scaled hrem_scaled) hcoeff_scaled
    _ = (427/2000000 + b*48712/100000000 + 112/10000000000000000 : ℝ)*(X : ℝ) := by ring
    _ ≤ (1/(D : ℝ) : ℝ)*(X : ℝ) := mul_le_mul_of_nonneg_right hnumeric hX0
    _ = _ := by ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma cdem4345_assembled_floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
    Nat.floorRoot 2 n = 1 ↔ Squarefree n := by
  constructor
  · intro hroot
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hdvd
    have h : p ∣ Nat.floorRoot 2 n := Nat.pow_dvd_iff_dvd_floorRoot.mp (by simpa [pow_two] using hdvd)
    rw [hroot] at h
    exact hp.ne_one (Nat.dvd_one.mp h)
  · intro hsf
    have h := hsf (Nat.floorRoot 2 n) (by simpa [pow_two] using Nat.floorRoot_pow_dvd (n:=2) (a:=n))
    exact Nat.isUnit_iff.mp h

lemma cdem4345_assembled_moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem cdem4345_assembled_moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
    (moebius n)^2 = ∑ d ∈ n.divisors,if d^2 ∣ n then moebius d else 0 := by
  have hroot0 : Nat.floorRoot 2 n ≠ 0 := Nat.floorRoot_ne_zero.mpr ⟨by norm_num,hn⟩
  have he : n.divisors.filter (fun d => d^2 ∣ n) = (Nat.floorRoot 2 n).divisors := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hsq⟩
      exact ⟨Nat.pow_dvd_iff_dvd_floorRoot.mp hsq,hroot0⟩
    · rintro ⟨hd,hr0⟩
      have hsq := Nat.pow_dvd_iff_dvd_floorRoot.mpr hd
      exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn⟩,hsq⟩
  rw [←Finset.sum_filter,he,cdem4345_assembled_moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [cdem4345_assembled_floorRoot_two_eq_one_iff_squarefree n hn]

lemma cdem4345_assembled_coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
    (∑ e ∈ q.divisors,if e ∣ n then moebius e else 0) =
      if Nat.Coprime n q then 1 else 0 := by
  have he : q.divisors.filter (fun e => e ∣ n) = (Nat.gcd n q).divisors := by
    ext e
    simp only [Finset.mem_filter,Nat.mem_divisors]
    have hg : Nat.gcd n q ≠ 0 := Nat.gcd_ne_zero_right hq
    constructor
    · rintro ⟨⟨heq,hq0⟩,hen⟩
      exact ⟨Nat.dvd_gcd hen heq,hg⟩
    · rintro ⟨heg,hg0⟩
      exact ⟨⟨dvd_trans heg (Nat.gcd_dvd_right n q),hq⟩,dvd_trans heg (Nat.gcd_dvd_left n q)⟩
  rw [←Finset.sum_filter,he,cdem4345_assembled_moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem cdem4345_assembled_squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast cdem4345_assembled_coprime_moebius_divisor_expansion q n hq
  rw [hcop]
  by_cases h : Nat.Coprime n q
  · simp only [if_pos h,mul_one]
    have he : (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
        ∑ d ∈ n.divisors,if d^2 ∣ n then ((moebius d : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdc : Nat.Coprime d q := h.of_dvd_left (Nat.dvd_of_mem_divisors hd)
      by_cases hs : d^2 ∣ n <;> simp [hs,hdc]
    rw [he]
    exact_mod_cast cdem4345_assembled_moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma cdem4345_assembled_squarefree_square_divisor_sum_cap (q n N : ℕ) (hn : 0<n) (hnN : n≤N) :
    (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0 := by
  rw [←Finset.sum_filter,←Finset.sum_filter]
  congr 1
  ext d
  simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hd,hn0⟩,hsq,hcop⟩
    have hdpos : 0<d := Nat.pos_of_dvd_of_pos hd hn
    have hdN : d≤N.sqrt := Nat.le_sqrt.mpr (by simpa [pow_two] using (Nat.le_of_dvd hn hsq).trans hnN)
    exact ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
  · rintro ⟨⟨hdpos,hdN⟩,hsq,hcop⟩
    exact ⟨⟨dvd_trans (dvd_pow_self d (by norm_num : 2 ≠ 0)) hsq,hn.ne'⟩,hsq,hcop⟩

theorem cdem4345_assembled_squarefree_coprime_count_exact (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0 := by
  have hp (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
        ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
          if d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n then
            ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ) else 0 := by
    rw [cdem4345_assembled_squarefree_coprime_pointwise_expansion q n hq (by have := (Finset.mem_Icc.mp hn).1;omega),
      cdem4345_assembled_squarefree_square_divisor_sum_cap q n N (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hs : d^2 ∣ n <;> by_cases hc : Nat.Coprime d q <;> by_cases he : e ∣ n <;>
      simp [hs,hc,he]
  rw [Finset.sum_congr rfl hp,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  by_cases hc : Nat.Coprime d q
  · rw [if_pos hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hde : Nat.Coprime (d^2) e := (hc.pow_left 2).of_dvd_right (Nat.dvd_of_mem_divisors he)
    have hdvd (n : ℕ) : (d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n) ↔ d^2*e ∣ n := by
      constructor
      · rintro ⟨hsq,hc,he⟩
        rw [←hde.lcm_eq_mul]
        exact Nat.lcm_dvd hsq he
      · intro h
        rw [←hde.lcm_eq_mul] at h
        exact ⟨(Nat.lcm_dvd_iff.mp h).1,hc,(Nat.lcm_dvd_iff.mp h).2⟩
    simp_rw [hdvd]
    rw [←Finset.sum_filter]
    simp only [Finset.sum_const,smul_eq_mul]
    have hi : (Finset.Icc 1 N).filter (fun n => d^2*e ∣ n) =
        (Finset.Ioc 0 N).filter (fun n => d^2*e ∣ n) := by congr 1
    rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
    ring
  · simp [hc]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma cdem4345_assembled_principal_character_nat_value (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if Nat.Coprime n q then 1 else 0 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc)
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))

lemma cdem4345_assembled_principal_LSeries_at_two (q : ℕ) (hq : q ≠ 0) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 =
      ((Real.pi : ℂ)^2/6)*∏ p ∈ q.primeFactors,(1-1/(p : ℂ)^2) := by
  letI : NeZero q := ⟨hq⟩
  have h := DirichletCharacter.LSeries_changeLevel (Nat.one_dvd q)
    (1 : DirichletCharacter ℂ 1) (s:=2) (by norm_num)
  rw [DirichletCharacter.changeLevel_one,DirichletCharacter.LSeries_modOne_eq,
    LSeries_one_eq_riemannZeta (by norm_num),riemannZeta_two] at h
  rw [h]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  rw [cdem4345_assembled_principal_character_nat_value]
  try simp only [Nat.coprime_one_right,if_true,one_mul]
  rw [Complex.cpow_neg]
  norm_num [Complex.cpow_natCast]

lemma cdem4345_assembled_principal_moebius_LSeries_at_two (q : ℕ) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 =
      ((∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) : ℂ) := by
  rw [LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn,cdem4345_assembled_principal_character_nat_value]
    norm_num [Complex.cpow_natCast]
    split_ifs <;> push_cast <;> ring

theorem cdem4345_assembled_squarefree_coprime_density_series (q : ℕ) (hq : q ≠ 0) :
    (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹ := by
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ q) (s:=2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 = 1 at h
  rw [cdem4345_assembled_principal_LSeries_at_two q hq,cdem4345_assembled_principal_moebius_LSeries_at_two] at h
  have hr : ((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)))*
      (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) = 1 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [apply_ite,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_intCast,Complex.ofReal_natCast,Complex.ofReal_zero] using h
  have hp0 : (∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hsq : (1 : ℝ)<(p : ℝ)^2 := by nlinarith
    have hinv : 1/(p : ℝ)^2 < 1 := (div_lt_one (by positivity)).mpr hsq
    linarith
  rw [Finset.prod_inv_distrib]
  have hpi : Real.pi^2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  have hx : (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      1/((Real.pi^2/6)*(∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2))) := by
    apply (eq_div_iff (mul_ne_zero (div_ne_zero hpi (by norm_num)) hp0)).mpr
    simpa only [mul_comm] using hr
  rw [hx]
  field_simp [hpi,hp0]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

lemma cdem4345_assembled_shifted_reciprocal_square_sum_le (D K : ℕ) (hD : 1≤D) :
    (∑ n ∈ Finset.range K,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) := by
  have hpoint (n : ℕ) : 1/((n+D+1 : ℕ) : ℝ)^2 ≤
      1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ) := by
    have hpos : (0 : ℝ)<((n+D : ℕ) : ℝ) := by exact_mod_cast (show 0<n+D by omega)
    push_cast
    field_simp
    nlinarith
  calc
    _ ≤ ∑ n ∈ Finset.range K,(1/((n+D : ℕ) : ℝ)-1/((n+D+1 : ℕ) : ℝ)) := Finset.sum_le_sum (fun n hn => hpoint n)
    _ = 1/(D : ℝ)-1/((K+D : ℕ) : ℝ) := by
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,add_assoc,add_comm,add_left_comm] using Finset.sum_range_sub' (fun n : ℕ => 1/((n+D : ℕ) : ℝ)) K
    _ ≤ _ := sub_le_self _ (by positivity)

lemma cdem4345_assembled_shifted_reciprocal_square_tsum_le (D : ℕ) (hD : 1≤D) :
    (∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => cdem4345_assembled_shifted_reciprocal_square_sum_le D K hD)

lemma cdem4345_assembled_coprime_moebius_reciprocal_square_norm_le (q n : ℕ) :
    ‖(if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)‖ ≤ 1/(n : ℝ)^2 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,Real.norm_eq_abs,abs_div]
    rw [show |(n : ℝ)^2| = (n : ℝ)^2 from abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n:=n)) (sq_nonneg _)
  · rw [if_neg hc,norm_zero]
    positivity

lemma cdem4345_assembled_coprime_moebius_reciprocal_square_summable (q : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) := by
  exact Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => cdem4345_assembled_coprime_moebius_reciprocal_square_norm_le q n)

lemma cdem4345_assembled_reciprocal_square_tsum_le_two : (∑' n : ℕ,1/(n : ℝ)^2) ≤ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at h
  have ht := cdem4345_assembled_shifted_reciprocal_square_tsum_le 1 (by norm_num)
  norm_num [add_assoc] at ht
  simp only [one_div]
  linarith

lemma cdem4345_assembled_coprime_moebius_density_norm_le_two (q : ℕ) (hq : q ≠ 0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹| ≤ 2 := by
  rw [←cdem4345_assembled_squarefree_coprime_density_series q hq]
  have hf := cdem4345_assembled_coprime_moebius_reciprocal_square_summable q
  calc
    _ ≤ ∑' n : ℕ,‖if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ,1/(n : ℝ)^2 := hf.norm.tsum_le_tsum
      (fun n => cdem4345_assembled_coprime_moebius_reciprocal_square_norm_le q n) hasSum_zeta_two.summable
    _ ≤ _ := cdem4345_assembled_reciprocal_square_tsum_le_two

theorem cdem4345_assembled_coprime_moebius_density_tail_error (q D : ℕ) (hq : q ≠ 0) (hD : 1≤D) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ n ∈ Finset.Icc 1 D,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)| ≤ 1/(D : ℝ) := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  have hf : Summable f := cdem4345_assembled_coprime_moebius_reciprocal_square_summable q
  have hs : (∑ n ∈ Finset.range (D+1),f n) = ∑ n ∈ Finset.Icc 1 D,f n := by
    rw [Finset.range_eq_Ico]
    have he : Finset.Ico 0 (D+1) = insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [he,Finset.sum_insert (by simp)]
    simp [f]
  rw [←cdem4345_assembled_squarefree_coprime_density_series q hq]
  change |(∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n)| ≤ _
  have he := hf.sum_add_tsum_nat_add (D+1)
  rw [hs] at he
  have herr : (∑' n : ℕ,f n)-(∑ n ∈ Finset.Icc 1 D,f n) = ∑' n : ℕ,f (n+(D+1)) := by linarith
  rw [herr]
  have htail : Summable (fun n : ℕ => f (n+(D+1))) := hf.comp_injective (fun n m h => by omega)
  have hnorm : Summable (fun n : ℕ => 1/((n+D+1 : ℕ) : ℝ)^2) :=
    hasSum_zeta_two.summable.comp_injective (fun n m h => by omega)
  calc
    _ ≤ ∑' n : ℕ,‖f (n+(D+1))‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm htail.norm
    _ ≤ ∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2 :=
      htail.norm.tsum_le_tsum (fun n => by simpa [f,Nat.add_assoc] using cdem4345_assembled_coprime_moebius_reciprocal_square_norm_le q (n+(D+1))) hnorm
    _ ≤ _ := cdem4345_assembled_shifted_reciprocal_square_tsum_le D hD

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem cdem4345_assembled_cdem_squarefree_floor_main_error (x : ℝ) (hx : 1 ≤ x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ)^2) -
      (⌊x⌋₊ : ℝ)*(∑ d ∈ Icc 1 (⌊x⌋₊).sqrt, (moebius d : ℝ)/(d : ℝ)^2)| ≤
      Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hc := cdem4345_assembled_squarefree_coprime_count_exact 1 ⌊x⌋₊ (by norm_num)
  simp only [Nat.coprime_one_right_iff, if_true, Nat.divisors_one, Finset.sum_singleton,
    moebius_apply_one, Int.cast_one, one_mul, Nat.mul_one] at hc
  rw [hc, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 (⌊x⌋₊).sqrt,
        |(moebius d : ℝ)*((⌊x⌋₊/(d^2) : ℕ) : ℝ) -
          (⌊x⌋₊ : ℝ)*((moebius d : ℝ)/(d : ℝ)^2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 (⌊x⌋₊).sqrt, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hf : |(⌊x⌋₊/(d^2) : ℕ) - (⌊x⌋₊ : ℝ)/(d : ℝ)^2| ≤ 1 := by
        have hf' := Nat.abs_sub_floor_le
          (a := (⌊x⌋₊ : ℝ)/((d^2 : ℕ) : ℝ)) (by positivity)
        rw [Nat.floor_div_eq_div] at hf'
        simpa only [Nat.cast_pow, abs_sub_comm] using hf'
      have hm : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n:=d)
      have he : (moebius d : ℝ)*((⌊x⌋₊/(d^2) : ℕ) : ℝ) -
          (⌊x⌋₊ : ℝ)*((moebius d : ℝ)/(d : ℝ)^2) =
          (moebius d : ℝ)*(((⌊x⌋₊/(d^2) : ℕ) : ℝ) - (⌊x⌋₊ : ℝ)/(d : ℝ)^2) := by ring
      rw [he, abs_mul]
      exact mul_le_one₀ hm (abs_nonneg _) hf
    _ = ((⌊x⌋₊).sqrt : ℝ) := by simp [Nat.card_Icc]
    _ ≤ Real.sqrt x := by
      have hs : (((⌊x⌋₊).sqrt : ℝ))^2 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.sqrt_le' ⌊x⌋₊
      simpa only [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (⌊x⌋₊).sqrt)] using
        Real.sqrt_le_sqrt (hs.trans (Nat.floor_le hx0))

end Helfgott
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# A coarse theorem-level squarefree seed for the CDEM bootstrap

The historical CDEM bootstrap starts from the cited estimate
`|Q(x)-(6/pi^2)x| <= 0.1333 sqrt(x)`.  That estimate is not finite: Cohen--Dress
(1988) obtains its unbounded tail from an earlier unbounded Mertens estimate.

For the bootstrap it is enough to start much more coarsely.  The already-proved
Möbius-square identity and reciprocal-square tail bound give

```text
|Q(x) - (6/pi^2)x| <= 3 sqrt(x)       (x >= 9).
```

This file proves that statement without any numerical cite.  The constant `3`
comes from three honest pieces:

* at most `sqrt(x)` when each floor in the squarefree-count identity is replaced
  by its real argument;
* at most `sqrt(x)+2` from truncating `sum mu(d)/d^2` at
  `d=floor(sqrt(floor x))`;
* at most `1` from replacing `floor(x)` by `x` in the main term.

Since `sqrt(x)>=3`, their sum `2 sqrt(x)+3` is at most `3 sqrt(x)`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000

namespace MathExtras.CohenDressElMarraki

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset


/-- The local absolute-Möbius squarefree count is the Möbius-square sum used by
`moebius_square_asymptotic_real`. -/
private theorem cdem4345_assembled_squarefreeCount_eq_moebius_sq_sum (x : ℝ) :
    cdem4345_assembled_squarefreeCount x
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((μ n : ℝ)) ^ 2 := by
  rw [cdem4345_assembled_squarefreeCount_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro n _
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

/-- A base-trio squarefree-remainder seed.  This deliberately has a coarse
constant: its role is to initialize repeated CDEM Lemma 4/Lemma 1 iteration,
not to replace the sharp final `0.02767` estimate directly. -/
theorem cdem4345_assembled_coarseSquarefreeRemainder_three
    {x : ℝ} (hx : 9 ≤ x) :
    |cdem4345_assembled_squarefreeCount x - (6 / Real.pi ^ 2) * x|
      ≤ 3 * Real.sqrt x := by
  classical
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  let N : ℕ := ⌊x⌋₊
  let K : ℕ := Nat.sqrt N
  let S : ℝ := ∑ d ∈ Finset.Icc 1 K, (μ d : ℝ) / ((d : ℝ) ^ 2)
  let L : ℝ := 6 / Real.pi ^ 2
  let Q : ℝ := ∑ n ∈ Finset.Icc 1 N, ((μ n : ℝ)) ^ 2

  have hNpos : 0 < N := by
    dsimp [N]
    exact Nat.floor_pos.mpr hx1
  have hKone : 1 ≤ K := by
    dsimp [K]
    exact Nat.le_sqrt'.mpr hNpos
  have hKRpos : 0 < (K : ℝ) := by exact_mod_cast hKone
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNle : (N : ℝ) ≤ x := by
    dsimp [N]
    exact Nat.floor_le hx0
  have hxlt : x < (N : ℝ) + 1 := by
    dsimp [N]
    exact Nat.lt_floor_add_one x
  have hgap0 : 0 ≤ x - (N : ℝ) := sub_nonneg.mpr hNle
  have hgap1 : x - (N : ℝ) ≤ 1 := by linarith

  have hK_le_sqrt : (K : ℝ) ≤ Real.sqrt x := by
    have hsq : K ^ 2 ≤ N := by
      dsimp [K]
      exact Nat.sqrt_le' N
    have hsqR : ((K : ℝ) : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hsq
    have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
    calc
      (K : ℝ) = Real.sqrt ((K : ℝ) ^ 2) := (Real.sqrt_sq hK0).symm
      _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hsqR
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hNle

  /- `N < (K+1)^2` and integrality sharpen the usual `N/K <= 2 sqrt N`
  to `N/K <= K+2 <= sqrt x+2`. -/
  have hN_le_K : N ≤ K ^ 2 + 2 * K := by
    have hlt : N < (K + 1) ^ 2 := by
      dsimp [K]
      exact Nat.lt_succ_sqrt' N
    nlinarith
  have hN_div_K : (N : ℝ) / (K : ℝ) ≤ Real.sqrt x + 2 := by
    rw [div_le_iff₀ hKRpos]
    have hcast : (N : ℝ) ≤ (K : ℝ) ^ 2 + 2 * (K : ℝ) := by
      exact_mod_cast hN_le_K
    have hmul : (K : ℝ) ^ 2 + 2 * (K : ℝ)
        ≤ (Real.sqrt x + 2) * (K : ℝ) := by
      have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
      nlinarith
    exact hcast.trans hmul

  have hengine : |Q - (N : ℝ) * S| ≤ Real.sqrt x := by
    simpa [Q, N, K, S] using Helfgott.cdem4345_assembled_cdem_squarefree_floor_main_error x hx1
  have htail : |L - S| ≤ 1 / (K : ℝ) := by
    simpa [L, S, Nat.coprime_one_right_iff] using
      Helfgott.cdem4345_assembled_coprime_moebius_density_tail_error 1 K (by norm_num) hKone
  have htail_scaled : (N : ℝ) * |S - L| ≤ Real.sqrt x + 2 := by
    calc
      (N : ℝ) * |S - L| = (N : ℝ) * |L - S| := by rw [abs_sub_comm]
      _ ≤ (N : ℝ) * (1 / (K : ℝ)) :=
        mul_le_mul_of_nonneg_left htail hN0
      _ = (N : ℝ) / (K : ℝ) := by ring
      _ ≤ Real.sqrt x + 2 := hN_div_K

  have hL : L = 6 / Real.pi ^ 2 := by
    rfl
  have hL0 : 0 ≤ L := by
    rw [hL]
    positivity
  have hL1 : L ≤ 1 := by
    rw [hL, div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
    nlinarith [Real.pi_gt_three]
  have hinterp : (x - (N : ℝ)) * L ≤ 1 := by
    calc
      (x - (N : ℝ)) * L ≤ 1 * L :=
        mul_le_mul_of_nonneg_right hgap1 hL0
      _ ≤ 1 := by simpa using hL1

  have hbridge : |(N : ℝ) * S - x * L| ≤ Real.sqrt x + 3 := by
    have hsplit : (N : ℝ) * S - x * L
        = (N : ℝ) * (S - L) + ((N : ℝ) - x) * L := by ring
    rw [hsplit]
    calc
      |(N : ℝ) * (S - L) + ((N : ℝ) - x) * L|
          ≤ |(N : ℝ) * (S - L)| + |((N : ℝ) - x) * L| := abs_add_le _ _
      _ = (N : ℝ) * |S - L| + (x - (N : ℝ)) * L := by
        rw [abs_mul, abs_mul, abs_of_nonneg hN0,
          abs_of_nonpos (sub_nonpos.mpr hNle), abs_of_nonneg hL0]
        ring
      _ ≤ (Real.sqrt x + 2) + 1 := add_le_add htail_scaled hinterp
      _ = Real.sqrt x + 3 := by ring

  have hsqrt_three : 3 ≤ Real.sqrt x := by
    calc
      (3 : ℝ) = Real.sqrt ((3 : ℝ) ^ 2) :=
        (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt (by norm_num; exact hx)
  have htotal : |Q - x * L| ≤ 3 * Real.sqrt x := by
    have hsplit : Q - x * L = (Q - (N : ℝ) * S) + ((N : ℝ) * S - x * L) := by
      ring
    rw [hsplit]
    calc
      |Q - (N : ℝ) * S + ((N : ℝ) * S - x * L)|
          ≤ |Q - (N : ℝ) * S| + |(N : ℝ) * S - x * L| := abs_add_le _ _
      _ ≤ Real.sqrt x + (Real.sqrt x + 3) := add_le_add hengine hbridge
      _ ≤ 3 * Real.sqrt x := by linarith

  rw [cdem4345_assembled_squarefreeCount_eq_moebius_sq_sum]
  simpa [Q, N, L, hL, mul_comm] using htotal

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Cohen--Dress--El Marraki Lemma 1: squarefree bootstrap

This file records the exact `T1/T2/T3` decomposition used in Section 2 of
Cohen--Dress--El Marraki (2007), and proves the algebraic/inequality assembly around it.
It also pins the second bootstrap to `n=197`.

There are two deliberately exposed theorem-level seams:

* `cdem4345_assembled_Lemma1ExactDecompositionAt x n` is the exact partial-summation identity obtained from
  CDEM (2.1) and the tail of `sum mu(a)/a^2`;
* `cdem4345_assembled_Lemma1CenteredCauchyAt x n` and `cdem4345_assembled_Lemma1PeriodicMajorantAt x n` are respectively the
  finite Cauchy--Schwarz step and the signed periodic-majorant estimate for the centered
  fractional-part sum.

These are pointwise mathematical propositions, not axioms and not restatements of the
unbounded squarefree conclusion.  The existing PNTA theorem
`MobiusLemma.mobius_lemma_1_sub` supplies the underlying squarefree/Mertens convolution
identity for the first seam.

## Constant audit

The two rounded component values printed in the proof of Theorem 3 bis must **not** be
used as upper bounds.  At the live endpoint `x=1.6*10^15`, the displayed formulas give

* `(1/4257)(4*sqrt(197)-1.46) = 0.0128453548...`, not `<=0.012845`;
* `T3/sqrt(x) = 0.0148202617...`, not `<=0.01479`.

Their exact combined value is about `0.0276656165`, which is still below `0.02767`.
Accordingly the formal boundary below uses one combined exact envelope and never relies
on either false rounded component inequality.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset MeasureTheory
open scoped BigOperators

/-- `X_j=sqrt(x/j)`.  All theorems using it carry `1≤j`, so the zero-denominator
artifact is never live. -/
noncomputable def cdem4345_assembled_lemma1X (x : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (x / j)

/-- Real-valued Mertens step function used by the paper. -/
noncomputable def cdem4345_assembled_lemma1M (t : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ)

/-- The squarefree remainder in the same normalization as the Lemma 4 wrapper. -/
noncomputable def cdem4345_assembled_lemma1Remainder (x : ℝ) : ℝ :=
  cdem4345_assembled_squarefreeCount x - (6 / Real.pi ^ 2) * x

/-- Signed tail integral occurring in the exact decomposition. -/
noncomputable def cdem4345_assembled_lemma1SignedTailIntegral (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), cdem4345_assembled_lemma1M t / t ^ 3

/-- `T1=2x integral_{X_n}^infinity |M(t)|/t^3 dt`. -/
noncomputable def cdem4345_assembled_lemma1T1 (x : ℝ) (n : ℕ) : ℝ :=
  2 * x * ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3

/-- `T2=sum_{j=1}^{n-1}|M(X_j)|+|M(X_n)|/2`. -/
noncomputable def cdem4345_assembled_lemma1T2 (x : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (n - 1), |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|)
    + |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n)| / 2

/-- The centered fractional-part sum whose absolute value is `T3`. -/
noncomputable def cdem4345_assembled_lemma1CenteredSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
    (ArithmeticFunction.moebius a : ℝ)
      * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2)

/-- `T3=|sum_{a≤X_n} mu(a)({x/a^2}-1/2)|`. -/
noncomputable def cdem4345_assembled_lemma1T3 (x : ℝ) (n : ℕ) : ℝ :=
  |cdem4345_assembled_lemma1CenteredSum x n|

/-- The square mass appearing after Cauchy--Schwarz. -/
noncomputable def cdem4345_assembled_lemma1CenteredSquareMass (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
    (if 4 ∣ a ∨ 9 ∣ a then 0 else 1 : ℝ)
      * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2

/-- The exact printed upper factor for `Q(X_n)`:
`6 sqrt(x)/(pi^2 sqrt(n)) + b x^(1/4)/n^(1/4)`.

Nested square roots are used for the quarter powers, avoiding any ambiguity about real
power notation at zero. -/
noncomputable def cdem4345_assembled_lemma1QFactor (x : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  6 * Real.sqrt x / (Real.pi ^ 2 * Real.sqrt n)
    + b * Real.sqrt (Real.sqrt x) / Real.sqrt (Real.sqrt n)

/-- The exact printed periodic-majorant factor:
`sqrt(x)/(18 sqrt(n-0.02)) + (12x)^(1/3)/6 - (2/3)(n-1/2)`. -/
noncomputable def cdem4345_assembled_lemma1SFactor (x : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt x / (18 * Real.sqrt ((n : ℝ) - 2 / 100))
    + (12 * x) ^ ((1 : ℝ) / 3) / 6
    - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2)

/-- The displayed `T3` envelope. -/
noncomputable def cdem4345_assembled_lemma1T3Envelope (x : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  Real.sqrt (cdem4345_assembled_lemma1QFactor x n b * cdem4345_assembled_lemma1SFactor x n)

/-- The finite reciprocal-square-root weight in the `T2` estimate. -/
noncomputable def cdem4345_assembled_lemma1T2Weight (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (n - 1), 1 / Real.sqrt j)
    + 1 / (2 * Real.sqrt n)

/-! ## Exact pointwise seams -/

/-- Exact partial-summation decomposition underlying CDEM Lemma 1:

`R(x) = -2x I + sum_{j<n} M(X_j) + M(X_n)/2 - centeredSum`.

This is a pointwise identity.  It is strictly stronger and structurally different from
the target inequality `|R(x)|≤b sqrt(x)`. -/
def cdem4345_assembled_Lemma1ExactDecompositionAt (x : ℝ) (n : ℕ) : Prop :=
  cdem4345_assembled_lemma1Remainder x
    = -2 * x * cdem4345_assembled_lemma1SignedTailIntegral x n
      + (∑ j ∈ Finset.Icc 1 (n - 1), cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j))
      + cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2
      - cdem4345_assembled_lemma1CenteredSum x n

/-- The pointwise Cauchy--Schwarz step for the centered sum. -/
def cdem4345_assembled_Lemma1CenteredCauchyAt (x : ℝ) (n : ℕ) : Prop :=
  cdem4345_assembled_lemma1T3 x n
    ≤ Real.sqrt (cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n) * cdem4345_assembled_lemma1CenteredSquareMass x n)

/-- The signed Euler--Maclaurin/periodic-majorant bound for the centered square mass. -/
def cdem4345_assembled_Lemma1PeriodicMajorantAt (x : ℝ) (n : ℕ) : Prop :=
  cdem4345_assembled_lemma1CenteredSquareMass x n ≤ cdem4345_assembled_lemma1SFactor x n

/-! ## Proven assembly around the seams -/

/-- The exact decomposition implies `|R|≤T1+T2+T3`, provided the standard absolute
integral inequality is supplied for the signed tail. -/
theorem cdem4345_assembled_lemma1_three_term_bound
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hdecomp : cdem4345_assembled_Lemma1ExactDecompositionAt x n)
    (htail_abs :
      |cdem4345_assembled_lemma1SignedTailIntegral x n|
        ≤ ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3) :
    |cdem4345_assembled_lemma1Remainder x| ≤ cdem4345_assembled_lemma1T1 x n + cdem4345_assembled_lemma1T2 x n + cdem4345_assembled_lemma1T3 x n := by
  rw [cdem4345_assembled_Lemma1ExactDecompositionAt] at hdecomp
  rw [hdecomp]
  have hsum :
      |∑ j ∈ Finset.Icc 1 (n - 1), cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|
        ≤ ∑ j ∈ Finset.Icc 1 (n - 1), |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)| :=
    Finset.abs_sum_le_sum_abs _ _
  have htail :
      |-2 * x * cdem4345_assembled_lemma1SignedTailIntegral x n| ≤ cdem4345_assembled_lemma1T1 x n := by
    rw [abs_mul, abs_mul, abs_of_nonneg hx]
    unfold cdem4345_assembled_lemma1T1
    have h2x : 0 ≤ 2 * x := by positivity
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left htail_abs h2x
  have hend : |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2| = |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n)| / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hcenter : |-cdem4345_assembled_lemma1CenteredSum x n| = cdem4345_assembled_lemma1T3 x n := by
    simp [cdem4345_assembled_lemma1T3]
  calc
    |-2 * x * cdem4345_assembled_lemma1SignedTailIntegral x n
        + (∑ j ∈ Finset.Icc 1 (n - 1), cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j))
        + cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2
        - cdem4345_assembled_lemma1CenteredSum x n|
      ≤ |-2 * x * cdem4345_assembled_lemma1SignedTailIntegral x n|
          + |∑ j ∈ Finset.Icc 1 (n - 1), cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|
          + |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2|
          + |-cdem4345_assembled_lemma1CenteredSum x n| := by
        calc
          |_ + _ + _ - _| ≤ |_ + _ + _| + |-_| := abs_add_le _ _
          _ ≤ (|_ + _| + |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2|) + |-_| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ ((|-2 * x * cdem4345_assembled_lemma1SignedTailIntegral x n|
                + |∑ j ∈ Finset.Icc 1 (n - 1), cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|)
                + |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2|) + |-_| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ cdem4345_assembled_lemma1T1 x n
          + ((∑ j ∈ Finset.Icc 1 (n - 1), |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|)
              + |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n)| / 2)
          + cdem4345_assembled_lemma1T3 x n := by
        rw [hend, hcenter]
        linarith
    _ = cdem4345_assembled_lemma1T1 x n + cdem4345_assembled_lemma1T2 x n + cdem4345_assembled_lemma1T3 x n := by
      rfl

/-- The `T1` estimate after the improper-integral comparison has been established.
The conclusion is exactly `2 epsilon sqrt(n) sqrt(x)`. -/
theorem cdem4345_assembled_lemma1_T1_le
    {x ε : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hε : 0 ≤ ε)
    (hint :
      (∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3)
        ≤ ε / cdem4345_assembled_lemma1X x n) :
    cdem4345_assembled_lemma1T1 x n ≤ 2 * ε * Real.sqrt n * Real.sqrt x := by
  have hmul := mul_le_mul_of_nonneg_left hint (show 0 ≤ 2 * x by positivity)
  unfold cdem4345_assembled_lemma1T1
  refine hmul.trans_eq ?_
  unfold cdem4345_assembled_lemma1X
  rw [Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- `T2` from pointwise Mertens bounds at the finitely many `X_j`. -/
theorem cdem4345_assembled_lemma1_T2_le_of_pointwise
    {x ε C : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx : 0 ≤ x) (hε : 0 ≤ ε)
    (hM : ∀ j ∈ Finset.Icc 1 n,
      |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)| ≤ ε * Real.sqrt x / Real.sqrt j)
    (hweight : cdem4345_assembled_lemma1T2Weight n ≤ C) :
    cdem4345_assembled_lemma1T2 x n ≤ ε * Real.sqrt x * C := by
  have hsum :
      (∑ j ∈ Finset.Icc 1 (n - 1), |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|)
        ≤ ∑ j ∈ Finset.Icc 1 (n - 1), ε * Real.sqrt x / Real.sqrt j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hM j (by simp only [Finset.mem_Icc] at hj ⊢; omega)
  have hend := hM n (by simp [hn])
  have hfactor :
      (∑ j ∈ Finset.Icc 1 (n - 1), ε * Real.sqrt x / Real.sqrt j)
          + (ε * Real.sqrt x / Real.sqrt n) / 2
        = ε * Real.sqrt x * cdem4345_assembled_lemma1T2Weight n := by
    unfold cdem4345_assembled_lemma1T2Weight
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · ring
  calc
    cdem4345_assembled_lemma1T2 x n
      ≤ (∑ j ∈ Finset.Icc 1 (n - 1), ε * Real.sqrt x / Real.sqrt j)
          + (ε * Real.sqrt x / Real.sqrt n) / 2 := by
        unfold cdem4345_assembled_lemma1T2
        linarith
    _ = ε * Real.sqrt x * cdem4345_assembled_lemma1T2Weight n := hfactor
    _ ≤ ε * Real.sqrt x * C :=
      mul_le_mul_of_nonneg_left hweight (mul_nonneg hε (Real.sqrt_nonneg _))

/-- Cauchy--Schwarz plus the two displayed factor bounds gives the exact `T3` envelope. -/
theorem cdem4345_assembled_lemma1_T3_le_envelope
    {x b : ℝ} {n : ℕ}
    (hCS : cdem4345_assembled_Lemma1CenteredCauchyAt x n)
    (hQnonneg : 0 ≤ cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n))
    (hSnonneg : 0 ≤ cdem4345_assembled_lemma1CenteredSquareMass x n)
    (hQ : cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n) ≤ cdem4345_assembled_lemma1QFactor x n b)
    (hS : cdem4345_assembled_Lemma1PeriodicMajorantAt x n) :
    cdem4345_assembled_lemma1T3 x n ≤ cdem4345_assembled_lemma1T3Envelope x n b := by
  rw [cdem4345_assembled_Lemma1CenteredCauchyAt] at hCS
  rw [cdem4345_assembled_Lemma1PeriodicMajorantAt] at hS
  unfold cdem4345_assembled_lemma1T3Envelope
  refine hCS.trans (Real.sqrt_le_sqrt ?_)
  exact mul_le_mul hQ hS hSnonneg (hQnonneg.trans hQ)

/-! ## The honest `n=197` specialization -/

def cdem4345_assembled_lemma1FinalN : ℕ := 197
def cdem4345_assembled_lemma1FinalX0 : ℝ := 1600000000000000
noncomputable def cdem4345_assembled_lemma1PreviousMertensEpsilon : ℝ := 1 / 4257
noncomputable def cdem4345_assembled_lemma1PreviousSquarefreeB : ℝ := 36438 / 1000000
noncomputable def cdem4345_assembled_lemma1FinalB : ℝ := 2767 / 100000

/-- Finite scalar `T2` weight check at `n=197`.  This is a fixed 196-term
inequality, not an unbounded analytic input. -/
def cdem4345_assembled_Lemma1N197T2WeightCertificate : Prop :=
  cdem4345_assembled_lemma1T2Weight cdem4345_assembled_lemma1FinalN
    ≤ 2 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100

/-- Exact `T1+T2` fold at `n=197`; no rounded decimal is introduced. -/
theorem cdem4345_assembled_lemma1_T12_n197
    {x : ℝ}
    (hT1 : cdem4345_assembled_lemma1T1 x cdem4345_assembled_lemma1FinalN
      ≤ 2 * cdem4345_assembled_lemma1PreviousMertensEpsilon * Real.sqrt cdem4345_assembled_lemma1FinalN * Real.sqrt x)
    (hT2 : cdem4345_assembled_lemma1T2 x cdem4345_assembled_lemma1FinalN
      ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon * Real.sqrt x
          * (2 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100)) :
    cdem4345_assembled_lemma1T1 x cdem4345_assembled_lemma1FinalN + cdem4345_assembled_lemma1T2 x cdem4345_assembled_lemma1FinalN
      ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon
          * (4 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100) * Real.sqrt x := by
  linarith

/-- Exact combined analytic envelope for the second bootstrap. -/
noncomputable def cdem4345_assembled_lemma1N197CombinedEnvelope (x : ℝ) : ℝ :=
  cdem4345_assembled_lemma1PreviousMertensEpsilon
      * (4 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100) * Real.sqrt x
    + cdem4345_assembled_lemma1T3Envelope x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB

/-- A fixed endpoint numerical proposition.  This is suitable for a verified-interval
certificate; unlike the false rounded component inequalities, it has positive margin. -/
def cdem4345_assembled_Lemma1N197EndpointCertificate : Prop :=
  cdem4345_assembled_lemma1N197CombinedEnvelope cdem4345_assembled_lemma1FinalX0
    ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt cdem4345_assembled_lemma1FinalX0

/-- The elementary monotonicity statement needed to propagate the endpoint certificate.
After division by `sqrt(x)`, it is a monotonicity problem in the negative powers
`x^(-1/6)`, `x^(-1/4)`, and `x^(-1/2)`. -/
def cdem4345_assembled_Lemma1N197EnvelopeAntitone : Prop :=
  AntitoneOn (fun x => cdem4345_assembled_lemma1N197CombinedEnvelope x / Real.sqrt x)
    (Set.Ici cdem4345_assembled_lemma1FinalX0)

/-- The fixed endpoint certificate and the full-range monotonicity theorem propagate the
combined envelope to every `x≥1.6*10^15`. -/
theorem cdem4345_assembled_lemma1_n197_combined_envelope
    (hendpoint : cdem4345_assembled_Lemma1N197EndpointCertificate)
    (hanti : cdem4345_assembled_Lemma1N197EnvelopeAntitone)
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    cdem4345_assembled_lemma1N197CombinedEnvelope x ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hbase0 : 0 < cdem4345_assembled_lemma1FinalX0 := by norm_num [cdem4345_assembled_lemma1FinalX0]
  rw [cdem4345_assembled_Lemma1N197EndpointCertificate] at hendpoint
  rw [cdem4345_assembled_Lemma1N197EnvelopeAntitone] at hanti
  have hmono := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs0 : 0 < Real.sqrt cdem4345_assembled_lemma1FinalX0 := Real.sqrt_pos.2 hbase0
  have hendpoint_div :
      cdem4345_assembled_lemma1N197CombinedEnvelope cdem4345_assembled_lemma1FinalX0 / Real.sqrt cdem4345_assembled_lemma1FinalX0
        ≤ cdem4345_assembled_lemma1FinalB := by
    rw [div_le_iff₀ hs0]
    simpa [mul_comm] using hendpoint
  have hdiv : cdem4345_assembled_lemma1N197CombinedEnvelope x / Real.sqrt x ≤ cdem4345_assembled_lemma1FinalB :=
    hmono.trans hendpoint_div
  rwa [div_le_iff₀ hsx] at hdiv

/-- The analytic `n=197` tail, once the three exact pointwise seams and their component
bounds have been proved.  The two components are combined before the final comparison,
so no false rounded sub-bound is used. -/
theorem cdem4345_assembled_lemma1_n197_tail
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 < x)
    (hthree : |cdem4345_assembled_lemma1Remainder x|
      ≤ cdem4345_assembled_lemma1T1 x cdem4345_assembled_lemma1FinalN + cdem4345_assembled_lemma1T2 x cdem4345_assembled_lemma1FinalN
          + cdem4345_assembled_lemma1T3 x cdem4345_assembled_lemma1FinalN)
    (hT12 : cdem4345_assembled_lemma1T1 x cdem4345_assembled_lemma1FinalN + cdem4345_assembled_lemma1T2 x cdem4345_assembled_lemma1FinalN
      ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon
          * (4 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100) * Real.sqrt x)
    (hT3 : cdem4345_assembled_lemma1T3 x cdem4345_assembled_lemma1FinalN
      ≤ cdem4345_assembled_lemma1T3Envelope x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB)
    (hendpoint : cdem4345_assembled_Lemma1N197EndpointCertificate)
    (hanti : cdem4345_assembled_Lemma1N197EnvelopeAntitone) :
    |cdem4345_assembled_lemma1Remainder x| ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt x := by
  have henv := cdem4345_assembled_lemma1_n197_combined_envelope hendpoint hanti hx.le
  unfold cdem4345_assembled_lemma1N197CombinedEnvelope at henv
  linarith

/-- Honest bounded base-range obligation for Theorem 3 bis.  This is finite: both
endpoints are explicit natural numbers. -/
def cdem4345_assembled_Theorem3BisFiniteWindowCertificate : Prop :=
  ∀ X : ℕ, 438653 < X → X ≤ 1600000000000000 →
    |cdem4345_assembled_lemma1Remainder X| ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt X

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: periodic-majorant reduction

The difficult part of the `T3` estimate is not Cauchy--Schwarz; it is the signed
Euler--Maclaurin estimate on each interval `(X_{k+1},X_k]`.  This file exposes exactly
that local estimate and proves the summation layer which yields
`cdem4345_assembled_Lemma1PeriodicMajorantAt`.

The signed differences of `rho` are retained.  Taking absolute values blockwise would
destroy the telescope and is not a faithful proof of the printed constant.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- `h(a)`, the characteristic function of integers not divisible by `4` or `9`. -/
def cdem4345_assembled_lemma1PeriodWeight (a : ℕ) : ℝ :=
  if 4 ∣ a ∨ 9 ∣ a then 0 else 1

/-- `H(z)=floor z-floor(z/4)-floor(z/9)+floor(z/36)`. -/
noncomputable def cdem4345_assembled_lemma1H (z : ℝ) : ℝ :=
  (⌊z⌋₊ : ℝ) - (⌊z / 4⌋₊ : ℝ) - (⌊z / 9⌋₊ : ℝ) + (⌊z / 36⌋₊ : ℝ)

/-- `rho(z)=H(z)-(2/3)z`. -/
noncomputable def cdem4345_assembled_lemma1Rho (z : ℝ) : ℝ :=
  cdem4345_assembled_lemma1H z - (2 / 3 : ℝ) * z

/-- The centered square mass in the block `(X_{k+1},X_k]`. -/
noncomputable def cdem4345_assembled_lemma1BlockMass (x : ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊,
    cdem4345_assembled_lemma1PeriodWeight a * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2

/-- The paper's signed upper envelope for one block, after the main term is bounded by
the shifted square-root telescope and `|r_k|≤2/3`. -/
noncomputable def cdem4345_assembled_lemma1BlockEnvelope (x : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt x / 18
      * (1 / Real.sqrt ((k : ℝ) - 2 / 100)
        - 1 / Real.sqrt ((k : ℝ) + 98 / 100))
    + 1 / 4 * (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (k + 1)))
    + 2 / 3

/-- The residual square mass below `X_{N+1}` after the first `N-n+1` blocks. -/
noncomputable def cdem4345_assembled_lemma1BlockRemainder (x : ℝ) (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊,
    cdem4345_assembled_lemma1PeriodWeight a * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2

/-- The one genuine local analytic seam: the signed Euler--Maclaurin block estimate.
It is local in both `x` and `k`; it does not state the final squarefree bound. -/
def cdem4345_assembled_Lemma1PeriodicBlockEstimateAt (x : ℝ) (k : ℕ) : Prop :=
  cdem4345_assembled_lemma1BlockMass x k ≤ cdem4345_assembled_lemma1BlockEnvelope x k

/-- The definitions of the period weight agree. -/
theorem cdem4345_assembled_centeredSquareMass_eq_periodWeight (x : ℝ) (n : ℕ) :
    cdem4345_assembled_lemma1CenteredSquareMass x n
      = ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
          cdem4345_assembled_lemma1PeriodWeight a * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2 := by
  unfold cdem4345_assembled_lemma1CenteredSquareMass cdem4345_assembled_lemma1PeriodWeight
  rfl

/-- Summation layer for the periodic majorant.

The three auxiliary hypotheses after the local block estimates are elementary finite
interval facts:

* `hpartition` is the disjoint partition into blocks plus the lower remainder;
* `hremainder` uses `|fract-1/2|≤1/2` and counts the period weight by `H`;
* `hfold` is the exact telescope (including the signed `rho` endpoints) and the choice
  `N=floor((x/144)^(1/3))` used in the paper.

They are parameters here so the genuinely difficult local block estimate is not hidden
inside an opaque aggregate proposition. -/
theorem cdem4345_assembled_lemma1_periodicMajorant_of_blocks
    {x : ℝ} {n N : ℕ} (hnN : n ≤ N)
    (hpartition :
      cdem4345_assembled_lemma1CenteredSquareMass x n
        = (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockMass x k)
            + cdem4345_assembled_lemma1BlockRemainder x N)
    (hblocks : ∀ k ∈ Finset.Icc n N, cdem4345_assembled_Lemma1PeriodicBlockEstimateAt x k)
    (hremainder : cdem4345_assembled_lemma1BlockRemainder x N ≤ 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (N + 1)))
    (hfold :
      (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockEnvelope x k)
          + 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (N + 1))
        ≤ cdem4345_assembled_lemma1SFactor x n) :
    cdem4345_assembled_Lemma1PeriodicMajorantAt x n := by
  rw [cdem4345_assembled_Lemma1PeriodicMajorantAt]
  rw [hpartition]
  calc
    (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockMass x k) + cdem4345_assembled_lemma1BlockRemainder x N
      ≤ (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockEnvelope x k)
          + 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (N + 1)) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro k hk
          exact hblocks k hk
        · exact hremainder
    _ ≤ cdem4345_assembled_lemma1SFactor x n := hfold

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the signed periodic-block frontier

This file separates the two estimates which were compressed into
`cdem4345_assembled_Lemma1PeriodicBlockEstimateAt`:

1. the paper's signed Euler--Maclaurin estimate, with its single remainder
   `r_k` satisfying `|r_k| <= 2/3`;
2. the elementary but very sharp comparison of the printed main coefficient with
   the shifted square-root difference at `k - 0.02` and `k + 0.98`.

The first item is the paper's “easy but detailed and delicate study of a few
functions”.  It is represented below by the local proposition
`cdem4345_assembled_Lemma1PeriodicSignedRemainderAt`; no pointwise absolute-value estimate is substituted
for it.  The second item is isolated as the one-variable proposition
`cdem4345_assembled_Lemma1RawCoefficientShiftAt`.  Supplying those two local facts proves the existing
block estimate.

Everything after the local facts is proved here.  In particular, both the shifted
square-root differences and the signed `rho` differences telescope *exactly*.  Thus
the two endpoint `rho` terms cancel when the lower remainder `H(X_{N+1})/4` is added.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-! ## The two printed local expressions -/

/-- The coefficient of `sqrt x` in CDEM's displayed estimate for `S_k`, before the
comparison with the shifted square-root difference. -/
noncomputable def cdem4345_assembled_lemma1RawBlockCoefficient (k : ℕ) : ℝ :=
  (16 / 9 * (k : ℝ) + 4 / 3 + 1 / (6 * (k : ℝ))) * Real.sqrt k
    - (16 / 9 * (k : ℝ) + 4 / 9 + 1 / (6 * ((k : ℝ) + 1)))
        * Real.sqrt (k + 1)

/-- The full main term in the displayed block estimate. -/
noncomputable def cdem4345_assembled_lemma1RawBlockMain (x : ℝ) (k : ℕ) : ℝ :=
  cdem4345_assembled_lemma1RawBlockCoefficient k * Real.sqrt x

/-- The endpoint whose successive difference is the paper's `0.02/0.98` majorant. -/
noncomputable def cdem4345_assembled_lemma1ShiftedSqrtEndpoint (k : ℕ) : ℝ :=
  1 / Real.sqrt ((k : ℝ) - 2 / 100)

/-- The shifted square-root part of `cdem4345_assembled_lemma1BlockEnvelope`. -/
noncomputable def cdem4345_assembled_lemma1ShiftedBlockMain (x : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt x / 18
    * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint k - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (k + 1))

/-- The elementary sharp comparison which CDEM records for `k > 4`.  It is independent
of `x`; multiplication by `sqrt x` is performed in
`cdem4345_assembled_lemma1RawBlockMain_le_shiftedBlockMain`. -/
def cdem4345_assembled_Lemma1RawCoefficientShiftAt (k : ℕ) : Prop :=
  cdem4345_assembled_lemma1RawBlockCoefficient k
    ≤ 1 / 18
      * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint k - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (k + 1))

/-- The smallest faithful local residual from the paper's signed block calculation.
The remainder is existential and signed.  Keeping it in this form is what makes the
subsequent `rho` telescope available. -/
def cdem4345_assembled_Lemma1PeriodicSignedRemainderAt (x : ℝ) (k : ℕ) : Prop :=
  ∃ r : ℝ, |r| ≤ 2 / 3 ∧
    cdem4345_assembled_lemma1BlockMass x k
      ≤ cdem4345_assembled_lemma1RawBlockMain x k
        + 1 / 4
            * (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (k + 1)))
        + r

/-- Successive shifted endpoints really have the printed arguments `k-0.02` and
`k+0.98`. -/
theorem cdem4345_assembled_lemma1ShiftedBlockMain_eq_printed (x : ℝ) (k : ℕ) :
    cdem4345_assembled_lemma1ShiftedBlockMain x k
      = Real.sqrt x / 18
          * (1 / Real.sqrt ((k : ℝ) - 2 / 100)
            - 1 / Real.sqrt ((k : ℝ) + 98 / 100)) := by
  have harg : (((k + 1 : ℕ) : ℝ) - 2 / 100)
      = (k : ℝ) + 98 / 100 := by
    push_cast
    ring
  rw [cdem4345_assembled_lemma1ShiftedBlockMain, cdem4345_assembled_lemma1ShiftedSqrtEndpoint,
    cdem4345_assembled_lemma1ShiftedSqrtEndpoint, harg]

/-- The existing block envelope is exactly “shifted main + signed rho difference
+ 2/3”. -/
theorem cdem4345_assembled_lemma1BlockEnvelope_eq_signed (x : ℝ) (k : ℕ) :
    cdem4345_assembled_lemma1BlockEnvelope x k
      = cdem4345_assembled_lemma1ShiftedBlockMain x k
        + 1 / 4
            * (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (k + 1)))
        + 2 / 3 := by
  rw [cdem4345_assembled_lemma1BlockEnvelope, cdem4345_assembled_lemma1ShiftedBlockMain_eq_printed]

/-- The coefficient comparison scales by `sqrt x` without any extra hypothesis on
`x`, since the real square root is nonnegative. -/
theorem cdem4345_assembled_lemma1RawBlockMain_le_shiftedBlockMain
    {x : ℝ} {k : ℕ} (hshift : cdem4345_assembled_Lemma1RawCoefficientShiftAt k) :
    cdem4345_assembled_lemma1RawBlockMain x k ≤ cdem4345_assembled_lemma1ShiftedBlockMain x k := by
  rw [cdem4345_assembled_Lemma1RawCoefficientShiftAt] at hshift
  rw [cdem4345_assembled_lemma1RawBlockMain, cdem4345_assembled_lemma1ShiftedBlockMain]
  calc
    cdem4345_assembled_lemma1RawBlockCoefficient k * Real.sqrt x
        ≤ (1 / 18
            * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint k - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (k + 1)))
              * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hshift (Real.sqrt_nonneg x)
    _ = Real.sqrt x / 18
          * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint k - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (k + 1)) := by
      ring

/-- The paper's two local facts imply the original block-estimate interface.  The
only use of `|r_k| <= 2/3` is the one-sided consequence `r_k <= 2/3`; the signed `rho`
difference is left untouched. -/
theorem cdem4345_assembled_lemma1_periodicBlockEstimate_of_signed
    {x : ℝ} {k : ℕ}
    (hsigned : cdem4345_assembled_Lemma1PeriodicSignedRemainderAt x k)
    (hshift : cdem4345_assembled_Lemma1RawCoefficientShiftAt k) :
    cdem4345_assembled_Lemma1PeriodicBlockEstimateAt x k := by
  rcases hsigned with ⟨r, hr, hblock⟩
  have hrle : r ≤ 2 / 3 := (le_abs_self r).trans hr
  have hmain := cdem4345_assembled_lemma1RawBlockMain_le_shiftedBlockMain
    (x := x) (k := k) hshift
  rw [cdem4345_assembled_Lemma1PeriodicBlockEstimateAt, cdem4345_assembled_lemma1BlockEnvelope_eq_signed]
  calc
    cdem4345_assembled_lemma1BlockMass x k
        ≤ cdem4345_assembled_lemma1RawBlockMain x k
            + 1 / 4
                * (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (k + 1)))
            + r := hblock
    _ ≤ cdem4345_assembled_lemma1ShiftedBlockMain x k
            + 1 / 4
                * (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (k + 1)))
            + 2 / 3 := by
      gcongr

/-! ## Exact finite telescopes -/

/-- A closed-interval version of the basic successive-difference telescope. -/
theorem cdem4345_assembled_sum_Icc_sub_succ (f : ℕ → ℝ) {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Finset.Icc n N, (f k - f (k + 1))) = f n - f (N + 1) := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ N hnN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : n ≤ N + 1), ih]
      ring

/-- Exact telescope of the shifted square-root main terms. -/
theorem cdem4345_assembled_sum_Icc_lemma1ShiftedBlockMain
    (x : ℝ) {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1ShiftedBlockMain x k)
      = Real.sqrt x / 18
          * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint n - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (N + 1)) := by
  simp_rw [cdem4345_assembled_lemma1ShiftedBlockMain]
  rw [← Finset.mul_sum, cdem4345_assembled_sum_Icc_sub_succ _ hnN]

/-- Exact telescope of the signed `rho` differences. -/
theorem cdem4345_assembled_sum_Icc_lemma1Rho_difference
    (x : ℝ) {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Finset.Icc n N,
        (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (k + 1))))
      = cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x n) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (N + 1)) := by
  exact cdem4345_assembled_sum_Icc_sub_succ (fun k => cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x k)) hnN

/-- The exact sum of all block envelopes.  No endpoint is estimated here. -/
theorem cdem4345_assembled_sum_Icc_lemma1BlockEnvelope
    (x : ℝ) {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockEnvelope x k)
      = Real.sqrt x / 18
          * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint n - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (N + 1))
        + 1 / 4
            * (cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x n) - cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x (N + 1)))
        + 2 / 3 * ((N + 1 - n : ℕ) : ℝ) := by
  simp_rw [cdem4345_assembled_lemma1BlockEnvelope_eq_signed]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    cdem4345_assembled_sum_Icc_lemma1ShiftedBlockMain x hnN, ← Finset.mul_sum,
    cdem4345_assembled_sum_Icc_lemma1Rho_difference x hnN, Finset.sum_const, Nat.card_Icc,
    nsmul_eq_mul]
  ring

/-- Rearrangement of the definition of `rho`. -/
theorem cdem4345_assembled_lemma1H_eq_two_thirds_add_rho (z : ℝ) :
    cdem4345_assembled_lemma1H z = 2 / 3 * z + cdem4345_assembled_lemma1Rho z := by
  rw [cdem4345_assembled_lemma1Rho]
  ring

/-- Adding the lower remainder count cancels the terminal `rho(X_{N+1})` exactly.
This is the signed finite telescope used in the paper. -/
theorem cdem4345_assembled_lemma1BlockEnvelope_add_remainder_count
    (x : ℝ) {n N : ℕ} (hnN : n ≤ N) :
    (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockEnvelope x k)
        + 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (N + 1))
      = Real.sqrt x / 18
          * (cdem4345_assembled_lemma1ShiftedSqrtEndpoint n - cdem4345_assembled_lemma1ShiftedSqrtEndpoint (N + 1))
        + 1 / 4 * cdem4345_assembled_lemma1Rho (cdem4345_assembled_lemma1X x n)
        + 1 / 6 * cdem4345_assembled_lemma1X x (N + 1)
        + 2 / 3 * ((N + 1 - n : ℕ) : ℝ) := by
  rw [cdem4345_assembled_sum_Icc_lemma1BlockEnvelope x hnN,
    cdem4345_assembled_lemma1H_eq_two_thirds_add_rho]
  ring

/-! ## The elementary lower-remainder estimate -/

/-- The centered fractional square is at most `1/4`. -/
theorem cdem4345_assembled_lemma1_centered_fract_sq_le_quarter (t : ℝ) :
    (Int.fract t - 1 / 2) ^ 2 ≤ (1 / 4 : ℝ) := by
  have h0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have h1 : Int.fract t ≤ 1 := (Int.fract_lt_one t).le
  nlinarith [sq_nonneg (Int.fract t - 1 / 2)]

theorem cdem4345_assembled_lemma1PeriodWeight_nonneg (a : ℕ) : 0 ≤ cdem4345_assembled_lemma1PeriodWeight a := by
  rw [cdem4345_assembled_lemma1PeriodWeight]
  split <;> norm_num

/-- The lower residual mass is at most one quarter of the exact period count. -/
theorem cdem4345_assembled_lemma1BlockRemainder_le_quarter_period_count (x : ℝ) (N : ℕ) :
    cdem4345_assembled_lemma1BlockRemainder x N
      ≤ 1 / 4
          * ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊, cdem4345_assembled_lemma1PeriodWeight a := by
  rw [cdem4345_assembled_lemma1BlockRemainder]
  calc
    (∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊,
        cdem4345_assembled_lemma1PeriodWeight a
          * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2)
        ≤ ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊,
            cdem4345_assembled_lemma1PeriodWeight a * (1 / 4 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left
        (cdem4345_assembled_lemma1_centered_fract_sq_le_quarter _) (cdem4345_assembled_lemma1PeriodWeight_nonneg a)
    _ = 1 / 4
          * ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊, cdem4345_assembled_lemma1PeriodWeight a := by
      rw [← Finset.sum_mul]
      ring

/-- Exact period counting is elementary and deliberately kept distinct from the
analytic local estimate. -/
def cdem4345_assembled_Lemma1PeriodCountAt (z : ℝ) : Prop :=
  (∑ a ∈ Finset.Icc 1 ⌊z⌋₊, cdem4345_assembled_lemma1PeriodWeight a) = cdem4345_assembled_lemma1H z

/-- Once the exact period count is supplied, the lower-remainder hypothesis of
`cdem4345_assembled_lemma1_periodicMajorant_of_blocks` follows automatically. -/
theorem cdem4345_assembled_lemma1BlockRemainder_le_quarter_H
    {x : ℝ} {N : ℕ} (hcount : cdem4345_assembled_Lemma1PeriodCountAt (cdem4345_assembled_lemma1X x (N + 1))) :
    cdem4345_assembled_lemma1BlockRemainder x N ≤ 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (N + 1)) := by
  rw [cdem4345_assembled_Lemma1PeriodCountAt] at hcount
  rw [← hcount]
  exact cdem4345_assembled_lemma1BlockRemainder_le_quarter_period_count x N

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: exact counting of the period weight

The lower block remainder is bounded by one quarter of the number of integers not
divisible by `4` or `9`.  This file proves the elementary inclusion--exclusion count

`sum_{a <= N} h(a) = N - floor(N/4) - floor(N/9) + floor(N/36)`

and hence discharges `cdem4345_assembled_Lemma1PeriodCountAt`.  This is an exact finite identity, not an
analytic estimate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- Real-valued indicator of divisibility. -/
private def cdem4345_assembled_dvdIndicator (d a : ℕ) : ℝ :=
  if d ∣ a then 1 else 0

/-- A reusable induction: if division by `d` has the expected successor increment,
the number of multiples of `d` in `[1,N]` is `N/d`. -/
private theorem cdem4345_assembled_sum_dvdIndicator_of_div_succ
    (d : ℕ)
    (hstep : ∀ N : ℕ,
      (N + 1) / d = N / d + if d ∣ N + 1 then 1 else 0) :
    ∀ N : ℕ,
      (∑ a ∈ Finset.Icc 1 N, cdem4345_assembled_dvdIndicator d a) = ((N / d : ℕ) : ℝ) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, hstep]
      by_cases hd : d ∣ N + 1 <;> simp [cdem4345_assembled_dvdIndicator, hd]

private theorem cdem4345_assembled_div_succ_four (N : ℕ) :
    (N + 1) / 4 = N / 4 + if 4 ∣ N + 1 then 1 else 0 := by
  by_cases h : 4 ∣ N + 1
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

private theorem cdem4345_assembled_div_succ_nine (N : ℕ) :
    (N + 1) / 9 = N / 9 + if 9 ∣ N + 1 then 1 else 0 := by
  by_cases h : 9 ∣ N + 1
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

private theorem cdem4345_assembled_div_succ_thirtySix (N : ℕ) :
    (N + 1) / 36 = N / 36 + if 36 ∣ N + 1 then 1 else 0 := by
  by_cases h : 36 ∣ N + 1
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

private theorem cdem4345_assembled_sum_dvdIndicator_four (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, cdem4345_assembled_dvdIndicator 4 a) = ((N / 4 : ℕ) : ℝ) :=
  cdem4345_assembled_sum_dvdIndicator_of_div_succ 4 cdem4345_assembled_div_succ_four N

private theorem cdem4345_assembled_sum_dvdIndicator_nine (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, cdem4345_assembled_dvdIndicator 9 a) = ((N / 9 : ℕ) : ℝ) :=
  cdem4345_assembled_sum_dvdIndicator_of_div_succ 9 cdem4345_assembled_div_succ_nine N

private theorem cdem4345_assembled_sum_dvdIndicator_thirtySix (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, cdem4345_assembled_dvdIndicator 36 a) = ((N / 36 : ℕ) : ℝ) :=
  cdem4345_assembled_sum_dvdIndicator_of_div_succ 36 cdem4345_assembled_div_succ_thirtySix N

/-- Pointwise inclusion--exclusion for “not divisible by `4` or `9`”. -/
private theorem cdem4345_assembled_lemma1PeriodWeight_eq_indicators (a : ℕ) :
    cdem4345_assembled_lemma1PeriodWeight a
      = 1 - cdem4345_assembled_dvdIndicator 4 a - cdem4345_assembled_dvdIndicator 9 a + cdem4345_assembled_dvdIndicator 36 a := by
  by_cases h4 : 4 ∣ a
  · by_cases h9 : 9 ∣ a
    · have h36 : 36 ∣ a := by omega
      simp [cdem4345_assembled_lemma1PeriodWeight, cdem4345_assembled_dvdIndicator, h4, h9, h36]
    · have h36 : ¬36 ∣ a := by
        intro h
        apply h9
        omega
      simp [cdem4345_assembled_lemma1PeriodWeight, cdem4345_assembled_dvdIndicator, h4, h9, h36]
  · by_cases h9 : 9 ∣ a
    · have h36 : ¬36 ∣ a := by
        intro h
        apply h4
        omega
      simp [cdem4345_assembled_lemma1PeriodWeight, cdem4345_assembled_dvdIndicator, h4, h9, h36]
    · have h36 : ¬36 ∣ a := by
        intro h
        apply h4
        omega
      simp [cdem4345_assembled_lemma1PeriodWeight, cdem4345_assembled_dvdIndicator, h4, h9, h36]

/-- Exact natural-cutoff count of the period weight. -/
theorem cdem4345_assembled_sum_lemma1PeriodWeight_Icc (N : ℕ) :
    (∑ a ∈ Finset.Icc 1 N, cdem4345_assembled_lemma1PeriodWeight a)
      = (N : ℝ) - (N / 4 : ℕ) - (N / 9 : ℕ) + (N / 36 : ℕ) := by
  simp_rw [cdem4345_assembled_lemma1PeriodWeight_eq_indicators]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    cdem4345_assembled_sum_dvdIndicator_four, cdem4345_assembled_sum_dvdIndicator_nine,
    cdem4345_assembled_sum_dvdIndicator_thirtySix]
  push_cast
  ring

/-- The exact count at a real cutoff is the paper's `H(z)`. -/
theorem cdem4345_assembled_lemma1PeriodCountAt_proven (z : ℝ) : cdem4345_assembled_Lemma1PeriodCountAt z := by
  rw [cdem4345_assembled_Lemma1PeriodCountAt, cdem4345_assembled_sum_lemma1PeriodWeight_Icc]
  unfold cdem4345_assembled_lemma1H
  have h4 : ⌊z / (4 : ℝ)⌋₊ = ⌊z⌋₊ / 4 := by
    simpa using Nat.floor_div_natCast z 4
  have h9 : ⌊z / (9 : ℝ)⌋₊ = ⌊z⌋₊ / 9 := by
    simpa using Nat.floor_div_natCast z 9
  have h36 : ⌊z / (36 : ℝ)⌋₊ = ⌊z⌋₊ / 36 := by
    simpa using Nat.floor_div_natCast z 36
  rw [h4, h9, h36]

/-- Unconditional lower-remainder estimate after discharging the period count. -/
theorem cdem4345_assembled_lemma1BlockRemainder_le_quarter_H_proven (x : ℝ) (N : ℕ) :
    cdem4345_assembled_lemma1BlockRemainder x N ≤ 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (N + 1)) :=
  cdem4345_assembled_lemma1BlockRemainder_le_quarter_H
    (cdem4345_assembled_lemma1PeriodCountAt_proven (cdem4345_assembled_lemma1X x (N + 1)))

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the sharp `0.02/0.98` scalar comparison

This file proves `cdem4345_assembled_Lemma1RawCoefficientShiftAt k` for every `k > 4`.  The proof is
uniform; it does not check a finite sample of values.

Put

`z(t) = (sqrt(t+1)-sqrt(t))^2`.

Rationalizing the two coefficients gives

`raw(k) = (2/9) z(k) sqrt(z(k)) (1+2z(k)^2)/(1-z(k)^2)`

and

`shift(k) = (2/9) z(k-1/50) sqrt(z(k-1/50))/(1-z(k-1/50)^2)`.

If `z=z(k)` and `Z=z(k-1/50)`, the identity

`z(t) + 1/z(t) = 4t+2`

gives exactly

`(Z-z)(1-zZ) = (2/25)zZ`.

For `k>=5`, `z<=1/(4k)<=1/20`.  It is therefore enough to check

`(1+(2/25)z)^3 >= (1+2z^2)^2`.

After expansion, the positive cubic term may be discarded and the negative terms are
bounded by `4z^2 <= z/5` and `4z^4 <= z/2000`.  The remaining margin is
`(6/25-1/5-1/2000)z = 79z/2000`.  Thus every decimal in the comparison is accounted
for by exact rational arithmetic.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

/-- The rationalized square-root gap. -/
noncomputable def cdem4345_assembled_lemma1Gap (t : ℝ) : ℝ :=
  (Real.sqrt (t + 1) - Real.sqrt t) ^ 2

/-- Normal form of the raw coefficient. -/
noncomputable def cdem4345_assembled_lemma1GapRawCoefficient (z : ℝ) : ℝ :=
  2 / 9 * (z * Real.sqrt z * (1 + 2 * z ^ 2)) / (1 - z ^ 2)

/-- Normal form of the shifted reciprocal-square-root coefficient. -/
noncomputable def cdem4345_assembled_lemma1GapShiftCoefficient (z : ℝ) : ℝ :=
  2 / 9 * (z * Real.sqrt z) / (1 - z ^ 2)

/-! ## Exact identities for the square-root gap -/

theorem cdem4345_assembled_lemma1Gap_pos {t : ℝ} (ht : 0 ≤ t) : 0 < cdem4345_assembled_lemma1Gap t := by
  have hs : Real.sqrt t < Real.sqrt (t + 1) :=
    Real.sqrt_lt_sqrt ht (by linarith)
  rw [cdem4345_assembled_lemma1Gap]
  positivity

/-- Rationalization of the gap. -/
theorem cdem4345_assembled_lemma1Gap_eq_inv_sum_sq {t : ℝ} (ht : 0 ≤ t) :
    cdem4345_assembled_lemma1Gap t = 1 / (Real.sqrt (t + 1) + Real.sqrt t) ^ 2 := by
  have ht1 : 0 ≤ t + 1 := by linarith
  have hprod :
      (Real.sqrt (t + 1) - Real.sqrt t)
          * (Real.sqrt (t + 1) + Real.sqrt t) = 1 := by
    nlinarith [Real.sq_sqrt ht, Real.sq_sqrt ht1]
  have hsum : 0 < Real.sqrt (t + 1) + Real.sqrt t := by
    have : 0 < Real.sqrt (t + 1) := Real.sqrt_pos.2 (by linarith)
    positivity
  rw [cdem4345_assembled_lemma1Gap, eq_div_iff (pow_ne_zero 2 hsum.ne')]
  rw [← mul_pow, hprod]
  norm_num

/-- Reciprocal identity for the gap. -/
theorem cdem4345_assembled_lemma1Gap_add_inv {t : ℝ} (ht : 0 ≤ t) :
    cdem4345_assembled_lemma1Gap t + 1 / cdem4345_assembled_lemma1Gap t = 4 * t + 2 := by
  have ht1 : 0 ≤ t + 1 := by linarith
  have hgap := cdem4345_assembled_lemma1Gap_pos ht
  have hprod :
      (Real.sqrt (t + 1) - Real.sqrt t)
          * (Real.sqrt (t + 1) + Real.sqrt t) = 1 := by
    nlinarith [Real.sq_sqrt ht, Real.sq_sqrt ht1]
  have hgap_ne : (Real.sqrt (t + 1) - Real.sqrt t) ^ 2 ≠ 0 := by
    simpa [cdem4345_assembled_lemma1Gap] using hgap.ne'
  have hinv : 1 / cdem4345_assembled_lemma1Gap t
      = (Real.sqrt (t + 1) + Real.sqrt t) ^ 2 := by
    rw [cdem4345_assembled_lemma1Gap, div_eq_iff hgap_ne]
    calc
      1 = ((Real.sqrt (t + 1) - Real.sqrt t)
            * (Real.sqrt (t + 1) + Real.sqrt t)) ^ 2 := by rw [hprod]; norm_num
      _ = (Real.sqrt (t + 1) + Real.sqrt t) ^ 2
            * (Real.sqrt (t + 1) - Real.sqrt t) ^ 2 := by ring
  rw [hinv, cdem4345_assembled_lemma1Gap]
  nlinarith [Real.sq_sqrt ht, Real.sq_sqrt ht1]

/-- Coarse but uniform gap bound. -/
theorem cdem4345_assembled_lemma1Gap_le_inv_four_mul {t : ℝ} (ht : 0 < t) :
    cdem4345_assembled_lemma1Gap t ≤ 1 / (4 * t) := by
  have ht0 := ht.le
  have ht1 : 0 ≤ t + 1 := by linarith
  have hsqrt : Real.sqrt t ≤ Real.sqrt (t + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hcross : 0 ≤ Real.sqrt t * (Real.sqrt (t + 1) - Real.sqrt t) :=
    mul_nonneg (Real.sqrt_nonneg t) (sub_nonneg.mpr hsqrt)
  have hden : 4 * t
      ≤ (Real.sqrt (t + 1) + Real.sqrt t) ^ 2 := by
    nlinarith [Real.sq_sqrt ht0, Real.sq_sqrt ht1,
      sq_nonneg (Real.sqrt (t + 1) - Real.sqrt t), hcross]
  rw [cdem4345_assembled_lemma1Gap_eq_inv_sum_sq ht0]
  exact one_div_le_one_div_of_le (by positivity) hden

/-! ## The exact coefficient normalizations -/

/-- Algebraic normalization of CDEM's raw coefficient. -/
theorem cdem4345_assembled_lemma1RawBlockCoefficient_eq_gap
    {k : ℕ} (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1RawBlockCoefficient k = cdem4345_assembled_lemma1GapRawCoefficient (cdem4345_assembled_lemma1Gap k) := by
  let u : ℝ := Real.sqrt k
  let v : ℝ := Real.sqrt (k + 1)
  let p : ℝ := u + v
  let d : ℝ := v - u
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hk1 : (0 : ℝ) ≤ k + 1 := by positivity
  have hu2 : u ^ 2 = (k : ℝ) := by
    simpa [u] using Real.sq_sqrt hk0
  have hv2 : v ^ 2 = (k : ℝ) + 1 := by
    simpa [v] using Real.sq_sqrt hk1
  have hu : 0 < u := Real.sqrt_pos.2 (by exact_mod_cast hk)
  have hv : 0 < v := Real.sqrt_pos.2 (by positivity)
  have huv : u < v := by
    dsimp [u, v]
    apply Real.sqrt_lt_sqrt hk0
    push_cast
    linarith
  have hp : 1 < p := by
    have hv1 : 1 ≤ v := by
      dsimp [v]
      apply Real.le_sqrt_of_sq_le
      norm_num
    dsimp [p]
    linarith
  have hdp : d * p = 1 := by
    dsimp [d, p]
    nlinarith [hu2, hv2]
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : d = 1 / p := by
    rw [eq_div_iff hp0.ne']
    exact hdp
  have huform : u = (p - d) / 2 := by
    dsimp [p, d]
    ring
  have hvform : v = (p + d) / 2 := by
    dsimp [p, d]
    ring
  have hinv0 : 0 < 1 / p := by positivity
  have hinv1 : 1 / p < 1 := (div_lt_one hp0).2 hp
  have hsub : 0 < p - 1 / p := by
    rw [sub_pos, div_lt_iff₀ hp0]
    nlinarith [sq_nonneg (p - 1)]
  have hplus : 0 < p + 1 / p := by positivity
  have hgapden : 0 < 1 - (1 / p) ^ 4 := by
    rw [show 1 - (1 / p) ^ 4
        = (1 - 1 / p) * (1 + 1 / p) * (1 + (1 / p) ^ 2) by ring]
    positivity
  have hp2gt : 1 < p ^ 2 := by
    nlinarith [mul_pos hp0 (sub_pos.mpr hp)]
  have hp4gt : 1 < p ^ 4 := by
    have hp2pos : 0 < p ^ 2 := sq_pos_of_pos hp0
    nlinarith [mul_pos hp2pos (sub_pos.mpr hp2gt)]
  have hp2ne : -1 + p ^ 2 ≠ 0 := by nlinarith
  have hp4ne : -1 + p ^ 4 ≠ 0 := by nlinarith
  have hp2subne : p ^ 2 - 1 ≠ 0 := (sub_pos.mpr hp2gt).ne'
  have hp4subne : p ^ 4 - 1 ≠ 0 := (sub_pos.mpr hp4gt).ne'
  have hp2subsqne : (p ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hp2subne
  have hp2sqne : 1 - p ^ 2 * 2 + p ^ 4 ≠ 0 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hp2gt)]
  have hgap : cdem4345_assembled_lemma1Gap (k : ℝ) = d ^ 2 := by
    unfold cdem4345_assembled_lemma1Gap
    dsimp [d, v, u]
  have hsqrtgap : Real.sqrt (cdem4345_assembled_lemma1Gap (k : ℝ)) = d := by
    rw [hgap, Real.sqrt_sq_eq_abs, abs_of_pos]
    dsimp [d]
    exact sub_pos.mpr huv
  rw [cdem4345_assembled_lemma1RawBlockCoefficient, cdem4345_assembled_lemma1GapRawCoefficient, hsqrtgap, hgap]
  change (16 / 9 * (k : ℝ) + 4 / 3 + 1 / (6 * (k : ℝ))) * u
      - (16 / 9 * (k : ℝ) + 4 / 9 + 1 / (6 * ((k : ℝ) + 1))) * v
    = 2 / 9 * (d ^ 2 * d * (1 + 2 * (d ^ 2) ^ 2)) /
        (1 - (d ^ 2) ^ 2)
  rw [← hv2, ← hu2, huform, hvform, hd]
  field_simp [hp0.ne', hsub.ne', hplus.ne', hgapden.ne',
    hp2ne, hp4ne, hp2sqne]
  field_simp [hp2subne, hp4subne, hp2subsqne]
  ring

/-- Algebraic normalization of the shifted reciprocal-square-root difference. -/
theorem cdem4345_assembled_lemma1_shiftedCoefficient_eq_gap
    {t : ℝ} (ht : 0 < t) :
    1 / 18 * (1 / Real.sqrt t - 1 / Real.sqrt (t + 1))
      = cdem4345_assembled_lemma1GapShiftCoefficient (cdem4345_assembled_lemma1Gap t) := by
  let u : ℝ := Real.sqrt t
  let v : ℝ := Real.sqrt (t + 1)
  let p : ℝ := u + v
  let d : ℝ := v - u
  have ht0 := ht.le
  have ht1 : 0 ≤ t + 1 := by linarith
  have hu2 : u ^ 2 = t := by simpa [u] using Real.sq_sqrt ht0
  have hv2 : v ^ 2 = t + 1 := by simpa [v] using Real.sq_sqrt ht1
  have hu : 0 < u := Real.sqrt_pos.2 ht
  have hv : 0 < v := Real.sqrt_pos.2 (by linarith)
  have huv : u < v := by
    dsimp [u, v]
    exact Real.sqrt_lt_sqrt ht.le (by linarith)
  have hp : 1 < p := by
    have hv1 : 1 ≤ v := by
      dsimp [v]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    dsimp [p]
    linarith
  have hdp : d * p = 1 := by
    dsimp [d, p]
    nlinarith [hu2, hv2]
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hd : d = 1 / p := by
    rw [eq_div_iff hp0.ne']
    exact hdp
  have huform : u = (p - d) / 2 := by
    dsimp [p, d]
    ring
  have hvform : v = (p + d) / 2 := by
    dsimp [p, d]
    ring
  have hinv0 : 0 < 1 / p := by positivity
  have hinv1 : 1 / p < 1 := (div_lt_one hp0).2 hp
  have hsub : 0 < p - 1 / p := by
    rw [sub_pos, div_lt_iff₀ hp0]
    nlinarith [sq_nonneg (p - 1)]
  have hplus : 0 < p + 1 / p := by positivity
  have hgapden : 0 < 1 - (1 / p) ^ 4 := by
    rw [show 1 - (1 / p) ^ 4
        = (1 - 1 / p) * (1 + 1 / p) * (1 + (1 / p) ^ 2) by ring]
    positivity
  have hp2gt : 1 < p ^ 2 := by
    nlinarith [mul_pos hp0 (sub_pos.mpr hp)]
  have hp4gt : 1 < p ^ 4 := by
    have hp2pos : 0 < p ^ 2 := sq_pos_of_pos hp0
    nlinarith [mul_pos hp2pos (sub_pos.mpr hp2gt)]
  have hp2ne : -1 + p ^ 2 ≠ 0 := by nlinarith
  have hp4ne : -1 + p ^ 4 ≠ 0 := by nlinarith
  have hp2subne : p ^ 2 - 1 ≠ 0 := (sub_pos.mpr hp2gt).ne'
  have hp4subne : p ^ 4 - 1 ≠ 0 := (sub_pos.mpr hp4gt).ne'
  have hp2subsqne : (p ^ 2 - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hp2subne
  have hp2sqne : 1 - p ^ 2 * 2 + p ^ 4 ≠ 0 := by
    nlinarith [sq_pos_of_pos (sub_pos.mpr hp2gt)]
  have hgap : cdem4345_assembled_lemma1Gap t = d ^ 2 := by rfl
  have hsqrtgap : Real.sqrt (cdem4345_assembled_lemma1Gap t) = d := by
    rw [hgap, Real.sqrt_sq_eq_abs, abs_of_pos]
    dsimp [d]
    exact sub_pos.mpr huv
  rw [cdem4345_assembled_lemma1GapShiftCoefficient, hsqrtgap, hgap]
  change 1 / 18 * (1 / u - 1 / v)
      = 2 / 9 * (d ^ 2 * d) / (1 - (d ^ 2) ^ 2)
  rw [huform, hvform, hd]
  field_simp [hp0.ne', hsub.ne', hplus.ne', hgapden.ne',
    hp2ne, hp4ne, hp2sqne]
  field_simp [hp2subne, hp4subne, hp2subsqne]
  ring

/-! ## The exact rational margin -/

/-- Core comparison in the two gap variables. -/
theorem cdem4345_assembled_lemma1GapRawCoefficient_le_shift
    {z Z : ℝ}
    (hz : 0 < z) (hz20 : z ≤ 1 / 20)
    (hZ : 0 < Z) (hZ1 : Z < 1)
    (hdelta : (Z - z) * (1 - z * Z) = 2 / 25 * z * Z) :
    cdem4345_assembled_lemma1GapRawCoefficient z ≤ cdem4345_assembled_lemma1GapShiftCoefficient Z := by
  have hz0 := hz.le
  have hZ0 := hZ.le
  have hz1 : z < 1 := lt_of_le_of_lt hz20 (by norm_num)
  have hprod0 : 0 ≤ z * Z := mul_nonneg hz0 hZ0
  have hprod1 : z * Z < 1 := by
    calc z * Z < z * 1 := (mul_lt_mul_of_pos_left hZ1 hz)
      _ < 1 := by simpa using hz1
  have hden : 0 < 1 - z * Z := by linarith
  have hmul : 0 < (Z - z) * (1 - z * Z) := by
    rw [hdelta]
    positivity
  have hzZ : z < Z := by
    rcases mul_pos_iff.mp hmul with h | h
    · linarith [h.1]
    · linarith [h.2, hden]
  have hden_le : 1 - z * Z ≤ 1 := by linarith
  have hdelta_le : 2 / 25 * z * Z ≤ Z - z := by
    rw [← hdelta]
    exact mul_le_of_le_one_right (sub_nonneg.mpr hzZ.le) hden_le
  have hzz_le : 2 / 25 * z ^ 2 ≤ 2 / 25 * z * Z := by
    nlinarith
  have hZlower : z * (1 + 2 / 25 * z) ≤ Z := by
    nlinarith

  -- Exact live-range constant trace.
  have hz2 : z ^ 2 ≤ z / 20 := by
    nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz20)]
  have hz3nonneg : 0 ≤ z ^ 3 := by positivity
  have hz3 : z ^ 3 ≤ z / 400 := by
    have := mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hz20)
    nlinarith
  have hz4 : z ^ 4 ≤ z / 8000 := by
    have := mul_nonneg hz3nonneg (sub_nonneg.mpr hz20)
    nlinarith
  have hmargin : 79 / 2000 * z ≤
      (1 + 2 / 25 * z) ^ 3 - (1 + 2 * z ^ 2) ^ 2 := by
    nlinarith [sq_nonneg z, hz2, hz4]
  have hpoly : (1 + 2 * z ^ 2) ^ 2 ≤ (1 + 2 / 25 * z) ^ 3 := by
    nlinarith

  have hbase0 : 0 ≤ z * (1 + 2 / 25 * z) := by positivity
  have hcube : (z * (1 + 2 / 25 * z)) ^ 3 ≤ Z ^ 3 :=
    pow_le_pow_left₀ hbase0 hZlower 3
  have hpoly_mul : z ^ 3 * (1 + 2 * z ^ 2) ^ 2
      ≤ z ^ 3 * (1 + 2 / 25 * z) ^ 3 :=
    mul_le_mul_of_nonneg_left hpoly hz3nonneg
  have hsquare :
      (z * Real.sqrt z * (1 + 2 * z ^ 2)) ^ 2
        ≤ (Z * Real.sqrt Z) ^ 2 := by
    calc
      (z * Real.sqrt z * (1 + 2 * z ^ 2)) ^ 2
          = z ^ 2 * (Real.sqrt z) ^ 2 * (1 + 2 * z ^ 2) ^ 2 := by ring
      _ = z ^ 3 * (1 + 2 * z ^ 2) ^ 2 := by
            rw [Real.sq_sqrt hz0]
            ring
      _ ≤ z ^ 3 * (1 + 2 / 25 * z) ^ 3 := hpoly_mul
      _ = (z * (1 + 2 / 25 * z)) ^ 3 := by ring
      _ ≤ Z ^ 3 := hcube
      _ = Z ^ 2 * (Real.sqrt Z) ^ 2 := by
            rw [Real.sq_sqrt hZ0]
            ring
      _ = (Z * Real.sqrt Z) ^ 2 := by ring
  have hnum : z * Real.sqrt z * (1 + 2 * z ^ 2)
      ≤ Z * Real.sqrt Z := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    exact hsquare
  have hdenZ : 0 < 1 - Z ^ 2 := by nlinarith [sq_nonneg (Z - 1)]
  have hdenz : 0 < 1 - z ^ 2 := by nlinarith [sq_nonneg (z - 1)]
  have hdens : 1 - Z ^ 2 ≤ 1 - z ^ 2 := by
    nlinarith [sq_nonneg (Z - z)]
  have hratio :
    (z * Real.sqrt z * (1 + 2 * z ^ 2)) / (1 - z ^ 2)
        ≤ (Z * Real.sqrt Z) / (1 - z ^ 2) :=
      div_le_div_of_nonneg_right hnum hdenz.le
  have hratio' :
      (z * Real.sqrt z * (1 + 2 * z ^ 2)) / (1 - z ^ 2)
        ≤ (Z * Real.sqrt Z) / (1 - Z ^ 2) :=
    hratio.trans (div_le_div_of_nonneg_left (by positivity) hdenZ hdens)
  rw [cdem4345_assembled_lemma1GapRawCoefficient, cdem4345_assembled_lemma1GapShiftCoefficient]
  calc
    2 / 9 * (z * Real.sqrt z * (1 + 2 * z ^ 2)) / (1 - z ^ 2)
        = 2 / 9 *
            ((z * Real.sqrt z * (1 + 2 * z ^ 2)) / (1 - z ^ 2)) := by ring
    _ ≤ 2 / 9 * ((Z * Real.sqrt Z) / (1 - Z ^ 2)) :=
      mul_le_mul_of_nonneg_left hratio' (by norm_num)
    _ = 2 / 9 * (Z * Real.sqrt Z) / (1 - Z ^ 2) := by ring

/-! ## Closing the printed comparison -/

/-- CDEM's sharp comparison, uniformly for every `k>4`. -/
theorem cdem4345_assembled_lemma1RawCoefficientShiftAt_proven
    {k : ℕ} (hk : 5 ≤ k) : cdem4345_assembled_Lemma1RawCoefficientShiftAt k := by
  let z : ℝ := cdem4345_assembled_lemma1Gap k
  let Z : ℝ := cdem4345_assembled_lemma1Gap ((k : ℝ) - 1 / 50)
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hkm : 0 < (k : ℝ) - 1 / 50 := by linarith
  have hz : 0 < z := cdem4345_assembled_lemma1Gap_pos (by positivity)
  have hZ : 0 < Z := cdem4345_assembled_lemma1Gap_pos hkm.le
  have hz20 : z ≤ 1 / 20 := by
    calc z ≤ 1 / (4 * (k : ℝ)) := cdem4345_assembled_lemma1Gap_le_inv_four_mul (by positivity)
      _ ≤ 1 / 20 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hZbound : Z ≤ 1 / (4 * ((k : ℝ) - 1 / 50)) :=
    cdem4345_assembled_lemma1Gap_le_inv_four_mul hkm
  have hZ1 : Z < 1 := by
    calc Z ≤ 1 / (4 * ((k : ℝ) - 1 / 50)) := hZbound
      _ < 1 := by
        rw [div_lt_one (by positivity)]
        nlinarith
  have hdiff :
      (z + 1 / z) - (Z + 1 / Z) = 2 / 25 := by
    rw [show z + 1 / z = 4 * (k : ℝ) + 2 from
      cdem4345_assembled_lemma1Gap_add_inv (by positivity),
      show Z + 1 / Z = 4 * ((k : ℝ) - 1 / 50) + 2 from
        cdem4345_assembled_lemma1Gap_add_inv hkm.le]
    ring
  have hdelta : (Z - z) * (1 - z * Z) = 2 / 25 * z * Z := by
    calc
      (Z - z) * (1 - z * Z)
          = z * Z * ((z + 1 / z) - (Z + 1 / Z)) := by
              field_simp [hz.ne', hZ.ne']
              ring
      _ = 2 / 25 * z * Z := by rw [hdiff]; ring
  have hcore := cdem4345_assembled_lemma1GapRawCoefficient_le_shift hz hz20 hZ hZ1 hdelta
  rw [cdem4345_assembled_Lemma1RawCoefficientShiftAt,
    cdem4345_assembled_lemma1RawBlockCoefficient_eq_gap (by omega : 1 ≤ k)]
  change cdem4345_assembled_lemma1GapRawCoefficient z
      ≤ 1 / 18
          * (1 / Real.sqrt ((k : ℝ) - 2 / 100)
            - 1 / Real.sqrt (((k + 1 : ℕ) : ℝ) - 2 / 100))
  have harg0 : (k : ℝ) - 2 / 100 = (k : ℝ) - 1 / 50 := by ring
  have harg1 : (((k + 1 : ℕ) : ℝ) - 2 / 100)
      = ((k : ℝ) - 1 / 50) + 1 := by
    push_cast
    ring
  rw [harg0, harg1]
  have hnorm := cdem4345_assembled_lemma1_shiftedCoefficient_eq_gap hkm
  change 1 / 18 *
      (1 / Real.sqrt ((k : ℝ) - 1 / 50)
        - 1 / Real.sqrt (((k : ℝ) - 1 / 50) + 1))
      = cdem4345_assembled_lemma1GapShiftCoefficient Z at hnorm
  rw [hnorm]
  exact hcore

/-- The original block interface now needs only the signed local remainder. -/
theorem cdem4345_assembled_lemma1_periodicBlockEstimate_of_signed_provenShift
    {x : ℝ} {k : ℕ} (hk : 5 ≤ k)
    (hsigned : cdem4345_assembled_Lemma1PeriodicSignedRemainderAt x k) :
    cdem4345_assembled_Lemma1PeriodicBlockEstimateAt x k :=
  cdem4345_assembled_lemma1_periodicBlockEstimate_of_signed hsigned
    (cdem4345_assembled_lemma1RawCoefficientShiftAt_proven hk)

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: exact-decomposition reduction

This file proves the centered-floor algebra in the exact CDEM Lemma 1 decomposition and
reduces `cdem4345_assembled_Lemma1ExactDecompositionAt` to precisely two classical identities:

1. CDEM (2.1), the finite hyperbola identity (`cdem4345_assembled_Lemma1Eq21At`);
2. Abel/partial summation of the reciprocal-square Möbius tail
   (`cdem4345_assembled_Lemma1RecipSqPartialSummationAt`).

Neither residual is an estimate, an unbounded Mertens hypothesis, or the target
squarefree conclusion.  The first is finite-sum combinatorics and is backed by PNTA's
`MobiusLemma.mobius_lemma_1_sub`; the second is a general exact summation-by-parts
identity backed by `MobiusLemma.sum_moebius_div_sq`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- The reciprocal-square Möbius head through `X_n`. -/
noncomputable def cdem4345_assembled_lemma1MobiusRecipHead (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
    (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2

/-- The floor head in CDEM (2.1). -/
noncomputable def cdem4345_assembled_lemma1FloorHead (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
    (ArithmeticFunction.moebius a : ℝ) * (⌊x / (a : ℝ) ^ 2⌋₊ : ℝ)

/-- CDEM equation (2.1), isolated at one point `(x,n)`. -/
def cdem4345_assembled_Lemma1Eq21At (x : ℝ) (n : ℕ) : Prop :=
  cdem4345_assembled_squarefreeCount x
    = cdem4345_assembled_lemma1FloorHead x n
      + (∑ j ∈ Finset.Icc 1 (n - 1), cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j))
      - ((n - 1 : ℕ) : ℝ) * cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n)

/-- Exact reciprocal-square partial summation at `(x,n)`:

`x sum_{a≤X_n} mu(a)/a² = (6/pi²)x + n M(X_n) - 2x integral M(t)/t³`.

This is the smallest analytic identity still needed for the exact decomposition. -/
def cdem4345_assembled_Lemma1RecipSqPartialSummationAt (x : ℝ) (n : ℕ) : Prop :=
  x * cdem4345_assembled_lemma1MobiusRecipHead x n
    = (6 / Real.pi ^ 2) * x
      + (n : ℝ) * cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n)
      - 2 * x * cdem4345_assembled_lemma1SignedTailIntegral x n

/-- The remaining finite reindexing in (2.1).  It exchanges the pairs
`n≤k≤x`, `a≤sqrt(x/k)` with `a≤X_n`, `n≤k≤x/a²`. -/
def cdem4345_assembled_Lemma1HyperbolaTailInterchangeAt (x : ℝ) (n : ℕ) : Prop :=
  (∑ k ∈ Finset.Icc n ⌊x⌋₊, cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x k))
    = cdem4345_assembled_lemma1FloorHead x n
      - ((n - 1 : ℕ) : ℝ) * cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n)

/-- The paper's real Mertens step is the corresponding finite real Möbius sum. -/
theorem cdem4345_assembled_lemma1M_eq_sum (t : ℝ) :
    cdem4345_assembled_lemma1M t
      = ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ) := by
  rfl

/-- For nonnegative `y`, the natural floor is `y-fract(y)`. -/
theorem cdem4345_assembled_natFloor_cast_eq_sub_fract {y : ℝ} (hy : 0 ≤ y) :
    (⌊y⌋₊ : ℝ) = y - Int.fract y := by
  have hfloor : ((⌊y⌋₊ : ℕ) : ℤ) = ⌊y⌋ := Int.natCast_floor_eq_floor hy
  have hreal : ((⌊y⌋ : ℤ) : ℝ) = y - Int.fract y :=
    (eq_sub_iff_add_eq).2 (Int.floor_add_fract y)
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hfloor
  norm_num at hcast
  exact hcast.trans hreal

/-- Exact centered fractional-part expansion of the floor head. -/
theorem cdem4345_assembled_lemma1_floorHead_centered
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x) :
    cdem4345_assembled_lemma1FloorHead x n
      = x * cdem4345_assembled_lemma1MobiusRecipHead x n
        - cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / 2
        - cdem4345_assembled_lemma1CenteredSum x n := by
  have hterm : ∀ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
      (ArithmeticFunction.moebius a : ℝ) * (⌊x / (a : ℝ) ^ 2⌋₊ : ℝ)
        = x * ((ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
          - (ArithmeticFunction.moebius a : ℝ) / 2
          - (ArithmeticFunction.moebius a : ℝ)
              * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    have ha_pos : (0 : ℝ) < (a : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ha'.1)
    have hy : 0 ≤ x / (a : ℝ) ^ 2 := div_nonneg hx (sq_nonneg _)
    rw [cdem4345_assembled_natFloor_cast_eq_sub_fract hy]
    field_simp
    ring
  have hhalf :
      (∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
          (ArithmeticFunction.moebius a : ℝ) / 2)
        = (∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
            (ArithmeticFunction.moebius a : ℝ)) / 2 := by
    simpa only [div_eq_mul_inv] using
      (Finset.sum_mul (s := Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊)
        (f := fun a => (ArithmeticFunction.moebius a : ℝ)) (2 : ℝ)⁻¹).symm
  unfold cdem4345_assembled_lemma1FloorHead cdem4345_assembled_lemma1MobiusRecipHead cdem4345_assembled_lemma1CenteredSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hhalf]
  have hM := cdem4345_assembled_lemma1M_eq_sum (cdem4345_assembled_lemma1X x n)
  rw [hM]

/-- **Exact CDEM Lemma 1 decomposition from its two irreducible identities.** -/
theorem cdem4345_assembled_lemma1_exactDecomposition_of_eq21_and_recipSq
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hn : 1 ≤ n)
    (heq21 : cdem4345_assembled_Lemma1Eq21At x n)
    (hrecip : cdem4345_assembled_Lemma1RecipSqPartialSummationAt x n) :
    cdem4345_assembled_Lemma1ExactDecompositionAt x n := by
  rw [cdem4345_assembled_Lemma1Eq21At] at heq21
  rw [cdem4345_assembled_Lemma1RecipSqPartialSummationAt] at hrecip
  rw [cdem4345_assembled_Lemma1ExactDecompositionAt]
  unfold cdem4345_assembled_lemma1Remainder
  rw [heq21, cdem4345_assembled_lemma1_floorHead_centered hx]
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast]
  linarith

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the sharp period-error bound

This file proves the paper's elementary bound `|rho(z)| <= 4/3` for nonnegative `z`.
Writing `floor z = 36q+r`, `0<=r<36`, gives

`rho(z) = r/3-floor(r/4)-floor(r/9)-(2/3)fract(z)`.

The first four terms lie in `[-2/3,4/3]`; this is an exact 36-residue check.  Since
`0<=fract(z)<1`, the asserted bound follows.  The finite residue check is transparent
and uses no analytic input.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

/-- The finite 36-residue calculation behind the `rho` bound. -/
private theorem cdem4345_assembled_lemma1_rho_residue_bounds (r : ℕ) (hr : r < 36) :
    (-2 / 3 : ℝ)
        ≤ (r : ℝ) / 3 - ((r / 4 : ℕ) : ℝ) - ((r / 9 : ℕ) : ℝ)
      ∧ (r : ℝ) / 3 - ((r / 4 : ℕ) : ℝ) - ((r / 9 : ℕ) : ℝ)
        ≤ 4 / 3 := by
  interval_cases r <;> norm_num

/-- Exact residue-class formula for `rho`. -/
theorem cdem4345_assembled_lemma1Rho_eq_residue
    {z : ℝ} (hz : 0 ≤ z) :
    let N := ⌊z⌋₊
    let r := N % 36
    cdem4345_assembled_lemma1Rho z
      = (r : ℝ) / 3 - ((r / 4 : ℕ) : ℝ) - ((r / 9 : ℕ) : ℝ)
          - 2 / 3 * Int.fract z := by
  let N : ℕ := ⌊z⌋₊
  let q : ℕ := N / 36
  let r : ℕ := N % 36
  have hr : r < 36 := Nat.mod_lt N (by norm_num)
  have hN : N = 36 * q + r := by
    dsimp [q, r]
    omega
  have hNreal : (N : ℝ) = 36 * (q : ℝ) + (r : ℝ) := by
    exact_mod_cast hN
  have h4 : N / 4 = 9 * q + r / 4 := by omega
  have h9 : N / 9 = 4 * q + r / 9 := by omega
  have h36 : N / 36 = q := by rfl
  have hzN : (N : ℝ) = z - Int.fract z := by
    exact cdem4345_assembled_natFloor_cast_eq_sub_fract hz
  have hfloor4 : ⌊z / (4 : ℝ)⌋₊ = N / 4 := by
    simpa [N] using Nat.floor_div_natCast z 4
  have hfloor9 : ⌊z / (9 : ℝ)⌋₊ = N / 9 := by
    simpa [N] using Nat.floor_div_natCast z 9
  have hfloor36 : ⌊z / (36 : ℝ)⌋₊ = N / 36 := by
    simpa [N] using Nat.floor_div_natCast z 36
  rw [cdem4345_assembled_lemma1Rho, cdem4345_assembled_lemma1H]
  dsimp only
  rw [hfloor4, hfloor9, hfloor36]
  change (N : ℝ) - ((N / 4 : ℕ) : ℝ) - ((N / 9 : ℕ) : ℝ)
      + ((N / 36 : ℕ) : ℝ) - 2 / 3 * z
        = (r : ℝ) / 3 - ((r / 4 : ℕ) : ℝ) - ((r / 9 : ℕ) : ℝ)
            - 2 / 3 * Int.fract z
  rw [h4, h9, h36]
  push_cast
  rw [hzN] at hNreal
  linarith

/-- CDEM's sharp uniform bound on the period error in the live nonnegative range. -/
theorem cdem4345_assembled_lemma1Rho_abs_le_four_thirds {z : ℝ} (hz : 0 ≤ z) :
    |cdem4345_assembled_lemma1Rho z| ≤ 4 / 3 := by
  let N : ℕ := ⌊z⌋₊
  let r : ℕ := N % 36
  have hr : r < 36 := Nat.mod_lt N (by norm_num)
  obtain ⟨hlo, hhi⟩ := cdem4345_assembled_lemma1_rho_residue_bounds r hr
  have hf0 : 0 ≤ Int.fract z := Int.fract_nonneg z
  have hf1 : Int.fract z < 1 := Int.fract_lt_one z
  rw [cdem4345_assembled_lemma1Rho_eq_residue hz]
  rw [abs_le]
  constructor <;> nlinarith

theorem cdem4345_assembled_lemma1Rho_le_four_thirds {z : ℝ} (hz : 0 ≤ z) :
    cdem4345_assembled_lemma1Rho z ≤ 4 / 3 :=
  (le_abs_self (cdem4345_assembled_lemma1Rho z)).trans (cdem4345_assembled_lemma1Rho_abs_le_four_thirds hz)

theorem cdem4345_assembled_neg_four_thirds_le_lemma1Rho {z : ℝ} (hz : 0 ≤ z) :
    (-4 / 3 : ℝ) ≤ cdem4345_assembled_lemma1Rho z :=
  by simpa only [neg_div] using
    (neg_le_of_abs_le (cdem4345_assembled_lemma1Rho_abs_le_four_thirds hz))

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the signed block profile

On the block `(X_{k+1},X_k]`, the floor of `x/a^2` is `k`.  Hence the centered
fractional square is the smooth profile

`f(t) = (x/t^2-k-1/2)^2`.

This file records its derivative, endpoint values, antiderivative, and the exact
identification with the finite block mass.  These are the functions suppressed by the
paper's phrase “a detailed and delicate study of a few functions”.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset MeasureTheory Set intervalIntegral
open scoped BigOperators

/-- The smooth function sampled by the `k`-th block. -/
noncomputable def cdem4345_assembled_lemma1BlockProfile (x : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (x / t ^ 2 - (k : ℝ) - 1 / 2) ^ 2

/-- Its derivative away from zero. -/
noncomputable def cdem4345_assembled_lemma1BlockProfileDeriv (x : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -4 * x / t ^ 3 * (x / t ^ 2 - (k : ℝ) - 1 / 2)

/-- An antiderivative of the block profile. -/
noncomputable def cdem4345_assembled_lemma1BlockProfilePrimitive (x : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  -x ^ 2 / (3 * t ^ 3)
    + 2 * ((k : ℝ) + 1 / 2) * x / t
    + ((k : ℝ) + 1 / 2) ^ 2 * t

/-- The unique zero of the profile inside the block. -/
noncomputable def cdem4345_assembled_lemma1BlockMidpoint (x : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (x / ((k : ℝ) + 1 / 2))

private theorem cdem4345_assembled_hasDerivAt_div_sq {x t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => x / u ^ 2) (-2 * x / t ^ 3) t := by
  have hinv := (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)
  have h := hinv.const_mul x
  have hfun : (fun u : ℝ => x / u ^ 2) =
      fun u : ℝ => x * (u ^ 2)⁻¹ := by
    funext u
    simp only [div_eq_mul_inv]
  rw [hfun]
  exact h.congr_deriv (by
    field_simp [ht]
    ring)

theorem cdem4345_assembled_hasDerivAt_lemma1BlockProfile
    {x t : ℝ} {k : ℕ} (ht : t ≠ 0) :
    HasDerivAt (cdem4345_assembled_lemma1BlockProfile x k) (cdem4345_assembled_lemma1BlockProfileDeriv x k t) t := by
  have hinner := (cdem4345_assembled_hasDerivAt_div_sq (x := x) ht).sub_const ((k : ℝ) + 1 / 2)
  have h := hinner.pow 2
  have hfun : cdem4345_assembled_lemma1BlockProfile x k =
      fun u : ℝ => (x / u ^ 2 - ((k : ℝ) + 1 / 2)) ^ 2 := by
    funext u
    rw [cdem4345_assembled_lemma1BlockProfile]
    ring
  rw [hfun]
  exact h.congr_deriv (by
    rw [cdem4345_assembled_lemma1BlockProfileDeriv]
    norm_num
    ring)

theorem cdem4345_assembled_hasDerivAt_lemma1BlockProfilePrimitive
    {x t : ℝ} {k : ℕ} (ht : t ≠ 0) :
    HasDerivAt (cdem4345_assembled_lemma1BlockProfilePrimitive x k) (cdem4345_assembled_lemma1BlockProfile x k t) t := by
  have hinv3 : HasDerivAt (fun u : ℝ => (u ^ 3)⁻¹) (-3 / t ^ 4) t := by
    exact ((hasDerivAt_pow 3 t).inv (pow_ne_zero 3 ht)).congr_deriv (by
      field_simp [ht]
      ring)
  have hinv1 : HasDerivAt (fun u : ℝ => u⁻¹) (-1 / t ^ 2) t := by
    exact (hasDerivAt_inv ht).congr_deriv (by simp [div_eq_mul_inv])
  have hfirst := hinv3.const_mul (-x ^ 2 / 3)
  have hsecond := hinv1.const_mul (2 * ((k : ℝ) + 1 / 2) * x)
  have hthird := (hasDerivAt_id t).const_mul (((k : ℝ) + 1 / 2) ^ 2)
  have h := hfirst.add hsecond |>.add hthird
  have hfun : cdem4345_assembled_lemma1BlockProfilePrimitive x k = fun u : ℝ =>
      (-x ^ 2 / 3) * (u ^ 3)⁻¹
        + (2 * ((k : ℝ) + 1 / 2) * x) * u⁻¹
        + ((k : ℝ) + 1 / 2) ^ 2 * u := by
    funext u
    rw [cdem4345_assembled_lemma1BlockProfilePrimitive]
    simp only [div_eq_mul_inv]
    ring
  rw [hfun]
  exact h.congr_deriv (by
    rw [cdem4345_assembled_lemma1BlockProfile]
    field_simp [ht]
    ring)

/-! ## The block geometry -/

theorem cdem4345_assembled_lemma1X_pos {x : ℝ} {j : ℕ} (hx : 0 < x) (hj : 1 ≤ j) :
    0 < cdem4345_assembled_lemma1X x j := by
  rw [cdem4345_assembled_lemma1X]
  exact Real.sqrt_pos.2 (div_pos hx (by exact_mod_cast hj))

theorem cdem4345_assembled_lemma1X_sq {x : ℝ} {j : ℕ} (hx : 0 ≤ x) (hj : 1 ≤ j) :
    cdem4345_assembled_lemma1X x j ^ 2 = x / (j : ℝ) := by
  rw [cdem4345_assembled_lemma1X, Real.sq_sqrt]
  exact div_nonneg hx (by positivity)

theorem cdem4345_assembled_lemma1X_succ_lt {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1X x (k + 1) < cdem4345_assembled_lemma1X x k := by
  rw [cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1X]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℕ))
    (by positivity : (0 : ℝ) < (k : ℕ))]
  push_cast
  nlinarith

theorem cdem4345_assembled_lemma1BlockMidpoint_pos
    {x : ℝ} {k : ℕ} (hx : 0 < x) :
    0 < cdem4345_assembled_lemma1BlockMidpoint x k := by
  rw [cdem4345_assembled_lemma1BlockMidpoint]
  positivity

theorem cdem4345_assembled_lemma1X_succ_lt_midpoint
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1X x (k + 1) < cdem4345_assembled_lemma1BlockMidpoint x k := by
  rw [cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1BlockMidpoint]
  apply Real.sqrt_lt_sqrt (by positivity)
  exact div_lt_div_of_pos_left hx (by positivity) (by
    push_cast
    linarith)

theorem cdem4345_assembled_lemma1BlockMidpoint_lt_X
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1BlockMidpoint x k < cdem4345_assembled_lemma1X x k := by
  rw [cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1BlockMidpoint]
  apply Real.sqrt_lt_sqrt (by positivity)
  exact div_lt_div_of_pos_left hx (by positivity) (by
    push_cast
    linarith)

theorem cdem4345_assembled_lemma1_x_div_X_sq
    {x : ℝ} {j : ℕ} (hx : 0 < x) (hj : 1 ≤ j) :
    x / cdem4345_assembled_lemma1X x j ^ 2 = (j : ℝ) := by
  rw [cdem4345_assembled_lemma1X_sq hx.le hj]
  field_simp [hx.ne', show (j : ℝ) ≠ 0 by positivity]

theorem cdem4345_assembled_lemma1BlockProfile_left_endpoint
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x (k + 1)) = 1 / 4 := by
  rw [cdem4345_assembled_lemma1BlockProfile, cdem4345_assembled_lemma1_x_div_X_sq hx (by omega : 1 ≤ k + 1)]
  push_cast
  ring

theorem cdem4345_assembled_lemma1BlockProfile_right_endpoint
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x k) = 1 / 4 := by
  rw [cdem4345_assembled_lemma1BlockProfile, cdem4345_assembled_lemma1_x_div_X_sq hx hk]
  ring

theorem cdem4345_assembled_lemma1BlockProfile_midpoint
    {x : ℝ} {k : ℕ} (hx : 0 < x) :
    cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1BlockMidpoint x k) = 0 := by
  have hc : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hs : cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 = x / ((k : ℝ) + 1 / 2) := by
    rw [cdem4345_assembled_lemma1BlockMidpoint, Real.sq_sqrt]
    exact div_nonneg hx.le hc.le
  rw [cdem4345_assembled_lemma1BlockProfile, hs]
  field_simp [hx.ne', hc.ne']
  ring

/-! ## Identification of the sampled finite sum -/

theorem cdem4345_assembled_lemma1_floor_x_div_sq_eq_block
    {x : ℝ} {k a : ℕ} (hx : 0 < x) (hk : 1 ≤ k)
    (ha : a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊) :
    ⌊x / (a : ℝ) ^ 2⌋₊ = k := by
  obtain ⟨haA, haB⟩ := Finset.mem_Ioc.mp ha
  have hA0 := (cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)).le
  have hB0 := (cdem4345_assembled_lemma1X_pos hx hk).le
  have hAa : cdem4345_assembled_lemma1X x (k + 1) < (a : ℝ) :=
    (Nat.floor_lt hA0).mp haA
  have haB' : (a : ℝ) ≤ cdem4345_assembled_lemma1X x k :=
    (Nat.le_floor_iff hB0).mp haB
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le
    (cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)) hAa.le
  have hsq_lo : cdem4345_assembled_lemma1X x (k + 1) ^ 2 < (a : ℝ) ^ 2 :=
    (sq_lt_sq₀ hA0 ha0.le).2 hAa
  have hsq_hi : (a : ℝ) ^ 2 ≤ cdem4345_assembled_lemma1X x k ^ 2 :=
    (sq_le_sq₀ ha0.le hB0).2 haB'
  have hlo : (k : ℝ) ≤ x / (a : ℝ) ^ 2 := by
    calc
      (k : ℝ) = x / cdem4345_assembled_lemma1X x k ^ 2 := (cdem4345_assembled_lemma1_x_div_X_sq hx hk).symm
      _ ≤ x / (a : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left hx.le (sq_pos_of_pos ha0) hsq_hi
  have hhi : x / (a : ℝ) ^ 2 < (k : ℝ) + 1 := by
    calc
      x / (a : ℝ) ^ 2 < x / cdem4345_assembled_lemma1X x (k + 1) ^ 2 :=
        div_lt_div_of_pos_left hx (sq_pos_of_pos
          (cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1))) hsq_lo
      _ = ((k + 1 : ℕ) : ℝ) :=
        cdem4345_assembled_lemma1_x_div_X_sq hx (by omega : 1 ≤ k + 1)
      _ = (k : ℝ) + 1 := by push_cast; ring
  rw [Nat.floor_eq_iff (div_nonneg hx.le (sq_nonneg _))]
  exact ⟨hlo, hhi⟩

theorem cdem4345_assembled_lemma1_fract_eq_blockProfile_inner
    {x : ℝ} {k a : ℕ} (hx : 0 < x) (hk : 1 ≤ k)
    (ha : a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊) :
    Int.fract (x / (a : ℝ) ^ 2) - 1 / 2
      = x / (a : ℝ) ^ 2 - (k : ℝ) - 1 / 2 := by
  have hfloor := cdem4345_assembled_lemma1_floor_x_div_sq_eq_block hx hk ha
  have hnat := cdem4345_assembled_natFloor_cast_eq_sub_fract
    (div_nonneg hx.le (sq_nonneg (a : ℝ)))
  rw [hfloor] at hnat
  linarith

theorem cdem4345_assembled_lemma1BlockMass_eq_profile
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1BlockMass x k
      = ∑ a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊,
          cdem4345_assembled_lemma1PeriodWeight a * cdem4345_assembled_lemma1BlockProfile x k a := by
  rw [cdem4345_assembled_lemma1BlockMass]
  apply Finset.sum_congr rfl
  intro a ha
  rw [cdem4345_assembled_lemma1BlockProfile, cdem4345_assembled_lemma1_fract_eq_blockProfile_inner hx hk ha]

/-! ## The exact smooth main term -/

theorem cdem4345_assembled_intervalIntegral_lemma1BlockProfile_eq_primitive_sub
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    (∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1X x k, cdem4345_assembled_lemma1BlockProfile x k t)
      = cdem4345_assembled_lemma1BlockProfilePrimitive x k (cdem4345_assembled_lemma1X x k)
          - cdem4345_assembled_lemma1BlockProfilePrimitive x k (cdem4345_assembled_lemma1X x (k + 1)) := by
  have hAB := (cdem4345_assembled_lemma1X_succ_lt hx hk).le
  have hA := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
  have hderiv : ∀ t ∈ Set.uIcc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
      HasDerivAt (cdem4345_assembled_lemma1BlockProfilePrimitive x k)
        (cdem4345_assembled_lemma1BlockProfile x k t) t := by
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    exact cdem4345_assembled_hasDerivAt_lemma1BlockProfilePrimitive (by linarith [ht.1])
  have hint : IntervalIntegrable (cdem4345_assembled_lemma1BlockProfile x k) volume
      (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k) := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    have ht0 : 0 < t := hA.trans_le ht.1
    exact (cdem4345_assembled_hasDerivAt_lemma1BlockProfile ht0.ne').continuousAt.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- Evaluation of the `2t/3` part of the Stieltjes measure.  This is exactly the raw
coefficient printed by CDEM, before the `0.02/0.98` comparison. -/
theorem cdem4345_assembled_two_thirds_integral_lemma1BlockProfile_eq_raw
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    2 / 3 * (∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1X x k,
      cdem4345_assembled_lemma1BlockProfile x k t) = cdem4345_assembled_lemma1RawBlockMain x k := by
  rw [cdem4345_assembled_intervalIntegral_lemma1BlockProfile_eq_primitive_sub hx hk]
  let sx : ℝ := Real.sqrt x
  let u : ℝ := Real.sqrt k
  let v : ℝ := Real.sqrt (((k + 1 : ℕ) : ℝ))
  have hsx : 0 < sx := Real.sqrt_pos.2 hx
  have hu : 0 < u := Real.sqrt_pos.2 (by exact_mod_cast hk)
  have hv : 0 < v := Real.sqrt_pos.2 (by positivity)
  have hsx2 : sx ^ 2 = x := by simpa [sx] using Real.sq_sqrt hx.le
  have hu2 : u ^ 2 = (k : ℝ) := by
    simpa [u] using Real.sq_sqrt (show (0 : ℝ) ≤ k by positivity)
  have hv2 : v ^ 2 = (k : ℝ) + 1 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) by positivity)
    rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by push_cast; ring] at h
    simpa [v] using h
  have hvRaw : Real.sqrt ((k : ℝ) + 1) = v := by
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      push_cast
      ring
    dsimp [v]
    rw [hcast]
  rw [cdem4345_assembled_lemma1BlockProfilePrimitive, cdem4345_assembled_lemma1BlockProfilePrimitive,
    cdem4345_assembled_lemma1RawBlockMain, cdem4345_assembled_lemma1RawBlockCoefficient, cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1X,
    Real.sqrt_div hx.le, Real.sqrt_div hx.le]
  rw [hvRaw]
  change 2 / 3 *
      ((-x ^ 2 / (3 * (sx / u) ^ 3)
          + 2 * ((k : ℝ) + 1 / 2) * x / (sx / u)
          + ((k : ℝ) + 1 / 2) ^ 2 * (sx / u))
        - (-x ^ 2 / (3 * (sx / v) ^ 3)
          + 2 * ((k : ℝ) + 1 / 2) * x / (sx / v)
          + ((k : ℝ) + 1 / 2) ^ 2 * (sx / v)))
    = ((16 / 9 * (k : ℝ) + 4 / 3 + 1 / (6 * (k : ℝ))) * u
        - (16 / 9 * (k : ℝ) + 4 / 9
            + 1 / (6 * ((k : ℝ) + 1))) * v) * sx
  rw [← hsx2, ← hv2, ← hu2]
  field_simp [hsx.ne', hu.ne', hv.ne']
  have huv : v ^ 2 = u ^ 2 + 1 := by rw [hv2, hu2]
  rw [huv]
  ring

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: exact total variation of a block profile

The profile decreases from `1/4` to `0` on `[X_{k+1},Y_k]` and increases from `0`
to `1/4` on `[Y_k,X_k]`, where `Y_k=sqrt(x/(k+1/2))`.  Consequently

`integral_{X_{k+1}}^{X_k} |f'_k(t)| dt = 1/2`.

This exact variation, combined with `|rho|<=4/3`, is the source of the paper's
`|r_k|<=2/3`.  No pointwise absolute bound is applied to the finite block sum.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open MeasureTheory Set intervalIntegral

theorem cdem4345_assembled_lemma1_x_div_midpoint_sq
    {x : ℝ} {k : ℕ} (hx : 0 < x) :
    x / cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 = (k : ℝ) + 1 / 2 := by
  have hc : 0 < (k : ℝ) + 1 / 2 := by positivity
  have hs : cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 = x / ((k : ℝ) + 1 / 2) := by
    rw [cdem4345_assembled_lemma1BlockMidpoint, Real.sq_sqrt]
    exact div_nonneg hx.le hc.le
  rw [hs]
  field_simp [hx.ne', hc.ne']

theorem cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
    {x : ℝ} {k : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (cdem4345_assembled_lemma1BlockProfileDeriv x k) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht0 : t ≠ 0 := by
    rw [Set.uIcc_of_le hab] at ht
    exact ne_of_gt (ha.trans_le ht.1)
  unfold cdem4345_assembled_lemma1BlockProfileDeriv
  have hrat : ContinuousAt (fun u : ℝ => -4 * x / u ^ 3) t :=
    continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht0)
  have hinner : ContinuousAt
      (fun u : ℝ => x / u ^ 2 - (k : ℝ) - 1 / 2) t :=
    ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).sub_const _).sub_const _
  exact (hrat.mul hinner).continuousWithinAt

/- The following two sign lemmas use only monotonicity of `t^2` on the positive axis. -/

theorem cdem4345_assembled_lemma1BlockProfileDeriv_nonpos_left
    {x t : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k)
    (ht : t ∈ Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1BlockMidpoint x k)) :
    cdem4345_assembled_lemma1BlockProfileDeriv x k t ≤ 0 := by
  have hA := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
  have ht0 : 0 < t := lt_of_lt_of_le hA ht.1
  have hC := cdem4345_assembled_lemma1BlockMidpoint_pos (k := k) hx
  have hsq : t ^ 2 ≤ cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 :=
    (sq_le_sq₀ ht0.le hC.le).2 ht.2
  have hinner : 0 ≤ x / t ^ 2 - (k : ℝ) - 1 / 2 := by
    have hdiv : x / cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 ≤ x / t ^ 2 :=
      div_le_div_of_nonneg_left hx.le (sq_pos_of_pos ht0) hsq
    rw [cdem4345_assembled_lemma1_x_div_midpoint_sq hx] at hdiv
    linarith
  rw [cdem4345_assembled_lemma1BlockProfileDeriv]
  have hcoeff : -4 * x / t ^ 3 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx.le) (by positivity)
  exact mul_nonpos_of_nonpos_of_nonneg hcoeff hinner

theorem cdem4345_assembled_lemma1BlockProfileDeriv_nonneg_right
    {x t : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k)
    (ht : t ∈ Set.Icc (cdem4345_assembled_lemma1BlockMidpoint x k) (cdem4345_assembled_lemma1X x k)) :
    0 ≤ cdem4345_assembled_lemma1BlockProfileDeriv x k t := by
  have hC := cdem4345_assembled_lemma1BlockMidpoint_pos (k := k) hx
  have ht0 : 0 < t := lt_of_lt_of_le hC ht.1
  have hB := cdem4345_assembled_lemma1X_pos hx hk
  have hsq : cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 ≤ t ^ 2 :=
    (sq_le_sq₀ hC.le ht0.le).2 ht.1
  have hinner : x / t ^ 2 - (k : ℝ) - 1 / 2 ≤ 0 := by
    have hdiv : x / t ^ 2 ≤ x / cdem4345_assembled_lemma1BlockMidpoint x k ^ 2 :=
      div_le_div_of_nonneg_left hx.le (sq_pos_of_pos hC) hsq
    rw [cdem4345_assembled_lemma1_x_div_midpoint_sq hx] at hdiv
    linarith
  rw [cdem4345_assembled_lemma1BlockProfileDeriv]
  have hcoeff : -4 * x / t ^ 3 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx.le) (by positivity)
  exact mul_nonneg_of_nonpos_of_nonpos hcoeff hinner

theorem cdem4345_assembled_intervalIntegral_abs_lemma1BlockProfileDeriv_left
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    (∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1BlockMidpoint x k,
        |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) = 1 / 4 := by
  have hAC := (cdem4345_assembled_lemma1X_succ_lt_midpoint hx hk).le
  have hA := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
  have hint := cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
    (x := x) (k := k) (b := cdem4345_assembled_lemma1BlockMidpoint x k) hA hAC
  have habs : (∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1BlockMidpoint x k,
      |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
      = -∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1BlockMidpoint x k,
          cdem4345_assembled_lemma1BlockProfileDeriv x k t := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1BlockMidpoint x k) := by
      rwa [Set.uIcc_of_le hAC] at ht
    change |cdem4345_assembled_lemma1BlockProfileDeriv x k t| = -cdem4345_assembled_lemma1BlockProfileDeriv x k t
    rw [abs_of_nonpos (cdem4345_assembled_lemma1BlockProfileDeriv_nonpos_left hx hk htI)]
  have hFTC : (∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1BlockMidpoint x k,
      cdem4345_assembled_lemma1BlockProfileDeriv x k t)
      = cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1BlockMidpoint x k)
          - cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x (k + 1)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hAC] at ht
      exact cdem4345_assembled_hasDerivAt_lemma1BlockProfile (by linarith [hA, ht.1])
    · exact hint
  rw [habs, hFTC, cdem4345_assembled_lemma1BlockProfile_midpoint hx,
    cdem4345_assembled_lemma1BlockProfile_left_endpoint hx hk]
  ring

theorem cdem4345_assembled_intervalIntegral_abs_lemma1BlockProfileDeriv_right
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    (∫ t in cdem4345_assembled_lemma1BlockMidpoint x k..cdem4345_assembled_lemma1X x k,
        |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) = 1 / 4 := by
  have hCB := (cdem4345_assembled_lemma1BlockMidpoint_lt_X hx hk).le
  have hC := cdem4345_assembled_lemma1BlockMidpoint_pos (k := k) hx
  have hint := cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
    (x := x) (k := k) (b := cdem4345_assembled_lemma1X x k) hC hCB
  have habs : (∫ t in cdem4345_assembled_lemma1BlockMidpoint x k..cdem4345_assembled_lemma1X x k,
      |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
      = ∫ t in cdem4345_assembled_lemma1BlockMidpoint x k..cdem4345_assembled_lemma1X x k,
          cdem4345_assembled_lemma1BlockProfileDeriv x k t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (cdem4345_assembled_lemma1BlockMidpoint x k) (cdem4345_assembled_lemma1X x k) := by
      rwa [Set.uIcc_of_le hCB] at ht
    change |cdem4345_assembled_lemma1BlockProfileDeriv x k t| = cdem4345_assembled_lemma1BlockProfileDeriv x k t
    rw [abs_of_nonneg (cdem4345_assembled_lemma1BlockProfileDeriv_nonneg_right hx hk htI)]
  have hFTC : (∫ t in cdem4345_assembled_lemma1BlockMidpoint x k..cdem4345_assembled_lemma1X x k,
      cdem4345_assembled_lemma1BlockProfileDeriv x k t)
      = cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x k)
          - cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1BlockMidpoint x k) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hCB] at ht
      exact cdem4345_assembled_hasDerivAt_lemma1BlockProfile (by linarith [hC, ht.1])
    · exact hint
  rw [habs, hFTC, cdem4345_assembled_lemma1BlockProfile_right_endpoint hx hk,
    cdem4345_assembled_lemma1BlockProfile_midpoint hx]
  ring

/-- The exact total variation used by CDEM. -/
theorem cdem4345_assembled_intervalIntegral_abs_lemma1BlockProfileDeriv
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    (∫ t in cdem4345_assembled_lemma1X x (k + 1)..cdem4345_assembled_lemma1X x k,
        |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) = 1 / 2 := by
  have hAC := (cdem4345_assembled_lemma1X_succ_lt_midpoint hx hk).le
  have hCB := (cdem4345_assembled_lemma1BlockMidpoint_lt_X hx hk).le
  have hL := (cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
    (x := x) (k := k) (a := cdem4345_assembled_lemma1X x (k + 1))
    (b := cdem4345_assembled_lemma1BlockMidpoint x k)
    (cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)) hAC).norm
  have hR := (cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
    (x := x) (k := k) (a := cdem4345_assembled_lemma1BlockMidpoint x k)
    (b := cdem4345_assembled_lemma1X x k) (cdem4345_assembled_lemma1BlockMidpoint_pos (k := k) hx) hCB).norm
  have hL' : IntervalIntegrable (fun t => |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
      volume (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1BlockMidpoint x k) := by
    simpa only [Real.norm_eq_abs] using hL
  have hR' : IntervalIntegrable (fun t => |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
      volume (cdem4345_assembled_lemma1BlockMidpoint x k) (cdem4345_assembled_lemma1X x k) := by
    simpa only [Real.norm_eq_abs] using hR
  rw [← intervalIntegral.integral_add_adjacent_intervals hL' hR',
    cdem4345_assembled_intervalIntegral_abs_lemma1BlockProfileDeriv_left hx hk,
    cdem4345_assembled_intervalIntegral_abs_lemma1BlockProfileDeriv_right hx hk]
  ring

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: discharge of the signed block estimate

This file performs continuous Abel summation on the exact block profile.  With
`A=X_{k+1}`, `B=X_k`, and `f=cdem4345_assembled_lemma1BlockProfile x k`, it gives

`sum h(a)f(a) = f(B)H(B)-f(A)H(A)-integral_A^B H(t)f'(t)dt`.

Substituting `H(t)=2t/3+rho(t)` has two effects:

* the linear part is `(2/3) integral_A^B f`, hence the printed raw main term;
* because `f(A)=f(B)=1/4`, the endpoint error remains the signed difference
  `(rho(B)-rho(A))/4`.

The remaining term is `r_k=-integral rho(t)f'(t)dt`.  The already proved bounds
`|rho|<=4/3` and `integral |f'|=1/2` give `|r_k|<=2/3`.  This proves
`cdem4345_assembled_Lemma1PeriodicSignedRemainderAt` without taking absolute values of the endpoint
`rho` differences.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset MeasureTheory Set intervalIntegral
open scoped BigOperators

/-! ## Measurability and the exact counting function -/

theorem cdem4345_assembled_measurable_lemma1H : Measurable cdem4345_assembled_lemma1H := by
  let g : ℕ → ℝ := fun N =>
    (N : ℝ) - ((N / 4 : ℕ) : ℝ) - ((N / 9 : ℕ) : ℝ)
      + ((N / 36 : ℕ) : ℝ)
  have hg : Measurable g := Measurable.of_discrete
  have hfactor : cdem4345_assembled_lemma1H = g ∘ (fun t : ℝ => ⌊t⌋₊) := by
    funext t
    rw [cdem4345_assembled_lemma1H]
    dsimp [g]
    have h4 : ⌊t / (4 : ℝ)⌋₊ = ⌊t⌋₊ / 4 := by
      simpa using Nat.floor_div_natCast t 4
    have h9 : ⌊t / (9 : ℝ)⌋₊ = ⌊t⌋₊ / 9 := by
      simpa using Nat.floor_div_natCast t 9
    have h36 : ⌊t / (36 : ℝ)⌋₊ = ⌊t⌋₊ / 36 := by
      simpa using Nat.floor_div_natCast t 36
    rw [h4, h9, h36]
  rw [hfactor]
  exact hg.comp Nat.measurable_floor

theorem cdem4345_assembled_measurable_lemma1Rho : Measurable cdem4345_assembled_lemma1Rho := by
  change Measurable (fun z : ℝ => cdem4345_assembled_lemma1H z - (2 / 3 : ℝ) * z)
  exact cdem4345_assembled_measurable_lemma1H.sub (measurable_const.mul measurable_id)

/-- The cumulative sum required by continuous Abel summation is exactly `H`. -/
theorem cdem4345_assembled_sum_Icc_zero_lemma1PeriodWeight_eq_H (z : ℝ) :
    (∑ a ∈ Finset.Icc 0 ⌊z⌋₊, cdem4345_assembled_lemma1PeriodWeight a) = cdem4345_assembled_lemma1H z := by
  have hsets : Finset.Icc 0 ⌊z⌋₊
      = insert 0 (Finset.Icc 1 ⌊z⌋₊) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hzero : cdem4345_assembled_lemma1PeriodWeight 0 = 0 := by simp [cdem4345_assembled_lemma1PeriodWeight]
  rw [hsets, Finset.sum_insert (by simp), hzero, zero_add]
  exact cdem4345_assembled_lemma1PeriodCountAt_proven z

/-! ## The signed remainder integral -/

/-- Integrability of the absolute derivative on the live block. -/
theorem cdem4345_assembled_integrableOn_abs_lemma1BlockProfileDeriv
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    IntegrableOn (fun t => |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
      (Set.Ioc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k)) := by
  have hAB := (cdem4345_assembled_lemma1X_succ_lt hx hk).le
  have hbase := cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
    (x := x) (k := k)
    (a := cdem4345_assembled_lemma1X x (k + 1)) (b := cdem4345_assembled_lemma1X x k)
    (cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)) hAB
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB] at hbase
  exact hbase.norm

/-- The signed `rho f'` remainder has the sharp `2/3` bound. -/
theorem cdem4345_assembled_abs_integral_lemma1Rho_mul_profileDeriv_le
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    |∫ t in Set.Ioc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
        cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t| ≤ 2 / 3 := by
  let A := cdem4345_assembled_lemma1X x (k + 1)
  let B := cdem4345_assembled_lemma1X x k
  have hAB : A ≤ B := (cdem4345_assembled_lemma1X_succ_lt hx hk).le
  have hA : 0 < A := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
  have habs : IntegrableOn (fun t => |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
      (Set.Ioc A B) := cdem4345_assembled_integrableOn_abs_lemma1BlockProfileDeriv hx hk
  have hmajor : IntegrableOn
      (fun t => 4 / 3 * |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) (Set.Ioc A B) :=
    habs.const_mul (4 / 3)
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioc A B)),
      ‖cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t‖
        ≤ 4 / 3 * |cdem4345_assembled_lemma1BlockProfileDeriv x k t| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_mul]
    have ht0 : 0 ≤ t := (hA.trans ht.1).le
    exact mul_le_mul_of_nonneg_right (cdem4345_assembled_lemma1Rho_abs_le_four_thirds ht0)
      (abs_nonneg _)
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le
    (f := fun t => cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t)
    (g := fun t => 4 / 3 * |cdem4345_assembled_lemma1BlockProfileDeriv x k t|)
    hmajor hae
  rw [Real.norm_eq_abs] at hnorm
  calc
    |∫ t in Set.Ioc A B, cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t|
        ≤ ∫ t in Set.Ioc A B, 4 / 3 * |cdem4345_assembled_lemma1BlockProfileDeriv x k t| := hnorm
    _ = 4 / 3 * (∫ t in Set.Ioc A B, |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) := by
      rw [MeasureTheory.integral_const_mul]
    _ = 4 / 3 * (∫ t in A..B, |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) := by
      rw [intervalIntegral.integral_of_le hAB]
    _ = 2 / 3 := by
      rw [cdem4345_assembled_intervalIntegral_abs_lemma1BlockProfileDeriv hx hk]
      ring

/-! ## Continuous Abel summation and the linear main term -/

/-- Integration by parts for the linear `2t/3` part of `H`. -/
theorem cdem4345_assembled_lemma1BlockProfile_linear_abel
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    2 / 3 *
        (cdem4345_assembled_lemma1X x k * cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x k)
          - cdem4345_assembled_lemma1X x (k + 1) * cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x (k + 1))
          - ∫ t in Set.Ioc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
              t * cdem4345_assembled_lemma1BlockProfileDeriv x k t)
      = cdem4345_assembled_lemma1RawBlockMain x k := by
  let A := cdem4345_assembled_lemma1X x (k + 1)
  let B := cdem4345_assembled_lemma1X x k
  let F : ℝ → ℝ := fun t =>
    t * cdem4345_assembled_lemma1BlockProfile x k t - cdem4345_assembled_lemma1BlockProfilePrimitive x k t
  have hAB : A ≤ B := (cdem4345_assembled_lemma1X_succ_lt hx hk).le
  have hA : 0 < A := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
  have hderiv : ∀ t ∈ Set.uIcc A B,
      HasDerivAt F (t * cdem4345_assembled_lemma1BlockProfileDeriv x k t) t := by
    intro t ht
    rw [Set.uIcc_of_le hAB] at ht
    have ht0 : t ≠ 0 := by linarith [hA, ht.1]
    have hp := (hasDerivAt_id t).mul
      (cdem4345_assembled_hasDerivAt_lemma1BlockProfile (x := x) (k := k) ht0)
    have hP := cdem4345_assembled_hasDerivAt_lemma1BlockProfilePrimitive (x := x) (k := k) ht0
    change HasDerivAt (fun u : ℝ =>
      u * cdem4345_assembled_lemma1BlockProfile x k u - cdem4345_assembled_lemma1BlockProfilePrimitive x k u)
        (t * cdem4345_assembled_lemma1BlockProfileDeriv x k t) t
    have h : HasDerivAt
        (id * cdem4345_assembled_lemma1BlockProfile x k - cdem4345_assembled_lemma1BlockProfilePrimitive x k)
        (t * cdem4345_assembled_lemma1BlockProfileDeriv x k t) t := by
      refine (hp.sub hP).congr_deriv ?_
      simp only [id_eq, one_mul]
      ring
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with u
    rfl
  have hint : IntervalIntegrable
      (fun t => t * cdem4345_assembled_lemma1BlockProfileDeriv x k t) volume A B := by
    have hbase := cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
      (x := x) (k := k) (a := A) (b := B) hA hAB
    simpa [mul_comm] using hbase.mul_continuousOn continuousOn_id
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hparts :
      B * cdem4345_assembled_lemma1BlockProfile x k B - A * cdem4345_assembled_lemma1BlockProfile x k A
          - ∫ t in Set.Ioc A B, t * cdem4345_assembled_lemma1BlockProfileDeriv x k t
        = ∫ t in A..B, cdem4345_assembled_lemma1BlockProfile x k t := by
    rw [← intervalIntegral.integral_of_le hAB, hFTC,
      cdem4345_assembled_intervalIntegral_lemma1BlockProfile_eq_primitive_sub hx hk]
    dsimp [F]
    ring
  rw [hparts]
  exact cdem4345_assembled_two_thirds_integral_lemma1BlockProfile_eq_raw hx hk

/-- Exact continuous Abel identity for the block profile. -/
theorem cdem4345_assembled_lemma1BlockMass_abel
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_lemma1BlockMass x k
      = cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x k) * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x k)
          - cdem4345_assembled_lemma1BlockProfile x k (cdem4345_assembled_lemma1X x (k + 1))
              * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x (k + 1))
          - ∫ t in Set.Ioc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
              cdem4345_assembled_lemma1BlockProfileDeriv x k t * cdem4345_assembled_lemma1H t := by
  have hAB := (cdem4345_assembled_lemma1X_succ_lt hx hk).le
  have hA := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
  have hhas : ∀ t ∈ Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
      HasDerivAt (cdem4345_assembled_lemma1BlockProfile x k) (cdem4345_assembled_lemma1BlockProfileDeriv x k t) t := by
    intro t ht
    exact cdem4345_assembled_hasDerivAt_lemma1BlockProfile (x := x) (k := k)
      (by linarith [hA, ht.1])
  have hdiff : ∀ t ∈ Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
      DifferentiableAt ℝ (cdem4345_assembled_lemma1BlockProfile x k) t := by
    intro t ht
    exact (hhas t ht).differentiableAt
  have hint : IntegrableOn (deriv (cdem4345_assembled_lemma1BlockProfile x k))
      (Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k)) := by
    have hcont : ContinuousOn (cdem4345_assembled_lemma1BlockProfileDeriv x k)
        (Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k)) := by
      intro t ht
      have ht0 : t ≠ 0 := by linarith [hA, ht.1]
      change ContinuousWithinAt
        (fun u : ℝ => (-4 * x / u ^ 3) *
          (x / u ^ 2 - (k : ℝ) - 1 / 2))
        (Set.Icc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k)) t
      have hrat : ContinuousAt (fun u : ℝ => -4 * x / u ^ 3) t :=
        continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht0)
      have hinner : ContinuousAt
          (fun u : ℝ => x / u ^ 2 - (k : ℝ) - 1 / 2) t :=
        ((continuousAt_const.div (continuousAt_id.pow 2)
          (pow_ne_zero 2 ht0)).sub_const _).sub_const _
      exact (hrat.mul hinner).continuousWithinAt
    refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
    exact (hhas t ht).deriv.symm
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := cdem4345_assembled_lemma1PeriodWeight) (f := cdem4345_assembled_lemma1BlockProfile x k)
    (a := cdem4345_assembled_lemma1X x (k + 1)) (b := cdem4345_assembled_lemma1X x k)
    (cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)).le hAB hdiff hint
  simp_rw [cdem4345_assembled_sum_Icc_zero_lemma1PeriodWeight_eq_H] at habel
  have hintegral :
      (∫ t in Set.Ioc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
          deriv (cdem4345_assembled_lemma1BlockProfile x k) t * cdem4345_assembled_lemma1H t) =
        ∫ t in Set.Ioc (cdem4345_assembled_lemma1X x (k + 1)) (cdem4345_assembled_lemma1X x k),
          cdem4345_assembled_lemma1BlockProfileDeriv x k t * cdem4345_assembled_lemma1H t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv (cdem4345_assembled_lemma1BlockProfile x k) t * cdem4345_assembled_lemma1H t =
      cdem4345_assembled_lemma1BlockProfileDeriv x k t * cdem4345_assembled_lemma1H t
    rw [(hhas t ⟨ht.1.le, ht.2⟩).deriv]
  rw [hintegral] at habel
  rw [cdem4345_assembled_lemma1BlockMass_eq_profile hx hk]
  calc
    (∑ a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊,
        cdem4345_assembled_lemma1PeriodWeight a * cdem4345_assembled_lemma1BlockProfile x k a)
        = ∑ a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊,
            cdem4345_assembled_lemma1BlockProfile x k a * cdem4345_assembled_lemma1PeriodWeight a := by
              apply Finset.sum_congr rfl
              intro a _
              ring
    _ = _ := habel

/-! ## Discharge of the local signed proposition -/

theorem cdem4345_assembled_lemma1PeriodicSignedRemainderAt_proven
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 1 ≤ k) :
    cdem4345_assembled_Lemma1PeriodicSignedRemainderAt x k := by
  let A := cdem4345_assembled_lemma1X x (k + 1)
  let B := cdem4345_assembled_lemma1X x k
  let r : ℝ := -∫ t in Set.Ioc A B,
    cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t
  refine ⟨r, ?_, ?_⟩
  · dsimp [r, A, B]
    rw [abs_neg]
    exact cdem4345_assembled_abs_integral_lemma1Rho_mul_profileDeriv_le hx hk
  · have habel := cdem4345_assembled_lemma1BlockMass_abel hx hk
    have hmain := cdem4345_assembled_lemma1BlockProfile_linear_abel hx hk
    have hAend := cdem4345_assembled_lemma1BlockProfile_left_endpoint hx hk
    have hBend := cdem4345_assembled_lemma1BlockProfile_right_endpoint hx hk
    have hsplit :
        (∫ t in Set.Ioc A B,
          cdem4345_assembled_lemma1BlockProfileDeriv x k t * cdem4345_assembled_lemma1H t)
          = 2 / 3 * (∫ t in Set.Ioc A B,
              t * cdem4345_assembled_lemma1BlockProfileDeriv x k t)
            + ∫ t in Set.Ioc A B,
                cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t := by
      have hAB : A ≤ B := (cdem4345_assembled_lemma1X_succ_lt hx hk).le
      have hA : 0 < A := cdem4345_assembled_lemma1X_pos hx (by omega : 1 ≤ k + 1)
      have hD := cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
        (x := x) (k := k) (a := A) (b := B) hA hAB
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB] at hD
      have htD : IntegrableOn (fun t => t * cdem4345_assembled_lemma1BlockProfileDeriv x k t)
          (Set.Ioc A B) := by
        have hmul := (cdem4345_assembled_intervalIntegrable_lemma1BlockProfileDeriv
          (x := x) (k := k) (a := A) (b := B) hA hAB).mul_continuousOn
            continuousOn_id
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hAB] at hmul
        simpa [mul_comm] using hmul
      have hrD : IntegrableOn
          (fun t => cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t)
          (Set.Ioc A B) := by
        have hmajor : IntegrableOn
            (fun t => 4 / 3 * |cdem4345_assembled_lemma1BlockProfileDeriv x k t|) (Set.Ioc A B) :=
          (cdem4345_assembled_integrableOn_abs_lemma1BlockProfileDeriv hx hk).const_mul _
        refine hmajor.mono' ((cdem4345_assembled_measurable_lemma1Rho.mul ?_).aestronglyMeasurable) ?_
        · change Measurable (fun t : ℝ => (-4 * x / t ^ 3) *
            (x / t ^ 2 - (k : ℝ) - 1 / 2))
          fun_prop
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right
            (cdem4345_assembled_lemma1Rho_abs_le_four_thirds (hA.trans ht.1).le) (abs_nonneg _)
      have heq : ∀ t ∈ Set.Ioc A B,
          cdem4345_assembled_lemma1BlockProfileDeriv x k t * cdem4345_assembled_lemma1H t
            = 2 / 3 * (t * cdem4345_assembled_lemma1BlockProfileDeriv x k t)
              + cdem4345_assembled_lemma1Rho t * cdem4345_assembled_lemma1BlockProfileDeriv x k t := by
        intro t _
        rw [cdem4345_assembled_lemma1H_eq_two_thirds_add_rho]
        ring
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc heq,
        MeasureTheory.integral_add (htD.const_mul _) hrD,
        MeasureTheory.integral_const_mul]
    rw [habel, hsplit, hAend, hBend]
    rw [hAend, hBend] at hmain
    dsimp [A, B, r] at hmain ⊢
    rw [cdem4345_assembled_lemma1H_eq_two_thirds_add_rho, cdem4345_assembled_lemma1H_eq_two_thirds_add_rho]
    linear_combination hmain

/-- Full discharge of the original periodic block estimate in its paper range. -/
theorem cdem4345_assembled_lemma1PeriodicBlockEstimateAt_proven
    {x : ℝ} {k : ℕ} (hx : 0 < x) (hk : 5 ≤ k) :
    cdem4345_assembled_Lemma1PeriodicBlockEstimateAt x k :=
  cdem4345_assembled_lemma1_periodicBlockEstimate_of_signed_provenShift hk
    (cdem4345_assembled_lemma1PeriodicSignedRemainderAt_proven hx (by omega))

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: assembly of the global periodic majorant

The paper's cutoff `N` means blocks `k=n,...,N-1` followed by the residual interval
`[1,X_N]`.  This file proves that exact finite partition and folds the proved local
block estimates.

The negative terminal shifted-square-root endpoint is retained.  Dropping it would
leave `X_N/6`; together with it the effective coefficient is `X_N/9`, which is the
constant needed by the paper's cube-root cutoff.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

private noncomputable def cdem4345_assembled_lemma1PeriodicSummand (x : ℝ) (a : ℕ) : ℝ :=
  cdem4345_assembled_lemma1PeriodWeight a * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2

private theorem cdem4345_assembled_sum_Icc_one_eq_sum_Ioc_zero (g : ℕ → ℝ) (M : ℕ) :
    (∑ a ∈ Finset.Icc 1 M, g a) = ∑ a ∈ Finset.Ioc 0 M, g a := by
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  · intro a _
    rfl

private theorem cdem4345_assembled_lemma1BlockMass_eq_periodicSummand (x : ℝ) (k : ℕ) :
    cdem4345_assembled_lemma1BlockMass x k
      = ∑ a ∈ Finset.Ioc ⌊cdem4345_assembled_lemma1X x (k + 1)⌋₊ ⌊cdem4345_assembled_lemma1X x k⌋₊,
          cdem4345_assembled_lemma1PeriodicSummand x a := by
  rfl

private theorem cdem4345_assembled_lemma1BlockRemainder_eq_periodicSummand (x : ℝ) (N : ℕ) :
    cdem4345_assembled_lemma1BlockRemainder x N
      = ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊,
          cdem4345_assembled_lemma1PeriodicSummand x a := by
  rfl

/-- Exact partition into blocks `n,...,N` and the remainder below `X_{N+1}`. -/
theorem cdem4345_assembled_lemma1CenteredSquareMass_block_partition
    {x : ℝ} {n N : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnN : n ≤ N) :
    cdem4345_assembled_lemma1CenteredSquareMass x n
      = (∑ k ∈ Finset.Icc n N, cdem4345_assembled_lemma1BlockMass x k)
          + cdem4345_assembled_lemma1BlockRemainder x N := by
  rw [cdem4345_assembled_centeredSquareMass_eq_periodWeight]
  induction N, hnN using Nat.le_induction with
  | base =>
      rw [Finset.Icc_self, Finset.sum_singleton,
        cdem4345_assembled_lemma1BlockMass_eq_periodicSummand,
        cdem4345_assembled_lemma1BlockRemainder_eq_periodicSummand,
        cdem4345_assembled_sum_Icc_one_eq_sum_Ioc_zero]
      have hfloor : ⌊cdem4345_assembled_lemma1X x (n + 1)⌋₊ ≤ ⌊cdem4345_assembled_lemma1X x n⌋₊ :=
        Nat.floor_le_floor (cdem4345_assembled_lemma1X_succ_lt hx hn).le
      have hsum := Finset.sum_Ioc_consecutive (cdem4345_assembled_lemma1PeriodicSummand x)
        (Nat.zero_le ⌊cdem4345_assembled_lemma1X x (n + 1)⌋₊) hfloor
      rw [← cdem4345_assembled_sum_Icc_one_eq_sum_Ioc_zero] at hsum
      simpa only [cdem4345_assembled_lemma1PeriodicSummand, add_comm] using hsum.symm
  | succ N hnN ih =>
      rw [Finset.sum_Icc_succ_top (by omega : n ≤ N + 1), ih,
        cdem4345_assembled_lemma1BlockMass_eq_periodicSummand,
        cdem4345_assembled_lemma1BlockRemainder_eq_periodicSummand,
        cdem4345_assembled_lemma1BlockRemainder_eq_periodicSummand,
        cdem4345_assembled_sum_Icc_one_eq_sum_Ioc_zero, cdem4345_assembled_sum_Icc_one_eq_sum_Ioc_zero]
      have hfloor : ⌊cdem4345_assembled_lemma1X x (N + 2)⌋₊ ≤ ⌊cdem4345_assembled_lemma1X x (N + 1)⌋₊ :=
        Nat.floor_le_floor (cdem4345_assembled_lemma1X_succ_lt hx (by omega : 1 ≤ N + 1)).le
      have hsum := Finset.sum_Ioc_consecutive (cdem4345_assembled_lemma1PeriodicSummand x)
        (Nat.zero_le ⌊cdem4345_assembled_lemma1X x (N + 2)⌋₊) hfloor
      linarith

/-- The one remaining scalar comparison after the exact signed telescope.  It retains
the terminal `N-0.02` endpoint. -/
def cdem4345_assembled_Lemma1PeriodicCutoffScalarAt (x : ℝ) (N : ℕ) : Prop :=
  -(Real.sqrt x / 18) * cdem4345_assembled_lemma1ShiftedSqrtEndpoint N
      + 1 / 6 * cdem4345_assembled_lemma1X x N + 2 / 3 * (N : ℝ)
    ≤ (12 * x) ^ ((1 : ℝ) / 3) / 6

/-- Exact envelope fold for a paper cutoff `N`: blocks stop at `N-1`, and the lower
remainder is counted at `X_N`. -/
theorem cdem4345_assembled_lemma1BlockEnvelope_fold_to_SFactor
    {x : ℝ} {n N : ℕ} (hx : 0 < x) (hn : 5 ≤ n) (hnN : n < N)
    (hscalar : cdem4345_assembled_Lemma1PeriodicCutoffScalarAt x N) :
    (∑ k ∈ Finset.Icc n (N - 1), cdem4345_assembled_lemma1BlockEnvelope x k)
        + 1 / 4 * cdem4345_assembled_lemma1H (cdem4345_assembled_lemma1X x N)
      ≤ cdem4345_assembled_lemma1SFactor x n := by
  have hnNm1 : n ≤ N - 1 := by omega
  have htel := cdem4345_assembled_lemma1BlockEnvelope_add_remainder_count x hnNm1
  have hindex : N - 1 + 1 = N := by omega
  rw [hindex] at htel
  have hXn0 : 0 ≤ cdem4345_assembled_lemma1X x n := (cdem4345_assembled_lemma1X_pos hx (by omega)).le
  have hrho := cdem4345_assembled_lemma1Rho_le_four_thirds hXn0
  rw [cdem4345_assembled_Lemma1PeriodicCutoffScalarAt] at hscalar
  rw [htel, cdem4345_assembled_lemma1SFactor]
  have hfirst : Real.sqrt x / 18 * cdem4345_assembled_lemma1ShiftedSqrtEndpoint n
      = Real.sqrt x / (18 * Real.sqrt ((n : ℝ) - 2 / 100)) := by
    rw [cdem4345_assembled_lemma1ShiftedSqrtEndpoint]
    ring
  rw [mul_sub, hfirst]
  rw [Nat.cast_sub (by omega : n ≤ N)]
  linarith

/-- Global periodic majorant from the proved local blocks and one scalar cutoff. -/
theorem cdem4345_assembled_lemma1PeriodicMajorantAt_of_cutoff
    {x : ℝ} {n N : ℕ} (hx : 0 < x) (hn : 5 ≤ n) (hnN : n < N)
    (hscalar : cdem4345_assembled_Lemma1PeriodicCutoffScalarAt x N) :
    cdem4345_assembled_Lemma1PeriodicMajorantAt x n := by
  apply cdem4345_assembled_lemma1_periodicMajorant_of_blocks (N := N - 1) (by omega)
  · exact cdem4345_assembled_lemma1CenteredSquareMass_block_partition hx (by omega) (by omega)
  · intro k hk
    exact cdem4345_assembled_lemma1PeriodicBlockEstimateAt_proven hx (by
      simp only [Finset.mem_Icc] at hk
      omega)
  · have h := cdem4345_assembled_lemma1BlockRemainder_le_quarter_H_proven x (N - 1)
    simpa only [show N - 1 + 1 = N by omega] using h
  · simpa [show N - 1 + 1 = N by omega] using
      cdem4345_assembled_lemma1BlockEnvelope_fold_to_SFactor hx hn hnN hscalar

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the integer cube-root cutoff

Let `y=(x/144)^(1/3)` and `N=floor y`.  The real optimum of the relaxed cutoff
expression is `N=y`.  Rounding costs at most `2/(3N)`.  The retained shifted endpoint
`N-0.02` saves at least `1/150`; hence the integer cutoff is no worse than the real
optimum as soon as `N>=100`.

This is why the negative endpoint in the signed telescope cannot be discarded.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

noncomputable def cdem4345_assembled_lemma1PeriodicCutoffY (x : ℝ) : ℝ :=
  (x / 144) ^ ((1 : ℝ) / 3)

noncomputable def cdem4345_assembled_lemma1PeriodicCutoff (x : ℝ) : ℕ :=
  ⌊cdem4345_assembled_lemma1PeriodicCutoffY x⌋₊

theorem cdem4345_assembled_lemma1PeriodicCutoffY_pos {x : ℝ} (hx : 0 < x) :
    0 < cdem4345_assembled_lemma1PeriodicCutoffY x := by
  rw [cdem4345_assembled_lemma1PeriodicCutoffY]
  exact Real.rpow_pos_of_pos (by positivity) _

theorem cdem4345_assembled_lemma1PeriodicCutoffY_cube {x : ℝ} (hx : 0 < x) :
    cdem4345_assembled_lemma1PeriodicCutoffY x ^ (3 : ℕ) = x / 144 := by
  rw [cdem4345_assembled_lemma1PeriodicCutoffY, ← Real.rpow_natCast
    ((x / 144) ^ ((1 : ℝ) / 3)) 3,
    ← Real.rpow_mul (show 0 ≤ x / 144 by positivity)]
  norm_num

theorem cdem4345_assembled_sqrt_eq_twelve_mul_cutoffY_sqrt
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt x
      = 12 * cdem4345_assembled_lemma1PeriodicCutoffY x * Real.sqrt (cdem4345_assembled_lemma1PeriodicCutoffY x) := by
  have hy := cdem4345_assembled_lemma1PeriodicCutoffY_pos hx
  have hy3 := cdem4345_assembled_lemma1PeriodicCutoffY_cube hx
  have hsx2 := Real.sq_sqrt hx.le
  have hsy2 := Real.sq_sqrt hy.le
  have hrhs0 : 0 ≤ 12 * cdem4345_assembled_lemma1PeriodicCutoffY x
      * Real.sqrt (cdem4345_assembled_lemma1PeriodicCutoffY x) := by positivity
  rw [← sq_eq_sq₀ (Real.sqrt_nonneg x) hrhs0]
  rw [hsx2]
  have hrhsSquare :
      (12 * cdem4345_assembled_lemma1PeriodicCutoffY x * Real.sqrt (cdem4345_assembled_lemma1PeriodicCutoffY x)) ^ 2
        = 144 * cdem4345_assembled_lemma1PeriodicCutoffY x ^ 3 := by
    calc
      (12 * cdem4345_assembled_lemma1PeriodicCutoffY x * Real.sqrt (cdem4345_assembled_lemma1PeriodicCutoffY x)) ^ 2
          = 144 * cdem4345_assembled_lemma1PeriodicCutoffY x ^ 2
              * Real.sqrt (cdem4345_assembled_lemma1PeriodicCutoffY x) ^ 2 := by ring
      _ = 144 * cdem4345_assembled_lemma1PeriodicCutoffY x ^ 3 := by rw [hsy2]; ring
  rw [hrhsSquare]
  nlinarith

theorem cdem4345_assembled_cubeTerm_eq_two_mul_cutoffY
    {x : ℝ} (hx : 0 < x) :
    (12 * x) ^ ((1 : ℝ) / 3) / 6 = 2 * cdem4345_assembled_lemma1PeriodicCutoffY x := by
  have hq : 0 < x / 144 := by positivity
  calc
    (12 * x) ^ ((1 : ℝ) / 3) / 6
        = (1728 * (x / 144)) ^ ((1 : ℝ) / 3) / 6 := by ring
    _ = (1728 : ℝ) ^ ((1 : ℝ) / 3)
          * (x / 144) ^ ((1 : ℝ) / 3) / 6 := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1728) hq.le]
    _ = 2 * cdem4345_assembled_lemma1PeriodicCutoffY x := by
      have h1728 : (1728 : ℝ) ^ ((1 : ℝ) / 3) = 12 := by
        rw [show (1728 : ℝ) = 12 ^ (3 : ℕ) by norm_num,
          ← Real.rpow_natCast (12 : ℝ) 3,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 12)]
        norm_num
      rw [h1728, cdem4345_assembled_lemma1PeriodicCutoffY]
      ring

/-- The scalar rounding lemma, stated independently of the rpow definition. -/
theorem cdem4345_assembled_lemma1PeriodicCutoffScalar_of_floor_data
    {x y : ℝ} {N : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hN : 100 ≤ N)
    (hNy : (N : ℝ) ≤ y) (hyN : y < (N : ℝ) + 1)
    (hsx : Real.sqrt x = 12 * y * Real.sqrt y)
    (hcube : (12 * x) ^ ((1 : ℝ) / 3) / 6 = 2 * y) :
    cdem4345_assembled_Lemma1PeriodicCutoffScalarAt x N := by
  let sN : ℝ := Real.sqrt N
  let sm : ℝ := Real.sqrt ((N : ℝ) - 1 / 50)
  let sy : ℝ := Real.sqrt y
  let d : ℝ := y - N
  have hNR : (100 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hNm : 0 < (N : ℝ) - 1 / 50 := by linarith
  have hsN : 0 < sN := Real.sqrt_pos.2 hN0
  have hsm : 0 < sm := Real.sqrt_pos.2 hNm
  have hsy : 0 < sy := Real.sqrt_pos.2 hy
  have hsN2 : sN ^ 2 = (N : ℝ) := by
    simpa [sN] using Real.sq_sqrt hN0.le
  have hsm2 : sm ^ 2 = (N : ℝ) - 1 / 50 := by
    simpa [sm] using Real.sq_sqrt hNm.le
  have hsy2 : sy ^ 2 = y := by simpa [sy] using Real.sq_sqrt hy.le
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith

  -- Concavity of sqrt, in the exact form needed for rounding `y` down to `N`.
  have hratio : sy / sN ≤ 1 + d / (2 * (N : ℝ)) := by
    have hrhs0 : 0 ≤ 1 + d / (2 * (N : ℝ)) := by positivity
    apply (sq_le_sq₀ (div_nonneg hsy.le hsN.le) hrhs0).mp
    rw [div_pow, hsy2, hsN2]
    dsimp [d]
    field_simp [show (N : ℝ) ≠ 0 by positivity]
    nlinarith [sq_nonneg (y - (N : ℝ))]
  have hd_sq : d ^ 2 ≤ 1 := by
    have := mul_nonneg hd0 (sub_nonneg.mpr hd1.le)
    nlinarith
  have hround : Real.sqrt x / (9 * sN) + 2 / 3 * (N : ℝ)
      ≤ 2 * y + 2 / (3 * (N : ℝ)) := by
    rw [hsx]
    have hmul := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 4 / 3 * y by positivity)
    have hcalc : 4 / 3 * y * (1 + d / (2 * (N : ℝ)))
          + 2 / 3 * (N : ℝ)
        = 2 * y + 2 / (3 * (N : ℝ)) * d ^ 2 := by
      dsimp [d]
      field_simp [show (N : ℝ) ≠ 0 by positivity]
      ring
    calc
      12 * y * sy / (9 * sN) + 2 / 3 * (N : ℝ)
          = 4 / 3 * y * (sy / sN) + 2 / 3 * (N : ℝ) := by ring
      _ ≤ 4 / 3 * y * (1 + d / (2 * (N : ℝ)))
            + 2 / 3 * (N : ℝ) := by linarith
      _ = 2 * y + 2 / (3 * (N : ℝ)) * d ^ 2 := hcalc
      _ ≤ 2 * y + 2 / (3 * (N : ℝ)) := by
        have hcoeff : 0 ≤ 2 / (3 * (N : ℝ)) := by positivity
        simpa only [mul_one, add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_left hd_sq hcoeff) (2 * y)

  -- The `0.02` shift saves at least `1/150`.
  have hms : sm ≤ sN := by
    dsimp [sm, sN]
    exact Real.sqrt_le_sqrt (by linarith)
  have hdiffprod : (sN - sm) * (sN + sm) = 1 / 50 := by
    nlinarith [hsN2, hsm2]
  have hdiff : 1 / sm - 1 / sN
      = (1 / 50) / (sm * sN * (sN + sm)) := by
    field_simp [hsm.ne', hsN.ne']
    nlinarith [hdiffprod]
  have hdenle : sm * sN * (sN + sm) ≤ 2 * (N : ℝ) * sN := by
    have h1 : sm * sN ≤ sN * sN :=
      mul_le_mul_of_nonneg_right hms hsN.le
    have h2 : sN + sm ≤ 2 * sN := by linarith
    calc
      sm * sN * (sN + sm) ≤ (sN * sN) * (2 * sN) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 * (N : ℝ) * sN := by rw [← pow_two sN, hsN2]; ring
  have hdifflo : 1 / (100 * (N : ℝ) * sN) ≤ 1 / sm - 1 / sN := by
    rw [hdiff]
    have hinv := one_div_le_one_div_of_le (by positivity) hdenle
    calc
      1 / (100 * (N : ℝ) * sN)
          = (1 / 50) * (1 / (2 * (N : ℝ) * sN)) := by ring
      _ ≤ (1 / 50) * (1 / (sm * sN * (sN + sm))) := by gcongr
      _ = (1 / 50) / (sm * sN * (sN + sm)) := by ring
  have hsyN : sN ≤ sy := by
    dsimp [sN, sy]
    exact Real.sqrt_le_sqrt hNy
  have hprod : (N : ℝ) * sN ≤ y * sy :=
    mul_le_mul hNy hsyN hsN.le hy.le
  have hsave : 1 / 150 ≤ Real.sqrt x / 18 * (1 / sm - 1 / sN) := by
    have hmul := mul_le_mul_of_nonneg_left hdifflo
      (show 0 ≤ Real.sqrt x / 18 by positivity)
    rw [hsx] at hmul
    have hratioN : 1 ≤ y * sy / ((N : ℝ) * sN) := by
      rw [le_div_iff₀ (by positivity)]
      simpa only [one_mul] using hprod
    calc
      1 / 150 ≤ 1 / 150 * (y * sy / ((N : ℝ) * sN)) := by
        nlinarith
      _ = (12 * y * sy) / 18 * (1 / (100 * (N : ℝ) * sN)) := by ring
      _ ≤ (12 * y * sy) / 18 * (1 / sm - 1 / sN) := hmul
      _ = Real.sqrt x / 18 * (1 / sm - 1 / sN) := by
        rw [hsx]
  have hround_save : 2 / (3 * (N : ℝ)) ≤ 1 / 150 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith

  rw [cdem4345_assembled_Lemma1PeriodicCutoffScalarAt, cdem4345_assembled_lemma1ShiftedSqrtEndpoint, cdem4345_assembled_lemma1X,
    Real.sqrt_div hx.le, hcube]
  have hshift : (2 : ℝ) / 100 = 1 / 50 := by norm_num
  rw [hshift]
  change -(Real.sqrt x / 18) * (1 / sm)
      + 1 / 6 * (Real.sqrt x / sN) + 2 / 3 * (N : ℝ) ≤ 2 * y
  have hrearrange :
      -(Real.sqrt x / 18) * (1 / sm)
          + 1 / 6 * (Real.sqrt x / sN) + 2 / 3 * (N : ℝ)
        = (Real.sqrt x / (9 * sN) + 2 / 3 * (N : ℝ))
            - Real.sqrt x / 18 * (1 / sm - 1 / sN) := by ring
  rw [hrearrange]
  linarith

/-- The paper cutoff satisfies the scalar fold throughout the large-x range. -/
theorem cdem4345_assembled_lemma1PeriodicCutoffScalarAt_proven
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    cdem4345_assembled_Lemma1PeriodicCutoffScalarAt x (cdem4345_assembled_lemma1PeriodicCutoff x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  let y := cdem4345_assembled_lemma1PeriodicCutoffY x
  let N := cdem4345_assembled_lemma1PeriodicCutoff x
  have hy : 0 < y := cdem4345_assembled_lemma1PeriodicCutoffY_pos hx0
  have hNy : (N : ℝ) ≤ y := Nat.floor_le hy.le
  have hyN : y < (N : ℝ) + 1 := Nat.lt_floor_add_one y
  have hy3 := cdem4345_assembled_lemma1PeriodicCutoffY_cube hx0
  have hy200 : (200 : ℝ) ≤ y := by
    apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hy.le
    rw [hy3]
    have : (200 : ℝ) ^ (3 : ℕ) ≤ x / 144 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 144)]
      norm_num [cdem4345_assembled_lemma1FinalX0] at hx ⊢
      linarith
    exact this
  have hN200 : 200 ≤ N := Nat.le_floor hy200
  exact cdem4345_assembled_lemma1PeriodicCutoffScalar_of_floor_data hx0 hy (by omega) hNy hyN
    (cdem4345_assembled_sqrt_eq_twelve_mul_cutoffY_sqrt hx0)
    (cdem4345_assembled_cubeTerm_eq_two_mul_cutoffY hx0)

/-- Unconditional global periodic majorant in the `n=197` large-x range. -/
theorem cdem4345_assembled_lemma1PeriodicMajorantAt_n197
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    cdem4345_assembled_Lemma1PeriodicMajorantAt x cdem4345_assembled_lemma1FinalN := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hscalar := cdem4345_assembled_lemma1PeriodicCutoffScalarAt_proven hx
  have hN200 : 200 ≤ cdem4345_assembled_lemma1PeriodicCutoff x := by
    let y := cdem4345_assembled_lemma1PeriodicCutoffY x
    let N := cdem4345_assembled_lemma1PeriodicCutoff x
    have hy := cdem4345_assembled_lemma1PeriodicCutoffY_pos hx0
    have hNy : (N : ℝ) ≤ y := Nat.floor_le hy.le
    have hyN : y < (N : ℝ) + 1 := Nat.lt_floor_add_one y
    have hy3 := cdem4345_assembled_lemma1PeriodicCutoffY_cube hx0
    have hy200 : (200 : ℝ) ≤ y := by
      apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hy.le
      rw [hy3]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 144)]
      norm_num [cdem4345_assembled_lemma1FinalX0] at hx ⊢
      linarith
    exact Nat.le_floor hy200
  apply cdem4345_assembled_lemma1PeriodicMajorantAt_of_cutoff hx0 (by norm_num [cdem4345_assembled_lemma1FinalN])
    (N := cdem4345_assembled_lemma1PeriodicCutoff x)
  · norm_num [cdem4345_assembled_lemma1FinalN] at hN200 ⊢
    omega
  · exact hscalar

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: centered Cauchy--Schwarz seam

This file proves `cdem4345_assembled_Lemma1CenteredCauchyAt`.  The periodic indicator is

`h(a)=1` if `4∤a` and `9∤a`, and `0` otherwise.

Every squarefree integer lies in the support of `h`, so `mu(a)h(a)=mu(a)`.  Applying
finite Cauchy--Schwarz to `mu(a)` and `h(a)({x/a²}-1/2)` gives exactly the two factors in
the paper.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

private noncomputable def cdem4345_assembled_lemma1PeriodIndicator (a : ℕ) : ℝ :=
  if 4 ∣ a ∨ 9 ∣ a then 0 else 1

private theorem cdem4345_assembled_moebius_mul_periodIndicator (a : ℕ) :
    (ArithmeticFunction.moebius a : ℝ) * cdem4345_assembled_lemma1PeriodIndicator a
      = (ArithmeticFunction.moebius a : ℝ) := by
  unfold cdem4345_assembled_lemma1PeriodIndicator
  split_ifs with h
  · have hnot : ¬Squarefree a := by
      intro hs
      rcases h with h4 | h9
      · have hs4 : Squarefree 4 := Squarefree.squarefree_of_dvd h4 hs
        exact (Nat.squarefree_iff_prime_squarefree.mp hs4 2 Nat.prime_two) (by norm_num)
      · have hs9 : Squarefree 9 := Squarefree.squarefree_of_dvd h9 hs
        exact (Nat.squarefree_iff_prime_squarefree.mp hs9 3 (by decide)) (by norm_num)
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnot]
    norm_num
  · ring

private theorem cdem4345_assembled_periodIndicator_sq (a : ℕ) :
    cdem4345_assembled_lemma1PeriodIndicator a ^ 2 = cdem4345_assembled_lemma1PeriodIndicator a := by
  unfold cdem4345_assembled_lemma1PeriodIndicator
  split_ifs <;> norm_num

private theorem cdem4345_assembled_moebius_real_sq_eq_abs (a : ℕ) :
    (ArithmeticFunction.moebius a : ℝ) ^ 2
      = |(ArithmeticFunction.moebius a : ℝ)| := by
  rcases ArithmeticFunction.moebius_eq_or a with h0 | h1 | hm1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num
  · rw [hm1]
    norm_num

/-- **CDEM Lemma 1 centered Cauchy--Schwarz, proved.** -/
theorem cdem4345_assembled_lemma1_centeredCauchy (x : ℝ) (n : ℕ) :
    cdem4345_assembled_Lemma1CenteredCauchyAt x n := by
  let s : Finset ℕ := Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊
  let centered : ℕ → ℝ := fun a => Int.fract (x / (a : ℝ) ^ 2) - 1 / 2
  let μR : ℕ → ℝ := fun a => (ArithmeticFunction.moebius a : ℝ)
  let h : ℕ → ℝ := cdem4345_assembled_lemma1PeriodIndicator
  have hrewrite :
      (∑ a ∈ s, μR a * centered a)
        = ∑ a ∈ s, μR a * (h a * centered a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, cdem4345_assembled_moebius_mul_periodIndicator]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq s μR (fun a => h a * centered a)
  have hfirst : (∑ a ∈ s, μR a ^ 2) = cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n) := by
    rw [cdem4345_assembled_squarefreeCount_eq_sum_Icc]
    apply Finset.sum_congr rfl
    intro a _
    exact cdem4345_assembled_moebius_real_sq_eq_abs a
  have hsecond :
      (∑ a ∈ s, (h a * centered a) ^ 2) = cdem4345_assembled_lemma1CenteredSquareMass x n := by
    unfold cdem4345_assembled_lemma1CenteredSquareMass
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_pow, cdem4345_assembled_periodIndicator_sq]
    rfl
  rw [← hrewrite, hfirst, hsecond] at hCS
  rw [cdem4345_assembled_Lemma1CenteredCauchyAt]
  unfold cdem4345_assembled_lemma1T3 cdem4345_assembled_lemma1CenteredSum
  have hQnonneg : 0 ≤ cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n) := by
    unfold cdem4345_assembled_squarefreeCount
    exact Finset.sum_nonneg fun a _ => abs_nonneg _
  have hSnonneg : 0 ≤ cdem4345_assembled_lemma1CenteredSquareMass x n := by
    unfold cdem4345_assembled_lemma1CenteredSquareMass
    apply Finset.sum_nonneg
    intro a _
    split <;> positivity
  rw [Real.le_sqrt (abs_nonneg _) (mul_nonneg hQnonneg hSnonneg)]
  simpa [s, centered, μR, sq_abs] using hCS

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the exact identities

This file discharges the two exact residuals left by
`CohenDressElMarrakiLemma1ExactDecomposition` in the live paper regime

`0 < x`, `1 ≤ n`, `n ≤ floor x`.

There are no estimates from CDEM in this file.  The only infinite argument is ordinary
Abel summation for the absolutely convergent series `sum mu(a)/a^2`.  Its convergence
guards are proved explicitly from the elementary bound `|M(t)| ≤ t+1`; in particular,
no prime-number theorem or Mertens estimate is used.  The second identity is a finite
reindexing of the lattice points

`n ≤ k ≤ x`, `a ≤ sqrt(x/k)`  <->  `a ≤ sqrt(x/n)`, `n ≤ k ≤ x/a^2`.

The strict positivity and denominator guards are stated on every public theorem.  They
exclude Lean's division-by-zero convention from the mathematical argument.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset MeasureTheory Filter Topology
open scoped BigOperators

/-! ## Elementary convergence guards for reciprocal-square Abel summation -/

/-- Adding the vanishing `a=0` term changes neither the Mertens step nor its value. -/
theorem cdem4345_assembled_sum_Icc_zero_moebius_eq_lemma1M (t : ℝ) :
    (∑ a ∈ Finset.Icc 0 ⌊t⌋₊,
        (ArithmeticFunction.moebius a : ℝ)) = cdem4345_assembled_lemma1M t := by
  rw [cdem4345_assembled_lemma1M_eq_sum]
  have hsets :
      Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsets, Finset.sum_insert (by simp)]
  simp

/-- The elementary step-function bound needed for the improper Abel limit.
The harmless `+1` avoids a special cardinality calculation at `0`. -/
theorem cdem4345_assembled_lemma1M_abs_le_add_one {t : ℝ} (ht : 0 ≤ t) :
    |cdem4345_assembled_lemma1M t| ≤ t + 1 := by
  rw [cdem4345_assembled_lemma1M_eq_sum]
  calc
    |∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ)|
        ≤ ∑ a ∈ Finset.Icc 1 ⌊t⌋₊,
            |(ArithmeticFunction.moebius a : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          rw [← Int.cast_abs]
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
    _ = (⌊t⌋₊ : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          ring
    _ ≤ t + 1 := by linarith [Nat.floor_le ht]

/-- The local Mertens step is measurable because it factors through natural floor. -/
theorem cdem4345_assembled_measurable_lemma1M : Measurable cdem4345_assembled_lemma1M := by
  have hsum : Measurable
      (fun N : ℕ => ∑ a ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ)) := measurable_of_countable _
  have hfactor : cdem4345_assembled_lemma1M =
      (fun N : ℕ => ∑ a ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ)) ∘ (fun t : ℝ => ⌊t⌋₊) := by
    funext t
    exact cdem4345_assembled_lemma1M_eq_sum t
  rw [hfactor]
  exact hsum.comp Nat.measurable_floor

/-- Absolute summability of `mu(a)/a^2`, by domination with the `p=2` series. -/
theorem cdem4345_assembled_summable_lemma1_moebius_div_sq :
    Summable (fun a : ℕ =>
      (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2) := by
  have hbound : ∀ a : ℕ,
      |(ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2|
        ≤ 1 / (a : ℝ) ^ 2 := by
    intro a
    rcases a.eq_zero_or_pos with rfl | ha
    · simp
    · rw [abs_div, abs_pow, Nat.abs_cast]
      have hmu : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := a)
      exact div_le_div_of_nonneg_right hmu (by positivity)
  refine (Summable.of_nonneg_of_le
    (g := fun a : ℕ =>
      |(ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2|)
    (f := fun a : ℕ => 1 / (a : ℝ) ^ 2)
    (fun a => abs_nonneg _) hbound
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))).of_abs

/-- Euler's reciprocal-square Möbius series, in the paper's `6/pi^2` normalization. -/
theorem cdem4345_assembled_tsum_lemma1_moebius_div_sq :
    (∑' a : ℕ, (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
      = 6 / Real.pi ^ 2 := by
  simpa [Nat.coprime_one_right_iff] using
    Helfgott.cdem4345_assembled_squarefree_coprime_density_series 1 (by norm_num)

/-- The reciprocal-cube Mertens integrand is absolutely integrable on every positive
half-line.  The proof uses only `|M(t)| ≤ t+1 ≤ 2t` for `t≥1`. -/
theorem cdem4345_assembled_integrableOn_lemma1M_div_cube_Ioi {u : ℝ} (hu : 1 ≤ u) :
    IntegrableOn (fun t : ℝ => cdem4345_assembled_lemma1M t / t ^ 3) (Set.Ioi u) := by
  have hmajor : IntegrableOn (fun t : ℝ => 2 * t ^ (-2 : ℝ)) (Set.Ioi u) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (lt_of_lt_of_le one_pos hu)).const_mul 2
  refine hmajor.mono' ((cdem4345_assembled_measurable_lemma1M.div
    (measurable_id.pow_const 3)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := hu.trans ht.le
  have htpos : 0 < t := one_pos.trans_le ht1
  have hM := cdem4345_assembled_lemma1M_abs_le_add_one htpos.le
  have hM2 : |cdem4345_assembled_lemma1M t| ≤ 2 * t := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos htpos]
  calc
    |cdem4345_assembled_lemma1M t| / t ^ 3 ≤ (2 * t) / t ^ 3 :=
      div_le_div_of_nonneg_right hM2 (by positivity)
    _ = 2 * t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg htpos.le, Real.rpow_two]
      field_simp

/-- The finite Abel endpoint vanishes.  Again, only the elementary bound is used. -/
theorem cdem4345_assembled_tendsto_lemma1M_div_sq_nat :
    Tendsto (fun N : ℕ => cdem4345_assembled_lemma1M N / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun N : ℕ => 2 * (N : ℝ)⁻¹) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hM := cdem4345_assembled_lemma1M_abs_le_add_one (show (0 : ℝ) ≤ N by positivity)
    have hM2 : |cdem4345_assembled_lemma1M N| ≤ 2 * (N : ℝ) := by linarith
    have hNabs : |(N : ℝ)| = (N : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg N)
    rw [Real.norm_eq_abs, abs_div, abs_pow, hNabs]
    have hNpos : (0 : ℝ) < N := by positivity
    calc
      |cdem4345_assembled_lemma1M N| / (N : ℝ) ^ 2 ≤ (2 * (N : ℝ)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hM2 (sq_nonneg _)
      _ = 2 * (N : ℝ)⁻¹ := by field_simp
  · simpa using
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ))

/-! ## Exact reciprocal-square Abel identity -/

/-- Derivative of the reciprocal-square weight, with the nonzero guard explicit. -/
private theorem cdem4345_assembled_hasDerivAt_one_div_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ => 1 / u ^ 2) (-2 / t ^ 3) t := by
  have h := (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)
  have hfun : (fun u : ℝ => 1 / u ^ 2) = (fun u : ℝ => u ^ 2)⁻¹ := by
    funext u
    simp only [Pi.inv_apply, one_div]
  rw [hfun]
  exact h.congr_deriv (by
    field_simp [ht]
    ring)

/-- Finite Abel summation between positive real endpoints.  This is the exact identity
that is sent to the improper limit; it contains no inequality. -/
theorem cdem4345_assembled_lemma1_recipSq_finite_abel
    {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    (∑ a ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
      = cdem4345_assembled_lemma1M v / v ^ 2 - cdem4345_assembled_lemma1M u / u ^ 2
        + 2 * ∫ t in Set.Ioc u v, cdem4345_assembled_lemma1M t / t ^ 3 := by
  have hdiff : ∀ t ∈ Set.Icc u v,
      DifferentiableAt ℝ (fun z : ℝ => 1 / z ^ 2) t := by
    intro t ht
    exact (cdem4345_assembled_hasDerivAt_one_div_sq
      (show t ≠ 0 by have := hu.trans ht.1; positivity)).differentiableAt
  have hint : IntegrableOn (deriv (fun z : ℝ => 1 / z ^ 2))
      (Set.Icc u v) := by
    have hcont : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Set.Icc u v) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 3)
      intro t ht
      exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le zero_lt_one (hu.trans ht.1)))
    refine (hcont.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    exact (cdem4345_assembled_hasDerivAt_one_div_sq
      (show t ≠ 0 by have := hu.trans ht.1; positivity)).deriv.symm
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun a : ℕ => (ArithmeticFunction.moebius a : ℝ))
    (f := fun z : ℝ => 1 / z ^ 2) (a := u) (b := v)
    (zero_le_one.trans hu) huv hdiff hint
  simp_rw [cdem4345_assembled_sum_Icc_zero_moebius_eq_lemma1M] at habel
  have hintegral :
      (∫ t in Set.Ioc u v,
          deriv (fun z : ℝ => 1 / z ^ 2) t * cdem4345_assembled_lemma1M t)
        = -2 * ∫ t in Set.Ioc u v, cdem4345_assembled_lemma1M t / t ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv (fun z : ℝ => 1 / z ^ 2) t * cdem4345_assembled_lemma1M t =
      -2 * (cdem4345_assembled_lemma1M t / t ^ 3)
    rw [(cdem4345_assembled_hasDerivAt_one_div_sq
      (show t ≠ 0 by have := hu.trans ht.1.le; positivity)).deriv]
    ring
  rw [hintegral] at habel
  calc
    (∑ a ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
        = ∑ a ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
            (1 / (a : ℝ) ^ 2) * (ArithmeticFunction.moebius a : ℝ) := by
              apply Finset.sum_congr rfl
              intro a _
              ring
    _ = (1 / v ^ 2) * cdem4345_assembled_lemma1M v - (1 / u ^ 2) * cdem4345_assembled_lemma1M u
          - (-2 * ∫ t in Set.Ioc u v, cdem4345_assembled_lemma1M t / t ^ 3) := habel
    _ = cdem4345_assembled_lemma1M v / v ^ 2 - cdem4345_assembled_lemma1M u / u ^ 2
          + 2 * ∫ t in Set.Ioc u v, cdem4345_assembled_lemma1M t / t ^ 3 := by ring

/-- Improper Abel summation for a positive real cutoff `u`:

`sum_{a≤u} mu(a)/a² = sum_a mu(a)/a² + M(u)/u² - 2 integral_u^infinity M(t)/t³`.

All three limiting facts used below were proved above: absolute summability, integrability
on `Ioi u`, and vanishing of the finite endpoint. -/
theorem cdem4345_assembled_lemma1_recipSq_head_eq
    {u : ℝ} (hu : 1 ≤ u) :
    (∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
      = (∑' a : ℕ,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
        + cdem4345_assembled_lemma1M u / u ^ 2
        - 2 * ∫ t in Set.Ioi u, cdem4345_assembled_lemma1M t / t ^ 3 := by
  let f : ℕ → ℝ := fun a =>
    (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2
  have hsum : Summable f := cdem4345_assembled_summable_lemma1_moebius_div_sq
  have htotal :
      Tendsto (fun N : ℕ => ∑ a ∈ Finset.Icc 0 N, f a) atTop
        (𝓝 (∑' a : ℕ, f a)) := by
    have hbase := (Summable.hasSum_iff_tendsto_nat hsum
      (m := ∑' a : ℕ, f a)).mp hsum.hasSum
    simpa [Function.comp_def, Nat.range_succ_eq_Icc_zero] using
      hbase.comp (Filter.tendsto_add_atTop_nat 1)
  have hzero : ∀ N : ℕ,
      (∑ a ∈ Finset.Icc 0 N, f a) = ∑ a ∈ Finset.Ioc 0 N, f a := by
    intro N
    rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
    simp [f]
  have htotal' :
      Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc 0 N, f a) atTop
        (𝓝 (∑' a : ℕ, f a)) :=
    htotal.congr (fun N => hzero N)
  have hleft :
      Tendsto (fun N : ℕ => ∑ a ∈ Finset.Ioc ⌊u⌋₊ N, f a) atTop
        (𝓝 ((∑' a : ℕ, f a) - ∑ a ∈ Finset.Ioc 0 ⌊u⌋₊, f a)) := by
    have hsub := htotal'.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        ∑ a ∈ Finset.Ioc 0 ⌊u⌋₊, f a) atTop
          (𝓝 (∑ a ∈ Finset.Ioc 0 ⌊u⌋₊, f a)))
    refine hsub.congr' ?_
    filter_upwards [eventually_ge_atTop ⌊u⌋₊] with N hN
    rw [← Finset.sum_Ioc_consecutive f (Nat.zero_le ⌊u⌋₊) hN]
    ring
  have hintegral := intervalIntegral_tendsto_integral_Ioi u
    (cdem4345_assembled_integrableOn_lemma1M_div_cube_Ioi hu)
    tendsto_natCast_atTop_atTop
  have hright :
      Tendsto (fun N : ℕ =>
          cdem4345_assembled_lemma1M N / (N : ℝ) ^ 2 - cdem4345_assembled_lemma1M u / u ^ 2
            + 2 * ∫ t in u..(N : ℝ), cdem4345_assembled_lemma1M t / t ^ 3) atTop
        (𝓝 (0 - cdem4345_assembled_lemma1M u / u ^ 2
          + 2 * ∫ t in Set.Ioi u, cdem4345_assembled_lemma1M t / t ^ 3)) :=
    (cdem4345_assembled_tendsto_lemma1M_div_sq_nat.sub tendsto_const_nhds).add
      (hintegral.const_mul 2)
  have heq : ∀ᶠ N : ℕ in atTop,
      (∑ a ∈ Finset.Ioc ⌊u⌋₊ N, f a)
        = cdem4345_assembled_lemma1M N / (N : ℝ) ^ 2 - cdem4345_assembled_lemma1M u / u ^ 2
            + 2 * ∫ t in u..(N : ℝ), cdem4345_assembled_lemma1M t / t ^ 3 := by
    filter_upwards [eventually_ge_atTop (⌊u⌋₊ + 1)] with N hN
    have huN : u ≤ (N : ℝ) := by
      exact (Nat.lt_floor_add_one u).le.trans (by exact_mod_cast hN)
    have habel := cdem4345_assembled_lemma1_recipSq_finite_abel hu huN
    rw [Nat.floor_natCast] at habel
    rw [intervalIntegral.integral_of_le huN]
    exact habel
  have hright' := hleft.congr' heq
  have hlimits := tendsto_nhds_unique hright' hright
  have hhead0 :
      (∑ a ∈ Finset.Ioc 0 ⌊u⌋₊, f a)
        = ∑ a ∈ Finset.Icc 1 ⌊u⌋₊, f a := by
    apply Finset.sum_congr
    · ext a
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    · intro a _
      rfl
  rw [hhead0] at hlimits
  change (∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
      (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2) = _
  dsimp [f] at hlimits
  rw [zero_sub] at hlimits
  linarith

/-- The exact reciprocal-square residual is a theorem in the live CDEM regime. -/
theorem cdem4345_assembled_lemma1_recipSqPartialSummation
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    cdem4345_assembled_Lemma1RecipSqPartialSummationAt x n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hdiv : 0 < x / (n : ℝ) := div_pos hx hnpos
  have hnxR : (n : ℝ) ≤ x := by
    have hnfloorR : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnx
    exact hnfloorR.trans (Nat.floor_le hx.le)
  have hratio : 1 ≤ x / (n : ℝ) :=
    (le_div_iff₀ hnpos).2 (by simpa using hnxR)
  have hX : 1 ≤ cdem4345_assembled_lemma1X x n := by
    unfold cdem4345_assembled_lemma1X
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hratio
  have hhead := cdem4345_assembled_lemma1_recipSq_head_eq hX
  rw [cdem4345_assembled_tsum_lemma1_moebius_div_sq] at hhead
  have hXsq : cdem4345_assembled_lemma1X x n ^ 2 = x / (n : ℝ) := by
    unfold cdem4345_assembled_lemma1X
    exact Real.sq_sqrt hdiv.le
  rw [cdem4345_assembled_Lemma1RecipSqPartialSummationAt]
  unfold cdem4345_assembled_lemma1MobiusRecipHead cdem4345_assembled_lemma1SignedTailIntegral
  calc
    x * (∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
        = x * (6 / Real.pi ^ 2 +
            cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / cdem4345_assembled_lemma1X x n ^ 2 -
            2 * ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), cdem4345_assembled_lemma1M t / t ^ 3) := by
              rw [hhead]
    _ = (6 / Real.pi ^ 2) * x +
          x * (cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / cdem4345_assembled_lemma1X x n ^ 2) -
          2 * x * ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), cdem4345_assembled_lemma1M t / t ^ 3 := by
            ring
    _ = (6 / Real.pi ^ 2) * x +
          (n : ℝ) * cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) -
          2 * x * ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), cdem4345_assembled_lemma1M t / t ^ 3 := by
            have hmiddle :
                x * (cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) / cdem4345_assembled_lemma1X x n ^ 2) =
                  (n : ℝ) * cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) := by
              rw [hXsq]
              field_simp [hx.ne', ne_of_gt hnpos]
              <;> ring
            rw [hmiddle]

/-! ## Exact finite hyperbola interchange -/

/-- The floor/square-root equivalence used to reindex the hyperbola lattice points.
All denominators are explicitly positive. -/
theorem cdem4345_assembled_lemma1_le_floor_X_iff
    {x : ℝ} {a k : ℕ} (hx : 0 ≤ x) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    a ≤ ⌊cdem4345_assembled_lemma1X x k⌋₊ ↔ k ≤ ⌊x / (a : ℝ) ^ 2⌋₊ := by
  have haR : (0 : ℝ) < a := by positivity
  have hkR : (0 : ℝ) < k := by positivity
  have hdiv0 : 0 ≤ x / (k : ℝ) := div_nonneg hx hkR.le
  unfold cdem4345_assembled_lemma1X
  rw [Nat.le_floor_iff (Real.sqrt_nonneg _),
    Nat.le_floor_iff (div_nonneg hx (sq_nonneg _))]
  rw [Real.le_sqrt (Nat.cast_nonneg a) hdiv0]
  rw [le_div_iff₀ hkR, le_div_iff₀ (sq_pos_of_pos haR)]
  constructor <;> intro h <;> nlinarith

/-- The finite hyperbola residual is a theorem under the exact nonempty-range guards. -/
theorem cdem4345_assembled_lemma1_hyperbolaTailInterchange
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    cdem4345_assembled_Lemma1HyperbolaTailInterchangeAt x n := by
  have hx0 : 0 ≤ x := hx.le
  have hnR : (0 : ℝ) < n := by positivity
  have hcommon : ∀ k ∈ Finset.Icc n ⌊x⌋₊,
      cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x k)
        = ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
            if a ≤ ⌊cdem4345_assembled_lemma1X x k⌋₊
            then (ArithmeticFunction.moebius a : ℝ) else 0 := by
    intro k hk
    have hk' : n ≤ k ∧ k ≤ ⌊x⌋₊ := Finset.mem_Icc.mp hk
    rw [cdem4345_assembled_lemma1M_eq_sum]
    have hkpos : 1 ≤ k := hn.trans hk'.1
    have hdiv : x / (k : ℝ) ≤ x / (n : ℝ) :=
      div_le_div_of_nonneg_left hx0 (by positivity) (by exact_mod_cast hk'.1)
    have hfloor : ⌊cdem4345_assembled_lemma1X x k⌋₊ ≤ ⌊cdem4345_assembled_lemma1X x n⌋₊ :=
      Nat.floor_mono (Real.sqrt_le_sqrt hdiv)
    have hfilter :
        (Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊).filter
            (fun a => a ≤ ⌊cdem4345_assembled_lemma1X x k⌋₊)
          = Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x k⌋₊ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← hfilter, Finset.sum_filter]
  rw [cdem4345_assembled_Lemma1HyperbolaTailInterchangeAt]
  calc
    (∑ k ∈ Finset.Icc n ⌊x⌋₊, cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x k))
        = ∑ k ∈ Finset.Icc n ⌊x⌋₊,
            ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
              if a ≤ ⌊cdem4345_assembled_lemma1X x k⌋₊
              then (ArithmeticFunction.moebius a : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hcommon k hk
    _ = ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
          ∑ k ∈ Finset.Icc n ⌊x⌋₊,
            if a ≤ ⌊cdem4345_assembled_lemma1X x k⌋₊
            then (ArithmeticFunction.moebius a : ℝ) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 ⌊cdem4345_assembled_lemma1X x n⌋₊,
          (ArithmeticFunction.moebius a : ℝ)
            * ((⌊x / (a : ℝ) ^ 2⌋₊ : ℝ) - (((n - 1 : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha' : 1 ≤ a ∧ a ≤ ⌊cdem4345_assembled_lemma1X x n⌋₊ := Finset.mem_Icc.mp ha
          have hna : n ≤ ⌊x / (a : ℝ) ^ 2⌋₊ :=
            (cdem4345_assembled_lemma1_le_floor_X_iff hx0 ha'.1 hn).mp ha'.2
          have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha'.1
          have ha_sq : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
            nlinarith [sq_nonneg ((a : ℝ) - 1)]
          have hquot : x / (a : ℝ) ^ 2 ≤ x :=
            div_le_self hx0 ha_sq
          have hax : ⌊x / (a : ℝ) ^ 2⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hquot
          have hfilter :
              (Finset.Icc n ⌊x⌋₊).filter
                  (fun k => k ≤ ⌊x / (a : ℝ) ^ 2⌋₊)
                = Finset.Icc n ⌊x / (a : ℝ) ^ 2⌋₊ := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Icc]
            omega
          have hinner :
              (∑ k ∈ Finset.Icc n ⌊x⌋₊,
                if a ≤ ⌊cdem4345_assembled_lemma1X x k⌋₊
                then (ArithmeticFunction.moebius a : ℝ) else 0)
                = ∑ k ∈ Finset.Icc n ⌊x⌋₊,
                    if k ≤ ⌊x / (a : ℝ) ^ 2⌋₊
                    then (ArithmeticFunction.moebius a : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : n ≤ k ∧ k ≤ ⌊x⌋₊ := Finset.mem_Icc.mp hk
            simpa only [cdem4345_assembled_lemma1_le_floor_X_iff hx0 ha'.1 (hn.trans hk'.1)]
          rw [hinner, ← Finset.sum_filter, hfilter, Finset.sum_const, Nat.card_Icc,
            nsmul_eq_mul]
          have hcast :
              ((((⌊x / (a : ℝ) ^ 2⌋₊ + 1 - n : ℕ)) : ℝ))
                = (⌊x / (a : ℝ) ^ 2⌋₊ : ℝ) - (((n - 1 : ℕ) : ℝ)) := by
            push_cast [Nat.cast_sub (by omega : n ≤ ⌊x / (a : ℝ) ^ 2⌋₊ + 1),
              Nat.cast_sub hn]
            ring
          rw [hcast]
          ring
    _ = cdem4345_assembled_lemma1FloorHead x n
          - (((n - 1 : ℕ) : ℝ)) * cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x n) := by
          unfold cdem4345_assembled_lemma1FloorHead
          rw [cdem4345_assembled_lemma1M_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring


/-- Exact square-root/floor compatibility, derived from their order laws. -/
lemma cdem4345_assembled_lemma1_nat_sqrt_floor (x : ℝ) (hx : 0 ≤ x) :
    (⌊x⌋₊).sqrt = ⌊Real.sqrt x⌋₊ := by
  apply Nat.le_antisymm
  · apply Nat.le_floor
    apply (Real.le_sqrt (Nat.cast_nonneg _) hx).2
    have hsq : (((⌊x⌋₊).sqrt : ℝ))^2 ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast Nat.sqrt_le' ⌊x⌋₊
    exact hsq.trans (Nat.floor_le hx)
  · apply Nat.le_sqrt'.2
    apply (Nat.le_floor_iff hx).2
    have hs := (Real.le_sqrt (Nat.cast_nonneg ⌊Real.sqrt x⌋₊) hx).1
      (Nat.floor_le (Real.sqrt_nonneg x))
    simpa only [Nat.cast_pow] using hs

/-- The squarefree/Mertens convolution, using the independently proved square-divisor identity. -/
theorem cdem4345_assembled_squarefreeCount_eq_sum_lemma1M {x : ℝ} (hx : 1 ≤ x) :
    cdem4345_assembled_squarefreeCount x = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x k) := by
  have hx0 : 0 ≤ x := by linarith
  have hnf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
  have htail := cdem4345_assembled_lemma1_hyperbolaTailInterchange (by linarith : 0 < x)
    (n := 1) (by norm_num) hnf
  rw [cdem4345_assembled_Lemma1HyperbolaTailInterchangeAt] at htail
  norm_num only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero] at htail
  rw [htail]
  have hcount := Helfgott.cdem4345_assembled_squarefree_coprime_count_exact 1 ⌊x⌋₊ (by norm_num)
  simp only [Nat.coprime_one_right_iff, if_true, Nat.divisors_one,
    Finset.sum_singleton, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    one_mul, Nat.mul_one] at hcount
  have heQ : cdem4345_assembled_squarefreeCount x =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius d : ℝ)^2 := by
    rw [cdem4345_assembled_squarefreeCount_eq_sum_Icc]
    apply Finset.sum_congr rfl
    intro d hd
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num
  rw [heQ, hcount, cdem4345_assembled_lemma1_nat_sqrt_floor x hx0]
  unfold cdem4345_assembled_lemma1FloorHead cdem4345_assembled_lemma1X
  simp only [Nat.cast_one, div_one]
  apply Finset.sum_congr rfl
  intro d hd
  have he : ⌊x/(d : ℝ)^2⌋₊ = ⌊x⌋₊/(d^2) := by
    rw [← Nat.cast_pow, Nat.floor_div_natCast]
  rw [he]

/-- CDEM (2.1) from the proved convolution and finite hyperbola interchange. -/
theorem cdem4345_assembled_lemma1_eq21_of_hyperbolaTail
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊)
    (htail : cdem4345_assembled_Lemma1HyperbolaTailInterchangeAt x n) :
    cdem4345_assembled_Lemma1Eq21At x n := by
  have hx1 : 1 ≤ x := by
    have hn1 : 1 ≤ ⌊x⌋₊ := hn.trans hnx
    have hf := Nat.floor_le hx.le
    have hnR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn1
    linarith
  rw [cdem4345_assembled_Lemma1HyperbolaTailInterchangeAt] at htail
  rw [cdem4345_assembled_Lemma1Eq21At, cdem4345_assembled_squarefreeCount_eq_sum_lemma1M hx1]
  have hsets : Finset.Icc 1 ⌊x⌋₊ = Finset.Icc 1 (n-1) ∪ Finset.Icc n ⌊x⌋₊ := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisjoint : Disjoint (Finset.Icc 1 (n-1)) (Finset.Icc n ⌊x⌋₊) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    have h1 := Finset.mem_Icc.mp hk1
    have h2 := Finset.mem_Icc.mp hk2
    omega
  rw [hsets, Finset.sum_union hdisjoint, htail]
  ring

/-- CDEM equation (2.1), now with no residual. -/
theorem cdem4345_assembled_lemma1_eq21
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    cdem4345_assembled_Lemma1Eq21At x n :=
  cdem4345_assembled_lemma1_eq21_of_hyperbolaTail hx hn hnx
    (cdem4345_assembled_lemma1_hyperbolaTailInterchange hx hn hnx)

/-- The exact CDEM decomposition, with the Abel and finite-reindex seams closed. -/
theorem cdem4345_assembled_lemma1_exactDecomposition
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    cdem4345_assembled_Lemma1ExactDecompositionAt x n :=
  cdem4345_assembled_lemma1_exactDecomposition_of_eq21_and_recipSq hx.le hn
    (cdem4345_assembled_lemma1_eq21 hx hn hnx)
    (cdem4345_assembled_lemma1_recipSqPartialSummation hx hn hnx)

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: monotonicity of the normalized `n=197` envelope

This file discharges the one unbounded scalar input left in the second squarefree
bootstrap.  After division by `sqrt x`, the two factors under the Cauchy--Schwarz
square root are

```text
q(x) = 6/(pi^2 sqrt 197)
       + (0.036438/sqrt(sqrt 197)) x^(-1/4),

s(x) = 1/(18 sqrt 196.98)
       + 12^(1/3)/6 x^(-1/6) - 131 x^(-1/2).
```

The first is decreasing.  For the second,

```text
s'(x) = x^(-3/2)
  * (131/2 - (12^(1/3)/36) x^(1/3)),
```

which is negative already when `x^(1/3) >= 10000`; the live interval begins at
`1.6*10^15`.  Thus no endpoint sampling is used to justify an unbounded
monotonicity assertion.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Set

/-- The normalized squarefree-count factor, written as a sum of powers. -/
private noncomputable def cdem4345_assembled_lemma1N197QRatioModel (x : ℝ) : ℝ :=
  6 / (Real.pi ^ 2 * Real.sqrt cdem4345_assembled_lemma1FinalN)
    + (cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN))
        * x ^ (-(1 : ℝ) / 4)

/-- The normalized periodic-square-mass factor, written as a sum of powers. -/
private noncomputable def cdem4345_assembled_lemma1N197SRatioModel (x : ℝ) : ℝ :=
  1 / (18 * Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100))
    + 12 ^ ((1 : ℝ) / 3) / 6 * x ^ (-(1 : ℝ) / 6)
    - (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)
        * x ^ (-(1 : ℝ) / 2)

lemma cdem4345_assembled_sqrt_sqrt_div_sqrt_eq_rpow_neg_quarter
    {x : ℝ} (hx : 0 < x) :
    Real.sqrt (Real.sqrt x) / Real.sqrt x = x ^ (-(1 : ℝ) / 4) := by
  have hx0 : 0 ≤ x := hx.le
  calc
    Real.sqrt (Real.sqrt x) / Real.sqrt x
        = (x ^ ((1 : ℝ) / 2)) ^ ((1 : ℝ) / 2)
            / x ^ ((1 : ℝ) / 2) := by
              rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ = x ^ ((1 : ℝ) / 4) / x ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_mul hx0]
          norm_num
    _ = x ^ (-(1 : ℝ) / 4) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hx0, ← Real.rpow_add hx]
          norm_num

lemma cdem4345_assembled_cuberoot_mul_div_sqrt_eq
    {x : ℝ} (hx : 0 < x) :
    (12 * x) ^ ((1 : ℝ) / 3) / Real.sqrt x =
      12 ^ ((1 : ℝ) / 3) * x ^ (-(1 : ℝ) / 6) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 12) hx.le,
    Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hx.le, mul_assoc,
    ← Real.rpow_add hx]
  norm_num

private lemma cdem4345_assembled_lemma1N197QRatio_eq_model {x : ℝ} (hx : 0 < x) :
    cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt x =
      cdem4345_assembled_lemma1N197QRatioModel x := by
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  unfold cdem4345_assembled_lemma1QFactor cdem4345_assembled_lemma1N197QRatioModel
  rw [add_div]
  apply congrArg₂ (fun u v : ℝ => u + v)
  · field_simp [hsx]
  · calc
      cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt (Real.sqrt x) /
              Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) / Real.sqrt x
          = cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN)
              * (Real.sqrt (Real.sqrt x) / Real.sqrt x) := by ring
      _ = cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN)
              * x ^ (-(1 : ℝ) / 4) := by
            rw [cdem4345_assembled_sqrt_sqrt_div_sqrt_eq_rpow_neg_quarter hx]

private lemma cdem4345_assembled_lemma1N197SRatio_eq_model {x : ℝ} (hx : 0 < x) :
    cdem4345_assembled_lemma1SFactor x cdem4345_assembled_lemma1FinalN / Real.sqrt x =
      cdem4345_assembled_lemma1N197SRatioModel x := by
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hneg :
      ((2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)) / Real.sqrt x =
        (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)
          * x ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hx.le]
    congr 2
    ring
  unfold cdem4345_assembled_lemma1SFactor cdem4345_assembled_lemma1N197SRatioModel
  rw [sub_div, add_div, hneg]
  apply congrArg₂ (fun u v : ℝ => u - v)
  · apply congrArg₂ (fun u v : ℝ => u + v)
    · field_simp [hsx]
    · calc
        (12 * x) ^ ((1 : ℝ) / 3) / 6 / Real.sqrt x
            = ((12 * x) ^ ((1 : ℝ) / 3) / Real.sqrt x) / 6 := by ring
        _ = 12 ^ ((1 : ℝ) / 3) * x ^ (-(1 : ℝ) / 6) / 6 := by
          rw [cdem4345_assembled_cuberoot_mul_div_sqrt_eq hx]
        _ = 12 ^ ((1 : ℝ) / 3) / 6 * x ^ (-(1 : ℝ) / 6) := by ring
  · rfl

private lemma cdem4345_assembled_lemma1N197QRatioModel_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt cdem4345_assembled_lemma1N197QRatioModel
      ((cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN))
        * ((-(1 : ℝ) / 4) * x ^ (-(1 : ℝ) / 4 - 1))) x := by
  unfold cdem4345_assembled_lemma1N197QRatioModel
  exact ((Real.hasDerivAt_rpow_const
      (p := (-(1 : ℝ) / 4)) (Or.inl hx.ne')).const_mul
        (cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN))).const_add
      (6 / (Real.pi ^ 2 * Real.sqrt cdem4345_assembled_lemma1FinalN))

private lemma cdem4345_assembled_lemma1N197SRatioModel_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt cdem4345_assembled_lemma1N197SRatioModel
      (12 ^ ((1 : ℝ) / 3) / 6
          * ((-(1 : ℝ) / 6) * x ^ (-(1 : ℝ) / 6 - 1))
        - (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)
          * ((-(1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2 - 1))) x := by
  unfold cdem4345_assembled_lemma1N197SRatioModel
  exact (((Real.hasDerivAt_rpow_const
      (p := (-(1 : ℝ) / 6)) (Or.inl hx.ne')).const_mul
        (12 ^ ((1 : ℝ) / 3) / 6)).const_add
          (1 / (18 * Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100)))).sub
      ((Real.hasDerivAt_rpow_const
        (p := (-(1 : ℝ) / 2)) (Or.inl hx.ne')).const_mul
          ((2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)))

lemma cdem4345_assembled_ten_thousand_le_cuberoot {x : ℝ}
    (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    (10000 : ℝ) ≤ x ^ ((1 : ℝ) / 3) := by
  have hx0 : 0 ≤ x :=
    le_trans (by norm_num [cdem4345_assembled_lemma1FinalX0] : (0 : ℝ) ≤ cdem4345_assembled_lemma1FinalX0) hx
  have hcube : (10000 : ℝ) ^ (3 : ℕ) ≤ x := by
    norm_num [cdem4345_assembled_lemma1FinalX0] at hx ⊢
    linarith
  have hpow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (10000 : ℝ) ^ (3 : ℕ))
    hcube (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
  calc
    (10000 : ℝ) = ((10000 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (10000 : ℝ) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10000)]
      norm_num
    _ ≤ x ^ ((1 : ℝ) / 3) := hpow

private lemma cdem4345_assembled_lemma1N197QRatioModel_deriv_nonpos
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 < x) :
    deriv cdem4345_assembled_lemma1N197QRatioModel x ≤ 0 := by
  have hx0 : 0 < x := lt_trans (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  rw [(cdem4345_assembled_lemma1N197QRatioModel_hasDerivAt hx0).deriv]
  have hb : 0 ≤ cdem4345_assembled_lemma1PreviousSquarefreeB := by
    norm_num [cdem4345_assembled_lemma1PreviousSquarefreeB]
  have hden : 0 < Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) := by
    norm_num [cdem4345_assembled_lemma1FinalN]
  have hpow : 0 ≤ x ^ (-(1 : ℝ) / 4 - 1) := Real.rpow_nonneg hx0.le _
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hb hden.le) (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hpow)

private lemma cdem4345_assembled_lemma1N197SRatioModel_deriv_nonpos
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 < x) :
    deriv cdem4345_assembled_lemma1N197SRatioModel x ≤ 0 := by
  have hx0 : 0 < x := lt_trans (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  rw [(cdem4345_assembled_lemma1N197SRatioModel_hasDerivAt hx0).deriv]
  have h12 : (1 : ℝ) ≤ 12 ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have hx13 : (10000 : ℝ) ≤ x ^ ((1 : ℝ) / 3) :=
    cdem4345_assembled_ten_thousand_le_cuberoot hx.le
  have hprod : (10000 : ℝ) ≤
      12 ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr h12) (sub_nonneg.mpr hx13)]
  have hpow_split :
      x ^ (-(1 : ℝ) / 6 - 1) =
        x ^ (-(1 : ℝ) / 2 - 1) * x ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hpow : 0 ≤ x ^ (-(1 : ℝ) / 2 - 1) := Real.rpow_nonneg hx0.le _
  rw [hpow_split]
  have hbracket :
      (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2) / 2
        - (12 ^ ((1 : ℝ) / 3) / 36) * x ^ ((1 : ℝ) / 3) ≤ 0 := by
    norm_num [cdem4345_assembled_lemma1FinalN]
    nlinarith
  have heq :
      12 ^ ((1 : ℝ) / 3) / 6
            * ((-(1 : ℝ) / 6) *
              (x ^ (-(1 : ℝ) / 2 - 1) * x ^ ((1 : ℝ) / 3)))
          - (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)
            * ((-(1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2 - 1))
        = x ^ (-(1 : ℝ) / 2 - 1) *
            ((2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2) / 2
              - (12 ^ ((1 : ℝ) / 3) / 36) * x ^ ((1 : ℝ) / 3)) := by
    ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hpow hbracket

private theorem cdem4345_assembled_lemma1N197QRatioModel_antitone :
    AntitoneOn cdem4345_assembled_lemma1N197QRatioModel (Set.Ici cdem4345_assembled_lemma1FinalX0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici cdem4345_assembled_lemma1FinalX0) ?_ ?_ ?_
  · intro x hx
    exact (cdem4345_assembled_lemma1N197QRatioModel_hasDerivAt
      (lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    exact (cdem4345_assembled_lemma1N197QRatioModel_hasDerivAt
      (lt_trans (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    exact cdem4345_assembled_lemma1N197QRatioModel_deriv_nonpos hx

private theorem cdem4345_assembled_lemma1N197SRatioModel_antitone :
    AntitoneOn cdem4345_assembled_lemma1N197SRatioModel (Set.Ici cdem4345_assembled_lemma1FinalX0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici cdem4345_assembled_lemma1FinalX0) ?_ ?_ ?_
  · intro x hx
    exact (cdem4345_assembled_lemma1N197SRatioModel_hasDerivAt
      (lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    exact (cdem4345_assembled_lemma1N197SRatioModel_hasDerivAt
      (lt_trans (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    exact cdem4345_assembled_lemma1N197SRatioModel_deriv_nonpos hx

private lemma cdem4345_assembled_lemma1N197QRatio_nonneg {x : ℝ}
    (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    0 ≤ cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  rw [cdem4345_assembled_lemma1N197QRatio_eq_model hx0]
  unfold cdem4345_assembled_lemma1N197QRatioModel
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb : 0 ≤ cdem4345_assembled_lemma1PreviousSquarefreeB := by
    norm_num [cdem4345_assembled_lemma1PreviousSquarefreeB]
  positivity

lemma cdem4345_assembled_lemma1N197SRatio_nonneg {x : ℝ}
    (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    0 ≤ cdem4345_assembled_lemma1SFactor x cdem4345_assembled_lemma1FinalN / Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  rw [cdem4345_assembled_lemma1N197SRatio_eq_model hx0]
  unfold cdem4345_assembled_lemma1N197SRatioModel
  have hsqrt_n : Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100) ≤ 15 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num [cdem4345_assembled_lemma1FinalN]
  have hsqrt_n_pos : 0 < Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100) := by
    apply Real.sqrt_pos.2
    norm_num [cdem4345_assembled_lemma1FinalN]
  have hconstant :
      (1 / 270 : ℝ) ≤
        1 / (18 * Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsqrt_x : (10000000 : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).2
    norm_num [cdem4345_assembled_lemma1FinalX0] at hx ⊢
    nlinarith
  have hsqrt_x_pos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hnegpow : x ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt x := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hrecip : 1 / Real.sqrt x ≤ (1 / 10000000 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hsqrt_x
  have hnegative :
      (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2)
          * x ^ (-(1 : ℝ) / 2) ≤ 1 / 270 := by
    rw [hnegpow]
    have hmul := mul_le_mul_of_nonneg_left hrecip
      (show 0 ≤ (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2) by
        norm_num [cdem4345_assembled_lemma1FinalN])
    norm_num [cdem4345_assembled_lemma1FinalN] at hmul ⊢
    linarith
  have hpositive :
      0 ≤ 12 ^ ((1 : ℝ) / 3) / 6 * x ^ (-(1 : ℝ) / 6) := by positivity
  linarith

lemma cdem4345_assembled_lemma1N197NormalizedT3_eq {x : ℝ}
    (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    cdem4345_assembled_lemma1T3Envelope x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt x =
      Real.sqrt
        ((cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt x)
          * (cdem4345_assembled_lemma1SFactor x cdem4345_assembled_lemma1FinalN / Real.sqrt x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
  have hqratio := cdem4345_assembled_lemma1N197QRatio_nonneg hx
  have hsratio := cdem4345_assembled_lemma1N197SRatio_nonneg hx
  have hq : 0 ≤ cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB := by
    have := mul_nonneg hqratio (Real.sqrt_nonneg x)
    rwa [div_mul_cancel₀ _ hsx] at this
  unfold cdem4345_assembled_lemma1T3Envelope
  rw [← Real.sqrt_div (mul_nonneg hq
    (by
      have := mul_nonneg hsratio (Real.sqrt_nonneg x)
      rwa [div_mul_cancel₀ _ hsx] at this))]
  congr 1
  field_simp [hsx]
  rw [Real.sq_sqrt hx0.le]

/-- The normalized combined `n=197` envelope is antitone on the complete live
large-`x` interval. -/
theorem cdem4345_assembled_lemma1N197EnvelopeAntitone_proven : cdem4345_assembled_Lemma1N197EnvelopeAntitone := by
  rw [cdem4345_assembled_Lemma1N197EnvelopeAntitone]
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hy
  have hq :
      cdem4345_assembled_lemma1QFactor y cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt y ≤
        cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt x := by
    rw [cdem4345_assembled_lemma1N197QRatio_eq_model hy0, cdem4345_assembled_lemma1N197QRatio_eq_model hx0]
    exact cdem4345_assembled_lemma1N197QRatioModel_antitone hx hy hxy
  have hs :
      cdem4345_assembled_lemma1SFactor y cdem4345_assembled_lemma1FinalN / Real.sqrt y ≤
        cdem4345_assembled_lemma1SFactor x cdem4345_assembled_lemma1FinalN / Real.sqrt x := by
    rw [cdem4345_assembled_lemma1N197SRatio_eq_model hy0, cdem4345_assembled_lemma1N197SRatio_eq_model hx0]
    exact cdem4345_assembled_lemma1N197SRatioModel_antitone hx hy hxy
  have hsy := cdem4345_assembled_lemma1N197SRatio_nonneg hy
  have hqx := cdem4345_assembled_lemma1N197QRatio_nonneg hx
  have hprod :
      (cdem4345_assembled_lemma1QFactor y cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt y)
          * (cdem4345_assembled_lemma1SFactor y cdem4345_assembled_lemma1FinalN / Real.sqrt y) ≤
        (cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB / Real.sqrt x)
          * (cdem4345_assembled_lemma1SFactor x cdem4345_assembled_lemma1FinalN / Real.sqrt x) :=
    mul_le_mul hq hs hsy hqx
  change cdem4345_assembled_lemma1N197CombinedEnvelope y / Real.sqrt y ≤
    cdem4345_assembled_lemma1N197CombinedEnvelope x / Real.sqrt x
  unfold cdem4345_assembled_lemma1N197CombinedEnvelope
  rw [add_div, add_div, mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hx0).ne',
    mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hy0).ne',
    cdem4345_assembled_lemma1N197NormalizedT3_eq hx, cdem4345_assembled_lemma1N197NormalizedT3_eq hy]
  gcongr

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: the exact `n=197` endpoint inequality

The paper prints the two rounded values `0.012845` and `0.01479`.  Neither is a
valid upper bound for its corresponding exact expression.  This file instead proves
the combined endpoint with the safe folds

```text
(T1+T2)/sqrt(x0) <= 0.012846,
T3/sqrt(x0)       <= 0.014824,
```

whose sum is exactly `0.02767`.  The proof uses only rational enclosures whose
correct directions are checked by squaring or cubing.  In particular the full
combined target is no longer treated as an opaque numerical certificate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

private lemma cdem4345_assembled_sqrt_finalX0 : Real.sqrt cdem4345_assembled_lemma1FinalX0 = 40000000 := by
  have hsq := Real.sq_sqrt
    (show 0 ≤ cdem4345_assembled_lemma1FinalX0 by norm_num [cdem4345_assembled_lemma1FinalX0])
  have hs0 := Real.sqrt_nonneg cdem4345_assembled_lemma1FinalX0
  norm_num [cdem4345_assembled_lemma1FinalX0] at hsq ⊢

private lemma cdem4345_assembled_sqrt_finalN_lower :
    (14035668 / 1000000 : ℝ) ≤ Real.sqrt cdem4345_assembled_lemma1FinalN := by
  apply (Real.le_sqrt (by norm_num) (by positivity : (0 : ℝ) ≤ cdem4345_assembled_lemma1FinalN)).2
  norm_num [cdem4345_assembled_lemma1FinalN]

private lemma cdem4345_assembled_sqrt_finalN_upper :
    Real.sqrt cdem4345_assembled_lemma1FinalN ≤ (14035669 / 1000000 : ℝ) := by
  apply (Real.sqrt_le_iff).2
  constructor <;> norm_num [cdem4345_assembled_lemma1FinalN]

private lemma cdem4345_assembled_sqrt_sqrt_finalN_lower :
    (3746420 / 1000000 : ℝ) ≤ Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) := by
  apply (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg cdem4345_assembled_lemma1FinalN)).2
  exact (by norm_num : (3746420 / 1000000 : ℝ) ^ 2 ≤
      14035668 / 1000000).trans cdem4345_assembled_sqrt_finalN_lower

private lemma cdem4345_assembled_sqrt_finalN_sub_lower :
    (14034956 / 1000000 : ℝ) ≤
      Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100) := by
  apply (Real.le_sqrt (by norm_num) (by norm_num [cdem4345_assembled_lemma1FinalN])).2
  norm_num [cdem4345_assembled_lemma1FinalN]

private lemma cdem4345_assembled_sqrt_sqrt_finalX0_upper :
    Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalX0) ≤ (6324556 / 1000 : ℝ) := by
  rw [cdem4345_assembled_sqrt_finalX0]
  apply (Real.sqrt_le_iff).2
  constructor <;> norm_num

private lemma cdem4345_assembled_cuberoot_final_upper :
    (12 * cdem4345_assembled_lemma1FinalX0) ^ ((1 : ℝ) / 3) ≤ (267773181 / 1000 : ℝ) := by
  let z : ℝ := (12 * cdem4345_assembled_lemma1FinalX0) ^ ((1 : ℝ) / 3)
  let c : ℝ := 267773181 / 1000
  have hz0 : 0 ≤ z := Real.rpow_nonneg (by norm_num [cdem4345_assembled_lemma1FinalX0]) _
  have hc0 : 0 ≤ c := by norm_num [c]
  have hz3 : z ^ (3 : ℕ) = 12 * cdem4345_assembled_lemma1FinalX0 := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num [cdem4345_assembled_lemma1FinalX0])]
    norm_num
  have hcube : z ^ (3 : ℕ) ≤ c ^ (3 : ℕ) := by
    rw [hz3]
    norm_num [c, cdem4345_assembled_lemma1FinalX0]
  by_contra hzc
  have hcz : c < z := lt_of_not_ge hzc
  have hsum : 0 < z ^ 2 + z * c + c ^ 2 := by positivity
  have hzcpos : 0 < z - c := sub_pos.2 hcz
  have hdiff : 0 < z ^ 3 - c ^ 3 := by
    have hmul := mul_pos hzcpos hsum
    nlinarith
  nlinarith

private lemma cdem4345_assembled_lemma1N197T12_endpoint_ratio_le :
    cdem4345_assembled_lemma1PreviousMertensEpsilon
        * (4 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100)
      ≤ (12846 / 1000000 : ℝ) := by
  have hlinear :
      4 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100 ≤
        4 * (14035669 / 1000000 : ℝ) - 146 / 100 := by
    nlinarith [cdem4345_assembled_sqrt_finalN_upper]
  have hmul := mul_le_mul_of_nonneg_left hlinear
    (show 0 ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon by
      norm_num [cdem4345_assembled_lemma1PreviousMertensEpsilon])
  calc
    cdem4345_assembled_lemma1PreviousMertensEpsilon
          * (4 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100)
        ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon
          * (4 * (14035669 / 1000000 : ℝ) - 146 / 100) := hmul
    _ ≤ (12846 / 1000000 : ℝ) := by
      norm_num [cdem4345_assembled_lemma1PreviousMertensEpsilon]

private lemma cdem4345_assembled_lemma1N197Q_endpoint_ratio_le :
    cdem4345_assembled_lemma1QFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB /
        Real.sqrt cdem4345_assembled_lemma1FinalX0 ≤ (43315 / 1000000 : ℝ) := by
  have hpi : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
    calc
      (3141592 / 1000000 : ℝ) = (3.141592 : ℝ) := by norm_num
      _ ≤ Real.pi := Real.pi_gt_d6.le
  have hpi0 : (0 : ℝ) < 3141592 / 1000000 := by norm_num
  have hpi_sq : (3141592 / 1000000 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ hpi0.le hpi 2
  have hden1 :
      (3141592 / 1000000 : ℝ) ^ 2 * (14035668 / 1000000) ≤
        Real.pi ^ 2 * Real.sqrt cdem4345_assembled_lemma1FinalN :=
    mul_le_mul hpi_sq cdem4345_assembled_sqrt_finalN_lower (by norm_num) (by positivity)
  have hmain :
      6 / (Real.pi ^ 2 * Real.sqrt cdem4345_assembled_lemma1FinalN) ≤
        6 / ((3141592 / 1000000 : ℝ) ^ 2 * (14035668 / 1000000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden1
  have hnum2 :
      cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalX0) ≤
        cdem4345_assembled_lemma1PreviousSquarefreeB * (6324556 / 1000 : ℝ) :=
    mul_le_mul_of_nonneg_left cdem4345_assembled_sqrt_sqrt_finalX0_upper
      (by norm_num [cdem4345_assembled_lemma1PreviousSquarefreeB])
  have hden2 :
      (3746420 / 1000000 : ℝ) * 40000000 ≤
        Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) * Real.sqrt cdem4345_assembled_lemma1FinalX0 := by
    rw [cdem4345_assembled_sqrt_finalX0]
    exact mul_le_mul_of_nonneg_right cdem4345_assembled_sqrt_sqrt_finalN_lower (by norm_num)
  have hfrac2 :
      cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalX0) /
          (Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) * Real.sqrt cdem4345_assembled_lemma1FinalX0) ≤
        (cdem4345_assembled_lemma1PreviousSquarefreeB * (6324556 / 1000 : ℝ)) /
          ((3746420 / 1000000 : ℝ) * 40000000) := by
    calc
      cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalX0) /
            (Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) * Real.sqrt cdem4345_assembled_lemma1FinalX0)
          ≤ (cdem4345_assembled_lemma1PreviousSquarefreeB * (6324556 / 1000 : ℝ)) /
            (Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) * Real.sqrt cdem4345_assembled_lemma1FinalX0) :=
        div_le_div_of_nonneg_right hnum2 (by positivity)
      _ ≤ (cdem4345_assembled_lemma1PreviousSquarefreeB * (6324556 / 1000 : ℝ)) /
            ((3746420 / 1000000 : ℝ) * 40000000) :=
        div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num [cdem4345_assembled_lemma1PreviousSquarefreeB]) (by norm_num))
          (by norm_num) hden2
  have hsx : Real.sqrt cdem4345_assembled_lemma1FinalX0 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num [cdem4345_assembled_lemma1FinalX0])).ne'
  have hratio :
      cdem4345_assembled_lemma1QFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB /
          Real.sqrt cdem4345_assembled_lemma1FinalX0 =
        6 / (Real.pi ^ 2 * Real.sqrt cdem4345_assembled_lemma1FinalN)
          + cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalX0) /
            (Real.sqrt (Real.sqrt cdem4345_assembled_lemma1FinalN) * Real.sqrt cdem4345_assembled_lemma1FinalX0) := by
    unfold cdem4345_assembled_lemma1QFactor
    field_simp [hsx]
  rw [hratio]
  have hfold :
      6 / ((3141592 / 1000000 : ℝ) ^ 2 * (14035668 / 1000000))
          + (cdem4345_assembled_lemma1PreviousSquarefreeB * (6324556 / 1000 : ℝ)) /
            ((3746420 / 1000000 : ℝ) * 40000000)
        ≤ (43315 / 1000000 : ℝ) := by
    norm_num [cdem4345_assembled_lemma1PreviousSquarefreeB]
  linarith

private lemma cdem4345_assembled_lemma1N197S_endpoint_ratio_le :
    cdem4345_assembled_lemma1SFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN / Real.sqrt cdem4345_assembled_lemma1FinalX0
      ≤ (5071 / 1000000 : ℝ) := by
  have hfirst :
      1 / (18 * Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100)) ≤
        1 / (18 * (14034956 / 1000000 : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left cdem4345_assembled_sqrt_finalN_sub_lower (by norm_num)
  have hcuberoot :
      (12 * cdem4345_assembled_lemma1FinalX0) ^ ((1 : ℝ) / 3) / (6 * 40000000) ≤
        (267773181 / 1000 : ℝ) / (6 * 40000000) :=
    div_le_div_of_nonneg_right cdem4345_assembled_cuberoot_final_upper (by norm_num)
  have hsx : Real.sqrt cdem4345_assembled_lemma1FinalX0 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num [cdem4345_assembled_lemma1FinalX0])).ne'
  have hratio :
      cdem4345_assembled_lemma1SFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN / Real.sqrt cdem4345_assembled_lemma1FinalX0 =
        1 / (18 * Real.sqrt ((cdem4345_assembled_lemma1FinalN : ℝ) - 2 / 100))
          + (12 * cdem4345_assembled_lemma1FinalX0) ^ ((1 : ℝ) / 3) /
            (6 * Real.sqrt cdem4345_assembled_lemma1FinalX0)
          - (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2) /
            Real.sqrt cdem4345_assembled_lemma1FinalX0 := by
    unfold cdem4345_assembled_lemma1SFactor
    field_simp [hsx]
  rw [hratio, cdem4345_assembled_sqrt_finalX0]
  have hfold :
      1 / (18 * (14034956 / 1000000 : ℝ))
          + (267773181 / 1000 : ℝ) / (6 * 40000000)
          - (2 / 3 : ℝ) * ((cdem4345_assembled_lemma1FinalN : ℝ) - 1 / 2) / 40000000
        ≤ (5071 / 1000000 : ℝ) := by
    norm_num [cdem4345_assembled_lemma1FinalN]
  linarith

private lemma cdem4345_assembled_lemma1N197T3_endpoint_ratio_le :
    cdem4345_assembled_lemma1T3Envelope cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB /
        Real.sqrt cdem4345_assembled_lemma1FinalX0 ≤ (14824 / 1000000 : ℝ) := by
  rw [cdem4345_assembled_lemma1N197NormalizedT3_eq (by simp [cdem4345_assembled_lemma1FinalX0])]
  have hq0 : 0 ≤
      cdem4345_assembled_lemma1QFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB /
        Real.sqrt cdem4345_assembled_lemma1FinalX0 := by
    unfold cdem4345_assembled_lemma1QFactor
    apply div_nonneg
    · apply add_nonneg
      · positivity
      · exact div_nonneg
          (mul_nonneg (by norm_num [cdem4345_assembled_lemma1PreviousSquarefreeB]) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)
    · exact Real.sqrt_nonneg _
  have hs0 : 0 ≤
      cdem4345_assembled_lemma1SFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN / Real.sqrt cdem4345_assembled_lemma1FinalX0 := by
    have := cdem4345_assembled_lemma1N197SRatio_nonneg
      (show cdem4345_assembled_lemma1FinalX0 ≤ cdem4345_assembled_lemma1FinalX0 from le_rfl)
    exact this
  calc
    Real.sqrt
        ((cdem4345_assembled_lemma1QFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB /
              Real.sqrt cdem4345_assembled_lemma1FinalX0)
          * (cdem4345_assembled_lemma1SFactor cdem4345_assembled_lemma1FinalX0 cdem4345_assembled_lemma1FinalN / Real.sqrt cdem4345_assembled_lemma1FinalX0))
      ≤ Real.sqrt ((43315 / 1000000 : ℝ) * (5071 / 1000000)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul cdem4345_assembled_lemma1N197Q_endpoint_ratio_le
          cdem4345_assembled_lemma1N197S_endpoint_ratio_le hs0 (by norm_num)
    _ ≤ (14824 / 1000000 : ℝ) := by
      apply (Real.sqrt_le_iff).2
      constructor <;> norm_num

/-- The combined endpoint inequality, proved with directed rational enclosures. -/
theorem cdem4345_assembled_lemma1N197EndpointCertificate_proven : cdem4345_assembled_Lemma1N197EndpointCertificate := by
  rw [cdem4345_assembled_Lemma1N197EndpointCertificate]
  have hsx : 0 < Real.sqrt cdem4345_assembled_lemma1FinalX0 :=
    Real.sqrt_pos.2 (by norm_num [cdem4345_assembled_lemma1FinalX0])
  rw [← (div_le_iff₀ hsx)]
  unfold cdem4345_assembled_lemma1N197CombinedEnvelope
  rw [add_div, mul_div_cancel_right₀ _ hsx.ne']
  have hsum := add_le_add cdem4345_assembled_lemma1N197T12_endpoint_ratio_le
    cdem4345_assembled_lemma1N197T3_endpoint_ratio_le
  norm_num [cdem4345_assembled_lemma1FinalB] at hsum ⊢
  exact hsum

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The elementary reciprocal-square kernel is adapted from AppendixCTailAbel.lean,
commit 27df23af6a712895f22204d0d81102baa74f0ebe. No zeta-zero module is imported.
-/
set_option autoImplicit false
set_option Elab.async false
open MeasureTheory Set Filter Topology
namespace MathExtras.Helfgott.AppendixC

private theorem cdem4345_assembled_cdem_hasDerivAt_neg_inv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => -u⁻¹) (1/t^2) t := by
  have h := (hasDerivAt_inv ht.ne').neg
  refine h.congr_deriv ?_
  rw [one_div, neg_neg]

private theorem cdem4345_assembled_cdem_tendsto_neg_inv :
    Tendsto (fun u : ℝ => -u⁻¹) atTop (𝓝 0) := by
  simpa using (tendsto_inv_atTop_zero : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0)).neg

theorem cdem4345_assembled_integrableOn_one_div_sq_Ioi {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => 1/t^2) (Ioi T) :=
  integrableOn_Ioi_deriv_of_nonneg
    ((cdem4345_assembled_cdem_hasDerivAt_neg_inv hT).continuousAt.continuousWithinAt)
    (fun x hx => cdem4345_assembled_cdem_hasDerivAt_neg_inv (hT.trans hx))
    (fun x hx => by positivity) cdem4345_assembled_cdem_tendsto_neg_inv

theorem cdem4345_assembled_integral_one_div_sq_Ioi {T : ℝ} (hT : 0 < T) :
    ∫ t in Ioi T, 1/t^2 = 1/T := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    ((cdem4345_assembled_cdem_hasDerivAt_neg_inv hT).continuousAt.continuousWithinAt)
    (fun x hx => cdem4345_assembled_cdem_hasDerivAt_neg_inv (hT.trans hx))
    (fun x hx => by positivity) cdem4345_assembled_cdem_tendsto_neg_inv
  rw [h, zero_sub, neg_neg, one_div]

end MathExtras.Helfgott.AppendixC
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# CDEM Lemma 1: honest `n=197` analytic assembly

All structural analytic work is now proved.  This file identifies the remaining inputs
without postulating them:

* the previous Mertens bootstrap (`1/4257`, above `2159561`);
* the previous squarefree bootstrap (`0.036438`, above `82005`);
* the fixed `n=197` T2-weight certificate;
* the bounded natural-number window through `1.6*10^15`.

Each is a named `Prop` consumed as a theorem parameter.  None is an axiom, a disguised
copy of the unbounded target, or a vacuous live-range assumption.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset MeasureTheory Set
open scoped BigOperators

def cdem4345_assembled_lemma1PreviousMertensThreshold : ℝ := 2159561
def cdem4345_assembled_lemma1PreviousSquarefreeThreshold : ℝ := 82005

/-- The already-established preceding Mertens bootstrap used by Theorem 3 bis. -/
def cdem4345_assembled_Lemma1PreviousMertensBootstrap : Prop :=
  ∀ t : ℝ, cdem4345_assembled_lemma1PreviousMertensThreshold < t →
    |cdem4345_assembled_lemma1M t| ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon * t

/-- The preceding squarefree remainder bootstrap (Theorem 3) used in `Q(X_n)`. -/
def cdem4345_assembled_Lemma1PreviousSquarefreeBootstrap : Prop :=
  ∀ t : ℝ, cdem4345_assembled_lemma1PreviousSquarefreeThreshold < t →
    |cdem4345_assembled_lemma1Remainder t| ≤ cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt t

/-- Audited ledger of the only inputs left after analytic assembly. -/
structure Lemma1N197RemainingInputs : Prop where
  previousMertens : cdem4345_assembled_Lemma1PreviousMertensBootstrap
  previousSquarefree : cdem4345_assembled_Lemma1PreviousSquarefreeBootstrap
  t2Weight : cdem4345_assembled_Lemma1N197T2WeightCertificate
  boundedWindow : cdem4345_assembled_Theorem3BisFiniteWindowCertificate

theorem cdem4345_assembled_lemma1X_finalN_gt_previousMertens
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    cdem4345_assembled_lemma1PreviousMertensThreshold < cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN := by
  rw [cdem4345_assembled_lemma1PreviousMertensThreshold, cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1FinalN]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2159561)).2
  rw [div_eq_mul_inv]
  norm_num [cdem4345_assembled_lemma1FinalX0] at hx ⊢
  nlinarith

theorem cdem4345_assembled_lemma1X_antitone_index
    {x : ℝ} {j n : ℕ} (hx : 0 ≤ x) (hj : 1 ≤ j) (hjn : j ≤ n) :
    cdem4345_assembled_lemma1X x n ≤ cdem4345_assembled_lemma1X x j := by
  rw [cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1X]
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left hx (by positivity) (by exact_mod_cast hjn)

theorem cdem4345_assembled_lemma1_previousMertens_pointwise_n197
    (hM : cdem4345_assembled_Lemma1PreviousMertensBootstrap)
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    ∀ j ∈ Finset.Icc 1 cdem4345_assembled_lemma1FinalN,
      |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|
        ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon * Real.sqrt x / Real.sqrt j := by
  rw [cdem4345_assembled_Lemma1PreviousMertensBootstrap] at hM
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hXj : cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN ≤ cdem4345_assembled_lemma1X x j :=
    cdem4345_assembled_lemma1X_antitone_index hx0.le hj'.1 hj'.2
  have hthreshold : cdem4345_assembled_lemma1PreviousMertensThreshold < cdem4345_assembled_lemma1X x j :=
    (cdem4345_assembled_lemma1X_finalN_gt_previousMertens hx).trans_le hXj
  have h := hM (cdem4345_assembled_lemma1X x j) hthreshold
  simpa [cdem4345_assembled_lemma1X, Real.sqrt_div hx0.le, mul_div_assoc] using h

/-- The previous Mertens bootstrap also gives the improper T1 comparison. -/
theorem cdem4345_assembled_lemma1_previousMertens_tail_integral
    (hM : cdem4345_assembled_Lemma1PreviousMertensBootstrap)
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    (∫ t in Set.Ioi (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN), |cdem4345_assembled_lemma1M t| / t ^ 3)
      ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon / cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN := by
  rw [cdem4345_assembled_Lemma1PreviousMertensBootstrap] at hM
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hA : 0 < cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN :=
    cdem4345_assembled_lemma1X_pos hx0 (by norm_num [cdem4345_assembled_lemma1FinalN])
  have hmajor : IntegrableOn
      (fun t : ℝ => cdem4345_assembled_lemma1PreviousMertensEpsilon * (1 / t ^ 2))
      (Set.Ioi (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN)) :=
    (MathExtras.Helfgott.AppendixC.cdem4345_assembled_integrableOn_one_div_sq_Ioi hA).const_mul _
  have hminor : IntegrableOn (fun t : ℝ => |cdem4345_assembled_lemma1M t| / t ^ 3)
      (Set.Ioi (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN)) := by
    refine hmajor.mono' (((continuous_abs.measurable.comp cdem4345_assembled_measurable_lemma1M).div
      (measurable_id.pow_const 3)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 := hA.trans ht
    have hMt := hM t ((cdem4345_assembled_lemma1X_finalN_gt_previousMertens hx).trans ht)
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_pow, abs_of_pos ht0]
    have hε0 : 0 ≤ cdem4345_assembled_lemma1PreviousMertensEpsilon := by
      norm_num [cdem4345_assembled_lemma1PreviousMertensEpsilon]
    calc
      |cdem4345_assembled_lemma1M t| / t ^ 3
          ≤ (cdem4345_assembled_lemma1PreviousMertensEpsilon * t) / t ^ 3 :=
        div_le_div_of_nonneg_right hMt (by positivity)
      _ = cdem4345_assembled_lemma1PreviousMertensEpsilon * (1 / t ^ 2) := by field_simp
  calc
    (∫ t in Set.Ioi (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN), |cdem4345_assembled_lemma1M t| / t ^ 3)
        ≤ ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN),
            cdem4345_assembled_lemma1PreviousMertensEpsilon * (1 / t ^ 2) :=
      setIntegral_mono_on hminor hmajor measurableSet_Ioi (fun t ht => by
        have ht0 := hA.trans ht
        have hMt := hM t ((cdem4345_assembled_lemma1X_finalN_gt_previousMertens hx).trans ht)
        calc
          |cdem4345_assembled_lemma1M t| / t ^ 3
              ≤ (cdem4345_assembled_lemma1PreviousMertensEpsilon * t) / t ^ 3 :=
            div_le_div_of_nonneg_right hMt (by positivity)
          _ = cdem4345_assembled_lemma1PreviousMertensEpsilon * (1 / t ^ 2) := by field_simp)
    _ = cdem4345_assembled_lemma1PreviousMertensEpsilon / cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN := by
      rw [integral_const_mul,
        MathExtras.Helfgott.AppendixC.cdem4345_assembled_integral_one_div_sq_Ioi hA]
      ring

theorem cdem4345_assembled_lemma1_previousSquarefree_QFactor
    (hQprev : cdem4345_assembled_Lemma1PreviousSquarefreeBootstrap)
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 ≤ x) :
    cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN)
      ≤ cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB := by
  rw [cdem4345_assembled_Lemma1PreviousSquarefreeBootstrap] at hQprev
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx
  have hX := cdem4345_assembled_lemma1X_finalN_gt_previousMertens hx
  have hthreshold : cdem4345_assembled_lemma1PreviousSquarefreeThreshold
      < cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN := by
    norm_num [cdem4345_assembled_lemma1PreviousMertensThreshold, cdem4345_assembled_lemma1PreviousSquarefreeThreshold] at hX ⊢
    linarith
  have hR := hQprev (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN) hthreshold
  have hRle := (le_abs_self (cdem4345_assembled_lemma1Remainder (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN))).trans hR
  have hQid : cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN)
      = (6 / Real.pi ^ 2) * cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN
          + cdem4345_assembled_lemma1Remainder (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN) := by
    rw [cdem4345_assembled_lemma1Remainder]
    ring
  rw [hQid]
  calc
    (6 / Real.pi ^ 2) * cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN
          + cdem4345_assembled_lemma1Remainder (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN)
        ≤ (6 / Real.pi ^ 2) * cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN
          + cdem4345_assembled_lemma1PreviousSquarefreeB * Real.sqrt (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN) := by
            linarith
    _ = cdem4345_assembled_lemma1QFactor x cdem4345_assembled_lemma1FinalN cdem4345_assembled_lemma1PreviousSquarefreeB := by
      rw [cdem4345_assembled_lemma1QFactor, cdem4345_assembled_lemma1X, Real.sqrt_div hx0.le,
        Real.sqrt_div (Real.sqrt_nonneg x)]
      ring

theorem cdem4345_assembled_lemma1_signedTail_abs_le
    {x : ℝ} {n : ℕ} :
    |cdem4345_assembled_lemma1SignedTailIntegral x n|
      ≤ ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3 := by
  unfold cdem4345_assembled_lemma1SignedTailIntegral
  calc
    |∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), cdem4345_assembled_lemma1M t / t ^ 3|
        ≤ ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), ‖cdem4345_assembled_lemma1M t / t ^ 3‖ :=
      by
        have hnorm :
            ‖∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), cdem4345_assembled_lemma1M t / t ^ 3‖
              ≤ ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), ‖cdem4345_assembled_lemma1M t / t ^ 3‖ :=
          norm_integral_le_integral_norm _
        simpa only [Real.norm_eq_abs] using hnorm
    _ = ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hX0 : 0 ≤ cdem4345_assembled_lemma1X x n := Real.sqrt_nonneg _
      have ht0 : 0 < t := lt_of_le_of_lt hX0 ht
      change |cdem4345_assembled_lemma1M t / t ^ 3| = |cdem4345_assembled_lemma1M t| / t ^ 3
      rw [abs_div, abs_pow, abs_of_pos ht0]

/-! ## Large-x analytic theorem from the exact remaining inputs -/

theorem cdem4345_assembled_lemma1_n197_analytic_of_inputs
    (hMprev : cdem4345_assembled_Lemma1PreviousMertensBootstrap)
    (hQprev : cdem4345_assembled_Lemma1PreviousSquarefreeBootstrap)
    (hweight : cdem4345_assembled_Lemma1N197T2WeightCertificate)
    {x : ℝ} (hx : cdem4345_assembled_lemma1FinalX0 < x) :
    |cdem4345_assembled_lemma1Remainder x| ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt x := by
  rw [cdem4345_assembled_Lemma1N197T2WeightCertificate] at hweight
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_lemma1FinalX0]) hx.le
  have hnx : cdem4345_assembled_lemma1FinalN ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    norm_num [cdem4345_assembled_lemma1FinalN, cdem4345_assembled_lemma1FinalX0] at hx ⊢
    linarith
  have hdecomp := cdem4345_assembled_lemma1_exactDecomposition hx0
    (by norm_num [cdem4345_assembled_lemma1FinalN]) hnx
  have hthree := cdem4345_assembled_lemma1_three_term_bound hx0.le hdecomp cdem4345_assembled_lemma1_signedTail_abs_le
  have hT1 := cdem4345_assembled_lemma1_T1_le hx0 (by norm_num [cdem4345_assembled_lemma1FinalN])
    (by norm_num [cdem4345_assembled_lemma1PreviousMertensEpsilon])
    (cdem4345_assembled_lemma1_previousMertens_tail_integral hMprev hx.le)
  have hpoint := cdem4345_assembled_lemma1_previousMertens_pointwise_n197 hMprev hx.le
  have hT2 := cdem4345_assembled_lemma1_T2_le_of_pointwise
    (n := cdem4345_assembled_lemma1FinalN) (x := x) (C := 2 * Real.sqrt cdem4345_assembled_lemma1FinalN - 146 / 100)
    (by norm_num [cdem4345_assembled_lemma1FinalN]) hx0.le
    (by norm_num [cdem4345_assembled_lemma1PreviousMertensEpsilon]) hpoint hweight
  have hT12 := cdem4345_assembled_lemma1_T12_n197 hT1 hT2
  have hCS := cdem4345_assembled_lemma1_centeredCauchy x cdem4345_assembled_lemma1FinalN
  have hQ := cdem4345_assembled_lemma1_previousSquarefree_QFactor hQprev hx.le
  have hS := cdem4345_assembled_lemma1PeriodicMajorantAt_n197 hx.le
  have hQ0 : 0 ≤ cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x cdem4345_assembled_lemma1FinalN) := by
    unfold cdem4345_assembled_squarefreeCount
    exact Finset.sum_nonneg fun a _ => abs_nonneg _
  have hS0 : 0 ≤ cdem4345_assembled_lemma1CenteredSquareMass x cdem4345_assembled_lemma1FinalN := by
    unfold cdem4345_assembled_lemma1CenteredSquareMass
    apply Finset.sum_nonneg
    intro a _
    split <;> positivity
  have hT3 := cdem4345_assembled_lemma1_T3_le_envelope hCS hQ0 hS0 hQ hS
  exact cdem4345_assembled_lemma1_n197_tail hx hthree hT12 hT3 cdem4345_assembled_lemma1N197EndpointCertificate_proven
    cdem4345_assembled_lemma1N197EnvelopeAntitone_proven

/-- The final natural-number theorem, with the bounded computation kept explicit. -/
theorem cdem4345_assembled_lemma1_theorem3bis_nat_of_inputs
    (hMprev : cdem4345_assembled_Lemma1PreviousMertensBootstrap)
    (hQprev : cdem4345_assembled_Lemma1PreviousSquarefreeBootstrap)
    (hweight : cdem4345_assembled_Lemma1N197T2WeightCertificate)
    (hwindow : cdem4345_assembled_Theorem3BisFiniteWindowCertificate)
    (X : ℕ) (hX : 438653 < X) :
    |cdem4345_assembled_lemma1Remainder X| ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt X := by
  by_cases hlarge : cdem4345_assembled_lemma1FinalX0 < X
  · exact cdem4345_assembled_lemma1_n197_analytic_of_inputs hMprev hQprev hweight
      (by exact_mod_cast hlarge)
  · rw [cdem4345_assembled_Theorem3BisFiniteWindowCertificate] at hwindow
    apply hwindow X hX
    have hle : (X : ℝ) ≤ cdem4345_assembled_lemma1FinalX0 := le_of_not_gt hlarge
    have hle' : (X : ℝ) ≤ (1600000000000000 : ℝ) := by
      simpa [cdem4345_assembled_lemma1FinalX0] using hle
    exact_mod_cast hle'

/-- Capstone phrased directly in terms of the audited remaining-input ledger. -/
theorem cdem4345_assembled_lemma1_theorem3bis_nat
    (h : Lemma1N197RemainingInputs)
    (X : ℕ) (hX : 438653 < X) :
    |cdem4345_assembled_lemma1Remainder X| ≤ cdem4345_assembled_lemma1FinalB * Real.sqrt X :=
  cdem4345_assembled_lemma1_theorem3bis_nat_of_inputs h.previousMertens h.previousSquarefree
    h.t2Weight h.boundedWindow X hX

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Parametric assembly of CDEM Lemma 1

The paper uses the same squarefree propagation several times with different
constants.  This file factors out the analytic assembly so later bootstrap
iterations expose only their real inputs and scalar endpoint facts.

There is no unbounded conclusion among the hypotheses:

* `hM` and `hQ` are the preceding, genuinely proved bootstrap stages;
* `hweight` is one fixed finite sum;
* `hperiodic` is the already-proved signed periodic majorant;
* `hendpoint` is one fixed real inequality;
* `hanti` is the elementary monotonicity of the displayed scalar envelope.

The threshold guards explicitly require both preceding bounds to be active at
`X_n=sqrt(x0/n)`.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset MeasureTheory Set
open scoped BigOperators

noncomputable def cdem4345_assembled_lemma1ParametricEnvelope
    (epsilon b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  epsilon * (4 * Real.sqrt n - 146 / 100) * Real.sqrt x
    + cdem4345_assembled_lemma1T3Envelope x n b

theorem cdem4345_assembled_lemma1X_mono_left
    {x0 x : ℝ} {n : ℕ} (hx0 : 0 ≤ x0) (hxx : x0 ≤ x) :
    cdem4345_assembled_lemma1X x0 n ≤ cdem4345_assembled_lemma1X x n := by
  rw [cdem4345_assembled_lemma1X, cdem4345_assembled_lemma1X]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hxx (Nat.cast_nonneg n))

theorem cdem4345_assembled_lemma1_parametric_M_pointwise
    {epsilon x0 mThreshold x : ℝ} {n : ℕ}
    (hx0 : 0 < x0) (hxx : x0 ≤ x)
    (hguard : mThreshold < cdem4345_assembled_lemma1X x0 n)
    (hM : ∀ t : ℝ, mThreshold < t → |cdem4345_assembled_lemma1M t| ≤ epsilon * t) :
    ∀ j ∈ Finset.Icc 1 n,
      |cdem4345_assembled_lemma1M (cdem4345_assembled_lemma1X x j)|
        ≤ epsilon * Real.sqrt x / Real.sqrt j := by
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hx : 0 < x := hx0.trans_le hxx
  have hXn_x : cdem4345_assembled_lemma1X x0 n ≤ cdem4345_assembled_lemma1X x n :=
    cdem4345_assembled_lemma1X_mono_left hx0.le hxx
  have hXj : cdem4345_assembled_lemma1X x n ≤ cdem4345_assembled_lemma1X x j :=
    cdem4345_assembled_lemma1X_antitone_index hx.le hj'.1 hj'.2
  have hthreshold : mThreshold < cdem4345_assembled_lemma1X x j :=
    hguard.trans_le (hXn_x.trans hXj)
  have h := hM (cdem4345_assembled_lemma1X x j) hthreshold
  simpa [cdem4345_assembled_lemma1X, Real.sqrt_div hx.le, mul_div_assoc] using h

theorem cdem4345_assembled_lemma1_parametric_tail_integral
    {epsilon x0 mThreshold x : ℝ} {n : ℕ}
    (hx0 : 0 < x0) (hn : 1 ≤ n) (hxx : x0 ≤ x)
    (hguard : mThreshold < cdem4345_assembled_lemma1X x0 n)
    (hM : ∀ t : ℝ, mThreshold < t → |cdem4345_assembled_lemma1M t| ≤ epsilon * t) :
    (∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3)
      ≤ epsilon / cdem4345_assembled_lemma1X x n := by
  have hx : 0 < x := hx0.trans_le hxx
  have hA : 0 < cdem4345_assembled_lemma1X x n := cdem4345_assembled_lemma1X_pos hx hn
  have hXn_x : cdem4345_assembled_lemma1X x0 n ≤ cdem4345_assembled_lemma1X x n :=
    cdem4345_assembled_lemma1X_mono_left hx0.le hxx
  have hthreshold : mThreshold < cdem4345_assembled_lemma1X x n := hguard.trans_le hXn_x
  have hmajor : IntegrableOn
      (fun t : ℝ => epsilon * (1 / t ^ 2)) (Set.Ioi (cdem4345_assembled_lemma1X x n)) :=
    (MathExtras.Helfgott.AppendixC.cdem4345_assembled_integrableOn_one_div_sq_Ioi hA).const_mul _
  have hminor : IntegrableOn (fun t : ℝ => |cdem4345_assembled_lemma1M t| / t ^ 3)
      (Set.Ioi (cdem4345_assembled_lemma1X x n)) := by
    refine hmajor.mono' (((continuous_abs.measurable.comp cdem4345_assembled_measurable_lemma1M).div
      (measurable_id.pow_const 3)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 := hA.trans ht
    have hMt := hM t (hthreshold.trans ht)
    rw [Real.norm_eq_abs, abs_div, abs_abs, abs_pow, abs_of_pos ht0]
    calc
      |cdem4345_assembled_lemma1M t| / t ^ 3 ≤ (epsilon * t) / t ^ 3 :=
        div_le_div_of_nonneg_right hMt (by positivity)
      _ = epsilon * (1 / t ^ 2) := by field_simp
  calc
    (∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), |cdem4345_assembled_lemma1M t| / t ^ 3)
        ≤ ∫ t in Set.Ioi (cdem4345_assembled_lemma1X x n), epsilon * (1 / t ^ 2) :=
      setIntegral_mono_on hminor hmajor measurableSet_Ioi (fun t ht => by
        have ht0 := hA.trans ht
        have hMt := hM t (hthreshold.trans ht)
        calc
          |cdem4345_assembled_lemma1M t| / t ^ 3 ≤ (epsilon * t) / t ^ 3 :=
            div_le_div_of_nonneg_right hMt (by positivity)
          _ = epsilon * (1 / t ^ 2) := by field_simp)
    _ = epsilon / cdem4345_assembled_lemma1X x n := by
      rw [integral_const_mul,
        MathExtras.Helfgott.AppendixC.cdem4345_assembled_integral_one_div_sq_Ioi hA]
      ring

theorem cdem4345_assembled_lemma1_parametric_QFactor
    {b x0 qThreshold x : ℝ} {n : ℕ}
    (hx0 : 0 < x0) (hxx : x0 ≤ x)
    (hguard : qThreshold < cdem4345_assembled_lemma1X x0 n)
    (hQ : ∀ t : ℝ, qThreshold < t →
      |cdem4345_assembled_lemma1Remainder t| ≤ b * Real.sqrt t) :
    cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n) ≤ cdem4345_assembled_lemma1QFactor x n b := by
  have hx : 0 < x := hx0.trans_le hxx
  have hXn_x : cdem4345_assembled_lemma1X x0 n ≤ cdem4345_assembled_lemma1X x n :=
    cdem4345_assembled_lemma1X_mono_left hx0.le hxx
  have hR := hQ (cdem4345_assembled_lemma1X x n) (hguard.trans_le hXn_x)
  have hRle := (le_abs_self (cdem4345_assembled_lemma1Remainder (cdem4345_assembled_lemma1X x n))).trans hR
  rw [show cdem4345_assembled_squarefreeCount (cdem4345_assembled_lemma1X x n) =
      (6 / Real.pi ^ 2) * cdem4345_assembled_lemma1X x n + cdem4345_assembled_lemma1Remainder (cdem4345_assembled_lemma1X x n) by
        rw [cdem4345_assembled_lemma1Remainder]
        ring]
  calc
    (6 / Real.pi ^ 2) * cdem4345_assembled_lemma1X x n + cdem4345_assembled_lemma1Remainder (cdem4345_assembled_lemma1X x n)
        ≤ (6 / Real.pi ^ 2) * cdem4345_assembled_lemma1X x n
            + b * Real.sqrt (cdem4345_assembled_lemma1X x n) := by linarith
    _ = cdem4345_assembled_lemma1QFactor x n b := by
      rw [cdem4345_assembled_lemma1QFactor, cdem4345_assembled_lemma1X, Real.sqrt_div hx.le,
        Real.sqrt_div (Real.sqrt_nonneg x)]
      ring

/-- Parametric CDEM Lemma 1.  All unbounded work is inherited from the preceding
`hM`/`hQ` stages; the conclusion is obtained from the exact decomposition,
signed periodic majorant, and scalar propagation supplied here. -/
theorem cdem4345_assembled_lemma1_parametric_analytic
    {epsilon b x0 B mThreshold qThreshold : ℝ} {n : ℕ}
    (hx0 : 0 < x0)
    (hn : 5 ≤ n)
    (hnx0 : (n : ℝ) ≤ x0)
    (hepsilon : 0 ≤ epsilon)
    (hMguard : mThreshold < cdem4345_assembled_lemma1X x0 n)
    (hQguard : qThreshold < cdem4345_assembled_lemma1X x0 n)
    (hM : ∀ t : ℝ, mThreshold < t → |cdem4345_assembled_lemma1M t| ≤ epsilon * t)
    (hQ : ∀ t : ℝ, qThreshold < t →
      |cdem4345_assembled_lemma1Remainder t| ≤ b * Real.sqrt t)
    (hweight : cdem4345_assembled_lemma1T2Weight n ≤ 2 * Real.sqrt n - 146 / 100)
    (hperiodic : ∀ x : ℝ, x0 ≤ x → cdem4345_assembled_Lemma1PeriodicMajorantAt x n)
    (hendpoint : cdem4345_assembled_lemma1ParametricEnvelope epsilon b n x0 ≤ B * Real.sqrt x0)
    (hanti : AntitoneOn
      (fun x => cdem4345_assembled_lemma1ParametricEnvelope epsilon b n x / Real.sqrt x)
      (Set.Ici x0))
    {x : ℝ} (hxx : x0 < x) :
    |cdem4345_assembled_lemma1Remainder x| ≤ B * Real.sqrt x := by
  have hx : 0 < x := hx0.trans hxx
  have hnx : n ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    exact hnx0.trans hxx.le
  have hdecomp := cdem4345_assembled_lemma1_exactDecomposition hx (by omega) hnx
  have hthree := cdem4345_assembled_lemma1_three_term_bound hx.le hdecomp cdem4345_assembled_lemma1_signedTail_abs_le
  have hT1 := cdem4345_assembled_lemma1_T1_le hx (by omega) hepsilon
    (cdem4345_assembled_lemma1_parametric_tail_integral hx0 (by omega) hxx.le hMguard hM)
  have hT2 := cdem4345_assembled_lemma1_T2_le_of_pointwise
    (n := n) (x := x) (C := 2 * Real.sqrt n - 146 / 100)
    (by omega) hx.le hepsilon
    (cdem4345_assembled_lemma1_parametric_M_pointwise hx0 hxx.le hMguard hM) hweight
  have hT12 : cdem4345_assembled_lemma1T1 x n + cdem4345_assembled_lemma1T2 x n
      ≤ epsilon * (4 * Real.sqrt n - 146 / 100) * Real.sqrt x := by
    linarith
  have hQfactor := cdem4345_assembled_lemma1_parametric_QFactor hx0 hxx.le hQguard hQ
  have hT3 := cdem4345_assembled_lemma1_T3_le_envelope (cdem4345_assembled_lemma1_centeredCauchy x n)
    (by unfold cdem4345_assembled_squarefreeCount; exact Finset.sum_nonneg fun a _ => abs_nonneg _)
    (by
      unfold cdem4345_assembled_lemma1CenteredSquareMass
      apply Finset.sum_nonneg
      intro a _
      split <;> positivity)
    hQfactor (hperiodic x hxx.le)
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsx0 : 0 < Real.sqrt x0 := Real.sqrt_pos.2 hx0
  have hmono := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hxx.le) hxx.le
  have henddiv : cdem4345_assembled_lemma1ParametricEnvelope epsilon b n x0 / Real.sqrt x0 ≤ B := by
    rw [div_le_iff₀ hsx0]
    simpa [mul_comm] using hendpoint
  have henvdiv := hmono.trans henddiv
  have henv : cdem4345_assembled_lemma1ParametricEnvelope epsilon b n x ≤ B * Real.sqrt x := by
    rwa [div_le_iff₀ hsx] at henvdiv
  unfold cdem4345_assembled_lemma1ParametricEnvelope at henv
  linarith

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

/-!
# Numeric parameters for the self-contained CDEM bootstrap

This leaf module deliberately contains only the exact numeric parameters.
Receipt-facing source propositions can therefore use the historical
fully-qualified names without importing any finite certificate proof.
-/

namespace MathExtras.CohenDressElMarraki

def cdem4345_assembled_selfBootstrapThreshold : ℝ := 9
noncomputable def cdem4345_assembled_selfBootstrapB1 : ℝ := 755 / 10000
noncomputable def cdem4345_assembled_selfBootstrapB2 : ℝ := 285 / 10000
noncomputable def cdem4345_assembled_selfBootstrapB3 : ℝ := 27 / 1000

def cdem4345_assembled_selfBootstrapX0 : ℝ := 10000000000000000

def cdem4345_assembled_selfBootstrapN1 : ℕ := 23
def cdem4345_assembled_selfBootstrapN2 : ℕ := 179
def cdem4345_assembled_selfBootstrapN3 : ℕ := 201

def cdem4345_assembled_selfBootstrapMThreshold1 : ℝ := 80000
def cdem4345_assembled_selfBootstrapMThreshold2 : ℝ := 4900000
def cdem4345_assembled_selfBootstrapMThreshold3 : ℝ := 6160000

noncomputable def cdem4345_assembled_selfBootstrapEpsilon1 : ℝ := 1 / 495
noncomputable def cdem4345_assembled_selfBootstrapEpsilon2 : ℝ := 1 / 3869
noncomputable def cdem4345_assembled_selfBootstrapEpsilon3 : ℝ := 1 / 4344

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Self-contained CDEM bootstrap: exact Lemma 4 iterations

The two historical analytic seeds `|M(x)|<=x/2360` and
`|R(x)|<=0.1333 sqrt(x)` are unnecessary.  The fixed `N=1.32*10^9`
Theorem 5 table can be rescaled and iterated, starting from the theorem-level
coarse bound `|R(x)|<=3 sqrt(x)`.

This file records the three exact Lemma 4 steps used by the replacement chain:

```text
R coefficient 3       -> M denominator 495
R coefficient 0.0755  -> M denominator 3869
R coefficient 0.0285  -> M denominator 4344.
```

The intervening squarefree improvements are CDEM Lemma 1 steps.  Their audited
parameters at `x0=10^16` are respectively

```text
(M denominator 495,  R coefficient 3,      n=23)  -> 0.0755
(M denominator 3869, R coefficient 0.0755, n=179) -> 0.0285
(M denominator 4344, R coefficient 0.0285, n=201) -> 0.0270.
```

They are assembled separately so that every `X_n`, finite Hurst bridge, and
bounded squarefree window remains explicit.
-/

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- Uniform real squarefree input required by one rescaled Theorem 5 row. -/
def cdem4345_assembled_SelfBootstrapSquarefreeBound (b : ℝ) : Prop :=
  ∀ y : ℝ, cdem4345_assembled_selfBootstrapThreshold < y →
    |cdem4345_assembled_squarefreeCount y - (6 / Real.pi ^ 2) * y| ≤ b * Real.sqrt y

/-- Real step-function form of one preceding Mertens stage.  The theorems below
use this only above the displayed finite-Hurst threshold. -/
def cdem4345_assembled_SelfBootstrapMertensBound (epsilon threshold : ℝ) : Prop :=
  ∀ t : ℝ, threshold < t → |cdem4345_assembled_lemma1M t| ≤ epsilon * t

/-- A fixed scalar endpoint for one Lemma 1 iteration. -/
def cdem4345_assembled_SelfBootstrapLemma1Endpoint (epsilon b : ℝ) (n : ℕ) (B : ℝ) : Prop :=
  cdem4345_assembled_lemma1ParametricEnvelope epsilon b n cdem4345_assembled_selfBootstrapX0
    ≤ B * Real.sqrt cdem4345_assembled_selfBootstrapX0

/-- Elementary propagation of the fixed scalar envelope. -/
def cdem4345_assembled_SelfBootstrapLemma1Antitone (epsilon b : ℝ) (n : ℕ) : Prop :=
  AntitoneOn
    (fun x => cdem4345_assembled_lemma1ParametricEnvelope epsilon b n x / Real.sqrt x)
    (Set.Ici cdem4345_assembled_selfBootstrapX0)

/-- One finite reciprocal-square-root sum. -/
def cdem4345_assembled_SelfBootstrapLemma1Weight (n : ℕ) : Prop :=
  cdem4345_assembled_lemma1T2Weight n ≤ 2 * Real.sqrt n - 146 / 100

theorem cdem4345_assembled_selfBootstrapSquarefreeBound_three :
    cdem4345_assembled_SelfBootstrapSquarefreeBound 3 := by
  rw [cdem4345_assembled_SelfBootstrapSquarefreeBound]
  intro y hy
  apply cdem4345_assembled_coarseSquarefreeRemainder_three
  norm_num [cdem4345_assembled_selfBootstrapThreshold] at hy ⊢
  linarith

/-! ## Exact Lemma 1 guards -/

theorem cdem4345_assembled_selfBootstrapPeriodicMajorant
    {n : ℕ} (hn5 : 5 ≤ n) (hn201 : n ≤ 201)
    {x : ℝ} (hx : cdem4345_assembled_selfBootstrapX0 ≤ x) :
    cdem4345_assembled_Lemma1PeriodicMajorantAt x n := by
  have hxFinal : cdem4345_assembled_lemma1FinalX0 ≤ x := by
    norm_num [cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_lemma1FinalX0] at hx ⊢
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  have hscalar := cdem4345_assembled_lemma1PeriodicCutoffScalarAt_proven hxFinal
  have hN202 : 202 ≤ cdem4345_assembled_lemma1PeriodicCutoff x := by
    let y := cdem4345_assembled_lemma1PeriodicCutoffY x
    have hy := cdem4345_assembled_lemma1PeriodicCutoffY_pos hx0
    have hy3 := cdem4345_assembled_lemma1PeriodicCutoffY_cube hx0
    have hy202 : (202 : ℝ) ≤ y := by
      apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hy.le
      rw [hy3, le_div_iff₀ (by norm_num : (0 : ℝ) < 144)]
      norm_num [cdem4345_assembled_selfBootstrapX0] at hx ⊢
      linarith
    exact Nat.le_floor hy202
  apply cdem4345_assembled_lemma1PeriodicMajorantAt_of_cutoff hx0 hn5
    (N := cdem4345_assembled_lemma1PeriodicCutoff x)
  · omega
  · exact hscalar

theorem cdem4345_assembled_selfBootstrapMGuard1 :
    cdem4345_assembled_selfBootstrapMThreshold1
      < cdem4345_assembled_lemma1X cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 := by
  rw [cdem4345_assembled_selfBootstrapMThreshold1, cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN1]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 80000)).2
  norm_num

theorem cdem4345_assembled_selfBootstrapMGuard2 :
    cdem4345_assembled_selfBootstrapMThreshold2
      < cdem4345_assembled_lemma1X cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN2 := by
  rw [cdem4345_assembled_selfBootstrapMThreshold2, cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN2]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 4900000)).2
  norm_num

theorem cdem4345_assembled_selfBootstrapMGuard3 :
    cdem4345_assembled_selfBootstrapMThreshold3
      < cdem4345_assembled_lemma1X cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN3 := by
  rw [cdem4345_assembled_selfBootstrapMThreshold3, cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN3]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 6160000)).2
  norm_num

theorem cdem4345_assembled_selfBootstrapQGuard1 :
    cdem4345_assembled_selfBootstrapThreshold < cdem4345_assembled_lemma1X cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 := by
  rw [cdem4345_assembled_selfBootstrapThreshold, cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN1]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 9)).2
  norm_num

theorem cdem4345_assembled_selfBootstrapQGuard2 :
    cdem4345_assembled_selfBootstrapThreshold < cdem4345_assembled_lemma1X cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN2 := by
  rw [cdem4345_assembled_selfBootstrapThreshold, cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN2]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 9)).2
  norm_num

theorem cdem4345_assembled_selfBootstrapQGuard3 :
    cdem4345_assembled_selfBootstrapThreshold < cdem4345_assembled_lemma1X cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN3 := by
  rw [cdem4345_assembled_selfBootstrapThreshold, cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN3]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 9)).2
  norm_num

/-- First Lemma 1 improvement in the self-contained chain. -/
theorem cdem4345_assembled_selfBootstrapSquarefreeB1_analytic
    (hM : cdem4345_assembled_SelfBootstrapMertensBound
      cdem4345_assembled_selfBootstrapEpsilon1 cdem4345_assembled_selfBootstrapMThreshold1)
    (hweight : cdem4345_assembled_SelfBootstrapLemma1Weight cdem4345_assembled_selfBootstrapN1)
    (hendpoint : cdem4345_assembled_SelfBootstrapLemma1Endpoint
      cdem4345_assembled_selfBootstrapEpsilon1 3 cdem4345_assembled_selfBootstrapN1 cdem4345_assembled_selfBootstrapB1)
    (hanti : cdem4345_assembled_SelfBootstrapLemma1Antitone
      cdem4345_assembled_selfBootstrapEpsilon1 3 cdem4345_assembled_selfBootstrapN1)
    {x : ℝ} (hx : cdem4345_assembled_selfBootstrapX0 < x) :
    |cdem4345_assembled_lemma1Remainder x| ≤ cdem4345_assembled_selfBootstrapB1 * Real.sqrt x := by
  apply cdem4345_assembled_lemma1_parametric_analytic
    (epsilon := cdem4345_assembled_selfBootstrapEpsilon1) (b := 3)
    (x0 := cdem4345_assembled_selfBootstrapX0) (B := cdem4345_assembled_selfBootstrapB1)
    (mThreshold := cdem4345_assembled_selfBootstrapMThreshold1)
    (qThreshold := cdem4345_assembled_selfBootstrapThreshold) (n := cdem4345_assembled_selfBootstrapN1)
  · norm_num [cdem4345_assembled_selfBootstrapX0]
  · norm_num [cdem4345_assembled_selfBootstrapN1]
  · norm_num [cdem4345_assembled_selfBootstrapN1, cdem4345_assembled_selfBootstrapX0]
  · norm_num [cdem4345_assembled_selfBootstrapEpsilon1]
  · exact cdem4345_assembled_selfBootstrapMGuard1
  · exact cdem4345_assembled_selfBootstrapQGuard1
  · exact hM
  · intro t ht
    unfold cdem4345_assembled_lemma1Remainder
    exact cdem4345_assembled_selfBootstrapSquarefreeBound_three t ht
  · exact hweight
  · intro y hy
    exact cdem4345_assembled_selfBootstrapPeriodicMajorant (by norm_num [cdem4345_assembled_selfBootstrapN1])
      (by norm_num [cdem4345_assembled_selfBootstrapN1]) hy
  · exact hendpoint
  · exact hanti
  · exact hx


end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scalar monotonicity for the self-contained CDEM bootstrap

All three replacement Lemma 1 iterations use `x0=10^16` and `5<=n<=201`.
This file proves their normalized envelope is antitone uniformly in `epsilon`
and every nonnegative preceding squarefree coefficient `b`.

The only non-obvious sign is the derivative of the normalized periodic factor.
It is already negative once `x^(1/3)>=10000`; the live range is much larger.
-/

namespace MathExtras.CohenDressElMarraki

open Set

private noncomputable def cdem4345_assembled_selfBootstrapQRatioModel (b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  6 / (Real.pi ^ 2 * Real.sqrt n)
    + (b / Real.sqrt (Real.sqrt n)) * x ^ (-(1 : ℝ) / 4)

private noncomputable def cdem4345_assembled_selfBootstrapSRatioModel (n : ℕ) (x : ℝ) : ℝ :=
  1 / (18 * Real.sqrt ((n : ℝ) - 2 / 100))
    + 12 ^ ((1 : ℝ) / 3) / 6 * x ^ (-(1 : ℝ) / 6)
    - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) * x ^ (-(1 : ℝ) / 2)

private lemma cdem4345_assembled_selfBootstrapQRatio_eq_model
    {b x : ℝ} {n : ℕ} (hx : 0 < x) :
    cdem4345_assembled_lemma1QFactor x n b / Real.sqrt x = cdem4345_assembled_selfBootstrapQRatioModel b n x := by
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  unfold cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapQRatioModel
  rw [add_div]
  apply congrArg₂ (fun u v : ℝ => u + v)
  · field_simp [hsx]
  · calc
      b * Real.sqrt (Real.sqrt x) / Real.sqrt (Real.sqrt n) / Real.sqrt x
          = b / Real.sqrt (Real.sqrt n)
              * (Real.sqrt (Real.sqrt x) / Real.sqrt x) := by ring
      _ = b / Real.sqrt (Real.sqrt n) * x ^ (-(1 : ℝ) / 4) := by
        rw [cdem4345_assembled_sqrt_sqrt_div_sqrt_eq_rpow_neg_quarter hx]

private lemma cdem4345_assembled_selfBootstrapSRatio_eq_model
    {x : ℝ} {n : ℕ} (hx : 0 < x) :
    cdem4345_assembled_lemma1SFactor x n / Real.sqrt x = cdem4345_assembled_selfBootstrapSRatioModel n x := by
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hneg :
      ((2 / 3 : ℝ) * ((n : ℝ) - 1 / 2)) / Real.sqrt x =
        (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) * x ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hx.le]
    ring
  unfold cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapSRatioModel
  rw [sub_div, add_div, hneg]
  apply congrArg₂ (fun u v : ℝ => u - v)
  · apply congrArg₂ (fun u v : ℝ => u + v)
    · field_simp [hsx]
    · calc
        (12 * x) ^ ((1 : ℝ) / 3) / 6 / Real.sqrt x
            = ((12 * x) ^ ((1 : ℝ) / 3) / Real.sqrt x) / 6 := by ring
        _ = 12 ^ ((1 : ℝ) / 3) * x ^ (-(1 : ℝ) / 6) / 6 := by
          rw [cdem4345_assembled_cuberoot_mul_div_sqrt_eq hx]
        _ = 12 ^ ((1 : ℝ) / 3) / 6 * x ^ (-(1 : ℝ) / 6) := by ring
  · rfl

private lemma cdem4345_assembled_selfBootstrapQRatioModel_hasDerivAt
    {b x : ℝ} {n : ℕ} (hx : 0 < x) :
    HasDerivAt (cdem4345_assembled_selfBootstrapQRatioModel b n)
      ((b / Real.sqrt (Real.sqrt n))
        * ((-(1 : ℝ) / 4) * x ^ (-(1 : ℝ) / 4 - 1))) x := by
  unfold cdem4345_assembled_selfBootstrapQRatioModel
  have h := (hasDerivAt_const x (6 / (Real.pi ^ 2 * Real.sqrt n))).add
    ((Real.hasDerivAt_rpow_const (p := (-(1 : ℝ) / 4))
      (Or.inl hx.ne')).const_mul (b / Real.sqrt (Real.sqrt n)))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with y
    rfl
  · ring

private lemma cdem4345_assembled_selfBootstrapSRatioModel_hasDerivAt
    {x : ℝ} {n : ℕ} (hx : 0 < x) :
    HasDerivAt (cdem4345_assembled_selfBootstrapSRatioModel n)
      (12 ^ ((1 : ℝ) / 3) / 6
          * ((-(1 : ℝ) / 6) * x ^ (-(1 : ℝ) / 6 - 1))
        - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2)
          * ((-(1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2 - 1))) x := by
  unfold cdem4345_assembled_selfBootstrapSRatioModel
  have h := ((hasDerivAt_const x
      (1 / (18 * Real.sqrt ((n : ℝ) - 2 / 100)))).add
    ((Real.hasDerivAt_rpow_const (p := (-(1 : ℝ) / 6))
      (Or.inl hx.ne')).const_mul (12 ^ ((1 : ℝ) / 3) / 6))).sub
    ((Real.hasDerivAt_rpow_const (p := (-(1 : ℝ) / 2))
      (Or.inl hx.ne')).const_mul ((2 / 3 : ℝ) * ((n : ℝ) - 1 / 2)))
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with y
    rfl
  · ring

private lemma cdem4345_assembled_selfBootstrapQRatioModel_deriv_nonpos
    {b x : ℝ} {n : ℕ} (hb : 0 ≤ b) (hn : 1 ≤ n)
    (hx : cdem4345_assembled_selfBootstrapX0 < x) :
    deriv (cdem4345_assembled_selfBootstrapQRatioModel b n) x ≤ 0 := by
  have hx0 : 0 < x := lt_trans (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  rw [(cdem4345_assembled_selfBootstrapQRatioModel_hasDerivAt hx0).deriv]
  have hden : 0 < Real.sqrt (Real.sqrt n) := by positivity
  have hpow : 0 ≤ x ^ (-(1 : ℝ) / 4 - 1) := Real.rpow_nonneg hx0.le _
  exact mul_nonpos_of_nonneg_of_nonpos (div_nonneg hb hden.le)
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hpow)

private lemma cdem4345_assembled_selfBootstrapSRatioModel_deriv_nonpos
    {x : ℝ} {n : ℕ} (hn201 : n ≤ 201)
    (hx : cdem4345_assembled_selfBootstrapX0 < x) :
    deriv (cdem4345_assembled_selfBootstrapSRatioModel n) x ≤ 0 := by
  have hx0 : 0 < x := lt_trans (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  rw [(cdem4345_assembled_selfBootstrapSRatioModel_hasDerivAt hx0).deriv]
  have h12 : (1 : ℝ) ≤ 12 ^ ((1 : ℝ) / 3) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have hx13 : (10000 : ℝ) ≤ x ^ ((1 : ℝ) / 3) := by
    apply cdem4345_assembled_ten_thousand_le_cuberoot
    norm_num [cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_lemma1FinalX0] at hx ⊢
    linarith
  have hprod : (10000 : ℝ) ≤
      12 ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 3) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr hx13)]
  have hpow_split :
      x ^ (-(1 : ℝ) / 6 - 1) =
        x ^ (-(1 : ℝ) / 2 - 1) * x ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hpow : 0 ≤ x ^ (-(1 : ℝ) / 2 - 1) := Real.rpow_nonneg hx0.le _
  rw [hpow_split]
  have hnR : (n : ℝ) ≤ 201 := by exact_mod_cast hn201
  have hbracket :
      (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) / 2
        - (12 ^ ((1 : ℝ) / 3) / 36) * x ^ ((1 : ℝ) / 3) ≤ 0 := by
    nlinarith
  have heq :
      12 ^ ((1 : ℝ) / 3) / 6
            * ((-(1 : ℝ) / 6) *
              (x ^ (-(1 : ℝ) / 2 - 1) * x ^ ((1 : ℝ) / 3)))
          - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2)
            * ((-(1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2 - 1))
        = x ^ (-(1 : ℝ) / 2 - 1) *
            ((2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) / 2
              - (12 ^ ((1 : ℝ) / 3) / 36) * x ^ ((1 : ℝ) / 3)) := by
    ring
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos hpow hbracket

private theorem cdem4345_assembled_selfBootstrapQRatioModel_antitone
    {b : ℝ} {n : ℕ} (hb : 0 ≤ b) (hn : 1 ≤ n) :
    AntitoneOn (cdem4345_assembled_selfBootstrapQRatioModel b n) (Set.Ici cdem4345_assembled_selfBootstrapX0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici cdem4345_assembled_selfBootstrapX0) ?_ ?_ ?_
  · intro x hx
    exact (cdem4345_assembled_selfBootstrapQRatioModel_hasDerivAt
      (lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    exact (cdem4345_assembled_selfBootstrapQRatioModel_hasDerivAt
      (lt_trans (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    exact cdem4345_assembled_selfBootstrapQRatioModel_deriv_nonpos hb hn hx

private theorem cdem4345_assembled_selfBootstrapSRatioModel_antitone
    {n : ℕ} (hn201 : n ≤ 201) :
    AntitoneOn (cdem4345_assembled_selfBootstrapSRatioModel n) (Set.Ici cdem4345_assembled_selfBootstrapX0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici cdem4345_assembled_selfBootstrapX0) ?_ ?_ ?_
  · intro x hx
    exact (cdem4345_assembled_selfBootstrapSRatioModel_hasDerivAt
      (lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx)).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    intro x hx
    exact (cdem4345_assembled_selfBootstrapSRatioModel_hasDerivAt
      (lt_trans (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    exact cdem4345_assembled_selfBootstrapSRatioModel_deriv_nonpos hn201 hx

lemma cdem4345_assembled_selfBootstrapQRatio_nonneg
    {b x : ℝ} {n : ℕ} (hb : 0 ≤ b) (hn : 1 ≤ n)
    (hx : cdem4345_assembled_selfBootstrapX0 ≤ x) :
    0 ≤ cdem4345_assembled_lemma1QFactor x n b / Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  rw [cdem4345_assembled_selfBootstrapQRatio_eq_model hx0]
  unfold cdem4345_assembled_selfBootstrapQRatioModel
  positivity

lemma cdem4345_assembled_selfBootstrapSRatio_nonneg
    {x : ℝ} {n : ℕ} (hn5 : 5 ≤ n) (hn201 : n ≤ 201)
    (hx : cdem4345_assembled_selfBootstrapX0 ≤ x) :
    0 ≤ cdem4345_assembled_lemma1SFactor x n / Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  rw [cdem4345_assembled_selfBootstrapSRatio_eq_model hx0]
  unfold cdem4345_assembled_selfBootstrapSRatioModel
  have hn5R : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hn201R : (n : ℝ) ≤ 201 := by exact_mod_cast hn201
  have hsqrt_n : Real.sqrt ((n : ℝ) - 2 / 100) ≤ 15 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  have hsqrt_n_pos : 0 < Real.sqrt ((n : ℝ) - 2 / 100) := by
    apply Real.sqrt_pos.2
    nlinarith
  have hconstant :
      (1 / 270 : ℝ) ≤ 1 / (18 * Real.sqrt ((n : ℝ) - 2 / 100)) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsqrt_x : (100000000 : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).2
    norm_num [cdem4345_assembled_selfBootstrapX0] at hx ⊢
    nlinarith
  have hnegpow : x ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt x := by
    rw [show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow]
    rw [one_div]
  have hrecip : 1 / Real.sqrt x ≤ (1 / 100000000 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hsqrt_x
  have hnegative :
      (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) * x ^ (-(1 : ℝ) / 2)
        ≤ 1 / 270 := by
    rw [hnegpow]
    have hmul := mul_le_mul_of_nonneg_left hrecip
      (show 0 ≤ (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) by nlinarith)
    nlinarith
  have hpositive :
      0 ≤ 12 ^ ((1 : ℝ) / 3) / 6 * x ^ (-(1 : ℝ) / 6) := by positivity
  linarith

lemma cdem4345_assembled_selfBootstrapNormalizedT3_eq
    {b x : ℝ} {n : ℕ} (hb : 0 ≤ b) (hn5 : 5 ≤ n) (hn201 : n ≤ 201)
    (hx : cdem4345_assembled_selfBootstrapX0 ≤ x) :
    cdem4345_assembled_lemma1T3Envelope x n b / Real.sqrt x =
      Real.sqrt ((cdem4345_assembled_lemma1QFactor x n b / Real.sqrt x)
        * (cdem4345_assembled_lemma1SFactor x n / Real.sqrt x)) := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx0).ne'
  have hqratio := cdem4345_assembled_selfBootstrapQRatio_nonneg (n := n) hb (by omega) hx
  have hsratio := cdem4345_assembled_selfBootstrapSRatio_nonneg hn5 hn201 hx
  have hq : 0 ≤ cdem4345_assembled_lemma1QFactor x n b := by
    have := mul_nonneg hqratio (Real.sqrt_nonneg x)
    rwa [div_mul_cancel₀ _ hsx] at this
  unfold cdem4345_assembled_lemma1T3Envelope
  rw [← Real.sqrt_div (mul_nonneg hq (by
    have := mul_nonneg hsratio (Real.sqrt_nonneg x)
    rwa [div_mul_cancel₀ _ hsx] at this))]
  congr 1
  field_simp [hsx]
  rw [Real.sq_sqrt hx0.le]

/-- Uniform monotonicity theorem covering all three self-contained Lemma 1
iterations. -/
theorem cdem4345_assembled_selfBootstrapLemma1Antitone_proven
    {epsilon b : ℝ} {n : ℕ} (hb : 0 ≤ b) (hn5 : 5 ≤ n) (hn201 : n ≤ 201) :
    cdem4345_assembled_SelfBootstrapLemma1Antitone epsilon b n := by
  rw [cdem4345_assembled_SelfBootstrapLemma1Antitone]
  intro x hx y hy hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hx
  have hy0 : 0 < y := lt_of_lt_of_le (by norm_num [cdem4345_assembled_selfBootstrapX0]) hy
  have hq : cdem4345_assembled_lemma1QFactor y n b / Real.sqrt y ≤
      cdem4345_assembled_lemma1QFactor x n b / Real.sqrt x := by
    rw [cdem4345_assembled_selfBootstrapQRatio_eq_model hy0, cdem4345_assembled_selfBootstrapQRatio_eq_model hx0]
    exact cdem4345_assembled_selfBootstrapQRatioModel_antitone hb (by omega) hx hy hxy
  have hs : cdem4345_assembled_lemma1SFactor y n / Real.sqrt y ≤
      cdem4345_assembled_lemma1SFactor x n / Real.sqrt x := by
    rw [cdem4345_assembled_selfBootstrapSRatio_eq_model hy0, cdem4345_assembled_selfBootstrapSRatio_eq_model hx0]
    exact cdem4345_assembled_selfBootstrapSRatioModel_antitone hn201 hx hy hxy
  have hsy := cdem4345_assembled_selfBootstrapSRatio_nonneg hn5 hn201 hy
  have hqx := cdem4345_assembled_selfBootstrapQRatio_nonneg (n := n) hb (by omega) hx
  have hprod :
      (cdem4345_assembled_lemma1QFactor y n b / Real.sqrt y) * (cdem4345_assembled_lemma1SFactor y n / Real.sqrt y)
        ≤ (cdem4345_assembled_lemma1QFactor x n b / Real.sqrt x) * (cdem4345_assembled_lemma1SFactor x n / Real.sqrt x) :=
    mul_le_mul hq hs hsy hqx
  change cdem4345_assembled_lemma1ParametricEnvelope epsilon b n y / Real.sqrt y ≤
    cdem4345_assembled_lemma1ParametricEnvelope epsilon b n x / Real.sqrt x
  unfold cdem4345_assembled_lemma1ParametricEnvelope
  rw [add_div, add_div,
    mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hx0).ne',
    mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hy0).ne',
    cdem4345_assembled_selfBootstrapNormalizedT3_eq hb hn5 hn201 hx,
    cdem4345_assembled_selfBootstrapNormalizedT3_eq hb hn5 hn201 hy]
  gcongr

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Exact endpoints for the self-contained CDEM bootstrap

The three endpoint computations use directed rational enclosures.  The safe
normalized splits are

```text
n=23:  0.035805 + 0.039688 = 0.075493 < 0.0755
n=179: 0.013455 + 0.015035 = 0.028490 < 0.0285
n=201: 0.012719 + 0.014257 = 0.026976 < 0.0270.
```

No decimal printed by a paper or floating-point calculation is trusted as a
proof; square and cube comparisons below establish every direction.
-/

namespace MathExtras.CohenDressElMarraki

private lemma cdem4345_assembled_sqrt_selfBootstrapX0 : Real.sqrt cdem4345_assembled_selfBootstrapX0 = 100000000 := by
  have hsq := Real.sq_sqrt (show 0 ≤ cdem4345_assembled_selfBootstrapX0 by norm_num [cdem4345_assembled_selfBootstrapX0])
  have hs0 := Real.sqrt_nonneg cdem4345_assembled_selfBootstrapX0
  norm_num [cdem4345_assembled_selfBootstrapX0] at hsq ⊢

private lemma cdem4345_assembled_sqrt_sqrt_selfBootstrapX0 :
    Real.sqrt (Real.sqrt cdem4345_assembled_selfBootstrapX0) = 10000 := by
  rw [cdem4345_assembled_sqrt_selfBootstrapX0]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 100000000 by norm_num)
  have hs0 := Real.sqrt_nonneg (100000000 : ℝ)
  norm_num at hsq ⊢

private lemma cdem4345_assembled_cuberoot_selfBootstrap_upper :
    (12 * cdem4345_assembled_selfBootstrapX0) ^ ((1 : ℝ) / 3) ≤ 493243 := by
  let z : ℝ := (12 * cdem4345_assembled_selfBootstrapX0) ^ ((1 : ℝ) / 3)
  have hz0 : 0 ≤ z := Real.rpow_nonneg (by norm_num [cdem4345_assembled_selfBootstrapX0]) _
  have hz3 : z ^ (3 : ℕ) = 12 * cdem4345_assembled_selfBootstrapX0 := by
    dsimp [z]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num [cdem4345_assembled_selfBootstrapX0])]
    norm_num
  have hcube : z ^ (3 : ℕ) ≤ (493243 : ℝ) ^ (3 : ℕ) := by
    rw [hz3]
    norm_num [cdem4345_assembled_selfBootstrapX0]
  by_contra h
  have hlt : (493243 : ℝ) < z := lt_of_not_ge h
  nlinarith [sq_nonneg (z + 493243), mul_pos (sub_pos.mpr hlt)
    (show 0 < z ^ 2 + z * 493243 + (493243 : ℝ) ^ 2 by positivity)]

/-! ## `n=23`, `epsilon=1/495`, `b=3` -/

private lemma cdem4345_assembled_sqrt_n1_lower : (4795831 / 1000000 : ℝ) ≤ Real.sqrt cdem4345_assembled_selfBootstrapN1 := by
  apply (Real.le_sqrt (by norm_num) (by positivity : (0 : ℝ) ≤ cdem4345_assembled_selfBootstrapN1)).2
  norm_num [cdem4345_assembled_selfBootstrapN1]

private lemma cdem4345_assembled_sqrt_n1_upper : Real.sqrt cdem4345_assembled_selfBootstrapN1 ≤ (4795832 / 1000000 : ℝ) := by
  apply (Real.sqrt_le_iff).2
  constructor <;> norm_num [cdem4345_assembled_selfBootstrapN1]

private lemma cdem4345_assembled_fourth_n1_lower :
    (2189938 / 1000000 : ℝ) ≤ Real.sqrt (Real.sqrt cdem4345_assembled_selfBootstrapN1) := by
  apply (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg cdem4345_assembled_selfBootstrapN1)).2
  exact (by norm_num : (2189938 / 1000000 : ℝ) ^ 2 ≤ 4795831 / 1000000).trans
    cdem4345_assembled_sqrt_n1_lower

private lemma cdem4345_assembled_sqrt_n1_sub_lower :
    (4793745 / 1000000 : ℝ) ≤ Real.sqrt ((cdem4345_assembled_selfBootstrapN1 : ℝ) - 2 / 100) := by
  apply (Real.le_sqrt (by norm_num) (by norm_num [cdem4345_assembled_selfBootstrapN1])).2
  norm_num [cdem4345_assembled_selfBootstrapN1]

private lemma cdem4345_assembled_selfBootstrapT12_1_le :
    cdem4345_assembled_selfBootstrapEpsilon1 * (4 * Real.sqrt cdem4345_assembled_selfBootstrapN1 - 146 / 100)
      ≤ (35805 / 1000000 : ℝ) := by
  have hlin :
      4 * Real.sqrt cdem4345_assembled_selfBootstrapN1 - 146 / 100
        ≤ 4 * (4795832 / 1000000 : ℝ) - 146 / 100 :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left cdem4345_assembled_sqrt_n1_upper (by norm_num)) _
  have h := mul_le_mul_of_nonneg_left hlin
    (show 0 ≤ cdem4345_assembled_selfBootstrapEpsilon1 by norm_num [cdem4345_assembled_selfBootstrapEpsilon1])
  norm_num [cdem4345_assembled_selfBootstrapEpsilon1] at h ⊢
  linarith

private lemma cdem4345_assembled_selfBootstrapQRatio_1_le :
    cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 3 / Real.sqrt cdem4345_assembled_selfBootstrapX0
      ≤ (126899 / 1000000 : ℝ) := by
  have hpi : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
    calc
      (3141592 / 1000000 : ℝ) = 392699 / 125000 := by norm_num
      _ = (3.141592 : ℝ) := by norm_num
      _ ≤ Real.pi := Real.pi_gt_d6.le
  have hpi_sq : (3141592 / 1000000 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hpi 2
  have hden1 :
      (3141592 / 1000000 : ℝ) ^ 2 * (4795831 / 1000000) ≤
        Real.pi ^ 2 * Real.sqrt cdem4345_assembled_selfBootstrapN1 :=
    mul_le_mul hpi_sq cdem4345_assembled_sqrt_n1_lower (by norm_num) (by positivity)
  have hmain :
      6 / (Real.pi ^ 2 * Real.sqrt cdem4345_assembled_selfBootstrapN1) ≤
        6 / ((3141592 / 1000000 : ℝ) ^ 2 * (4795831 / 1000000)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hden1
  have hsecond :
      (3 : ℝ) * 10000 / (Real.sqrt (Real.sqrt cdem4345_assembled_selfBootstrapN1) * 100000000)
        ≤ 3 * 10000 / ((2189938 / 1000000 : ℝ) * 100000000) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_right cdem4345_assembled_fourth_n1_lower (by norm_num))
  have hratio :
      cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 3 / Real.sqrt cdem4345_assembled_selfBootstrapX0 =
        6 / (Real.pi ^ 2 * Real.sqrt cdem4345_assembled_selfBootstrapN1)
          + 3 * 10000 / (Real.sqrt (Real.sqrt cdem4345_assembled_selfBootstrapN1) * 100000000) := by
    unfold cdem4345_assembled_lemma1QFactor
    rw [cdem4345_assembled_sqrt_sqrt_selfBootstrapX0, cdem4345_assembled_sqrt_selfBootstrapX0]
    ring
  rw [hratio]
  have hfold :
      6 / ((3141592 / 1000000 : ℝ) ^ 2 * (4795831 / 1000000))
          + 3 * 10000 / ((2189938 / 1000000 : ℝ) * 100000000)
        ≤ (126899 / 1000000 : ℝ) := by norm_num
  linarith

private lemma cdem4345_assembled_selfBootstrapSRatio_1_le :
    cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 / Real.sqrt cdem4345_assembled_selfBootstrapX0
      ≤ (12412 / 1000000 : ℝ) := by
  have hfirst :
      1 / (18 * Real.sqrt ((cdem4345_assembled_selfBootstrapN1 : ℝ) - 2 / 100)) ≤
        1 / (18 * (4793745 / 1000000 : ℝ)) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left cdem4345_assembled_sqrt_n1_sub_lower (by norm_num)
  have hc :
      (12 * cdem4345_assembled_selfBootstrapX0) ^ ((1 : ℝ) / 3) / (6 * 100000000) ≤
        493243 / (6 * 100000000 : ℝ) :=
    div_le_div_of_nonneg_right cdem4345_assembled_cuberoot_selfBootstrap_upper (by norm_num)
  have hratio :
      cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 / Real.sqrt cdem4345_assembled_selfBootstrapX0 =
        1 / (18 * Real.sqrt ((cdem4345_assembled_selfBootstrapN1 : ℝ) - 2 / 100))
          + (12 * cdem4345_assembled_selfBootstrapX0) ^ ((1 : ℝ) / 3) / (6 * 100000000)
          - (2 / 3 : ℝ) * ((cdem4345_assembled_selfBootstrapN1 : ℝ) - 1 / 2) / 100000000 := by
    unfold cdem4345_assembled_lemma1SFactor
    rw [cdem4345_assembled_sqrt_selfBootstrapX0]
    ring
  rw [hratio]
  have hfold :
      1 / (18 * (4793745 / 1000000 : ℝ)) + 493243 / (6 * 100000000 : ℝ)
          - (2 / 3 : ℝ) * ((cdem4345_assembled_selfBootstrapN1 : ℝ) - 1 / 2) / 100000000
        ≤ (12412 / 1000000 : ℝ) := by norm_num [cdem4345_assembled_selfBootstrapN1]
  linarith

private lemma cdem4345_assembled_selfBootstrapT3_1_le :
    cdem4345_assembled_lemma1T3Envelope cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 3 / Real.sqrt cdem4345_assembled_selfBootstrapX0
      ≤ (39688 / 1000000 : ℝ) := by
  rw [cdem4345_assembled_selfBootstrapNormalizedT3_eq (by norm_num) (by norm_num [cdem4345_assembled_selfBootstrapN1])
    (by norm_num [cdem4345_assembled_selfBootstrapN1]) le_rfl]
  calc
    Real.sqrt ((cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 3 /
          Real.sqrt cdem4345_assembled_selfBootstrapX0) *
        (cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapX0 cdem4345_assembled_selfBootstrapN1 / Real.sqrt cdem4345_assembled_selfBootstrapX0))
      ≤ Real.sqrt ((126899 / 1000000 : ℝ) * (12412 / 1000000)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul cdem4345_assembled_selfBootstrapQRatio_1_le cdem4345_assembled_selfBootstrapSRatio_1_le
          (cdem4345_assembled_selfBootstrapSRatio_nonneg (n := cdem4345_assembled_selfBootstrapN1)
            (by norm_num [cdem4345_assembled_selfBootstrapN1]) (by norm_num [cdem4345_assembled_selfBootstrapN1]) le_rfl)
          (by norm_num)
    _ ≤ (39688 / 1000000 : ℝ) := by
      apply (Real.sqrt_le_iff).2
      constructor <;> norm_num

theorem cdem4345_assembled_selfBootstrapEndpoint1_proven :
    cdem4345_assembled_SelfBootstrapLemma1Endpoint cdem4345_assembled_selfBootstrapEpsilon1 3 cdem4345_assembled_selfBootstrapN1 cdem4345_assembled_selfBootstrapB1 := by
  rw [cdem4345_assembled_SelfBootstrapLemma1Endpoint]
  have hsx : 0 < Real.sqrt cdem4345_assembled_selfBootstrapX0 :=
    Real.sqrt_pos.2 (by norm_num [cdem4345_assembled_selfBootstrapX0])
  rw [← div_le_iff₀ hsx]
  unfold cdem4345_assembled_lemma1ParametricEnvelope
  rw [add_div, mul_div_cancel_right₀ _ hsx.ne']
  have hsum := add_le_add cdem4345_assembled_selfBootstrapT12_1_le cdem4345_assembled_selfBootstrapT3_1_le
  norm_num [cdem4345_assembled_selfBootstrapB1] at hsum ⊢
  linarith

/-! ## Shared endpoint machinery for `n=179` and `n=201` -/

private lemma cdem4345_assembled_endpoint_of_ratio_bounds
    {epsilon b B qBound sBound t12Bound t3Bound : ℝ} {n : ℕ}
    (hb : 0 ≤ b) (hn5 : 5 ≤ n) (hn201 : n ≤ 201)
    (hT12 : epsilon * (4 * Real.sqrt n - 146 / 100) ≤ t12Bound)
    (hQ : cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapX0 n b / Real.sqrt cdem4345_assembled_selfBootstrapX0 ≤ qBound)
    (hS : cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapX0 n / Real.sqrt cdem4345_assembled_selfBootstrapX0 ≤ sBound)
    (hroot : Real.sqrt (qBound * sBound) ≤ t3Bound)
    (hsum : t12Bound + t3Bound ≤ B) :
    cdem4345_assembled_SelfBootstrapLemma1Endpoint epsilon b n B := by
  have hT3 : cdem4345_assembled_lemma1T3Envelope cdem4345_assembled_selfBootstrapX0 n b / Real.sqrt cdem4345_assembled_selfBootstrapX0
      ≤ t3Bound := by
    rw [cdem4345_assembled_selfBootstrapNormalizedT3_eq hb hn5 hn201 le_rfl]
    have hqBound : 0 ≤ qBound :=
      (cdem4345_assembled_selfBootstrapQRatio_nonneg (n := n) hb (by omega) le_rfl).trans hQ
    exact (Real.sqrt_le_sqrt (mul_le_mul hQ hS
      (cdem4345_assembled_selfBootstrapSRatio_nonneg (n := n) hn5 hn201 le_rfl)
      hqBound)).trans hroot
  rw [cdem4345_assembled_SelfBootstrapLemma1Endpoint]
  have hsx : 0 < Real.sqrt cdem4345_assembled_selfBootstrapX0 :=
    Real.sqrt_pos.2 (by norm_num [cdem4345_assembled_selfBootstrapX0])
  rw [← div_le_iff₀ hsx]
  unfold cdem4345_assembled_lemma1ParametricEnvelope
  rw [add_div, mul_div_cancel_right₀ _ hsx.ne']
  linarith

private lemma cdem4345_assembled_sqrt_n2_lower : (13379088 / 1000000 : ℝ) ≤ Real.sqrt cdem4345_assembled_selfBootstrapN2 := by
  apply (Real.le_sqrt (by norm_num) (by positivity : (0 : ℝ) ≤ cdem4345_assembled_selfBootstrapN2)).2
  norm_num [cdem4345_assembled_selfBootstrapN2]
private lemma cdem4345_assembled_sqrt_n2_upper : Real.sqrt cdem4345_assembled_selfBootstrapN2 ≤ (13379089 / 1000000 : ℝ) := by
  apply (Real.sqrt_le_iff).2; constructor <;> norm_num [cdem4345_assembled_selfBootstrapN2]
private lemma cdem4345_assembled_fourth_n2_lower : (3657743 / 1000000 : ℝ) ≤ Real.sqrt (Real.sqrt cdem4345_assembled_selfBootstrapN2) := by
  apply (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg cdem4345_assembled_selfBootstrapN2)).2
  exact (by norm_num : (3657743 / 1000000 : ℝ) ^ 2 ≤ 13379088 / 1000000).trans cdem4345_assembled_sqrt_n2_lower
private lemma cdem4345_assembled_sqrt_n2_sub_lower : (13378340 / 1000000 : ℝ) ≤ Real.sqrt ((cdem4345_assembled_selfBootstrapN2 : ℝ) - 2 / 100) := by
  apply (Real.le_sqrt (by norm_num) (by norm_num [cdem4345_assembled_selfBootstrapN2])).2
  norm_num [cdem4345_assembled_selfBootstrapN2]

private lemma cdem4345_assembled_sqrt_n3_lower : (14177446 / 1000000 : ℝ) ≤ Real.sqrt cdem4345_assembled_selfBootstrapN3 := by
  apply (Real.le_sqrt (by norm_num) (by positivity : (0 : ℝ) ≤ cdem4345_assembled_selfBootstrapN3)).2
  norm_num [cdem4345_assembled_selfBootstrapN3]
private lemma cdem4345_assembled_sqrt_n3_upper : Real.sqrt cdem4345_assembled_selfBootstrapN3 ≤ (14177447 / 1000000 : ℝ) := by
  apply (Real.sqrt_le_iff).2; constructor <;> norm_num [cdem4345_assembled_selfBootstrapN3]
private lemma cdem4345_assembled_fourth_n3_lower : (3765294 / 1000000 : ℝ) ≤ Real.sqrt (Real.sqrt cdem4345_assembled_selfBootstrapN3) := by
  apply (Real.le_sqrt (by norm_num) (Real.sqrt_nonneg cdem4345_assembled_selfBootstrapN3)).2
  exact (by norm_num : (3765294 / 1000000 : ℝ) ^ 2 ≤ 14177446 / 1000000).trans cdem4345_assembled_sqrt_n3_lower
private lemma cdem4345_assembled_sqrt_n3_sub_lower : (14176741 / 1000000 : ℝ) ≤ Real.sqrt ((cdem4345_assembled_selfBootstrapN3 : ℝ) - 2 / 100) := by
  apply (Real.le_sqrt (by norm_num) (by norm_num [cdem4345_assembled_selfBootstrapN3])).2
  norm_num [cdem4345_assembled_selfBootstrapN3]

private lemma cdem4345_assembled_qRatio_le_of_lower
    {b qBound sqrtLower fourthLower : ℝ} {n : ℕ}
    (hb : 0 ≤ b) (hn : 1 ≤ n)
    (hsqrtLower : 0 < sqrtLower) (hfourthLower : 0 < fourthLower)
    (hsqrt : sqrtLower ≤ Real.sqrt n)
    (hfourth : fourthLower ≤ Real.sqrt (Real.sqrt n))
    (hfold :
      6 / ((3141592 / 1000000 : ℝ) ^ 2 * sqrtLower)
          + b * 10000 / (fourthLower * 100000000) ≤ qBound) :
    cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapX0 n b / Real.sqrt cdem4345_assembled_selfBootstrapX0 ≤ qBound := by
  have hpi : (3141592 / 1000000 : ℝ) ≤ Real.pi := by
    calc
      (3141592 / 1000000 : ℝ) = 392699 / 125000 := by norm_num
      _ = (3.141592 : ℝ) := by norm_num
      _ ≤ Real.pi := Real.pi_gt_d6.le
  have hpi_sq : (3141592 / 1000000 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hpi 2
  have hmain : 6 / (Real.pi ^ 2 * Real.sqrt n) ≤
      6 / ((3141592 / 1000000 : ℝ) ^ 2 * sqrtLower) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul hpi_sq hsqrt hsqrtLower.le (sq_nonneg _)
  have hsecond : b * 10000 / (Real.sqrt (Real.sqrt n) * 100000000) ≤
      b * 10000 / (fourthLower * 100000000) := by
    apply div_le_div_of_nonneg_left (mul_nonneg hb (by norm_num)) (by positivity)
    exact mul_le_mul_of_nonneg_right hfourth (by norm_num)
  have hratio : cdem4345_assembled_lemma1QFactor cdem4345_assembled_selfBootstrapX0 n b / Real.sqrt cdem4345_assembled_selfBootstrapX0 =
      6 / (Real.pi ^ 2 * Real.sqrt n)
        + b * 10000 / (Real.sqrt (Real.sqrt n) * 100000000) := by
    unfold cdem4345_assembled_lemma1QFactor
    rw [cdem4345_assembled_sqrt_sqrt_selfBootstrapX0, cdem4345_assembled_sqrt_selfBootstrapX0]
    ring
  rw [hratio]
  linarith

private lemma cdem4345_assembled_sRatio_le_of_lower
    {sBound subLower : ℝ} {n : ℕ}
    (hn5 : 5 ≤ n)
    (hsubLower : 0 < subLower)
    (hsub : subLower ≤ Real.sqrt ((n : ℝ) - 2 / 100))
    (hfold : 1 / (18 * subLower) + 493243 / (6 * 100000000 : ℝ)
        - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) / 100000000 ≤ sBound) :
    cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapX0 n / Real.sqrt cdem4345_assembled_selfBootstrapX0 ≤ sBound := by
  have hfirst : 1 / (18 * Real.sqrt ((n : ℝ) - 2 / 100)) ≤ 1 / (18 * subLower) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left hsub (by norm_num)
  have hc := div_le_div_of_nonneg_right cdem4345_assembled_cuberoot_selfBootstrap_upper
    (by norm_num : (0 : ℝ) ≤ 6 * 100000000)
  have hratio : cdem4345_assembled_lemma1SFactor cdem4345_assembled_selfBootstrapX0 n / Real.sqrt cdem4345_assembled_selfBootstrapX0 =
      1 / (18 * Real.sqrt ((n : ℝ) - 2 / 100))
        + (12 * cdem4345_assembled_selfBootstrapX0) ^ ((1 : ℝ) / 3) / (6 * 100000000)
        - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2) / 100000000 := by
    unfold cdem4345_assembled_lemma1SFactor
    rw [cdem4345_assembled_sqrt_selfBootstrapX0]
    ring
  rw [hratio]
  linarith

theorem cdem4345_assembled_selfBootstrapEndpoint2_proven :
    cdem4345_assembled_SelfBootstrapLemma1Endpoint cdem4345_assembled_selfBootstrapEpsilon2 cdem4345_assembled_selfBootstrapB1
      cdem4345_assembled_selfBootstrapN2 cdem4345_assembled_selfBootstrapB2 := by
  apply cdem4345_assembled_endpoint_of_ratio_bounds
    (qBound := 45441 / 1000000) (sBound := 4974 / 1000000)
    (t12Bound := 13455 / 1000000) (t3Bound := 15035 / 1000000)
  · norm_num [cdem4345_assembled_selfBootstrapB1]
  · norm_num [cdem4345_assembled_selfBootstrapN2]
  · norm_num [cdem4345_assembled_selfBootstrapN2]
  · have hlin :
        4 * Real.sqrt cdem4345_assembled_selfBootstrapN2 - 146 / 100
          ≤ 4 * (13379089 / 1000000 : ℝ) - 146 / 100 :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left cdem4345_assembled_sqrt_n2_upper (by norm_num)) _
    have h := mul_le_mul_of_nonneg_left hlin
      (show 0 ≤ cdem4345_assembled_selfBootstrapEpsilon2 by norm_num [cdem4345_assembled_selfBootstrapEpsilon2])
    norm_num [cdem4345_assembled_selfBootstrapEpsilon2] at h ⊢
    linarith
  · apply cdem4345_assembled_qRatio_le_of_lower (by norm_num [cdem4345_assembled_selfBootstrapB1])
      (by norm_num [cdem4345_assembled_selfBootstrapN2]) (by norm_num) (by norm_num)
      cdem4345_assembled_sqrt_n2_lower cdem4345_assembled_fourth_n2_lower
    norm_num [cdem4345_assembled_selfBootstrapB1]
  · apply cdem4345_assembled_sRatio_le_of_lower (by norm_num [cdem4345_assembled_selfBootstrapN2]) (by norm_num)
      cdem4345_assembled_sqrt_n2_sub_lower
    norm_num [cdem4345_assembled_selfBootstrapN2]
  · apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  · norm_num [cdem4345_assembled_selfBootstrapB2]

theorem cdem4345_assembled_selfBootstrapEndpoint3_proven :
    cdem4345_assembled_SelfBootstrapLemma1Endpoint cdem4345_assembled_selfBootstrapEpsilon3 cdem4345_assembled_selfBootstrapB2
      cdem4345_assembled_selfBootstrapN3 cdem4345_assembled_selfBootstrapB3 := by
  apply cdem4345_assembled_endpoint_of_ratio_bounds
    (qBound := 42881 / 1000000) (sBound := 4740 / 1000000)
    (t12Bound := 12719 / 1000000) (t3Bound := 14257 / 1000000)
  · norm_num [cdem4345_assembled_selfBootstrapB2]
  · norm_num [cdem4345_assembled_selfBootstrapN3]
  · norm_num [cdem4345_assembled_selfBootstrapN3]
  · have hlin :
        4 * Real.sqrt cdem4345_assembled_selfBootstrapN3 - 146 / 100
          ≤ 4 * (14177447 / 1000000 : ℝ) - 146 / 100 :=
      sub_le_sub_right (mul_le_mul_of_nonneg_left cdem4345_assembled_sqrt_n3_upper (by norm_num)) _
    have h := mul_le_mul_of_nonneg_left hlin
      (show 0 ≤ cdem4345_assembled_selfBootstrapEpsilon3 by norm_num [cdem4345_assembled_selfBootstrapEpsilon3])
    norm_num [cdem4345_assembled_selfBootstrapEpsilon3] at h ⊢
    linarith
  · apply cdem4345_assembled_qRatio_le_of_lower (by norm_num [cdem4345_assembled_selfBootstrapB2])
      (by norm_num [cdem4345_assembled_selfBootstrapN3]) (by norm_num) (by norm_num)
      cdem4345_assembled_sqrt_n3_lower cdem4345_assembled_fourth_n3_lower
    norm_num [cdem4345_assembled_selfBootstrapB2]
  · apply cdem4345_assembled_sRatio_le_of_lower (by norm_num [cdem4345_assembled_selfBootstrapN3]) (by norm_num)
      cdem4345_assembled_sqrt_n3_sub_lower
    norm_num [cdem4345_assembled_selfBootstrapN3]
  · apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  · norm_num [cdem4345_assembled_selfBootstrapB3]

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Finite CDEM Lemma-1 weight certificates

The three reciprocal-square-root sums needed by the self-contained bootstrap
are proved with directed rational bounds.  For each `j`, `sqrt j` is rounded
down to six decimal places using `Nat.sqrt (j * 10^12)`.  The remaining finite
rational inequalities are normalized to ordinary kernel proof terms.
-/

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

private def cdem4345_assembled_weightScale : Nat := 1000000
private def cdem4345_assembled_weightScaleSq : Nat := 1000000000000

private def cdem4345_assembled_sqrtFloorQ (j : Nat) : ℚ :=
  Nat.sqrt (j * cdem4345_assembled_weightScaleSq) / cdem4345_assembled_weightScale

private noncomputable def cdem4345_assembled_sqrtFloor (j : Nat) : Real :=
  (Nat.sqrt (j * cdem4345_assembled_weightScaleSq) : Real) / cdem4345_assembled_weightScale

private lemma cdem4345_assembled_sqrtFloor_eq_cast (j : Nat) :
    cdem4345_assembled_sqrtFloor j = (cdem4345_assembled_sqrtFloorQ j : Real) := by
  simp [cdem4345_assembled_sqrtFloor, cdem4345_assembled_sqrtFloorQ]

private lemma cdem4345_assembled_sqrtFloor_le (j : Nat) : cdem4345_assembled_sqrtFloor j ≤ Real.sqrt j := by
  apply (Real.le_sqrt (by unfold cdem4345_assembled_sqrtFloor; positivity) (by positivity)).2
  have h := Nat.sqrt_le (j * cdem4345_assembled_weightScaleSq)
  have hcast : ((Nat.sqrt (j * cdem4345_assembled_weightScaleSq) : Nat) : Real) *
        ((Nat.sqrt (j * cdem4345_assembled_weightScaleSq) : Nat) : Real) ≤
      (j * cdem4345_assembled_weightScaleSq : Nat) := by
    exact_mod_cast h
  have h' : ((Nat.sqrt (j * cdem4345_assembled_weightScaleSq) : Nat) : Real) ^ 2 ≤
      (j * cdem4345_assembled_weightScaleSq : Nat) := by
    simpa [pow_two] using hcast
  unfold cdem4345_assembled_sqrtFloor cdem4345_assembled_weightScale cdem4345_assembled_weightScaleSq
  push_cast at h'
  rw [div_pow]
  norm_num at h' ⊢
  apply (div_le_iff₀ (by norm_num : (0 : Real) < 1000000000000)).2
  exact h'

private lemma cdem4345_assembled_sqrtFloor_pos {j : Nat} (hj : 1 ≤ j) : 0 < cdem4345_assembled_sqrtFloor j := by
  have hs : cdem4345_assembled_weightScale ≤ Nat.sqrt (j * cdem4345_assembled_weightScaleSq) := by
    rw [Nat.le_sqrt]
    simp only [cdem4345_assembled_weightScale, cdem4345_assembled_weightScaleSq]
    omega
  have hs0 : 0 < Nat.sqrt (j * cdem4345_assembled_weightScaleSq) :=
    lt_of_lt_of_le (by norm_num [cdem4345_assembled_weightScale]) hs
  unfold cdem4345_assembled_sqrtFloor
  exact div_pos (by exact_mod_cast hs0) (by norm_num [cdem4345_assembled_weightScale])

private lemma cdem4345_assembled_inv_sqrt_le_floor {j : Nat} (hj : 1 ≤ j) :
    1 / Real.sqrt j ≤ 1 / cdem4345_assembled_sqrtFloor j := by
  exact one_div_le_one_div_of_le (cdem4345_assembled_sqrtFloor_pos hj) (cdem4345_assembled_sqrtFloor_le j)

private lemma cdem4345_assembled_weight_le_floor (n : Nat) (hn : 1 ≤ n) :
    cdem4345_assembled_lemma1T2Weight n ≤
      (∑ j ∈ Finset.Icc 1 (n - 1), 1 / cdem4345_assembled_sqrtFloor j) + 1 / (2 * cdem4345_assembled_sqrtFloor n) := by
  unfold cdem4345_assembled_lemma1T2Weight
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j hj
    exact cdem4345_assembled_inv_sqrt_le_floor (Finset.mem_Icc.mp hj).1
  · apply one_div_le_one_div_of_le (mul_pos (by norm_num) (cdem4345_assembled_sqrtFloor_pos hn))
    exact mul_le_mul_of_nonneg_left (cdem4345_assembled_sqrtFloor_le n) (by norm_num)

private lemma cdem4345_assembled_qcert23 :
    (∑ j ∈ Finset.Icc 1 (cdem4345_assembled_selfBootstrapN1 - 1), 1 / cdem4345_assembled_sqrtFloorQ j) +
          1 / (2 * cdem4345_assembled_sqrtFloorQ cdem4345_assembled_selfBootstrapN1) ≤
        2 * cdem4345_assembled_sqrtFloorQ cdem4345_assembled_selfBootstrapN1 - 146 / 100 := by
  set_option maxRecDepth 1000000 in
    set_option maxHeartbeats 0 in
      norm_num [cdem4345_assembled_selfBootstrapN1, cdem4345_assembled_sqrtFloorQ, cdem4345_assembled_weightScale, cdem4345_assembled_weightScaleSq,
        Finset.sum_Icc_succ_top]

private lemma cdem4345_assembled_qcert179 :
    (∑ j ∈ Finset.Icc 1 (cdem4345_assembled_selfBootstrapN2 - 1), 1 / cdem4345_assembled_sqrtFloorQ j) +
          1 / (2 * cdem4345_assembled_sqrtFloorQ cdem4345_assembled_selfBootstrapN2) ≤
        2 * cdem4345_assembled_sqrtFloorQ cdem4345_assembled_selfBootstrapN2 - 146 / 100 := by
  set_option maxRecDepth 1000000 in
    set_option maxHeartbeats 0 in
      norm_num [cdem4345_assembled_selfBootstrapN2, cdem4345_assembled_sqrtFloorQ, cdem4345_assembled_weightScale, cdem4345_assembled_weightScaleSq,
        Finset.sum_Icc_succ_top]

private lemma cdem4345_assembled_qcert201 :
    (∑ j ∈ Finset.Icc 1 (cdem4345_assembled_selfBootstrapN3 - 1), 1 / cdem4345_assembled_sqrtFloorQ j) +
          1 / (2 * cdem4345_assembled_sqrtFloorQ cdem4345_assembled_selfBootstrapN3) ≤
        2 * cdem4345_assembled_sqrtFloorQ cdem4345_assembled_selfBootstrapN3 - 146 / 100 := by
  set_option maxRecDepth 1000000 in
    set_option maxHeartbeats 0 in
      norm_num [cdem4345_assembled_selfBootstrapN3, cdem4345_assembled_sqrtFloorQ, cdem4345_assembled_weightScale, cdem4345_assembled_weightScaleSq,
        Finset.sum_Icc_succ_top]

private lemma cdem4345_assembled_rcert (n : Nat)
    (hq : (∑ j ∈ Finset.Icc 1 (n - 1), 1 / cdem4345_assembled_sqrtFloorQ j) +
          1 / (2 * cdem4345_assembled_sqrtFloorQ n) ≤ 2 * cdem4345_assembled_sqrtFloorQ n - 146 / 100) :
    (∑ j ∈ Finset.Icc 1 (n - 1), 1 / cdem4345_assembled_sqrtFloor j) +
          1 / (2 * cdem4345_assembled_sqrtFloor n) ≤ 2 * cdem4345_assembled_sqrtFloor n - 146 / 100 := by
  simp_rw [cdem4345_assembled_sqrtFloor_eq_cast]
  have hcast :
      ((↑((∑ j ∈ Finset.Icc 1 (n - 1), 1 / cdem4345_assembled_sqrtFloorQ j) +
          1 / (2 * cdem4345_assembled_sqrtFloorQ n)) : Real) ≤
        (↑(2 * cdem4345_assembled_sqrtFloorQ n - 146 / 100) : Real)) := Rat.cast_le.2 hq
  push_cast at hcast
  exact hcast

/-- The `n = 23` Lemma-1 weight, proved by an ordinary-kernel rational certificate. -/
theorem cdem4345_assembled_selfBootstrapLemma1WeightN23_cert :
    cdem4345_assembled_SelfBootstrapLemma1Weight cdem4345_assembled_selfBootstrapN1 := by
  rw [cdem4345_assembled_SelfBootstrapLemma1Weight]
  calc
    cdem4345_assembled_lemma1T2Weight cdem4345_assembled_selfBootstrapN1 ≤
        (∑ j ∈ Finset.Icc 1 (cdem4345_assembled_selfBootstrapN1 - 1), 1 / cdem4345_assembled_sqrtFloor j) +
          1 / (2 * cdem4345_assembled_sqrtFloor cdem4345_assembled_selfBootstrapN1) :=
      cdem4345_assembled_weight_le_floor cdem4345_assembled_selfBootstrapN1 (by norm_num [cdem4345_assembled_selfBootstrapN1])
    _ ≤ 2 * cdem4345_assembled_sqrtFloor cdem4345_assembled_selfBootstrapN1 - 146 / 100 := cdem4345_assembled_rcert _ cdem4345_assembled_qcert23
    _ ≤ 2 * Real.sqrt cdem4345_assembled_selfBootstrapN1 - 146 / 100 := by
      gcongr
      exact cdem4345_assembled_sqrtFloor_le cdem4345_assembled_selfBootstrapN1

/-- The `n = 179` Lemma-1 weight, proved by an ordinary-kernel rational certificate. -/
theorem cdem4345_assembled_selfBootstrapLemma1WeightN179_cert :
    cdem4345_assembled_SelfBootstrapLemma1Weight cdem4345_assembled_selfBootstrapN2 := by
  rw [cdem4345_assembled_SelfBootstrapLemma1Weight]
  calc
    cdem4345_assembled_lemma1T2Weight cdem4345_assembled_selfBootstrapN2 ≤
        (∑ j ∈ Finset.Icc 1 (cdem4345_assembled_selfBootstrapN2 - 1), 1 / cdem4345_assembled_sqrtFloor j) +
          1 / (2 * cdem4345_assembled_sqrtFloor cdem4345_assembled_selfBootstrapN2) :=
      cdem4345_assembled_weight_le_floor cdem4345_assembled_selfBootstrapN2 (by norm_num [cdem4345_assembled_selfBootstrapN2])
    _ ≤ 2 * cdem4345_assembled_sqrtFloor cdem4345_assembled_selfBootstrapN2 - 146 / 100 := cdem4345_assembled_rcert _ cdem4345_assembled_qcert179
    _ ≤ 2 * Real.sqrt cdem4345_assembled_selfBootstrapN2 - 146 / 100 := by
      gcongr
      exact cdem4345_assembled_sqrtFloor_le cdem4345_assembled_selfBootstrapN2

/-- The `n = 201` Lemma-1 weight, proved by an ordinary-kernel rational certificate. -/
theorem cdem4345_assembled_selfBootstrapLemma1WeightN201_cert :
    cdem4345_assembled_SelfBootstrapLemma1Weight cdem4345_assembled_selfBootstrapN3 := by
  rw [cdem4345_assembled_SelfBootstrapLemma1Weight]
  calc
    cdem4345_assembled_lemma1T2Weight cdem4345_assembled_selfBootstrapN3 ≤
        (∑ j ∈ Finset.Icc 1 (cdem4345_assembled_selfBootstrapN3 - 1), 1 / cdem4345_assembled_sqrtFloor j) +
          1 / (2 * cdem4345_assembled_sqrtFloor cdem4345_assembled_selfBootstrapN3) :=
      cdem4345_assembled_weight_le_floor cdem4345_assembled_selfBootstrapN3 (by norm_num [cdem4345_assembled_selfBootstrapN3])
    _ ≤ 2 * cdem4345_assembled_sqrtFloor cdem4345_assembled_selfBootstrapN3 - 146 / 100 := cdem4345_assembled_rcert _ cdem4345_assembled_qcert201
    _ ≤ 2 * Real.sqrt cdem4345_assembled_selfBootstrapN3 - 146 / 100 := by
      gcongr
      exact cdem4345_assembled_sqrtFloor_le cdem4345_assembled_selfBootstrapN3

end MathExtras.CohenDressElMarraki
end

section
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Threshold-aware CDEM bootstrap for the actual Mobius function. The analytic
steps, scalar endpoints, finite weights and actual prefix are proved here.
The only remaining inputs are two finite Abel aggregates, the bounded Hurst
window, and two bounded squarefree windows. No previous unbounded Mertens or
squarefree estimate is assumed. The finite windows are not asserted proved.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott
open MathExtras.CohenDressElMarraki

noncomputable def cdem4345_assembled_cdemMertensFunction (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, (moebius d : ℝ)
def cdem4345_assembled_cdemTau : ℝ := 10000000000000000

def cdem4345_assembled_CDEMSquarefreeFiniteHead (b threshold : ℝ) : Prop :=
  ∀ y : ℝ, threshold < y → y ≤ cdem4345_assembled_cdemTau →
    |cdem4345_assembled_squarefreeCount y - (6/Real.pi^2)*y| ≤ b*Real.sqrt y

def cdem4345_assembled_CDEMSquarefreeBound (b threshold : ℝ) : Prop :=
  ∀ y : ℝ, threshold < y →
    |cdem4345_assembled_squarefreeCount y - (6/Real.pi^2)*y| ≤ b*Real.sqrt y

private theorem cdem4345_assembled_cdem_lemma1M_eq_mertens_floor {t : ℝ} (_ht : 0 ≤ t) :
    cdem4345_assembled_lemma1M t = cdem4345_assembled_cdemMertensFunction ⌊t⌋₊ := by rfl

theorem cdem4345_assembled_cdem_real_mertens_bound_of_finite_hurst_tail
    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |cdem4345_assembled_cdemMertensFunction k| ≤ (571/1000 : ℝ)*Real.sqrt k)
    (D T : ℕ) (hD : 1 ≤ D) (hT : 80000 ≤ T)
    (hscalar : ((571 : ℝ) / 1000 * D) ^ 2 ≤ T)
    (htail : ∀ X : ℕ, cdem4345_assembled_cdemTau < (X : ℝ) →
      |cdem4345_assembled_cdemMertensFunction X| ≤ (X : ℝ) / D) :
    cdem4345_assembled_SelfBootstrapMertensBound (1 / (D : ℝ)) T := by
  rw [cdem4345_assembled_SelfBootstrapMertensBound]
  intro t ht
  have ht0 : 0 ≤ t := by
    have : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    linarith
  let k := ⌊t⌋₊
  have hkT : T ≤ k := by
    apply Nat.le_floor
    exact_mod_cast ht.le
  have hk80000 : 80000 ≤ k := hT.trans hkT
  have hkt : (k : ℝ) ≤ t := by
    dsimp [k]
    exact Nat.floor_le ht0
  have hbound :
      |cdem4345_assembled_cdemMertensFunction k| ≤ (k : ℝ) / D := by
    by_cases hk16 : k ≤ 10 ^ 16
    · have hH := hHurst k hk80000 hk16
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hscalar_k : ((571 : ℝ) / 1000 * D) ^ 2 ≤ (k : ℝ) := by
        exact hscalar.trans (by exact_mod_cast hkT)
      have hroot : (571 : ℝ) / 1000 * D ≤ Real.sqrt k := by
        apply (Real.le_sqrt (by positivity) hk0).2
        simpa using hscalar_k
      have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
      calc
        |cdem4345_assembled_cdemMertensFunction k|
            ≤ (571 / 1000 : ℝ) * Real.sqrt k := by
          simpa only [show (0.571 : ℝ) = 571 / 1000 by norm_num] using hH
        _ ≤ (k : ℝ) / D := by
          rw [le_div_iff₀ hDpos]
          have hs0 : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
          calc
            (571 / 1000 : ℝ) * Real.sqrt k * D
                = ((571 / 1000 : ℝ) * D) * Real.sqrt k := by ring
            _ ≤ Real.sqrt k * Real.sqrt k :=
              mul_le_mul_of_nonneg_right hroot hs0
            _ = (k : ℝ) := by simpa only [pow_two] using Real.sq_sqrt hk0
    · have hklarge : 10 ^ 16 < k := lt_of_not_ge hk16
      apply htail k
      have hklargeR : (10 ^ 16 : ℝ) < (k : ℝ) := by exact_mod_cast hklarge
      norm_num [cdem4345_assembled_cdemTau] at hklargeR ⊢
      exact hklargeR
  rw [cdem4345_assembled_cdem_lemma1M_eq_mertens_floor ht0]
  calc
    |cdem4345_assembled_cdemMertensFunction k| ≤ (k : ℝ) / D := hbound
    _ ≤ t / D := div_le_div_of_nonneg_right hkt (by positivity)
    _ = (1 / (D : ℝ)) * t := by ring

theorem cdem4345_assembled_cdem_squarefree_bound_of_finite_head
    {b threshold : ℝ}
    (hhead : cdem4345_assembled_CDEMSquarefreeFiniteHead b threshold)
    (htail : ∀ y : ℝ, cdem4345_assembled_selfBootstrapX0 < y →
      |cdem4345_assembled_lemma1Remainder y| ≤ b*Real.sqrt y) :
    cdem4345_assembled_CDEMSquarefreeBound b threshold := by
  intro y hy
  by_cases hlarge : cdem4345_assembled_selfBootstrapX0 < y
  · simpa only [cdem4345_assembled_lemma1Remainder] using htail y hlarge
  · exact hhead y hy (by simpa only [cdem4345_assembled_cdemTau, cdem4345_assembled_selfBootstrapX0] using le_of_not_gt hlarge)

theorem cdem4345_assembled_cdem_squarefree_B2_from_previous_stage
    (hM : cdem4345_assembled_SelfBootstrapMertensBound cdem4345_assembled_selfBootstrapEpsilon2 cdem4345_assembled_selfBootstrapMThreshold2)
    (hQ : cdem4345_assembled_CDEMSquarefreeBound cdem4345_assembled_selfBootstrapB1 9243)
    {x : ℝ} (hx : cdem4345_assembled_selfBootstrapX0 < x) :
    |cdem4345_assembled_lemma1Remainder x| ≤ cdem4345_assembled_selfBootstrapB2*Real.sqrt x := by
  apply cdem4345_assembled_lemma1_parametric_analytic
    (epsilon := cdem4345_assembled_selfBootstrapEpsilon2) (b := cdem4345_assembled_selfBootstrapB1)
    (x0 := cdem4345_assembled_selfBootstrapX0) (B := cdem4345_assembled_selfBootstrapB2)
    (mThreshold := cdem4345_assembled_selfBootstrapMThreshold2)
    (qThreshold := 9243) (n := cdem4345_assembled_selfBootstrapN2)
  · norm_num [cdem4345_assembled_selfBootstrapX0]
  · norm_num [cdem4345_assembled_selfBootstrapN2]
  · norm_num [cdem4345_assembled_selfBootstrapN2, cdem4345_assembled_selfBootstrapX0]
  · norm_num [cdem4345_assembled_selfBootstrapEpsilon2]
  · exact cdem4345_assembled_selfBootstrapMGuard2
  · rw [cdem4345_assembled_lemma1X, cdem4345_assembled_selfBootstrapX0, cdem4345_assembled_selfBootstrapN2]
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 9243)).2
    norm_num
  · exact hM
  · intro t ht
    unfold cdem4345_assembled_lemma1Remainder
    exact hQ t ht
  · exact cdem4345_assembled_selfBootstrapLemma1WeightN179_cert
  · intro y hy
    exact cdem4345_assembled_selfBootstrapPeriodicMajorant (by norm_num [cdem4345_assembled_selfBootstrapN2])
      (by norm_num [cdem4345_assembled_selfBootstrapN2]) hy
  · exact cdem4345_assembled_selfBootstrapEndpoint2_proven
  · exact cdem4345_assembled_selfBootstrapLemma1Antitone_proven (by norm_num [cdem4345_assembled_selfBootstrapB1])
      (by norm_num [cdem4345_assembled_selfBootstrapN2]) (by norm_num [cdem4345_assembled_selfBootstrapN2])
  · exact hx

theorem cdem_mertens4345_tail_of_finite_sources_complete
    (hU : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
        (324880457633740 / 1000000000000000000 : ℝ))
    (hV : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
        (48710223109607260068028 / 1000000000000000000 : ℝ))

    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, (moebius d : ℝ)| ≤ (571/1000 : ℝ)*Real.sqrt k)
    (hQhead1 : ∀ y : ℝ, 9243 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (755/10000 : ℝ)*Real.sqrt y)
    (hQhead2 : ∀ y : ℝ, 438429 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (285/10000 : ℝ)*Real.sqrt y)
    (X : ℕ) (hX : 10000000000000000 ≤ X) :
    |∑ d ∈ Icc 1 X, (moebius d : ℝ)| ≤ (X : ℝ)/4345 := by
  rcases cdem4345_assembled_cdem_fixedpoint_of_two_finite_abel_bounds hU hV with
    ⟨hS0, hS1, hM, hMain, hRemainder⟩
  have hTail1 : ∀ n : ℕ, cdem4345_assembled_cdemTau < (n : ℝ) →
      |cdem4345_assembled_cdemMertensFunction n| ≤ (n : ℝ)/495 := by
    intro n hn
    have hnR : (10000000000000000 : ℝ) ≤ n := by
      exact le_of_lt hn
    have hnN : 10000000000000000 ≤ n := by exact_mod_cast hnR
    exact cdem4345_assembled_cdem_mertens_tail_of_finite_table 3 9 495 n (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
      (fun y hy => cdem4345_assembled_coarseSquarefreeRemainder_three (le_of_lt hy))
      (by norm_num) hnN hS0 hS1 hM hMain hRemainder
  have hRealM1 : cdem4345_assembled_SelfBootstrapMertensBound cdem4345_assembled_selfBootstrapEpsilon1 cdem4345_assembled_selfBootstrapMThreshold1 := by
    rw [cdem4345_assembled_selfBootstrapEpsilon1, cdem4345_assembled_selfBootstrapMThreshold1]
    exact cdem4345_assembled_cdem_real_mertens_bound_of_finite_hurst_tail hHurst 495 80000
      (by norm_num) (by norm_num) (by norm_num) hTail1
  have hHead1 : cdem4345_assembled_CDEMSquarefreeFiniteHead cdem4345_assembled_selfBootstrapB1 9243 := by
    intro y hy hhi
    simpa only [cdem4345_assembled_squarefreeCount_eq_sum_Icc, cdem4345_assembled_selfBootstrapB1, cdem4345_assembled_cdemTau] using hQhead1 y hy hhi
  have hQ1 : cdem4345_assembled_CDEMSquarefreeBound cdem4345_assembled_selfBootstrapB1 9243 := by
    apply cdem4345_assembled_cdem_squarefree_bound_of_finite_head hHead1
    intro y hy
    exact cdem4345_assembled_selfBootstrapSquarefreeB1_analytic hRealM1 cdem4345_assembled_selfBootstrapLemma1WeightN23_cert
      cdem4345_assembled_selfBootstrapEndpoint1_proven
      (cdem4345_assembled_selfBootstrapLemma1Antitone_proven (by norm_num)
        (by norm_num [cdem4345_assembled_selfBootstrapN1]) (by norm_num [cdem4345_assembled_selfBootstrapN1])) hy
  have hTail2 : ∀ n : ℕ, cdem4345_assembled_cdemTau < (n : ℝ) →
      |cdem4345_assembled_cdemMertensFunction n| ≤ (n : ℝ)/3869 := by
    intro n hn
    have hnR : (10000000000000000 : ℝ) ≤ n := le_of_lt hn
    have hnN : 10000000000000000 ≤ n := by exact_mod_cast hnR
    exact cdem4345_assembled_cdem_mertens_tail_of_finite_table cdem4345_assembled_selfBootstrapB1 9243 3869 n
      (by norm_num [cdem4345_assembled_selfBootstrapB1]) (by norm_num) (by norm_num) (by norm_num)
      hQ1 (by norm_num [cdem4345_assembled_selfBootstrapB1]) hnN hS0 hS1 hM hMain hRemainder
  have hRealM2 : cdem4345_assembled_SelfBootstrapMertensBound cdem4345_assembled_selfBootstrapEpsilon2 cdem4345_assembled_selfBootstrapMThreshold2 := by
    rw [cdem4345_assembled_selfBootstrapEpsilon2, cdem4345_assembled_selfBootstrapMThreshold2]
    exact cdem4345_assembled_cdem_real_mertens_bound_of_finite_hurst_tail hHurst 3869 4900000
      (by norm_num) (by norm_num) (by norm_num) hTail2
  have hHead2 : cdem4345_assembled_CDEMSquarefreeFiniteHead cdem4345_assembled_selfBootstrapB2 438429 := by
    intro y hy hhi
    simpa only [cdem4345_assembled_squarefreeCount_eq_sum_Icc, cdem4345_assembled_selfBootstrapB2, cdem4345_assembled_cdemTau] using hQhead2 y hy hhi
  have hQ2 : cdem4345_assembled_CDEMSquarefreeBound cdem4345_assembled_selfBootstrapB2 438429 := by
    apply cdem4345_assembled_cdem_squarefree_bound_of_finite_head hHead2
    intro y hy
    exact cdem4345_assembled_cdem_squarefree_B2_from_previous_stage hRealM2 hQ1 hy
  exact cdem4345_assembled_cdem_mertens_tail_of_finite_table cdem4345_assembled_selfBootstrapB2 438429 4345 X
    (by norm_num [cdem4345_assembled_selfBootstrapB2]) (by norm_num) (by norm_num) (by norm_num)
    hQ2 (by norm_num [cdem4345_assembled_selfBootstrapB2]) hX hS0 hS1 hM hMain hRemainder

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution 
    (hU : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, (G k-G (k-1))/(k : ℝ)) ≤
        (324880457633740 / 1000000000000000000 : ℝ))
    (hV : let G : ℕ → ℝ := fun k => if k = 0 then 0 else
        |1 - ∑ d ∈ Icc 1 199330, (moebius d : ℝ)*((k/d : ℕ) : ℝ)|
      (∑ k ∈ Icc 1 5000000000, |G k-G (k-1)|/Real.sqrt k) ≤
        (48710223109607260068028 / 1000000000000000000 : ℝ))

    (hHurst : ∀ k : ℕ, 80000 ≤ k → k ≤ 10 ^ 16 →
      |∑ d ∈ Icc 1 k, (moebius d : ℝ)| ≤ (571/1000 : ℝ)*Real.sqrt k)
    (hQhead1 : ∀ y : ℝ, 9243 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (755/10000 : ℝ)*Real.sqrt y)
    (hQhead2 : ∀ y : ℝ, 438429 < y → y ≤ (10000000000000000 : ℝ) →
      |(∑ d ∈ Icc 1 ⌊y⌋₊, |(moebius d : ℝ)|) - (6/Real.pi^2)*y| ≤
        (285/10000 : ℝ)*Real.sqrt y)
    (X : ℕ) (hX : 10000000000000000 ≤ X) :
    |∑ d ∈ Icc 1 X, (moebius d : ℝ)| ≤ (X : ℝ)/4345 := Helfgott.cdem_mertens4345_tail_of_finite_sources_complete hU hV hHurst hQhead1 hQhead2 X hX
#print axioms solution
