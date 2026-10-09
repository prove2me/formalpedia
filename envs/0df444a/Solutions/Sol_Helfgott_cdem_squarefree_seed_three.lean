-- Prove2me | solution 1 for Helfgott.cdem_squarefree_seed_three
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T01:35:45.495129+00:00
-- url     : https://prove2.me/submissions/321bf2d4-9a64-4c96-97f7-4ce31a9bffa6

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Real.Pi.Bounds

section
set_option autoImplicit false
open Finset
open scoped BigOperators Classical
namespace Helfgott

theorem finite_positive_divisor_reindex (B : ℕ) (F : ℕ → ℕ → ℝ) :
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

lemma cdem_moebius_divisor_sum (q : ℕ) :
    (∑ d ∈ q.divisors, (moebius d : ℝ)) = if q = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f q)
    (coe_moebius_mul_coe_zeta (R := ℝ))
  simpa only [coe_mul_zeta_apply, intCoe_apply, one_apply] using h

theorem cdem_moebius_floor_nat (B : ℕ) (hB : 1 ≤ B) :
    (∑ n ∈ Icc 1 B, (moebius n : ℝ) * (B/n : ℕ)) = 1 := by
  have h := finite_positive_divisor_reindex B (fun d _ => (moebius d : ℝ))
  have hright : (∑ d ∈ Icc 1 B, ∑ _r ∈ Icc 1 (B/d), (moebius d : ℝ)) =
      ∑ d ∈ Icc 1 B, (moebius d : ℝ) * (B/d : ℕ) := by
    apply sum_congr rfl
    intro d hd
    simp [Nat.card_Icc, mul_comm]
  rw [hright] at h
  rw [← h]
  simp_rw [cdem_moebius_divisor_sum]
  simp [hB]

theorem cdem_moebius_floor_real (x : ℝ) (hx : 1 ≤ x) :
    (∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ) * (⌊x/(n : ℝ)⌋₊ : ℝ)) = 1 := by
  simp_rw [Nat.floor_div_natCast]
  exact cdem_moebius_floor_nat ⌊x⌋₊
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
noncomputable def signedMainWeight (N : ℕ) (Gseq : ℕ → ℝ) (maxG : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 N, (Gseq k - Gseq (k - 1)) / (k : ℝ))
    + (maxG - Gseq N) / (N + 1 : ℕ)

/-- The absolute-variation coefficient called `v` in CDEM Lemma 4, before instantiating
the concrete floor sum.  Only the increments in this remainder coefficient are replaced
by their absolute values. -/
noncomputable def absoluteRemainderWeight (N : ℕ) (Gseq : ℕ → ℝ) (maxG : ℝ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 N, |Gseq k - Gseq (k - 1)| / Real.sqrt k)
    + (maxG - Gseq N) / Real.sqrt (N + 1)

/-- The paper's displayed definitions

`u = uN + maxG/(N+1)` and `v = vN + maxG/sqrt(N+1)`

are exactly `signedMainWeight` and `absoluteRemainderWeight`. -/
theorem paper_weights_eq
    (N : ℕ) (Gseq : ℕ → ℝ) (maxG : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (Gseq k - Gseq (k - 1)) / (k : ℝ))
          - Gseq N / (N + 1 : ℕ) + maxG / (N + 1 : ℕ)
        = signedMainWeight N Gseq maxG
      ∧
    (∑ k ∈ Finset.Icc 1 N, |Gseq k - Gseq (k - 1)| / Real.sqrt k)
          - Gseq N / Real.sqrt (N + 1) + maxG / Real.sqrt (N + 1)
        = absoluteRemainderWeight N Gseq maxG := by
  unfold signedMainWeight absoluteRemainderWeight
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
theorem signed_abel_remainder_bound
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
      ≤ mainCoeff * x * signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt x * absoluteRemainderWeight N Gseq maxG := by
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
    _ = mainCoeff * x * signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt x * absoluteRemainderWeight N Gseq maxG := by
      rw [Finset.sum_add_distrib, hmain_sum, herr_sum]
      unfold signedMainWeight absoluteRemainderWeight
      ring

/-- **Finite Abel identity used by CDEM Lemma 4.**

The left side is the hyperbola-grouped squarefree sum, with the complementary range
bounded by `maxG`.  The right side exposes the signed differences of `Gseq`.  The
assumption `Gseq 0 = 0` records the paper's explicit auxiliary-sequence override. -/
theorem finite_abel_identity
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
This simply composes `finite_abel_identity` with `signed_abel_remainder_bound`; it is kept
as a separate theorem so later arithmetic work only has to identify the hyperbola-grouped
sum with this left-hand side. -/
theorem grouped_squarefree_bound
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
      ≤ mainCoeff * x * signedMainWeight N Gseq maxG
          + errorCoeff * Real.sqrt x * absoluteRemainderWeight N Gseq maxG := by
  rw [finite_abel_identity N Gseq Qseq maxG hG0]
  exact signed_abel_remainder_bound N Gseq Qseq mainCoeff errorCoeff x maxG
    hGN_nonneg hGN_le hQ

/-! ## The fundamental Möbius--floor identity -/

/-- A finite CDEM floor sum.  The denominators are real, not silently coerced naturals:
this covers the paper's nonintegral periodizing denominator. -/
noncomputable def floorSum {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) (y : ℝ) : ℝ :=
  ∑ i ∈ s, coeff i * (⌊y / denominator i⌋₊ : ℝ)

/-- The nonnegative floor-sum error `G(y)=|1-F(y)|` in CDEM Lemma 4. -/
noncomputable def floorError {ι : Type*} (s : Finset ι)
    (coeff denominator : ι → ℝ) (y : ℝ) : ℝ :=
  |1 - floorSum s coeff denominator y|

/-- The exact guard which makes a real denominator harmless for the unit-step table up
to `N`.  An integral denominator is constant on every half-open unit interval.  A
nonintegral denominator is also harmless if it is at least `N+1`, because its floor term
vanishes throughout the tabulated range `[1,N+1)`.

This is the guard needed for the paper's large nonintegral periodizing denominator; it
must not be silently treated as an integer. -/
def UnitStepDenominatorGuard (N : ℕ) (a : ℝ) : Prop :=
  (∃ d : ℕ, 1 ≤ d ∧ a = d) ∨ (N + 1 : ℕ) ≤ a

/-- A single guarded floor term is constant on every tabulated unit interval. -/
theorem floor_div_constant_on_unit_of_guard
    (N k : ℕ) (a y : ℝ)
    (hk : k ∈ Finset.Icc 1 N)
    (hy_lower : (k : ℝ) ≤ y)
    (hy_upper : y < k + 1)
    (ha : UnitStepDenominatorGuard N a) :
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
theorem floorSum_constant_on_unit_of_guards
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N k : ℕ) (y : ℝ)
    (hk : k ∈ Finset.Icc 1 N)
    (hy_lower : (k : ℝ) ≤ y)
    (hy_upper : y < k + 1)
    (hdenom : ∀ i ∈ s, UnitStepDenominatorGuard N (denominator i)) :
    floorSum s coeff denominator y = floorSum s coeff denominator k := by
  unfold floorSum
  apply Finset.sum_congr rfl
  intro i hi
  rw [floor_div_constant_on_unit_of_guard N k (denominator i) y hk hy_lower hy_upper
    (hdenom i hi)]

/-- Consequently the CDEM error `G(y)=|1-F(y)|` has the same unit-step property. -/
theorem floorError_constant_on_unit_of_guards
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N k : ℕ) (y : ℝ)
    (hk : k ∈ Finset.Icc 1 N)
    (hy_lower : (k : ℝ) ≤ y)
    (hy_upper : y < k + 1)
    (hdenom : ∀ i ∈ s, UnitStepDenominatorGuard N (denominator i)) :
    floorError s coeff denominator y = floorError s coeff denominator k := by
  unfold floorError
  rw [floorSum_constant_on_unit_of_guards s coeff denominator N k y hk hy_lower hy_upper
    hdenom]

/-- A scaled form of the PNTA Möbius--floor identity.

For a real denominator `a ≥ 1` which is active at height `x` (`a ≤ x`),

`sum_{n≤x} mu(n) floor((x/n)/a) = 1`.

The upper summation limit is `floor x`, rather than `floor (x/a)`.  Terms in the
difference vanish because `a ≥ 1`.  No integrality assumption on `a` is used. -/
theorem sum_mobius_scaled_floor
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
    _ = 1 := Helfgott.cdem_moebius_floor_real (x / a) hy

/-- **Fundamental Möbius--floor identity (CDEM Lemma 4, step 1).**

If every denominator in the finite floor sum is at least `1` and no larger than `x`, then

`sum_{n≤x} mu(n) (1 - F(x/n)) = sum_{n≤x} mu(n) - sum_i c_i`.

The upper guard `denominator i ≤ x` is essential.  In the CDEM data one periodizing
denominator is nonintegral and extremely large; below it this theorem cannot be applied
to the full coefficient table.  Such an inactive term must instead be omitted explicitly
(and its coefficient charged to the finite `w` endpoint), exactly as the paper remarks.
This theorem does not use or hide an integrality assumption on denominators. -/
theorem mobius_floor_fundamental_identity
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ) (x : ℝ)
    (hdenom_one : ∀ i ∈ s, 1 ≤ denominator i)
    (hdenom_active : ∀ i ∈ s, denominator i ≤ x) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ)
          * (1 - floorSum s coeff denominator (x / n)))
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
        rw [sum_mobius_scaled_floor x (denominator i)
          (hdenom_one i hi) (hdenom_active i hi), mul_one]
  calc
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ)
          * (1 - floorSum s coeff denominator (x / n)))
      = (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
          - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ∑ i ∈ s, (ArithmeticFunction.moebius n : ℝ)
                * (coeff i * (⌊(x / n) / denominator i⌋₊ : ℝ)) := by
        unfold floorSum
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
theorem abs_mobius_floor_fundamental_le_squarefree_sum
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ) (x : ℝ)
    (hdenom_one : ∀ i ∈ s, 1 ≤ denominator i)
    (hdenom_active : ∀ i ∈ s, denominator i ≤ x) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius n : ℝ))
        - ∑ i ∈ s, coeff i|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)|
            * floorError s coeff denominator (x / n) := by
  rw [← mobius_floor_fundamental_identity s coeff denominator x hdenom_one hdenom_active]
  calc
    |∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.moebius n : ℝ)
          * (1 - floorSum s coeff denominator (x / n))|
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)
            * (1 - floorSum s coeff denominator (x / n))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)|
            * floorError s coeff denominator (x / n) := by
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
theorem hyperbola_grouping_floor
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
noncomputable def squarefreeCount (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), |(ArithmeticFunction.moebius n : ℝ)|

/-- Removing the vanishing `n=0` term recovers the usual interval definition of `Q`. -/
theorem squarefreeCount_eq_sum_Icc (y : ℝ) :
    squarefreeCount y
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, |(ArithmeticFunction.moebius n : ℝ)| := by
  unfold squarefreeCount
  rw [show Finset.range (⌊y⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊y⌋₊) by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega,
      Finset.sum_insert (by simp)]
  simp

/-- The complementary small-`n` range is bounded by `maxG * Q(x/(N+1))`.
This is the only use of the global `G≤maxG` bound in the hyperbola split. -/
theorem floorError_small_n_le_max
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x maxG : ℝ) (hx : 0 ≤ x)
    (hmax : ∀ y : ℝ, 0 ≤ y → floorError s coeff denominator y ≤ maxG) :
    (∑ n ∈ Finset.Icc 1 ⌊x / (N + 1 : ℕ)⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * floorError s coeff denominator (x / n))
      ≤ maxG * squarefreeCount (x / (N + 1 : ℕ)) := by
  rw [squarefreeCount_eq_sum_Icc, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  rw [mul_comm maxG]
  exact mul_le_mul_of_nonneg_left
    (hmax (x / n) (div_nonneg hx (Nat.cast_nonneg n))) (abs_nonneg _)

/-- A hyperbola fiber is the difference of two squarefree counts. -/
theorem squarefreeCount_sub_eq_sum_fiber
    (x : ℝ) (k : ℕ) (hx : 0 ≤ x) (hk : 1 ≤ k) :
    squarefreeCount (x / k) - squarefreeCount (x / (k + 1 : ℕ))
      = ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℕ)⌋₊ ⌊x / k⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)| := by
  have hdiv : x / (k + 1 : ℕ) ≤ x / k := by
    gcongr
    norm_cast
    omega
  have hfloor : ⌊x / (k + 1 : ℕ)⌋₊ ≤ ⌊x / k⌋₊ := Nat.floor_mono hdiv
  rw [← Finset.Ico_add_one_add_one_eq_Ioc]
  unfold squarefreeCount
  exact (Finset.sum_Ico_eq_sub (f := fun n => |(ArithmeticFunction.moebius n : ℝ)|)
    (Nat.add_le_add_right hfloor 1)).symm

/-- Hyperbola grouping for the actual CDEM error function `G(y)=|1-F(y)|`.

The integer-or-inactive denominator guard is threaded explicitly: it is what permits
replacing `G(x/n)` by `G(floor(x/n))` on the grouped range. -/
theorem floorError_hyperbola_grouping
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hdenom : ∀ i ∈ s, UnitStepDenominatorGuard N (denominator i)) :
    (∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * floorError s coeff denominator (x / n))
      = ∑ k ∈ Finset.Icc 1 N, floorError s coeff denominator k
          * ∑ n ∈ Finset.Ioc ⌊x / (k + 1 : ℝ)⌋₊ ⌊x / (k : ℝ)⌋₊,
              |(ArithmeticFunction.moebius n : ℝ)| := by
  have hreplace :
      (∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
          |(ArithmeticFunction.moebius n : ℝ)|
            * floorError s coeff denominator (x / n))
        = ∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
            |(ArithmeticFunction.moebius n : ℝ)|
              * floorError s coeff denominator ⌊x / (n : ℝ)⌋₊ := by
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
    rw [floorError_constant_on_unit_of_guards s coeff denominator N
      ⌊x / (n : ℝ)⌋₊ (x / (n : ℝ)) hk hy_lower hy_upper hdenom]
  rw [hreplace]
  have hgroup := hyperbola_grouping_floor x (N + 1) (Nat.succ_pos N) hx
    (fun n => |(ArithmeticFunction.moebius n : ℝ)|)
    (fun k => floorError s coeff denominator k)
  rw [Finset.Ico_add_one_right_eq_Icc] at hgroup
  exact hgroup

/-- The same grouping in the paper's displayed `Q(x/k)-Q(x/(k+1))` notation. -/
theorem floorError_hyperbola_grouping_squarefreeCount
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x : ℝ) (hx : 1 ≤ x)
    (hdenom : ∀ i ∈ s, UnitStepDenominatorGuard N (denominator i)) :
    (∑ n ∈ Finset.Ioc ⌊x / (N + 1 : ℕ)⌋₊ ⌊x⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * floorError s coeff denominator (x / n))
      = ∑ k ∈ Finset.Icc 1 N, floorError s coeff denominator k
          * (squarefreeCount (x / k) - squarefreeCount (x / (k + 1 : ℕ))) := by
  rw [floorError_hyperbola_grouping s coeff denominator N x hx hdenom]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  rw [squarefreeCount_sub_eq_sum_fiber x k (zero_le_one.trans hx) hk'.1]
  norm_num [Nat.cast_add, Nat.cast_one]

/-- **CDEM Lemma 4, hyperbola/absolute-value step.**

After replacing `|mu(n)|` by squarefree increments, split at `x/(N+1)`.  The
large-`n` part is grouped exactly by `floor(x/n)`; only the complementary small-`n`
part uses the global bound `G≤maxG`. -/
theorem floorError_squarefree_sum_le_grouped
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (coeff denominator : ι → ℝ)
    (N : ℕ) (x maxG : ℝ) (hx : 1 ≤ x)
    (hdenom : ∀ i ∈ s, UnitStepDenominatorGuard N (denominator i))
    (hmax : ∀ y : ℝ, 0 ≤ y → floorError s coeff denominator y ≤ maxG) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        |(ArithmeticFunction.moebius n : ℝ)|
          * floorError s coeff denominator (x / n))
      ≤ (∑ k ∈ Finset.Icc 1 N, floorError s coeff denominator k
          * (squarefreeCount (x / k) - squarefreeCount (x / (k + 1 : ℕ))))
        + maxG * squarefreeCount (x / (N + 1 : ℕ)) := by
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
    floorError_hyperbola_grouping_squarefreeCount s coeff denominator N x hx hdenom]
  have hsmall := floorError_small_n_le_max s coeff denominator N x maxG
    (zero_le_one.trans hx) hmax
  linarith

end MathExtras.CohenDressElMarraki
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma floorRoot_two_eq_one_iff_squarefree (n : ℕ) (hn : n ≠ 0) :
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

lemma moebius_divisor_sum (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors,moebius d) = if n=1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  simpa [ArithmeticFunction.one_apply,hn] using h

theorem moebius_square_divisor_expansion (n : ℕ) (hn : n ≠ 0) :
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
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ hroot0,moebius_sq]
  simp only [floorRoot_two_eq_one_iff_squarefree n hn]

lemma coprime_moebius_divisor_expansion (q n : ℕ) (hq : q ≠ 0) :
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
  rw [←Finset.sum_filter,he,moebius_divisor_sum _ (Nat.gcd_ne_zero_right hq)]

theorem squarefree_coprime_pointwise_expansion (q n : ℕ) (hq : q ≠ 0) (hn : n ≠ 0) :
    (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      (∑ d ∈ n.divisors,if d^2 ∣ n ∧ Nat.Coprime d q then ((moebius d : ℤ) : ℝ) else 0)*
      (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) := by
  have hcop : (∑ e ∈ q.divisors,if e ∣ n then ((moebius e : ℤ) : ℝ) else 0) =
      if Nat.Coprime n q then 1 else 0 := by
    exact_mod_cast coprime_moebius_divisor_expansion q n hq
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
    exact_mod_cast moebius_square_divisor_expansion n hn
  · simp [h]

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma squarefree_square_divisor_sum_cap (q n N : ℕ) (hn : 0<n) (hnN : n≤N) :
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

theorem squarefree_coprime_count_exact (q N : ℕ) (hq : q ≠ 0) :
    (∑ n ∈ Finset.Icc 1 N,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
      ∑ d ∈ Finset.Icc 1 N.sqrt,if Nat.Coprime d q then
        ((moebius d : ℤ) : ℝ)*(∑ e ∈ q.divisors,((moebius e : ℤ) : ℝ)*((N/(d^2*e) : ℕ) : ℝ)) else 0 := by
  have hp (n : ℕ) (hn : n∈Finset.Icc 1 N) :
      (if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)^2 else 0) =
        ∑ d ∈ Finset.Icc 1 N.sqrt,∑ e ∈ q.divisors,
          if d^2 ∣ n ∧ Nat.Coprime d q ∧ e ∣ n then
            ((moebius d : ℤ) : ℝ)*((moebius e : ℤ) : ℝ) else 0 := by
    rw [squarefree_coprime_pointwise_expansion q n hq (by have := (Finset.mem_Icc.mp hn).1;omega),
      squarefree_square_divisor_sum_cap q n N (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2,
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

lemma principal_character_nat_value (q n : ℕ) :
    (1 : DirichletCharacter ℂ q) n = if Nat.Coprime n q then 1 else 0 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hc)
  · rw [if_neg hc]
    exact MulChar.map_nonunit _ (fun h => hc ((ZMod.isUnit_iff_coprime n q).mp h))

lemma principal_LSeries_at_two (q : ℕ) (hq : q ≠ 0) :
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
  rw [principal_character_nat_value]
  try simp only [Nat.coprime_one_right,if_true,one_mul]
  rw [Complex.cpow_neg]
  norm_num [Complex.cpow_natCast]

lemma principal_moebius_LSeries_at_two (q : ℕ) :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 =
      ((∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) : ℂ) := by
  rw [LSeries]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · subst n
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn,principal_character_nat_value]
    norm_num [Complex.cpow_natCast]
    split_ifs <;> push_cast <;> ring

theorem squarefree_coprime_density_series (q : ℕ) (hq : q ≠ 0) :
    (∑' n : ℕ,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) =
      (6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹ := by
  have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ q) (s:=2) (by norm_num)
  change LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n) 2 *
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) n * (moebius n : ℂ)) 2 = 1 at h
  rw [principal_LSeries_at_two q hq,principal_moebius_LSeries_at_two] at h
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

lemma shifted_reciprocal_square_sum_le (D K : ℕ) (hD : 1≤D) :
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

lemma shifted_reciprocal_square_tsum_le (D : ℕ) (hD : 1≤D) :
    (∑' n : ℕ,1/((n+D+1 : ℕ) : ℝ)^2) ≤ 1/(D : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (fun K => shifted_reciprocal_square_sum_le D K hD)

lemma coprime_moebius_reciprocal_square_norm_le (q n : ℕ) :
    ‖(if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)‖ ≤ 1/(n : ℝ)^2 := by
  by_cases hc : Nat.Coprime n q
  · rw [if_pos hc,Real.norm_eq_abs,abs_div]
    rw [show |(n : ℝ)^2| = (n : ℝ)^2 from abs_of_nonneg (sq_nonneg _)]
    exact div_le_div_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n:=n)) (sq_nonneg _)
  · rw [if_neg hc,norm_zero]
    positivity

lemma coprime_moebius_reciprocal_square_summable (q : ℕ) :
    Summable (fun n : ℕ => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0) := by
  exact Summable.of_norm_bounded hasSum_zeta_two.summable (fun n => coprime_moebius_reciprocal_square_norm_le q n)

lemma reciprocal_square_tsum_le_two : (∑' n : ℕ,1/(n : ℝ)^2) ≤ 2 := by
  have h := hasSum_zeta_two.summable.sum_add_tsum_nat_add 2
  norm_num [Finset.sum_range_succ] at h
  have ht := shifted_reciprocal_square_tsum_le 1 (by norm_num)
  norm_num [add_assoc] at ht
  simp only [one_div]
  linarith

lemma coprime_moebius_density_norm_le_two (q : ℕ) (hq : q ≠ 0) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹| ≤ 2 := by
  rw [←squarefree_coprime_density_series q hq]
  have hf := coprime_moebius_reciprocal_square_summable q
  calc
    _ ≤ ∑' n : ℕ,‖if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0‖ := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n : ℕ,1/(n : ℝ)^2 := hf.norm.tsum_le_tsum
      (fun n => coprime_moebius_reciprocal_square_norm_le q n) hasSum_zeta_two.summable
    _ ≤ _ := reciprocal_square_tsum_le_two

theorem coprime_moebius_density_tail_error (q D : ℕ) (hq : q ≠ 0) (hD : 1≤D) :
    |(6/Real.pi^2)*∏ p ∈ q.primeFactors,(1-1/(p : ℝ)^2)⁻¹-
      (∑ n ∈ Finset.Icc 1 D,if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0)| ≤ 1/(D : ℝ) := by
  let f : ℕ → ℝ := fun n => if Nat.Coprime n q then ((moebius n : ℤ) : ℝ)/(n : ℝ)^2 else 0
  have hf : Summable f := coprime_moebius_reciprocal_square_summable q
  have hs : (∑ n ∈ Finset.range (D+1),f n) = ∑ n ∈ Finset.Icc 1 D,f n := by
    rw [Finset.range_eq_Ico]
    have he : Finset.Ico 0 (D+1) = insert 0 (Finset.Icc 1 D) := by ext n;simp;omega
    rw [he,Finset.sum_insert (by simp)]
    simp [f]
  rw [←squarefree_coprime_density_series q hq]
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
      htail.norm.tsum_le_tsum (fun n => by simpa [f,Nat.add_assoc] using coprime_moebius_reciprocal_square_norm_le q (n+(D+1))) hnorm
    _ ≤ _ := shifted_reciprocal_square_tsum_le D hD

end Helfgott
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem cdem_squarefree_floor_main_error (x : ℝ) (hx : 1 ≤ x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ)^2) -
      (⌊x⌋₊ : ℝ)*(∑ d ∈ Icc 1 (⌊x⌋₊).sqrt, (moebius d : ℝ)/(d : ℝ)^2)| ≤
      Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hc := squarefree_coprime_count_exact 1 ⌊x⌋₊ (by norm_num)
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
private theorem squarefreeCount_eq_moebius_sq_sum (x : ℝ) :
    squarefreeCount x
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((μ n : ℝ)) ^ 2 := by
  rw [squarefreeCount_eq_sum_Icc]
  apply Finset.sum_congr rfl
  intro n _
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num

/-- A base-trio squarefree-remainder seed.  This deliberately has a coarse
constant: its role is to initialize repeated CDEM Lemma 4/Lemma 1 iteration,
not to replace the sharp final `0.02767` estimate directly. -/
theorem coarseSquarefreeRemainder_three
    {x : ℝ} (hx : 9 ≤ x) :
    |squarefreeCount x - (6 / Real.pi ^ 2) * x|
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
    simpa [Q, N, K, S] using Helfgott.cdem_squarefree_floor_main_error x hx1
  have htail : |L - S| ≤ 1 / (K : ℝ) := by
    simpa [L, S, Nat.coprime_one_right_iff] using
      Helfgott.coprime_moebius_density_tail_error 1 K (by norm_num) hKone
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

  rw [squarefreeCount_eq_moebius_sq_sum]
  simpa [Q, N, L, hL, mul_comm] using htotal

end MathExtras.CohenDressElMarraki
end

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical
namespace Helfgott

theorem cdem_squarefree_seed_three_complete (x : ℝ) (hx : 9 ≤ x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ)^2) -
      (6 / Real.pi^2)*x| ≤ 3*Real.sqrt x := by
  have he : MathExtras.CohenDressElMarraki.squarefreeCount x =
      ∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ)^2 := by
    rw [MathExtras.CohenDressElMarraki.squarefreeCount_eq_sum_Icc]
    apply Finset.sum_congr rfl
    intro n hn
    rcases moebius_eq_or n with h | h | h <;> rw [h] <;> norm_num
  rw [← he]
  exact MathExtras.CohenDressElMarraki.coarseSquarefreeRemainder_three hx

end Helfgott
end

open Helfgott Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution  (x : ℝ) (hx : 9 ≤ x) :
    |(∑ n ∈ Icc 1 ⌊x⌋₊, (moebius n : ℝ)^2) -
      (6 / Real.pi^2)*x| ≤ 3*Real.sqrt x := Helfgott.cdem_squarefree_seed_three_complete x hx
#print axioms solution
