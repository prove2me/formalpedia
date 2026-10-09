-- Prove2me | solution 1 for Helfgott.cdem_squarefree_exact_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T02:22:14.348663+00:00
-- url     : https://prove2.me/submissions/4ef3ba8c-4ab2-4b0d-9aa5-47bfa9296987

import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

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

* `Lemma1ExactDecompositionAt x n` is the exact partial-summation identity obtained from
  CDEM (2.1) and the tail of `sum mu(a)/a^2`;
* `Lemma1CenteredCauchyAt x n` and `Lemma1PeriodicMajorantAt x n` are respectively the
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
noncomputable def lemma1X (x : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (x / j)

/-- Real-valued Mertens step function used by the paper. -/
noncomputable def lemma1M (t : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ)

/-- The squarefree remainder in the same normalization as the Lemma 4 wrapper. -/
noncomputable def lemma1Remainder (x : ℝ) : ℝ :=
  squarefreeCount x - (6 / Real.pi ^ 2) * x

/-- Signed tail integral occurring in the exact decomposition. -/
noncomputable def lemma1SignedTailIntegral (x : ℝ) (n : ℕ) : ℝ :=
  ∫ t in Set.Ioi (lemma1X x n), lemma1M t / t ^ 3

/-- `T1=2x integral_{X_n}^infinity |M(t)|/t^3 dt`. -/
noncomputable def lemma1T1 (x : ℝ) (n : ℕ) : ℝ :=
  2 * x * ∫ t in Set.Ioi (lemma1X x n), |lemma1M t| / t ^ 3

/-- `T2=sum_{j=1}^{n-1}|M(X_j)|+|M(X_n)|/2`. -/
noncomputable def lemma1T2 (x : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (n - 1), |lemma1M (lemma1X x j)|)
    + |lemma1M (lemma1X x n)| / 2

/-- The centered fractional-part sum whose absolute value is `T3`. -/
noncomputable def lemma1CenteredSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
    (ArithmeticFunction.moebius a : ℝ)
      * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2)

/-- `T3=|sum_{a≤X_n} mu(a)({x/a^2}-1/2)|`. -/
noncomputable def lemma1T3 (x : ℝ) (n : ℕ) : ℝ :=
  |lemma1CenteredSum x n|

/-- The square mass appearing after Cauchy--Schwarz. -/
noncomputable def lemma1CenteredSquareMass (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
    (if 4 ∣ a ∨ 9 ∣ a then 0 else 1 : ℝ)
      * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2) ^ 2

/-- The exact printed upper factor for `Q(X_n)`:
`6 sqrt(x)/(pi^2 sqrt(n)) + b x^(1/4)/n^(1/4)`.

Nested square roots are used for the quarter powers, avoiding any ambiguity about real
power notation at zero. -/
noncomputable def lemma1QFactor (x : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  6 * Real.sqrt x / (Real.pi ^ 2 * Real.sqrt n)
    + b * Real.sqrt (Real.sqrt x) / Real.sqrt (Real.sqrt n)

/-- The exact printed periodic-majorant factor:
`sqrt(x)/(18 sqrt(n-0.02)) + (12x)^(1/3)/6 - (2/3)(n-1/2)`. -/
noncomputable def lemma1SFactor (x : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt x / (18 * Real.sqrt ((n : ℝ) - 2 / 100))
    + (12 * x) ^ ((1 : ℝ) / 3) / 6
    - (2 / 3 : ℝ) * ((n : ℝ) - 1 / 2)

/-- The displayed `T3` envelope. -/
noncomputable def lemma1T3Envelope (x : ℝ) (n : ℕ) (b : ℝ) : ℝ :=
  Real.sqrt (lemma1QFactor x n b * lemma1SFactor x n)

/-- The finite reciprocal-square-root weight in the `T2` estimate. -/
noncomputable def lemma1T2Weight (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (n - 1), 1 / Real.sqrt j)
    + 1 / (2 * Real.sqrt n)

/-! ## Exact pointwise seams -/

/-- Exact partial-summation decomposition underlying CDEM Lemma 1:

`R(x) = -2x I + sum_{j<n} M(X_j) + M(X_n)/2 - centeredSum`.

This is a pointwise identity.  It is strictly stronger and structurally different from
the target inequality `|R(x)|≤b sqrt(x)`. -/
def Lemma1ExactDecompositionAt (x : ℝ) (n : ℕ) : Prop :=
  lemma1Remainder x
    = -2 * x * lemma1SignedTailIntegral x n
      + (∑ j ∈ Finset.Icc 1 (n - 1), lemma1M (lemma1X x j))
      + lemma1M (lemma1X x n) / 2
      - lemma1CenteredSum x n

/-- The pointwise Cauchy--Schwarz step for the centered sum. -/
def Lemma1CenteredCauchyAt (x : ℝ) (n : ℕ) : Prop :=
  lemma1T3 x n
    ≤ Real.sqrt (squarefreeCount (lemma1X x n) * lemma1CenteredSquareMass x n)

/-- The signed Euler--Maclaurin/periodic-majorant bound for the centered square mass. -/
def Lemma1PeriodicMajorantAt (x : ℝ) (n : ℕ) : Prop :=
  lemma1CenteredSquareMass x n ≤ lemma1SFactor x n

/-! ## Proven assembly around the seams -/

/-- The exact decomposition implies `|R|≤T1+T2+T3`, provided the standard absolute
integral inequality is supplied for the signed tail. -/
theorem lemma1_three_term_bound
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hdecomp : Lemma1ExactDecompositionAt x n)
    (htail_abs :
      |lemma1SignedTailIntegral x n|
        ≤ ∫ t in Set.Ioi (lemma1X x n), |lemma1M t| / t ^ 3) :
    |lemma1Remainder x| ≤ lemma1T1 x n + lemma1T2 x n + lemma1T3 x n := by
  rw [Lemma1ExactDecompositionAt] at hdecomp
  rw [hdecomp]
  have hsum :
      |∑ j ∈ Finset.Icc 1 (n - 1), lemma1M (lemma1X x j)|
        ≤ ∑ j ∈ Finset.Icc 1 (n - 1), |lemma1M (lemma1X x j)| :=
    Finset.abs_sum_le_sum_abs _ _
  have htail :
      |-2 * x * lemma1SignedTailIntegral x n| ≤ lemma1T1 x n := by
    rw [abs_mul, abs_mul, abs_of_nonneg hx]
    unfold lemma1T1
    have h2x : 0 ≤ 2 * x := by positivity
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_left htail_abs h2x
  have hend : |lemma1M (lemma1X x n) / 2| = |lemma1M (lemma1X x n)| / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hcenter : |-lemma1CenteredSum x n| = lemma1T3 x n := by
    simp [lemma1T3]
  calc
    |-2 * x * lemma1SignedTailIntegral x n
        + (∑ j ∈ Finset.Icc 1 (n - 1), lemma1M (lemma1X x j))
        + lemma1M (lemma1X x n) / 2
        - lemma1CenteredSum x n|
      ≤ |-2 * x * lemma1SignedTailIntegral x n|
          + |∑ j ∈ Finset.Icc 1 (n - 1), lemma1M (lemma1X x j)|
          + |lemma1M (lemma1X x n) / 2|
          + |-lemma1CenteredSum x n| := by
        calc
          |_ + _ + _ - _| ≤ |_ + _ + _| + |-_| := abs_add_le _ _
          _ ≤ (|_ + _| + |lemma1M (lemma1X x n) / 2|) + |-_| := by
            gcongr
            exact abs_add_le _ _
          _ ≤ ((|-2 * x * lemma1SignedTailIntegral x n|
                + |∑ j ∈ Finset.Icc 1 (n - 1), lemma1M (lemma1X x j)|)
                + |lemma1M (lemma1X x n) / 2|) + |-_| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ lemma1T1 x n
          + ((∑ j ∈ Finset.Icc 1 (n - 1), |lemma1M (lemma1X x j)|)
              + |lemma1M (lemma1X x n)| / 2)
          + lemma1T3 x n := by
        rw [hend, hcenter]
        linarith
    _ = lemma1T1 x n + lemma1T2 x n + lemma1T3 x n := by
      rfl

/-- The `T1` estimate after the improper-integral comparison has been established.
The conclusion is exactly `2 epsilon sqrt(n) sqrt(x)`. -/
theorem lemma1_T1_le
    {x ε : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hε : 0 ≤ ε)
    (hint :
      (∫ t in Set.Ioi (lemma1X x n), |lemma1M t| / t ^ 3)
        ≤ ε / lemma1X x n) :
    lemma1T1 x n ≤ 2 * ε * Real.sqrt n * Real.sqrt x := by
  have hmul := mul_le_mul_of_nonneg_left hint (show 0 ≤ 2 * x by positivity)
  unfold lemma1T1
  refine hmul.trans_eq ?_
  unfold lemma1X
  rw [Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt hx.le, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- `T2` from pointwise Mertens bounds at the finitely many `X_j`. -/
theorem lemma1_T2_le_of_pointwise
    {x ε C : ℝ} {n : ℕ} (hn : 1 ≤ n) (hx : 0 ≤ x) (hε : 0 ≤ ε)
    (hM : ∀ j ∈ Finset.Icc 1 n,
      |lemma1M (lemma1X x j)| ≤ ε * Real.sqrt x / Real.sqrt j)
    (hweight : lemma1T2Weight n ≤ C) :
    lemma1T2 x n ≤ ε * Real.sqrt x * C := by
  have hsum :
      (∑ j ∈ Finset.Icc 1 (n - 1), |lemma1M (lemma1X x j)|)
        ≤ ∑ j ∈ Finset.Icc 1 (n - 1), ε * Real.sqrt x / Real.sqrt j := by
    apply Finset.sum_le_sum
    intro j hj
    exact hM j (by simp only [Finset.mem_Icc] at hj ⊢; omega)
  have hend := hM n (by simp [hn])
  have hfactor :
      (∑ j ∈ Finset.Icc 1 (n - 1), ε * Real.sqrt x / Real.sqrt j)
          + (ε * Real.sqrt x / Real.sqrt n) / 2
        = ε * Real.sqrt x * lemma1T2Weight n := by
    unfold lemma1T2Weight
    rw [mul_add, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · ring
  calc
    lemma1T2 x n
      ≤ (∑ j ∈ Finset.Icc 1 (n - 1), ε * Real.sqrt x / Real.sqrt j)
          + (ε * Real.sqrt x / Real.sqrt n) / 2 := by
        unfold lemma1T2
        linarith
    _ = ε * Real.sqrt x * lemma1T2Weight n := hfactor
    _ ≤ ε * Real.sqrt x * C :=
      mul_le_mul_of_nonneg_left hweight (mul_nonneg hε (Real.sqrt_nonneg _))

/-- Cauchy--Schwarz plus the two displayed factor bounds gives the exact `T3` envelope. -/
theorem lemma1_T3_le_envelope
    {x b : ℝ} {n : ℕ}
    (hCS : Lemma1CenteredCauchyAt x n)
    (hQnonneg : 0 ≤ squarefreeCount (lemma1X x n))
    (hSnonneg : 0 ≤ lemma1CenteredSquareMass x n)
    (hQ : squarefreeCount (lemma1X x n) ≤ lemma1QFactor x n b)
    (hS : Lemma1PeriodicMajorantAt x n) :
    lemma1T3 x n ≤ lemma1T3Envelope x n b := by
  rw [Lemma1CenteredCauchyAt] at hCS
  rw [Lemma1PeriodicMajorantAt] at hS
  unfold lemma1T3Envelope
  refine hCS.trans (Real.sqrt_le_sqrt ?_)
  exact mul_le_mul hQ hS hSnonneg (hQnonneg.trans hQ)

/-! ## The honest `n=197` specialization -/

def lemma1FinalN : ℕ := 197
def lemma1FinalX0 : ℝ := 1600000000000000
noncomputable def lemma1PreviousMertensEpsilon : ℝ := 1 / 4257
noncomputable def lemma1PreviousSquarefreeB : ℝ := 36438 / 1000000
noncomputable def lemma1FinalB : ℝ := 2767 / 100000

/-- Finite scalar `T2` weight check at `n=197`.  This is a fixed 196-term
inequality, not an unbounded analytic input. -/
def Lemma1N197T2WeightCertificate : Prop :=
  lemma1T2Weight lemma1FinalN
    ≤ 2 * Real.sqrt lemma1FinalN - 146 / 100

/-- Exact `T1+T2` fold at `n=197`; no rounded decimal is introduced. -/
theorem lemma1_T12_n197
    {x : ℝ}
    (hT1 : lemma1T1 x lemma1FinalN
      ≤ 2 * lemma1PreviousMertensEpsilon * Real.sqrt lemma1FinalN * Real.sqrt x)
    (hT2 : lemma1T2 x lemma1FinalN
      ≤ lemma1PreviousMertensEpsilon * Real.sqrt x
          * (2 * Real.sqrt lemma1FinalN - 146 / 100)) :
    lemma1T1 x lemma1FinalN + lemma1T2 x lemma1FinalN
      ≤ lemma1PreviousMertensEpsilon
          * (4 * Real.sqrt lemma1FinalN - 146 / 100) * Real.sqrt x := by
  linarith

/-- Exact combined analytic envelope for the second bootstrap. -/
noncomputable def lemma1N197CombinedEnvelope (x : ℝ) : ℝ :=
  lemma1PreviousMertensEpsilon
      * (4 * Real.sqrt lemma1FinalN - 146 / 100) * Real.sqrt x
    + lemma1T3Envelope x lemma1FinalN lemma1PreviousSquarefreeB

/-- A fixed endpoint numerical proposition.  This is suitable for a verified-interval
certificate; unlike the false rounded component inequalities, it has positive margin. -/
def Lemma1N197EndpointCertificate : Prop :=
  lemma1N197CombinedEnvelope lemma1FinalX0
    ≤ lemma1FinalB * Real.sqrt lemma1FinalX0

/-- The elementary monotonicity statement needed to propagate the endpoint certificate.
After division by `sqrt(x)`, it is a monotonicity problem in the negative powers
`x^(-1/6)`, `x^(-1/4)`, and `x^(-1/2)`. -/
def Lemma1N197EnvelopeAntitone : Prop :=
  AntitoneOn (fun x => lemma1N197CombinedEnvelope x / Real.sqrt x)
    (Set.Ici lemma1FinalX0)

/-- The fixed endpoint certificate and the full-range monotonicity theorem propagate the
combined envelope to every `x≥1.6*10^15`. -/
theorem lemma1_n197_combined_envelope
    (hendpoint : Lemma1N197EndpointCertificate)
    (hanti : Lemma1N197EnvelopeAntitone)
    {x : ℝ} (hx : lemma1FinalX0 ≤ x) :
    lemma1N197CombinedEnvelope x ≤ lemma1FinalB * Real.sqrt x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num [lemma1FinalX0]) hx
  have hbase0 : 0 < lemma1FinalX0 := by norm_num [lemma1FinalX0]
  rw [Lemma1N197EndpointCertificate] at hendpoint
  rw [Lemma1N197EnvelopeAntitone] at hanti
  have hmono := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs0 : 0 < Real.sqrt lemma1FinalX0 := Real.sqrt_pos.2 hbase0
  have hendpoint_div :
      lemma1N197CombinedEnvelope lemma1FinalX0 / Real.sqrt lemma1FinalX0
        ≤ lemma1FinalB := by
    rw [div_le_iff₀ hs0]
    simpa [mul_comm] using hendpoint
  have hdiv : lemma1N197CombinedEnvelope x / Real.sqrt x ≤ lemma1FinalB :=
    hmono.trans hendpoint_div
  rwa [div_le_iff₀ hsx] at hdiv

/-- The analytic `n=197` tail, once the three exact pointwise seams and their component
bounds have been proved.  The two components are combined before the final comparison,
so no false rounded sub-bound is used. -/
theorem lemma1_n197_tail
    {x : ℝ} (hx : lemma1FinalX0 < x)
    (hthree : |lemma1Remainder x|
      ≤ lemma1T1 x lemma1FinalN + lemma1T2 x lemma1FinalN
          + lemma1T3 x lemma1FinalN)
    (hT12 : lemma1T1 x lemma1FinalN + lemma1T2 x lemma1FinalN
      ≤ lemma1PreviousMertensEpsilon
          * (4 * Real.sqrt lemma1FinalN - 146 / 100) * Real.sqrt x)
    (hT3 : lemma1T3 x lemma1FinalN
      ≤ lemma1T3Envelope x lemma1FinalN lemma1PreviousSquarefreeB)
    (hendpoint : Lemma1N197EndpointCertificate)
    (hanti : Lemma1N197EnvelopeAntitone) :
    |lemma1Remainder x| ≤ lemma1FinalB * Real.sqrt x := by
  have henv := lemma1_n197_combined_envelope hendpoint hanti hx.le
  unfold lemma1N197CombinedEnvelope at henv
  linarith

/-- Honest bounded base-range obligation for Theorem 3 bis.  This is finite: both
endpoints are explicit natural numbers. -/
def Theorem3BisFiniteWindowCertificate : Prop :=
  ∀ X : ℕ, 438653 < X → X ≤ 1600000000000000 →
    |lemma1Remainder X| ≤ lemma1FinalB * Real.sqrt X

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
reduces `Lemma1ExactDecompositionAt` to precisely two classical identities:

1. CDEM (2.1), the finite hyperbola identity (`Lemma1Eq21At`);
2. Abel/partial summation of the reciprocal-square Möbius tail
   (`Lemma1RecipSqPartialSummationAt`).

Neither residual is an estimate, an unbounded Mertens hypothesis, or the target
squarefree conclusion.  The first is finite-sum combinatorics. The second is exact summation by parts.
Both are proved here from Mathlib, with the density at exponent two and the
square-divisor convolution supplied by our independent proofs.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000

namespace MathExtras.CohenDressElMarraki

open Finset
open scoped BigOperators

/-- The reciprocal-square Möbius head through `X_n`. -/
noncomputable def lemma1MobiusRecipHead (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
    (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2

/-- The floor head in CDEM (2.1). -/
noncomputable def lemma1FloorHead (x : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
    (ArithmeticFunction.moebius a : ℝ) * (⌊x / (a : ℝ) ^ 2⌋₊ : ℝ)

/-- CDEM equation (2.1), isolated at one point `(x,n)`. -/
def Lemma1Eq21At (x : ℝ) (n : ℕ) : Prop :=
  squarefreeCount x
    = lemma1FloorHead x n
      + (∑ j ∈ Finset.Icc 1 (n - 1), lemma1M (lemma1X x j))
      - ((n - 1 : ℕ) : ℝ) * lemma1M (lemma1X x n)

/-- Exact reciprocal-square partial summation at `(x,n)`:

`x sum_{a≤X_n} mu(a)/a² = (6/pi²)x + n M(X_n) - 2x integral M(t)/t³`.

This is the smallest analytic identity still needed for the exact decomposition. -/
def Lemma1RecipSqPartialSummationAt (x : ℝ) (n : ℕ) : Prop :=
  x * lemma1MobiusRecipHead x n
    = (6 / Real.pi ^ 2) * x
      + (n : ℝ) * lemma1M (lemma1X x n)
      - 2 * x * lemma1SignedTailIntegral x n

/-- The remaining finite reindexing in (2.1).  It exchanges the pairs
`n≤k≤x`, `a≤sqrt(x/k)` with `a≤X_n`, `n≤k≤x/a²`. -/
def Lemma1HyperbolaTailInterchangeAt (x : ℝ) (n : ℕ) : Prop :=
  (∑ k ∈ Finset.Icc n ⌊x⌋₊, lemma1M (lemma1X x k))
    = lemma1FloorHead x n
      - ((n - 1 : ℕ) : ℝ) * lemma1M (lemma1X x n)

/-- The paper's real Mertens step is the corresponding finite real Möbius sum. -/
theorem lemma1M_eq_sum (t : ℝ) :
    lemma1M t
      = ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ) := by
  rfl

/-- For nonnegative `y`, the natural floor is `y-fract(y)`. -/
theorem natFloor_cast_eq_sub_fract {y : ℝ} (hy : 0 ≤ y) :
    (⌊y⌋₊ : ℝ) = y - Int.fract y := by
  have hfloor : ((⌊y⌋₊ : ℕ) : ℤ) = ⌊y⌋ := Int.natCast_floor_eq_floor hy
  have hreal : ((⌊y⌋ : ℤ) : ℝ) = y - Int.fract y :=
    (eq_sub_iff_add_eq).2 (Int.floor_add_fract y)
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hfloor
  norm_num at hcast
  exact hcast.trans hreal

/-- Exact centered fractional-part expansion of the floor head. -/
theorem lemma1_floorHead_centered
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x) :
    lemma1FloorHead x n
      = x * lemma1MobiusRecipHead x n
        - lemma1M (lemma1X x n) / 2
        - lemma1CenteredSum x n := by
  have hterm : ∀ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
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
    rw [natFloor_cast_eq_sub_fract hy]
    field_simp
    ring
  have hhalf :
      (∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
          (ArithmeticFunction.moebius a : ℝ) / 2)
        = (∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
            (ArithmeticFunction.moebius a : ℝ)) / 2 := by
    simpa only [div_eq_mul_inv] using
      (Finset.sum_mul (s := Finset.Icc 1 ⌊lemma1X x n⌋₊)
        (f := fun a => (ArithmeticFunction.moebius a : ℝ)) (2 : ℝ)⁻¹).symm
  unfold lemma1FloorHead lemma1MobiusRecipHead lemma1CenteredSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hhalf]
  have hM := lemma1M_eq_sum (lemma1X x n)
  rw [hM]

/-- **Exact CDEM Lemma 1 decomposition from its two irreducible identities.** -/
theorem lemma1_exactDecomposition_of_eq21_and_recipSq
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hn : 1 ≤ n)
    (heq21 : Lemma1Eq21At x n)
    (hrecip : Lemma1RecipSqPartialSummationAt x n) :
    Lemma1ExactDecompositionAt x n := by
  rw [Lemma1Eq21At] at heq21
  rw [Lemma1RecipSqPartialSummationAt] at hrecip
  rw [Lemma1ExactDecompositionAt]
  unfold lemma1Remainder
  rw [heq21, lemma1_floorHead_centered hx]
  have hcast : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]
    norm_num
  rw [hcast]
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
theorem sum_Icc_zero_moebius_eq_lemma1M (t : ℝ) :
    (∑ a ∈ Finset.Icc 0 ⌊t⌋₊,
        (ArithmeticFunction.moebius a : ℝ)) = lemma1M t := by
  rw [lemma1M_eq_sum]
  have hsets :
      Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsets, Finset.sum_insert (by simp)]
  simp

/-- The elementary step-function bound needed for the improper Abel limit.
The harmless `+1` avoids a special cardinality calculation at `0`. -/
theorem lemma1M_abs_le_add_one {t : ℝ} (ht : 0 ≤ t) :
    |lemma1M t| ≤ t + 1 := by
  rw [lemma1M_eq_sum]
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
theorem measurable_lemma1M : Measurable lemma1M := by
  have hsum : Measurable
      (fun N : ℕ => ∑ a ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ)) := measurable_of_countable _
  have hfactor : lemma1M =
      (fun N : ℕ => ∑ a ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ)) ∘ (fun t : ℝ => ⌊t⌋₊) := by
    funext t
    exact lemma1M_eq_sum t
  rw [hfactor]
  exact hsum.comp Nat.measurable_floor

/-- Absolute summability of `mu(a)/a^2`, by domination with the `p=2` series. -/
theorem summable_lemma1_moebius_div_sq :
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
theorem tsum_lemma1_moebius_div_sq :
    (∑' a : ℕ, (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
      = 6 / Real.pi ^ 2 := by
  simpa [Nat.coprime_one_right_iff] using
    Helfgott.squarefree_coprime_density_series 1 (by norm_num)

/-- The reciprocal-cube Mertens integrand is absolutely integrable on every positive
half-line.  The proof uses only `|M(t)| ≤ t+1 ≤ 2t` for `t≥1`. -/
theorem integrableOn_lemma1M_div_cube_Ioi {u : ℝ} (hu : 1 ≤ u) :
    IntegrableOn (fun t : ℝ => lemma1M t / t ^ 3) (Set.Ioi u) := by
  have hmajor : IntegrableOn (fun t : ℝ => 2 * t ^ (-2 : ℝ)) (Set.Ioi u) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (lt_of_lt_of_le one_pos hu)).const_mul 2
  refine hmajor.mono' ((measurable_lemma1M.div
    (measurable_id.pow_const 3)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := hu.trans ht.le
  have htpos : 0 < t := one_pos.trans_le ht1
  have hM := lemma1M_abs_le_add_one htpos.le
  have hM2 : |lemma1M t| ≤ 2 * t := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos htpos]
  calc
    |lemma1M t| / t ^ 3 ≤ (2 * t) / t ^ 3 :=
      div_le_div_of_nonneg_right hM2 (by positivity)
    _ = 2 * t ^ (-2 : ℝ) := by
      rw [Real.rpow_neg htpos.le, Real.rpow_two]
      field_simp

/-- The finite Abel endpoint vanishes.  Again, only the elementary bound is used. -/
theorem tendsto_lemma1M_div_sq_nat :
    Tendsto (fun N : ℕ => lemma1M N / (N : ℝ) ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun N : ℕ => 2 * (N : ℝ)⁻¹) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hM := lemma1M_abs_le_add_one (show (0 : ℝ) ≤ N by positivity)
    have hM2 : |lemma1M N| ≤ 2 * (N : ℝ) := by linarith
    have hNabs : |(N : ℝ)| = (N : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg N)
    rw [Real.norm_eq_abs, abs_div, abs_pow, hNabs]
    have hNpos : (0 : ℝ) < N := by positivity
    calc
      |lemma1M N| / (N : ℝ) ^ 2 ≤ (2 * (N : ℝ)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hM2 (sq_nonneg _)
      _ = 2 * (N : ℝ)⁻¹ := by field_simp
  · simpa using
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ))

/-! ## Exact reciprocal-square Abel identity -/

/-- Derivative of the reciprocal-square weight, with the nonzero guard explicit. -/
private theorem hasDerivAt_one_div_sq {t : ℝ} (ht : t ≠ 0) :
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
theorem lemma1_recipSq_finite_abel
    {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    (∑ a ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
      = lemma1M v / v ^ 2 - lemma1M u / u ^ 2
        + 2 * ∫ t in Set.Ioc u v, lemma1M t / t ^ 3 := by
  have hdiff : ∀ t ∈ Set.Icc u v,
      DifferentiableAt ℝ (fun z : ℝ => 1 / z ^ 2) t := by
    intro t ht
    exact (hasDerivAt_one_div_sq
      (show t ≠ 0 by have := hu.trans ht.1; positivity)).differentiableAt
  have hint : IntegrableOn (deriv (fun z : ℝ => 1 / z ^ 2))
      (Set.Icc u v) := by
    have hcont : ContinuousOn (fun t : ℝ => -2 / t ^ 3) (Set.Icc u v) := by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 3)
      intro t ht
      exact pow_ne_zero 3 (ne_of_gt (lt_of_lt_of_le zero_lt_one (hu.trans ht.1)))
    refine (hcont.integrableOn_Icc).congr_fun (fun t ht => ?_) measurableSet_Icc
    exact (hasDerivAt_one_div_sq
      (show t ≠ 0 by have := hu.trans ht.1; positivity)).deriv.symm
  have habel := sum_mul_eq_sub_sub_integral_mul
    (c := fun a : ℕ => (ArithmeticFunction.moebius a : ℝ))
    (f := fun z : ℝ => 1 / z ^ 2) (a := u) (b := v)
    (zero_le_one.trans hu) huv hdiff hint
  simp_rw [sum_Icc_zero_moebius_eq_lemma1M] at habel
  have hintegral :
      (∫ t in Set.Ioc u v,
          deriv (fun z : ℝ => 1 / z ^ 2) t * lemma1M t)
        = -2 * ∫ t in Set.Ioc u v, lemma1M t / t ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change deriv (fun z : ℝ => 1 / z ^ 2) t * lemma1M t =
      -2 * (lemma1M t / t ^ 3)
    rw [(hasDerivAt_one_div_sq
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
    _ = (1 / v ^ 2) * lemma1M v - (1 / u ^ 2) * lemma1M u
          - (-2 * ∫ t in Set.Ioc u v, lemma1M t / t ^ 3) := habel
    _ = lemma1M v / v ^ 2 - lemma1M u / u ^ 2
          + 2 * ∫ t in Set.Ioc u v, lemma1M t / t ^ 3 := by ring

/-- Improper Abel summation for a positive real cutoff `u`:

`sum_{a≤u} mu(a)/a² = sum_a mu(a)/a² + M(u)/u² - 2 integral_u^infinity M(t)/t³`.

All three limiting facts used below were proved above: absolute summability, integrability
on `Ioi u`, and vanishing of the finite endpoint. -/
theorem lemma1_recipSq_head_eq
    {u : ℝ} (hu : 1 ≤ u) :
    (∑ a ∈ Finset.Icc 1 ⌊u⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
      = (∑' a : ℕ,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
        + lemma1M u / u ^ 2
        - 2 * ∫ t in Set.Ioi u, lemma1M t / t ^ 3 := by
  let f : ℕ → ℝ := fun a =>
    (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2
  have hsum : Summable f := summable_lemma1_moebius_div_sq
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
    (integrableOn_lemma1M_div_cube_Ioi hu)
    tendsto_natCast_atTop_atTop
  have hright :
      Tendsto (fun N : ℕ =>
          lemma1M N / (N : ℝ) ^ 2 - lemma1M u / u ^ 2
            + 2 * ∫ t in u..(N : ℝ), lemma1M t / t ^ 3) atTop
        (𝓝 (0 - lemma1M u / u ^ 2
          + 2 * ∫ t in Set.Ioi u, lemma1M t / t ^ 3)) :=
    (tendsto_lemma1M_div_sq_nat.sub tendsto_const_nhds).add
      (hintegral.const_mul 2)
  have heq : ∀ᶠ N : ℕ in atTop,
      (∑ a ∈ Finset.Ioc ⌊u⌋₊ N, f a)
        = lemma1M N / (N : ℝ) ^ 2 - lemma1M u / u ^ 2
            + 2 * ∫ t in u..(N : ℝ), lemma1M t / t ^ 3 := by
    filter_upwards [eventually_ge_atTop (⌊u⌋₊ + 1)] with N hN
    have huN : u ≤ (N : ℝ) := by
      exact (Nat.lt_floor_add_one u).le.trans (by exact_mod_cast hN)
    have habel := lemma1_recipSq_finite_abel hu huN
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
theorem lemma1_recipSqPartialSummation
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    Lemma1RecipSqPartialSummationAt x n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hdiv : 0 < x / (n : ℝ) := div_pos hx hnpos
  have hnxR : (n : ℝ) ≤ x := by
    have hnfloorR : (n : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hnx
    exact hnfloorR.trans (Nat.floor_le hx.le)
  have hratio : 1 ≤ x / (n : ℝ) :=
    (le_div_iff₀ hnpos).2 (by simpa using hnxR)
  have hX : 1 ≤ lemma1X x n := by
    unfold lemma1X
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hratio
  have hhead := lemma1_recipSq_head_eq hX
  rw [tsum_lemma1_moebius_div_sq] at hhead
  have hXsq : lemma1X x n ^ 2 = x / (n : ℝ) := by
    unfold lemma1X
    exact Real.sq_sqrt hdiv.le
  rw [Lemma1RecipSqPartialSummationAt]
  unfold lemma1MobiusRecipHead lemma1SignedTailIntegral
  calc
    x * (∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2)
        = x * (6 / Real.pi ^ 2 +
            lemma1M (lemma1X x n) / lemma1X x n ^ 2 -
            2 * ∫ t in Set.Ioi (lemma1X x n), lemma1M t / t ^ 3) := by
              rw [hhead]
    _ = (6 / Real.pi ^ 2) * x +
          x * (lemma1M (lemma1X x n) / lemma1X x n ^ 2) -
          2 * x * ∫ t in Set.Ioi (lemma1X x n), lemma1M t / t ^ 3 := by
            ring
    _ = (6 / Real.pi ^ 2) * x +
          (n : ℝ) * lemma1M (lemma1X x n) -
          2 * x * ∫ t in Set.Ioi (lemma1X x n), lemma1M t / t ^ 3 := by
            have hmiddle :
                x * (lemma1M (lemma1X x n) / lemma1X x n ^ 2) =
                  (n : ℝ) * lemma1M (lemma1X x n) := by
              rw [hXsq]
              field_simp [hx.ne', ne_of_gt hnpos]
              <;> ring
            rw [hmiddle]

/-! ## Exact finite hyperbola interchange -/

/-- The floor/square-root equivalence used to reindex the hyperbola lattice points.
All denominators are explicitly positive. -/
theorem lemma1_le_floor_X_iff
    {x : ℝ} {a k : ℕ} (hx : 0 ≤ x) (ha : 1 ≤ a) (hk : 1 ≤ k) :
    a ≤ ⌊lemma1X x k⌋₊ ↔ k ≤ ⌊x / (a : ℝ) ^ 2⌋₊ := by
  have haR : (0 : ℝ) < a := by positivity
  have hkR : (0 : ℝ) < k := by positivity
  have hdiv0 : 0 ≤ x / (k : ℝ) := div_nonneg hx hkR.le
  unfold lemma1X
  rw [Nat.le_floor_iff (Real.sqrt_nonneg _),
    Nat.le_floor_iff (div_nonneg hx (sq_nonneg _))]
  rw [Real.le_sqrt (Nat.cast_nonneg a) hdiv0]
  rw [le_div_iff₀ hkR, le_div_iff₀ (sq_pos_of_pos haR)]
  constructor <;> intro h <;> nlinarith

/-- The finite hyperbola residual is a theorem under the exact nonempty-range guards. -/
theorem lemma1_hyperbolaTailInterchange
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    Lemma1HyperbolaTailInterchangeAt x n := by
  have hx0 : 0 ≤ x := hx.le
  have hnR : (0 : ℝ) < n := by positivity
  have hcommon : ∀ k ∈ Finset.Icc n ⌊x⌋₊,
      lemma1M (lemma1X x k)
        = ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
            if a ≤ ⌊lemma1X x k⌋₊
            then (ArithmeticFunction.moebius a : ℝ) else 0 := by
    intro k hk
    have hk' : n ≤ k ∧ k ≤ ⌊x⌋₊ := Finset.mem_Icc.mp hk
    rw [lemma1M_eq_sum]
    have hkpos : 1 ≤ k := hn.trans hk'.1
    have hdiv : x / (k : ℝ) ≤ x / (n : ℝ) :=
      div_le_div_of_nonneg_left hx0 (by positivity) (by exact_mod_cast hk'.1)
    have hfloor : ⌊lemma1X x k⌋₊ ≤ ⌊lemma1X x n⌋₊ :=
      Nat.floor_mono (Real.sqrt_le_sqrt hdiv)
    have hfilter :
        (Finset.Icc 1 ⌊lemma1X x n⌋₊).filter
            (fun a => a ≤ ⌊lemma1X x k⌋₊)
          = Finset.Icc 1 ⌊lemma1X x k⌋₊ := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [← hfilter, Finset.sum_filter]
  rw [Lemma1HyperbolaTailInterchangeAt]
  calc
    (∑ k ∈ Finset.Icc n ⌊x⌋₊, lemma1M (lemma1X x k))
        = ∑ k ∈ Finset.Icc n ⌊x⌋₊,
            ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
              if a ≤ ⌊lemma1X x k⌋₊
              then (ArithmeticFunction.moebius a : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hcommon k hk
    _ = ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
          ∑ k ∈ Finset.Icc n ⌊x⌋₊,
            if a ≤ ⌊lemma1X x k⌋₊
            then (ArithmeticFunction.moebius a : ℝ) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc 1 ⌊lemma1X x n⌋₊,
          (ArithmeticFunction.moebius a : ℝ)
            * ((⌊x / (a : ℝ) ^ 2⌋₊ : ℝ) - (((n - 1 : ℕ) : ℝ))) := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha' : 1 ≤ a ∧ a ≤ ⌊lemma1X x n⌋₊ := Finset.mem_Icc.mp ha
          have hna : n ≤ ⌊x / (a : ℝ) ^ 2⌋₊ :=
            (lemma1_le_floor_X_iff hx0 ha'.1 hn).mp ha'.2
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
                if a ≤ ⌊lemma1X x k⌋₊
                then (ArithmeticFunction.moebius a : ℝ) else 0)
                = ∑ k ∈ Finset.Icc n ⌊x⌋₊,
                    if k ≤ ⌊x / (a : ℝ) ^ 2⌋₊
                    then (ArithmeticFunction.moebius a : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro k hk
            have hk' : n ≤ k ∧ k ≤ ⌊x⌋₊ := Finset.mem_Icc.mp hk
            simpa only [lemma1_le_floor_X_iff hx0 ha'.1 (hn.trans hk'.1)]
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
    _ = lemma1FloorHead x n
          - (((n - 1 : ℕ) : ℝ)) * lemma1M (lemma1X x n) := by
          unfold lemma1FloorHead
          rw [lemma1M_eq_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring


/-- Exact square-root/floor compatibility, derived from their order laws. -/
lemma lemma1_nat_sqrt_floor (x : ℝ) (hx : 0 ≤ x) :
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
theorem squarefreeCount_eq_sum_lemma1M {x : ℝ} (hx : 1 ≤ x) :
    squarefreeCount x = ∑ k ∈ Finset.Icc 1 ⌊x⌋₊, lemma1M (lemma1X x k) := by
  have hx0 : 0 ≤ x := by linarith
  have hnf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
  have htail := lemma1_hyperbolaTailInterchange (by linarith : 0 < x)
    (n := 1) (by norm_num) hnf
  rw [Lemma1HyperbolaTailInterchangeAt] at htail
  norm_num only [Nat.sub_self, Nat.cast_zero, zero_mul, sub_zero] at htail
  rw [htail]
  have hcount := Helfgott.squarefree_coprime_count_exact 1 ⌊x⌋₊ (by norm_num)
  simp only [Nat.coprime_one_right_iff, if_true, Nat.divisors_one,
    Finset.sum_singleton, ArithmeticFunction.moebius_apply_one, Int.cast_one,
    one_mul, Nat.mul_one] at hcount
  have heQ : squarefreeCount x =
      ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.moebius d : ℝ)^2 := by
    rw [squarefreeCount_eq_sum_Icc]
    apply Finset.sum_congr rfl
    intro d hd
    rcases ArithmeticFunction.moebius_eq_or d with h | h | h <;> rw [h] <;> norm_num
  rw [heQ, hcount, lemma1_nat_sqrt_floor x hx0]
  unfold lemma1FloorHead lemma1X
  simp only [Nat.cast_one, div_one]
  apply Finset.sum_congr rfl
  intro d hd
  have he : ⌊x/(d : ℝ)^2⌋₊ = ⌊x⌋₊/(d^2) := by
    rw [← Nat.cast_pow, Nat.floor_div_natCast]
  rw [he]

/-- CDEM (2.1) from the proved convolution and finite hyperbola interchange. -/
theorem lemma1_eq21_of_hyperbolaTail
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊)
    (htail : Lemma1HyperbolaTailInterchangeAt x n) :
    Lemma1Eq21At x n := by
  have hx1 : 1 ≤ x := by
    have hn1 : 1 ≤ ⌊x⌋₊ := hn.trans hnx
    have hf := Nat.floor_le hx.le
    have hnR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn1
    linarith
  rw [Lemma1HyperbolaTailInterchangeAt] at htail
  rw [Lemma1Eq21At, squarefreeCount_eq_sum_lemma1M hx1]
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
theorem lemma1_eq21
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    Lemma1Eq21At x n :=
  lemma1_eq21_of_hyperbolaTail hx hn hnx
    (lemma1_hyperbolaTailInterchange hx hn hnx)

/-- The exact CDEM decomposition, with the Abel and finite-reindex seams closed. -/
theorem lemma1_exactDecomposition
    {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    Lemma1ExactDecompositionAt x n :=
  lemma1_exactDecomposition_of_eq21_and_recipSq hx.le hn
    (lemma1_eq21 hx hn hnx)
    (lemma1_recipSqPartialSummation hx hn hnx)

end MathExtras.CohenDressElMarraki
end

section
/-!
The exact CDEM squarefree identity, stated with the actual Mobius function and
without local helper definitions in its public type. The imported analytic and
finite-sum proof was adapted from the Apache 2.0 source by Gershon Bialer, with
its convolution and reciprocal-square density supplied independently here.
-/

set_option autoImplicit false
set_option Elab.async false

open Finset MeasureTheory ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem cdem_squarefree_exact_decomposition_complete (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    let M : ℝ → ℝ := fun t =>
      ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ)
    let X : ℕ → ℝ := fun j => Real.sqrt (x / (j : ℝ))
    (∑ a ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius a : ℝ)|)
        - (6 / Real.pi ^ 2) * x
      = -2 * x * (∫ t in Set.Ioi (X n), M t / t ^ 3)
        + (∑ j ∈ Finset.Icc 1 (n - 1), M (X j)) + M (X n) / 2
        - (∑ a ∈ Finset.Icc 1 ⌊X n⌋₊,
          (ArithmeticFunction.moebius a : ℝ)
            * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2)) := by
  simpa only [MathExtras.CohenDressElMarraki.Lemma1ExactDecompositionAt,
    MathExtras.CohenDressElMarraki.lemma1Remainder,
    MathExtras.CohenDressElMarraki.lemma1SignedTailIntegral,
    MathExtras.CohenDressElMarraki.lemma1CenteredSum,
    MathExtras.CohenDressElMarraki.lemma1M,
    MathExtras.CohenDressElMarraki.lemma1X,
    MathExtras.CohenDressElMarraki.squarefreeCount_eq_sum_Icc] using
      MathExtras.CohenDressElMarraki.lemma1_exactDecomposition hx hn hnx

end Helfgott
end

open Helfgott Finset MeasureTheory ArithmeticFunction Real
open scoped BigOperators Classical

theorem solution  (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 1 ≤ n) (hnx : n ≤ ⌊x⌋₊) :
    let M : ℝ → ℝ := fun t =>
      ∑ a ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.moebius a : ℝ)
    let X : ℕ → ℝ := fun j => Real.sqrt (x / (j : ℝ))
    (∑ a ∈ Finset.Icc 1 ⌊x⌋₊, |(ArithmeticFunction.moebius a : ℝ)|)
        - (6 / Real.pi ^ 2) * x
      = -2 * x * (∫ t in Set.Ioi (X n), M t / t ^ 3)
        + (∑ j ∈ Finset.Icc 1 (n - 1), M (X j)) + M (X n) / 2
        - (∑ a ∈ Finset.Icc 1 ⌊X n⌋₊,
          (ArithmeticFunction.moebius a : ℝ)
            * (Int.fract (x / (a : ℝ) ^ 2) - 1 / 2)) := Helfgott.cdem_squarefree_exact_decomposition_complete x n hx hn hnx
#print axioms solution
