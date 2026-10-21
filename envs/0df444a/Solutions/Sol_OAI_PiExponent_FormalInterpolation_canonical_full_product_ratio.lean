-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.canonical_full_product_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T17:51:57.329736+00:00
-- url     : https://prove2.me/submissions/6448d4ad-6840-4d23-ba11-d8c17d0387b6

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (∏ i, (w i : Real)) / (∏ i, (v i : Real)) =
       ((d.w0 : Real) / (d.v0 : Real)) * (d.base.theta : Real) ^ d.m) := by
  classical
  let a : Fin d.m → Rat := fun j => (Nat.ceil (Real.log (d.q j.val)) : Nat)
  have ha (j : Fin d.m) : 0 < (a j : Real) := by
    dsimp [a]
    have hq : 2 ≤ d.q j.val := (d.approximations j.val).1
    have hq' : (1 : Real) < (d.q j.val : Real) := by exact_mod_cast Nat.lt_of_lt_of_le (by decide) hq
    have hl : 0 < Real.log (d.q j.val) := Real.log_pos hq'
    have hc : 0 < Nat.ceil (Real.log (d.q j.val)) := Nat.ceil_pos.mpr hl
    exact_mod_cast hc
  have ht : 0 < (d.base.theta : Real) := d.base.theta_pos
  have hpoint (j : Fin d.m) :
      (a j : Real) / (((a j : Rat) / d.base.theta : Rat) : Real) = (d.base.theta : Real) := by
    have har : 0 < a j := by exact_mod_cast ha j
    have htr : 0 < d.base.theta := by exact_mod_cast ht
    have hr : (a j : Rat) / ((a j : Rat) / d.base.theta) = d.base.theta := by
      field_simp [ne_of_gt har, ne_of_gt htr]
      <;> ring
    exact_mod_cast hr
  have htail :
      (∏ j : Fin d.m, (a j : Real)) /
        (∏ j : Fin d.m, (((a j : Rat) / d.base.theta : Rat) : Real)) =
        (d.base.theta : Real) ^ d.m := by
    rw [← Finset.prod_div_distrib]
    simp_rw [hpoint]
    simp
  dsimp
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  change
    ((d.w0 : Real) * (∏ j : Fin d.m, (a j : Real))) /
        ((d.v0 : Real) *
          (∏ j : Fin d.m, (((a j : Rat) / d.base.theta : Rat) : Real))) =
      ((d.w0 : Real) / (d.v0 : Real)) * (d.base.theta : Real) ^ d.m
  rw [mul_div_mul_comm, htail]
