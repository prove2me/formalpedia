-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_volume_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:53:54.598054+00:00
-- url     : https://prove2.me/submissions/150e77ca-0b7d-425d-847c-fafc87c3f653

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_canonical_full_product_ratio
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_canonical_fibre_product_ratio
import Mathlib.Tactic.Ring
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (d.K : Real) * (1 + 3 * (d.sigma : Real)) ^ (d.m + 1) * (∏ i, (w i : Real)) / (∏ i, (v i : Real)) < 1) ∧
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     (d.K : Real) * (1 + 3 * (d.sigma : Real)) ^ d.m * (∏ i : Fin d.m, (w i.succ : Real)) / (∏ i : Fin d.m, (v i.succ : Real)) < 1) := by
  constructor
  · dsimp only
    rw [mul_div_assoc, OAI.PiExponent.FormalInterpolation.canonical_full_product_ratio d]
    convert d.sigma_volume using 1 <;> ring
  · dsimp only
    rw [mul_div_assoc, OAI.PiExponent.FormalInterpolation.canonical_fibre_product_ratio d]
    convert d.sigma_centers using 1 <;> ring