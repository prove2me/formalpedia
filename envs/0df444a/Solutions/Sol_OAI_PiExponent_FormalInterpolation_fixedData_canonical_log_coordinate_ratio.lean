-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_coordinate_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:41:58.17276+00:00
-- url     : https://prove2.me/submissions/ba412b8b-203e-4039-a618-644b965749b8

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     ∀ i : Fin d.m, (1 + (d.sigma : Real)) * (w i.succ : Real) < (v i.succ : Real)) := by
  dsimp only
  intro i
  have hq : 2 ≤ d.q i.val := (d.approximations i.val).1
  have hlog : 0 < Real.log (d.q i.val) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < d.q i.val by omega)
  let n : Nat := Nat.ceil (Real.log (d.q i.val))
  have hn : 0 < n := Nat.ceil_pos.mpr hlog
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hscale : (1 + (d.sigma : Real)) < 1 / (d.base.theta : Real) := by
    exact (lt_div_iff₀ d.base.theta_pos).2 d.sigma_theta
  have hmul := mul_lt_mul_of_pos_right hscale hnR
  have hnatcast : (((Nat.ceil (Real.log (d.q i.val)) : Nat) : Rat) : Real) = (n : Real) := by
    simp [n]
  have hdivcast :
      ((((Nat.ceil (Real.log (d.q i.val)) : Nat) : Rat) / d.base.theta : Rat) : Real) =
        (n : Real) / (d.base.theta : Real) := by
    simp [n]
  simp only [Fin.cases_succ]
  rw [hnatcast, hdivcast]
  calc
    (1 + (d.sigma : Real)) * (n : Real) < (1 / (d.base.theta : Real)) * (n : Real) := hmul
    _ = (n : Real) / (d.base.theta : Real) := by ring