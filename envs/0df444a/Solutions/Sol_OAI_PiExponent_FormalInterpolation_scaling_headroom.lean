-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaling_headroom
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:48:46.936869+00:00
-- url     : https://prove2.me/submissions/3eccb676-6c80-4312-9aa3-80e4527477d3

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_scaling_headroom_local_interval

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (m : Nat) (A B : Real) (c d : Fin m -> Real)
    (hA : A < 1) (hB : B < 1)
    (hcd : forall i, c i < d i) :
    exists q : Rat, 1 < q /\
      ((q : Real) ^ (m + 1) * A < 1) /\
      ((q : Real) ^ m * B < 1) /\
      (forall i, (q : Real) * c i < d i) := by
  obtain ⟨ε, hε, hlocal⟩ :=
    OAI.PiExponent.FormalInterpolation.scaling_headroom_local_interval
      m A B c d hA hB hcd
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show (1 : Real) < 1 + ε by linarith)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hq₁
  · exact hlocal (q : Real) (by exact_mod_cast hq₁) (by exact_mod_cast hq₂) |>.1
  · exact hlocal (q : Real) (by exact_mod_cast hq₁) (by exact_mod_cast hq₂) |>.2.1
  · exact (hlocal (q : Real) (by exact_mod_cast hq₁) (by exact_mod_cast hq₂)).2.2