-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_canonical_log_weights_positive
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:54:53.457804+00:00
-- url     : https://prove2.me/submissions/0790aa3d-e842-40af-a441-1cd5ceb59c7e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) :
    1 ≤ d.m ∧
    (let w : Fin (d.m + 1) → Rat := fun i => Fin.cases d.w0 (fun j => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i
     ∀ i, 0 < (w i : Real)) ∧
    (let v : Fin (d.m + 1) → Rat := fun i => Fin.cases d.v0 (fun j => (((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta)) i
     ∀ i, 0 < (v i : Real)) := by
  refine ⟨d.m_pos, ?_, ?_⟩
  · change ∀ i : Fin (d.m + 1),
      0 < ((Fin.cases d.w0
        (fun j : Fin d.m => ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat)) i : Rat) : Real)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact d.w0_pos
    · simp only [Fin.cases_succ]
      have hceilReal :
          (1 : Real) ≤ (Nat.ceil (Real.log (d.q j.val)) : Real) := by
        rw [← d.x_log j.val]
        exact d.x_one_le (j.val + 1)
      have hceilNat : 1 ≤ Nat.ceil (Real.log (d.q j.val)) := by
        exact_mod_cast hceilReal
      have hposNat : 0 < Nat.ceil (Real.log (d.q j.val)) :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one hceilNat
      exact_mod_cast hposNat
  · change ∀ i : Fin (d.m + 1),
      0 < ((Fin.cases d.v0
        (fun j : Fin d.m =>
          ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta) i : Rat) : Real)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact d.v0_pos
    · simp only [Fin.cases_succ]
      have hceilReal :
          (1 : Real) ≤ (Nat.ceil (Real.log (d.q j.val)) : Real) := by
        rw [← d.x_log j.val]
        exact d.x_one_le (j.val + 1)
      have hceilNat : 1 ≤ Nat.ceil (Real.log (d.q j.val)) := by
        exact_mod_cast hceilReal
      have hposNat : 0 < Nat.ceil (Real.log (d.q j.val)) :=
        Nat.lt_of_lt_of_le Nat.zero_lt_one hceilNat
      have hnum :
          0 < ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) := by
        exact_mod_cast hposNat
      have htheta : 0 < d.base.theta := by
        exact_mod_cast d.base.theta_pos
      have hquot :
          0 < ((Nat.ceil (Real.log (d.q j.val)) : Nat) : Rat) / d.base.theta :=
        div_pos hnum htheta
      exact_mod_cast hquot