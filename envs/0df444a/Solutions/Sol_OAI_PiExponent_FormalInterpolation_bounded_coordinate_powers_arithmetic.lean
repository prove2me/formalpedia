-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.bounded_coordinate_powers_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T19:35:17.799007+00:00
-- url     : https://prove2.me/submissions/b504a128-4948-42f3-a152-3f2d2e602962

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_rational_weights_common_integer_scale
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_bounded_weights_common_degree

open scoped BigOperators

theorem solution
    {d : Nat} (I : Ideal (MvPolynomial (Fin d) Complex))
    (w : Fin d -> Rat) (R : Real)
    (hw : forall i, 0 < (w i : Real))
    (s : Nat) (hs : 0 < s) (B : Nat)
    (hBR : (B : Real) < (s : Real) * R)
    (hcoord : forall i : Fin d, exists n : Nat, 0 < n /\
      MvPolynomial.X i ^ n ∈ I ^ s /\
      (n : Real) * (w i : Real) <= (B : Real)) :
    exists q : Nat, exists D : Nat, 0 < q /\ 0 < D /\
      (D : Real) < ((s * q : Nat) : Real) * R /\
      forall i : Fin d, exists n : Nat, exists m : Nat,
        0 < n /\ MvPolynomial.X i ^ n ∈ I ^ s /\
        (n : Real) * (w i : Real) <= (B : Real) /\
        q * n <= m /\ 0 < m /\
        (m : Real) * (w i : Real) = (D : Real) := by
  obtain ⟨L, hL, c, hc⟩ :=
    OAI.PiExponent.FormalInterpolation.rational_weights_common_integer_scale w hw
  let n : Fin d -> Nat := fun i => Classical.choose (hcoord i)
  have hn : forall i : Fin d, 0 < n i /\
      MvPolynomial.X i ^ n i ∈ I ^ s /\
      (n i : Real) * (w i : Real) <= (B : Real) := by
    intro i
    exact Classical.choose_spec (hcoord i)
  have hn_arith : forall i : Fin d, 0 < n i /\
      (n i : Real) * (w i : Real) <= (B : Real) := by
    intro i
    exact ⟨(hn i).1, (hn i).2.2⟩
  obtain ⟨q, D, hq, hD, hcut, hm⟩ :=
    OAI.PiExponent.FormalInterpolation.bounded_weights_common_degree
      w hw R s hs B hBR L hL c hc n hn_arith
  refine ⟨q, D, hq, hD, hcut, ?_⟩
  intro i
  obtain ⟨m, hqm, hmpos, hweight⟩ := hm i
  refine ⟨n i, m, (hn i).1, (hn i).2.1, (hn i).2.2, hqm, hmpos, hweight⟩