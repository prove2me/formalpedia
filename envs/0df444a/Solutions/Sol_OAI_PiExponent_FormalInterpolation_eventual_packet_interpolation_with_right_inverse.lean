-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.eventual_packet_interpolation_with_right_inverse
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T20:14:16.17938+00:00
-- url     : https://prove2.me/submissions/17c31e47-5f3c-4902-b99e-720daa86d283
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_FormalInterpolation_eventual_packet_interpolation

open Filter Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    (nu : Real) (hnu : 2 < nu) (d : FixedData nu) :
    Exists fun R : Rat => 0 < R /\ Exists fun N : Nat =>
      forall n : Nat, N <= n ->
        Exists fun F : (Row d ((n : Real) * (R : Real)) -> Complex) ->
          FormalInterpolation.WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real)) =>
          forall y : (Row d ((n : Real) * (R : Real)) -> Complex),
            FormalInterpolation.packetMap d ((n : Real) * (R : Real)) (F y) = y := by
  obtain ⟨R, hR, hEventually⟩ :=
    OAI.PiExponent.FormalInterpolation.eventual_packet_interpolation nu hnu d
  rcases Filter.eventually_atTop.1 hEventually with ⟨N, hN⟩
  refine ⟨R, hR, N, ?_⟩
  intro n hn
  have hSurj : Function.Surjective
      (FormalInterpolation.packetMap d ((n : Real) * (R : Real))) := hN n hn
  refine ⟨fun y => Classical.choose (hSurj y), ?_⟩
  intro y
  exact Classical.choose_spec (hSurj y)
