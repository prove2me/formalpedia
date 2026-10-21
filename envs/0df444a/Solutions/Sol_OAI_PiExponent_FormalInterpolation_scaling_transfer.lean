-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.scaling_transfer
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T13:17:39.899694+00:00
-- url     : https://prove2.me/submissions/0d5e90a8-64f2-4893-86a2-abcde70dde38

import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem solution
    (m K : Nat) (sigma : Rat) (w v : Fin (m + 1) -> Rat)
    (hN : OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics m K w v sigma)
    (q : Rat) (hq : 1 < q)
    (hvol : (q : Real) ^ (m + 1) *
      ((K : Real) * (1 + 3 * (sigma : Real)) ^ (m + 1) *
        Finset.prod Finset.univ (fun i => (w i : Real)) /
          Finset.prod Finset.univ (fun i => (v i : Real))) < 1)
    (hfibre : (q : Real) ^ m *
      ((K : Real) * (1 + 3 * (sigma : Real)) ^ m *
        Finset.prod Finset.univ (fun i : Fin m => (w i.succ : Real)) /
          Finset.prod Finset.univ (fun i : Fin m => (v i.succ : Real))) < 1)
    (hcoord : forall i : Fin m,
      (q : Real) * ((1 + (sigma : Real)) * (w i.succ : Real)) <
        (v i.succ : Real)) :
    OAI.PiExponent.FormalInterpolation.LogarithmicInterpolationNumerics
      m K (fun i => q * w i) v sigma := by
  refine {
    m_pos := hN.m_pos
    K_pos := hN.K_pos
    sigma_pos := hN.sigma_pos
    degree_pos := ?_
    jet_pos := hN.jet_pos
    volume := ?_
    fibre_volume := ?_
    separated := ?_
    coordinate_ratio := ?_ }
  · intro i
    have hqpos : 0 < q := by linarith
    have hqposR : 0 < (q : Real) := by exact_mod_cast hqpos
    simpa only [Rat.cast_mul] using (mul_pos hqposR (hN.degree_pos i))
  · convert hvol using 1 <;> simp [Finset.prod_mul_distrib] <;> ring
  · convert hfibre using 1 <;> simp [Finset.prod_mul_distrib] <;> ring
  · intro A B hcard i hne hi hnot htail
    have hsep := hN.separated A B hcard i hne hi hnot htail
    have hqpow : 1 ≤ (q : Real) ^ A.card :=
      one_le_pow₀ (by exact_mod_cast hq.le : (1 : Real) ≤ (q : Real))
    have hprod : 0 < Finset.prod A (fun j => (w j : Real)) :=
      Finset.prod_pos fun j hj => hN.degree_pos j
    have hscale :
        Finset.prod A (fun j => ((q * w j : Rat) : Real)) =
          (q : Real) ^ A.card * Finset.prod A (fun j => (w j : Real)) := by
      simp only [Rat.cast_mul]
      rw [Finset.prod_mul_distrib]
      simp
    rw [hscale]
    calc
      OAI.PiExponent.interpolationSeparationConstant m sigma *
          Finset.prod B (fun j => (v j : Real)) <
          Finset.prod A (fun j => (w j : Real)) := hsep
      _ ≤ (q : Real) ^ A.card * Finset.prod A (fun j => (w j : Real)) :=
        le_mul_of_one_le_left (le_of_lt hprod) hqpow
  · intro i
    convert hcoord i using 1 <;> push_cast <;> ring
