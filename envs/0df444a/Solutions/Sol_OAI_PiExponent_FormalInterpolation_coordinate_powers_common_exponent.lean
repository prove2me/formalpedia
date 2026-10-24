-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.coordinate_powers_common_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:58:35.722726+00:00
-- url     : https://prove2.me/submissions/940e9887-67a4-48ae-9f68-20804af849ad

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

open scoped BigOperators

theorem solution {d : Nat} (J : Ideal (MvPolynomial (Fin d) ℂ))
    (hpow : ∀ i : Fin d, ∃ e : Nat, 0 < e ∧ (MvPolynomial.X i) ^ e ∈ J) :
    ∃ N : Nat, 0 < N ∧ ∀ i : Fin d, (MvPolynomial.X i) ^ N ∈ J := by
  classical
  let e : Fin d → Nat := fun i => Classical.choose (hpow i)
  have he_mem : ∀ i : Fin d, (MvPolynomial.X i) ^ e i ∈ J := by
    intro i
    exact (Classical.choose_spec (hpow i)).2
  let N : Nat := (∑ i : Fin d, e i) + 1
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    omega
  · intro i
    have hle_sum : e i ≤ ∑ j : Fin d, e j :=
      Finset.single_le_sum (fun j hj => Nat.zero_le (e j)) (Finset.mem_univ i)
    have hle : e i ≤ N := by
      dsimp [N]
      omega
    let x : MvPolynomial (Fin d) ℂ := MvPolynomial.X i
    have hfactor : x ^ N = x ^ (N - e i) * x ^ e i := by
      calc
        x ^ N = x ^ ((N - e i) + e i) := by
          congr 1
          exact (Nat.sub_add_cancel hle).symm
        _ = x ^ (N - e i) * x ^ e i := by
          rw [pow_add]
    rw [hfactor]
    exact J.mul_mem_left _ (he_mem i)