-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.zero_truncated_packet_implies_ideal_power
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-16T11:52:17.579956+00:00
-- url     : https://prove2.me/submissions/7deffea9-7b6d-469d-aaa2-f7260484ffd3

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Algebra.Polynomial.Coeff

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

/- The requested target is false. The following proved lemmas verify the
counterexample m = 0, K = 2, v0 = theta = H = n = e(0) = 1,
P = X 0 - 1. The theorem solution negates the entire target proposition. -/

noncomputable section

theorem counterexample_packet_zero :
    truncatedPolynomialPacket 2 1 1 (fun i : Fin 0 => Fin.elim0 i) 1
      (fun i : Fin 0 => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
      (MvPolynomial.X (0 : Fin 1) - 1) = 0 := by
  classical
  funext rho
  have ha : rho.2.val = (fun _ => 0) := by
    have hlt := (Finset.mem_filter.mp rho.2.property).2
    change (∑ i : Fin 1, InterpolationMatrix.rowWeights 1 1
      (fun i : Fin 0 => Fin.elim0 i) i * (rho.2.val i : Real)) < 1 at hlt
    simp only [InterpolationMatrix.rowWeights, Fin.sum_univ_one,
      Fin.cases_zero, one_mul] at hlt
    have hzlt : rho.2.val 0 < 1 := by exact_mod_cast hlt
    have hz : rho.2.val 0 = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hzlt)
    funext i
    simpa only [Fin.eq_zero i] using hz
  have hexp : InterpolationMatrix.exponentVector rho.2.val = 0 := by
    ext i
    simp [InterpolationMatrix.exponentVector, ha]
  simp [truncatedPolynomialPacket, truncatedPolynomialJet, hexp]

theorem counterexample_centers_ideal :
    logarithmicCentersIdeal (fun _ : Fin 2 => fun i : Fin 0 => Fin.elim0 i)
      (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 1) =
      Ideal.span ({(MvPolynomial.X (0 : Fin 1) - 1)^2} :
        Set (MvPolynomial (Fin 1) Complex)) := by
  classical
  have hc : ∀ c : Fin 0 → Complex,
      logarithmicCenterIdeal c (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 1) =
      Ideal.span ({MvPolynomial.X (0 : Fin 1) - 1} :
        Set (MvPolynomial (Fin 1) Complex)) := by
    intro c
    unfold logarithmicCenterIdeal
    congr 1
    ext p
    simp [Set.mem_range, logarithmicCoordinate, Fin.exists_fin_one, eq_comm]
  simp only [logarithmicCentersIdeal, hc, Fin.prod_univ_two,
    Ideal.span_singleton_mul_span_singleton, pow_two]

theorem counterexample_not_mem :
    (MvPolynomial.X (0 : Fin 1) - 1) ∉
      (logarithmicCentersIdeal (fun _ : Fin 2 => fun i : Fin 0 => Fin.elim0 i)
        (fun i : Fin 0 => Fin.elim0 i) (fun _ : Fin 1 => 1)) ^ 1 := by
  classical
  rw [pow_one, counterexample_centers_ideal, Ideal.mem_span_singleton']
  rintro ⟨q, hq⟩
  let f : MvPolynomial (Fin 1) Complex →+* Polynomial Complex :=
    MvPolynomial.eval₂Hom Polynomial.C (fun _ => Polynomial.X + 1)
  have hf : f (MvPolynomial.X (0 : Fin 1) - 1) = Polynomial.X := by
    simp [f]
  have heq := congrArg f hq
  simp only [map_mul, map_pow, hf] at heq
  have hcoeff := congrArg (fun p : Polynomial Complex => p.coeff 1) heq
  simp [Polynomial.coeff_mul_X_pow'] at hcoeff

-- This negates the entire target, including all its hypotheses.
theorem solution :
    ¬ (∀ {m K : Nat} (v0 theta : Real) (w : Fin m → Real) (H : Real)
      (r : Fin m → Complex) (T : Fin m → Nat) (e : Fin (m + 1) → Nat),
      0 < v0 → 0 < theta → (∀ i, 0 < w i) → 0 < H → (∀ i, 0 < e i) →
      (∀ i : Fin m, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
        (T i : Real) * InterpolationMatrix.rowWeights v0 theta w 0) →
      (∀ i : Fin (m + 1), H ≤ (e i : Real) *
        InterpolationMatrix.rowWeights v0 theta w i) →
      ∀ (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex),
      truncatedPolynomialPacket K v0 theta w ((n : Real) * H) r T P = 0 →
      P ∈ (logarithmicCentersIdeal
        (fun j : Fin K => fun i => (j.val : Complex) * r i) T e) ^ n) := by
  intro h
  have hn := h (m := 0) (K := 2) 1 1 (fun i => Fin.elim0 i) 1
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun _ => 1)
    zero_lt_one zero_lt_one (fun i => Fin.elim0 i) zero_lt_one
    (fun _ => Nat.zero_lt_one) (fun i => Fin.elim0 i)
    (by
      intro i
      rw [Fin.eq_zero i]
      simp [InterpolationMatrix.rowWeights])
  have hm := hn (1 : Nat) (MvPolynomial.X (0 : Fin 1) - 1)
    (by
      rw [Nat.cast_one, one_mul]
      exact counterexample_packet_zero)
  have hc : (fun j : Fin 2 => fun i : Fin 0 => (j.val : Complex) * Fin.elim0 i) =
      (fun _ : Fin 2 => fun i : Fin 0 => Fin.elim0 i) := by
    funext j i
    exact Fin.elim0 i
  rw [hc] at hm
  exact counterexample_not_mem hm
