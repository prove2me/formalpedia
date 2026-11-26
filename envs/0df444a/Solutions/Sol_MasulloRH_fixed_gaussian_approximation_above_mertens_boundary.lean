-- Prove2me | solution 1 for MasulloRH.fixed_gaussian_approximation_above_mertens_boundary
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:23:45.18793+00:00
-- url     : https://prove2.me/submissions/68c4b3c4-b037-4fb8-a2b0-9be554e9f6ce

import Theorems.Thm_GRH_principal_mobius_partial_sum_subpower
import Theorems.Thm_MasulloRH_finite_theta_energy_approximation_of_mertens_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MasulloRH.GaussianApproximation MeasureTheory Filter Finset

/-- Every window wholly to the right of the recorded Möbius exponent has
arbitrarily accurate rational theta approximations, for every pulse scale. -/
theorem solution (T c b ε : ℝ) (hT : 0≤T) (hb : 0≤b)
    (hleft : (0.8749570698:ℝ)<c-b) (hright : c+b<1) (hε : 0<ε) :
    ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
      energy c b (residual T (fun i => ((a i).1:ℂ)+((a i).2:ℂ)*Complex.I)
        (fun i => (y i:ℝ))) < ε := by
  let β := ((0.8749570698:ℝ)+(c-b))/2
  have hβ : (0.8749570698:ℝ)<β := by dsimp [β];linarith
  have hsum := GRH.principal_mobius_partial_sum_subpower 1 β hβ
  have eqsum (N : ℕ) :
      (∑ k ∈ range (N+1), (1 : DirichletCharacter ℂ 1) (k:ZMod 1) * (ArithmeticFunction.moebius k:ℂ))=
        ∑ k ∈ Icc 1 N, (ArithmeticFunction.moebius k:ℂ) := by
    simp only [Subsingleton.elim (_:ZMod 1) 1,map_one,one_mul]
    have e : range (N+1)=insert 0 (Icc 1 N) := by
      ext i
      simp only [mem_range,mem_insert,mem_Icc]
      omega
    rw [e,sum_insert (by simp)]
    simp
  simp_rw [eqsum] at hsum
  obtain ⟨m,a,y,_,he⟩ := MasulloRH.finite_theta_energy_approximation_of_mertens_bound β c b T ε
    (by linarith) hb hT (by dsimp [β];linarith) hright hsum hε
  exact ⟨m,a,y,he⟩
