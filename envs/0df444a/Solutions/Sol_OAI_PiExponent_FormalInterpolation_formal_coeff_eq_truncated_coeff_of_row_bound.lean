-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.formal_coeff_eq_truncated_coeff_of_row_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-16T11:52:57.408743+00:00
-- url     : https://prove2.me/submissions/1477af3f-33cc-41d2-a339-dffc6d4c4b2c

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open scoped BigOperators

noncomputable section

-- Counterexample to the target: the linear logarithm term is removed by truncation at 1.

@[simp] theorem fin_two_cases_one {A : Sort*} (a : A) (f : Fin 1 → A) :
    Fin.cases a f (1 : Fin 2) = f 0 := rfl

theorem counterexample_formal_coeff :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
      (formalJet (fun _ : Fin 1 => (0 : Complex))
        (MvPolynomial.X (Fin.succ (0 : Fin 1)))) = 1 := by
  classical
  have hcons : (Finsupp.cons 1 (0 : Fin 1 →₀ Nat)) =
      Finsupp.single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [Finsupp.cons]
  have hlog : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
      (liftSeries 1 (PowerSeries.log Complex)) = 1 := by
    rw [← hcons, ← MvPowerSeries.coeff_coeff_finSuccEquiv]
    simp [liftSeries]
  simpa [formalJet, MvPowerSeries.coeff_X,
    Finsupp.single_eq_single_iff] using hlog

theorem counterexample_truncated_coeff :
    (truncatedPolynomialJet (fun _ : Fin 1 => (0 : Complex)) (fun _ => 1)
      (MvPolynomial.X (Fin.succ (0 : Fin 1)))).coeff
        (Finsupp.single (0 : Fin 2) 1) = 0 := by
  classical
  have hlog : InterpolationMatrix.truncatedLog 1 = 0 := by
    ext n
    simp [InterpolationMatrix.truncatedLog]
  simp [truncatedPolynomialJet, hlog, MvPolynomial.coeff_X,
    Finsupp.single_eq_single_iff]

theorem target_counterexample :
    ∃ (P : WeightedPolynomial 1 (fun _ : Fin 1 => 1) 2)
      (rho : InterpolationMatrix.Row 1 1 1 (fun _ : Fin 1 => 1) 2),
      (∀ i : Fin 1, InterpolationMatrix.rowWeights 1 1 (fun _ : Fin 1 => 1) i.succ ≤
        ((1 : Nat) : Real) * InterpolationMatrix.rowWeights 1 1
          (fun _ : Fin 1 => 1) 0) ∧
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (formalJet (fun i => (rho.1.val : Complex) * (0 : Complex)) P.val) ≠
        (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * (0 : Complex))
          (fun _ => 1) P.val).coeff (InterpolationMatrix.exponentVector rho.2.val) := by
  classical
  let P : WeightedPolynomial 1 (fun _ : Fin 1 => 1) 2 :=
    ⟨MvPolynomial.X (Fin.succ (0 : Fin 1)), by
      intro a ha
      simp only [MvPolynomial.support_X, Finset.mem_singleton] at ha
      subst a
      norm_num [InterpolationMatrix.columnWeights, Fin.sum_univ_succ,
        Finsupp.single_apply]⟩
  let b : Fin 2 → Nat := Fin.cases 1 (fun _ => 0)
  have hb : b ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights 1 1 (fun _ : Fin 1 => 1)) 2 := by
    norm_num [strictWeightedSimplex, realWeightedSimplex, b,
      InterpolationMatrix.rowWeights, Fin.sum_univ_succ,
      Fintype.mem_piFinset, Finset.mem_range, Fin.forall_fin_succ]
  let rho : InterpolationMatrix.Row 1 1 1 (fun _ : Fin 1 => 1) 2 :=
    ⟨0, ⟨b, hb⟩⟩
  have hbexp : InterpolationMatrix.exponentVector b =
      Finsupp.single (0 : Fin 2) 1 := by
    ext i
    fin_cases i <;> simp [InterpolationMatrix.exponentVector, b]
  refine ⟨P, rho, ?_, ?_⟩
  · intro i
    norm_num [InterpolationMatrix.rowWeights]
  · simp only [rho, P, mul_zero, hbexp]
    rw [counterexample_formal_coeff, counterexample_truncated_coeff]
    exact one_ne_zero

-- Negation of the full quantified target, derived from the certified witness.
theorem solution :
    ¬ (∀ {m : Nat} (K : Nat) (w0 v0 theta : Real) (w : Fin m → Real) (H : Real)
      (r : Fin m → Complex) (T : Fin m → Nat)
      (_hT : ∀ i, InterpolationMatrix.rowWeights v0 theta w i.succ ≤
        (T i : Real) * InterpolationMatrix.rowWeights v0 theta w 0)
      (P : WeightedPolynomial w0 w H)
      (rho : InterpolationMatrix.Row K v0 theta w H),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (formalJet (fun i => (rho.1.val : Complex) * r i) P.val) =
        (truncatedPolynomialJet (fun i => (rho.1.val : Complex) * r i) T P.val).coeff
          (InterpolationMatrix.exponentVector rho.2.val)) := by
  intro h
  obtain ⟨P, rho, hT, hne⟩ := target_counterexample
  exact hne (@h 1 1 1 1 1 (fun _ => 1) 2 (fun _ => 0) (fun _ => 1) hT P rho)
