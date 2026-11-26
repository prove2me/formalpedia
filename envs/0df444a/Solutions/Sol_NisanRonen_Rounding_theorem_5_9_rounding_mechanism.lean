-- Prove2me | solution 1 for NisanRonen.Rounding.theorem_5_9_rounding_mechanism
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:12:43.167811+00:00
-- url     : https://prove2.me/submissions/2837e082-85d7-446b-92ec-3a44dec0fe08

import Theorems.Thm_NisanRonen_Rounding_exists_polytime_solver_with_report_certificates
import Theorems.Thm_NisanRonen_Rounding_approximation_iff_report_certificates
import Theorems.Thm_NisanRonen_Rounding_rounding_mechanism_truthful
import Theorems.Thm_NisanRonen_Rounding_unitMakespan_polytime

open NisanRonen.Rounding

theorem solution :
    ∀ ε : ℝ, 0 < ε → ∀ a : ℝ, 0 < a → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, a < b → ∀ (n : ℕ) [NeZero n],
        ∃ f : List (Fin n → ℕ) → List (Fin n),
          Nonempty (Turing.TM2ComputableInPolyTime (encodeInstance (n := n))
            (id : List (Fin n) → List (Fin n)) f) ∧
          Nonempty (Turing.TM2ComputableInPolyTime (encodeInstanceAlloc (n := n))
            Computability.encodeNat (unitMakespan (n := n))) ∧
          IsExactRoundedSolver f δ a b ∧
          (∀ (k : ℕ) (t : Fin n → Fin k → ℝ), (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
            ∀ i : Fin n, IsDominant f δ a b i (t i) (truthStrategy (t i))) ∧
          (∀ (k : ℕ) (t : Fin n → Fin k → ℝ), (∀ i j, a ≤ t i j ∧ t i j ≤ b) →
            ∀ s : Fin n → Strategy n k, (∀ i, IsDominant f δ a b i (t i) (s i)) →
            ∀ y : Fin k → Fin n,
              makespan (allocOf f δ (fun i => (s i).decl)) (actualTimes f δ s) ≤
                (1 + ε) * makespan y (corrStar y t)) := by
  intro ε hε a ha
  obtain ⟨δ, hδ, hsolver⟩ := exists_polytime_solver_with_report_certificates ε hε a ha
  refine ⟨δ, hδ, ?_⟩
  intro b hab n _
  obtain ⟨f, htime, hf, hcert⟩ := hsolver b hab n
  refine ⟨f, htime, unitMakespan_polytime n, hf, ?_, ?_⟩
  · intro k t ht
    exact rounding_mechanism_truthful ha hab hδ f hf t ht
  · exact (approximation_iff_report_certificates ha hab hδ hε.le f hf).2 hcert
