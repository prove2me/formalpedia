-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_grid_event_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:34:20.3933+00:00
-- url     : https://prove2.me/submissions/62e030cf-874b-4e7d-a87f-3744b19e89cd

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_grid_term_event_zero
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Every finite deterministic predictable grid gain is integrable
and has zero integral on every event in the filtration before its start. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (hPsi : ∀ (t : NNReal) (theta : Real),
      (∫ w, Complex.exp (Complex.I*(theta:Complex)*(L.X t w:Complex)) ∂P) =
      Complex.exp (-((t:Real):Complex)*Psi theta))
    (alpha beta : Real) (u : Nat → NNReal) (N : Nat) (hu : Monotone u)
    (a : NNReal) (ha : a ≤ u 0) :
    Integrable (Q L Psi alpha beta u N) P ∧
      ∀ A : Set Ω, MeasurableSet[F a] A →
        (∫ w in A, Q L Psi alpha beta u N w ∂P) = 0 := by
  let q : Nat → Ω → Complex := fun i w =>
    H L Psi alpha beta (u i) w*(E L Psi alpha (u (i+1)) w-E L Psi alpha (u i) w)
  have hTerm (i : Nat) := Kyprianou.Ch04.kw48_grid_term_event_zero L Psi hPsi
    alpha beta (u i) (u (i+1)) (hu (Nat.le_succ i))
  constructor
  · change Integrable (fun w => ∑ i ∈ Finset.range N, q i w) P
    exact integrable_finset_sum _ (fun i hi => (hTerm i).1)
  · intro A hA
    change (∫ w in A, ∑ i ∈ Finset.range N, q i w ∂P) = 0
    rw [integral_finsetSum (Finset.range N) (fun i _ => (hTerm i).1.integrableOn)]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hTerm i).2 A ((F.mono (ha.trans (hu (Nat.zero_le i)))) A hA)
