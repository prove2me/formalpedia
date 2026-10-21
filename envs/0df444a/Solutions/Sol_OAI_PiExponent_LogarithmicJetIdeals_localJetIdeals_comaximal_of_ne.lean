-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localJetIdeals_comaximal_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:13:46.41501+00:00
-- url     : https://prove2.me/submissions/e7dbc5ab-e1cd-4bb5-a5ad-e829b8e28c1d

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinateJetGenerators_comaximal_of_ne
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c d : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ)
    (h : ∃ i : Fin m, c i ≠ d i) :
    localJetIdeal c T e ⊔ localJetIdeal d T e = ⊤ := by
  rcases h with ⟨i, hcd⟩
  have hleft :
      Ideal.span ({jetCoordinate c T i.succ ^ e i.succ} : Set (MvPolynomial (Fin (m + 1)) ℂ)) ≤
        localJetIdeal c T e := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  have hright :
      Ideal.span ({jetCoordinate d T i.succ ^ e i.succ} : Set (MvPolynomial (Fin (m + 1)) ℂ)) ≤
        localJetIdeal d T e := by
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  have hcore :=
    OAI.PiExponent.LogarithmicJetIdeals.coordinateJetGenerators_comaximal_of_ne
      c d T e i hcd
  apply top_unique
  rw [← hcore]
  exact sup_le (le_trans hleft le_sup_left) (le_trans hright le_sup_right)
