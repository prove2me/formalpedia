-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.plainJet_mem_span_X_pow_of_mem_rectangularJetIdeal
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:14:40.632986+00:00
-- url     : https://prove2.me/submissions/07dec37b-3cda-4402-adc4-2ed9980fd9be

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_RectangularJetIdeal
import Mathlib.RingTheory.Ideal.Operations

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : Nat} (c : Fin m -> Complex) (degree : Fin (m + 1) -> Nat)
    (R : MvPolynomial (Fin (m + 1)) Complex)
    (h : R ∈ OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree) :
    OAI.PiExponent.LogarithmicJetIdeals.plainJet c R ∈
      Ideal.span (Set.range (fun k : Fin (m + 1) =>
        (MvPowerSeries.X k : MvPowerSeries (Fin (m + 1)) Complex) ^ (degree k + 1))) := by
  classical
  have hb : ∀ k : Fin (m + 1),
      OAI.PiExponent.LogarithmicJetIdeals.plainJet c
        (MvPolynomial.X k - MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) =
        MvPowerSeries.X k := by
    intro k
    rw [map_sub]
    refine Fin.cases ?_ ?_ k
    · simp [OAI.PiExponent.LogarithmicJetIdeals.plainJet, MvPowerSeries.c_eq_algebraMap]
    · intro i
      simp only [OAI.PiExponent.LogarithmicJetIdeals.plainJet, MvPolynomial.aeval_X,
        MvPolynomial.aeval_C, Fin.cases_succ]
      rw [MvPowerSeries.c_eq_algebraMap]
      ring
  have hle : OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal c degree ≤
      Ideal.comap (OAI.PiExponent.LogarithmicJetIdeals.plainJet c).toRingHom
        (Ideal.span (Set.range (fun k : Fin (m + 1) =>
          (MvPowerSeries.X k : MvPowerSeries (Fin (m + 1)) Complex) ^ (degree k + 1)))) := by
    rw [OAI.PiExponent.LogarithmicJetIdeals.rectangularJetIdeal]
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change (OAI.PiExponent.LogarithmicJetIdeals.plainJet c)
      ((MvPolynomial.X k - MvPolynomial.C ((Fin.cases (1 : Complex) c : Fin (m + 1) -> Complex) k)) ^ (degree k).succ) ∈
      (Ideal.span (Set.range (fun k : Fin (m + 1) =>
        (MvPowerSeries.X k : MvPowerSeries (Fin (m + 1)) Complex) ^ (degree k + 1))))
    rw [map_pow, hb k, Nat.succ_eq_add_one]
    exact Ideal.subset_span ⟨k, rfl⟩
  exact hle h
