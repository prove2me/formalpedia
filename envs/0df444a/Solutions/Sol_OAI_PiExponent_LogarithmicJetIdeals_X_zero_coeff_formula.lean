-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.X_zero_coeff_formula
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T18:17:23.144251+00:00
-- url     : https://prove2.me/submissions/82f2f33f-e04f-4259-89f5-7fccd2a9e220

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution {m : Nat} (d : Fin (m + 1) -> Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
      (MvPowerSeries.X 0) =
      if (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) then 1 else 0 := by
  classical
  rw [MvPowerSeries.coeff_X]
  have hiff :
      (Finsupp.equivFunOnFinite.symm d = Finsupp.single (0 : Fin (m + 1)) 1) ↔
        (d 0 = 1 ∧ ∀ i : Fin (m + 1), i ≠ 0 → d i = 0) := by
    constructor
    · intro h
      constructor
      · have h0 := congrArg (fun f : Fin (m + 1) →₀ Nat => f 0) h
        simpa using h0
      · intro i hi
        have hii := congrArg (fun f : Fin (m + 1) →₀ Nat => f i) h
        simpa [hi] using hii
    · rintro ⟨h0, hne⟩
      apply Finsupp.ext
      intro i
      by_cases hi : i = 0
      · subst i
        simp [h0]
      · simpa [hi] using hne i hi
  exact if_congr hiff rfl rfl