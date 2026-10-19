-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_of_successor_top_support
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:02:07.143166+00:00
-- url     : https://prove2.me/submissions/8146b087-549c-4e58-b612-eafdf9f5d90c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_coeff_eq_top_sum
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_formalShear_top_sum_eq_coeff

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (delta : Fin m → PowerSeries ℂ) (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hbound : ∀ a ∈ P.support, ∀ i : Fin m, a i.succ ≤ e i.succ)
    (htop : ∀ a ∈ P.support, (∀ i : Fin m, a i.succ = e i.succ) → a = e) :
    MvPowerSeries.coeff e (formalShear delta P) =
      MvPolynomial.coeff e P *
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (e 0)) := by
  rw [OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_coeff_eq_top_sum
    delta e P hbound]
  exact OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_sum_eq_coeff
    e P htop
