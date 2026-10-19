-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.formalShear_top_sum_eq_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T17:10:29.887005+00:00
-- url     : https://prove2.me/submissions/0f9a49cc-978f-47af-99e6-54a7f8e3274e

import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem solution
    {m : ℕ} (e : Fin (m + 1) →₀ ℕ)
    (P : MvPolynomial (Fin (m + 1)) ℂ)
    (htop : ∀ a ∈ P.support, (∀ i : Fin m, a i.succ = e i.succ) → a = e) :
    (∑ a ∈ P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ),
      MvPolynomial.coeff a P *
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (a 0))) =
      MvPolynomial.coeff e P *
        PowerSeries.coeff (e 0) ((PowerSeries.X : PowerSeries ℂ) ^ (e 0)) := by
  classical
  by_cases he : e ∈ P.support
  · have hfilter :
        P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ) = {e} := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hcoords⟩
        exact htop a ha hcoords
      · intro hae
        subst a
        exact ⟨he, fun _ => rfl⟩
    simp [hfilter]
  · have hfilter :
        P.support.filter (fun a => ∀ i : Fin m, a i.succ = e i.succ) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro a ha hcoords
      exact he (htop a ha hcoords ▸ ha)
    have hcoeff : MvPolynomial.coeff e P = 0 :=
      MvPolynomial.notMem_support_iff.mp he
    simp [hfilter, hcoeff]
