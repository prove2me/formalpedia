-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.localJetIdeal_isCoprime_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T07:10:12.904357+00:00
-- url     : https://prove2.me/submissions/0892fa3c-5e71-4545-bf5e-c5bef04b0b1e

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_jetCoordinate_powers_isCoprime_of_ne

open OAI.PiExponent.LogarithmicJetIdeals

theorem solution
    {m : ℕ} (c d : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (hcd : c ≠ d) :
    IsCoprime (localJetIdeal c T e) (localJetIdeal d T e) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin m, c i ≠ d i := by
    by_contra h
    apply hcd
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  have hcore :=
    OAI.PiExponent.LogarithmicJetIdeals.jetCoordinate_powers_isCoprime_of_ne
      c d T e i hi
  have hleft :
      Ideal.span
        ({jetCoordinate c T i.succ ^ e i.succ} :
          Set (MvPolynomial (Fin (m + 1)) ℂ)) ≤ localJetIdeal c T e := by
    refine Ideal.span_le.2 ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  have hright :
      Ideal.span
        ({jetCoordinate d T i.succ ^ e i.succ} :
          Set (MvPolynomial (Fin (m + 1)) ℂ)) ≤ localJetIdeal d T e := by
    refine Ideal.span_le.2 ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Ideal.subset_span ⟨i.succ, rfl⟩
  rw [Ideal.isCoprime_iff_sup_eq]
  apply top_unique
  calc
    ⊤ =
        Ideal.span
            ({jetCoordinate c T i.succ ^ e i.succ} :
              Set (MvPolynomial (Fin (m + 1)) ℂ)) ⊔
          Ideal.span
            ({jetCoordinate d T i.succ ^ e i.succ} :
              Set (MvPolynomial (Fin (m + 1)) ℂ)) := hcore.sup_eq.symm
    _ ≤ localJetIdeal c T e ⊔ localJetIdeal d T e := sup_le_sup hleft hright