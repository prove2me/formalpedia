-- Prove2me | solution 1 for JMMS.exists_isMinimal_subshift_mulEquiv_IETOn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T15:34:18.155988+00:00
-- url     : https://prove2.me/submissions/29d04758-8069-479f-bf70-e91a37e12a5c

import Mathlib
import Definitions.Def_CantorSystems
import Theorems.Thm_JMMS_exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le

section

open CantorSystems IntervalExchange

namespace JMMS

/-- Proposition 5.11 (corrected) is the first part of the milestone that adds Lemma 5.13. -/
theorem chk_exists_isMinimal_subshift_mulEquiv_IETOn
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      ∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S), h x ∉ cosetsOf Λ σ →
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x) := by
  obtain ⟨k, S, h1, h2, h3, -⟩ :=
    exists_isMinimal_subshift_mulEquiv_IETOn_and_complexity_le Λ hΛ hfg σ hσ
  exact ⟨k, S, h1, h2, h3⟩

end JMMS

end

open CantorSystems IntervalExchange
theorem solution
    (Λ : AddSubgroup UnitAddCircle) (hΛ : (Λ : Set UnitAddCircle).Infinite) (hfg : Λ.FG)
    (σ : Finset UnitAddCircle) (hσ : σ.Nonempty) :
    ∃ k : ℕ, ∃ S : Subshift Λ (Fin k), IsCantorSpace S ∧ AddAction.IsMinimal Λ S ∧
      ∃ π : topologicalFullGroup Λ S ≃* IETOn Λ σ, ∃ h : S → UnitAddCircle,
        Continuous h ∧ Function.Surjective h ∧
        ∀ (g : topologicalFullGroup Λ S) (x : S), h x ∉ cosetsOf Λ σ →
          h ((g : S ≃ₜ S) x) = (π g : Equiv.Perm UnitAddCircle) (h x) :=
  JMMS.chk_exists_isMinimal_subshift_mulEquiv_IETOn Λ hΛ hfg σ hσ
