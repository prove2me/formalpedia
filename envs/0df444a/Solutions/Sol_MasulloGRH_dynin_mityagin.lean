-- Prove2me | solution 1 for MasulloGRH.dynin_mityagin
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-11-21T07:43:08.656889+00:00
-- url     : https://prove2.me/submissions/b5abf4ca-67d4-4dc3-b312-04714181950c

import Theorems.Thm_MasulloGRH_nuclear_equicontinuous_basis_absolute
import Theorems.Thm_MasulloGRH_schauderBasis_equicontinuous_frechet_or_strictLF
import Theorems.Thm_MasulloGRH_nuclear_of_countable_inductive_limit

set_option autoImplicit false
open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x : ℕ → E) (f : ℕ → StrongDual ℂ E) (hx : IsSchauderBasis x f) :
    (IsNuclear E → IsEquicontinuousBasis x f → IsAbsoluteBasis x f) ∧
    (IsNuclear E → IsFrechet E → IsAbsoluteBasis x f) ∧
    (IsStrictLFOfNuclearFrechet E → IsAbsoluteBasis x f) := by
  have habs := nuclear_equicontinuous_basis_absolute E hE x f hx
  refine ⟨habs, ?_, ?_⟩
  · intro hN hF
    exact habs hN (schauderBasis_equicontinuous_frechet_or_strictLF E hE x f hx (.inl hF))
  · rintro ⟨X, hmono, hexh, hX, htop⟩
    have hLF : IsStrictLF E := ⟨X, hmono, hexh, fun n ↦ (hX n).1, htop⟩
    have hN : IsNuclear E := by
      apply nuclear_of_countable_inductive_limit E hE X (fun n ↦ inferInstance) hexh
      · intro n
        refine ⟨hmono (Nat.le_succ n), ?_⟩
        exact continuous_subtype_val.subtype_mk _
      · exact fun n ↦ (hX n).2
      · exact htop
    exact habs hN (schauderBasis_equicontinuous_frechet_or_strictLF E hE x f hx (.inr hLF))
