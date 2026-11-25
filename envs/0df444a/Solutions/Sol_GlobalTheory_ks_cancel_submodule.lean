-- Prove2me | solution 1 for GlobalTheory.ks_cancel_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:10.711315+00:00
-- url     : https://prove2.me/submissions/72148cd6-24dd-4a96-84dc-395e8fefce5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismIndecomposableNilpotentOrBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummand
import Theorems.Thm_GlobalTheory_T_cancel_prod_summand_nilpotent_or_bijective
import Theorems.Thm_GlobalTheory_T_endomorphism_indecomposable_nilpotent_or_bijective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P]
    [IsNoetherian R P] (N : Submodule R P) :
    ∀ (M M' : Type) [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'],
      Nonempty ((M × N) ≃ₗ[R] (M' × N)) → Nonempty (M ≃ₗ[R] M') := by
  induction N using WellFoundedLT.induction with
  | _ N ih =>
  intro M M' _ _ _ _ e
  by_cases hind : ∀ A B : Submodule R N, IsCompl A B → A = ⊥ ∨ B = ⊥
  · exact GlobalTheory.T.cancel_prod_summand_nilpotent_or_bijective R M M' N (GlobalTheory.T.endomorphism_indecomposable_nilpotent_or_bijective R N hind) e
  · push_neg at hind
    obtain ⟨A, B, hAB, hA, hB⟩ := hind
    have hAlt : A.map N.subtype < N := by
      have h1 : A < ⊤ := lt_top_iff_ne_top.mpr (fun h => hB (by
        have := hAB.inf_eq_bot; rw [h, top_inf_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    have hBlt : B.map N.subtype < N := by
      have h1 : B < ⊤ := lt_top_iff_ne_top.mpr (fun h => hA (by
        have := hAB.inf_eq_bot; rw [h, inf_top_eq] at this; exact this))
      have := Submodule.map_strictMono_of_injective N.injective_subtype h1
      rwa [Submodule.map_subtype_top] at this
    let eA : A ≃ₗ[R] A.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype A
    let eB : B ≃ₗ[R] B.map N.subtype := Submodule.equivMapOfInjective _ N.injective_subtype B
    let eN : N ≃ₗ[R] (A.map N.subtype × B.map N.subtype) :=
      (Submodule.prodEquivOfIsCompl A B hAB).symm ≪≫ₗ LinearEquiv.prodCongr eA eB
    obtain ⟨e⟩ := e
    let f : ((M × A.map N.subtype) × B.map N.subtype) ≃ₗ[R]
        ((M' × A.map N.subtype) × B.map N.subtype) :=
      (LinearEquiv.prodAssoc R M _ _) ≪≫ₗ (LinearEquiv.prodCongr (LinearEquiv.refl R M) eN).symm ≪≫ₗ e ≪≫ₗ
        (LinearEquiv.prodCongr (LinearEquiv.refl R M') eN) ≪≫ₗ (LinearEquiv.prodAssoc R M' _ _).symm
    obtain ⟨g⟩ := ih _ hBlt _ _ ⟨f⟩
    exact ih _ hAlt M M' ⟨g⟩
end GlobalTheory
