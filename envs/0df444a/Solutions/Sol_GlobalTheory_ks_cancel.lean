-- Prove2me | solution 1 for GlobalTheory.ks_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:28.346269+00:00
-- url     : https://prove2.me/submissions/9bd4d577-7556-450b-8e4b-82941a5ba801

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismIndecomposableNilpotentOrBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummand
import Theorems.Thm_GlobalTheory_ks_cancel_submodule

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
theorem _root_.solution : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ _ _ ⟨e⟩
  let t : (⊤ : Submodule R P) ≃ₗ[R] P := Submodule.topEquiv
  exact ks_cancel_submodule R P ⊤ M M'
    ⟨(LinearEquiv.prodCongr (LinearEquiv.refl R M) t) ≪≫ₗ e ≪≫ₗ
      (LinearEquiv.prodCongr (LinearEquiv.refl R M') t).symm⟩
end GlobalTheory
