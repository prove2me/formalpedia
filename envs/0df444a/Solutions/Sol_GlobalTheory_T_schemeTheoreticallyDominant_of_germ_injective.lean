-- Prove2me | solution 1 for GlobalTheory.T.schemeTheoreticallyDominant_of_germ_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:43:53.439086+00:00
-- url     : https://prove2.me/submissions/15bee4f1-98bb-4738-8c31-cce5ae6c27ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchemeTheoreticallyDominantOfGermInjectiveStatement
import Theorems.Thm_P2M_GlobalTheory_isSchemeTheoreticallyDominant___of_germ_eq_zero_over_affine_6b5f7e9382c1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X T : Scheme.{0}) (p : X ⟶ T) (W : X.Opens),
    (∀ (U : X.Opens) (V : T.Opens), IsAffineOpen U → IsAffineOpen V → U ≤ p ⁻¹ᵁ V →
      ∀ b : Γ(X, U), (∀ (x : X) (hx : x ∈ U), x ∈ W → X.presheaf.germ U x hx b = 0) → b = 0) →
    IsSchemeTheoreticallyDominant W.ι := by
  first | exact @GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | exact GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine | (intros; apply GlobalTheory.isSchemeTheoreticallyDominant_ι_of_germ_eq_zero_over_affine <;> assumption)
end _root_.GlobalTheory.T
