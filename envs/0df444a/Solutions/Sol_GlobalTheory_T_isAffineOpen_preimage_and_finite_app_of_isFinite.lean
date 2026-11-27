-- Prove2me | solution 1 for GlobalTheory.T.isAffineOpen_preimage_and_finite_app_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:24.649527+00:00
-- url     : https://prove2.me/submissions/74f40cab-fd9c-45c4-81f5-93514acb6111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestri
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineOpenPreimageAndFiniteAppOfIsFiniteRestriStatement
import Theorems.Thm_GlobalTheory_isAffineOpen_preimage_and_finite_app_of_isFinite_restrict


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsFinite (φ ∣_ V) → IsAffineOpen (φ ⁻¹ᵁ V) ∧ (φ.app V).hom.Finite := by
  first | exact @GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict | exact GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict | (intros; apply GlobalTheory.isAffineOpen_preimage_and_finite_app_of_isFinite_restrict <;> assumption)
end _root_.GlobalTheory.T
