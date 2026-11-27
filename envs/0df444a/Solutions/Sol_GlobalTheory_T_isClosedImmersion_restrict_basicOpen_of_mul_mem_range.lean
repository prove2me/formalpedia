-- Prove2me | solution 1 for GlobalTheory.T.isClosedImmersion_restrict_basicOpen_of_mul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:33:35.56784+00:00
-- url     : https://prove2.me/submissions/666a58aa-a982-4371-a7f0-ee86dc3487f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulM
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedImmersionMorphismRestrictBasicOpenOfMulMStatement
import Theorems.Thm_GlobalTheory_isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range


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
theorem _root_.solution : ∀ (X Z : Scheme.{0}) (φ : X ⟶ Z) (V : Z.Opens), IsAffineOpen V → IsAffineOpen (φ ⁻¹ᵁ V) → ∀ r : Γ(Z, V), (∀ c : Γ(X, φ ⁻¹ᵁ V), ∃ b : Γ(Z, V), (φ.app V).hom r * c = (φ.app V).hom b) → IsClosedImmersion (φ ∣_ Z.basicOpen r) := by
  first | exact @GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | exact GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range | (intros; apply GlobalTheory.isClosedImmersion_morphismRestrict_basicOpen_of_mul_mem_range <;> assumption)
end _root_.GlobalTheory.T
