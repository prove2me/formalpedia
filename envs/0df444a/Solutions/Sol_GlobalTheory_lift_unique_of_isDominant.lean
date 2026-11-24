-- Prove2me | solution 1 for GlobalTheory.lift_unique_of_isDominant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:31:08.003223+00:00
-- url     : https://prove2.me/submissions/705a93e1-1025-455e-864c-3e73f2a1a3a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
variable {U T Z Y : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (j : U ⟶ T) [IsDominant j] [IsReduced T] (p : Z ⟶ Y)
    [IsSeparated p] {c c' : T ⟶ Z} (h₁ : j ≫ c = j ≫ c') (h₂ : c ≫ p = c' ≫ p) : c = c' := ext_of_isDominant_of_isSeparated p h₂ j h₁
end GlobalTheory
