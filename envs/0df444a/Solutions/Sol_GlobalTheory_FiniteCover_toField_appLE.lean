-- Prove2me | solution 1 for GlobalTheory.FiniteCover.toField_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:33:02.423974+00:00
-- url     : https://prove2.me/submissions/0f82e577-25a1-40a0-aaa7-033e11b2d090

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
namespace GlobalTheory.FiniteCover
theorem _root_.solution (φ : X' ⟶ X) [IsDominant φ] {U : X.Opens} {V : X'.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X' ∈ V) (a : Γ(X, U)) :
    toField hV ((φ.appLE U V e).hom a) = functionFieldMap φ (toField hU a) := by
  have h₁ : toField hV ((φ.appLE U V e).hom a) = toField (e hV) ((φ.app U).hom a) :=
    toField_rs e hV _
  rw [h₁, functionFieldMap, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (Scheme.Hom.germ_stalkMap_apply φ U (genericPoint X') (e hV) a).symm
end GlobalTheory.FiniteCover
