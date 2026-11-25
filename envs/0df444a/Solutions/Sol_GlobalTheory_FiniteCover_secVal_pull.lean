-- Prove2me | solution 1 for GlobalTheory.FiniteCover.secVal_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:01:38.173403+00:00
-- url     : https://prove2.me/submissions/1c1d16e5-5cd5-4887-afaf-df6dcc85711e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Theorems.Thm_GlobalTheory_FiniteCover_toField_appLE

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
variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)
namespace GlobalTheory.FiniteCover
theorem _root_.solution (φ : X' ⟶ X) [IsDominant φ] {V : X.Opens} (hV : genericPoint X ∈ V)
    (h₀' : genericPoint X' ∈ (M.pull φ).U fun _ => k₀) (hV' : genericPoint X' ∈ φ ⁻¹ᵁ V)
    (σ : SecOn M V) :
    secVal h₀' hV' (SecOn.pull M φ V σ) = functionFieldMap φ (secVal h₀ hV σ) :=
  toField_appLE φ _ _ _ _
end GlobalTheory.FiniteCover
