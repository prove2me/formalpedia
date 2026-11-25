-- Prove2me | solution 1 for GlobalTheory.FiniteCover.exists_toField_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:42:11.341813+00:00
-- url     : https://prove2.me/submissions/849863e5-302d-45d9-93a0-ef24ee3a9c83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Theorems.Thm_GlobalTheory_FiniteCover_toField_injective

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
theorem _root_.solution {D : X.Opens} (hD : genericPoint X ∈ D) {I : Type} (O : I → X.Opens)
    (hO : ∀ a, O a ≤ D) (hc : D ≤ ⨆ a, O a) (hη : ∀ a, genericPoint X ∈ O a) (x : X.functionField)
    (hx : ∀ a, ∃ y, toField (hη a) y = x) : ∃ y, toField hD y = x := by
  choose y hy using hx
  obtain ⟨z, hz, -⟩ := X.sheaf.existsUnique_gluing' O D (fun a => homOfLE (hO a)) hc y
    fun a b => toField_injective (U := O a ⊓ O b) (generic_inf (hη a) (hη b))
      (((toField_rs inf_le_left _ _).trans (hy a)).trans ((toField_rs inf_le_right _ _).trans (hy b)).symm)
  obtain ⟨a, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc hD)
  exact ⟨z, (toField_rs (hO a) (hη a) z).symm.trans ((congrArg _ (hz a)).trans (hy a))⟩
end GlobalTheory.FiniteCover
