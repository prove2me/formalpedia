-- Prove2me | solution 1 for GlobalTheory.FiniteCover.toField_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:56:12.27106+00:00
-- url     : https://prove2.me/submissions/80234f01-842e-4cac-ac48-a0a4898ac982

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_compat


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
theorem _root_.solution {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) {k : M.ι}
    (hk : genericPoint X ∈ M.U k) :
    toField (U := V ⊓ M.U k) (generic_inf (hV) (hk)) (GlobalTheory.LB.coord σ k) =
      toField (U := M.U k ⊓ M.U k₀) (generic_inf (hk) (h₀)) (M.g k k₀).val * secVal h₀ hV σ := by
  have e := congrArg (toField (U := V ⊓ M.U k ⊓ M.U k₀) (generic_inf (generic_inf hV hk) h₀))
    (SecOn.compat σ k k₀ (O := V ⊓ M.U k ⊓ M.U k₀) inf_le_left (inf_le_inf_right _ inf_le_left)
      (inf_le_inf_right _ inf_le_right))
  rw [map_mul, toField_rs, toField_rs, toField_rs] at e
  exact e
end GlobalTheory.FiniteCover
