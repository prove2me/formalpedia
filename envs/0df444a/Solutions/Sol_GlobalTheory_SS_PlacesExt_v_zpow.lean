-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.v_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:10:31.196262+00:00
-- url     : https://prove2.me/submissions/7546b3fc-1ba5-448e-a264-1ef59f370bcb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField
import Theorems.Thm_GlobalTheory_SS_PlacesExt_v_one
import Theorems.Thm_GlobalTheory_SS_PlacesExt_v_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PlacesExt
open IsDedekindDomain Polynomial ReciprocityTheory.ChartRestriction.G.T0
variable {k F : Type} [Field k] [Field F] [Algebra k F] (Pl : Places k F)
namespace GlobalTheory.SS.PlacesExt
theorem _root_.solution (i : Pl.I) (x : Fˣ) (n : ℤ) : Pl.v i (x ^ n) = n * Pl.v i x := by
  induction n using Int.induction_on with
  | zero => simp [v_one]
  | succ n ih => rw [zpow_add_one, Pl.v_mul, ih]; ring
  | pred n ih => rw [zpow_sub_one, Pl.v_mul, ih, v_inv]; ring
end GlobalTheory.SS.PlacesExt
