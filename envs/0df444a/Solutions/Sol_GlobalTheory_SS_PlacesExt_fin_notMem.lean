-- Prove2me | solution 1 for GlobalTheory.SS.PlacesExt.fin_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:18:11.096804+00:00
-- url     : https://prove2.me/submissions/d86abe59-a6da-4f5b-8154-cc3852de6bd1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsProductFormulaPlacesFunctionField

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
theorem _root_.solution (x : F) : {i | x ∉ Pl.O i}.Finite := by
  by_cases hx : x = 0
  · subst hx; simp
  · refine (Pl.fin (Units.mk0 x hx)).subset fun i hi h => hi ?_
    exact (Pl.mem i (Units.mk0 x hx)).2 (le_of_eq (Eq.symm h))
end GlobalTheory.SS.PlacesExt
