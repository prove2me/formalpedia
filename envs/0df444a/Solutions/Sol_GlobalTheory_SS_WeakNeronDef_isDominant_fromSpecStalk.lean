-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronDef.isDominant_fromSpecStalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:58:17.450436+00:00
-- url     : https://prove2.me/submissions/1062bfc3-d7ad-4c27-9aba-029622ab5c29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsModelMapDefinedWeakNeronFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronDef
namespace GlobalTheory.SS.WeakNeronDef
theorem _root_.solution (X : Scheme.{0}) [IsIntegral X] (x : X) : IsDominant (X.fromSpecStalk x) := by
  refine ⟨?_⟩
  have h : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec X).specializes trivial
  have h2 : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact genericPoint_spec X
  exact h2.mono (Set.singleton_subset_iff.2 h)
end GlobalTheory.SS.WeakNeronDef
