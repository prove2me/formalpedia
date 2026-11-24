-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.appLE_cstK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:50:20.094771+00:00
-- url     : https://prove2.me/submissions/83753c19-889c-4409-9f0b-cbd34e546d82

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueModelHasJacobianOrder
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsEqDivOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsVf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsStalkDerivationOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VectorFieldOrderAddOfProdStrictHenselian
import Theorems.Thm_GlobalTheory_SS_OrdProd_appLE_congr_hom

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
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.OrdProd
variable {K : Type} [Field K]
namespace GlobalTheory.SS.OrdProd
theorem _root_.solution {P X : Over (Sp K)} (p : P ⟶ X) (V : X.left.Opens) (W : P.left.Opens)
    (h : W ≤ p.left ⁻¹ᵁ V) (c : K) : (p.left.appLE V W h).hom (cstK X V c) = cstK P W c := by
  have e : X.hom.appLE ⊤ V le_top ≫ p.left.appLE V W h = P.hom.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE p.left X.hom ⊤ V W le_top h).trans ?_
    exact appLE_congr_hom (Over.w p) _ _ _ _
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)) e
end GlobalTheory.SS.OrdProd
