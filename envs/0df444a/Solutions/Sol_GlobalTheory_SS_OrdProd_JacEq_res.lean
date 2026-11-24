-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.JacEq.res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:53:35.752861+00:00
-- url     : https://prove2.me/submissions/e6dd17a3-a36d-4aa1-954f-398e3acf6ea7

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
import Theorems.Thm_GlobalTheory_SS_OrdProd_jac_res
import Theorems.Thm_GlobalTheory_SS_OrdProd_cstK_res
import Theorems.Thm_GlobalTheory_SS_OrdProd_app_res

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
variable {R : Type} [CommRing R] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.OrdProd
namespace JacEq
theorem _root_.solution {I : Type} [Fintype I] [DecidableEq I] {M : Model R A} {D : I → VF A} {c : K}
    {U V : M.Y.left.Opens} {t : I → Γ(M.Y.left, U)} {s : Γ(M.Y.left, U)} (H : JacEq M D c U t s) (h : V ≤ U) :
    JacEq M D c V (fun i => (M.Y.left.presheaf.map (homOfLE h).op).hom (t i))
      ((M.Y.left.presheaf.map (homOfLE h).op).hom s) := by
  unfold JacEq at H ⊢
  simp only [app_res]
  rw [jac_res, H, map_mul, cstK_res]
end JacEq
end GlobalTheory.SS.OrdProd
