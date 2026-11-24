-- Prove2me | solution 1 for GlobalTheory.SS.OrdProd.app_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:20.149616+00:00
-- url     : https://prove2.me/submissions/30e54b8d-ae75-41c6-b453-9ade93df174c

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
variable {R : Type} [CommRing R] [Algebra R K] {A A' : Over (Sp K)}
namespace GlobalTheory.SS.OrdProd
theorem _root_.solution {Q : Model R A'} {M : Model R A} {p : A' ⟶ A} {p' : Q.Y.left ⟶ M.Y.left}
    (e : Q.j ≫ p' = p.left ≫ M.j) {V : M.Y.left.Opens} {W : Q.Y.left.Opens} (h : W ≤ p' ⁻¹ᵁ V)
    (u : Γ(M.Y.left, V)) :
    (Q.j.app W).hom ((p'.appLE V W h).hom u) =
      (p.left.appLE (M.j ⁻¹ᵁ V) (Q.j ⁻¹ᵁ W) (pre_le e h)).hom ((M.j.app V).hom u) := by
  have : p'.appLE V W h ≫ Q.j.app W = M.j.app V ≫ p.left.appLE (M.j ⁻¹ᵁ V) (Q.j ⁻¹ᵁ W) (pre_le e h) := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr_hom e _ _ _ _
  exact congrArg (fun f => f.hom u) this
end GlobalTheory.SS.OrdProd
