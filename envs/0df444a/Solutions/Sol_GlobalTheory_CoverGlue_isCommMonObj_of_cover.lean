-- Prove2me | solution 1 for GlobalTheory.CoverGlue.isCommMonObj_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:32:46.675807+00:00
-- url     : https://prove2.me/submissions/1218dbe6-b50c-4022-bb90-3f45661af8df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsAbelianSchemeAndRelDimOfOpenCover
import Theorems.Thm_GlobalTheory_CoverGlue_exists_lift
import Theorems.Thm_GlobalTheory_CoverGlue_over_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverGlue
namespace GlobalTheory.CoverGlue
theorem _root_.solution {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {A : Over S}
    [GrpObj A] {G : ∀ i, Over (U i).toScheme} [∀ i, GrpObj (G i)] {ψ : ∀ i, (G i).left ⟶ A.left}
    (h : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (hc : ∀ i, IsCommMonObj (G i)) : IsCommMonObj A := by
  refine (isCommMonObj_iff_isMulCommutative A).2 fun T => ⟨⟨fun x y => ?_⟩⟩
  refine over_ext hU fun i T' r => ?_
  have := hc i
  rw [MonObj.comp_mul, MonObj.comp_mul]
  obtain ⟨a, ha⟩ := exists_lift (h i).1 (r ≫ x)
  obtain ⟨b, hb⟩ := exists_lift (h i).1 (r ≫ y)
  ext1
  rw [(h i).2 T' a b _ _ ha hb, (h i).2 T' b a _ _ hb ha, mul_comm a b]
end GlobalTheory.CoverGlue
