-- Prove2me | solution 1 for GlobalTheory.eq_of_isGen_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:06:02.175251+00:00
-- url     : https://prove2.me/submissions/3b2ef4ae-2156-4c07-9b64-c81e35d8db5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIsGenOfInvariant
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EqOfIsGenTransl
import Theorems.Thm_GlobalTheory_exists_isGen_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b b' : TF (R := R) F ⟶ D.P.A) (r : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] ![1, -1])), r.IsGen → b = b' := by
  intro R _ _ D F _ _ b b' r hr
  have key : b * b'⁻¹ = 1 := by
    refine D.P.ktriv F (TF (R := R) F).hom (b * b'⁻¹) fun p => ⟨⊤, trivial, ?_⟩
    have h3 : (fun i => (DegPre.trPt D F b'⁻¹).left ≫ ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] i) =
        ![(lift (fst (TF (R := R) F) D.P.A ≫ (b * b'⁻¹)) (snd (TF (R := R) F) D.P.A) ≫ μ[D.P.A]).left, (snd (TF (R := R) F) D.P.A).left] := by
      have g : ∀ m : TF (R := R) F ⟶ D.P.A, DegPre.trPt D F b'⁻¹ ≫ DegPre.trPt D F m ≫ DegPre.prB D F =
          (fst (TF (R := R) F) D.P.A ≫ (m * b'⁻¹)) * DegPre.prB D F := fun m => by
        rw [DVR.tr_pr, MonObj.comp_mul, DVR.tr_pr, ← Category.assoc, DVR.tr_fst, MonObj.comp_mul]
        exact (_root_.mul_comm _ _).trans ((congrArg _ (_root_.mul_comm _ _)).trans (_root_.mul_assoc _ _ _).symm)
      funext i
      fin_cases i
      · exact congrArg (fun q => q.left) (g b)
      · refine congrArg (fun q => q.left) ((g b').trans ?_)
        rw [mul_inv_cancel, MonObj.comp_one, _root_.one_mul]
    have h4 : ∃ w : LB.Gen (LB.LinComb D.P.L (fun i => (DegPre.trPt D F b'⁻¹).left ≫ ![(DegPre.trPt D F b ≫ DegPre.prB D F).left, (DegPre.trPt D F b' ≫ DegPre.prB D F).left] i) ![1, -1]), w.IsGen :=
      ⟨_, DVR.pullGen_isGen _ _ _ r hr _⟩
    rw [h3] at h4
    obtain ⟨w, hw⟩ := h4
    exact exists_isGen_pull (translDiff D.P.A D.P.L (b * b'⁻¹)) w hw _
  exact mul_inv_eq_one.1 key
end GlobalTheory
