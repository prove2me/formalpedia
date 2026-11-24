-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.inv_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:12.829165+00:00
-- url     : https://prove2.me/submissions/ba6dbe35-6c69-431a-ad88-ea287aadd1cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieCombIffProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHom
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_pbT
import Theorems.Thm_GlobalTheory_KS_InvHom_pbT_app
import Theorems.Thm_GlobalTheory_KS_InvHom_thick
import Theorems.Thm_GlobalTheory_KS_InvHom_tr_preimage
import Theorems.Thm_GlobalTheory_KS_InvHom_pull
import Theorems.Thm_GlobalTheory_PowLie_isTangent_iff


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory.PowLie (sc zeroPt isTangent_iff)
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvHom
variable {K : Type} [Field K]
variable {A : Over (Sp K)} [GrpObj A]
namespace GlobalTheory.KS.InvHom
theorem _root_.solution {A₁ : Over (Sp K)} [GrpObj A₁] (f : A₁ ⟶ A) [IsMonHom f] {w : epsR K ⟶ A₁}
    (hw : IsTangent w) (hwf : IsTangent (w ≫ f)) {dw D} (hdw : IsInvDer w dw) (hD : IsInvDer (w ≫ f) D)
    (W : A.left.Opens) (h : Γ(A.left, W)) :
    dw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h) = (f.left.app W).hom (D W h) := by
  have e : (epsR K ◁ f) ≫ tr (w ≫ f) = tr w ≫ f := by
    rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc]
  have h1 := pull hwf hD (epsR K ◁ f) W h ((snd (epsR K) A₁).left ⁻¹ᵁ (f.left ⁻¹ᵁ W))
    (by rw [whiskerLeft_snd]; exact le_rfl)
  rw [e, whiskerLeft_snd, whiskerLeft_fst, Over.comp_left, Over.comp_left,
    ← pbT_pbT _ _ le_rfl (tr_preimage hw _).ge, ← pbT_pbT _ _ le_rfl le_rfl h,
    ← pbT_pbT _ _ le_rfl le_rfl (D W h), pbT_app f.left, pbT_app f.left, pbT_app, pbT_app] at h1
  have h2 := hdw (f.left ⁻¹ᵁ W) ((f.left.app W).hom h)
  rw [pbT_app, pbT_app] at h2
  have := ((thick A₁).2 (f.left ⁻¹ᵁ W) _).unique (y₁ := (_, _)) (y₂ := (_, _)) h2 h1
  exact congrArg Prod.snd this
end GlobalTheory.KS.InvHom
