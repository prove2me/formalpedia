-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.inv_sc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:43:55.916596+00:00
-- url     : https://prove2.me/submissions/41de4cd9-3d5f-4295-bbf6-aac93b6bfab9

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
import Theorems.Thm_GlobalTheory_KS_InvHom_constFn_spMap
import Theorems.Thm_GlobalTheory_KS_InvHom_constFn_mul
import Theorems.Thm_GlobalTheory_KS_InvHom_pull
import Theorems.Thm_GlobalTheory_KS_pbT_constFn
import Theorems.Thm_GlobalTheory_KS_pbT_mul
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
theorem _root_.solution {v : epsR K ⟶ A} (hv : IsTangent v) {d} (hd : IsInvDer v d) (c : K) :
    IsInvDer (sc c ≫ v) (fun W f => constFn A.hom W c * d W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (sc c ≫ v)) * snd (epsR K) A = (sc c ▷ A) ≫ tr v := by
    rw [MonObj.comp_mul, whiskerRight_snd, whiskerRight_fst_assoc]
  have h := pull hv hd (sc c ▷ A) W f ((snd (epsR K) A).left ⁻¹ᵁ W) (by rw [whiskerRight_snd])
  rw [whiskerRight_snd, whiskerRight_fst] at h
  rw [e, h, pbT_mul, pbT_constFn _ _ le_rfl, ← _root_.mul_assoc]
  congr 2
  have w : (snd (epsR K) A).left ≫ A.hom = (fst (epsR K) A).left ≫ spMap (algebraMap K (DualNumber K)) :=
    (Over.w (snd (epsR K) A)).trans (Over.w (fst (epsR K) A)).symm
  have e2 : epsScaleR c (DualNumber.eps : DualNumber K) = DualNumber.eps * algebraMap K (DualNumber K) c := by
    ext <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  rw [w]
  refine (constFn_spMap (epsScaleR c) (fst (epsR K) A).left _ _).trans ?_
  rw [e2]
  refine (constFn_mul _ _ _ _).trans ?_
  congr 1
  exact (constFn_spMap _ _ _ _).symm
end GlobalTheory.KS.InvHom
