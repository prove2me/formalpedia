-- Prove2me | solution 1 for GlobalTheory.KS.InvHom.inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:41:28.652561+00:00
-- url     : https://prove2.me/submissions/d2623fac-6bc2-440d-994b-1bcdfa011eb0

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
import Theorems.Thm_GlobalTheory_KS_InvHom_constFn_mul
import Theorems.Thm_GlobalTheory_KS_InvHom_constFn_zero
import Theorems.Thm_GlobalTheory_KS_InvHom_tr_preimage
import Theorems.Thm_GlobalTheory_KS_InvHom_pull
import Theorems.Thm_GlobalTheory_KS_pbT_add
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
theorem _root_.solution {u u' : epsR K ⟶ A} (hu : IsTangent u) (hu' : IsTangent u') {d d'}
    (hd : IsInvDer u d) (hd' : IsInvDer u' d') : IsInvDer (u * u') (fun W f => d W f + d' W f) := by
  intro W f
  have e : (fst (epsR K) A ≫ (u * u')) * snd (epsR K) A = lift (fst _ _) (tr u') ≫ tr u := by
    rw [MonObj.comp_mul, MonObj.comp_mul, lift_snd, ← Category.assoc, lift_fst, _root_.mul_assoc]
  have h := pull hu hd (lift (fst _ _) (tr u')) W f ((snd (epsR K) A).left ⁻¹ᵁ W)
    (by rw [lift_snd]; exact (tr_preimage hu' W).ge)
  rw [lift_snd, lift_fst, hd' W f, hd' W (d W f)] at h
  rw [e, h, pbT_add]
  have h2 : constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps *
      constFn (R := DualNumber K) (fst (epsR K) A).left ((snd (epsR K) A).left ⁻¹ᵁ W) DualNumber.eps = 0 := by
    rw [← constFn_mul, DualNumber.eps_mul_eps, constFn_zero]
  linear_combination (pbT (snd (epsR K) A).left (d' W (d W f)) ((snd (epsR K) A).left ⁻¹ᵁ W)) * h2
end GlobalTheory.KS.InvHom
