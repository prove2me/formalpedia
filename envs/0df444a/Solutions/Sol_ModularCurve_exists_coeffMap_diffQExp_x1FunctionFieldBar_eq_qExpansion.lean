-- Prove2me | solution 1 for ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/91156a17-2bf6-5060-ad67-5539ce92c427

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.JH.torsionGaloisRep_apply CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open scoped MatrixGroups

open ModularCurve in
theorem solution
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (hf : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 ⇑f).coeff n ∈ ι₀.range) :
    ∃ ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ],
      ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) := by
  obtain ⟨ω, hω⟩ :=
    ModularCurve.exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpFunctionFieldC_eq_qExpansion
      M (CongruenceSubgroup.Gamma1 M) le_rfl (CongruenceSubgroup.Gamma1_in_Gamma0 M) ι₀ f
      (fun n => hf n)
  refine ⟨ω, ?_⟩
  rw [← ModularCurve.qExpansionDiffAlong_val_eq_diffQExp]
  exact hω

#print axioms solution

end S_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion
end P2MW
export P2MW.S_ModularCurve_exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion (solution)
