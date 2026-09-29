-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.isStrictTypeOne_frickeInvolutionBar_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/978c1a93-1325-501f-8fa2-8912748f46ea

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar ModularPolynomialData PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frickeInvolutionBar restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem redFst_frickeInvolutionBar_smul' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redFst (frickeInvolutionBar (1 * q) • W) = P.redSnd W := by
  show P.sp _ = P.sp _
  rw [ModularCurve.restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul]

theorem redSnd_frickeInvolutionBar_smul' (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redSnd (frickeInvolutionBar (1 * q) • W) = P.redFst W := by
  show P.sp _ = P.sp _
  rw [ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul]

end ModularCurve.PlaceSpecialization

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff.ModularCurve.PlaceSpecialization in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeOne (frickeInvolutionBar (1 * q) • W) ↔ P.IsStrictTypeTwo W := by
  rw [IsStrictTypeOne, IsStrictTypeTwo, redFst_frickeInvolutionBar_smul', redSnd_frickeInvolutionBar_smul']
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩

end S_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_isStrictTypeOne_frickeInvolutionBar_smul_iff (solution)
