-- Prove2me | solution 1 for ModularCurve.inertiaDegAlong_heckeAlphaC_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/404fcddf-609e-5477-b354-5f9c2c78f9d3

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Theorems.Thm_ModularCurve_place_deg_eq_one_charLDegeneracyRoof
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_open "ModularCurve AlgebraicCurve P2MW.S_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one.AlgebraicCurve"
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section Engine
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place algebraAlong isScalarTower_along isIntegral_along" namespace Place p2m_export "AlgebraicCurve.Place" "deg restrict inertiaDeg deg_restrict_mul_inertiaDeg inertiaDegAlong" end AlgebraicCurve.Place
namespace AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.inertiaDegAlong_eq_one_of_deg_target_eq_one
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (hw : w.deg = 1) :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h : (w.restrict F).deg * w.inertiaDeg F = 1 := hw ▸ w.deg_restrict_mul_inertiaDeg
  exact Nat.eq_one_of_mul_eq_one_left h

end AlgebraicCurve.Place
p2m_export "" "AlgebraicCurve.Place.inertiaDegAlong_eq_one_of_deg_target_eq_one"
end Engine

theorem solution
    (k : Type*) [Field k] [IsAlgClosed k] (N q : ℕ) [NeZero N] [NeZero q]
    (hαc : HeckeAlphaCIntegral k N q)
    (W : AlgebraicCurve.Place k (charLDegeneracyRoof k N q)) :
    W.inertiaDegAlong (heckeAlphaC k N q) hαc = 1 :=
  W.inertiaDegAlong_eq_one_of_deg_target_eq_one (heckeAlphaC k N q) hαc
    (ModularCurve.place_deg_eq_one_charLDegeneracyRoof k N q W)

end S_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one
end P2MW
export P2MW.S_ModularCurve_inertiaDegAlong_heckeAlphaC_eq_one (solution)
