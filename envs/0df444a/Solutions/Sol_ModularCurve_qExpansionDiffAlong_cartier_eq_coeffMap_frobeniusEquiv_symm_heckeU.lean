-- Prove2me | solution 1 for ModularCurve.qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/21f84037-b0a3-55e3-975e-ac1a25ec35ff

import Mathlib
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_LaurentSeries_HeckeU
import Theorems.Thm_ModularCurve_coeff_qExpansionDiffAlong_cartier_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open ModularCurve AlgebraicCurve

theorem solution
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectField K]
    (N : ℕ) [NeZero N] [IsCurveOver K (modularFunctionFieldC K N)]
    (C : Ω[↥(modularFunctionFieldC K N)⁄K] →+ Ω[↥(modularFunctionFieldC K N)⁄K])
    (hsemi : ∀ (f : modularFunctionFieldC K N) (ω : Ω[↥(modularFunctionFieldC K N)⁄K]),
      C (f ^ p • ω) = f • C ω)
    (hker : ∀ f : modularFunctionFieldC K N,
      C (KaehlerDifferential.D K (modularFunctionFieldC K N) f) = 0)
    (hlog : ∀ f : modularFunctionFieldC K N,
      C (f ^ (p - 1) • KaehlerDifferential.D K (modularFunctionFieldC K N) f)
        = KaehlerDifferential.D K (modularFunctionFieldC K N) f)
    (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) :
    qExpansionDiffAlong (modularFunctionFieldC K N).val (C ω)
      = coeffMap ((frobeniusEquiv K p).symm : K ≃+* K).toRingHom
          (LaurentSeries.heckeU K p (Fact.out : p.Prime).pos
            (qExpansionDiffAlong (modularFunctionFieldC K N).val ω)) := by
  ext n
  rw [coeffMap_coeff, LaurentSeries.coeff_heckeU]
  apply (frobeniusEquiv K p).injective
  change frobeniusEquiv K p _ =
    frobeniusEquiv K p ((frobeniusEquiv K p).symm
      ((qExpansionDiffAlong (modularFunctionFieldC K N).val ω).coeff ((p : ℤ) * n)))
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def,
    coeff_qExpansionDiffAlong_cartier_pow K p N C hsemi hker hlog ω n, mul_comm]

end S_ModularCurve_qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU
end P2MW
export P2MW.S_ModularCurve_qExpansionDiffAlong_cartier_eq_coeffMap_frobeniusEquiv_symm_heckeU (solution)
