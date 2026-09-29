-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_residue_coeffMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/286c9182-8b83-5f83-a780-d065a1f39b87

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_jFun_jqFun
import Theorems.Thm_ModularCurve_MultCovering_jpF_eq_jqFun
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_residue_of_forall_coeff_mem
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_chartFst_mem_integers_residue_ne_zero_of_qCoeff
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_exists_quotient
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residueFst_ne_zero_iff_exists_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_infChart_residue_coeffMap
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem solution {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * p)) :
    ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar (1 * p))) ∈ (infChart Γ).integers,
      (((infChart Γ).residue ⟨_, hint⟩ : ↥(modularFunctionFieldC (IsLocalRing.ResidueField ↥A) 1)) :
          LaurentSeries (IsLocalRing.ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y :=
  ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_coeffMap Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply y hy

end S_ModularCurve_MultCovering_infChart_residue_coeffMap
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_residue_coeffMap (solution)
