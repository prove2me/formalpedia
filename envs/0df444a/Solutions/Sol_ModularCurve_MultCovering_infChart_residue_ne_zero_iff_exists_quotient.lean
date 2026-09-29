-- Prove2me | solution 1 for ModularCurve.MultCovering.infChart_residue_ne_zero_iff_exists_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e7b87885-68f9-5c65-b55f-f0d510011c93

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

namespace P2MW.S_ModularCurve_MultCovering_infChart_residue_ne_zero_iff_exists_quotient
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization ModularCurve.MultCovering

theorem solution {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (f : ↥(modularFunctionFieldBar (1 * p))) :
    (∃ h : f ∈ (infChart Γ).integers, (infChart Γ).residue ⟨f, h⟩ ≠ 0) ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
  rw [← Γ.R.residueFst_ne_zero_iff_exists_quotient f]
  show (∃ h : f ∈ Γ.R.R₁.integers, Γ.R.residue₁ ⟨f, h⟩ ≠ 0) ↔ (∃ h : f ∈ Γ.R.R₁.integers, Γ.R.residue₁ ⟨f, h⟩ ≠ 0)
  exact Iff.rfl

end S_ModularCurve_MultCovering_infChart_residue_ne_zero_iff_exists_quotient
end P2MW
export P2MW.S_ModularCurve_MultCovering_infChart_residue_ne_zero_iff_exists_quotient (solution)
