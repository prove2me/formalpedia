-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_prolongationDatum_mem_integers_iff_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/52d9b572-9f54-550d-be2e-53ca525e9fbe

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_prolongationDatum_mem_integers_iff_gauss
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) :
    ∃ Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ,

      ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers ↔
        ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
          ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by
  have hGM := ModularCurve.JHPlaceSpecialization.exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap p M H hpM hpM2 hHp A hA
  obtain ⟨R₁, hg, hres⟩ := hGM
  have hRC := AlgebraicCurve.RegularProlongation.exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv A R₁ θ
  obtain ⟨R₂, hmem, hres₂⟩ := hRC
  exact ⟨⟨R₁, R₂, hres, hmem, hres₂⟩, hg⟩

end S_ModularCurve_JHPlaceSpecialization_exists_prolongationDatum_mem_integers_iff_gauss
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_prolongationDatum_mem_integers_iff_gauss (solution)
