-- Prove2me | solution 1 for ModularCurve.geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ad55de75-cae1-532c-9345-cbe6ff89b970

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] :
    GeometricallyIntegral
      (pullback.snd (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)))) := by
  rw [geometricallyIntegral_iff, geometrically_iff_of_commRing (R := ℚ)]
  intro K _ _ Y fst snd h

  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : Algebra ↥(GaloisRep.ratLocalizedAt p) K := ((algebraMap ℚ K).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ)).toAlgebra

  have big := h.paste_horiz (IsPullback.of_hasPullback
    (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ))))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at big
  have e : (algebraMap ℚ K).comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ℚ) = algebraMap ↥(GaloisRep.ratLocalizedAt p) K := rfl
  rw [e] at big
  haveI : IsIntegral ↑(pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) K)))) :=
    ModularCurve.isIntegral_pullback_toBase_twoChartIntegralModel_qExpFunctionFieldC_of_charZero Γ p j K
  haveI : Nonempty ↥Y := (inferInstance : Nonempty ↥(pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) K))))).map big.isoPullback.inv.base
  exact isIntegral_of_isOpenImmersion big.isoPullback.hom

end S_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat
end P2MW
export P2MW.S_ModularCurve_geometricallyIntegral_pullback_snd_toBase_twoChartIntegralModel_qExpFunctionFieldC_rat (solution)
