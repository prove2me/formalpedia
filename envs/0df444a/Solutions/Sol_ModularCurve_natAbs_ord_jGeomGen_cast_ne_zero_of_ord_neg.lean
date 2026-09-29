-- Prove2me | solution 1 for ModularCurve.natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/52140f2a-286b-550c-9f84-7a834f4d1d03

import Mathlib
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.cuspCount_one ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply"
set_option autoImplicit false
open AlgebraicCurve ModularCurve

namespace HtameE4

theorem exists_place_of_eq {K L : Type*} [Field K] [Field L] [Algebra K L] {E₁ E₂ : IntermediateField K L}
    (h : E₁ = E₂) (y : AlgebraicCurve.Place K ↥E₁) :
    ∃ y' : AlgebraicCurve.Place K ↥E₂, ∀ (x : ↥E₁) (hx : (x : L) ∈ E₂), y'.ord ⟨x, hx⟩ = y.ord x := by
  subst h
  exact ⟨y, fun x hx => rfl⟩

end HtameE4

open HtameE4 in
theorem solution
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N)) (hw : w.ord (jGeomGen K N) < 0) :
    (((w.ord (jGeomGen K N)).natAbs : ℕ) : K) ≠ 0 := by
  have hpN : ¬ p ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K p N).mpr h)
  have hC := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K p N hpN
  obtain ⟨w', hw'⟩ := exists_place_of_eq hC w
  have e' : w.ord (jGeomGen K N) = w'.ord ⟨jqModC K, jqModC_mem_full K N⟩ :=
    (hw' (jGeomGen K N) (jqModC_mem_full K N)).symm
  have hx : (⟨qExpand K 1 (jqModC K), jqModCd_mem_full K N (one_dvd _)⟩ : ↥(modularFunctionFieldFullC K N))
      = ⟨jqModC K, jqModC_mem_full K N⟩ := Subtype.ext (qExpand_one_apply _)
  have hneg : w'.ord ⟨jqModC K, jqModC_mem_full K N⟩ < 0 := by
    have h := hw
    rwa [e'] at h
  have key := ModularCurve.cast_natAbs_ord_qExpand_jqModC_ne_zero_of_ord_neg p K N hN w' hneg 1 (one_dvd _)
  rw [hx] at key
  rwa [e']

end S_ModularCurve_natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg
end P2MW
export P2MW.S_ModularCurve_natAbs_ord_jGeomGen_cast_ne_zero_of_ord_neg (solution)
