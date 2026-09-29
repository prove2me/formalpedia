-- Prove2me | solution 1 for ModularCurve.CharPModel.ord_jBar_dvd_of_ord_jBar_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/95f976f0-fc68-5fac-9def-1b845994722d

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
import Theorems.Thm_ModularCurve_exists_slot_of_isCusp
import Theorems.Thm_ModularCurve_slot_ord_of_algHom_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_ord_jBar_dvd_of_ord_jBar_neg
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply"

set_option autoImplicit false

open ModularCurve ModularCurve.CharPModel

private theorem ord_jq_dvd_of_neg (N : ℕ) [NeZero N]
    (b : AlgebraicCurve.Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)))
    (hb : b.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) < 0) :
    b.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∣ (N : ℤ) := by
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) N
  set ζ : (AlgebraicClosure ℚ)ˣ := (hz.isUnit (NeZero.ne N)).unit with hζdef
  have hζ : IsPrimitiveRoot (ζ : AlgebraicClosure ℚ) N := by
    rw [hζdef, IsUnit.unit_spec]
    exact hz
  have hc := (ModularCurve.isCusp_iff_ord_neg _ b).mpr hb
  obtain ⟨a, c, ha, -, -, hne, ι, h1, h2, hw⟩ := ModularCurve.exists_slot_of_isCusp (AlgebraicClosure ℚ) N ζ hζ b hc
  haveI := hne
  have hγ : (0 : ℤ) < ((a * Nat.gcd a (N / a) : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (NeZero.pos a) (Nat.gcd_pos_of_pos_left (N / a) (NeZero.pos a))
  obtain ⟨-, hj, -⟩ :=
    ModularCurve.slot_ord_of_algHom_laurentBaseChange (AlgebraicClosure ℚ) N ζ a c ha ι h1 h2 b _ hγ hw
  rw [hj, neg_dvd]
  have hdvd : N / a / Nat.gcd a (N / a) ∣ N :=
    ⟨Nat.gcd a (N / a) * a, by
      rw [← mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_right a (N / a)), Nat.div_mul_cancel ha]⟩
  exact_mod_cast hdvd

theorem solution (N : ℕ) [NeZero N]
    (b : AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : b.ord (jBar N) < 0) : b.ord (jBar N) ∣ (N : ℤ) := by
  have hj : jBar N = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ := rfl
  rw [hj] at hb ⊢
  exact ord_jq_dvd_of_neg N b hb

end S_ModularCurve_CharPModel_ord_jBar_dvd_of_ord_jBar_neg
end P2MW
export P2MW.S_ModularCurve_CharPModel_ord_jBar_dvd_of_ord_jBar_neg (solution)
