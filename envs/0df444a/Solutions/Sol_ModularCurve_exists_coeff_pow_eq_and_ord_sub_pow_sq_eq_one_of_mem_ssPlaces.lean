-- Prove2me | solution 1 for ModularCurve.exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bfa78c10-8229-5369-b9ad-14ae32cc1af1

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Theorems.Thm_ModularCurve_exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"
set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace UniformiserOrder

private theorem ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) (n : ℕ) :
    v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast f n, v.ord_zpow]

private theorem adicValuation_lt_one_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) (hf : 0 < v.ord f) : v.adicValuation f < 1 := by
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, v.ord_zero] at hf; exact lt_irrefl 0 hf
  have hv0 : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero hf0
  have hlog : WithZero.log (v.adicValuation f) = -v.ord f := by
    simp [Place.ord]
  calc v.adicValuation f = WithZero.exp (WithZero.log (v.adicValuation f)) :=
        (WithZero.exp_log hv0).symm
    _ < 1 := by
        rw [hlog, ← WithZero.exp_zero]
        exact WithZero.exp_lt_exp.mpr (by omega)

private theorem ord_one_sub_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) (hf : 0 < v.ord f) :
    v.ord (1 - f) = 0 := by
  have h1 : v.adicValuation (1 - f) = 1 :=
    (v.adicValuation).map_one_sub_of_lt (adicValuation_lt_one_of_ord_pos v f hf)
  simp [Place.ord, h1]

private theorem one_sub_ne_zero_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (f : F) (hf : 0 < v.ord f) : (1 : F) - f ≠ 0 := by
  intro h0
  have hf1 : f = 1 := (sub_eq_zero.mp h0).symm
  rw [hf1] at hf
  simp [Place.ord, map_one, WithZero.log_one] at hf

end UniformiserOrder

theorem solution
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (hqN : ¬ q ∣ N) (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k) :
    ∃ gbar : ↥(modularFunctionFieldC k N),
      (∀ n : ℤ, ((gbar : LaurentSeries k).coeff n) ^ q = (gbar : LaurentSeries k).coeff n) ∧
      (∀ u : Place k (modularFunctionFieldC k N), IsAffineGeomPlace k N u → gbar ∈ u.toValuationSubring) ∧
      w.ord (gbar - gbar ^ (q ^ 2)) = 1 ∧ (arithFrobC q k N • w).ord (gbar - gbar ^ (q ^ 2)) = 1 := by
  obtain ⟨t, hfix, hreg, hw1, hwφ1⟩ :=
    ModularCurve.exists_coeff_pow_eq_and_ord_eq_one_of_mem_ssPlaces hqN w hw
  have hq2 : 1 < q ^ 2 := by
    have hq := (Fact.out : q.Prime).one_lt
    calc 1 < q := hq
      _ ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have key : ∀ v : Place k ↥(modularFunctionFieldC k N), v.ord t = 1 →
      v.ord (t - t ^ (q ^ 2)) = 1 := by
    intro v hv1
    have ht0 : t ≠ 0 := by
      intro h0; rw [h0, v.ord_zero] at hv1; exact absurd hv1 (by norm_num)
    have hfac : t - t ^ (q ^ 2) = t * (1 - t ^ (q ^ 2 - 1)) := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hq2.le]
    have hpos : 0 < v.ord (t ^ (q ^ 2 - 1)) := by
      rw [UniformiserOrder.ord_pow' v t (q ^ 2 - 1), hv1, mul_one]
      exact_mod_cast Nat.sub_pos_of_lt hq2
    have hu0 : v.ord (1 - t ^ (q ^ 2 - 1)) = 0 :=
      UniformiserOrder.ord_one_sub_eq_zero v _ hpos
    have hne : (1 : ↥(modularFunctionFieldC k N)) - t ^ (q ^ 2 - 1) ≠ 0 :=
      UniformiserOrder.one_sub_ne_zero_of_ord_pos v _ hpos
    rw [hfac, v.ord_mul ht0 hne, hv1, hu0, add_zero]
  exact ⟨t, hfix, hreg, key w hw1, key _ hwφ1⟩

end

end S_ModularCurve_exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_exists_coeff_pow_eq_and_ord_sub_pow_sq_eq_one_of_mem_ssPlaces (solution)
