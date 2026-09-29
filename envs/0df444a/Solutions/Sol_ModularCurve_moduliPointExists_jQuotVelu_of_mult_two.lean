-- Prove2me | solution 1 for ModularCurve.moduliPointExists_jQuotVelu_of_mult_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/920575f2-79fb-535c-a054-9d24bdee65fb

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero
import Theorems.Thm_ModularCurve_exists_place_of_modularPolynomial_eval_eq_zero
import Theorems.Thm_ModularCurve_modularPolynomial_rootMultiplicity_jQuotVelu_eq_one
import Theorems.Thm_ModularCurve_place_eq_of_modularPolynomial_rootMultiplicity_eq_one
import Theorems.Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_moduliPointExists_jQuotVelu_of_mult_two
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

open ModularCurve

private def fixedSubfield : Subfield (AlgebraicClosure ℚ) where
  carrier := {z | ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ z = z}
  mul_mem' := fun ha hb σ => by rw [map_mul, ha σ, hb σ]
  one_mem' := fun σ => map_one σ
  add_mem' := fun ha hb σ => by rw [map_add, ha σ, hb σ]
  zero_mem' := fun σ => map_zero σ
  neg_mem' := fun ha σ => by rw [map_neg, ha σ]
  inv_mem' := fun z ha σ => by rw [map_inv₀, ha σ]

private lemma mem_fixedSubfield_iff {z : AlgebraicClosure ℚ} :
    z ∈ fixedSubfield ↔ ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ z = z :=
  Iff.rfl

private lemma coordsOrZero_mem_fixedSubfield {W' : WeierstrassCurve ℚ}
    (P : (W'⁄(AlgebraicClosure ℚ)).Point)
    (hP : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • P = P) :
    P.coordsOrZero.1 ∈ fixedSubfield ∧ P.coordsOrZero.2 ∈ fixedSubfield := by
  rcases P with _ | ⟨x, y, hxy⟩
  · exact ⟨zero_mem _, zero_mem _⟩
  · have h : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ x = x ∧ σ y = y := by
      intro σ
      have h := hP σ
      rw [Point.algEquiv_smul_def, Point.map_some, Point.some.injEq] at h
      exact ⟨h.1, h.2⟩
    exact ⟨mem_fixedSubfield_iff.mpr fun σ => (h σ).1,
      mem_fixedSubfield_iff.mpr fun σ => (h σ).2⟩

private lemma arithGal_smul_jBar (p : ℕ) [NeZero p]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull p) σ • jBar p = jBar p :=
  Subtype.ext (coeffMap_coeffEmb σ _)

private lemma arithGal_smul_jpBar (p : ℕ) [NeZero p]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (modularFunctionFieldFull p) σ • jpBar p = jpBar p :=
  Subtype.ext (coeffMap_coeffEmb σ _)

private lemma arithGal_smul_sub_algebraMap (p : ℕ) [NeZero p]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (f : modularFunctionFieldBar p) (c : AlgebraicClosure ℚ)
    (hf : arithmeticGalois (modularFunctionFieldFull p) σ • f = f) (hc : σ c = c) :
    arithmeticGalois (modularFunctionFieldFull p) σ •
        (f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) c)
      = f - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) c := by
  have hbase : (SemilinearAut.baseAut (arithmeticGalois (modularFunctionFieldFull p) σ)) c = c :=
    hc
  rw [smul_sub, hf, SemilinearAut.smul_algebraMap, hbase]

private lemma ord_smul_pos (p : ℕ) [NeZero p]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    {f : modularFunctionFieldBar p}
    (hf : arithmeticGalois (modularFunctionFieldFull p) σ • f = f)
    (h : 0 < x.ord f) :
    0 < (arithmeticGalois (modularFunctionFieldFull p) σ • x).ord f := by
  have hord := SemilinearAut.ord_smul (arithmeticGalois (modularFunctionFieldFull p) σ) x f
  rw [hf] at hord
  rw [hord]
  exact h

private lemma j_eq_c₄_pow_div_Δ {V : WeierstrassCurve (AlgebraicClosure ℚ)} (hΔ' : V.Δ ≠ 0) :
    @WeierstrassCurve.j (AlgebraicClosure ℚ) _ V ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
      = V.c₄ ^ 3 / V.Δ := by
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  ring

private lemma jquot_mem_fixedSubfield (W' : WeierstrassCurve ℚ)
    (Q : (W'⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hΔb : (W'⁄(AlgebraicClosure ℚ)).Δ ≠ 0)
    (hQodd : addOrderOf Q = 2 * (addOrderOf Q / 2) + 1) :
    ((W'⁄(AlgebraicClosure ℚ)).veluQuotient
        ((W'⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (addOrderOf Q / 2))).c₄ ^ 3 /
      ((W'⁄(AlgebraicClosure ℚ)).veluQuotient
        ((W'⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (addOrderOf Q / 2))).Δ
    ∈ fixedSubfield := by
  haveI : (W'⁄(AlgebraicClosure ℚ)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔb⟩

  have hΔ' : ((W'⁄(AlgebraicClosure ℚ)).veluQuotient
      ((W'⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (addOrderOf Q / 2))).Δ ≠ 0 :=
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero
      (by norm_num : (2 : AlgebraicClosure ℚ) ≠ 0) (W'⁄(AlgebraicClosure ℚ))
      (addOrderOf Q / 2) Q hQodd

  have hT : ∀ P ∈ (W'⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (addOrderOf Q / 2),
      P.1 ∈ fixedSubfield ∧ P.2 ∈ fixedSubfield := by
    intro P hP
    rw [WeierstrassCurve.mem_oddOrderSummingSet] at hP
    obtain ⟨k, -, -, rfl⟩ := hP
    refine coordsOrZero_mem_fixedSubfield _ fun τ => ?_
    have h := Point.algEquiv_smul_zsmul τ (k : ℤ) Q
    rw [hQfix τ] at h
    simpa [natCast_zsmul] using h

  have hmemK := WeierstrassCurve.veluQuotient_j_mem_of_mem (W'⁄(AlgebraicClosure ℚ))
    fixedSubfield ((W'⁄(AlgebraicClosure ℚ)).oddOrderSummingSet Q (addOrderOf Q / 2))
    (mem_fixedSubfield_iff.mpr fun τ => τ.commutes _)
    (mem_fixedSubfield_iff.mpr fun τ => τ.commutes _)
    (mem_fixedSubfield_iff.mpr fun τ => τ.commutes _)
    (mem_fixedSubfield_iff.mpr fun τ => τ.commutes _)
    (mem_fixedSubfield_iff.mpr fun τ => τ.commutes _)
    hT hΔ'
  rwa [j_eq_c₄_pow_div_Δ hΔ'] at hmemK

theorem solution
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (h2Δ : (2 : ℤ) ∣ W.Δ) (h2c₄ : ¬ (2 : ℤ) ∣ W.c₄)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p) :
    ∃ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
      x.deg = 1 ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          arithmeticGalois (modularFunctionFieldFull p) σ • x = x) ∧
      0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (jInt W)) ∧
      0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p)
            (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
             let V := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
             (V.c₄ : AlgebraicClosure ℚ) ^ 3 / (V.Δ : AlgebraicClosure ℚ))) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩

  obtain ⟨data, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p

  have hroot := ModularCurve.modularPolynomial_eval_jInt_jQuotVelu_eq_zero p hp hp2 data W hΔ
    Nat.prime_two (by exact_mod_cast h2Δ) (by exact_mod_cast h2c₄) Q hQfix hQord

  have hmult := ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one p hp hp2 data W
    hΔ h2Δ h2c₄ Q hQfix hQord

  obtain ⟨x, hdeg, hx₁, hx₂⟩ :=
    ModularCurve.exists_place_of_modularPolynomial_eval_eq_zero p hp data (jInt W) _ hroot
  refine ⟨x, hdeg, ?_, hx₁, hx₂⟩

  intro σ
  have hj₁ : σ (jInt W) = jInt W := by
    simp only [jInt, map_div₀, map_pow, map_intCast]
  have hΔb : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Δ ≠ 0 := by
    have h : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Δ
        = ((W.Δ : ℤ) : AlgebraicClosure ℚ) := by
      simp [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    rw [h]
    exact_mod_cast hΔ
  have hQodd : addOrderOf Q = 2 * (addOrderOf Q / 2) + 1 := by
    have h1 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    rw [hQord]
    omega
  have hj₂ := mem_fixedSubfield_iff.mp
    (jquot_mem_fixedSubfield (W.map (Int.castRingHom ℚ)) Q hQfix hΔb hQodd) σ
  have hfix₁ := arithGal_smul_sub_algebraMap p σ (jBar p) (jInt W)
    (arithGal_smul_jBar p σ) hj₁
  have hfix₂ := arithGal_smul_sub_algebraMap p σ (jpBar p) _
    (arithGal_smul_jpBar p σ) hj₂
  exact (ModularCurve.place_eq_of_modularPolynomial_rootMultiplicity_eq_one p hp data _ _ hroot
    hmult x (arithmeticGalois (modularFunctionFieldFull p) σ • x) hx₁ hx₂
    (ord_smul_pos p σ x hfix₁ hx₁) (ord_smul_pos p σ x hfix₂ hx₂)).symm

end S_ModularCurve_moduliPointExists_jQuotVelu_of_mult_two
end P2MW
export P2MW.S_ModularCurve_moduliPointExists_jQuotVelu_of_mult_two (solution)
