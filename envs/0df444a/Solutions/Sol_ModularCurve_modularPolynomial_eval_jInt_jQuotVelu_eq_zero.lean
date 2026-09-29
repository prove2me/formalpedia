-- Prove2me | solution 1 for ModularCurve.modularPolynomial_eval_jInt_jQuotVelu_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f50eb2d0-7055-512a-b596-bf098b0f6772

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
import Theorems.Thm_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_ne_zero
import Theorems.Thm_WeierstrassCurve_map_veluQuotient_image
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X"
p2m_attr_erase "simp" "ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty"

p2m_attr_erase "instance" "HahnSeries.powerSeriesAlgebra"

p2m_open "WeierstrassCurve WeierstrassCurve.Affine ModularCurve P2MW.S_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero.ModularCurve Polynomial"

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "𝕂" => HahnSeries ℚ (AlgebraicClosure ℚ)

scoped instance ist_Q_Q_Qbar : IsScalarTower ℚ ℚ (AlgebraicClosure ℚ) :=
  ⟨fun r s x => by rw [smul_eq_mul, mul_smul]⟩

scoped instance ist_Q_Q_K : IsScalarTower ℚ ℚ (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
  ⟨fun r s x => by rw [smul_eq_mul, mul_smul]⟩

scoped instance ist_Q_Qbar_K :
    IsScalarTower ℚ (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
  ⟨fun r s x => HahnSeries.ext (funext fun g => by
    rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul, smul_assoc])⟩

namespace ModularCurve
p2m_export "ModularCurve" "jInt ModularPolynomialData ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq"
namespace N4aBridge
p2m_open "ModularCurve"

def iotaA : (AlgebraicClosure ℚ) →ₐ[ℚ] (HahnSeries ℚ (AlgebraicClosure ℚ)) where
  toRingHom := HahnSeries.C
  commutes' r := (HahnSeries.algebraMap_apply (R := ℚ) (r := r)).symm

lemma iotaA_apply (x : ℚ̄) : iotaA x = HahnSeries.C x := rfl

lemma iotaA_injective : Function.Injective (iotaA : ℚ̄ → 𝕂) :=
  fun _ _ h => HahnSeries.C_injective h

lemma iotaA_eq_algebraMap (x : ℚ̄) : (iotaA x : 𝕂) = algebraMap ℚ̄ 𝕂 x := by
  rw [iotaA_apply]
  exact (HahnSeries.algebraMap_apply (R := ℚ̄) (r := x)).symm.trans
    (by simp only [Algebra.algebraMap_self, RingHom.id_apply])

lemma iotaA_coe_eq_algebraMap :
    ((iotaA : ℚ̄ →ₐ[ℚ] 𝕂) : ℚ̄ → 𝕂) = algebraMap ℚ̄ 𝕂 :=
  funext iotaA_eq_algebraMap

lemma Wbc_Δ (W : WeierstrassCurve ℤ) (A : Type*) [CommRing A] [Algebra ℚ A] :
    ((W.map (Int.castRingHom ℚ))⁄A).Δ = ((W.Δ : ℤ) : A) := by
  have h : ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ A)).Δ
      = (algebraMap ℚ A) ((W.Δ : ℤ) : ℚ) := by rw [map_Δ, map_Δ]; rfl
  exact h.trans (map_intCast (algebraMap ℚ A) W.Δ)

lemma Wbc_c₄ (W : WeierstrassCurve ℤ) (A : Type*) [CommRing A] [Algebra ℚ A] :
    ((W.map (Int.castRingHom ℚ))⁄A).c₄ = ((W.c₄ : ℤ) : A) := by
  have h : ((W.map (Int.castRingHom ℚ)).map (algebraMap ℚ A)).c₄
      = (algebraMap ℚ A) ((W.c₄ : ℤ) : ℚ) := by rw [map_c₄, map_c₄]; rfl
  exact h.trans (map_intCast (algebraMap ℚ A) W.c₄)

lemma Wbc_isElliptic (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (A : Type*) [Field A]
    [Algebra ℚ A] : ((W.map (Int.castRingHom ℚ))⁄A).IsElliptic := by
  haveI : CharZero A := (RingHom.charZero_iff (algebraMap ℚ A).injective).mp inferInstance
  rw [isElliptic_iff, isUnit_iff_ne_zero, Wbc_Δ]
  exact Int.cast_ne_zero.mpr hΔ

lemma j_eq_div {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j = W.c₄ ^ 3 / W.Δ := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', eq_div_iff W.Δ'.ne_zero,
    mul_right_comm, Units.inv_mul, one_mul]

lemma Wbc_j_eq_C (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) :
    haveI := Wbc_isElliptic W hΔ 𝕂
    haveI := Wbc_isElliptic W hΔ ℚ̄
    ((W.map (Int.castRingHom ℚ))⁄𝕂).j
      = HahnSeries.C (((W.map (Int.castRingHom ℚ))⁄ℚ̄).j) := by
  haveI := Wbc_isElliptic W hΔ 𝕂
  haveI := Wbc_isElliptic W hΔ ℚ̄
  rw [j_eq_div, j_eq_div, Wbc_c₄, Wbc_c₄, Wbc_Δ, Wbc_Δ, map_div₀, map_pow]
  congr 1 <;> exact (map_intCast (HahnSeries.C : ℚ̄ →+* 𝕂) _).symm

lemma coordsOrZero_map {R : Type*} [CommRing R]
    {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
    [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (W' : WeierstrassCurve R) (f : F →ₐ[S] K) (P : (W'⁄F).Point) :
    ((Point.map f) P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0 : (W'⁄K).Point).coordsOrZero) = Prod.map f f (0, 0)
    simp [Point.coordsOrZero]
  · rfl

lemma oddOrderSummingSet_map {R : Type*} [CommRing R]
    {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
    [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    (W' : WeierstrassCurve R) (f : F →ₐ[S] K) (Q : (W'⁄F).Point) (n : ℕ) :
    (W'⁄K).oddOrderSummingSet ((Point.map f) Q) n
      = ((W'⁄F).oddOrderSummingSet Q n).image (Prod.map f f) := by
  unfold WeierstrassCurve.oddOrderSummingSet
  rw [Finset.image_image]
  congr 1
  funext k
  simp only [Function.comp_apply]
  have hmap : (k • Point.map (W' := W') f Q) = Point.map (W' := W') f (k • Q) :=
    (map_nsmul (Point.map (W' := W') f : (W'⁄F).Point →+ (W'⁄K).Point) k Q).symm
  rw [hmap]
  exact coordsOrZero_map W' f (k • Q)

lemma baseChange_eq_map_of_tower {R : Type*} [CommRing R]
    {F K : Type*} [CommRing F] [CommRing K] [Algebra R F] [Algebra R K] [Algebra F K]
    [IsScalarTower R F K] (W' : WeierstrassCurve R) :
    W'⁄K = (W'⁄F).map (algebraMap F K) := by
  show W'.map (algebraMap R K) = (W'.map (algebraMap R F)).map (algebraMap F K)
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq]

lemma MPD_cast {a b : ℕ} [NeZero a] [NeZero b] (h : a = b)
    (d : ModularCurve.ModularPolynomialData a) :
    ∃ d' : ModularCurve.ModularPolynomialData b, d'.Φ = d.Φ := by
  subst h; exact ⟨d, rfl⟩

end ModularCurve.N4aBridge

open ModularCurve.N4aBridge

theorem solution
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : ModularCurve.ModularPolynomialData p)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jInt W)).toRingHom
      (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
       let V := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
       (V.c₄ : AlgebraicClosure ℚ) ^ 3 / (V.Δ : AlgebraicClosure ℚ)) = 0 := by
  classical

  letI : IsScalarTower ℚ ℚ ℚ̄ := ist_Q_Q_Qbar
  letI : IsScalarTower ℚ ℚ 𝕂 := ist_Q_Q_K
  letI : IsScalarTower ℚ ℚ̄ 𝕂 := ist_Q_Qbar_K
  let Wq : WeierstrassCurve ℚ := W.map (Int.castRingHom ℚ)
  have hpn : p = 2 * (p / 2) + 1 := by
    have h1 : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2); omega
  haveI hNZ : NeZero (2 * (p / 2) + 1) := ⟨Nat.succ_ne_zero _⟩
  have hQord' : addOrderOf Q = 2 * (p / 2) + 1 := hQord.trans hpn
  haveI hEb : (Wq⁄ℚ̄).IsElliptic := Wbc_isElliptic W hΔ ℚ̄
  let V := (Wq⁄ℚ̄).veluQuotient ((Wq⁄ℚ̄).oddOrderSummingSet Q (p / 2))
  have hVΔ : V.Δ ≠ 0 :=
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero
      (by norm_num : (2 : ℚ̄) ≠ 0) (Wq⁄ℚ̄) (p / 2) Q hQord'
  haveI hEV : V.IsElliptic := ⟨isUnit_iff_ne_zero.mpr hVΔ⟩
  have hjInt : ModularCurve.jInt W = (Wq⁄ℚ̄).j := by
    rw [j_eq_div, Wbc_c₄, Wbc_Δ, ModularCurve.jInt]
  have hjQuot : (let Wb := (W.map (Int.castRingHom ℚ))⁄ℚ̄
       let Vb := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
       (Vb.c₄ : ℚ̄) ^ 3 / (Vb.Δ : ℚ̄)) = V.j := by
    simp only [hQord]; exact (j_eq_div V).symm
  rw [hjInt, hjQuot]

  refine iotaA_injective ?_
  rw [iotaA_apply, iotaA_apply, map_zero]
  rw [Polynomial.hom_eval₂ data.Φ (Polynomial.aeval (R := ℤ) ((Wq⁄ℚ̄).j)).toRingHom
    (HahnSeries.C : ℚ̄ →+* 𝕂) V.j]

  haveI hE𝕂 : (Wq⁄𝕂).IsElliptic := Wbc_isElliptic W hΔ 𝕂
  let Q𝕂 : (Wq⁄𝕂).Point := Point.map (W' := Wq) iotaA Q
  have hQ𝕂ord : addOrderOf Q𝕂 = 2 * (p / 2) + 1 := by
    have hinj : Function.Injective (Point.map (W' := Wq) iotaA) :=
      Point.map_injective (W' := Wq) iotaA
    exact (addOrderOf_injective (Point.map (W' := Wq) iotaA) hinj Q).trans hQord'

  have hPmap : (Prod.map (iotaA : ℚ̄ → 𝕂) (iotaA : ℚ̄ → 𝕂))
      = Prod.map (algebraMap ℚ̄ 𝕂) (algebraMap ℚ̄ 𝕂) := by
    rw [iotaA_coe_eq_algebraMap]
  have hS𝕂 : (Wq⁄𝕂).oddOrderSummingSet Q𝕂 (p/2)
      = ((Wq⁄ℚ̄).oddOrderSummingSet Q (p/2)).image
          (Prod.map (algebraMap ℚ̄ 𝕂) (algebraMap ℚ̄ 𝕂)) := by
    rw [← hPmap]; exact oddOrderSummingSet_map Wq iotaA Q (p/2)
  have hcard : (((Wq⁄ℚ̄).oddOrderSummingSet Q (p/2)).image
      (Prod.map (algebraMap ℚ̄ 𝕂) (algebraMap ℚ̄ 𝕂))).card
      = ((Wq⁄ℚ̄).oddOrderSummingSet Q (p/2)).card :=
    Finset.card_image_of_injective _
      (Prod.map_injective.mpr ⟨(algebraMap ℚ̄ 𝕂).injective, (algebraMap ℚ̄ 𝕂).injective⟩)
  have hbc : (Wq⁄𝕂) = (Wq⁄ℚ̄).map (algebraMap ℚ̄ 𝕂) := baseChange_eq_map_of_tower Wq
  have hV𝕂 : (Wq⁄𝕂).veluQuotient ((Wq⁄𝕂).oddOrderSummingSet Q𝕂 (p/2))
      = V.map (algebraMap ℚ̄ 𝕂) := by
    rw [hS𝕂, hbc]
    exact WeierstrassCurve.map_veluQuotient_image (Wq⁄ℚ̄) (algebraMap ℚ̄ 𝕂) _ hcard
  have hV𝕂Δ : ((Wq⁄𝕂).veluQuotient ((Wq⁄𝕂).oddOrderSummingSet Q𝕂 (p/2))).Δ ≠ 0 := by
    rw [hV𝕂, map_Δ]
    exact fun h => hVΔ ((algebraMap ℚ̄ 𝕂).injective (h.trans (map_zero _).symm))

  obtain ⟨data', hdata'Φ⟩ := MPD_cast (a := p) (b := 2 * (p / 2) + 1) hpn data

  have key := ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
      (Wq⁄𝕂) (p/2) Q𝕂 hQ𝕂ord hV𝕂Δ data'
  rw [hdata'Φ] at key
  haveI : ((Wq⁄𝕂).veluQuotient ((Wq⁄𝕂).oddOrderSummingSet Q𝕂 (p/2))).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hV𝕂Δ⟩

  have hjW𝕂 : (Wq⁄𝕂).j = HahnSeries.C ((Wq⁄ℚ̄).j) := Wbc_j_eq_C W hΔ
  have hjV𝕂 : ((Wq⁄𝕂).veluQuotient ((Wq⁄𝕂).oddOrderSummingSet Q𝕂 (p/2))).j
      = HahnSeries.C V.j := by
    rw [j_eq_div, hV𝕂, map_c₄, map_Δ, j_eq_div V, map_div₀, map_pow]
    simp only [← iotaA_eq_algebraMap, iotaA_apply]
  rw [Polynomial.IsRoot, Polynomial.eval_map, hjW𝕂, hjV𝕂] at key

  refine Eq.trans ?_ key
  congr 1
  refine RingHom.ext fun q => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Polynomial.aeval_def, Polynomial.coe_eval₂RingHom]
  rw [Polynomial.hom_eval₂]
  congr 1

end
end S_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero
end P2MW
export P2MW.S_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero (solution)
