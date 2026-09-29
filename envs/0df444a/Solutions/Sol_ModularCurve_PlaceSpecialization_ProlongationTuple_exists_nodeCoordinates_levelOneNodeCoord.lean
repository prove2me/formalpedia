-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.exists_nodeCoordinates_levelOneNodeCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/f134e541-d321-59e3-ba60-9f2bd211c7fa

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_PlaceWidth
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint
import Theorems.Thm_ModularCurve_NodeLocalized_pointEval_eq_zero_of_modularEval_eq_zero
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_existsUnique_kroneckerRemainder
import Theorems.Thm_ModularCurve_exists_isAtkinLehnerAutFull_of_prime_of_not_dvd
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_qExpand_jqNModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

set_option autoImplicit false

namespace FltWs29
namespace P1N

section TV
open Polynomial

noncomputable def twoVarEval (S : Type*) [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) : S :=
  ((P.map (mapRingHom (Int.castRingHom S))).eval (C v)).eval u

theorem twoVarEval_eq_evalEval (S : Type*) [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    twoVarEval S u v P = (P.map (mapRingHom (Int.castRingHom S))).evalEval u v := rfl

theorem eval₂_aeval_eq_twoVarEval {S : Type*} [CommRing S] (u v : S) (P : Polynomial (Polynomial ℤ)) :
    P.eval₂ (aeval u).toRingHom v = twoVarEval S u v P := by
  induction P using Polynomial.induction_on' with
  | add p r hp hr =>
    simp only [eval₂_add, twoVarEval, Polynomial.map_add, eval_add] at hp hr ⊢
    rw [hp, hr]
  | monomial n p =>
    simp only [twoVarEval, eval₂_monomial, Polynomial.map_monomial, eval_monomial, eval_mul,
      eval_pow, eval_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def, eval_map,
      algebraMap_int_eq, coe_mapRingHom]

theorem map_twoVarEval {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S') (u v : S)
    (P : Polynomial (Polynomial ℤ)) : f (twoVarEval S u v P) = twoVarEval S' (f u) (f v) P := by
  rw [← eval₂_aeval_eq_twoVarEval, ← eval₂_aeval_eq_twoVarEval, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]

variable {T : Type*} [CommRing T]

noncomputable def kroneckerForm (q : ℕ) (R : Polynomial (Polynomial T)) : Polynomial (Polynomial T) :=
  (C X ^ q - X) * (C X - X ^ q) + C (C (q : T)) * R

theorem evalEval_kroneckerForm (q : ℕ) (R : Polynomial (Polynomial T)) (a b : T) :
    (kroneckerForm q R).evalEval a b = (a ^ q - b) * (a - b ^ q) + q * R.evalEval a b := by
  simp only [kroneckerForm, Polynomial.evalEval, eval_add, eval_mul, eval_sub, eval_pow, eval_C,
    eval_X, eval_natCast]

theorem map_eq_kroneckerForm {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) (S : Type*) [CommRing S] :
    Φ.map (mapRingHom (Int.castRingHom S)) = kroneckerForm q (R.map (mapRingHom (Int.castRingHom S))) := by
  rw [hR]
  simp only [kroneckerForm, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_pow, Polynomial.map_natCast, map_C, map_X, coe_mapRingHom, eq_intCast, Int.cast_natCast,
    map_natCast]

theorem twoVarEval_of_kronecker {q : ℕ} {Φ R : Polynomial (Polynomial ℤ)}
    (hR : Φ = (C X ^ q - X) * (C X - X ^ q) + C (C (q : ℤ)) * R) (S : Type*) [CommRing S] (u v : S) :
    twoVarEval S u v Φ = (u ^ q - v) * (u - v ^ q) + q * twoVarEval S u v R := by
  rw [twoVarEval_eq_evalEval, map_eq_kroneckerForm hR, evalEval_kroneckerForm, ← twoVarEval_eq_evalEval]

end TV

section OC
open Finset

variable {B : Type*} [CommRing B]

theorem le_add_of_newton {e a i s : ℕ} (hae : a ≤ e) (hie : i ≤ e) (h : (e - i) * a ≤ e * s) :
    a ≤ i + s := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · omega
  · have h1 : e * a ≤ e * (i + s) := by
      have h2 : (e - i) * a + i * a = e * a := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hie]
      have h3 : i * a ≤ i * e := Nat.mul_le_mul_left i hae
      nlinarith
    exact Nat.le_of_mul_le_mul_left h1 he

theorem sum_pow_mul_eq_pow_mul_T (G H ϖ : B) (U : Bˣ) (hGH : G * H = ϖ * U)
    (e a : ℕ) (hae : a ≤ e) (s : Fin (e + 1) → ℕ) (w : Fin (e + 1) → B)
    (hNP : ∀ i : Fin (e + 1), (e - i) * a ≤ e * s i) :
    ∑ i : Fin (e + 1), ϖ ^ s i * w i * G ^ (i : ℕ)
      = G ^ a * ∑ i : Fin (e + 1), w i * G ^ ((i : ℕ) + s i - a) * H ^ s i * ((U⁻¹ : Bˣ) : B) ^ s i := by
  have hϖ : ϖ = G * H * ((U⁻¹ : Bˣ) : B) := by
    rw [hGH, mul_assoc, Units.mul_inv, mul_one]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : a ≤ (i : ℕ) + s i := le_add_of_newton hae (Nat.lt_succ_iff.mp i.2) (hNP i)
  rw [hϖ, mul_pow, mul_pow]
  have : G ^ (i : ℕ) * G ^ s i = G ^ a * G ^ ((i : ℕ) + s i - a) := by
    rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hi]
  calc G ^ s i * H ^ s i * ((U⁻¹ : Bˣ) : B) ^ s i * w i * G ^ (i : ℕ)
      = w i * (G ^ (i : ℕ) * G ^ s i) * H ^ s i * ((U⁻¹ : Bˣ) : B) ^ s i := by ring
    _ = G ^ a * (w i * G ^ ((i : ℕ) + s i - a) * H ^ s i * ((U⁻¹ : Bˣ) : B) ^ s i) := by rw [this]; ring

end OC

section L
open ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple Polynomial

theorem jqNModC_congr (L : Type*) [CommRing L] {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    jqNModC L n = jqNModC L m := by
  subst h
  rfl

theorem modularEval_X0 (M : ℕ) [NeZero M] {L : Type*} [CommRing L] (S : Subring L) :
    NodeLocalized.modularEval M S (MvPolynomial.X 0) = jqModC L := by
  simp [NodeLocalized.modularEval]

theorem modularEval_X1 (M : ℕ) [NeZero M] {L : Type*} [CommRing L] (S : Subring L) :
    NodeLocalized.modularEval M S (MvPolynomial.X 1) = jqNModC L M := by
  simp [NodeLocalized.modularEval, Matrix.cons_val_one, Matrix.head_cons]

theorem pointEval_X0 {L : Type*} [CommRing L] (S : Subring L) {κ : Type*} [Field κ] (red : S →+* κ) (a b : κ) :
    NodeLocalized.pointEval S red a b (MvPolynomial.X 0) = a := by
  simp [NodeLocalized.pointEval]

theorem pointEval_X1 {L : Type*} [CommRing L] (S : Subring L) {κ : Type*} [Field κ] (red : S →+* κ) (a b : κ) :
    NodeLocalized.pointEval S red a b (MvPolynomial.X 1) = b := by
  simp [NodeLocalized.pointEval, Matrix.cons_val_one, Matrix.head_cons]

theorem modularEval_twoVarEval (M : ℕ) [NeZero M] {L : Type*} [CommRing L] (S : Subring L)
    (P : Polynomial (Polynomial ℤ)) :
    NodeLocalized.modularEval M S
        (twoVarEval (MvPolynomial (Fin 2) S) (MvPolynomial.X 0) (MvPolynomial.X 1) P)
      = twoVarEval (LaurentSeries L) (jqModC L) (jqNModC L M) P := by
  rw [map_twoVarEval, modularEval_X0, modularEval_X1]

theorem pointEval_twoVarEval {L : Type*} [CommRing L] (S : Subring L) {κ : Type*} [Field κ] (red : S →+* κ)
    (a b : κ) (P : Polynomial (Polynomial ℤ)) :
    NodeLocalized.pointEval S red a b
        (twoVarEval (MvPolynomial (Fin 2) S) (MvPolynomial.X 0) (MvPolynomial.X 1) P)
      = twoVarEval κ a b P := by
  rw [map_twoVarEval, pointEval_X0, pointEval_X1]

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

theorem coe_jFun : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    = jqModC (AlgebraicClosure ℚ) := by
  show coeffEmb (AlgebraicClosure ℚ) jq = _
  exact coeffEmb_jq _

theorem coe_jQFun : ((jQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
    = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
  rw [jqNModC_congr (AlgebraicClosure ℚ) (one_mul q)]
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
  rw [coeffEmb_qExpand, coeffEmb_jq]
  rfl

theorem coe_twoVarEval (M : ℕ) [NeZero M] (u v : ↥(modularFunctionFieldBar M)) (P : Polynomial (Polynomial ℤ)) :
    ((twoVarEval (↥(modularFunctionFieldBar M)) u v P : ↥(modularFunctionFieldBar M)) : LaurentSeries (AlgebraicClosure ℚ))
      = twoVarEval (LaurentSeries (AlgebraicClosure ℚ)) (u : LaurentSeries (AlgebraicClosure ℚ))
          (v : LaurentSeries (AlgebraicClosure ℚ)) P :=
  map_twoVarEval (modularFunctionFieldBar M).val.toRingHom u v P

theorem eval₂_eq_twoVarEval {S : Type*} [CommRing S] (f : Polynomial ℤ →+* S) (v : S) (P : Polynomial (Polynomial ℤ)) :
    P.eval₂ f v = twoVarEval S (f X) v P := by
  have hf : f = (aeval (f X)).toRingHom :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X])
  calc P.eval₂ f v = P.eval₂ (aeval (f X)).toRingHom v := by rw [← hf]
    _ = twoVarEval S (f X) v P := eval₂_aeval_eq_twoVarEval _ _ _

theorem twoVarEval_jFun_jQFun (data : ModularPolynomialData q) :
    twoVarEval (↥(modularFunctionFieldBar (N * q))) (jFun N q) (jQFun N q) data.Φ = 0 := by
  have h : twoVarEval (LaurentSeries ℚ) jq (qExpand ℚ q jq) data.Φ = 0 := by
    have h0 := data.eval_eq_zero
    rw [eval₂_eq_twoVarEval, evalAtJ_X] at h0
    exact h0
  apply Subtype.val_injective
  rw [coe_twoVarEval, ZeroMemClass.coe_zero]
  have e1 : ((jFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) jq := rfl
  have e2 : ((jQFun N q : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) := rfl
  rw [e1, e2, ← map_twoVarEval, h, map_zero]

end L

section Co
open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ}

noncomputable def co (R : ProlongationTuple P) (w : Place k ↥(modularFunctionFieldC k N)) (z : A) : ↥(R.nodeIntegers w) :=
  ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (z : AlgebraicClosure ℚ),
    R.algebraMap_mem_nodeIntegers w z⟩

@[scoped simp] theorem coe_co (R : ProlongationTuple P) (w : Place k ↥(modularFunctionFieldC k N)) (z : A) :
    ((co R w z : ↥(R.nodeIntegers w)) : ↥(modularFunctionFieldBar (N * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) (z : AlgebraicClosure ℚ) := rfl

end Co

end FltWs29.P1N
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29"

namespace FltWs29
namespace S6

open AlgebraicCurve IsLocalRing ModularCurve Polynomial
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple
open FltWs29.P1N

section G
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem HasValue.add (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem HasValue.neg (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) :
    v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem HasValue.sub (v : Place K F) {g g' : F} {a a' : K} (h : v.HasValue g a)
    (h' : v.HasValue g' a') : v.HasValue (g - g') (a - a') := by
  simpa only [sub_eq_add_neg] using HasValue.add v h (HasValue.neg v h')

theorem HasValue.pow (v : Place K F) {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) :
    v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using v.hasValue_one
  | succ n ih => simpa only [pow_succ] using ih.mul h

theorem hasValue_evalAt (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.HasValue f (v.evalAt f) :=
  ⟨hf, (v.algebraMap_evalAt hv hf).symm⟩

end G
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"

section AL

theorem qExpand_congr (S : Type*) [CommRing S] {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) (x : LaurentSeries S) :
    qExpand S n x = qExpand S m x := by
  subst h
  rfl

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N]

theorem isAtkinLehnerAutFull_of_not_dvd (hqN : ¬ q ∣ N) :
    IsAtkinLehnerAutFull N q (atkinLehnerInvolutionFull N q) :=
  isAtkinLehnerAutFull_atkinLehnerInvolutionFull N q
    (exists_isAtkinLehnerAutFull_of_prime_of_not_dvd N q Fact.out hqN)

theorem jFun_eq_mk :
    jFun N q = ⟨coeffEmb (AlgebraicClosure ℚ)
        ((⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))).2⟩ := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) jq = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq)
  rw [qExpand_one_apply]

theorem jQFun_eq_mk :
    jQFun N q = ⟨coeffEmb (AlgebraicClosure ℚ)
        ((⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩ :
          ↥(modularFunctionFieldFull (N * q))).2⟩ := by
  apply Subtype.ext
  show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
  rw [qExpand_congr ℚ (one_mul q)]

theorem atkinLehnerBar_jFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jFun N q) = jQFun N q := by
  obtain ⟨h1, -⟩ := isAtkinLehnerAutFull_of_not_dvd (q := q) (N := N) hqN 1 inferInstance (one_dvd N)
  have e := geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ 1 jq, jqd_mem_full (N * q) (Dvd.dvd.mul_right (one_dvd N) q)⟩
  rw [h1] at e
  rw [show atkinLehnerBar N q (jFun N q)
      = geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) (jFun N q) from rfl,
    jFun_eq_mk, e, jQFun_eq_mk]

theorem atkinLehnerBar_jQFun (hqN : ¬ q ∣ N) : atkinLehnerBar N q (jQFun N q) = jFun N q := by
  obtain ⟨-, h2⟩ := isAtkinLehnerAutFull_of_not_dvd (q := q) (N := N) hqN 1 inferInstance (one_dvd N)
  have e := geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q)
    ⟨qExpand ℚ (1 * q) jq, jqd_mem_full (N * q) (Nat.mul_dvd_mul_right (one_dvd N) q)⟩
  rw [h2] at e
  rw [show atkinLehnerBar N q (jQFun N q)
      = geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * q)) (atkinLehnerInvolutionFull N q) (jQFun N q) from rfl,
    jQFun_eq_mk, e, jFun_eq_mk]

end AL
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"

section RS
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)

theorem residue₁_of_coeffMap (y : LaurentSeries A) (f : ↥(modularFunctionFieldBar (N * q)))
    (hf : (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : f ∈ R.R₁.integers,
      ((R.residue₁ ⟨f, h⟩ : ↥(modularFunctionFieldC k N)) : LaurentSeries k) = coeffMap red y := by
  obtain ⟨f, hfF⟩ := f
  simp only at hf
  subst hf
  obtain ⟨hmem, hres⟩ := R.residue₁_coeffMap y hfF
  refine ⟨hmem, ?_⟩
  rw [ProlongationTuple.residue₁_apply, R.ι_coe, hres, coeffMap_coeffMap,
    show R.redBar.comp (IsLocalRing.residue A) = red from RingHom.ext R.redBar_residue]

theorem jFun_mem₁_and_residue₁ :
    ∃ h : jFun N q ∈ R.R₁.integers, R.residue₁ ⟨jFun N q, h⟩ = jGeomGen k N := by
  obtain ⟨h, hres⟩ := residue₁_of_coeffMap R (jqModC A) (jFun N q)
    (by rw [coe_jFun]; exact (coeffSemilinearAut.coeffMap_jqModC _).symm)
  exact ⟨h, Subtype.ext (by rw [hres]; exact coeffSemilinearAut.coeffMap_jqModC _)⟩

theorem jQFun_mem₁_and_residue₁ :
    ∃ h : jQFun N q ∈ R.R₁.integers, R.residue₁ ⟨jQFun N q, h⟩ = jGeomGen k N ^ q := by
  obtain ⟨h, hres⟩ := residue₁_of_coeffMap R (qExpand A q (jqModC A)) (jQFun N q)
    (by
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ q jq) = _
      rw [coeffEmb_qExpand, coeffEmb_jq, coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC])
  refine ⟨h, Subtype.ext ?_⟩
  rw [hres, coeffSemilinearAut.coeffMap_qExpand, coeffSemilinearAut.coeffMap_jqModC]
  show qExpand k q (jqModC k) = ((jGeomGen k N : ↥(modularFunctionFieldC k N)) : LaurentSeries k) ^ q
  have hpow := qExpand_jqNModC_eq_pow_unconditional k 1 (ℓ := q)
  rw [jqNModC_one] at hpow
  exact hpow

theorem residue₁_jFun (h : jFun N q ∈ R.R₁.integers) : R.residue₁ ⟨jFun N q, h⟩ = jGeomGen k N := by
  obtain ⟨h', e⟩ := jFun_mem₁_and_residue₁ (q := q) (N := N) R
  exact e

theorem residue₁_jQFun (h : jQFun N q ∈ R.R₁.integers) : R.residue₁ ⟨jQFun N q, h⟩ = jGeomGen k N ^ q := by
  obtain ⟨h', e⟩ := jQFun_mem₁_and_residue₁ (q := q) (N := N) R
  exact e

theorem jFun_mem₂ (hqN : ¬ q ∣ N) : jFun N q ∈ R.R₂.integers :=
  (R.mem_integers₂_iff _).mpr (by rw [atkinLehnerBar_jFun hqN]; exact (jQFun_mem₁_and_residue₁ R).1)

theorem jQFun_mem₂ (hqN : ¬ q ∣ N) : jQFun N q ∈ R.R₂.integers :=
  (R.mem_integers₂_iff _).mpr (by rw [atkinLehnerBar_jQFun hqN]; exact (jFun_mem₁_and_residue₁ R).1)

theorem residue₂_jFun (hqN : ¬ q ∣ N) (h₂ : jFun N q ∈ R.R₂.integers) :
    R.residue₂ ⟨jFun N q, h₂⟩ = jGeomGen k N ^ q := by
  rw [ProlongationTuple.residue₂_apply, R.residue₂_eq]
  have key : ∀ (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.R₁.integers), g = jQFun N q →
      R.ι (R.R₁.residue ⟨g, hg⟩) = jGeomGen k N ^ q := by
    rintro g hg rfl
    exact residue₁_jQFun R hg
  exact key _ _ (atkinLehnerBar_jFun hqN)

theorem residue₂_jQFun (hqN : ¬ q ∣ N) (h₂ : jQFun N q ∈ R.R₂.integers) :
    R.residue₂ ⟨jQFun N q, h₂⟩ = jGeomGen k N := by
  rw [ProlongationTuple.residue₂_apply, R.residue₂_eq]
  have key : ∀ (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.R₁.integers), g = jFun N q →
      R.ι (R.R₁.residue ⟨g, hg⟩) = jGeomGen k N := by
    rintro g hg rfl
    exact residue₁_jFun R hg
  exact key _ _ (atkinLehnerBar_jQFun hqN)

theorem residue₁_G (h : jQFun N q - jFun N q ^ q ∈ R.R₁.integers) :
    R.residue₁ ⟨jQFun N q - jFun N q ^ q, h⟩ = 0 := by
  obtain ⟨hJ, eJ⟩ := jFun_mem₁_and_residue₁ (q := q) (N := N) R
  obtain ⟨hJq, eJq⟩ := jQFun_mem₁_and_residue₁ (q := q) (N := N) R
  rw [show (⟨jQFun N q - jFun N q ^ q, h⟩ : ↥R.R₁.integers) = ⟨jQFun N q, hJq⟩ - ⟨jFun N q, hJ⟩ ^ q from rfl,
    map_sub, map_pow, eJ, eJq, sub_self]

theorem residue₁_H (h : jFun N q - jQFun N q ^ q ∈ R.R₁.integers) :
    R.residue₁ ⟨jFun N q - jQFun N q ^ q, h⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  obtain ⟨hJ, eJ⟩ := jFun_mem₁_and_residue₁ (q := q) (N := N) R
  obtain ⟨hJq, eJq⟩ := jQFun_mem₁_and_residue₁ (q := q) (N := N) R
  rw [show (⟨jFun N q - jQFun N q ^ q, h⟩ : ↥R.R₁.integers) = ⟨jFun N q, hJ⟩ - ⟨jQFun N q, hJq⟩ ^ q from rfl,
    map_sub, map_pow, eJ, eJq]

theorem residue₂_G (hqN : ¬ q ∣ N) (h : jQFun N q - jFun N q ^ q ∈ R.R₂.integers) :
    R.residue₂ ⟨jQFun N q - jFun N q ^ q, h⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  rw [show (⟨jQFun N q - jFun N q ^ q, h⟩ : ↥R.R₂.integers) = ⟨jQFun N q, jQFun_mem₂ R hqN⟩ - ⟨jFun N q, jFun_mem₂ R hqN⟩ ^ q
      from rfl, map_sub, map_pow, residue₂_jFun R hqN, residue₂_jQFun R hqN]

theorem residue₂_H (hqN : ¬ q ∣ N) (h : jFun N q - jQFun N q ^ q ∈ R.R₂.integers) :
    R.residue₂ ⟨jFun N q - jQFun N q ^ q, h⟩ = 0 := by
  rw [show (⟨jFun N q - jQFun N q ^ q, h⟩ : ↥R.R₂.integers) = ⟨jFun N q, jFun_mem₂ R hqN⟩ - ⟨jQFun N q, jQFun_mem₂ R hqN⟩ ^ q
      from rfl, map_sub, map_pow, residue₂_jFun R hqN, residue₂_jQFun R hqN, sub_self]

end RS
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"

section Ord
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

variable {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] {k : Type*} [Field k] [CharP k q]

theorem jGeomGen_sub_pow_sq_eq (c : k) (hc : c ^ (q ^ 2) = c) :
    jGeomGen k N - (jGeomGen k N ^ q) ^ q
      = (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c)
          * (1 - (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c) ^ (q ^ 2 - 1)) := by
  haveI : CharP ↥(modularFunctionFieldC k N) q :=
    charP_of_injective_algebraMap (algebraMap k ↥(modularFunctionFieldC k N)).injective q
  have hfrob : (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) c) ^ (q ^ 2)
      = jGeomGen k N ^ (q ^ 2) - algebraMap k ↥(modularFunctionFieldC k N) c := by
    rw [sub_pow_char_pow, ← map_pow, hc]
  calc jGeomGen k N - (jGeomGen k N ^ q) ^ q
      = (jGeomGen k N - algebraMap k _ c) - (jGeomGen k N ^ (q ^ 2) - algebraMap k _ c) := by rw [← pow_mul, ← sq]; ring
    _ = (jGeomGen k N - algebraMap k _ c) - (jGeomGen k N - algebraMap k _ c) ^ (q ^ 2) := by rw [hfrob]
    _ = _ := by
      have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow 2 q (Fact.out : q.Prime).pos
      conv_lhs => rw [show q ^ 2 = (q ^ 2 - 1) + 1 from (Nat.sub_add_cancel hq2).symm, pow_succ]
      ring

variable [IsAlgClosed k] [DecidableEq k]

theorem ord_jGeomGen_sub_eq_one (hq : 5 ≤ q) (hqN : ¬ q ∣ N)
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k)
    {a : k} (ha : w.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) = 1 := by
  have hss : IsSupersingularPlace q N k w := hw
  have hdvd := placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hq hqN hw
  rw [ha, jWidth_of_ne h0 h1728, Nat.dvd_one] at hdvd
  have hpos : 0 < w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (w.evalAt (jGeomGen k N))) :=
    ord_sub_evalAt_pos_of_isRational hss.1 hss.2.1.1 (jGeomGen_sub_algebraMap_ne_zero k N _)
  rw [ha] at hpos
  have hram : placeRamificationJ N w
      = (w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) (w.evalAt (jGeomGen k N)))).toNat := rfl
  rw [ha, hdvd] at hram
  have h2 : ((w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a)).toNat : ℤ)
      = w.ord (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) := Int.toNat_of_nonneg hpos.le
  rw [← hram] at h2
  exact_mod_cast h2.symm

theorem ord_jGeomGen_sub_pow_sq_eq_one (hq : 5 ≤ q) (hqN : ¬ q ∣ N)
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k)
    {a : k} (ha : w.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    w.ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = 1 := by
  have hss : IsSupersingularPlace q N k w := hw
  have ha2 : a ^ (q ^ 2) = a := by
    have h := pow_q_sq_eq_self_of_mem_ssJSet q hss.2.2
    rwa [ha] at h
  have hJ : w.HasValue (jGeomGen k N) a := ha ▸ hasValue_evalAt w hss.1 hss.2.1.1
  have h1 := ord_jGeomGen_sub_eq_one hq hqN hw ha h0 h1728
  have hne : jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at h1; exact zero_ne_one h1
  obtain ⟨m, hm⟩ : ∃ m, q ^ 2 - 1 = m + 1 :=
    ⟨q ^ 2 - 2, by have := Nat.one_lt_pow (two_ne_zero) (Fact.out : q.Prime).one_lt; omega⟩
  have hunit : w.HasValue (1 - (jGeomGen k N - algebraMap k ↥(modularFunctionFieldC k N) a) ^ (q ^ 2 - 1)) 1 := by
    have h := HasValue.sub _ hJ (w.hasValue_algebraMap a)
    have h2 := HasValue.sub _ (w.hasValue_one) (HasValue.pow _ h (m + 1))
    rw [hm]
    simpa only [sub_self, zero_pow (Nat.succ_ne_zero m), sub_zero] using h2
  rw [jGeomGen_sub_pow_sq_eq a ha2, Place.ord_mul _ hne (hunit.ne_zero one_ne_zero), h1,
    hunit.ord_eq_zero one_ne_zero, add_zero]

theorem arithFrobC_smul_jGeomGen_sub_pow_sq :
    arithFrobC q k N • (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = jGeomGen k N - (jGeomGen k N ^ q) ^ q := by
  have hj : arithFrobC q k N • jGeomGen k N = jGeomGen k N := arithFrobC_smul_jq q k N
  show SemilinearAut.toRingAut (arithFrobC q k N) (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = _
  rw [map_sub, map_pow, map_pow, show SemilinearAut.toRingAut (arithFrobC q k N) (jGeomGen k N) = jGeomGen k N from hj]

theorem ord_smul_jGeomGen_sub_pow_sq_eq_one (hq : 5 ≤ q) (hqN : ¬ q ∣ N)
    {w : Place k ↥(modularFunctionFieldC k N)} (hw : w ∈ ssPlaces q N k)
    {a : k} (ha : w.evalAt (jGeomGen k N) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    (arithFrobC q k N • w).ord (jGeomGen k N - (jGeomGen k N ^ q) ^ q) = 1 := by
  conv_lhs => rw [← arithFrobC_smul_jGeomGen_sub_pow_sq (q := q) (k := k) (N := N)]
  rw [SemilinearAut.ord_smul]
  exact ord_jGeomGen_sub_pow_sq_eq_one hq hqN hw ha h0 h1728

end Ord
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"

section Main
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

theorem main
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (w : Place k ↥(modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    ∃ c : R.NodeCoordinates K w,
      ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (jQFun N q - jFun N q ^ q) ∧
      ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (jFun N q - jQFun N q ^ q) ∧
      ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ eK * u := by
  classical
  obtain ⟨Rk, hRk, -⟩ := existsUnique_kroneckerRemainder q data hKr
  have hssw : IsSupersingularPlace q N k w := hw
  have hss : a ∈ ssJSet q k := by
    rw [← ha]
    exact ((isSupersingularPlace_iff q N k w).mp hssw).2.2

  have memBK : ∀ g : ↥(modularFunctionFieldBar (N * q)),
      (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ NodeLocalized.modularLocalizedAtPoint (1 * q)
        (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) →
      g ∈ R.nodeIntegersOver K w := by
    intro g hg
    obtain ⟨g', hg', hc⟩ := R.exists_mem_nodeIntegersOver_of_mem_modularLocalizedAtPoint {w}
      (fun v hv => by rw [Finset.mem_singleton] at hv; rw [hv]; exact hw) K w (Finset.mem_singleton_self w) a ha _ hg
    rw [← (Subtype.ext hc : g' = g)]
    exact hg'
  have hJ : jFun N q ∈ R.nodeIntegersOver K w := memBK _ (by
    rw [coe_jFun, ← modularEval_X0 (1 * q) (NodeLocalized.coeffSubring A K)]
    exact NodeLocalized.modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _)
  have hJq : jQFun N q ∈ R.nodeIntegersOver K w := memBK _ (by
    rw [coe_jQFun, ← modularEval_X1 (1 * q) (NodeLocalized.coeffSubring A K)]
    exact NodeLocalized.modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _)
  set Jo : ↥(R.nodeIntegersOver K w) := ⟨jFun N q, hJ⟩ with hJo
  set Jqo : ↥(R.nodeIntegersOver K w) := ⟨jQFun N q, hJq⟩ with hJqo
  set Go : ↥(R.nodeIntegersOver K w) := Jqo - Jo ^ q with hGo
  set Ho : ↥(R.nodeIntegersOver K w) := Jo - Jqo ^ q with hHo
  set Uo : ↥(R.nodeIntegersOver K w) := twoVarEval (↥(R.nodeIntegersOver K w)) Jo Jqo Rk with hUo
  have cGo : (Go : ↥(modularFunctionFieldBar (N * q))) = jQFun N q - jFun N q ^ q := rfl
  have cHo : (Ho : ↥(modularFunctionFieldBar (N * q))) = jFun N q - jQFun N q ^ q := rfl
  have cUo : (Uo : ↥(modularFunctionFieldBar (N * q)))
      = twoVarEval (↥(modularFunctionFieldBar (N * q))) (jFun N q) (jQFun N q) Rk := by
    rw [show ((Uo : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (R.nodeIntegersOver K w).subtype Uo from rfl,
      hUo, map_twoVarEval]
    rfl

  set RkA : MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K) :=
    twoVarEval (MvPolynomial (Fin 2) ↥(NodeLocalized.coeffSubring A K)) (MvPolynomial.X 0) (MvPolynomial.X 1) Rk
    with hRkA
  have hK2 : twoVarEval k a (a ^ q) Rk ≠ 0 :=
    eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data Rk hRk a hss h0 h1728
  have hpt : NodeLocalized.pointEval (NodeLocalized.coeffSubring A K) (NodeLocalized.redRestrict red K) a (a ^ q) RkA ≠ 0 := by
    rw [hRkA, pointEval_twoVarEval]
    exact hK2
  have hUL : NodeLocalized.modularEval (1 * q) (NodeLocalized.coeffSubring A K) RkA
      = ((Uo : ↥(modularFunctionFieldBar (N * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hRkA, modularEval_twoVarEval, cUo, coe_twoVarEval, coe_jFun, coe_jQFun]
  have hUne : (Uo : ↥(modularFunctionFieldBar (N * q))) ≠ 0 := by
    intro h0'
    apply hpt
    apply NodeLocalized.pointEval_eq_zero_of_modularEval_eq_zero
    rw [hUL, h0', ZeroMemClass.coe_zero]
  have hUinv : (Uo : ↥(modularFunctionFieldBar (N * q)))⁻¹ ∈ R.nodeIntegersOver K w := memBK _ ⟨1, RkA, hpt, by
    rw [map_one, hUL, ← MulMemClass.coe_mul, inv_mul_cancel₀ hUne, OneMemClass.coe_one]⟩
  have hUunit : IsUnit Uo :=
    ⟨⟨Uo, ⟨(Uo : ↥(modularFunctionFieldBar (N * q)))⁻¹, hUinv⟩,
      Subtype.ext (mul_inv_cancel₀ hUne), Subtype.ext (inv_mul_cancel₀ hUne)⟩, rfl⟩

  have hGHF : (jQFun N q - jFun N q ^ q) * (jFun N q - jQFun N q ^ q)
      = (q : ↥(modularFunctionFieldBar (N * q)))
        * twoVarEval (↥(modularFunctionFieldBar (N * q))) (jFun N q) (jQFun N q) Rk := by
    have hk := twoVarEval_of_kronecker hRk (↥(modularFunctionFieldBar (N * q))) (jFun N q) (jQFun N q)
    rw [twoVarEval_jFun_jQFun data] at hk
    linear_combination hk
  have hGH : Go * Ho = (q : ↥(R.nodeIntegersOver K w)) * Uo := by
    apply Subtype.ext
    push_cast
    rw [cGo, cHo, cUo]
    exact hGHF

  have hG₁ : jQFun N q - jFun N q ^ q ∈ R.R₁.integers := Go.2.1.1
  have hG₂ : jQFun N q - jFun N q ^ q ∈ R.R₂.integers := Go.2.1.2.1
  have hH₁ : jFun N q - jQFun N q ^ q ∈ R.R₁.integers := Ho.2.1.1
  have hH₂ : jFun N q - jQFun N q ^ q ∈ R.R₂.integers := Ho.2.1.2.1
  have x_fst : R.nodeResidue₁ w ⟨(Go : ↥(modularFunctionFieldBar (N * q))), Go.2.1⟩ = 0 := by
    rw [nodeResidue₁_apply]
    exact residue₁_G R hG₁
  have x_snd : (arithFrobC q k N • w).ord (R.nodeResidue₂ w ⟨(Go : ↥(modularFunctionFieldBar (N * q))), Go.2.1⟩) = 1 := by
    rw [nodeResidue₂_apply]
    rw [show R.residue₂ ⟨((⟨(Go : ↥(modularFunctionFieldBar (N * q))), Go.2.1⟩ : ↥(R.nodeIntegers w)) :
        ↥(modularFunctionFieldBar (N * q))), Go.2.1.2.1⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q from residue₂_G R hqN hG₂]
    exact ord_smul_jGeomGen_sub_pow_sq_eq_one hq hqN hw ha h0 h1728
  have y_snd : R.nodeResidue₂ w ⟨(Ho : ↥(modularFunctionFieldBar (N * q))), Ho.2.1⟩ = 0 := by
    rw [nodeResidue₂_apply]
    exact residue₂_H R hqN hH₂
  have y_fst : w.ord (R.nodeResidue₁ w ⟨(Ho : ↥(modularFunctionFieldBar (N * q))), Ho.2.1⟩) = 1 := by
    rw [nodeResidue₁_apply]
    rw [show R.residue₁ ⟨((⟨(Ho : ↥(modularFunctionFieldBar (N * q))), Ho.2.1⟩ : ↥(R.nodeIntegers w)) :
        ↥(modularFunctionFieldBar (N * q))), Ho.2.1.1⟩ = jGeomGen k N - (jGeomGen k N ^ q) ^ q from residue₁_H R hH₁]
    exact ord_jGeomGen_sub_pow_sq_eq_one hq hqN hw ha h0 h1728

  refine ⟨⟨Go, Ho, x_fst, x_snd, y_snd, y_fst⟩, cGo, cHo, R.nodeConst K w ε * Uo,
    (hε.map (R.nodeConst K w)).mul hUunit, ?_⟩
  show Go * Ho = R.nodeConst K w ϖ ^ eK * (R.nodeConst K w ε * Uo)
  rw [hGH, ← map_natCast (R.nodeConst K w) q, hqe, map_mul, map_pow, mul_assoc]

end Main
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"

end FltWs29.S6
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29 P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord.FltWs29.P1N"

open AlgebraicCurve IsLocalRing ModularCurve in
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (hqN : ¬ q ∣ N) (hq : 5 ≤ q)
    (w : Place k ↥(modularFunctionFieldC k N)) (hw : w ∈ ssPlaces q N k)
    (hfix : arithFrobC q k N • (arithFrobC q k N • w) = w)
    (a : k) (ha : w.evalAt (jGeomGen k N) = a)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K), NodeLocalized.redRestrict red K d = 0 ↔ ∃ d', d = ϖ * d')
    (eK : ℕ) (ε : ↥(NodeLocalized.coeffSubring A K)) (hε : IsUnit ε)
    (hqe : ((q : ℕ) : ↥(NodeLocalized.coeffSubring A K)) = ϖ ^ eK * ε) :
    ∃ c : R.NodeCoordinates K w,
      ((c.x : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (jQFun N q - jFun N q ^ q) ∧
      ((c.y : ↥(R.nodeIntegersOver K w)) : ↥(modularFunctionFieldBar (N * q))) = (jFun N q - jQFun N q ^ q) ∧
      ∃ u : ↥(R.nodeIntegersOver K w), IsUnit u ∧ c.x * c.y = R.nodeConst K w ϖ ^ eK * u :=
  FltWs29.S6.main R hker hqN hq w hw hfix a ha h0 h1728 K ϖ hϖ eK ε hε hqe

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_nodeCoordinates_levelOneNodeCoord (solution)
