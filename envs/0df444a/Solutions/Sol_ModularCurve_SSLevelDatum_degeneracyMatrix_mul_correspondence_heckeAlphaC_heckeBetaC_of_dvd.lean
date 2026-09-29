-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.degeneracyMatrix_mul_correspondence_heckeAlphaC_heckeBetaC_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1acd743e-720e-5663-8f4b-3f836cb821bd

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Definitions.Def_ModularCurve_ComponentGroupHecke
import Theorems.Thm_ModularCurve_degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed
import Theorems.Thm_ModularCurve_degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_single_one
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_degeneracyMatrix_mul_correspondence_heckeAlphaC_heckeBetaC_of_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply"
p2m_attr_erase "simp" "ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluX_empty WeierstrassCurve.veluY_empty WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_norm AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_SSLevelDatum_degeneracyMatrix_mul_correspondence_heckeAlphaC_heckeBetaC_of_dvd.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "levelAlphaC coe_levelAlphaC levelBetaC coe_levelBetaC SSLevelDatum charLDegeneracyRoof heckeAlphaC heckeBetaC modularFunctionFieldC qExpand ssPlaces degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected"
namespace SSLevelDatum
p2m_export "ModularCurve.SSLevelDatum" "degeneracyData sndIntegral legsIntegral mem_s mem_M fstIntegral"
namespace F1
p2m_open "ModularCurve.SSLevelDatum ModularCurve"

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
variable {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s)

def levelPair : Fin 2 → (↥(modularFunctionFieldC K M) →ₐ[K] ↥(modularFunctionFieldC K (M * s))) :=
  ![levelAlphaC K M s X.mem_M, levelBetaC K M s X.mem_s]

theorem levelPair_integral : ∀ i, (levelPair X i).toRingHom.IsIntegral := by
  intro i
  fin_cases i
  · exact X.fstIntegral
  · exact X.sndIntegral

theorem coe_levelPair_zero (x : ↥(modularFunctionFieldC K M)) :
    ((levelPair X 0 x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K) = x :=
  coe_levelAlphaC K M s X.mem_M x

theorem coe_levelPair_one (x : ↥(modularFunctionFieldC K M)) :
    ((levelPair X 1 x : ↥(modularFunctionFieldC K (M * s))) : LaurentSeries K) = qExpand K s x :=
  coe_levelBetaC K M s X.mem_s x

def legMap : Fin 2 → (↥(ssPlaces p (M * s) K) → ↥(ssPlaces p M K)) :=
  ![X.degeneracyData.a, X.degeneracyData.b]

theorem legMap_eq (i : Fin 2) : ![X.degeneracyData.a, X.degeneracyData.b] i = legMap X i := rfl

theorem legMap_val (i : Fin 2) (e : ↥(ssPlaces p (M * s) K)) :
    (legMap X i e).1 = Place.restrictAlong (levelPair X i) (levelPair_integral X i) e.1 := by
  fin_cases i <;> rfl

theorem mem_of_restrictAlong_eq (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) (i : Fin 2)
    (v : ↥(ssPlaces p M K)) (W : Place K ↥(modularFunctionFieldC K (M * s)))
    (hW : Place.restrictAlong (levelPair X i) (levelPair_integral X i) W = v.1) : W ∈ ssPlaces p (M * s) K :=
  (degeneracyPair_finiteSeparableDeg_ssPlaces_preserved_reflected M s p hs hsp hpM hsM (k := K)
    (levelPair X) (levelPair_integral X) (coe_levelPair_zero X) (coe_levelPair_one X)).2.2.2.2 i v.1 v.2 W hW

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] in

theorem deg_eq_one_of_mem {N : ℕ} [NeZero N] {w : Place K ↥(modularFunctionFieldC K N)}
    (h : w ∈ ssPlaces p N K) : w.deg = 1 :=
  (Place.isRational_iff_deg_eq_one w).1 h.1

theorem pushforwardAlong_single_eq (i : Fin 2) (e : ↥(ssPlaces p (M * s) K)) (n : ℤ) :
    Divisor.pushforwardAlong (levelPair X i) (levelPair_integral X i) (Finsupp.single e.1 n) =
      Finsupp.single (legMap X i e).1 n := by
  have h1 : Divisor.pushforwardAlong (levelPair X i) (levelPair_integral X i) (Finsupp.single e.1 1) =
      Finsupp.single (legMap X i e).1 1 := by
    rw [legMap_val]
    refine Divisor.pushforwardAlong_single_one _ _ _ (deg_eq_one_of_mem e.2) ?_
    rw [← legMap_val]
    exact deg_eq_one_of_mem (legMap X i e).2
  rw [← Finsupp.smul_single_one e.1 n, map_zsmul, h1, Finsupp.smul_single_one]

theorem pushforwardAlong_apply_eq_sum (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M)
    [Fintype ↥(ssPlaces p (M * s) K)] [DecidableEq ↥(ssPlaces p M K)] (i : Fin 2)
    (D : Divisor K ↥(modularFunctionFieldC K (M * s))) (v : ↥(ssPlaces p M K)) :
    Divisor.pushforwardAlong (levelPair X i) (levelPair_integral X i) D v.1 =
      ∑ e ∈ Finset.univ.filter (fun e => legMap X i e = v), D e.1 := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_const_zero]
  | add f g hf hg => rw [map_add, Finsupp.add_apply, hf, hg, ← Finset.sum_add_distrib]; rfl
  | single w n =>
      by_cases hw : Place.restrictAlong (levelPair X i) (levelPair_integral X i) w = v.1
      ·
        have hwss : w ∈ ssPlaces p (M * s) K := mem_of_restrictAlong_eq X hs hsp hpM hsM i v w hw
        set e₀ : ↥(ssPlaces p (M * s) K) := ⟨w, hwss⟩ with he₀
        have hleg : legMap X i e₀ = v := Subtype.ext (by rw [legMap_val]; exact hw)
        rw [show w = e₀.1 from rfl, pushforwardAlong_single_eq X i e₀ n, hleg, Finsupp.single_eq_same]
        rw [Finset.sum_eq_single e₀]
        · rw [Finsupp.single_eq_same]
        · intro e he hne
          rw [Finsupp.single_apply, if_neg]
          intro h
          exact hne (Subtype.ext h.symm)
        · intro h
          exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ e₀, hleg⟩) h
      ·
        rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, if_neg hw]
        symm
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_filter] at he
        rw [Finsupp.single_apply, if_neg]
        intro h
        apply hw
        rw [h, ← legMap_val, he.2]

theorem main (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M)
    [Fintype ↥(ssPlaces p (M * s) K)] [Fintype ↥(ssPlaces p M K)] [DecidableEq ↥(ssPlaces p M K)]
    (ℓ : Nat.Primes) (hℓM : (ℓ : ℕ) ∣ M) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ)] (i : Fin 2) :
    CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) *
        Matrix.of (fun y x : ↥(ssPlaces p (M * s) K) =>
          Divisor.correspondence (heckeAlphaC K (M * s) ℓ) (heckeBetaC K (M * s) ℓ)
            (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 (Finsupp.single x.1 1) y.1) =
      Matrix.of (fun y x : ↥(ssPlaces p M K) =>
          Divisor.correspondence (heckeAlphaC K M ℓ) (heckeBetaC K M ℓ)
            (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2 (Finsupp.single x.1 1) y.1) *
        CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) := by
  classical
  have hℓs : (ℓ : ℕ) ≠ s := fun h => hsM (h ▸ hℓM)
  have hℓp : (ℓ : ℕ) ≠ p := fun h => hpM (h ▸ hℓM)

  have comm := degeneracyPair_pushforwardAlong_correspondence_comm_of_ne_of_charP_of_isAlgClosed M s ℓ p hs ℓ.prop
    hℓs hsp hℓp hpM hsM (k := K) (levelPair X) (levelPair_integral X) (coe_levelPair_zero X) (coe_levelPair_one X)
    (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2 i
  ext v x
  rw [legMap_eq, Matrix.mul_apply, Matrix.mul_apply]
  simp only [CerednikDrinfeld.degeneracyMatrix, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero]

  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

  rw [← Finset.sum_filter]
  rw [← pushforwardAlong_apply_eq_sum X hs hsp hpM hsM i _ v, comm (Finsupp.single x.1 1),
    pushforwardAlong_single_eq X i x 1]

end ModularCurve.SSLevelDatum.F1

open ModularCurve.SSLevelDatum.F1 in
theorem solution
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    {M s : ℕ} [NeZero M] [NeZero s] (X : SSLevelDatum p K M s)
    (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M)
    [Fintype ↥(ssPlaces p (M * s) K)] [Fintype ↥(ssPlaces p M K)] [DecidableEq ↥(ssPlaces p M K)]
    (ℓ : Nat.Primes) (hℓM : (ℓ : ℕ) ∣ M) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K M ℓ)] (i : Fin 2) :
    CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) *
        Matrix.of (fun y x : ↥(ssPlaces p (M * s) K) =>
          Divisor.correspondence (heckeAlphaC K (M * s) ℓ) (heckeBetaC K (M * s) ℓ)
            (X.legsIntegral (M * s) ℓ).1 (X.legsIntegral (M * s) ℓ).2 (Finsupp.single x.1 1) y.1) =
      Matrix.of (fun y x : ↥(ssPlaces p M K) =>
          Divisor.correspondence (heckeAlphaC K M ℓ) (heckeBetaC K M ℓ)
            (X.legsIntegral M ℓ).1 (X.legsIntegral M ℓ).2 (Finsupp.single x.1 1) y.1) *
        CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i) :=
  main X hs hsp hpM hsM ℓ hℓM i

end

end S_ModularCurve_SSLevelDatum_degeneracyMatrix_mul_correspondence_heckeAlphaC_heckeBetaC_of_dvd
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_degeneracyMatrix_mul_correspondence_heckeAlphaC_heckeBetaC_of_dvd (solution)
