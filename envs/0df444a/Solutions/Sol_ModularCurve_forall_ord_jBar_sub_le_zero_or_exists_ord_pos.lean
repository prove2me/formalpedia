-- Prove2me | solution 1 for ModularCurve.forall_ord_jBar_sub_le_zero_or_exists_ord_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/462eed0e-d220-50f6-90f8-8e534f92aea5

import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Mathlib.RingTheory.Valuation.LocalSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

noncomputable section

open ModularCurve AlgebraicCurve Polynomial

namespace CharpS10bB
namespace TRI

private abbrev Qb : Type := AlgebraicClosure ℚ

variable (N : ℕ) [NeZero N]

private abbrev Fb : IntermediateField Qb (LaurentSeries Qb) := modularFunctionFieldBar N

private def J : Fb N :=
  ⟨coeffEmb Qb jq, coeffEmb_mem_laurentBaseChange Qb (modularFunctionField_le_full N (jq_mem N))⟩

private def JN : Fb N :=
  ⟨coeffEmb Qb (qExpand ℚ N jq), coeffEmb_mem_laurentBaseChange Qb (jqd_mem_full N (dvd_refl N))⟩

@[scoped simp] private theorem coe_J : ((J N : Fb N) : LaurentSeries Qb) = coeffEmb Qb jq := rfl
@[scoped simp] private theorem coe_JN : ((JN N : Fb N) : LaurentSeries Qb) = coeffEmb Qb (qExpand ℚ N jq) := rfl

omit [NeZero N] in

private theorem coe_algebraMap (c : Qb) :
    ((algebraMap Qb (Fb N) c : Fb N) : LaurentSeries Qb) = HahnSeries.single 0 c := by
  show algebraMap Qb (LaurentSeries Qb) c = _
  exact algebraMap_laurentSeries_eq_single Qb c

private theorem J_sub_ne_zero (c : Qb) : J N - algebraMap Qb (Fb N) c ≠ 0 := by
  intro h
  have h1 := congrArg (fun x : Fb N => ((x : Fb N) : LaurentSeries Qb).coeff (-1)) (sub_eq_zero.mp h)
  simp only [coe_J, coeffEmb_coeff, coeff_jq_neg_one, map_one, coe_algebraMap,
    HahnSeries.coeff_single_of_ne (show (-1 : ℤ) ≠ 0 by decide)] at h1
  exact one_ne_zero h1

private theorem JN_sub_ne_zero (c : Qb) : JN N - algebraMap Qb (Fb N) c ≠ 0 := by
  intro h
  have hN0 : (-(N : ℤ)) ≠ 0 := by
    have := NeZero.ne N
    omega
  have h1 := congrArg (fun x : Fb N => ((x : Fb N) : LaurentSeries Qb).coeff (-(N : ℤ)))
    (sub_eq_zero.mp h)
  have hq : (qExpand ℚ N jq).coeff (-(N : ℤ)) = 1 := by
    rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jq_neg_one]
  simp only [coe_JN, coeffEmb_coeff, hq, map_one, coe_algebraMap, HahnSeries.coeff_single_of_ne hN0] at h1
  exact one_ne_zero h1

private theorem coeffEmb_eval₂Bivar (Φ : Polynomial (Polynomial ℤ)) (u w : LaurentSeries ℚ) :
    coeffEmb Qb (Φ.eval₂ (Polynomial.aeval (R := ℤ) u).toRingHom w)
      = Φ.eval₂ (Polynomial.aeval (R := ℤ) (coeffEmb Qb u)).toRingHom (coeffEmb Qb w) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply Polynomial.ringHom_ext
  · intro a
    simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.aeval_X]

private theorem eval₂_J_JN (dataN : ModularPolynomialData N) :
    dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (J N)).toRingHom (JN N) = 0 := by
  apply (algebraMap (Fb N) (LaurentSeries Qb)).injective
  rw [map_zero, Polynomial.hom_eval₂]
  have hcomp : (algebraMap (Fb N) (LaurentSeries Qb)).comp (Polynomial.aeval (R := ℤ) (J N)).toRingHom
      = (Polynomial.aeval (R := ℤ) (coeffEmb Qb jq)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Polynomial.aeval_X]
      rfl
  rw [hcomp, show algebraMap (Fb N) (LaurentSeries Qb) (JN N) = coeffEmb Qb (qExpand ℚ N jq) from rfl,
    show qExpand ℚ N jq = jqN N from rfl, ← coeffEmb_eval₂Bivar,
    show (Polynomial.aeval (R := ℤ) jq).toRingHom = evalAtJ from rfl, dataN.eval_eq_zero, map_zero]

section AtPlace

variable (v : Place Qb (Fb N))

private theorem isRational : v.IsRational := by
  have hdeg : Module.finrank Qb v.ResidueField = 1 := deg_eq_one_modularFunctionFieldBar N v
  intro x
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp hdeg x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

private theorem sub_evalAt_mem_maximalIdeal {f : Fb N} (hf : f ∈ v.toValuationSubring) :
    (⟨f - algebraMap Qb (Fb N) (v.evalAt f), sub_mem hf (v.algebraMap_mem' _)⟩ : v.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨f - algebraMap Qb (Fb N) (v.evalAt f), sub_mem hf (v.algebraMap_mem' _)⟩
      : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap Qb v.toValuationSubring (v.evalAt f) :=
    Subtype.ext rfl
  rw [hsplit, (IsLocalRing.residue v.toValuationSubring).map_sub, ← v.algebraMap_evalAt (isRational N v) hf,
    IsScalarTower.algebraMap_apply Qb v.toValuationSubring v.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq, sub_self]

omit [NeZero N] in

private theorem ord_pos_of_mem {f : Fb N} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring)
    (hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring) :
    0 < v.ord f :=
  (v.mem_maximalIdeal_iff_ord_pos hf0 hf).mp hm

omit [NeZero N] in

private theorem aeval_mem {x : Fb N} (hx : x ∈ v.toValuationSubring) (p : Polynomial ℤ) :
    Polynomial.aeval (R := ℤ) x p ∈ v.toValuationSubring := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, algebraMap_int_eq, eq_intCast]
    exact mul_mem (intCast_mem _ a) (pow_mem hx n)

end AtPlace

private theorem dichotomy (A : ValuationSubring Qb) (dataN : ModularPolynomialData N) (v : Place Qb (Fb N)) :
    (∀ a : A, v.ord (J N - algebraMap Qb (Fb N) (a : Qb)) ≤ 0) ∨
    ∃ a aN : A, 0 < v.ord (J N - algebraMap Qb (Fb N) (a : Qb)) ∧
      0 < v.ord (JN N - algebraMap Qb (Fb N) (aN : Qb)) := by
  by_cases hJ : (J N : Fb N) ∈ v.toValuationSubring
  swap
  ·
    left
    intro a
    by_contra hlt
    rw [not_le] at hlt
    apply hJ
    have hmem := v.mem_toValuationSubring_of_ord_nonneg_alt (J_sub_ne_zero N (a : Qb)) hlt.le
    have := add_mem hmem (v.algebraMap_mem' (a : Qb))
    rwa [sub_add_cancel] at this

  set c : Qb := v.evalAt (J N) with hc
  have hJc := sub_evalAt_mem_maximalIdeal N v hJ
  by_cases hcA : c ∈ A
  swap
  ·
    left
    intro a
    by_contra hlt
    rw [not_le] at hlt
    have hne : (c - (a : Qb)) ≠ 0 := by
      intro h
      apply hcA
      rw [sub_eq_zero] at h
      rw [h]
      exact a.2
    have hmemJa : J N - algebraMap Qb (Fb N) (a : Qb) ∈ v.toValuationSubring :=
      sub_mem hJ (v.algebraMap_mem' _)
    have hJa : (⟨J N - algebraMap Qb (Fb N) (a : Qb), hmemJa⟩ : v.toValuationSubring)
        ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
      (v.mem_maximalIdeal_iff_ord_pos (J_sub_ne_zero N (a : Qb)) hmemJa).mpr hlt

    have hconst : algebraMap Qb v.toValuationSubring (c - (a : Qb))
        ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
      have hdiff := sub_mem hJa hJc
      convert hdiff using 1
      apply Subtype.ext
      show algebraMap Qb (Fb N) (c - (a : Qb)) = (J N - algebraMap Qb (Fb N) (a : Qb))
        - (J N - algebraMap Qb (Fb N) (v.evalAt (J N)))
      rw [map_sub, ← hc]
      ring
    exact (IsLocalRing.mem_maximalIdeal _).mp hconst ((IsUnit.mk0 _ hne).map _)

  right

  set P : Polynomial (Fb N) := dataN.Φ.map (Polynomial.aeval (R := ℤ) (J N)).toRingHom with hP
  have hPm : P.Monic := dataN.monic.map _
  have hPc : ∀ i, P.coeff i ∈ v.toValuationSubring := by
    intro i
    rw [hP, Polynomial.coeff_map]
    exact aeval_mem N v hJ _
  have hPev : P.eval (JN N) = 0 := by
    rw [hP, Polynomial.eval_map]
    exact eval₂_J_JN N dataN
  have hJN : (JN N : Fb N) ∈ v.toValuationSubring := v.mem_of_eval_monic_eq_zero hPm hPc hPev
  set cN : Qb := v.evalAt (JN N) with hcN
  have hJNc := sub_evalAt_mem_maximalIdeal N v hJN

  have hrel : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) c).toRingHom cN = 0 := by
    apply (algebraMap Qb v.ResidueField).injective
    rw [map_zero, Polynomial.hom_eval₂]

    have hOv : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨J N, hJ⟩ : v.toValuationSubring)).toRingHom
        ⟨JN N, hJN⟩ = 0 := by
      apply Subtype.val_injective
      show ((dataN.Φ.eval₂ _ _ : v.toValuationSubring) : Fb N) = ((0 : v.toValuationSubring) : Fb N)
      rw [show ((dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (⟨J N, hJ⟩ : v.toValuationSubring)).toRingHom
            ⟨JN N, hJN⟩ : v.toValuationSubring) : Fb N)
          = (algebraMap v.toValuationSubring (Fb N)) (dataN.Φ.eval₂ _ _) from rfl,
        Polynomial.hom_eval₂]
      have hcomp : (algebraMap v.toValuationSubring (Fb N)).comp
          (Polynomial.aeval (R := ℤ) (⟨J N, hJ⟩ : v.toValuationSubring)).toRingHom
          = (Polynomial.aeval (R := ℤ) (J N)).toRingHom := by
        apply Polynomial.ringHom_ext
        · intro a
          simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
        · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
            AlgHom.coe_toRingHom, Polynomial.aeval_X]
          rfl
      rw [hcomp]
      exact eval₂_J_JN N dataN

    have hres := congrArg (IsLocalRing.residue v.toValuationSubring) hOv
    rw [map_zero, Polynomial.hom_eval₂] at hres
    convert hres using 2
    · apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, Polynomial.aeval_X]
        rw [hc]
        exact v.algebraMap_evalAt (isRational N v) hJ
    · rw [hcN]
      exact v.algebraMap_evalAt (isRational N v) hJN

  have hcNA : cN ∈ A := by
    set a₀ : A := ⟨c, hcA⟩ with ha₀
    have hcomp : (algebraMap A Qb).comp (Polynomial.aeval (R := ℤ) a₀).toRingHom
        = (Polynomial.aeval (R := ℤ) c).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [AlgHom.toRingHom_eq_coe, eq_intCast, map_intCast]
      · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom, Polynomial.aeval_X]
        rfl
    have hint : IsIntegral A cN := by
      refine ⟨dataN.Φ.map (Polynomial.aeval (R := ℤ) a₀).toRingHom, dataN.monic.map _, ?_⟩
      rw [Polynomial.eval₂_map, hcomp]
      exact hrel
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Qb)).mp hint
    rw [← hy]
    exact y.2
  refine ⟨⟨c, hcA⟩, ⟨cN, hcNA⟩, ?_, ?_⟩
  · exact ord_pos_of_mem N v (J_sub_ne_zero N c) _ hJc
  · exact ord_pos_of_mem N v (JN_sub_ne_zero N cN) _ hJNc

end TRI
p2m_reactivate "P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos.CharpS10bB.TRI"
end CharpS10bB
p2m_reactivate "P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos.CharpS10bB.TRI P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos.CharpS10bB"

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ) [NeZero N]
    (dataN : ModularCurve.ModularPolynomialData N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)) :
    (∀ a : A,
      v.ord
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ≤ 0) ∨
    ∃ a aN : A,
      0 < v.ord
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.modularFunctionField_le_full N (ModularCurve.jq_mem N))⟩
          - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)
              (a : AlgebraicClosure ℚ)) ∧
      0 < v.ord
        (⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ N ModularCurve.jq),
            ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.jqd_mem_full N (dvd_refl N))⟩
          - algebraMap (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)
              (aN : AlgebraicClosure ℚ)) :=
  CharpS10bB.TRI.dichotomy N A dataN v

end
p2m_reactivate "P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos.CharpS10bB.TRI P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos.CharpS10bB"

end S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos
end P2MW
export P2MW.S_ModularCurve_forall_ord_jBar_sub_le_zero_or_exists_ord_pos (solution)
