-- Prove2me | solution 1 for ModularCurve.algEquiv_eq_refl_of_forall_coe_eq_infSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/71af82d2-1a5c-5bd2-a04b-0861fdccfb63

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_eq_qExpand_jqModC_of_isRoot_map_modularPolynomial
import Theorems.Thm_ModularCurve_xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_laurentBaseChange_qExpFunctionFieldC_eq
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_algEquiv_eq_refl_of_forall_coe_eq_infSubgroup
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open ModularCurve Polynomial

theorem DECK.hom_eval₂_eval₂ {A B : Type*} [CommRing A] [CommRing B] (Φ : Polynomial (Polynomial ℤ))
    (g : A →+* B) (a b : A) :
    g (Φ.eval₂ (eval₂RingHom (Int.castRingHom A) a) b) =
      Φ.eval₂ (eval₂RingHom (Int.castRingHom B) (g a)) (g b) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  apply RingHom.ext
  intro q
  rw [RingHom.comp_apply, coe_eval₂RingHom, coe_eval₂RingHom, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (τ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hτ : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
      ((τ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ))) :
    τ = AlgEquiv.refl := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpM) (Fact.out : p.Prime).pos).ne'⟩

  have hgen := ModularCurve.xHFunctionFieldBar_div_sup_adjoin_qExpand_jqModC_eq_xHFunctionFieldBar p M H hpM hpM2 hHp
  have hF'le : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H := le_sup_left.trans hgen.le

  have hjF' : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    have h1 : jqModC (AlgebraicClosure ℚ) ∈
        qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) :=
      qExpFunctionFieldC_mono (AlgebraicClosure ℚ) (CohCarrier.GammaH_le_Gamma0 _)
        (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (AlgebraicClosure ℚ) (M / p)
          (jqModC_mem_full (AlgebraicClosure ℚ) (M / p)))
    have e : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) = qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)) :=
      ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) _
    rw [e]; exact h1
  have hyF : qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar M H :=
    hgen.le ((le_sup_right : _ ≤ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ⊔ _) (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)))
  let jb : xHFunctionFieldBar M H := ⟨jqModC (AlgebraicClosure ℚ), hF'le hjF'⟩
  let y : xHFunctionFieldBar M H := ⟨qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)), hyF⟩

  have hfix : ∀ z : xHFunctionFieldBar M H, (z : LaurentSeries (AlgebraicClosure ℚ)) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) → τ z = z := by
    intro z hz
    apply Subtype.ext
    exact hτ z ⟨z, hz⟩ rfl
  have hτj : τ jb = jb := hfix jb hjF'

  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  have h0LS : data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)))
      (qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) = 0 := by
    have h1 := ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero data (AlgebraicClosure ℚ) 1
    have e1 : jqNModC (AlgebraicClosure ℚ) 1 = jqModC (AlgebraicClosure ℚ) := qExpand_one_apply _
    have e2 : jqNModC (AlgebraicClosure ℚ) (1 * p) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) :=
      qExpand_congr (one_mul p) _
    rw [e1, e2] at h1
    have e3 : (eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ))) =
        (Polynomial.aeval (R := ℤ) (jqModC (AlgebraicClosure ℚ))).toRingHom := by
      apply RingHom.ext; intro q
      rw [coe_eval₂RingHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_def,
        RingHom.ext_int (algebraMap ℤ (LaurentSeries (AlgebraicClosure ℚ))) (Int.castRingHom _)]
    rw [e3]; exact h1
  have h0F : data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (xHFunctionFieldBar M H)) jb) y = 0 := by
    apply (algebraMap (xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [DECK.hom_eval₂_eval₂, map_zero]
    exact h0LS
  have hτroot : data.Φ.eval₂ (eval₂RingHom (Int.castRingHom (xHFunctionFieldBar M H)) jb) (τ y) = 0 := by
    have h := DECK.hom_eval₂_eval₂ data.Φ (τ : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H) jb y
    rw [h0F, map_zero] at h
    have h' : ((τ : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H) jb) = jb := hτj
    rw [h'] at h
    exact h.symm
  have hτy : τ y = y := by
    apply Subtype.ext
    have hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)))).IsRoot
        ((τ y : xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [Polynomial.IsRoot, Polynomial.eval_map]
      have h := DECK.hom_eval₂_eval₂ data.Φ (algebraMap (xHFunctionFieldBar M H) (LaurentSeries (AlgebraicClosure ℚ))) jb (τ y)
      rw [hτroot, map_zero] at h
      exact h.symm
    exact ModularCurve.eq_qExpand_jqModC_of_isRoot_map_modularPolynomial (AlgebraicClosure ℚ) p data _ hroot

  let G : Subgroup (xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H) := Subgroup.zpowers τ
  have hmemG : ∀ z : xHFunctionFieldBar M H, τ z = z → z ∈ IntermediateField.fixedField G := by
    intro z hz
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    clear hf
    have hz' : τ.symm z = z := by
      conv_lhs => rw [← hz]
      exact τ.symm_apply_apply z
    induction k using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, AlgEquiv.mul_apply, hz, ih]
    | pred n ih => rw [zpow_sub_one, AlgEquiv.mul_apply, AlgEquiv.aut_inv, hz', ih]
  have hle : xHFunctionFieldBar M H ≤ IntermediateField.lift (IntermediateField.fixedField G) := by
    conv_lhs => rw [← hgen]
    refine sup_le ?_ ?_
    · intro x hx
      exact (IntermediateField.mem_lift (⟨x, hF'le hx⟩ : xHFunctionFieldBar M H)).mpr (hmemG _ (hfix _ hx))
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact (IntermediateField.mem_lift y).mpr (hmemG _ hτy)

  apply AlgEquiv.ext
  intro z
  have hz : z ∈ IntermediateField.fixedField G := (IntermediateField.mem_lift z).mp (hle z.2)
  exact (IntermediateField.mem_fixedField_iff G z).mp hz τ (Subgroup.mem_zpowers τ)

end S_ModularCurve_algEquiv_eq_refl_of_forall_coe_eq_infSubgroup
end P2MW
export P2MW.S_ModularCurve_algEquiv_eq_refl_of_forall_coe_eq_infSubgroup (solution)
