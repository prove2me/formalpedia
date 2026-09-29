-- Prove2me | solution 1 for ModularCurve.pic0Congr_jH_top_jZero_galois_hecke_diamond_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/be051adb-ce84-54c9-bb36-c8807fb6e52f

import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_pic0Congr_jH_top_jZero_galois_hecke_diamond_compat
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicCurve ModularCurve HahnSeries IntermediateField CongruenceSubgroup UpperHalfPlane

open scoped MatrixGroups ModularForm

namespace JZeroCoeSol

local notation "Qb" => AlgebraicClosure ℚ

example (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    JH M H = Pic0 Qb (laurentBaseChange Qb (xHFunctionField M H)) := rfl
example (M : ℕ) [NeZero M] :
    JZero M = Pic0 Qb (laurentBaseChange Qb (modularFunctionFieldFull M)) := rfl

section Fields

theorem gamma0_mul_le (M ℓ : ℕ) : Gamma0 (M * ℓ) ≤ Gamma0 M := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have h := map_intCast (ZMod.castHom (dvd_mul_right M ℓ) (ZMod M)) ((A 1 0 : ℤ))
  rw [← h, hA, map_zero]

theorem gamma0_inf_gamma0_mul (M ℓ : ℕ) : Gamma0 M ⊓ Gamma0 (M * ℓ) = Gamma0 (M * ℓ) :=
  le_antisymm inf_le_right (le_inf (gamma0_mul_le M ℓ) le_rfl)

variable (M : ℕ) [NeZero M]

theorem field_eq : xHFunctionField M ⊤ = modularFunctionFieldFull M :=
  (xHFunctionFieldC_top ℚ M).trans (qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull M)

theorem topField_eq (ℓ : ℕ) [NeZero ℓ] :
    xHTopFunctionFieldC ℚ M ⊤ (M * ℓ) = modularFunctionFieldFull (M * ℓ) := by
  rw [xHTopFunctionFieldC, CohCarrier.GammaH_top, gamma0_inf_gamma0_mul]
  exact qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull (M * ℓ)

end Fields

section Congr

theorem congrRingEquiv_refl {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (v : Place K F) :
    Place.congrRingEquiv (RingEquiv.refl F) he v = v := by
  ext1
  exact SetLike.ext fun x => Iff.rfl

theorem Divisor.congr_refl {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (D : Divisor K F) :
    Divisor.congr (RingEquiv.refl F) he D = D := by
  induction D using Finsupp.induction with
  | zero => exact map_zero _
  | single_add v n D _ _ ih =>
      rw [map_add, ih, Divisor.congr_single, congrRingEquiv_refl]

theorem Pic0.congr_refl_apply {K F : Type*} [Field K] [Field F] [Algebra K F]
    (he : ∀ a : K, (RingEquiv.refl F) (algebraMap K F a) = algebraMap K F a) (z : Pic0 K F) :
    Pic0.congr (RingEquiv.refl F) he z = z := by
  induction z using QuotientAddGroup.induction_on with
  | H D =>
      change (QuotientAddGroup.mk (Pic0.degZeroCongr (RingEquiv.refl F) he D) : Pic0 K F) =
        QuotientAddGroup.mk D
      exact congrArg _ (Subtype.ext (Divisor.congr_refl he (D : Divisor K F)))

theorem Pic0.congr_equivOfEq_heq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {F₀ F₁ : IntermediateField K E} (h : F₀ = F₁)
    (he : ∀ a : K, (IntermediateField.equivOfEq h).toRingEquiv (algebraMap K F₀ a) = algebraMap K F₁ a)
    (z : Pic0 K F₀) :
    HEq (Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv he z) z := by
  subst h
  have hr : (IntermediateField.equivOfEq (rfl : F₀ = F₀)).toRingEquiv = RingEquiv.refl F₀ := by
    ext x; rfl
  apply heq_of_eq
  revert he
  rw [hr]
  intro he
  exact Pic0.congr_refl_apply he z

theorem congr_apply_eq_of_heq {K E : Type*} [Field K] [Field E] [Algebra K E]
    {F₀ F₁ : IntermediateField K E} (h : F₀ = F₁) (e : Pic0 K F₀ ≃+ Pic0 K F₁)
    (he : ∀ z, HEq (e z) z) (T₀ : Pic0 K F₀ → Pic0 K F₀) (T₁ : Pic0 K F₁ → Pic0 K F₁)
    (hT : HEq T₀ T₁) (x : Pic0 K F₀) : e (T₀ x) = T₁ (e x) := by
  subst h
  cases hT
  have he' : ∀ z, e z = z := fun z => eq_of_heq (he z)
  rw [he', he']

end Congr

section Galois

theorem galois_smul_heq {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : F₀ = F₁)
    (σ : Qb ≃ₐ[ℚ] Qb) :
    HEq (fun z : Pic0 Qb (laurentBaseChange Qb F₀) => σ • z)
      (fun z : Pic0 Qb (laurentBaseChange Qb F₁) => σ • z) := by
  subst hF
  rfl

end Galois

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L]

def gAlpha (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (hle : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁) :
    laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₁ :=
  IntermediateField.inclusion hle

def gBeta (F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)) (ℓ : ℕ) [NeZero ℓ]
    (hmem : ∀ x : laurentBaseChange L F₀, qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L F₁) :
    laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₁ where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), hmem x⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)
  commutes' a := Subtype.ext <| by
    show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem gAlpha_heq {F₀ F₁ F₀' F₁' : IntermediateField ℚ (LaurentSeries ℚ)} (e₀ : F₀ = F₀') (e₁ : F₁ = F₁')
    (hle : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁) (hle' : laurentBaseChange L F₀' ≤ laurentBaseChange L F₁') :
    HEq (gAlpha L F₀ F₁ hle) (gAlpha L F₀' F₁' hle') := by
  subst e₀; subst e₁; rfl

theorem gBeta_heq {F₀ F₁ F₀' F₁' : IntermediateField ℚ (LaurentSeries ℚ)} (e₀ : F₀ = F₀') (e₁ : F₁ = F₁')
    (ℓ : ℕ) [NeZero ℓ]
    (hmem : ∀ x : laurentBaseChange L F₀, qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L F₁)
    (hmem' : ∀ x : laurentBaseChange L F₀', qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L F₁') :
    HEq (gBeta L F₀ F₁ ℓ hmem) (gBeta L F₀' F₁' ℓ hmem') := by
  subst e₀; subst e₁; rfl

theorem correspondence_heq {F₀ F₁ F₀' F₁' : IntermediateField ℚ (LaurentSeries ℚ)}
    (e₀ : F₀ = F₀') (e₁ : F₁ = F₁')
    (α β : laurentBaseChange L F₀ →ₐ[L] laurentBaseChange L F₁) (α' β' : laurentBaseChange L F₀' →ₐ[L] laurentBaseChange L F₁')
    (eα : HEq α α') (eβ : HEq β β')
    [i : HasPrincipalDivisors L (laurentBaseChange L F₁)] [i' : HasPrincipalDivisors L (laurentBaseChange L F₁')]
    (hβ : β.toRingHom.IsIntegral) (hα : α.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong L β hβ) (hfin : FiniteAlong L α)
    (hN : NormFormulaAlong L α hfin)
    (hβ' : β'.toRingHom.IsIntegral) (hα' : α'.toRingHom.IsIntegral)
    (hFI' : FundamentalIdentityAlong L β' hβ') (hfin' : FiniteAlong L α')
    (hN' : NormFormulaAlong L α' hfin') :
    HEq (⇑(Pic0.correspondence β α hβ hα hFI hfin hN))
      (⇑(Pic0.correspondence β' α' hβ' hα' hFI' hfin' hN')) := by
  subst e₀; subst e₁
  cases eα
  cases eβ
  rfl

variable (M : ℕ) [NeZero M] (ℓ : ℕ) [NeZero ℓ]

theorem heckeAlphaHBar_eq_g (H : Subgroup (ZMod M)ˣ)
    (hle : laurentBaseChange L (xHFunctionField M H) ≤ laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :
    heckeAlphaHBar L M H ℓ = gAlpha L _ _ hle := rfl

theorem heckeAlphaBar_eq_g
    (hle : laurentBaseChange L (modularFunctionFieldFull M) ≤ laurentBaseChange L (modularFunctionFieldFull (M * ℓ))) :
    heckeAlphaBar L M ℓ = gAlpha L _ _ hle := rfl

theorem heckeBetaHBar_eq_g (H : Subgroup (ZMod M)ˣ) (h0 : HeckeBetaHDefined M H ℓ)
    (hmem : ∀ x : laurentBaseChange L (xHFunctionField M H),
      qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :
    heckeBetaHBar L M H ℓ = gBeta L _ _ ℓ hmem := by
  rw [heckeBetaHBar_eq M H ℓ h0]
  rfl

theorem heckeBetaBar_eq_g
    (hmem : ∀ x : laurentBaseChange L (modularFunctionFieldFull M),
      qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L (modularFunctionFieldFull (M * ℓ))) :
    heckeBetaBar L M ℓ = gBeta L _ _ ℓ hmem := rfl

theorem heckeAlpha_heq : HEq (heckeAlphaHBar L M ⊤ ℓ) (heckeAlphaBar L M ℓ) := by
  have hle : laurentBaseChange L (xHFunctionField M ⊤) ≤ laurentBaseChange L (xHTopFunctionFieldC ℚ M ⊤ (M * ℓ)) :=
    fun x hx => by simpa using (heckeAlphaHBar L M ⊤ ℓ ⟨x, hx⟩).2
  have hle' : laurentBaseChange L (modularFunctionFieldFull M) ≤ laurentBaseChange L (modularFunctionFieldFull (M * ℓ)) :=
    fun x hx => by simpa using (heckeAlphaBar L M ℓ ⟨x, hx⟩).2
  rw [heckeAlphaHBar_eq_g L M ℓ ⊤ hle, heckeAlphaBar_eq_g L M ℓ hle']
  exact gAlpha_heq L (field_eq M) (topField_eq M ℓ) hle hle'

theorem heckeBeta_heq (h0 : HeckeBetaHDefined M ⊤ ℓ) :
    HEq (heckeBetaHBar L M ⊤ ℓ) (heckeBetaBar L M ℓ) := by
  have hmem : ∀ x : laurentBaseChange L (xHFunctionField M ⊤),
      qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L (xHTopFunctionFieldC ℚ M ⊤ (M * ℓ)) :=
    fun x => (heckeBetaHBarOf L M ⊤ ℓ h0 x).2
  have hmem' : ∀ x : laurentBaseChange L (modularFunctionFieldFull M),
      qExpand L ℓ (x : LaurentSeries L) ∈ laurentBaseChange L (modularFunctionFieldFull (M * ℓ)) :=
    fun x => (heckeBetaBar L M ℓ x).2
  rw [heckeBetaHBar_eq_g L M ℓ ⊤ h0 hmem, heckeBetaBar_eq_g L M ℓ hmem']
  exact gBeta_heq L (field_eq M) (topField_eq M ℓ) ℓ hmem hmem'

theorem heckeOperator_heq (hinH : HeckeInputsHAlong L M ⊤ ℓ) (hin0 : HeckeInputsAlong L M ℓ) :
    HEq (⇑(heckeOperatorHAlong L M ⊤ ℓ)) (⇑(heckeOperatorAlong L M ℓ)) := by
  obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := hinH
  obtain ⟨hα', hβ', hP', hfin', hFI', hN'⟩ := hin0
  rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, heckeOperatorAlong_eq hα' hβ' hFI' hfin' hN']
  exact correspondence_heq L (field_eq M) (topField_eq M ℓ)
    (heckeAlphaHBar L M ⊤ ℓ) (heckeBetaHBar L M ⊤ ℓ) (heckeAlphaBar L M ℓ) (heckeBetaBar L M ℓ)
    (heckeAlpha_heq L M ℓ) (heckeBeta_heq L M ℓ h0) (i := hP) (i' := hP')
    hβ hα hFI hfin hN hβ' hα' hFI' hfin' hN'

end Hecke

section Diamond

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC :=
  RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffEmb_algebraMap (c : ℚ) :
    coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap Qb (LaurentSeries Qb) (algebraMap ℚ Qb c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]

variable {M : ℕ} [NeZero M]

theorem eq_refl_of_isDiamondAutHBar_top (d : (ZMod M)ˣ)
    (σ : xHFunctionFieldBar M ⊤ ≃ₐ[Qb] xHFunctionFieldBar M ⊤) (hσ : IsDiamondAutHBar M ⊤ d σ) :
    σ = AlgEquiv.refl := by

  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have hγ : (γd : SL(2, ℤ)) ∈ Gamma0 M := γd.2
  have hγ00 : (((γd : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h1 : (CohCarrier.gamma0Units M γd)⁻¹ = d := by rw [hγd, inv_inv]
    have h2 : ((CohCarrier.gamma0Units M γd)⁻¹ : (ZMod M)ˣ).val = (d : ZMod M) := by rw [h1]
    exact h2
  have hγH : (γd : SL(2, ℤ)) ∈ CohCarrier.GammaH M ⊤ := by
    rw [CohCarrier.GammaH_top]; exact hγ
  have hγGL : ((γd : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈
      ((CohCarrier.GammaH M ⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hγH
  set F₀ := xHFunctionField M ⊤ with hF₀

  have hφ : ∀ (x : LaurentSeries ℚ) (hx : x ∈ F₀) (hm : coeffEmb Qb x ∈ xHFunctionFieldBar M ⊤),
      σ ⟨coeffEmb Qb x, hm⟩ = ⟨coeffEmb Qb x, hm⟩ := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
        intro hm
        obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
        obtain ⟨w, hw, hσw, hwslash⟩ := hσ k f g pf pg hf hg hg0 γd hγ hγ00
        have hfγ : (⇑f ∣[k] ((γd : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑f :=
          SlashInvariantForm.slash_action_eqn f _ hγGL
        have hgγ : (⇑g ∣[k] ((γd : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑g :=
          SlashInvariantForm.slash_action_eqn g _ hγGL
        rw [hfγ, hgγ] at hwslash
        change ιC w * qC g = qC f at hwslash
        rw [← ιC_intSeriesC hf, ← ιC_intSeriesC hg] at hwslash
        have hQ : ιC (intSeriesC ℚ pg) ≠ 0 := (map_ne_zero_iff _ ιC_injective).mpr hg0
        have hw' : w = intSeriesC ℚ pf / intSeriesC ℚ pg := by
          apply ιC_injective
          rw [map_div₀, eq_div_iff hQ, hwslash]
        exact Subtype.ext (hσw.trans (by rw [hw']))
    | algebraMap c =>
        intro hm
        have e1 : (⟨coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c), hm⟩ : xHFunctionFieldBar M ⊤) =
            algebraMap Qb (xHFunctionFieldBar M ⊤) (algebraMap ℚ Qb c) :=
          Subtype.ext (coeffEmb_algebraMap c)
        rw [e1, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
        intro hm
        have e1 : (⟨coeffEmb Qb (x + y), hm⟩ : xHFunctionFieldBar M ⊤) =
            ⟨coeffEmb Qb x, coeffEmb_mem_laurentBaseChange Qb hx⟩ +
              ⟨coeffEmb Qb y, coeffEmb_mem_laurentBaseChange Qb hy⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e1, map_add, ihx, ihy]
    | inv x hx ih =>
        intro hm
        have e1 : (⟨coeffEmb Qb x⁻¹, hm⟩ : xHFunctionFieldBar M ⊤) =
            ⟨coeffEmb Qb x, coeffEmb_mem_laurentBaseChange Qb hx⟩⁻¹ :=
          Subtype.ext (map_inv₀ _ _)
        rw [e1, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        intro hm
        have e1 : (⟨coeffEmb Qb (x * y), hm⟩ : xHFunctionFieldBar M ⊤) =
            ⟨coeffEmb Qb x, coeffEmb_mem_laurentBaseChange Qb hx⟩ *
              ⟨coeffEmb Qb y, coeffEmb_mem_laurentBaseChange Qb hy⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [e1, map_mul, ihx, ihy]

  apply AlgEquiv.ext
  intro z
  obtain ⟨z, hz⟩ := z
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact hφ y hy _
  | algebraMap c =>
      have : (⟨algebraMap Qb (LaurentSeries Qb) c, IntermediateField.algebraMap_mem _ c⟩ :
          xHFunctionFieldBar M ⊤) = algebraMap Qb (xHFunctionFieldBar M ⊤) c := rfl
      rw [this, AlgEquiv.commutes]
      rfl
  | add x y hx hy ihx ihy =>
      show σ (⟨x, hx⟩ + ⟨y, hy⟩) = AlgEquiv.refl (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show σ (⟨x, hx⟩⁻¹) = AlgEquiv.refl (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show σ (⟨x, hx⟩ * ⟨y, hy⟩) = AlgEquiv.refl (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

theorem diamondAutHBar_top (d : (ZMod M)ˣ) : diamondAutHBar M ⊤ d = AlgEquiv.refl := by
  rcases Classical.em (∃ σ : xHFunctionFieldBar M ⊤ ≃ₐ[Qb] xHFunctionFieldBar M ⊤, IsDiamondAutHBar M ⊤ d σ)
    with h | h
  · exact eq_refl_of_isDiamondAutHBar_top d _ (isDiamondAutHBar_diamondAutHBar h)
  · exact diamondAutHBar_of_not h

theorem diamondHBar_top_apply (d : (ZMod M)ˣ) (x : JH M ⊤) : diamondHBar M ⊤ d x = x := by
  rw [diamondHBar_apply, diamondAutHBar_top]
  have : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : xHFunctionFieldBar M ⊤ ≃ₐ[Qb] xHFunctionFieldBar M ⊤) = 1 :=
    map_one _
  rw [this, one_smul]

end Diamond

end JZeroCoeSol

namespace JZeroCoeSol

variable (M : ℕ) [NeZero M] (hF : xHFunctionFieldBar M ⊤ = modularFunctionFieldBar M)
  (e : JH M ⊤ ≃+ JZero M)
  (he : ∀ x : JH M ⊤,
    e x = AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq hF).toRingEquiv
      (fun a => (IntermediateField.equivOfEq hF).commutes a) x)

include he in

theorem e_heq (z : JH M ⊤) : HEq (e z) z :=
  (heq_of_eq (he z)).trans (Pic0.congr_equivOfEq_heq hF _ z)

include he in
theorem galois_conj (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M ⊤) :
    e (σ • x) = σ • e x :=
  congr_apply_eq_of_heq hF e (e_heq M hF e he) (fun z : JH M ⊤ => σ • z) (fun w : JZero M => σ • w)
    (galois_smul_heq (field_eq M) σ) x

include he in
theorem hecke_conj (hinH : HeckeDiamondInputsHAll M ⊤)
    (hin0 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      HeckeInputsAlong (AlgebraicClosure ℚ) M ℓ)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : JH M ⊤) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    e (heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊤ ℓ x) =
      heckeOperatorAlong (AlgebraicClosure ℚ) M ℓ (e x) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  exact congr_apply_eq_of_heq hF e (e_heq M hF e he)
    (fun z : JH M ⊤ => heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊤ ℓ z)
    (fun w : JZero M => heckeOperatorAlong (AlgebraicClosure ℚ) M ℓ w)
    (heckeOperator_heq (AlgebraicClosure ℚ) M ℓ (hinH.heckeInputsHAlong ℓ hℓ) (hin0 ℓ hℓ)) x

theorem diamond_conj (d : (ZMod M)ˣ) (x : JH M ⊤) : e (diamondHBar M ⊤ d x) = e x := by
  rw [diamondHBar_top_apply]

end JZeroCoeSol

open JZeroCoeSol in
open ModularCurve in
theorem solution (M : ℕ) [NeZero M]
    (hinH : HeckeDiamondInputsHAll M ⊤)
    (hin0 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      HeckeInputsAlong (AlgebraicClosure ℚ) M ℓ)
    (hF : xHFunctionFieldBar M ⊤ = modularFunctionFieldBar M)
    (e : JH M ⊤ ≃+ JZero M)
    (he : ∀ x : JH M ⊤,
      e x = AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq hF).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hF).commutes a) x) :
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M ⊤), e (σ • x) = σ • e x) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x : JH M ⊤),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      e (heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊤ ℓ x) = heckeOperatorAlong (AlgebraicClosure ℚ) M ℓ (e x)) ∧
    (∀ (d : (ZMod M)ˣ) (x : JH M ⊤), e (diamondHBar M ⊤ d x) = e x) :=
  ⟨galois_conj M hF e he, hecke_conj M hF e he hinH hin0, diamond_conj M e⟩

end
end S_ModularCurve_pic0Congr_jH_top_jZero_galois_hecke_diamond_compat
end P2MW
export P2MW.S_ModularCurve_pic0Congr_jH_top_jZero_galois_hecke_diamond_compat (solution)
