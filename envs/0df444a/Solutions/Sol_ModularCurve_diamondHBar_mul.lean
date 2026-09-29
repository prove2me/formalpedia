-- Prove2me | solution 1 for ModularCurve.diamondHBar_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b8adb0d9-91ea-5d6b-a0d8-b65fdb90ec51

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondHBar_mul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup ModularCurve
open scoped MatrixGroups ModularForm

namespace XHDiaMul

local notation "ΓHℝ(" M ", " H ")" =>
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simpa [coeffMap_coeff] using this

theorem ofPowerSeries_coeff_negSucc (p : PowerSeries R) (n : ℕ) :
    (ofPowerSeries ℤ R p).coeff (Int.negSucc n) = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  simp

theorem coeffMap_ofPowerSeries (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [coeffMap_coeff]
  cases k with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast]
      rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  | negSucc n =>
      rw [ofPowerSeries_coeff_negSucc, ofPowerSeries_coeff_negSucc, map_zero]

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = intSeriesC ℂ p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1

theorem intSeriesC_eq_zero_iff {K : Type*} [Field K] [CharZero K] (p : PowerSeries ℤ) :
    intSeriesC K p = 0 ↔ p = 0 := by
  constructor
  · intro h
    rw [intSeriesC] at h
    have h1 : p.map (Int.castRingHom K) = 0 :=
      ofPowerSeries_injective (h.trans (ofPowerSeries ℤ K).map_zero.symm)
    have h2 : p.map (Int.castRingHom K) = (0 : PowerSeries ℤ).map (Int.castRingHom K) := by
      rw [h1, (PowerSeries.map (Int.castRingHom K)).map_zero]
    exact PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective h2
  · rintro rfl
    exact intSeriesC_zero K

theorem intSeriesC_add {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem intSeriesC_C (K : Type*) [Field K] (z : ℤ) :
    intSeriesC K (PowerSeries.C z) = HahnSeries.C (z : K) := by
  rw [intSeriesC, PowerSeries.map_C, ofPowerSeries_C]
  simp

theorem intSeriesC_eq_of_isIntegralQExp {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) :
    intSeriesC ℂ p = ofPowerSeries ℤ ℂ (qExpansion 1 f) := by
  rw [intSeriesC]
  exact congrArg (ofPowerSeries ℤ ℂ) h

end Laurent

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem exists_gamma0 [NeZero M] (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨γ, γ.2, ?_⟩
  have : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = ((γ.1 0 0 : ℤ) : ZMod M) := rfl
  rw [← this, hγ, inv_inv]

private theorem _root_.XHDiaMul.conj_mem_GammaH {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ CohCarrier.GammaH M H) :
    γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H :=
  CohCarrier.conj_mem_GammaH M H (⟨γ, hγ⟩ : Gamma0 M) ⟨A, hA⟩

p2m_export "XHDiaMul" "conj_mem_GammaH"
open ConjAct Pointwise in

theorem gammaH_le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓHℝ(M, H) ≤ toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • ΓHℝ(M, H) := by
  intro x hx
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine Subgroup.mem_map.mpr ⟨γ * A * γ⁻¹, conj_mem_GammaH hγ hA, ?_⟩
  show Matrix.SpecialLinearGroup.mapGL ℝ (γ * A * γ⁻¹) =
    Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ A *
      (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem coeGL_mul (a b : SL(2, ℤ)) :
    ((a * b : SL(2, ℤ)) : GL (Fin 2) ℝ) = (a : GL (Fin 2) ℝ) * (b : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) a b

theorem entry_inv_mul {M : ℕ} {γ₁ γ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h : γ ∈ Gamma0 M)
    {a b : ZMod M} (ha : ((γ₁ 0 0 : ℤ) : ZMod M) = a) (hab : ((γ 0 0 : ℤ) : ZMod M) = a * b) :
    (((γ₁⁻¹ * γ) 0 0 : ℤ) : ZMod M) = b := by
  have hdet : (γ₁ 0 0 : ℤ) * γ₁ 1 1 - γ₁ 0 1 * γ₁ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ₁
    rwa [Matrix.det_fin_two] at this
  have hdet' : ((γ₁ 0 0 : ℤ) : ZMod M) * ((γ₁ 1 1 : ℤ) : ZMod M)
      - ((γ₁ 0 1 : ℤ) : ZMod M) * ((γ₁ 1 0 : ℤ) : ZMod M) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod M) hdet
  have hC : ((γ₁ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp h₁
  have hg : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp h
  have hentry : ((γ₁⁻¹ * γ) 0 0 : ℤ) = γ₁ 1 1 * γ 0 0 + (-γ₁ 0 1) * γ 1 0 := by
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hentry]
  push_cast
  linear_combination ((γ₁ 1 1 : ℤ) : ZMod M) * hab + (-((γ₁ 0 1 : ℤ) : ZMod M)) * hg
    + (-(b * ((γ₁ 1 1 : ℤ) : ZMod M))) * ha + b * hdet' + (b * ((γ₁ 0 1 : ℤ) : ZMod M)) * hC

end Group

section Forms

theorem one_mem_strictPeriods (M : ℕ) (H : Subgroup (ZMod M)ˣ) : (1 : ℝ) ∈ (ΓHℝ(M, H)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

open ConjAct Pointwise in

def conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ΓHℝ(M, H) k) :
    ModularForm ΓHℝ(M, H) k :=
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ΓHℝ(M, H) k) :
    (⇑(conjForm γ hγ f) : ℍ → ℂ) = (⇑f) ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

def slashQ (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) : LaurentSeries ℂ :=
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))

theorem slashQ_eq_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ΓHℝ(M, H) k) :
    slashQ k f γ = ofPowerSeries ℤ ℂ (qExpansion 1 (conjForm γ hγ f)) :=
  rfl

theorem qexp_mul {a b : ℤ} (F : ModularForm ΓHℝ(M, H) a) (G : ModularForm ΓHℝ(M, H) b) :
    qExpansion 1 (⇑F * ⇑G) = qExpansion 1 F * qExpansion 1 G :=
  ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M H) F G

theorem eq_of_qexp_eq {k : ℤ} {F G : ModularForm ΓHℝ(M, H) k}
    (h : qExpansion 1 (⇑F) = qExpansion 1 (⇑G)) : (⇑F : ℍ → ℂ) = ⇑G := by
  have h0 : F - G = 0 := by
    refine (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M H) (F - G)).mp ?_
    rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M H), h,
      sub_self]
  rw [sub_eq_zero.mp h0]

theorem ne_zero_of_isIntegralQExp {k : ℤ} {g : ModularForm ΓHℝ(M, H) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  apply hg0
  rw [intSeriesC_eq_zero_iff]
  have h1 : qExpansion 1 (⇑g) = 0 := by rw [h, ModularForm.coe_zero, qExpansion_zero]
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_zero]
  exact hg.trans h1

theorem conjForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm ΓHℝ(M, H) k}
    (hg : g ≠ 0) : conjForm γ hγ g ≠ 0 := by
  intro h
  apply hg
  have h1 : (⇑g : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by
    rw [← coe_conjForm γ hγ g, h, ModularForm.coe_zero]
  have h2 : (⇑g : ℍ → ℂ) = 0 := (SlashAction.slash_eq_zero_iff _ _ _).mp h1
  exact DFunLike.ext' (by rw [h2, ModularForm.coe_zero])

theorem slashQ_ne_zero {k : ℤ} {g : ModularForm ΓHℝ(M, H) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    slashQ k g γ ≠ 0 := by
  rw [slashQ_eq_conjForm γ hγ]
  refine (map_ne_zero_iff _ ofPowerSeries_injective).mpr ?_
  rw [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M H)]
  exact conjForm_ne_zero γ hγ (ne_zero_of_isIntegralQExp hg hg0)

theorem ofPowerSeries_qexp_ne_zero {k : ℤ} {g : ModularForm ΓHℝ(M, H) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g)) ≠ 0 := by
  rw [← intSeriesC_eq_of_isIntegralQExp hg, Ne, intSeriesC_eq_zero_iff]
  exact fun h => hg0 (by rw [h, intSeriesC_zero])

end Forms

section Ratios

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem mem_intFormRatiosC_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField M H) :
    y ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H) :=
  (mem_qExpFunctionFieldC_rat_iff_mem_intFormRatiosC (CohCarrier.GammaH M H) (one_mem_strictPeriods M H) y).mp hy

end Ratios

section Diamond

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

local notation "ℚbar" => AlgebraicClosure ℚ

def gen {k : ℤ} (f g : ModularForm ΓHℝ(M, H) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    xHFunctionFieldBar M H :=
  ⟨coeffEmb ℚbar (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange ℚbar (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

theorem isDiamondAutHBar_apply {d : (ZMod M)ˣ} {σ : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (h : IsDiamondAutHBar M H d σ) (k : ℤ) (f g : ModularForm ΓHℝ(M, H) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
      ((σ (gen f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y ∧
      coeffMap (algebraMap ℚ ℂ) y * slashQ k g γ = slashQ k f γ :=
  h k f g pf pg hf hg hg0 γ hγ hγd

theorem coeffEmb_injective : Function.Injective (coeffEmb ℚbar) :=
  coeffMap_injective (algebraMap ℚ ℚbar).injective

theorem algEquiv_ext_of_ratios {σ σ' : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H)),
      σ ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar (intFormRatiosC_subset ℚ _ hx)⟩ =
        σ' ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar (intFormRatiosC_subset ℚ _ hx)⟩) :
    σ = σ' := by

  have hF : ∀ (x : LaurentSeries ℚ) (hx : x ∈ xHFunctionField M H),
      σ ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ =
        σ' ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ := by
    intro x hxF
    have hx' : x ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hxF
    induction hx' using IntermediateField.adjoin_induction with
    | mem x hx => exact h x hx
    | algebraMap r =>

        have e : (⟨coeffEmb ℚbar (algebraMap ℚ (LaurentSeries ℚ) r),
            coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) = (r : xHFunctionFieldBar M H) := by
          apply Subtype.ext
          rw [SubfieldClass.coe_ratCast]
          show coeffEmb ℚbar (algebraMap ℚ (LaurentSeries ℚ) r) = _
          rw [eq_ratCast, map_ratCast]
        rw [e, map_ratCast, map_ratCast]
    | add x x' hx hx' ihx ihx' =>
        have e : (⟨coeffEmb ℚbar (x + x'), coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) =
            ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ +
              ⟨coeffEmb ℚbar x', coeffEmb_mem_laurentBaseChange ℚbar hx'⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add, map_add, ihx hx, ihx' hx']
    | inv x hx ihx =>
        have e : (⟨coeffEmb ℚbar x⁻¹, coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) = (⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩)⁻¹ :=
          Subtype.ext (map_inv₀ _ _)
        rw [e, map_inv₀, map_inv₀, ihx hx]
    | mul x x' hx hx' ihx ihx' =>
        have e : (⟨coeffEmb ℚbar (x * x'), coeffEmb_mem_laurentBaseChange ℚbar hxF⟩ :
            xHFunctionFieldBar M H) =
            ⟨coeffEmb ℚbar x, coeffEmb_mem_laurentBaseChange ℚbar hx⟩ *
              ⟨coeffEmb ℚbar x', coeffEmb_mem_laurentBaseChange ℚbar hx'⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [e, map_mul, map_mul, ihx hx, ihx' hx']

  apply AlgEquiv.ext
  rintro ⟨z, hz⟩
  have hz' : z ∈ IntermediateField.adjoin ℚbar
      (⇑(coeffEmb ℚbar) '' (xHFunctionField M H : Set (LaurentSeries ℚ))) := hz
  induction hz' using IntermediateField.adjoin_induction with
  | mem x hx =>
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      exact hF x₀ hx₀
  | algebraMap c =>
      have e : (⟨algebraMap ℚbar (LaurentSeries ℚbar) c, IntermediateField.algebraMap_mem _ c⟩ :
          xHFunctionFieldBar M H) = algebraMap ℚbar (xHFunctionFieldBar M H) c := rfl
      rw [e, AlgEquiv.commutes, AlgEquiv.commutes]
  | add x x' hx hx' ihx ihx' =>
      have e : (⟨x + x', add_mem hx hx'⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩ + ⟨x', hx'⟩ := rfl
      rw [e, map_add, map_add, ihx, ihx']
  | inv x hx ihx =>
      have e : (⟨x⁻¹, inv_mem hx⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩⁻¹ := rfl
      rw [e, map_inv₀, map_inv₀, ihx]
  | mul x x' hx hx' ihx ihx' =>
      have e : (⟨x * x', mul_mem hx hx'⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩ * ⟨x', hx'⟩ := rfl
      rw [e, map_mul, map_mul, ihx, ihx']

theorem isDiamondAutHBar_unique [NeZero M] {d : (ZMod M)ˣ}
    {σ σ' : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hσ' : IsDiamondAutHBar M H d σ') : σ = σ' := by
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0 d
  refine algEquiv_ext_of_ratios fun x hx => ?_
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  obtain ⟨y, -, hy, hyq⟩ := isDiamondAutHBar_apply hσ k f g pf pg hf hg hg0 γ hγ hγd
  obtain ⟨y', -, hy', hyq'⟩ := isDiamondAutHBar_apply hσ' k f g pf pg hf hg hg0 γ hγ hγd
  have hyy : y = y' := by
    apply coeffMap_injective (algebraMap ℚ ℂ).injective
    apply mul_right_cancel₀ (slashQ_ne_zero hg hg0 hγ)
    rw [hyq, hyq']
  apply Subtype.ext
  exact (hy.trans (by rw [hyy])).trans hy'.symm

theorem isDiamondAutHBar_trans [NeZero M] {d e : (ZMod M)ˣ}
    {σ τ : xHFunctionFieldBar M H ≃ₐ[ℚbar] xHFunctionFieldBar M H}
    (hσ : IsDiamondAutHBar M H d σ) (hτ : IsDiamondAutHBar M H e τ) :
    IsDiamondAutHBar M H (d * e) (σ.trans τ) := by
  intro k f g pf pg hf hg hg0 γ hγ hγde

  obtain ⟨γd, hγd, hγdd⟩ := exists_gamma0 d
  set γe : SL(2, ℤ) := γd⁻¹ * γ with hγe_def
  have hγe : γe ∈ Gamma0 M := (Gamma0 M).mul_mem ((Gamma0 M).inv_mem hγd) hγ
  have hγee : ((γe 0 0 : ℤ) : ZMod M) = (e : ZMod M) :=
    entry_inv_mul hγd hγ hγdd (by rw [hγde, Units.val_mul])
  have hγfac : (γd : GL (Fin 2) ℝ) * (γe : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) := by
    rw [← coeGL_mul, hγe_def, mul_inv_cancel_left]

  obtain ⟨y, hyF, hy, H1⟩ := isDiamondAutHBar_apply hσ k f g pf pg hf hg hg0 γd hγd hγdd
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', hyv⟩ := mem_intFormRatiosC_of_mem hyF
  have hgen : σ (gen f g hf hg hg0) = gen f' g' hf' hg' hg0' := by
    apply Subtype.ext
    rw [hy]
    show coeffEmb ℚbar y = coeffEmb ℚbar (intSeriesC ℚ pf' / intSeriesC ℚ pg')
    rw [hyv]
  obtain ⟨y'', hy''F, hy'', H2⟩ := isDiamondAutHBar_apply hτ k' f' g' pf' pg' hf' hg' hg0' γe hγe hγee
  refine ⟨y'', hy''F, ?_, ?_⟩
  · show ((τ (σ (gen f g hf hg hg0)) : xHFunctionFieldBar M H) : LaurentSeries ℚbar) = coeffEmb ℚbar y''
    rw [hgen, hy'']

  set Fd := conjForm γd hγd f
  set Gd := conjForm γd hγd g
  set F'e := conjForm γe hγe f'
  set G'e := conjForm γe hγe g'
  set Fγ := conjForm γ hγ f
  set Gγ := conjForm γ hγ g

  have hyC : coeffMap (algebraMap ℚ ℂ) y =
      ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f')) / ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g')) := by
    rw [hyv, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC, intSeriesC_eq_of_isIntegralQExp hf',
      intSeriesC_eq_of_isIntegralQExp hg']
  have hg'C := ofPowerSeries_qexp_ne_zero hg' hg0'
  rw [hyC, slashQ_eq_conjForm γd hγd, slashQ_eq_conjForm γd hγd,
    div_mul_eq_mul_div, div_eq_iff hg'C, ← map_mul, ← map_mul] at H1
  have H1' : qExpansion 1 (⇑f' * ⇑Gd) = qExpansion 1 (⇑g' * ⇑Fd) := by
    rw [qexp_mul, qexp_mul, mul_comm (qExpansion 1 (⇑g'))]
    exact ofPowerSeries_injective H1

  have E1 : (⇑f' : ℍ → ℂ) * ⇑Gd = ⇑g' * ⇑Fd := by
    have := eq_of_qexp_eq (F := f'.mul Gd) (G := g'.mul Fd)
      (by rw [ModularForm.coe_mul, ModularForm.coe_mul]; exact H1')
    rwa [ModularForm.coe_mul, ModularForm.coe_mul] at this
  have E2 : (⇑F'e : ℍ → ℂ) * ⇑Gγ = ⇑G'e * ⇑Fγ := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k' + k] γe) E1
    rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2] at this
    simp only [ModularForm.SL_slash] at this
    simp only [Fd, Gd, coe_conjForm, ← SlashAction.slash_mul, hγfac] at this
    simpa only [F'e, G'e, Fγ, Gγ, coe_conjForm] using this

  have E3 : slashQ k' f' γe * slashQ k g γ = slashQ k' g' γe * slashQ k f γ := by
    rw [slashQ_eq_conjForm γe hγe, slashQ_eq_conjForm γe hγe, slashQ_eq_conjForm γ hγ,
      slashQ_eq_conjForm γ hγ, ← map_mul, ← map_mul, ← qexp_mul, ← qexp_mul]
    exact congrArg _ (congrArg _ E2)

  show coeffMap (algebraMap ℚ ℂ) y'' * slashQ k g γ = slashQ k f γ
  apply mul_right_cancel₀ (slashQ_ne_zero hg' hg0' hγe)
  linear_combination (slashQ k g γ) * H2 + E3

theorem diamondAutHBar_mul [NeZero M] (d d' : (ZMod M)ˣ) :
    diamondAutHBar M H (d * d') = diamondAutHBar M H d * diamondAutHBar M H d' := by
  have hin := (heckeDiamondInputsHAll M H).2
  have h1 : IsDiamondAutHBar M H (d' * d) ((diamondAutHBar M H d').trans (diamondAutHBar M H d)) :=
    isDiamondAutHBar_trans (isDiamondAutHBar_diamondAutHBar (hin d')) (isDiamondAutHBar_diamondAutHBar (hin d))
  rw [mul_comm d' d] at h1
  exact isDiamondAutHBar_unique (isDiamondAutHBar_diamondAutHBar (hin (d * d'))) h1

end Diamond

end XHDiaMul
p2m_reactivate "P2MW.S_ModularCurve_diamondHBar_mul.XHDiaMul"

theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (d d' : (ZMod M)ˣ) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H (d * d') x =
      ModularCurve.diamondHBar M H d (ModularCurve.diamondHBar M H d' x) := by
  rw [ModularCurve.diamondHBar_apply, ModularCurve.diamondHBar_apply, ModularCurve.diamondHBar_apply,
    XHDiaMul.diamondAutHBar_mul, map_mul, mul_smul]

end
p2m_reactivate "P2MW.S_ModularCurve_diamondHBar_mul.XHDiaMul"

end S_ModularCurve_diamondHBar_mul
end P2MW
export P2MW.S_ModularCurve_diamondHBar_mul (solution)
