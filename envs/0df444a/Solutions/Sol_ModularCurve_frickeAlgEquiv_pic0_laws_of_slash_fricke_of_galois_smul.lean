-- Prove2me | solution 1 for ModularCurve.frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0f7ddbdc-8de7-5488-936d-c32849c433de

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CohCarrier_Fricke
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_swap_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

noncomputable section

namespace A2FRHG

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries AlgebraicCurve

open scoped MatrixGroups ModularForm Pointwise

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (ΓGL Γ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

variable (M) in

def frickeGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_frickeGL [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL [NeZero M] : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem det_frickeGL_pos [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

theorem eq_frickeGL [NeZero M] {W : GL (Fin 2) ℝ}
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) : W = frickeGL M :=
  Units.ext (by rw [hW]; rfl)

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

theorem frickeGL_mul_mul_inv [NeZero M] (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) :
    frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ * (frickeGL M)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h) := by
  rw [mul_inv_eq_iff_eq_mul, mapGL_eq_coe, mapGL_eq_coe]
  ext i j
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 / M : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne M)]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, CohCarrier.frickeMat, hc]; try ring)

theorem le_conj_frickeGL [NeZero M] :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct (frickeGL M)⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have h10 := CohCarrier.N_dvd_of_mem_GammaH M H ⟨δ, hδ⟩
  exact ⟨CohCarrier.frickeMat M δ h10, CohCarrier.frickeMat_mem M H ⟨δ, hδ⟩,
    (frickeGL_mul_mul_inv δ h10).symm⟩

def frickeForm [NeZero M] {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm le_conj_frickeGL (ModularForm.translate f (frickeGL M))

@[scoped simp]
theorem coe_frickeForm [NeZero M] {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(frickeForm f) = ⇑f ∣[k] frickeGL M := rfl

def scalarGL (a : ℝ) (ha : a ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a]
    (by rw [Matrix.det_fin_two_of]; simpa using ha)

@[scoped simp]
theorem val_scalarGL (a : ℝ) (ha : a ≠ 0) :
    ((scalarGL a ha : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, a] := rfl

theorem det_scalarGL (a : ℝ) (ha : a ≠ 0) : ((scalarGL a ha).det : ℝ) = a * a := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL, Matrix.det_fin_two_of]; ring

theorem scalarGL_smul (a : ℝ) (ha : a ≠ 0) (τ : ℍ) : scalarGL a ha • τ = τ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hdet]
  simp only [num, denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  rw [mul_div_assoc, mul_div_cancel₀ _ (by exact_mod_cast ha)]

theorem slash_scalarGL (k : ℤ) (a : ℝ) (ha : a ≠ 0) (φ : ℍ → ℂ) :
    φ ∣[k] scalarGL a ha = (fun _ => ((|a * a| : ℝ) : ℂ) ^ (k - 1) * (a : ℂ) ^ (-k)) * φ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  funext τ
  rw [ModularForm.slash_apply, scalarGL_smul, Pi.mul_apply]
  have hσ : σ (scalarGL a ha) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_scalarGL]
  simp only [denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

theorem frickeGL_mul_frickeGL [NeZero M] :
    frickeGL M * frickeGL M = scalarGL (-(M : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast NeZero.ne M)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def frickeSqConst (M : ℕ) (k : ℤ) : ℂ :=
  ((|(-(M : ℝ)) * (-(M : ℝ))| : ℝ) : ℂ) ^ (k - 1) * ((-(M : ℝ) : ℝ) : ℂ) ^ (-k)

theorem frickeSqConst_ne_zero [NeZero M] (k : ℤ) : frickeSqConst M k ≠ 0 := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
  · exact_mod_cast (abs_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hM) (neg_ne_zero.mpr hM)))
  · exact_mod_cast neg_ne_zero.mpr hM

theorem slash_frickeGL_frickeGL [NeZero M] (k : ℤ) (φ : ℍ → ℂ) :
    (φ ∣[k] frickeGL M) ∣[k] frickeGL M = (fun _ => frickeSqConst M k) * φ := by
  rw [← SlashAction.slash_mul, frickeGL_mul_frickeGL, slash_scalarGL]
  rfl

end Groups

section GroupIdentity

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

def liftSub : Subgroup (ZMod (M * ℓ))ˣ :=
  H.comap (ZMod.unitsMap (Dvd.intro ℓ rfl : M ∣ M * ℓ))

theorem gammaH_inf_gamma0_eq :
    CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) = CohCarrier.GammaH (M * ℓ) (liftSub M H ℓ) := by
  ext A
  simp only [Subgroup.mem_inf, CohCarrier.mem_GammaH_iff, liftSub, Subgroup.mem_comap]
  have hdvd : M ∣ M * ℓ := Dvd.intro ℓ rfl
  have key : ∀ (hA : A ∈ Gamma0 (M * ℓ)) (hA' : A ∈ Gamma0 M),
      ZMod.unitsMap hdvd (CohCarrier.gamma0Units (M * ℓ) ⟨A, hA⟩) =
        CohCarrier.gamma0Units M ⟨A, hA'⟩ := fun hA hA' => by
    ext
    rw [ZMod.unitsMap_val]
    change ZMod.cast (((A 1 1 : ℤ) : ZMod (M * ℓ))) = ((A 1 1 : ℤ) : ZMod M)
    rw [ZMod.cast_intCast hdvd]
  have h0 : ∀ hA : A ∈ Gamma0 (M * ℓ), A ∈ Gamma0 M := fun hA => by
    rw [Gamma0_mem] at hA ⊢
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((Int.natCast_dvd_natCast.mpr hdvd).trans h)
  constructor
  · rintro ⟨⟨hA0, hH⟩, hAℓ⟩
    exact ⟨hAℓ, by rwa [key hAℓ hA0]⟩
  · rintro ⟨hAℓ, hH⟩
    exact ⟨⟨h0 hAℓ, by rwa [key hAℓ (h0 hAℓ)] at hH⟩, hAℓ⟩

end GroupIdentity

section QExp

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

include hT

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (ΓGL Γ) k₁) (g : ModularForm (ΓGL Γ) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods_of_T_mem hT)]

theorem qC_add {k : ℤ} (f g : ModularForm (ΓGL Γ) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_of_T_mem hT) f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT) c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods_of_T_mem hT) f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem hT) f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

omit hT in
theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

omit hT in
theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit hT in

theorem coe_smul_form {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) : ⇑(c • f) = c • ⇑f :=
  FunLike.coe_smul c f

theorem qC_const_mul {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    qC ((fun _ => c) * ⇑f) = HahnSeries.C c * qC f := by
  rw [show ((fun _ => c) * ⇑f : ℍ → ℂ) = c • ⇑f from rfl, qC_smul hT]

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (ΓGL Γ) k₁)
    (f₂ : ModularForm (ΓGL Γ) k₂) (f₃ : ModularForm (ΓGL Γ) k₃) (f₄ : ModularForm (ΓGL Γ) k₄)
    (hk : k₃ + k₄ = k₁ + k₂) (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) :
    (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (ΓGL Γ) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_of_T_mem hT)
      (f₁.mul f₂) (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul hT, qC_mul hT, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff hT D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

omit hT in
theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

omit hT in
theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

theorem mul_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem hT
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem hT
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
    ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos h1, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul,
      div_add_div _ _ hg₁0 hg₂0]

theorem neg_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    -a ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods_of_T_mem hT) f).symm
  · rw [intSeriesC_neg', neg_div]

omit hT in
theorem inv_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · exact ⟨k, g, f, pg, pf, hg, hf, hf0, by rw [inv_div]⟩

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) : ModularForm (ΓGL Γ) 0) : ℍ → ℂ)
      (PowerSeries.C n) := by
  have hc : ((ModularForm.const (n : ℂ) : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) =
      (n : ℂ) • ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [IsIntegralQExp, PowerSeries.map_C, hc,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT),
    ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_ratios (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const hT _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const (Γ := Γ) hT (c.den : ℤ)
    push_cast at this
    exact this
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

def ratioField : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := intFormRatiosC ℚ Γ
  mul_mem' ha hb := mul_mem_ratios hT ha hb
  one_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 1
  add_mem' ha hb := add_mem_ratios hT ha hb
  zero_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 0
  algebraMap_mem' c := algebraMap_mem_ratios hT c
  inv_mem' a ha := inv_mem_ratios ha

theorem mem_ratios_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) :
    y ∈ intFormRatiosC ℚ Γ := by
  have hle : qExpFunctionFieldC ℚ Γ ≤ ratioField (Γ := Γ) hT :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end QExp

section Coeff

local notation "Qb" => AlgebraicClosure ℚ

variable (ι : Qb →+* ℂ)

theorem coeffMap_injective : Function.Injective (coeffMap ι) := fun x y h => by
  ext k
  exact ι.injective (by simpa using congrArg (fun z => z.coeff k) h)

theorem coeffMap_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb Qb y) = coeffMap (algebraMap ℚ ℂ) y := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

omit ι in
theorem coeffMap_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffMap_coeffEmb_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap ι (coeffEmb Qb (intSeriesC ℚ p)) = qC F := by
  rw [coeffMap_coeffEmb, coeffMap_intSeriesC h]

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    coeffMap f (HahnSeries.C c) = HahnSeries.C (f c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem ofPowerSeries_eq_qExpand {ℓ : ℕ} [NeZero ℓ] (p p' : PowerSeries ℂ)
    (h : ∀ n, PowerSeries.coeff n p' = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0) :
    ofPowerSeries ℤ ℂ p' = qExpand ℂ ℓ (ofPowerSeries ℤ ℂ p) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity), h]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qC_comp_heckeDiag {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (F : ModularForm (ΓGL Γ) k) (ℓ : ℕ) [NeZero ℓ] :
    qC (fun τ => F (ModularForm.heckeDiagMatrix ℓ • τ)) = qExpand ℂ ℓ (qC F) :=
  ofPowerSeries_eq_qExpand _ _ fun n =>
    ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_of_T_mem hT)
      (NeZero.ne ℓ) n

end Coeff

section LevelMatrices

variable {M : ℕ} [NeZero M] {ℓ : ℕ} [NeZero ℓ]

scoped instance : NeZero (M * ℓ) := ⟨Nat.mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩

theorem frickeGL_mul_heckeDiag :
    frickeGL M * ModularForm.heckeDiagMatrix ℓ = frickeGL (M * ℓ) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ),
    val_frickeGL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeDiag_mul_frickeGL :
    ModularForm.heckeDiagMatrix ℓ * frickeGL (M * ℓ) =
      frickeGL M * scalarGL (ℓ : ℝ) (by exact_mod_cast NeZero.ne ℓ) := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne ℓ),
    val_frickeGL, val_scalarGL]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)

theorem slash_frickeGL_mul (k : ℤ) (φ : ℍ → ℂ) :
    φ ∣[k] frickeGL (M * ℓ) =
      (fun _ => ((ℓ : ℂ) ^ (k - 1))) * fun τ => (φ ∣[k] frickeGL M) (ModularForm.heckeDiagMatrix ℓ • τ) := by
  rw [← frickeGL_mul_heckeDiag, SlashAction.slash_mul]
  funext τ
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ)]
  rfl

end LevelMatrices

section Spec

local notation "Qb" => AlgebraicClosure ℚ

abbrev LBC (Γ : Subgroup SL(2, ℤ)) : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (qExpFunctionFieldC ℚ Γ)

def FrickeSpec (Γ : Subgroup SL(2, ℤ)) (W : GL (Fin 2) ℝ) (ι : Qb →+* ℂ) (w : LBC Γ → LBC Γ) :
    Prop :=
  ∀ (x : LBC Γ) (k : ℤ) (f g : ModularForm (ΓGL Γ) k),
    coeffMap ι (x : LaurentSeries Qb) * qC g = qC f →
      coeffMap ι ((w x : LBC Γ) : LaurentSeries Qb) * qC (⇑g ∣[k] W) = qC (⇑f ∣[k] W)

variable {Γ : Subgroup SL(2, ℤ)}

def gen {k : ℤ} (f g : ModularForm (ΓGL Γ) k) {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : LBC Γ :=
  ⟨coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange Qb (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩

@[scoped simp]
theorem coe_gen {k : ℤ} (f g : ModularForm (ΓGL Γ) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ((gen f g hf hg hg0 : LBC Γ) : LaurentSeries Qb) = coeffEmb Qb (intSeriesC ℚ pf / intSeriesC ℚ pg) :=
  rfl

theorem qC_ne_zero_of_witness {k : ℤ} {g : ModularForm (ΓGL Γ) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← coeffMap_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem gen_rep (ι : Qb →+* ℂ) {k : ℤ} (f g : ModularForm (ΓGL Γ) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffMap ι ((gen f g hf hg hg0 : LBC Γ) : LaurentSeries Qb) * qC g = qC f := by
  rw [coe_gen, map_div₀, map_div₀, coeffMap_coeffEmb_intSeriesC ι hf,
    coeffMap_coeffEmb_intSeriesC ι hg, div_mul_cancel₀ _ (qC_ne_zero_of_witness hg hg0)]

theorem algHom_ext_gen (hT : ModularGroup.T ∈ Γ) {E : Type*} [Semiring E] [Algebra Qb E]
    {φ₁ φ₂ : LBC Γ →ₐ[Qb] E}
    (h : ∀ (k : ℤ) (f g : ModularForm (ΓGL Γ) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      φ₁ (gen f g hf hg hg0) = φ₂ (gen f g hf hg hg0)) : φ₁ = φ₂ := by
  refine IntermediateField.algHom_ext_of_eq_adjoin Qb (S := LBC Γ)
    (s := ⇑(coeffEmb Qb) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT hy
  exact h k f g pf pg hf hg hg0

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem apply_apply_of_frickeSpec (ι : Qb →+* ℂ) {w : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (x : LBC (CohCarrier.GammaH M H)) :
    w (w x) = x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  suffices h : (w.trans w).toAlgHom = AlgHom.id Qb _ from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => ?_
  change w (w (gen f g hf hg hg0)) = gen f g hf hg hg0
  set x₀ := gen f g hf hg hg0 with hx₀
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0
  have h1 := spec x₀ k f g h0
  rw [← coe_frickeForm, ← coe_frickeForm] at h1
  have h2 := spec (w x₀) k (frickeForm f) (frickeForm g) h1
  rw [coe_frickeForm, coe_frickeForm, slash_frickeGL_frickeGL, slash_frickeGL_frickeGL,
    qC_const_mul hT, qC_const_mul hT, ← mul_assoc, mul_comm (coeffMap ι _), mul_assoc] at h2
  have h3 := mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr
    (frickeSqConst_ne_zero (M := M) k)) h2
  rw [← h0] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ hg' h3))

end Spec

section Rep

local notation "Qb" => AlgebraicClosure ℚ

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT

theorem rep_add {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL Γ) k₁}
    {f₂ g₂ : ModularForm (ΓGL Γ) k₂} (h₁ : X * qC g₁ = qC f₁) (h₂ : Y * qC g₂ = qC f₂) :
    (X + Y) * qC (⇑(g₁.mul g₂)) = qC (⇑(f₁.mul g₂ + g₁.mul f₂)) := by
  rw [ModularForm.coe_add, qC_add hT, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul,
    qC_mul hT, qC_mul hT, qC_mul hT]
  linear_combination qC ⇑g₂ * h₁ + qC ⇑g₁ * h₂

theorem rep_mul {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL Γ) k₁}
    {f₂ g₂ : ModularForm (ΓGL Γ) k₂} (h₁ : X * qC g₁ = qC f₁) (h₂ : Y * qC g₂ = qC f₂) :
    (X * Y) * qC (⇑(g₁.mul g₂)) = qC (⇑(f₁.mul f₂)) := by
  rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT, qC_mul hT]
  linear_combination qC ⇑f₂ * h₁ + X * qC ⇑g₁ * h₂

theorem rep_neg {X : LaurentSeries ℂ} {k : ℤ} {f g : ModularForm (ΓGL Γ) k} (h : X * qC g = qC f) :
    (-X) * qC g = qC (⇑(-f)) := by
  rw [ModularForm.coe_neg, qC_neg hT, ← h]; ring

omit hT in

theorem rep_inv {X : LaurentSeries ℂ} {k : ℤ} {f g : ModularForm (ΓGL Γ) k} (h : X * qC g = qC f)
    (hf : qC f ≠ 0) : X⁻¹ * qC f = qC g := by
  have hX : X ≠ 0 := by rintro rfl; exact hf (by rw [← h, zero_mul])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hX, one_mul]

theorem qC_const (a : ℂ) : qC ((ModularForm.const a : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) = HahnSeries.C a := by
  have hc : ((ModularForm.const a : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) =
      a • ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [hc, qC_smul hT, ModularForm.one_coe_eq_one, qC_one, mul_one]

omit hT in
theorem qC_one_form : qC ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) = 1 := by
  rw [ModularForm.one_coe_eq_one, qC_one]

theorem cross_mul_eq {X : LaurentSeries ℂ} {k k' : ℤ} {f g : ModularForm (ΓGL Γ) k}
    {F G : ModularForm (ΓGL Γ) k'} (h : X * qC g = qC f) (h' : X * qC G = qC F) :
    (⇑f * ⇑G : ℍ → ℂ) = ⇑F * ⇑g := by
  refine mul_eq_mul_of_qC hT f G F g (add_comm k' k) ?_
  rw [← h, ← h']; ring

end Rep

section Diamond

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem le_conj_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ΓGL (CohCarrier.GammaH M H) ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • ΓGL (CohCarrier.GammaH M H) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

def slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

theorem coe_slashForm_mul {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁) (g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂) :
    ⇑((slashForm γ hγ f).mul (slashForm γ hγ g)) = ⇑(f.mul g) ∣[k₁ + k₂] (γ : GL (Fin 2) ℝ) := by
  simp only [coe_slashForm, ModularForm.coe_mul, ← ModularForm.SL_slash]
  exact (ModularForm.mul_slash_SL2 k₁ k₂ γ f g).symm

theorem coe_slashForm_add {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(slashForm γ hγ f + slashForm γ hγ g) = ⇑(f + g) ∣[k] (γ : GL (Fin 2) ℝ) := by
  simp only [coe_slashForm, ModularForm.coe_add, SlashAction.add_slash]

theorem coe_slashForm_neg {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(-slashForm γ hγ f) = ⇑(-f) ∣[k] (γ : GL (Fin 2) ℝ) := by
  simp only [coe_slashForm, ModularForm.coe_neg, SlashAction.neg_slash]

theorem slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    {f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hf : f ≠ 0) : slashForm γ hγ f ≠ 0 := by
  intro h
  apply hf
  have h' : ⇑f ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by rw [← coe_slashForm γ hγ, h, ModularForm.coe_zero]
  have : (⇑f : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k] ((γ : GL (Fin 2) ℝ))⁻¹) h'
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using this
  exact DFunLike.ext' (by rw [this, ModularForm.coe_zero])

variable (ι : Qb →+* ℂ) (D : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)) (γ : SL(2, ℤ))
  (hγ : γ ∈ Gamma0 M)

def DiaP (x : LBC (CohCarrier.GammaH M H)) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k), qC g ≠ 0 ∧
    coeffMap ι (x : LaurentSeries Qb) * qC g = qC f ∧
    coeffMap ι ((D x : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) * qC (slashForm γ hγ g) = qC (slashForm γ hγ f)

variable {ι D γ hγ}

private theorem hT' : ModularGroup.T ∈ (CohCarrier.GammaH M H) := translation_mem_GammaH M H

theorem DiaP.apply_rep {x : LBC (CohCarrier.GammaH M H)} (hx : DiaP ι D γ hγ x) {k' : ℤ} (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k')
    (h' : coeffMap ι (x : LaurentSeries Qb) * qC G = qC F) :
    coeffMap ι ((D x : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) * qC (slashForm γ hγ G) = qC (slashForm γ hγ F) := by
  obtain ⟨k, f, g, hg0, h, hD⟩ := hx
  by_cases hG : qC G = 0
  · have hG0 : G = 0 := (qC_eq_zero_iff hT' G).mp hG
    have hF0 : F = 0 := (qC_eq_zero_iff hT' F).mp (by rw [← h', hG, mul_zero])
    subst hG0 hF0
    simp [coe_slashForm, ModularForm.coe_zero, qC_zero]
  have hfun := cross_mul_eq hT' h h'

  have hsl : (⇑(slashForm γ hγ f) * ⇑(slashForm γ hγ G) : ℍ → ℂ) =
      ⇑(slashForm γ hγ F) * ⇑(slashForm γ hγ g) := by
    have := congrArg (fun P : ℍ → ℂ => P ∣[k + k'] (γ : GL (Fin 2) ℝ)) hfun
    beta_reduce at this
    rw [← ModularForm.SL_slash, ModularForm.mul_slash_SL2] at this
    conv at this => rhs; rw [add_comm, ← ModularForm.SL_slash, ModularForm.mul_slash_SL2]
    simpa only [coe_slashForm, ModularForm.SL_slash] using this
  have hq := congrArg qC hsl
  rw [qC_mul hT', qC_mul hT'] at hq
  have hgγ : qC (slashForm γ hγ g) ≠ 0 := fun h0 =>
    slashForm_ne_zero γ hγ (fun hg => hg0 ((qC_eq_zero_iff hT' g).mpr hg)) ((qC_eq_zero_iff hT' _).mp h0)
  apply mul_right_cancel₀ hgγ
  rw [mul_assoc, mul_comm (qC _) (qC _), ← hq, ← mul_assoc, hD]

theorem DiaP.add {x y : LBC (CohCarrier.GammaH M H)} (hx : DiaP ι D γ hγ x) (hy : DiaP ι D γ hγ y) : DiaP ι D γ hγ (x + y) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, hD₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, hD₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_add, map_add]; exact rep_add hT' h₁ h₂
  · rw [map_add, IntermediateField.coe_add, map_add]
    have e1 : ⇑(slashForm γ hγ (g₁.mul g₂)) = ⇑((slashForm γ hγ g₁).mul (slashForm γ hγ g₂)) :=
      (coe_slashForm_mul γ hγ g₁ g₂).symm
    have e2 : ⇑(slashForm γ hγ (f₁.mul g₂ + g₁.mul f₂)) =
        ⇑((slashForm γ hγ f₁).mul (slashForm γ hγ g₂) + (slashForm γ hγ g₁).mul (slashForm γ hγ f₂)) := by
      rw [coe_slashForm, ModularForm.coe_add, SlashAction.add_slash, ModularForm.coe_add,
        coe_slashForm_mul, coe_slashForm_mul]
    rw [e1, e2]
    exact rep_add hT' hD₁ hD₂

theorem DiaP.mul {x y : LBC (CohCarrier.GammaH M H)} (hx : DiaP ι D γ hγ x) (hy : DiaP ι D γ hγ y) : DiaP ι D γ hγ (x * y) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, hD₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, hD₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_mul, map_mul]; exact rep_mul hT' h₁ h₂
  · rw [map_mul, IntermediateField.coe_mul, map_mul]
    have e1 : ⇑(slashForm γ hγ (g₁.mul g₂)) = ⇑((slashForm γ hγ g₁).mul (slashForm γ hγ g₂)) :=
      (coe_slashForm_mul γ hγ g₁ g₂).symm
    have e2 : ⇑(slashForm γ hγ (f₁.mul f₂)) = ⇑((slashForm γ hγ f₁).mul (slashForm γ hγ f₂)) :=
      (coe_slashForm_mul γ hγ f₁ f₂).symm
    rw [e1, e2]
    exact rep_mul hT' hD₁ hD₂

theorem DiaP.neg {x : LBC (CohCarrier.GammaH M H)} (hx : DiaP ι D γ hγ x) : DiaP ι D γ hγ (-x) := by
  obtain ⟨k, f, g, hg, h, hD⟩ := hx
  refine ⟨k, -f, g, hg, ?_, ?_⟩
  · rw [IntermediateField.coe_neg, map_neg]; exact rep_neg hT' h
  · rw [map_neg, IntermediateField.coe_neg, map_neg]
    have e : ⇑(slashForm γ hγ (-f)) = ⇑(-slashForm γ hγ f) := (coe_slashForm_neg γ hγ f).symm
    rw [e]
    exact rep_neg hT' hD

theorem DiaP.zero : DiaP ι D γ hγ 0 := by
  refine ⟨0, 0, 1, ?_, ?_, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · simp [qC_zero]
  · rw [map_zero]
    simp [qC_zero]

theorem DiaP.inv {x : LBC (CohCarrier.GammaH M H)} (hx : DiaP ι D γ hγ x) : DiaP ι D γ hγ x⁻¹ := by
  obtain ⟨k, f, g, hg, h, hD⟩ := hx
  by_cases hf : qC f = 0
  · have hx0 : x = 0 := by
      have : coeffMap ι (x : LaurentSeries Qb) = 0 := by
        rw [hf] at h; exact (mul_eq_zero.mp h).resolve_right hg
      exact Subtype.ext (coeffMap_injective ι (by rw [this, IntermediateField.coe_zero, map_zero]))
    rw [hx0, _root_.inv_zero]
    exact DiaP.zero
  refine ⟨k, g, f, hf, ?_, ?_⟩
  · rw [IntermediateField.coe_inv, map_inv₀]; exact rep_inv h hf
  · rw [map_inv₀, IntermediateField.coe_inv, map_inv₀]
    refine rep_inv hD fun h0 => ?_
    exact slashForm_ne_zero γ hγ (fun hf' => hf ((qC_eq_zero_iff hT' f).mpr hf'))
      ((qC_eq_zero_iff hT' _).mp h0)

theorem diaP_algebraMap (c : Qb) : DiaP ι D γ hγ (algebraMap Qb (LBC (CohCarrier.GammaH M H)) c) := by
  have hc : ((algebraMap Qb (LBC (CohCarrier.GammaH M H)) c : LBC (CohCarrier.GammaH M H)) :
      LaurentSeries Qb) = HahnSeries.C c := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  refine ⟨0, ModularForm.const (ι c), 1, ?_, ?_, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · rw [qC_one_form, mul_one, qC_const hT', hc, coeffMap_C]
  · rw [AlgEquiv.commutes, hc, coeffMap_C, coe_slashForm, coe_slashForm, ModularForm.one_coe_eq_one,
      ModularForm.is_invariant_one', qC_one, mul_one]
    have : ((ModularForm.const (ι c) : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) : ℍ → ℂ) ∣[(0 : ℤ)] (γ : GL (Fin 2) ℝ) =
        (ModularForm.const (ι c) : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) := by
      rw [← ModularForm.SL_slash]
      exact ModularForm.is_invariant_const γ (ι c)
    rw [this, qC_const hT']

theorem diaP_gen {d : (ZMod M)ˣ} (hDd : IsDiamondAutHBar M H d D) (hγd : ((γ 0 0 : ℤ) : ZMod M) = d)
    {k : ℤ} (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : DiaP ι D γ hγ (gen f g hf hg hg0) := by
  refine ⟨k, f, g, qC_ne_zero_of_witness hg hg0, gen_rep ι f g hf hg hg0, ?_⟩
  obtain ⟨y, -, hy, hyq⟩ := hDd k f g pf pg hf hg hg0 γ hγ hγd
  change ((D (gen f g hf hg hg0) : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) = coeffEmb Qb y at hy
  rw [hy, coeffMap_coeffEmb]
  exact hyq

theorem diaP_all {d : (ZMod M)ˣ} (hDd : IsDiamondAutHBar M H d D) (hγd : ((γ 0 0 : ℤ) : ZMod M) = d)
    (x : LBC (CohCarrier.GammaH M H)) : DiaP ι D γ hγ x := by
  obtain ⟨z, hz⟩ := x
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT' hy
      exact diaP_gen hDd hγd f g hf hg hg0
  | algebraMap a =>
      have e : (algebraMap Qb (LBC (CohCarrier.GammaH M H)) a : LBC (CohCarrier.GammaH M H)) =
          ⟨algebraMap Qb (LaurentSeries Qb) a, IntermediateField.algebraMap_mem _ a⟩ :=
        Subtype.ext (IntermediateField.coe_algebraMap_apply _ a)
      rw [← e]; exact diaP_algebraMap a
  | add x y hx hy px py =>
      have e : ((⟨x, hx⟩ + ⟨y, hy⟩ : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H)) =
          ⟨x + y, add_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_add _ _ _)
      rw [← e]; exact DiaP.add px py
  | inv x hx px =>
      have e : ((⟨x, hx⟩ : LBC (CohCarrier.GammaH M H))⁻¹ : LBC (CohCarrier.GammaH M H)) = ⟨x⁻¹, inv_mem hx⟩ :=
        Subtype.ext (IntermediateField.coe_inv _ _)
      rw [← e]; exact DiaP.inv px
  | mul x y hx hy px py =>
      have e : ((⟨x, hx⟩ * ⟨y, hy⟩ : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H)) =
          ⟨x * y, mul_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_mul _ _ _)
      rw [← e]; exact DiaP.mul px py

end Diamond

section LawTwo

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

omit [NeZero M] in

theorem mul_frickeMat_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    γ * CohCarrier.frickeMat M γ (CohCarrier.N_dvd_of_mem_Gamma0 M hγ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨mul_mem hγ (CohCarrier.frickeMat_mem_Gamma0 M hγ), ?_⟩
  have h := CohCarrier.gamma0Units_frickeMat M ⟨γ, hγ⟩
  have : (⟨γ * CohCarrier.frickeMat M γ (CohCarrier.N_dvd_of_mem_Gamma0 M hγ),
      mul_mem hγ (CohCarrier.frickeMat_mem_Gamma0 M hγ)⟩ : Gamma0 M) =
      ⟨γ, hγ⟩ * ⟨CohCarrier.frickeMat M γ (CohCarrier.N_dvd_of_mem_Gamma0 M hγ),
        CohCarrier.frickeMat_mem_Gamma0 M hγ⟩ := rfl
  rw [this, map_mul, h, mul_inv_cancel]
  exact one_mem H

theorem slash_gamma_fricke_gamma {k : ℤ} (h : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((⇑h ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] frickeGL M) ∣[k] (γ : GL (Fin 2) ℝ) = ⇑h ∣[k] frickeGL M := by
  have h10 := CohCarrier.N_dvd_of_mem_Gamma0 M hγ
  have hW : frickeGL M * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h10) * frickeGL M := by
    rw [← frickeGL_mul_mul_inv γ h10, inv_mul_cancel_right]
  have hmat : (γ : GL (Fin 2) ℝ) * frickeGL M * (γ : GL (Fin 2) ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (γ * CohCarrier.frickeMat M γ h10) * frickeGL M := by
    rw [map_mul, ← mapGL_eq_coe, mul_assoc, hW, mul_assoc]
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, hmat, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantForm.slash_action_eqn h _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (mul_frickeMat_mem hγ))

theorem frickeForm_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : g ≠ 0) :
    frickeForm g ≠ 0 := by
  intro h
  apply hg
  have h' : (⇑g ∣[k] frickeGL M) ∣[k] frickeGL M = 0 := by
    rw [← coe_frickeForm, h, ModularForm.coe_zero, SlashAction.zero_slash]
  rw [slash_frickeGL_frickeGL] at h'
  have : (⇑g : ℍ → ℂ) = 0 := by
    funext τ
    have := congrFun h' τ
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero, frickeSqConst_ne_zero, false_or] at this
    exact this
  exact DFunLike.ext' (by rw [this, ModularForm.coe_zero])

theorem qC_frickeForm_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k}
    (hg : qC g ≠ 0) : qC (⇑g ∣[k] frickeGL M) ≠ 0 := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  rw [← coe_frickeForm]
  exact fun h0 => frickeForm_ne_zero (fun h => hg ((qC_eq_zero_iff hT g).mpr h))
    ((qC_eq_zero_iff hT _).mp h0)

theorem exists_gamma0_upperLeft (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), ∃ _ : γ ∈ Gamma0 M, ((γ 0 0 : ℤ) : ZMod M) = d := by
  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h1 : (CohCarrier.gamma0Units M γd)⁻¹ = d := by rw [hγd, inv_inv]
  refine ⟨γd, γd.2, ?_⟩
  rw [← h1]
  rfl

theorem dia_fricke_dia (ι : Qb →+* ℂ)
    {w : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    {D : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)} {d : (ZMod M)ˣ}
    (hDd : IsDiamondAutHBar M H d D) (x : LBC (CohCarrier.GammaH M H)) : D (w (D x)) = w x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0_upperLeft (M := M) d
  suffices h : (D.trans (w.trans D)).toAlgHom = w.toAlgHom from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => ?_
  change D (w (D (gen f g hf hg hg0))) = w (gen f g hf hg hg0)
  set x₀ := gen f g hf hg hg0
  have hall := fun y => diaP_all (ι := ι) (D := D) (γ := γ) (hγ := hγ) hDd hγd y
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0
  have h1 := (hall x₀).apply_rep f g h0
  have h2 := spec (D x₀) k (slashForm γ hγ f) (slashForm γ hγ g) h1
  rw [← coe_frickeForm, ← coe_frickeForm] at h2
  have h3 := (hall (w (D x₀))).apply_rep (frickeForm (slashForm γ hγ f))
    (frickeForm (slashForm γ hγ g)) h2
  simp only [coe_slashForm, coe_frickeForm, slash_gamma_fricke_gamma _ hγ] at h3
  have h4 := spec x₀ k f g h0
  rw [← h4] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ (qC_frickeForm_ne_zero hg') h3))

theorem diamondAut_fricke_diamondAut (ι : Qb →+* ℂ)
    {w : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (d : (ZMod M)ˣ)
    (x : xHFunctionFieldBar M H) :
    diamondAutHBar M H d (w (diamondAutHBar M H d x)) = w x := by
  rcases Classical.em (∃ σ : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) with h | h
  · exact dia_fricke_dia ι spec (isDiamondAutHBar_diamondAutHBar h) x
  · rw [diamondAutHBar_of_not h]; rfl

end LawTwo

section LawOne

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]

theorem exists_top (ι : Qb →+* ℂ)
    (child : ∀ (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ),
      ∃ w : LBC (CohCarrier.GammaH M' H') ≃ₐ[Qb] LBC (CohCarrier.GammaH M' H'),
        FrickeSpec (CohCarrier.GammaH M' H') (frickeGL M') ι w) :
    ∃ w' : LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≃ₐ[Qb]
        LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)),
      FrickeSpec (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (frickeGL (M * ℓ)) ι w' ∧
        ∀ x, w' (w' x) = x := by
  have key : ∀ Γ' : Subgroup SL(2, ℤ), Γ' = CohCarrier.GammaH (M * ℓ) (liftSub M H ℓ) →
      ∃ w' : LBC Γ' ≃ₐ[Qb] LBC Γ', FrickeSpec Γ' (frickeGL (M * ℓ)) ι w' ∧ ∀ x, w' (w' x) = x := by
    rintro _ rfl
    obtain ⟨w', spec'⟩ := child (M * ℓ) (liftSub M H ℓ)
    exact ⟨w', spec', apply_apply_of_frickeSpec ι spec'⟩
  exact key _ (gammaH_inf_gamma0_eq M H ℓ)

variable (ι : Qb →+* ℂ)
  {w : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
  {w' : LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ))}

omit [NeZero M] [NeZero ℓ] in
variable (ℓ) in
theorem le_top_bot : ΓGL (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) ≤ ΓGL (CohCarrier.GammaH M H) :=
  Subgroup.map_mono inf_le_left

theorem qC_slash_frickeGL_mul {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qC (⇑f ∣[k] frickeGL (M * ℓ)) =
      qExpand ℂ ℓ (HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) * qC (⇑f ∣[k] frickeGL M)) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  rw [slash_frickeGL_mul, ← coe_frickeForm, ← qC_smul hT, ← coe_smul_form,
    ← qC_comp_heckeDiag hT ((((ℓ : ℂ) ^ (k - 1))) • frickeForm f) ℓ]
  congr 1

theorem leg_alpha (hβ : HeckeBetaHDefined M H ℓ)
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (spec' : FrickeSpec (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (frickeGL (M * ℓ)) ι w')
    (x : LBC (CohCarrier.GammaH M H)) :
    w' (heckeAlphaHBar Qb M H ℓ x) = heckeBetaHBar Qb M H ℓ (w x) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  suffices h : w'.toAlgHom.comp (heckeAlphaHBar Qb M H ℓ) =
      (heckeBetaHBar Qb M H ℓ).comp w.toAlgHom from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => Subtype.ext ?_
  set x₀ := gen f g hf hg hg0
  change ((w' (heckeAlphaHBar Qb M H ℓ x₀) : LBC _) : LaurentSeries Qb) =
    ((heckeBetaHBar Qb M H ℓ (w x₀) : LBC _) : LaurentSeries Qb)
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0

  have h4 := spec x₀ k f g h0

  have h0' : coeffMap ι ((heckeAlphaHBar Qb M H ℓ x₀ : LBC _) : LaurentSeries Qb) *
      qC (restrictForm (le_top_bot ℓ) g) = qC (restrictForm (le_top_bot ℓ) f) := by
    rw [coe_heckeAlphaHBar]; exact h0
  have h5 := spec' _ k (restrictForm (le_top_bot ℓ) f) (restrictForm (le_top_bot ℓ) g) h0'
  rw [coe_restrictForm, coe_restrictForm, qC_slash_frickeGL_mul, qC_slash_frickeGL_mul] at h5

  apply coeffMap_injective ι
  rw [coe_heckeBetaHBar M H ℓ hβ, coeffMap_qExpand]
  have hne : qExpand ℂ ℓ (HahnSeries.C ((ℓ : ℂ) ^ (k - 1)) * qC (⇑g ∣[k] frickeGL M)) ≠ 0 := by
    refine (map_ne_zero_iff (qExpand ℂ ℓ) (qExpand_injective ℓ)).mpr
      (mul_ne_zero ?_ (qC_frickeForm_ne_zero hg'))
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr
      (zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ))
  apply mul_right_cancel₀ hne
  rw [h5, ← map_mul, mul_left_comm, h4]

theorem leg_beta (hβ : HeckeBetaHDefined M H ℓ)
    (spec : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (spec' : FrickeSpec (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (frickeGL (M * ℓ)) ι w')
    (hw' : ∀ y, w' (w' y) = y) (x : LBC (CohCarrier.GammaH M H)) :
    w' (heckeBetaHBar Qb M H ℓ x) = heckeAlphaHBar Qb M H ℓ (w x) := by
  have h := leg_alpha ι hβ spec spec' (w x)
  rw [apply_apply_of_frickeSpec ι spec] at h
  rw [← h, hw']

end LawOne

section LawFour

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

omit [NeZero M] in
theorem semilinear_twist (w D : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H)
    (σ : Qb ≃ₐ[ℚ] Qb)
    (h : ∀ x : xHFunctionFieldBar M H,
      w (arithmeticGalois (xHFunctionField M H) σ • x) =
        arithmeticGalois (xHFunctionField M H) σ • D (w x)) :
    SemilinearAut.ofAlgAut w * arithmeticGalois (xHFunctionField M H) σ =
      arithmeticGalois (xHFunctionField M H) σ * SemilinearAut.ofAlgAut D * SemilinearAut.ofAlgAut w := by
  refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => ?_) ?_)
  · exact h x
  · change (1 : Qb ≃+* Qb) * σ.toRingEquiv = σ.toRingEquiv * 1 * 1
    rw [one_mul, mul_one, mul_one]

end LawFour

section Assembly

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ι : Qb →+* ℂ)
  {w : xHFunctionFieldBar M H ≃ₐ[Qb] xHFunctionFieldBar M H}

theorem lawOne (spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w)
    (child : ∀ (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ),
      ∃ w : LBC (CohCarrier.GammaH M' H') ≃ₐ[Qb] LBC (CohCarrier.GammaH M' H'),
        FrickeSpec (CohCarrier.GammaH M' H') (frickeGL M') ι w)
    (ℓ : ℕ) [Fact ℓ.Prime] (hβdef : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral Qb M H ℓ) (hβ : HeckeBetaHBarIntegral Qb M H ℓ)
    [HasPrincipalDivisors Qb (laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFIβ : FundamentalIdentityAlong Qb (heckeBetaHBar Qb M H ℓ) hβ)
    (hfinα : FiniteAlong Qb (heckeAlphaHBar Qb M H ℓ))
    (hNα : NormFormulaAlong Qb (heckeAlphaHBar Qb M H ℓ) hfinα)
    (hFIα : FundamentalIdentityAlong Qb (heckeAlphaHBar Qb M H ℓ) hα)
    (hfinβ : FiniteAlong Qb (heckeBetaHBar Qb M H ℓ))
    (hNβ : NormFormulaAlong Qb (heckeBetaHBar Qb M H ℓ) hfinβ) (x : JH M H) :
    heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
      = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨w', spec', hw'⟩ := exists_top (M := M) (H := H) (ℓ := ℓ) ι child
  let g' : SemilinearAut Qb (laurentBaseChange Qb (xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
    SemilinearAut.ofAlgAut w'
  have h₁ : ∀ y : xHFunctionFieldBar M H,
      g' • heckeAlphaHBar Qb M H ℓ y = heckeBetaHBar Qb M H ℓ (SemilinearAut.ofAlgAut w • y) :=
    fun y => leg_alpha ι hβdef spec₀ spec' y
  have h₂ : ∀ y : xHFunctionFieldBar M H,
      g' • heckeBetaHBar Qb M H ℓ y = heckeAlphaHBar Qb M H ℓ (SemilinearAut.ofAlgAut w • y) :=
    fun y => leg_beta ι hβdef spec₀ spec' hw' y
  exact AlgebraicCurve.SemilinearAut.pic0_correspondence_swap_smul
    (heckeAlphaHBar _ M H ℓ) (heckeBetaHBar _ M H ℓ) hα hβ hFIα hfinβ hNβ hFIβ hfinα hNα h₁ h₂ x

theorem lawTwo (spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (d : (ZMod M)ˣ)
    (x : JH M H) :
    diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x) = SemilinearAut.ofAlgAut w • x := by
  have hDwD : diamondAutHBar M H d * w * diamondAutHBar M H d = w :=
    AlgEquiv.ext fun y => diamondAut_fricke_diamondAut ι spec₀ d y
  have key0 : SemilinearAut.ofAlgAut (diamondAutHBar M H d * w * diamondAutHBar M H d) =
      SemilinearAut.ofAlgAut w := congrArg _ hDwD
  rw [MonoidHom.map_mul, MonoidHom.map_mul] at key0
  rw [diamondHBar_apply, diamondHBar_apply]
  calc _ = (SemilinearAut.ofAlgAut (diamondAutHBar M H d) * SemilinearAut.ofAlgAut w *
        SemilinearAut.ofAlgAut (diamondAutHBar M H d)) • x := by rw [mul_smul, mul_smul]
    _ = _ := by rw [key0]

theorem lawThree (spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w) (x : JH M H) :
    SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x := by
  have hww : w * w = 1 := AlgEquiv.ext fun y => apply_apply_of_frickeSpec ι spec₀ y
  have key0 : SemilinearAut.ofAlgAut (w * w) =
      (1 : SemilinearAut Qb (xHFunctionFieldBar M H)) := by rw [hww, MonoidHom.map_one]
  rw [MonoidHom.map_mul] at key0
  rw [← mul_smul, key0, one_smul]

omit [NeZero M] in

theorem lawFour
    (hgal : ∀ (σ : Qb ≃ₐ[ℚ] Qb) (c : ℕ) (hc : c.Coprime M), (∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : xHFunctionFieldBar M H,
        w (arithmeticGalois (xHFunctionField M H) σ • x) =
          arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))
    (σ : Qb ≃ₐ[ℚ] Qb) (c : ℕ) (hc : c.Coprime M) (hζ : ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c)
    (x : JH M H) :
    SemilinearAut.ofAlgAut w • (σ • x)
      = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x) := by
  have key := semilinear_twist w _ σ (hgal σ c hc hζ)
  have := congrArg (fun g => g • x) key
  simp only [mul_smul] at this
  rw [galois_smul_pic0_def, galois_smul_pic0_def, diamondHBar_apply]
  exact this

end Assembly

end A2FRHG
p2m_reactivate "P2MW.S_ModularCurve_frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul.A2FRHG"

open A2FRHG AlgebraicCurve ModularCurve CongruenceSubgroup in
open scoped MatrixGroups ModularForm in
theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])

    (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hw₁ : ∀ (x : ↥(xHFunctionFieldBar M H)) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        coeffMap ι ((w x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)))
    (hw₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ↥(xHFunctionFieldBar M H),
          w (arithmeticGalois (xHFunctionField M H) σ • x) =
            arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x)) :
    (∀ (ℓ : ℕ) [Fact ℓ.Prime]
        (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
        (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) M H ℓ)
        [HasPrincipalDivisors (AlgebraicClosure ℚ)
          (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
        (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβ)
        (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ))
        (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
          (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hfinα)
        (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
          (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hα)
        (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ))
        (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
          (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hfinβ)
        (x : JH M H),
      heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
        = SemilinearAut.ofAlgAut w • heckePic0HBar hα hβ hFIβ hfinα hNα x) ∧
    (∀ (d : (ZMod M)ˣ) (x : JH M H),
      diamondHBar M H d (SemilinearAut.ofAlgAut w • diamondHBar M H d x)
        = SemilinearAut.ofAlgAut w • x) ∧
    (∀ x : JH M H, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : JH M H,
          SemilinearAut.ofAlgAut w • (σ • x)
            = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x)) := by

  obtain rfl : W = frickeGL M := eq_frickeGL hW

  have spec₀ : FrickeSpec (CohCarrier.GammaH M H) (frickeGL M) ι w := fun x k f g h => hw₁ x k f g h

  have hin := fun (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ) =>
    ModularCurve.heckeDiamondInputsHAll M' H'

  have child : ∀ (M' : ℕ) [NeZero M'] (H' : Subgroup (ZMod M')ˣ),
      ∃ w : LBC (CohCarrier.GammaH M' H') ≃ₐ[AlgebraicClosure ℚ] LBC (CohCarrier.GammaH M' H'),
        FrickeSpec (CohCarrier.GammaH M' H') (frickeGL M') ι w := fun M' _ H' => by
    obtain ⟨w', spec', -⟩ :=
      ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul M' H' (hin M' H').2 ι
        (frickeGL M') rfl
    exact ⟨w', fun x k f g h => spec' x k f g h⟩
  refine ⟨fun ℓ _ hα hβ _ hFIβ hfinα hNα hFIα hfinβ hNβ x => ?_, fun d x => lawTwo ι spec₀ d x,
    fun x => lawThree ι spec₀ x,
    fun σ c hc hζ x => lawFour hw₂ σ c hc hζ x⟩
  have hβdef : HeckeBetaHDefined M H ℓ := ((hin M H).1 ℓ Fact.out).fst
  exact lawOne ι spec₀ child ℓ hβdef hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ x

end
end S_ModularCurve_frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul
end P2MW
export P2MW.S_ModularCurve_frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul (solution)
