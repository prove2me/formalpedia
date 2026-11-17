-- Prove2me | solution 1 for N25.gamma_pow_five
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:50.41166+00:00
-- url     : https://prove2.me/submissions/60307379-75d3-44ac-bc54-13250acff401

import Mathlib
import Definitions.Def_N25

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup ModularCurve

open scoped MatrixGroups ModularForm

namespace N25
/- Integral q-expansion ratios already form the rational function field. -/

namespace RationalRatios

open ModularCurve UpperHalfPlane

variable {Γ : Subgroup SL(2, ℤ)} (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)

include hΓ in
private theorem analytic {k : ℤ} (f : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ

include hΓ in
private theorem isIntegralQExp_mul {k₁ k₂ : ℤ} (f : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) k₁) (g : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) k₂)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f.mul g)) (pf * pg) := by
  unfold IsIntegralQExp at *
  rw [map_mul, hf, hg, ModularForm.coe_mul, qExpansion_mul (analytic hΓ f) (analytic hΓ g)]

include hΓ in
private theorem isIntegralQExp_add {k : ℤ} (f g : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (⇑(f + g)) (pf + pg) := by
  unfold IsIntegralQExp at *
  rw [map_add, hf, hg, ModularForm.coe_add, qExpansion_add (analytic hΓ f) (analytic hΓ g)]

include hΓ in
private theorem isIntegralQExp_intCast_smul_one (a : ℤ) :
    IsIntegralQExp (⇑(((a : ℂ)) • (1 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0))) (PowerSeries.C a) := by
  unfold IsIntegralQExp
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one,
    qExpansion_smul (by rw [← ModularForm.one_coe_eq_one (Γ := ((Γ : Subgroup (GL (Fin 2) ℝ))))]; exact analytic hΓ (1 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0)),
    qExpansion_one, PowerSeries.map_C]
  ext n
  simp [PowerSeries.coeff_C, Algebra.smul_def]

private theorem intSeriesC_add (K : Type*) [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

private theorem intSeriesC_C (K : Type*) [Field K] (a : ℤ) : intSeriesC K (PowerSeries.C a) = HahnSeries.C (a : K) := by
  simp [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]

include hΓ in

private theorem exists_intermediateField : ∃ S : IntermediateField ℚ (LaurentSeries ℚ), (S : Set (LaurentSeries ℚ)) = intFormRatiosC ℚ Γ := by
  classical
  refine ⟨{ carrier := intFormRatiosC ℚ Γ
            mul_mem' := ?_, one_mem' := one_mem_intFormRatiosC ℚ Γ, add_mem' := ?_, zero_mem' := ?_,
            algebraMap_mem' := ?_, inv_mem' := ?_ }, rfl⟩
  · rintro _ _ ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, h₁, rfl⟩ ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, h₂, rfl⟩
    refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, isIntegralQExp_mul hΓ f₁ f₂ hf₁ hf₂,
      isIntegralQExp_mul hΓ g₁ g₂ hg₁ hg₂, ?_, ?_⟩
    · rw [intSeriesC_mul]; exact mul_ne_zero h₁ h₂
    · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]
  · rintro _ _ ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, h₁, rfl⟩ ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, h₂, rfl⟩
    refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
      isIntegralQExp_add hΓ _ _ (isIntegralQExp_mul hΓ f₁ g₂ hf₁ hg₂) (isIntegralQExp_mul hΓ g₁ f₂ hg₁ hf₂),
      isIntegralQExp_mul hΓ g₁ g₂ hg₁ hg₂, ?_, ?_⟩
    · rw [intSeriesC_mul]; exact mul_ne_zero h₁ h₂
    · rw [intSeriesC_add, intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ h₁ h₂]
  · refine ⟨0, 0, 1, 0, 1, ?_, ?_, by simp, by simp⟩
    · show IsIntegralQExp (⇑(0 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0)) 0
      rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
    · show IsIntegralQExp (⇑(1 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0)) 1
      rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
  · intro c
    refine ⟨0, ((c.num : ℂ)) • (1 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0), ((c.den : ℤ) : ℂ) • (1 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0),
      PowerSeries.C c.num, PowerSeries.C (c.den : ℤ), isIntegralQExp_intCast_smul_one hΓ c.num,
      isIntegralQExp_intCast_smul_one hΓ c.den, ?_, ?_⟩
    · rw [intSeriesC_C]
      exact HahnSeries.C_ne_zero (by exact_mod_cast c.den_nz)
    · rw [intSeriesC_C, intSeriesC_C, ← map_div₀]
      push_cast
      rw [Rat.num_div_den, HahnSeries.algebraMap_apply']
      simp
  · rintro _ ⟨k, f, g, pf, pg, hf, hg, h, rfl⟩
    by_cases hpf : intSeriesC ℚ pf = 0
    · rw [hpf, zero_div, inv_zero]
      refine ⟨0, 0, 1, 0, 1, ?_, ?_, by simp, by simp⟩
      · show IsIntegralQExp (⇑(0 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0)) 0
        rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
      · show IsIntegralQExp (⇑(1 : ModularForm ((Γ : Subgroup (GL (Fin 2) ℝ))) 0)) 1
        rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
    · exact ⟨k, g, f, pg, pf, hg, hf, hpf, (inv_div _ _)⟩

end RationalRatios

private theorem mem_ratios_iff
    (Γ : Subgroup SL(2, ℤ)) (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup (GL (Fin 2) ℝ))).strictPeriods)
    (x : LaurentSeries ℚ) :
    x ∈ ModularCurve.qExpFunctionFieldC ℚ Γ ↔ x ∈ ModularCurve.intFormRatiosC ℚ Γ := by
  obtain ⟨S, hS⟩ := RationalRatios.exists_intermediateField hΓ
  have hle : ModularCurve.qExpFunctionFieldC ℚ Γ ≤ S :=
    IntermediateField.adjoin_le_iff.mpr (by rw [hS])
  constructor
  · intro hx
    have := hle hx
    rwa [← SetLike.mem_coe, hS] at this
  · intro hx
    exact ModularCurve.intFormRatiosC_subset ℚ Γ hx

/- Diamond specifications compose by the slash action on rational ratios. -/

namespace DiamondComposition

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

private theorem coeffMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simpa [coeffMap_coeff] using this

private theorem ofPowerSeries_coeff_negSucc (p : PowerSeries R) (n : ℕ) :
    (ofPowerSeries ℤ R p).coeff (Int.negSucc n) = 0 := by
  rw [ofPowerSeries_apply, embDomain_notin_range]
  simp

private theorem coeffMap_ofPowerSeries (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R p) = ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [coeffMap_coeff]
  cases k with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast]
      rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  | negSucc n =>
      rw [ofPowerSeries_coeff_negSucc, ofPowerSeries_coeff_negSucc, map_zero]

private theorem coeffMap_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = intSeriesC ℂ p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1

private theorem intSeriesC_eq_zero_iff {K : Type*} [Field K] [CharZero K] (p : PowerSeries ℤ) :
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

private theorem intSeriesC_add {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

private theorem intSeriesC_C (K : Type*) [Field K] (z : ℤ) :
    intSeriesC K (PowerSeries.C z) = HahnSeries.C (z : K) := by
  rw [intSeriesC, PowerSeries.map_C, ofPowerSeries_C]
  simp

private theorem intSeriesC_eq_of_isIntegralQExp {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) :
    intSeriesC ℂ p = ofPowerSeries ℤ ℂ (qExpansion 1 f) := by
  rw [intSeriesC]
  exact congrArg (ofPowerSeries ℤ ℂ) h

end Laurent

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private theorem exists_gamma0 [NeZero M] (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  refine ⟨γ, γ.2, ?_⟩
  have : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = ((γ.1 0 0 : ℤ) : ZMod M) := rfl
  rw [← this, hγ, inv_inv]

private theorem conj_mem_GammaH {γ A : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hA : A ∈ CohCarrier.GammaH M H) :
    γ * A * γ⁻¹ ∈ CohCarrier.GammaH M H :=
  CohCarrier.conj_mem_GammaH M H (⟨γ, hγ⟩ : Gamma0 M) ⟨A, hA⟩

open ConjAct Pointwise in

private theorem gammaH_le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine Subgroup.mem_map.mpr ⟨γ * A * γ⁻¹, conj_mem_GammaH hγ hA, ?_⟩
  show Matrix.SpecialLinearGroup.mapGL ℝ (γ * A * γ⁻¹) =
    Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ A *
      (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
  rw [map_mul, map_mul, map_inv]

private theorem coeGL_mul (a b : SL(2, ℤ)) :
    ((a * b : SL(2, ℤ)) : GL (Fin 2) ℝ) = (a : GL (Fin 2) ℝ) * (b : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) a b

private theorem entry_inv_mul {M : ℕ} {γ₁ γ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h : γ ∈ Gamma0 M)
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
    change (((γ₁⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
      (γ : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = _
    simp [Matrix.SpecialLinearGroup.SL2_inv_expl, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hentry]
  push_cast
  linear_combination ((γ₁ 1 1 : ℤ) : ZMod M) * hab + (-((γ₁ 0 1 : ℤ) : ZMod M)) * hg
    + (-(b * ((γ₁ 1 1 : ℤ) : ZMod M))) * ha + b * hdet' + (b * ((γ₁ 0 1 : ℤ) : ZMod M)) * hC

end Group

section Forms

private theorem one_mem_strictPeriods (M : ℕ) (H : Subgroup (ZMod M)ˣ) : (1 : ℝ) ∈ (((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

open ConjAct Pointwise in



private theorem coe_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    (⇑((fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γ hγ f) : ℍ → ℂ) = (⇑f) ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

private theorem slashQ_eq_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k f γ = ofPowerSeries ℤ ℂ (qExpansion 1 ((fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γ hγ f)) :=
  rfl

private theorem qexp_mul {a b : ℤ} (F : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) a) (G : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) b) :
    qExpansion 1 (⇑F * ⇑G) = qExpansion 1 F * qExpansion 1 G :=
  ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M H) F G

private theorem eq_of_qexp_eq {k : ℤ} {F G : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k}
    (h : qExpansion 1 (⇑F) = qExpansion 1 (⇑G)) : (⇑F : ℍ → ℂ) = ⇑G := by
  have h0 : F - G = 0 := by
    refine (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M H) (F - G)).mp ?_
    rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M H), h,
      sub_self]
  rw [sub_eq_zero.mp h0]

private theorem ne_zero_of_isIntegralQExp {k : ℤ} {g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  apply hg0
  rw [intSeriesC_eq_zero_iff]
  have h1 : qExpansion 1 (⇑g) = 0 := by rw [h, ModularForm.coe_zero, qExpansion_zero]
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_zero]
  exact hg.trans h1

private theorem conjForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k}
    (hg : g ≠ 0) : (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γ hγ g ≠ 0 := by
  intro h
  apply hg
  have h1 : (⇑g : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by
    rw [← coe_conjForm γ hγ g, h, ModularForm.coe_zero]
  have h2 : (⇑g : ℍ → ℂ) = 0 := (SlashAction.slash_eq_zero_iff _ _ _).mp h1
  exact DFunLike.ext' (by rw [h2, ModularForm.coe_zero])

private theorem slashQ_ne_zero {k : ℤ} {g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k g γ ≠ 0 := by
  rw [slashQ_eq_conjForm γ hγ]
  refine (map_ne_zero_iff _ ofPowerSeries_injective).mpr ?_
  rw [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M H)]
  exact conjForm_ne_zero γ hγ (ne_zero_of_isIntegralQExp hg hg0)

private theorem ofPowerSeries_qexp_ne_zero {k : ℤ} {g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g)) ≠ 0 := by
  rw [← intSeriesC_eq_of_isIntegralQExp hg, Ne, intSeriesC_eq_zero_iff]
  exact fun h => hg0 (by rw [h, intSeriesC_zero])

end Forms

section Ratios

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private theorem mem_intFormRatiosC_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField M H) :
    y ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H) :=
  (mem_ratios_iff (CohCarrier.GammaH M H) (one_mem_strictPeriods M H) y).mp hy

end Ratios

section Diamond

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private theorem isDiamondAutHBar_apply {d : (ZMod M)ˣ} {σ : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H}
    (h : IsDiamondAutHBar M H d σ) (k : ℤ) (f g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
      ((σ ((fun {k : ℤ}
  (f g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
  {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
  (hg0 : intSeriesC ℚ pg ≠ 0) =>
  (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H)) f g hf hg hg0) : xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
      coeffMap (algebraMap ℚ ℂ) y * (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k g γ = (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k f γ :=
  h k f g pf pg hf hg hg0 γ hγ hγd

private theorem isDiamondAutHBar_trans [NeZero M] {d e : (ZMod M)ˣ}
    {σ τ : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H}
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
  have hgen : σ ((fun {k : ℤ}
  (f g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
  {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
  (hg0 : intSeriesC ℚ pg ≠ 0) =>
  (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H)) f g hf hg hg0) = (fun {k : ℤ}
  (f g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
  {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
  (hg0 : intSeriesC ℚ pg ≠ 0) =>
  (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H)) f' g' hf' hg' hg0' := by
    apply Subtype.ext
    rw [hy]
    show coeffEmb (AlgebraicClosure ℚ) y = coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf' / intSeriesC ℚ pg')
    rw [hyv]
  obtain ⟨y'', hy''F, hy'', H2⟩ := isDiamondAutHBar_apply hτ k' f' g' pf' pg' hf' hg' hg0' γe hγe hγee
  refine ⟨y'', hy''F, ?_, ?_⟩
  · show ((τ (σ ((fun {k : ℤ}
  (f g : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
  {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
  (hg0 : intSeriesC ℚ pg ≠ 0) =>
  (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H)) f g hf hg hg0)) : xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y''
    rw [hgen, hy'']

  set Fd := (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γd hγd f
  set Gd := (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γd hγd g
  set F'e := (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γe hγe f'
  set G'e := (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γe hγe g'
  set Fγ := (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γ hγ f
  set Gγ := (fun {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
  (f : ModularForm ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) =>
  restrictForm (gammaH_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) γ hγ g

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
    change ((⇑f') ∣[k'] (γe : GL (Fin 2) ℝ)) *
        (((⇑g) ∣[k] (γd : GL (Fin 2) ℝ)) ∣[k] (γe : GL (Fin 2) ℝ)) =
      ((⇑g') ∣[k'] (γe : GL (Fin 2) ℝ)) *
        (((⇑f) ∣[k] (γd : GL (Fin 2) ℝ)) ∣[k] (γe : GL (Fin 2) ℝ)) at this
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, hγfac] at this
    exact this

  have E3 : (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k' f' γe * (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k g γ = (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k' g' γe * (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k f γ := by
    rw [slashQ_eq_conjForm γe hγe, slashQ_eq_conjForm γe hγe, slashQ_eq_conjForm γ hγ,
      slashQ_eq_conjForm γ hγ, ← map_mul, ← map_mul, ← qexp_mul, ← qexp_mul]
    exact congrArg _ (congrArg _ E2)

  show coeffMap (algebraMap ℚ ℂ) y'' * (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k g γ = (fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k f γ
  apply mul_right_cancel₀ (slashQ_ne_zero hg' hg0' hγe)
  linear_combination ((fun (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) =>
  ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))) k g γ) * H2 + E3

end Diamond

end DiamondComposition

/- A diamond label in the defining subgroup fixes the generating modular forms. -/

namespace DiamondTriviality

private theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

private theorem coeffMap_intSeriesC (K L : Type*) [Field K] [Field L] (φ : K →+* L) (p : PowerSeries ℤ) :
    coeffMap φ (intSeriesC K p) = intSeriesC L p := by
  rw [intSeriesC, DiamondComposition.coeffMap_ofPowerSeries, intSeriesC]
  congr 1
  have h := PowerSeries.map_comp (Int.castRingHom K) φ
  rw [RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)] at h
  rw [h]
  rfl

private theorem ofPowerSeries_qExpansion_eq {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) = coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ pf) := by
  rw [coeffMap_intSeriesC]
  unfold IsIntegralQExp at hf
  rw [← hf]
  rfl

private theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private theorem eq_refl_of_isDiamond {d : (ZMod M)ˣ} (hd : d ∈ H)
    (σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H)
    (hσ : IsDiamondAutHBar M H d σ) : σ = AlgEquiv.refl := by
  obtain ⟨γ0, hγ0⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h11 : ((γ0.1 1 1 : ℤ) : ZMod M) = ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    rw [← hγ0]; rfl
  have h00 : ((γ0.1 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have hmul := CohCarrier.Gamma0_d_mul_a M γ0
    rw [h11] at hmul
    calc ((γ0.1 0 0 : ℤ) : ZMod M)
        = (d : ZMod M) * (((d⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ0.1 0 0 : ℤ) : ZMod M)) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = (d : ZMod M) := by rw [hmul, mul_one]
  have hγH : (γ0.1 : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
    CohCarrier.mem_GammaH_iff.2 ⟨γ0.2, by
      rw [show (⟨γ0.1, γ0.2⟩ : Gamma0 M) = γ0 from rfl, hγ0]; exact H.inv_mem hd⟩
  have hγH' : ((γ0.1 : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem _ hγH

  have hgen : ∀ z ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H), ∀ hz' : coeffEmb (AlgebraicClosure ℚ) z ∈ xHFunctionFieldBar M H,
      σ ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ := by
    rintro z ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ hz'
    obtain ⟨y, -, hσy, hrel⟩ := hσ k f g pf pg hf hg hg0 γ0.1 γ0.2 h00
    apply Subtype.ext
    refine hσy.trans ?_
    rw [SlashInvariantForm.slash_action_eqn _ _ hγH', SlashInvariantForm.slash_action_eqn _ _ hγH',
      ofPowerSeries_qExpansion_eq f hf, ofPowerSeries_qExpansion_eq g hg, ← map_mul] at hrel
    have hy : y * intSeriesC ℚ pg = intSeriesC ℚ pf :=
      coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective hrel
    rw [(eq_div_iff hg0).2 hy]

  have hinner : ∀ z : LaurentSeries ℚ, z ∈ xHFunctionField M H →
      ∀ hz' : coeffEmb (AlgebraicClosure ℚ) z ∈ xHFunctionFieldBar M H,
        σ ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ := by
    intro z hz
    replace hz : z ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap c =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c), hz'⟩ : xHFunctionFieldBar M H) =
            algebraMap (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (algebraMap ℚ (AlgebraicClosure ℚ) c) := by
          apply Subtype.ext
          show coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c) = _
          rw [coeffEmb_algebraMap]
          rfl
        rw [e, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) (x + y), hz'⟩ : xHFunctionFieldBar M H) =
            ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange _ hx⟩ +
              ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange _ hy⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add, ihx, ihy]
    | inv x hx ih =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) x⁻¹, hz'⟩ : xHFunctionFieldBar M H) =
            (⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange _ hx⟩ : xHFunctionFieldBar M H)⁻¹ :=
          Subtype.ext (map_inv₀ _ _)
        rw [e, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) (x * y), hz'⟩ : xHFunctionFieldBar M H) =
            ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange _ hx⟩ *
              ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange _ hy⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [e, map_mul, ihx, ihy]

  have houter : ∀ (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ xHFunctionFieldBar M H), σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro x hx
    have hx0 : x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
        (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (xHFunctionField M H : Set (LaurentSeries ℚ))) := hx
    revert hx
    induction hx0 using IntermediateField.adjoin_induction with
    | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        exact hinner z hz
    | algebraMap c =>
        intro hx
        have e : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c, hx⟩ : xHFunctionFieldBar M H) =
            algebraMap (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) c := rfl
        rw [e, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
        intro h'
        have e : (⟨x + y, h'⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [e, map_add, ihx, ihy]
    | inv x hx ih =>
        intro h'
        have e : (⟨x⁻¹, h'⟩ : xHFunctionFieldBar M H) = (⟨x, hx⟩ : xHFunctionFieldBar M H)⁻¹ := rfl
        rw [e, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        intro h'
        have e : (⟨x * y, h'⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [e, map_mul, ihx, ihy]
  apply AlgEquiv.ext
  intro x
  exact houter x.1 x.2

end DiamondTriviality

/-- The fifth power of the label-13 diamond operator is trivial because 13⁵ lies in H25. -/
theorem _root_.solution (x : N25.J) : N25.gamma (N25.gamma (N25.gamma (N25.gamma (N25.gamma x)))) = x := by
  classical
  let d : (ZMod 25)ˣ := ZMod.unitOfCoprime 13 (by decide)
  have hd : d ^ 5 = (ZMod.unitOfCoprime 7 (by decide)) ^ 3 := by
    apply Units.ext
    change (13 : ZMod 25) ^ 5 = (7 : ZMod 25) ^ 3
    decide
  have hm : d ^ 5 ∈ H25 := by
    rw [hd]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  rcases Classical.em (∃ τ : xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ]
      xHFunctionFieldBar 25 H25, IsDiamondAutHBar 25 H25 d τ) with hex | hex
  · let τ := diamondAutHBar 25 H25 d
    have hτ : IsDiamondAutHBar 25 H25 d τ := isDiamondAutHBar_diamondAutHBar hex
    have hp (n : ℕ) : IsDiamondAutHBar 25 H25 (d ^ (n + 1)) (τ ^ (n + 1)) := by
      induction n with
      | zero => simpa only [zero_add, pow_one] using hτ
      | succ n ih =>
        have h := DiamondComposition.isDiamondAutHBar_trans hτ ih
        rw [mul_comm d (d ^ (n + 1))] at h
        have heq : τ.trans (τ ^ (n + 1)) = τ ^ (n + 1) * τ := by
          ext y
          rfl
        rw [heq] at h
        simpa only [pow_succ] using h
    have ht : τ ^ 5 = 1 :=
      DiamondTriviality.eq_refl_of_isDiamond 25 H25 hm (τ ^ 5) (hp 4)
    change SemilinearAut.ofAlgAut τ • (SemilinearAut.ofAlgAut τ •
      (SemilinearAut.ofAlgAut τ • (SemilinearAut.ofAlgAut τ •
        (SemilinearAut.ofAlgAut τ • x)))) = x
    repeat rw [← mul_smul]
    have he : SemilinearAut.ofAlgAut τ * SemilinearAut.ofAlgAut τ *
        SemilinearAut.ofAlgAut τ * SemilinearAut.ofAlgAut τ * SemilinearAut.ofAlgAut τ = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
      have ht' : τ * τ * τ * τ * τ = 1 := by
        simpa only [pow_succ, pow_zero, one_mul] using ht
      rw [ht', map_one]
    rw [he, one_smul]
  · change diamondHBar 25 H25 d (diamondHBar 25 H25 d
      (diamondHBar 25 H25 d (diamondHBar 25 H25 d (diamondHBar 25 H25 d x)))) = x
    simp only [diamondHBar_of_not 25 H25 hex]

end N25
