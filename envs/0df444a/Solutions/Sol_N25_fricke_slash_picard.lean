-- Prove2me | solution 1 for N25.fricke_slash_picard
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:12.770285+00:00
-- url     : https://prove2.me/submissions/ac8b8a1a-58d4-4498-b365-7007cf1f8ae1

import Mathlib
import Definitions.Def_N25
import Definitions.Def_CohCarrier_Fricke
import Theorems.Thm_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace N25

namespace FrickePicard

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries AlgebraicCurve

open scoped MatrixGroups ModularForm Pointwise

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

private theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

private theorem frickeGL_mul_mul_inv [NeZero M] (γ : SL(2, ℤ)) (h : (M : ℤ) ∣ γ 1 0) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) * Matrix.SpecialLinearGroup.mapGL ℝ γ * ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h) := by
  rw [mul_inv_eq_iff_eq_mul, mapGL_eq_coe, mapGL_eq_coe]
  ext i j
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 / M : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne M)]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, CohCarrier.frickeMat, hc]; try ring)

private theorem le_conj_frickeGL [NeZero M] :
    (((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ConjAct.toConjAct ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))⁻¹ • (((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have h10 := CohCarrier.N_dvd_of_mem_GammaH M H ⟨δ, hδ⟩
  exact ⟨CohCarrier.frickeMat M δ h10, CohCarrier.frickeMat_mem M H ⟨δ, hδ⟩,
    (frickeGL_mul_mul_inv δ h10).symm⟩

private theorem coe_frickeForm [NeZero M] {k : ℤ} (f : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) :
    ⇑((restrictForm le_conj_frickeGL (ModularForm.translate f ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))))) = ⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) := rfl

private theorem val_scalarGL (a : ℝ) (ha : a ≠ 0) :
    (((Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha))) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, a] := rfl

private theorem det_scalarGL (a : ℝ) (ha : a ≠ 0) : (((Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha)))).det : ℝ) = a * a := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL a ha, Matrix.det_fin_two_of]; ring

private theorem scalarGL_smul (a : ℝ) (ha : a ≠ 0) (τ : ℍ) : (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha))) • τ = τ := by
  have hdet : 0 < (((Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha)))).det : ℝ) := by rw [det_scalarGL a ha]; exact mul_self_pos.mpr ha
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hdet]
  simp only [num, denom, val_scalarGL a ha, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  rw [mul_div_assoc, mul_div_cancel₀ _ (by exact_mod_cast ha)]

private theorem slash_scalarGL (k : ℤ) (a : ℝ) (ha : a ≠ 0) (φ : ℍ → ℂ) :
    φ ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha))) = (fun _ => ((|a * a| : ℝ) : ℂ) ^ (k - 1) * (a : ℂ) ^ (-k)) * φ := by
  have hdet : 0 < (((Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha)))).det : ℝ) := by rw [det_scalarGL a ha]; exact mul_self_pos.mpr ha
  funext τ
  rw [ModularForm.slash_apply, scalarGL_smul a ha, Pi.mul_apply]
  have hσ : σ ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a] (by rw [Matrix.det_fin_two_of]; simpa using (show (a : ℝ) ≠ 0 from ha)))) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_scalarGL a ha]
  simp only [denom, val_scalarGL a ha, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

private theorem frickeGL_mul_frickeGL [NeZero M] :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) * (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) = (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(-(M : ℝ)), 0; 0, (-(M : ℝ))] (by rw [Matrix.det_fin_two_of]; simpa using (show ((-(M : ℝ)) : ℝ) ≠ 0 from (neg_ne_zero.mpr (by exact_mod_cast NeZero.ne M))))) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem frickeSqConst_ne_zero [NeZero M] (k : ℤ) : ((((|(-(M : ℝ)) * (-(M : ℝ))| : ℝ) : ℂ) ^ (k - 1)) * (((-(M : ℝ) : ℝ) : ℂ) ^ (-k))) ≠ 0 := by
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
  · exact_mod_cast (abs_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr hM) (neg_ne_zero.mpr hM)))
  · exact_mod_cast neg_ne_zero.mpr hM

private theorem slash_frickeGL_frickeGL [NeZero M] (k : ℤ) (φ : ℍ → ℂ) :
    (φ ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))) ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) = (fun _ => ((((|(-(M : ℝ)) * (-(M : ℝ))| : ℝ) : ℂ) ^ (k - 1)) * (((-(M : ℝ) : ℝ) : ℂ) ^ (-k)))) * φ := by
  rw [← SlashAction.slash_mul, frickeGL_mul_frickeGL, slash_scalarGL k (-(M : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast NeZero.ne M)) φ]

end Groups

section QExp

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT

private theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₁) (g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₂) :
    (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f * ⇑g)) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) := by
  rw [← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods_of_T_mem hT)]

private theorem qC_add {k : ℤ} (f g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f + ⇑g)) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) + (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) := by
  rw [← map_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_of_T_mem hT) f g]

private theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) :
    (ofPowerSeries ℤ ℂ (qExpansion 1 (c • ⇑f)) : LaurentSeries ℂ) = HahnSeries.C c * (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) := by
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT) c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

private theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) : (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) = 0 ↔ f = 0 := by
  rw [← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem hT) f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

omit hT in
private theorem qC_zero : (ofPowerSeries ℤ ℂ (qExpansion 1 (0 : ℍ → ℂ)) : LaurentSeries ℂ) = 0 := by rw [qExpansion_zero, map_zero]

omit hT in
private theorem qC_one : (ofPowerSeries ℤ ℂ (qExpansion 1 (1 : ℍ → ℂ)) : LaurentSeries ℂ) = 1 := by rw [qExpansion_one, map_one]

omit hT in

private theorem qC_slash_zero (k : ℤ) (A : GL (Fin 2) ℝ) :
    (ofPowerSeries ℤ ℂ (qExpansion 1 ((0 : ℍ → ℂ) ∣[k] A)) : LaurentSeries ℂ) = 0 := by
  rw [SlashAction.zero_slash, qC_zero]

private theorem qC_const_mul {k : ℤ} (c : ℂ) (f : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) :
    (ofPowerSeries ℤ ℂ (qExpansion 1 ((fun _ => c) * ⇑f)) : LaurentSeries ℂ) = HahnSeries.C c * (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) := by
  rw [show ((fun _ => c) * ⇑f : ℍ → ℂ) = c • ⇑f from rfl, qC_smul hT]

private theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₁)
    (f₂ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₂) (f₃ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₃) (f₄ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₄)
    (hk : k₃ + k₄ = k₁ + k₂) (h : (ofPowerSeries ℤ ℂ (qExpansion 1 f₁) : LaurentSeries ℂ) * (ofPowerSeries ℤ ℂ (qExpansion 1 f₂) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f₃) : LaurentSeries ℂ) * (ofPowerSeries ℤ ℂ (qExpansion 1 f₄) : LaurentSeries ℂ)) :
    (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, FunLike.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑D)) : LaurentSeries ℂ) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_of_T_mem hT)
      (f₁.mul f₂) (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, hsub, map_sub]
    change (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f₁ * ⇑f₂)) : LaurentSeries ℂ) - (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f₃ * ⇑f₄)) : LaurentSeries ℂ) = 0
    rw [qC_mul hT, qC_mul hT, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff hT D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, FunLike.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

omit hT in
private theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

private theorem mul_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
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

private theorem add_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem hT
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
    ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, FunLike.coe_add,
      ModularForm.qExpansion_add one_pos h1, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul,
      div_add_div _ _ hg₁0 hg₂0]

omit hT in
private theorem inv_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · exact ⟨k, g, f, pg, pf, hg, hf, hf0, by rw [inv_div]⟩

private theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ)
      (PowerSeries.C n) := by
  have hc : ((ModularForm.const (n : ℂ) : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ) =
      (n : ℂ) • ((1 : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [IsIntegralQExp, PowerSeries.map_C, hc,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT),
    ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

private theorem algebraMap_mem_ratios (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
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

private theorem mem_ratios_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) :
    y ∈ intFormRatiosC ℚ Γ := by
  have hle : qExpFunctionFieldC ℚ Γ ≤ ({ carrier := intFormRatiosC ℚ Γ, mul_mem' := fun ha hb => mul_mem_ratios hT ha hb, one_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 1, add_mem' := fun ha hb => add_mem_ratios hT ha hb, zero_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 0, algebraMap_mem' := fun c => algebraMap_mem_ratios hT c, inv_mem' := fun a ha => inv_mem_ratios ha } : IntermediateField ℚ (LaurentSeries ℚ)) :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end QExp

section Coeff

variable (ι : (AlgebraicClosure ℚ) →+* ℂ)

private theorem coeffMap_injective : Function.Injective (coeffMap ι) := fun x y h => by
  ext k
  exact ι.injective (by simpa using congrArg (fun z => z.coeff k) h)

private theorem coeffMap_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb (AlgebraicClosure ℚ) y) = coeffMap (algebraMap ℚ ℂ) y := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

omit ι in
private theorem coeffMap_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = (ofPowerSeries ℤ ℂ (qExpansion 1 F) : LaurentSeries ℂ) := by
  rw [← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

private theorem coeffMap_coeffEmb_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap ι (coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ p)) = (ofPowerSeries ℤ ℂ (qExpansion 1 F) : LaurentSeries ℂ) := by
  rw [coeffMap_coeffEmb, coeffMap_intSeriesC h]

private theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    coeffMap f (HahnSeries.C c) = HahnSeries.C (f c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

private theorem subtype_eq_zero_of_coeffMap
    (ι : (AlgebraicClosure ℚ) →+* ℂ) (S : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))) (x : S)
    (hx : coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) = 0) : x = 0 := by
  have hv : (x : LaurentSeries (AlgebraicClosure ℚ)) = 0 :=
    coeffMap_injective ι (hx.trans (map_zero (coeffMap ι)).symm)
  exact Subtype.ext hv

end Coeff

section Spec

variable {Γ : Subgroup SL(2, ℤ)}

private theorem coe_gen {k : ℤ} (f g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    (((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _))) : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg) :=
  rfl

private theorem qC_ne_zero_of_witness {k : ℤ} {g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) ≠ 0 := by
  rw [← coeffMap_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

private theorem gen_rep (ι : (AlgebraicClosure ℚ) →+* ℂ) {k : ℤ} (f g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k)
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) :
    coeffMap ι (((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _))) : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) := by
  rw [coe_gen f g hf hg hg0, map_div₀, map_div₀, coeffMap_coeffEmb_intSeriesC ι hf,
    coeffMap_coeffEmb_intSeriesC ι hg, div_mul_cancel₀ _ (qC_ne_zero_of_witness hg hg0)]

private theorem algHom_ext_gen (hT : ModularGroup.T ∈ Γ) {E : Type*} [Semiring E] [Algebra (AlgebraicClosure ℚ) E]
    {φ₁ φ₂ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →ₐ[(AlgebraicClosure ℚ)] E}
    (h : ∀ (k : ℤ) (f g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0),
      φ₁ ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))) = φ₂ ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _))))) : φ₁ = φ₂ := by
  refine IntermediateField.algHom_ext_of_eq_adjoin (AlgebraicClosure ℚ) (S := (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)))
    (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (qExpFunctionFieldC ℚ Γ : Set (LaurentSeries ℚ))) rfl ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT hy
  exact h k f g pf pg hf hg hg0

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

private theorem apply_apply_of_frickeSpec (ι : (AlgebraicClosure ℚ) →+* ℂ) {w : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≃ₐ[(AlgebraicClosure ℚ)] (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))}
    (spec : (∀ (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (k : ℤ) (f g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k), coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) → coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ))) (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) :
    w (w x) = x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  suffices h : (w.trans w).toAlgHom = AlgHom.id (AlgebraicClosure ℚ) _ from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => ?_
  change w (w ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _))))) = (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))
  set x₀ := (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _))) with hx₀
  have hg' : (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) := gen_rep ι f g hf hg hg0
  have h1 := spec x₀ k f g h0
  rw [← coe_frickeForm, ← coe_frickeForm] at h1
  have h2 := spec (w x₀) k ((restrictForm le_conj_frickeGL (ModularForm.translate f ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))))) ((restrictForm le_conj_frickeGL (ModularForm.translate g ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))))) h1
  rw [coe_frickeForm, coe_frickeForm, slash_frickeGL_frickeGL, slash_frickeGL_frickeGL,
    qC_const_mul hT, qC_const_mul hT, ← mul_assoc, mul_comm (coeffMap ι _), mul_assoc] at h2
  have h3 := mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr
    (frickeSqConst_ne_zero (M := M) k)) h2
  rw [← h0] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ hg' h3))

end Spec

section Rep

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

include hT

private theorem rep_add {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₁}
    {f₂ g₂ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₂} (h₁ : X * (ofPowerSeries ℤ ℂ (qExpansion 1 g₁) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f₁) : LaurentSeries ℂ)) (h₂ : Y * (ofPowerSeries ℤ ℂ (qExpansion 1 g₂) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f₂) : LaurentSeries ℂ)) :
    (X + Y) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(g₁.mul g₂))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(f₁.mul g₂ + g₁.mul f₂))) : LaurentSeries ℂ) := by
  rw [FunLike.coe_add, qC_add hT, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul,
    qC_mul hT, qC_mul hT, qC_mul hT]
  linear_combination (ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g₂) : LaurentSeries ℂ) * h₁ + (ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g₁) : LaurentSeries ℂ) * h₂

private theorem rep_mul {X Y : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₁}
    {f₂ g₂ : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₂} (h₁ : X * (ofPowerSeries ℤ ℂ (qExpansion 1 g₁) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f₁) : LaurentSeries ℂ)) (h₂ : Y * (ofPowerSeries ℤ ℂ (qExpansion 1 g₂) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f₂) : LaurentSeries ℂ)) :
    (X * Y) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(g₁.mul g₂))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑(f₁.mul f₂))) : LaurentSeries ℂ) := by
  rw [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT, qC_mul hT]
  linear_combination (ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f₂) : LaurentSeries ℂ) * h₁ + X * (ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g₁) : LaurentSeries ℂ) * h₂

omit hT in

private theorem rep_inv {X : LaurentSeries ℂ} {k : ℤ} {f g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k} (h : X * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ))
    (hf : (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) ≠ 0) : X⁻¹ * (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) := by
  have hX : X ≠ 0 := by rintro rfl; exact hf (by rw [← h, zero_mul])
  rw [← h, ← mul_assoc, inv_mul_cancel₀ hX, one_mul]

private theorem qC_const (a : ℂ) : (ofPowerSeries ℤ ℂ (qExpansion 1 ((ModularForm.const a : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ)) : LaurentSeries ℂ) = HahnSeries.C a := by
  have hc : ((ModularForm.const a : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ) =
      a • ((1 : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [hc, qC_smul hT, ModularForm.one_coe_eq_one, qC_one, mul_one]

omit hT in
private theorem qC_one_form : (ofPowerSeries ℤ ℂ (qExpansion 1 ((1 : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ)) : LaurentSeries ℂ) = 1 := by
  rw [ModularForm.one_coe_eq_one, qC_one]

private theorem cross_mul_eq {X : LaurentSeries ℂ} {k k' : ℤ} {f g : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k}
    {F G : ModularForm (((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k'} (h : X * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ)) (h' : X * (ofPowerSeries ℤ ℂ (qExpansion 1 G) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 F) : LaurentSeries ℂ)) :
    (⇑f * ⇑G : ℍ → ℂ) = ⇑F * ⇑g := by
  refine mul_eq_mul_of_qC hT f G F g (add_comm k' k) ?_
  rw [← h, ← h']; ring

end Rep

section Diamond

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

private theorem le_conj_gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    (((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ConjAct.toConjAct ((γ : GL (Fin 2) ℝ))⁻¹ • (((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨γ * δ * γ⁻¹, CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨δ, hδ⟩, by simp; rfl⟩

private theorem coe_slashForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) :
    ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ)))) = ⇑f ∣[k] (γ : GL (Fin 2) ℝ) := rfl

private theorem coe_slashForm_mul {k₁ k₂ : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    (f : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₁) (g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k₂) :
    ⇑(((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ)))).mul ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g (γ : GL (Fin 2) ℝ))))) = ⇑(f.mul g) ∣[k₁ + k₂] (γ : GL (Fin 2) ℝ) := by
  simp only [coe_slashForm γ hγ, ModularForm.coe_mul, ← ModularForm.SL_slash]
  exact (ModularForm.mul_slash_SL2 k₁ k₂ γ f g).symm

private theorem slashForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)
    {f : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k} (hf : f ≠ 0) : (restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))) ≠ 0 := by
  intro h
  apply hf
  have h' : ⇑f ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by rw [← coe_slashForm γ hγ, h, FunLike.coe_zero]
  have : (⇑f : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k] ((γ : GL (Fin 2) ℝ))⁻¹) h'
    simpa only [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one,
      SlashAction.zero_slash] using this
  exact DFunLike.ext' (by rw [this, FunLike.coe_zero])

variable (ι : (AlgebraicClosure ℚ) →+* ℂ) (D : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≃ₐ[(AlgebraicClosure ℚ)] (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (γ : SL(2, ℤ))
  (hγ : γ ∈ Gamma0 M)

variable {ι D γ hγ}

private theorem hT' : ModularGroup.T ∈ (CohCarrier.GammaH M H) := translation_mem_GammaH M H

private theorem dia_apply_rep {x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} (hx : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ))) {k' : ℤ} (F G : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k')
    (h' : coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 G) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 F) : LaurentSeries ℂ)) :
    coeffMap ι ((D x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate G (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate F (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) := by
  obtain ⟨k, f, g, hg0, h, hD⟩ := hx
  by_cases hG : (ofPowerSeries ℤ ℂ (qExpansion 1 G) : LaurentSeries ℂ) = 0
  · have hG0 : G = 0 := (qC_eq_zero_iff hT' G).mp hG
    have hF0 : F = 0 := (qC_eq_zero_iff hT' F).mp (by rw [← h', hG, mul_zero])
    subst hG0 hF0
    change coeffMap ι (D x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((0 : ℍ → ℂ) ∣[k'] (γ : GL (Fin 2) ℝ))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((0 : ℍ → ℂ) ∣[k'] (γ : GL (Fin 2) ℝ))) : LaurentSeries ℂ)
    rw [qC_slash_zero k' (γ : GL (Fin 2) ℝ), mul_zero]
  have hfun := cross_mul_eq hT' h h'

  have hsl : (⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ)))) * ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate G (γ : GL (Fin 2) ℝ)))) : ℍ → ℂ) =
      ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate F (γ : GL (Fin 2) ℝ)))) * ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g (γ : GL (Fin 2) ℝ)))) := by
    have := congrArg (fun P : ℍ → ℂ => P ∣[k + k'] (γ : GL (Fin 2) ℝ)) hfun
    beta_reduce at this
    rw [← ModularForm.SL_slash, ModularForm.mul_slash_SL2] at this
    conv at this => rhs; rw [add_comm, ← ModularForm.SL_slash, ModularForm.mul_slash_SL2]
    simpa only [coe_slashForm γ hγ, ModularForm.SL_slash] using this
  have hq := congrArg (fun (F : ℍ → ℂ) => (ofPowerSeries ℤ ℂ (qExpansion 1 F) : LaurentSeries ℂ)) hsl
  rw [qC_mul hT', qC_mul hT'] at hq
  have hgγ : (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) ≠ 0 := fun h0 =>
    slashForm_ne_zero γ hγ (fun hg => hg0 ((qC_eq_zero_iff hT' g).mpr hg)) ((qC_eq_zero_iff hT' _).mp h0)
  apply mul_right_cancel₀ hgγ
  rw [mul_assoc, mul_comm ((ofPowerSeries ℤ ℂ (qExpansion 1 _) : LaurentSeries ℂ)) ((ofPowerSeries ℤ ℂ (qExpansion 1 _) : LaurentSeries ℂ)), ← hq, ← mul_assoc, hD]

private theorem dia_add {x y : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} (hx : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ))) (hy : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (y : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D y : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ))) : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι ((x + y) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D (x + y) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, hD₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, hD₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [map_add]; exact rep_add hT' h₁ h₂
  · rw [map_add, IntermediateField.coe_add, map_add]
    have e1 : ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate (g₁.mul g₂) (γ : GL (Fin 2) ℝ)))) = ⇑(((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g₁ (γ : GL (Fin 2) ℝ)))).mul ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g₂ (γ : GL (Fin 2) ℝ))))) :=
      (coe_slashForm_mul γ hγ g₁ g₂).symm
    have e2 : ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate (f₁.mul g₂ + g₁.mul f₂) (γ : GL (Fin 2) ℝ)))) =
        ⇑(((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f₁ (γ : GL (Fin 2) ℝ)))).mul ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g₂ (γ : GL (Fin 2) ℝ)))) + ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g₁ (γ : GL (Fin 2) ℝ)))).mul ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f₂ (γ : GL (Fin 2) ℝ))))) := by
      rw [coe_slashForm γ hγ, FunLike.coe_add, SlashAction.add_slash, FunLike.coe_add,
        coe_slashForm_mul γ hγ, coe_slashForm_mul γ hγ]
    rw [e1, e2]
    exact rep_add hT' hD₁ hD₂

private theorem dia_mul {x y : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} (hx : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ))) (hy : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (y : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D y : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ))) : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι ((x * y) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D (x * y) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, hD₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, hD₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [map_mul]; exact rep_mul hT' h₁ h₂
  · rw [map_mul, IntermediateField.coe_mul, map_mul]
    have e1 : ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate (g₁.mul g₂) (γ : GL (Fin 2) ℝ)))) = ⇑(((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g₁ (γ : GL (Fin 2) ℝ)))).mul ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g₂ (γ : GL (Fin 2) ℝ))))) :=
      (coe_slashForm_mul γ hγ g₁ g₂).symm
    have e2 : ⇑((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate (f₁.mul f₂) (γ : GL (Fin 2) ℝ)))) = ⇑(((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f₁ (γ : GL (Fin 2) ℝ)))).mul ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f₂ (γ : GL (Fin 2) ℝ))))) :=
      (coe_slashForm_mul γ hγ f₁ f₂).symm
    rw [e1, e2]
    exact rep_mul hT' hD₁ hD₂

private theorem dia_zero : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (0 : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D 0 : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  refine ⟨0, 0, 1, ?_, ?_, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · simp [qC_zero]
  · rw [map_zero, IntermediateField.coe_zero, map_zero, zero_mul,
      coe_slashForm γ hγ, FunLike.coe_zero, SlashAction.zero_slash, qC_zero]

private theorem dia_inv {x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} (hx : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ))) : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (x⁻¹ : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D x⁻¹ : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  obtain ⟨k, f, g, hg, h, hD⟩ := hx
  by_cases hf : (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) = 0
  · have hx0 : x = 0 := by
      have : coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
        rw [hf] at h; exact (mul_eq_zero.mp h).resolve_right hg
      exact subtype_eq_zero_of_coeffMap ι _ x this
    simpa only [hx0, IntermediateField.coe_zero, _root_.inv_zero] using
      (dia_zero (M := M) (H := H) (ι := ι) (D := D) (γ := γ) (hγ := hγ))
  refine ⟨k, g, f, hf, ?_, ?_⟩
  · rw [map_inv₀]; exact rep_inv h hf
  · rw [map_inv₀, IntermediateField.coe_inv, map_inv₀]
    refine rep_inv hD fun h0 => ?_
    exact slashForm_ne_zero γ hγ (fun hf' => hf ((qC_eq_zero_iff hT' f).mpr hf'))
      ((qC_eq_zero_iff hT' _).mp h0)

private theorem diaP_algebraMap (c : (AlgebraicClosure ℚ)) : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι ((algebraMap (AlgebraicClosure ℚ) ((laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) c) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D (algebraMap (AlgebraicClosure ℚ) ((laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) c) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  have hc : ((algebraMap (AlgebraicClosure ℚ) ((laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) c : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) :
      LaurentSeries (AlgebraicClosure ℚ)) = HahnSeries.C c := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  refine ⟨0, ModularForm.const (ι c), 1, ?_, ?_, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · rw [qC_one_form, mul_one, qC_const hT', hc, coeffMap_C]
  · rw [AlgEquiv.commutes, hc, coeffMap_C, coe_slashForm γ hγ, coe_slashForm γ hγ, ModularForm.one_coe_eq_one,
      ModularForm.is_invariant_one', qC_one, mul_one]
    have : ((ModularForm.const (ι c) : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) : ℍ → ℂ) ∣[(0 : ℤ)] (γ : GL (Fin 2) ℝ) =
        (ModularForm.const (ι c) : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 0) := by
      rw [← ModularForm.SL_slash]
      exact ModularForm.is_invariant_const γ (ι c)
    rw [this, qC_const hT']

private theorem diaP_gen {d : (ZMod M)ˣ} (hDd : IsDiamondAutHBar M H d D) (hγd : ((γ 0 0 : ℤ) : ZMod M) = d)
    {k : ℤ} (f g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k) {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))) : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  refine ⟨k, f, g, qC_ne_zero_of_witness hg hg0, gen_rep ι f g hf hg hg0, ?_⟩
  obtain ⟨y, -, hy, hyq⟩ := hDd k f g pf pg hf hg hg0 γ hγ hγd
  change ((D ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))) : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y at hy
  rw [hy, coeffMap_coeffEmb]
  exact hyq

private theorem diaP_all {d : (ZMod M)ˣ} (hDd : IsDiamondAutHBar M H d D) (hγd : ((γ 0 0 : ℤ) : ZMod M) = d)
    (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : (∃ (weight : ℤ) (numForm denForm : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) weight), (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) ≠ 0 ∧ coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 denForm) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 numForm) : LaurentSeries ℂ) ∧ coeffMap ι (D x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate denForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate numForm (γ : GL (Fin 2) ℝ))))) : LaurentSeries ℂ)) := by
  obtain ⟨z, hz⟩ := x
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT' hy
      exact diaP_gen (hγ := hγ) hDd hγd f g hf hg hg0
  | algebraMap a =>
      have e : (algebraMap (AlgebraicClosure ℚ) ((laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) a : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) =
          ⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a, IntermediateField.algebraMap_mem _ a⟩ :=
        Subtype.ext (IntermediateField.coe_algebraMap_apply _ a)
      rw [← e]; exact diaP_algebraMap (hγ := hγ) a
  | add x y hx hy px py =>
      have e : ((⟨x, hx⟩ + ⟨y, hy⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) =
          ⟨x + y, add_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_add _ _ _)
      rw [← e]; exact dia_add (hγ := hγ) px py
  | inv x hx px =>
      have e : ((⟨x, hx⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))))⁻¹ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) = ⟨x⁻¹, inv_mem hx⟩ :=
        Subtype.ext (IntermediateField.coe_inv _ _)
      rw [← e]; exact dia_inv (hγ := hγ) px
  | mul x y hx hy px py =>
      have e : ((⟨x, hx⟩ * ⟨y, hy⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) =
          ⟨x * y, mul_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_mul _ _ _)
      rw [← e]; exact dia_mul (hγ := hγ) px py

end Diamond

section LawTwo

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

omit [NeZero M] in

private theorem mul_frickeMat_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
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

private theorem slash_gamma_fricke_gamma {k : ℤ} (h : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ((⇑h ∣[k] (γ : GL (Fin 2) ℝ)) ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))) ∣[k] (γ : GL (Fin 2) ℝ) = ⇑h ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) := by
  have h10 := CohCarrier.N_dvd_of_mem_Gamma0 M hγ
  have hW : (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) * Matrix.SpecialLinearGroup.mapGL ℝ γ =
      Matrix.SpecialLinearGroup.mapGL ℝ (CohCarrier.frickeMat M γ h10) * (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) := by
    rw [← frickeGL_mul_mul_inv γ h10, inv_mul_cancel_right]
  have hmat : (γ : GL (Fin 2) ℝ) * (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) * (γ : GL (Fin 2) ℝ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (γ * CohCarrier.frickeMat M γ h10) * (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) := by
    rw [map_mul, ← mapGL_eq_coe, mul_assoc, hW, mul_assoc]
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul, ← mul_assoc, hmat, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantForm.slash_action_eqn h _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (mul_frickeMat_mem hγ))

private theorem frickeForm_ne_zero {k : ℤ} {g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k} (hg : g ≠ 0) :
    (restrictForm le_conj_frickeGL (ModularForm.translate g ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) ≠ 0 := by
  intro h
  apply hg
  have h' : (⇑g ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))) ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])) = 0 := by
    rw [← coe_frickeForm, h, FunLike.coe_zero, SlashAction.zero_slash]
  rw [slash_frickeGL_frickeGL] at h'
  have : (⇑g : ℍ → ℂ) = 0 := by
    funext τ
    have := congrFun h' τ
    change ((((|(-(M : ℝ)) * (-(M : ℝ))| : ℝ) : ℂ) ^ (k - 1)) * (((-(M : ℝ) : ℝ) : ℂ) ^ (-k))) * g τ = 0 at this
    exact (mul_eq_zero.mp this).resolve_left (frickeSqConst_ne_zero (M := M) k)
  exact DFunLike.ext' (by rw [this, FunLike.coe_zero])

private theorem qC_frickeForm_ne_zero {k : ℤ} {g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k}
    (hg : (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) ≠ 0) : (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))) : LaurentSeries ℂ) ≠ 0 := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  rw [← coe_frickeForm]
  exact fun h0 => frickeForm_ne_zero (fun h => hg ((qC_eq_zero_iff hT g).mpr h))
    ((qC_eq_zero_iff hT _).mp h0)

private theorem exists_gamma0_upperLeft (d : (ZMod M)ˣ) :
    ∃ γ : SL(2, ℤ), ∃ _ : γ ∈ Gamma0 M, ((γ 0 0 : ℤ) : ZMod M) = d := by
  obtain ⟨γd, hγd⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h1 : (CohCarrier.gamma0Units M γd)⁻¹ = d := by rw [hγd, inv_inv]
  refine ⟨γd, γd.2, ?_⟩
  rw [← h1]
  rfl

private theorem dia_fricke_dia (ι : (AlgebraicClosure ℚ) →+* ℂ)
    {w : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≃ₐ[(AlgebraicClosure ℚ)] (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))}
    (spec : (∀ (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (k : ℤ) (f g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k), coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) → coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ)))
    {D : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≃ₐ[(AlgebraicClosure ℚ)] (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} {d : (ZMod M)ˣ}
    (hDd : IsDiamondAutHBar M H d D) (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) : D (w (D x)) = w x := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0_upperLeft (M := M) d
  suffices h : (D.trans (w.trans D)).toAlgHom = w.toAlgHom from AlgHom.congr_fun h x
  refine algHom_ext_gen hT fun k f g pf pg hf hg hg0 => ?_
  change D (w (D ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))))) = w ((⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _))))
  set x₀ := (⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ _)))
  have hall := fun y => diaP_all (ι := ι) (D := D) (γ := γ) (hγ := hγ) hDd hγd y
  have hg' : (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) := gen_rep ι f g hf hg hg0
  have h1 := dia_apply_rep (hγ := hγ) (hall x₀) f g h0
  have h2 := spec (D x₀) k ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ)))) ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g (γ : GL (Fin 2) ℝ)))) h1
  rw [← coe_frickeForm, ← coe_frickeForm] at h2
  have h3 := dia_apply_rep (hγ := hγ) (hall (w (D x₀))) ((restrictForm le_conj_frickeGL (ModularForm.translate ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ)))) ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))))
    ((restrictForm le_conj_frickeGL (ModularForm.translate ((restrictForm (le_conj_gamma0 hγ) (ModularForm.translate g (γ : GL (Fin 2) ℝ)))) ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])))))) h2
  simp only [coe_slashForm γ hγ, coe_frickeForm, slash_gamma_fricke_gamma _ hγ] at h3
  have h4 := spec x₀ k f g h0
  rw [← h4] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ (qC_frickeForm_ne_zero hg') h3))

private theorem diamondAut_fricke_diamondAut (ι : (AlgebraicClosure ℚ) →+* ℂ)
    {w : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H}
    (spec : (∀ (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (k : ℤ) (f g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k), coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) → coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ))) (d : (ZMod M)ˣ)
    (x : xHFunctionFieldBar M H) :
    diamondAutHBar M H d (w (diamondAutHBar M H d x)) = w x := by
  rcases Classical.em (∃ σ : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) with h | h
  · exact dia_fricke_dia ι spec (isDiamondAutHBar_diamondAutHBar h) x
  · rw [diamondAutHBar_of_not h]; rfl

end LawTwo

section LawFour

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

omit [NeZero M] in
private theorem semilinear_twist (w D : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
    (h : ∀ x : xHFunctionFieldBar M H,
      w (arithmeticGalois (xHFunctionField M H) σ • x) =
        arithmeticGalois (xHFunctionField M H) σ • D (w x)) :
    SemilinearAut.ofAlgAut w * arithmeticGalois (xHFunctionField M H) σ =
      arithmeticGalois (xHFunctionField M H) σ * SemilinearAut.ofAlgAut D * SemilinearAut.ofAlgAut w := by
  refine Subtype.ext (Prod.ext (RingEquiv.ext fun x => ?_) ?_)
  · exact h x
  · change (1 : (AlgebraicClosure ℚ) ≃+* (AlgebraicClosure ℚ)) * σ.toRingEquiv = σ.toRingEquiv * 1 * 1
    rw [one_mul, mul_one, mul_one]

end LawFour

section Assembly

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ι : (AlgebraicClosure ℚ) →+* ℂ)
  {w : xHFunctionFieldBar M H ≃ₐ[(AlgebraicClosure ℚ)] xHFunctionFieldBar M H}

private theorem lawTwo (spec₀ : (∀ (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (k : ℤ) (f g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k), coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) → coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ))) (d : (ZMod M)ˣ)
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

private theorem lawThree (spec₀ : (∀ (x : (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))) (k : ℤ) (f g : ModularForm ((((CohCarrier.GammaH M H) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) k), coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 g) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 f) : LaurentSeries ℂ) → coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) * (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ) = (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] ((Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0] (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M]))))) : LaurentSeries ℂ))) (x : JH M H) :
    SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x := by
  have hww : w * w = 1 := AlgEquiv.ext fun y => apply_apply_of_frickeSpec ι spec₀ y
  have key0 : SemilinearAut.ofAlgAut (w * w) =
      (1 : SemilinearAut (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) := by rw [hww, MonoidHom.map_one]
  rw [MonoidHom.map_mul] at key0
  rw [← mul_smul, key0, one_smul]

omit [NeZero M] in

private theorem lawFour
    (hgal : ∀ (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (c : ℕ) (hc : c.Coprime M), (∀ ζ : (AlgebraicClosure ℚ), ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : xHFunctionFieldBar M H,
        w (arithmeticGalois (xHFunctionField M H) σ • x) =
          arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (c : ℕ) (hc : c.Coprime M) (hζ : ∀ ζ : (AlgebraicClosure ℚ), ζ ^ M = 1 → σ ζ = ζ ^ c)
    (x : JH M H) :
    SemilinearAut.ofAlgAut w • (σ • x)
      = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x) := by
  have key := semilinear_twist w _ σ (hgal σ c hc hζ)
  have := congrArg (fun g => g • x) key
  simp only [mul_smul] at this
  rw [galois_smul_pic0_def, galois_smul_pic0_def, diamondHBar_apply]
  exact this

end Assembly

end FrickePicard

open UpperHalfPlane ModularCurve HahnSeries AlgebraicCurve

open scoped MatrixGroups ModularForm

/-- A single slash-pinned Fricke automorphism induces Picard inversion,
involutivity, and the cyclotomic Galois covariance. -/
theorem _root_.solution
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (25 : ℝ), 0]) :
    ∃ w : xHFunctionFieldBar 25 H25 ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 25 H25,
      (∀ (x : xHFunctionFieldBar 25 H25) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH 25 H25 : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g) = ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) →
        coeffMap ι (w x : LaurentSeries (AlgebraicClosure ℚ)) *
            ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] W)) =
          ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (d : (ZMod 25)ˣ) (x : J),
        diamondHBar 25 H25 d (SemilinearAut.ofAlgAut w • diamondHBar 25 H25 d x) =
          SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : J, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (σ : Gal) (c : ℕ) (hc : c.Coprime 25),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ 25 = 1 → σ ζ = ζ ^ c) →
        ∀ x : J, SemilinearAut.ofAlgAut w • (σ • x) =
          σ • diamondHBar 25 H25 (ZMod.unitOfCoprime c hc) (SemilinearAut.ofAlgAut w • x)) := by
  obtain ⟨w, hspec, hgal⟩ :=
    exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul 25 H25
      (heckeDiamondInputsHAll 25 H25).2 ι W hW
  refine ⟨w, hspec, ?_, ?_, ?_⟩
  · have hW' : W = Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(0 : ℝ), -1; (25 : ℝ), 0]
        (by rw [Matrix.det_fin_two_of]; norm_num) := Units.ext hW
    rw [hW'] at hspec
    exact fun d x => FrickePicard.lawTwo ι hspec d x
  · have hW' : W = Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(0 : ℝ), -1; (25 : ℝ), 0]
        (by rw [Matrix.det_fin_two_of]; norm_num) := Units.ext hW
    rw [hW'] at hspec
    exact fun x => FrickePicard.lawThree ι hspec x
  · exact fun σ c hc hζ x => FrickePicard.lawFour hgal σ c hc hζ x

end N25
