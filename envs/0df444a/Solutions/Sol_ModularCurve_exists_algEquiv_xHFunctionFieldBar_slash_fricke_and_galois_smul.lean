-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/c11d2fa6-6502-5740-af44-f288acc6d840

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_CohCarrier_Fricke
import Theorems.Thm_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0
import Theorems.Thm_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul

set_option autoImplicit false

noncomputable section

namespace A2FRE

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

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem hT) f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

omit hT in
theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

omit hT in
theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit hT in

theorem coe_smul_form {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) : ⇑(c • f) = c • ⇑f :=
  rfl

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

private theorem _root_.A2FRE.coeffMap_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb Qb y) = coeffMap (algebraMap ℚ ℂ) y := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

p2m_export "A2FRE" "coeffMap_coeffEmb"
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

end Coeff

section Spec

local notation "Qb" => AlgebraicClosure ℚ

abbrev LBC (Γ : Subgroup SL(2, ℤ)) : IntermediateField Qb (LaurentSeries Qb) :=
  laurentBaseChange Qb (qExpFunctionFieldC ℚ Γ)

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

end LawTwo

section Cyclo

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M]

omit [NeZero M] in

theorem pow_eq_pow_mod {ζ : Qb} (hζ : ζ ^ M = 1) (n : ℕ) : ζ ^ n = ζ ^ (n % M) := by
  conv_lhs => rw [← Nat.div_add_mod n M, _root_.pow_add, _root_.pow_mul, hζ, one_pow, one_mul]

def invExp (c : ℕ) (hc : c.Coprime M) : ℕ := (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod M)ˣ) : ZMod M).val

theorem natCast_invExp (c : ℕ) (hc : c.Coprime M) :
    ((invExp c hc : ℕ) : ZMod M) = (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod M)ˣ) : ZMod M) :=
  ZMod.natCast_zmod_val _

theorem mul_invExp_mod (c : ℕ) (hc : c.Coprime M) : (c * invExp c hc) % M = 1 % M := by
  have h : ((c * invExp c hc : ℕ) : ZMod M) = ((1 : ℕ) : ZMod M) := by
    rw [Nat.cast_mul, natCast_invExp, ← ZMod.coe_unitOfCoprime c hc, Units.mul_inv, Nat.cast_one]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h

theorem symm_apply_eq_pow {σ : Qb ≃ₐ[ℚ] Qb} {c : ℕ} (hc : c.Coprime M)
    (hσ : ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c) (ζ : Qb) (hζ : ζ ^ M = 1) :
    σ.symm ζ = ζ ^ invExp c hc := by
  set ξ := σ.symm ζ with hξdef
  have hξ : ξ ^ M = 1 := by
    apply σ.injective
    rw [map_pow, hξdef, AlgEquiv.apply_symm_apply, hζ, map_one]
  have h1 : ζ = ξ ^ c := by rw [← hσ ξ hξ, hξdef, AlgEquiv.apply_symm_apply]
  rw [h1, ← pow_mul, pow_eq_pow_mod hξ, mul_invExp_mod, ← pow_eq_pow_mod hξ, pow_one]

end Cyclo

section Span

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def res1 {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k :=
  restrictForm (Subgroup.map_mono (Gamma1_le_GammaH M H)) f

omit [NeZero M] in
@[scoped simp] theorem coe_res1 {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    ⇑(res1 f) = ⇑f := rfl

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : PowerSeries R) : coeffMap φ (ofPowerSeries ℤ R P) = ofPowerSeries ℤ S (P.map φ) := by
  ext n
  simp only [coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · rw [PowerSeries.coeff_map]

variable (ι : Qb →+* ℂ)

def qCHom (M : ℕ) (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k →+ LaurentSeries ℂ where
  toFun F := qC ⇑F
  map_zero' := by rw [ModularForm.coe_zero, qC_zero]
  map_add' F G := by rw [ModularForm.coe_add, qC_add hT']

theorem exists_rep_slash_frickeGL {k : ℤ} (f h : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    {pf ph : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hh : IsIntegralQExp h ph)
    (hh0 : intSeriesC ℚ ph ≠ 0) :
    ∃ u : LBC (CohCarrier.GammaH M H),
      coeffMap ι (u : LaurentSeries Qb) * qC h = qC (⇑f ∣[k] frickeGL M) := by
  have hfrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑f).coeff n = (r : ℂ) := fun n =>
    ⟨((PowerSeries.coeff n pf : ℤ) : ℚ), by rw [← hf.coeff n, Rat.cast_intCast]⟩
  obtain ⟨n, c, g, p, hp, hsum⟩ :=
    ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion M H f hfrat ι (frickeGL M)
      val_frickeGL
  refine ⟨∑ i, algebraMap Qb (LBC (CohCarrier.GammaH M H)) (c i) * gen (g i) h (hp i) hh hh0, ?_⟩

  have hs : (∑ i, ι (c i) • (⇑(g i) : ℍ → ℂ)) = ⇑(∑ i, ι (c i) • g i) := by
    rw [show (⇑(∑ i, ι (c i) • g i) : ℍ → ℂ) = ∑ i, ⇑(ι (c i) • g i) from
      FunLike.coe_sum ..]
    exact Finset.sum_congr rfl fun i _ => (coe_smul_form _ _).symm
  have hq : qC (⇑f ∣[k] frickeGL M) = ∑ i, HahnSeries.C (ι (c i)) * qC (g i) := by
    rw [hsum, hs, show qC (⇑(∑ i, ι (c i) • g i)) = qCHom M H k (∑ i, ι (c i) • g i) from rfl, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change qC ⇑(ι (c i) • g i) = _
    rw [coe_smul_form, qC_smul hT']
  rw [hq, IntermediateField.coe_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [IntermediateField.coe_mul, map_mul, mul_assoc, gen_rep ι _ h (hp i) hh hh0]
  congr 1
  have e : (((algebraMap Qb (LBC (CohCarrier.GammaH M H)) (c i)) :
      LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) = HahnSeries.C (c i) := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  rw [e, coeffMap_C]

end Span

section FrickeQ

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def qW {k : ℤ} (φ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) : LaurentSeries ℂ :=
  qC (⇑φ ∣[k] frickeGL M)

theorem qW_def {k : ℤ} (φ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qW φ = qC (⇑φ ∣[k] frickeGL M) := rfl

theorem qW_eq_qC_frickeForm {k : ℤ} (φ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qW φ = qC (frickeForm φ) := rfl

theorem coe_mul_slash_frickeGL {k₁ k₂ : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁)
    (g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂) :
    ⇑(f.mul g) ∣[k₁ + k₂] frickeGL M = (M : ℂ) • ⇑((frickeForm f).mul (frickeForm g)) := by
  rw [ModularForm.coe_mul, ModularForm.mul_slash, ModularForm.coe_mul, coe_frickeForm,
    coe_frickeForm, det_frickeGL, Nat.abs_cast]
  funext τ
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_natCast]

theorem qW_mul {k₁ k₂ : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁)
    (g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂) :
    qW (f.mul g) = HahnSeries.C (M : ℂ) * (qW f * qW g) := by
  rw [qW, coe_mul_slash_frickeGL, qC_smul hT', ModularForm.coe_mul, qC_mul hT']
  rfl

theorem qW_add {k : ℤ} (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) :
    qW (f + g) = qW f + qW g := by
  rw [qW, ModularForm.coe_add, SlashAction.add_slash, ← coe_frickeForm, ← coe_frickeForm,
    qC_add hT']
  rfl

theorem qW_zero {k : ℤ} : qW (0 : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) = 0 := by
  rw [qW, ModularForm.coe_zero, SlashAction.zero_slash, qC_zero]

theorem qW_ne_zero {k : ℤ} {g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : qC g ≠ 0) :
    qW g ≠ 0 :=
  qC_frickeForm_ne_zero hg

def frickeOneConst (M : ℕ) : ℂ := ((|(M : ℝ)| : ℝ) : ℂ) ^ ((0 : ℤ) - 1)

theorem const_slash_frickeGL (a : ℂ) :
    ((ModularForm.const a : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) : ℍ → ℂ) ∣[(0 : ℤ)]
        frickeGL M =
      ((ModularForm.const (a * frickeOneConst M) : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) :
        ℍ → ℂ) := by
  funext τ
  rw [ModularForm.slash_apply, ModularForm.const_apply, ModularForm.const_apply]
  have hσ : σ (frickeGL M) = ContinuousAlgEquiv.refl ℝ ℂ := by rw [σ, if_pos det_frickeGL_pos]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_frickeGL, neg_zero, zpow_zero, mul_one, frickeOneConst]

theorem qW_const (a : ℂ) :
    qW (ModularForm.const a : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) =
      HahnSeries.C (a * frickeOneConst M) := by
  rw [qW, const_slash_frickeGL, qC_const hT']

theorem qW_one : qW (1 : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) = HahnSeries.C (frickeOneConst M) := by
  have h : (1 : ModularForm (ΓGL (CohCarrier.GammaH M H)) 0) = ModularForm.const 1 := by
    apply DFunLike.ext'; funext z
    rw [ModularForm.one_coe_eq_one, Pi.one_apply, ModularForm.const_apply]
  rw [h, qW_const, one_mul]

theorem specW_add {X' Y' : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁}
    {f₂ g₂ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂} (h₁ : X' * qW g₁ = qW f₁) (h₂ : Y' * qW g₂ = qW f₂) :
    (X' + Y') * qW (g₁.mul g₂) = qW (f₁.mul g₂ + g₁.mul f₂) := by
  rw [qW_add, qW_mul, qW_mul, qW_mul]
  linear_combination (HahnSeries.C (M : ℂ) * qW g₂) * h₁ + (HahnSeries.C (M : ℂ) * qW g₁) * h₂

theorem specW_mul {X' Y' : LaurentSeries ℂ} {k₁ k₂ : ℤ} {f₁ g₁ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₁}
    {f₂ g₂ : ModularForm (ΓGL (CohCarrier.GammaH M H)) k₂} (h₁ : X' * qW g₁ = qW f₁) (h₂ : Y' * qW g₂ = qW f₂) :
    (X' * Y') * qW (g₁.mul g₂) = qW (f₁.mul f₂) := by
  rw [qW_mul, qW_mul]
  linear_combination (HahnSeries.C (M : ℂ) * X' * qW g₁) * h₂ + (HahnSeries.C (M : ℂ) * qW f₂) * h₁

theorem qW_cross {k k' : ℤ} {f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k}
    {F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k'} (h : (⇑f * ⇑G : ℍ → ℂ) = ⇑F * ⇑g) :
    qW f * qW G = qW F * qW g := by
  have h1 : (⇑(f.mul G) : ℍ → ℂ) ∣[k + k'] frickeGL M = ⇑(F.mul g) ∣[k' + k] frickeGL M := by
    rw [ModularForm.coe_mul, ModularForm.coe_mul, h, add_comm]
  rw [coe_mul_slash_frickeGL, coe_mul_slash_frickeGL] at h1
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h2 : (⇑((frickeForm f).mul (frickeForm G)) : ℍ → ℂ) = ⇑((frickeForm F).mul (frickeForm g)) := by
    funext τ
    have := congrFun h1 τ
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hM this
  have h3 := congrArg qC h2
  rwa [ModularForm.coe_mul, ModularForm.coe_mul, qC_mul hT', qC_mul hT'] at h3

variable (ι : Qb →+* ℂ)

def FrP (x : LBC (CohCarrier.GammaH M H)) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k), qC g ≠ 0 ∧
    coeffMap ι (x : LaurentSeries Qb) * qC g = qC f ∧
    ∃ y : LBC (CohCarrier.GammaH M H), coeffMap ι (y : LaurentSeries Qb) * qW g = qW f

variable {ι}

theorem FrP.apply_rep {x : LBC (CohCarrier.GammaH M H)} (hx : FrP ι x) :
    ∃ y : LBC (CohCarrier.GammaH M H), ∀ (k' : ℤ) (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k'),
      coeffMap ι (x : LaurentSeries Qb) * qC G = qC F →
        coeffMap ι (y : LaurentSeries Qb) * qW G = qW F := by
  obtain ⟨k, f, g, hg0, h, y, hy⟩ := hx
  refine ⟨y, fun k' F G h' => ?_⟩
  by_cases hG : qC G = 0
  · have hG0 : G = 0 := (qC_eq_zero_iff hT' G).mp hG
    have hF0 : F = 0 := (qC_eq_zero_iff hT' F).mp (by rw [← h', hG, mul_zero])
    subst hG0 hF0
    simp only [qW_zero, mul_zero]
  have hcross := qW_cross (cross_mul_eq hT' h h')
  apply mul_right_cancel₀ (qW_ne_zero hg0)
  rw [mul_assoc, mul_comm (qW G), ← hcross, ← mul_assoc, hy]

theorem FrP.add {x y : LBC (CohCarrier.GammaH M H)} (hx : FrP ι x) (hy : FrP ι y) : FrP ι (x + y) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, y₁, hy₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, y₂, hy₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul g₂ + g₁.mul f₂, g₁.mul g₂, ?_, ?_, y₁ + y₂, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_add, map_add]; exact rep_add hT' h₁ h₂
  · rw [IntermediateField.coe_add, map_add]; exact specW_add hy₁ hy₂

theorem FrP.mul {x y : LBC (CohCarrier.GammaH M H)} (hx : FrP ι x) (hy : FrP ι y) : FrP ι (x * y) := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁, y₁, hy₁⟩ := hx
  obtain ⟨k₂, f₂, g₂, hg₂, h₂, y₂, hy₂⟩ := hy
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, ?_, ?_, y₁ * y₂, ?_⟩
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_mul, map_mul]; exact rep_mul hT' h₁ h₂
  · rw [IntermediateField.coe_mul, map_mul]; exact specW_mul hy₁ hy₂

theorem FrP.zero : FrP ι (0 : LBC (CohCarrier.GammaH M H)) := by
  refine ⟨0, 0, 1, ?_, ?_, 0, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · simp [qC_zero]
  · rw [IntermediateField.coe_zero, map_zero, zero_mul, qW_zero]

theorem FrP.inv {x : LBC (CohCarrier.GammaH M H)} (hx : FrP ι x) : FrP ι x⁻¹ := by
  obtain ⟨k, f, g, hg, h, y, hy⟩ := hx
  by_cases hf : qC f = 0
  · have hx0 : x = 0 := by
      have : coeffMap ι (x : LaurentSeries Qb) = 0 := by
        rw [hf] at h; exact (mul_eq_zero.mp h).resolve_right hg
      exact Subtype.ext (coeffMap_injective ι (by rw [this, IntermediateField.coe_zero, map_zero]))
    rw [hx0, _root_.inv_zero]
    exact FrP.zero
  refine ⟨k, g, f, hf, ?_, y⁻¹, ?_⟩
  · rw [IntermediateField.coe_inv, map_inv₀]; exact rep_inv h hf
  · rw [IntermediateField.coe_inv, map_inv₀]
    exact rep_inv (f := frickeForm f) (g := frickeForm g) hy (qW_ne_zero hf)

theorem frP_algebraMap (c : Qb) : FrP ι (algebraMap Qb (LBC (CohCarrier.GammaH M H)) c) := by
  have hc : ((algebraMap Qb (LBC (CohCarrier.GammaH M H)) c : LBC (CohCarrier.GammaH M H)) :
      LaurentSeries Qb) = HahnSeries.C c := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  refine ⟨0, ModularForm.const (ι c), 1, ?_, ?_, algebraMap Qb (LBC (CohCarrier.GammaH M H)) c, ?_⟩
  · rw [qC_one_form]; exact one_ne_zero
  · rw [qC_one_form, mul_one, qC_const hT', hc, coeffMap_C]
  · rw [hc, coeffMap_C, qW_one, qW_const, ← map_mul]

theorem frP_gen {k : ℤ} (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    FrP ι (gen f g hf hg hg0) := by
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  refine ⟨k, f, g, hg', gen_rep ι f g hf hg hg0, ?_⟩
  obtain ⟨uf, huf⟩ := exists_rep_slash_frickeGL ι f g hf hg hg0
  obtain ⟨ug, hug⟩ := exists_rep_slash_frickeGL ι g g hg hg hg0
  have hug0 : coeffMap ι (ug : LaurentSeries Qb) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hug
    exact qW_ne_zero hg' hug.symm
  refine ⟨uf * ug⁻¹, ?_⟩
  rw [IntermediateField.coe_mul, IntermediateField.coe_inv, map_mul, map_inv₀, qW_def, ← hug,
    mul_assoc, inv_mul_cancel_left₀ hug0, huf, qW_def]

theorem frP_all (x : LBC (CohCarrier.GammaH M H)) : FrP ι x := by
  obtain ⟨z, hz⟩ := x
  induction hz using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_ratios_of_mem hT' hy
      exact frP_gen f g hf hg hg0
  | algebraMap a =>
      have e : (algebraMap Qb (LBC (CohCarrier.GammaH M H)) a : LBC (CohCarrier.GammaH M H)) =
          ⟨algebraMap Qb (LaurentSeries Qb) a, IntermediateField.algebraMap_mem _ a⟩ :=
        Subtype.ext (IntermediateField.coe_algebraMap_apply _ a)
      rw [← e]; exact frP_algebraMap a
  | add x y hx hy px py =>
      have e : ((⟨x, hx⟩ + ⟨y, hy⟩ : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H)) =
          ⟨x + y, add_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_add _ _ _)
      rw [← e]; exact FrP.add px py
  | inv x hx px =>
      have e : ((⟨x, hx⟩ : LBC (CohCarrier.GammaH M H))⁻¹ : LBC (CohCarrier.GammaH M H)) = ⟨x⁻¹, inv_mem hx⟩ :=
        Subtype.ext (IntermediateField.coe_inv _ _)
      rw [← e]; exact FrP.inv px
  | mul x y hx hy px py =>
      have e : ((⟨x, hx⟩ * ⟨y, hy⟩ : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H)) =
          ⟨x * y, mul_mem hx hy⟩ := Subtype.ext (IntermediateField.coe_mul _ _ _)
      rw [← e]; exact FrP.mul px py

end FrickeQ

section Construction

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ι : Qb →+* ℂ)

theorem exists_transport (x : LBC (CohCarrier.GammaH M H)) :
    ∃ y : LBC (CohCarrier.GammaH M H), ∀ (k : ℤ) (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k),
      coeffMap ι (x : LaurentSeries Qb) * qC G = qC F →
        coeffMap ι (y : LaurentSeries Qb) * qW G = qW F :=
  (frP_all (ι := ι) x).apply_rep

irreducible_def wfun (x : LBC (CohCarrier.GammaH M H)) : LBC (CohCarrier.GammaH M H) :=
  (exists_transport ι x).choose

theorem wfun_spec (x : LBC (CohCarrier.GammaH M H)) (k : ℤ)
    (F G : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (h : coeffMap ι (x : LaurentSeries Qb) * qC G = qC F) :
    coeffMap ι ((wfun ι x : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) * qW G = qW F := by
  rw [wfun_def]
  exact (exists_transport ι x).choose_spec k F G h

variable {ι}

theorem wfun_unique {x y : LBC (CohCarrier.GammaH M H)} {k : ℤ}
    {f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k} (hg : qC g ≠ 0)
    (h : coeffMap ι (x : LaurentSeries Qb) * qC g = qC f)
    (hy : coeffMap ι (y : LaurentSeries Qb) * qW g = qW f) : wfun ι x = y := by
  have h1 := wfun_spec ι x k f g h
  rw [← hy] at h1
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ (qW_ne_zero hg) h1))

theorem exists_rep (x : LBC (CohCarrier.GammaH M H)) :
    ∃ (k : ℤ) (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k), qC g ≠ 0 ∧
      coeffMap ι (x : LaurentSeries Qb) * qC g = qC f := by
  obtain ⟨k, f, g, hg, h, -⟩ := frP_all (ι := ι) x
  exact ⟨k, f, g, hg, h⟩

theorem wfun_add (x y : LBC (CohCarrier.GammaH M H)) : wfun ι (x + y) = wfun ι x + wfun ι y := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁⟩ := exists_rep (ι := ι) x
  obtain ⟨k₂, f₂, g₂, hg₂, h₂⟩ := exists_rep (ι := ι) y
  refine wfun_unique (f := f₁.mul g₂ + g₁.mul f₂) (g := g₁.mul g₂) ?_ ?_ ?_
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_add, map_add]; exact rep_add hT' h₁ h₂
  · rw [IntermediateField.coe_add, map_add]
    exact specW_add (wfun_spec ι x k₁ f₁ g₁ h₁) (wfun_spec ι y k₂ f₂ g₂ h₂)

theorem wfun_mul (x y : LBC (CohCarrier.GammaH M H)) : wfun ι (x * y) = wfun ι x * wfun ι y := by
  obtain ⟨k₁, f₁, g₁, hg₁, h₁⟩ := exists_rep (ι := ι) x
  obtain ⟨k₂, f₂, g₂, hg₂, h₂⟩ := exists_rep (ι := ι) y
  refine wfun_unique (f := f₁.mul f₂) (g := g₁.mul g₂) ?_ ?_ ?_
  · rw [ModularForm.coe_mul, qC_mul hT']; exact mul_ne_zero hg₁ hg₂
  · rw [IntermediateField.coe_mul, map_mul]; exact rep_mul hT' h₁ h₂
  · rw [IntermediateField.coe_mul, map_mul]
    exact specW_mul (wfun_spec ι x k₁ f₁ g₁ h₁) (wfun_spec ι y k₂ f₂ g₂ h₂)

theorem wfun_algebraMap (c : Qb) :
    wfun ι (algebraMap Qb (LBC (CohCarrier.GammaH M H)) c) = algebraMap Qb (LBC (CohCarrier.GammaH M H)) c := by
  have hc : ((algebraMap Qb (LBC (CohCarrier.GammaH M H)) c : LBC (CohCarrier.GammaH M H)) :
      LaurentSeries Qb) = HahnSeries.C c := by
    rw [HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]; rfl
  refine wfun_unique (f := ModularForm.const (ι c)) (g := 1) ?_ ?_ ?_
  · rw [qC_one_form]; exact one_ne_zero
  · rw [qC_one_form, mul_one, qC_const hT', hc, coeffMap_C]
  · rw [hc, coeffMap_C, qW_one, qW_const, ← map_mul]

variable (ι)

def wAlg : LBC (CohCarrier.GammaH M H) →ₐ[Qb] LBC (CohCarrier.GammaH M H) where
  toFun := wfun ι
  map_one' := by rw [← map_one (algebraMap Qb (LBC (CohCarrier.GammaH M H))), wfun_algebraMap]
  map_mul' := wfun_mul
  map_zero' := by rw [← map_zero (algebraMap Qb (LBC (CohCarrier.GammaH M H))), wfun_algebraMap]
  map_add' := wfun_add
  commutes' := wfun_algebraMap

theorem wAlg_comp_wAlg : (wAlg ι).comp (wAlg ι) = AlgHom.id Qb (LBC (CohCarrier.GammaH M H)) := by
  refine algHom_ext_gen hT' fun k f g pf pg hf hg hg0 => ?_
  change wfun ι (wfun ι (gen f g hf hg hg0)) = gen f g hf hg hg0
  set x₀ := gen f g hf hg hg0 with hx₀
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0
  have h1 := wfun_spec ι x₀ k f g h0
  rw [qW_eq_qC_frickeForm, qW_eq_qC_frickeForm] at h1
  have h2 := wfun_spec ι (wfun ι x₀) k (frickeForm f) (frickeForm g) h1
  rw [qW_def, qW_def, coe_frickeForm, coe_frickeForm, slash_frickeGL_frickeGL, slash_frickeGL_frickeGL,
    qC_const_mul hT', qC_const_mul hT', ← mul_assoc, mul_comm (coeffMap ι _), mul_assoc] at h2
  have h3 := mul_left_cancel₀ ((map_ne_zero_iff _ HahnSeries.C_injective).mpr
    (frickeSqConst_ne_zero (M := M) k)) h2
  rw [← h0] at h3
  exact Subtype.ext (coeffMap_injective ι (mul_right_cancel₀ hg' h3))

theorem wAlg_wAlg (x : LBC (CohCarrier.GammaH M H)) : wAlg ι (wAlg ι x) = x := by
  have h := AlgHom.congr_fun (wAlg_comp_wAlg ι) x
  rwa [AlgHom.comp_apply, AlgHom.id_apply] at h

def wEquiv : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H) :=
  AlgEquiv.ofAlgHom (wAlg ι) (wAlg ι) (AlgHom.ext (wAlg_wAlg ι)) (AlgHom.ext (wAlg_wAlg ι))

theorem wEquiv_frickeSpec (x : LBC (CohCarrier.GammaH M H)) (k : ℤ)
    (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    (h : coeffMap ι (x : LaurentSeries Qb) * qC g = qC f) :
    coeffMap ι ((wEquiv ι x : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) *
        qC (⇑g ∣[k] frickeGL M) = qC (⇑f ∣[k] frickeGL M) :=
  wfun_spec ι x k f g h

end Construction

section GaloisLaw

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (ι : Qb →+* ℂ)

theorem exists_series_slash_frickeGL {k : ℤ} (f : ModularForm (ΓGL (CohCarrier.GammaH M H)) k)
    {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf)
    (σ : Qb ≃ₐ[ℚ] Qb) (c : ℕ) (hc : c.Coprime M) (hσ : ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγc : ((γ 0 0 : ℤ) : ZMod M) = (ZMod.unitOfCoprime c hc : ZMod M)) :
    ∃ A : LaurentSeries Qb, coeffMap ι A = qC (⇑f ∣[k] frickeGL M) ∧
      coeffMap (ι.comp (σ.symm : Qb →+* Qb)) A = qC ((⇑f ∣[k] frickeGL M) ∣[k] (γ : GL (Fin 2) ℝ)) := by
  have hfrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 ⇑(res1 f)).coeff n = (r : ℂ) := fun n =>
    ⟨((PowerSeries.coeff n pf : ℤ) : ℚ), by rw [coe_res1, ← hf.coeff n, Rat.cast_intCast]⟩
  obtain ⟨a, ha1, ha2⟩ :=
    ModularCurve.exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0 M (res1 f) hfrat ι
      (frickeGL M) val_frickeGL
  simp only [coe_res1] at ha1 ha2

  have hγd : ((γ 1 1 : ℤ) : ZMod M) = (invExp c hc : ℕ) := by
    rw [natCast_invExp]
    have hda := CohCarrier.Gamma0_d_mul_a M ⟨γ, hγ⟩
    simp only at hda
    rw [hγc] at hda
    exact Units.eq_inv_of_mul_eq_one_right hda
  refine ⟨ofPowerSeries ℤ Qb (PowerSeries.mk a), ?_, ?_⟩
  · rw [coeffMap_ofPowerSeries, qC]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, ha1]
  · rw [coeffMap_ofPowerSeries, qC]
    congr 1
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, RingHom.comp_apply, RingHom.coe_coe,
      ha2 σ.symm (invExp c hc) (symm_apply_eq_pow hc hσ) γ hγ hγd n]

theorem galois_gen (σ : Qb ≃ₐ[ℚ] Qb) (c : ℕ) (hc : c.Coprime M)
    (hσ : ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c)
    {D : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
    (hD : IsDiamondAutHBar M H (ZMod.unitOfCoprime c hc) D)
    {k : ℤ} (f g : ModularForm (ΓGL (CohCarrier.GammaH M H)) k) {pf pg : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    (arithmeticGalois (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) σ)⁻¹ • wEquiv ι (gen f g hf hg hg0) =
      D (wEquiv ι (gen f g hf hg hg0)) := by
  obtain ⟨γ, hγ, hγc⟩ := exists_gamma0_upperLeft (M := M) (ZMod.unitOfCoprime c hc)
  set x₀ := gen f g hf hg hg0 with hx₀
  have hg' : qC g ≠ 0 := qC_ne_zero_of_witness hg hg0
  have h0 : coeffMap ι (x₀ : LaurentSeries Qb) * qC g = qC f := gen_rep ι f g hf hg hg0

  have h1 : coeffMap ι ((wEquiv ι x₀ : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) *
      qC (frickeForm g) = qC (frickeForm f) := wfun_spec ι x₀ k f g h0
  have hG : qC (frickeForm g) ≠ 0 := qC_frickeForm_ne_zero hg'
  have hGγ : qC (slashForm γ hγ (frickeForm g)) ≠ 0 := fun h => slashForm_ne_zero γ hγ
    (fun h' => hG ((qC_eq_zero_iff hT' _).mpr h')) ((qC_eq_zero_iff hT' _).mp h)

  have hDside := (diaP_all (ι := ι) (D := D) (γ := γ) (hγ := hγ) hD hγc (wEquiv ι x₀)).apply_rep
    (frickeForm f) (frickeForm g) h1

  obtain ⟨Af, hAf, hAf'⟩ := exists_series_slash_frickeGL ι f hf σ c hc hσ γ hγ hγc
  obtain ⟨Ag, hAg, hAg'⟩ := exists_series_slash_frickeGL ι g hg σ c hc hσ γ hγ hγc
  have h2 : ((wEquiv ι x₀ : LBC (CohCarrier.GammaH M H)) : LaurentSeries Qb) * Ag = Af := by
    apply coeffMap_injective ι
    rw [map_mul, hAg, hAf, ← coe_frickeForm, ← coe_frickeForm, h1]
  have h3 := congrArg (coeffMap (ι.comp (σ.symm : Qb →+* Qb))) h2
  rw [map_mul, hAg', hAf', ← coe_frickeForm, ← coe_frickeForm, ← coe_slashForm γ hγ,
    ← coe_slashForm γ hγ] at h3

  rw [← hDside] at h3
  have h4 := mul_right_cancel₀ hGγ h3
  refine Subtype.ext (coeffMap_injective ι ?_)
  rw [← h4, ← coeffMap_coeffMap]
  rfl

def conjAlgHom {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (w : F ≃ₐ[K] F) : F →ₐ[K] F where
  toFun x := g⁻¹ • w (g • x)
  map_one' := by rw [smul_one, map_one, smul_one]
  map_mul' x y := by rw [smul_mul', map_mul, smul_mul']
  map_zero' := by rw [smul_zero, map_zero, smul_zero]
  map_add' x y := by rw [smul_add, map_add, smul_add]
  commutes' a := by
    rw [SemilinearAut.smul_def g, SemilinearAut.commutes, AlgEquiv.commutes, SemilinearAut.smul_def,
      SemilinearAut.commutes, SemilinearAut.baseAut_inv, RingEquiv.symm_apply_apply]

theorem conjAlgHom_apply {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    (w : F ≃ₐ[K] F) (x : F) : conjAlgHom g w x = g⁻¹ • w (g • x) := rfl

theorem galois_law (σ : Qb ≃ₐ[ℚ] Qb) (c : ℕ) (hc : c.Coprime M)
    (hσ : ∀ ζ : Qb, ζ ^ M = 1 → σ ζ = ζ ^ c)
    {D : LBC (CohCarrier.GammaH M H) ≃ₐ[Qb] LBC (CohCarrier.GammaH M H)}
    (hD : IsDiamondAutHBar M H (ZMod.unitOfCoprime c hc) D) (x : LBC (CohCarrier.GammaH M H)) :
    wEquiv ι (arithmeticGalois (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) σ • x) =
      arithmeticGalois (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) σ • D (wEquiv ι x) := by

  have hφ : conjAlgHom (arithmeticGalois (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) σ) (wEquiv ι) =
      D.toAlgHom.comp (wEquiv ι).toAlgHom := by
    refine algHom_ext_gen hT' fun k f g pf pg hf hg hg0 => ?_
    simp only [conjAlgHom_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom]
    have hfix : arithmeticGalois (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) σ • gen f g hf hg hg0 =
        gen f g hf hg hg0 :=
      Subtype.ext (ModularCurve.coeffMap_coeffEmb σ _)
    rw [hfix]
    exact galois_gen ι σ c hc hσ hD f g hf hg hg0
  have hx := AlgHom.congr_fun hφ x
  simp only [conjAlgHom_apply, AlgHom.comp_apply, AlgEquiv.coe_algHom] at hx
  rw [← hx, smul_inv_smul]

end GaloisLaw

end A2FRE
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.A2FRE"

open scoped MatrixGroups ModularForm in
open A2FRE ModularCurve in
theorem solution (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ∀ d : (ZMod M)ˣ, ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H, ModularCurve.IsDiamondAutHBar M H d σ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar M H,
      (∀ (x : ModularCurve.xHFunctionFieldBar M H) (k : ℤ)
          (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
          ModularCurve.coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
          ModularCurve.coeffMap ι ((w x : ModularCurve.xHFunctionFieldBar M H) :
                LaurentSeries (AlgebraicClosure ℚ)) *
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W))) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x : ModularCurve.xHFunctionFieldBar M H,
            w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
              ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
                ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x)) := by
  obtain rfl : W = frickeGL M := eq_frickeGL hW
  refine ⟨wEquiv (H := H) ι, fun x k f g h => wEquiv_frickeSpec ι x k f g h, fun σ c hc hσ x => ?_⟩
  exact galois_law ι σ c hc hσ (isDiamondAutHBar_diamondAutHBar (hin _)) x

end
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul.A2FRE"

end S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul (solution)
