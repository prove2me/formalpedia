-- Prove2me | solution 1 for ModularCurve.diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/358b1eb2-f368-5fd8-b49d-fc469aa81809

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0
import Theorems.Thm_ModularForm_exists_coe_eq_slash_of_mem_gamma0_gammaH
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open scoped MatrixGroups ModularForm
p2m_open "ModularCurve P2MW.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply.ModularCurve CongruenceSubgroup HahnSeries"

namespace ModularCurve
p2m_export "ModularCurve" "IsDiamondAutHBar diamondAutHBar isDiamondAutHBar_diamondAutHBar Gamma1_le_GammaH xHFunctionField xHFunctionFieldBar restrictForm coe_restrictForm IsIntegralQExp intSeriesC intSeriesC_zero intSeriesC_mul div_mem_qExpFunctionFieldC coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange coeffMap_intSeriesC exists_algEquiv_laurentBaseChange_cover exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0"
namespace DiaFFBody
p2m_open "ModularCurve"

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem gamma0_diag (γ : Gamma0 M) :
    (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) * (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe (γ : SL(2, ℤ))
  rw [Matrix.det_fin_two] at hdet
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have := congrArg (Int.cast : ℤ → ZMod M) hdet
  push_cast at this
  rw [h10, mul_zero, sub_zero] at this
  exact this

theorem mul_inv_mem_Gamma1 (γ γ' : Gamma0 M)
    (h : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (((γ' : SL(2, ℤ)) 0 0 : ℤ) : ZMod M)) :
    ((γ * γ'⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ Gamma1 M := by
  have hd := gamma0_diag γ
  have hd' := gamma0_diag γ'
  have h10 : (((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have h10' : (((γ' : SL(2, ℤ)) 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ'.2
  have hmul : ((γ * γ'⁻¹ : Gamma0 M) : SL(2, ℤ)) = (γ : SL(2, ℤ)) * (γ' : SL(2, ℤ))⁻¹ := rfl
  rw [Gamma1_mem, hmul]
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast
  rw [h10, h10']
  refine ⟨?_, ?_, by ring⟩
  · rw [h]; linear_combination hd'
  · rw [← h]; linear_combination hd

theorem Gamma1_le_GammaH : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  have hA' := hA
  rw [Gamma1_mem] at hA'
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2
  refine CohCarrier.mem_GammaH_iff.mpr ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hA'.2.1
  rw [h1]
  exact one_mem H

theorem T_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H :=
  Gamma1_le_GammaH (by rw [Gamma1_mem]; simp [ModularGroup.T])

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]; simp [ModularGroup.T]

theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]; exact AddSubgroup.mem_zmultiples _

theorem intSeriesC_C_mul (L : Type*) [Field L] (z : ℤ) (p : PowerSeries ℤ) :
    intSeriesC L (PowerSeries.C z * p) = (z : L) • intSeriesC L p := by
  rw [intSeriesC_mul]
  have : intSeriesC L (PowerSeries.C z) = HahnSeries.C (z : L) := by
    simp [intSeriesC]
  rw [this, HahnSeries.C_mul_eq_smul]

theorem isIntegralQExp_pow_smul {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {w : ℤ}
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w) {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (c : ℕ) :
    IsIntegralQExp (((M : ℂ) ^ c) • (⇑f : UpperHalfPlane → ℂ)) (PowerSeries.C ((M : ℤ) ^ c) * pf) := by
  unfold IsIntegralQExp at hf ⊢
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods hT) ((M : ℂ) ^ c) f, map_mul, PowerSeries.map_C, hf,
    PowerSeries.smul_eq_C_mul]
  simp

theorem coe_real_pow_smul {Γ : Subgroup SL(2, ℤ)} {w : ℤ} (φ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w) (c : ℕ) :
    (⇑(((M : ℝ) ^ c) • φ) : UpperHalfPlane → ℂ) = ((M : ℂ) ^ c) • (⇑φ : UpperHalfPlane → ℂ) := by
  ext τ
  rw [ModularForm.coe_smul, Pi.smul_apply, Pi.smul_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  rfl

theorem intSeriesC_ne_zero_of_ne_zero {w : ℤ} (φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp φ p) (hφ : (⇑φ : UpperHalfPlane → ℂ) ≠ 0) : intSeriesC ℚ p ≠ 0 := by
  intro h0
  apply hφ
  have hp0 : p = 0 := by
    ext n
    have := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h0
    simp only [intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map, HahnSeries.coeff_zero,
      eq_intCast, Int.cast_eq_zero] at this
    simpa using this
  have hq : UpperHalfPlane.qExpansion 1 ⇑φ = 0 := by
    unfold IsIntegralQExp at hp
    rw [← hp, hp0, map_zero]
  have := (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods T_mem_GammaH) φ).mp hq
  rw [this]
  rfl

theorem intSeriesC_eq_zero_of_eq_zero {w : ℤ} (φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp φ p) (hφ : (⇑φ : UpperHalfPlane → ℂ) = 0) : intSeriesC ℚ p = 0 := by
  have hp0 : p.map (Int.castRingHom ℂ) = 0 := by
    unfold IsIntegralQExp at hp
    rw [hp, hφ, UpperHalfPlane.qExpansion_zero]
  have : p = 0 := by
    apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
    rw [hp0, map_zero]
  rw [this, intSeriesC_zero]

theorem exists_integral_smul_slash {w : ℤ} (φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp φ p) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    ∃ (n : ℕ) (Φ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w) (P : PowerSeries ℤ)
      (Φσ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w),
      IsIntegralQExp Φ P ∧ (⇑Φσ : UpperHalfPlane → ℂ) = ((⇑φ : UpperHalfPlane → ℂ) ∣[w] γ) ∧
      (⇑Φ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ n) • ((⇑φ : UpperHalfPlane → ℂ) ∣[w] (γ : GL (Fin 2) ℝ)) := by
  have hle : ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ ((CohCarrier.GammaH M H) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.map_mono Gamma1_le_GammaH
  obtain ⟨n, φ₁, P, hφ₁, hφ₁eq⟩ := ModularCurve.exists_isIntegralQExp_level_pow_smul_slash_of_mem_Gamma0 M
    (restrictForm hle φ) (by rw [coe_restrictForm]; exact hp) γ hγ
  rw [coe_restrictForm] at hφ₁eq
  obtain ⟨Φσ, hΦσ⟩ := ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH M H φ γ hγ
  refine ⟨n, ((M : ℝ) ^ n) • Φσ, P, Φσ, ?_, hΦσ, ?_⟩
  · rw [coe_real_pow_smul, hΦσ, ← hφ₁eq]; exact hφ₁
  · rw [coe_real_pow_smul, hΦσ, ModularForm.SL_slash]

theorem intSeriesC_complex_eq {w : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} (φ : ModularForm Γ w) {p : PowerSeries ℤ} (hp : IsIntegralQExp φ p) :
    intSeriesC ℂ p = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑φ) := by
  unfold IsIntegralQExp at hp
  rw [intSeriesC, hp]

theorem ofPowerSeries_smul (c : ℂ) (P : PowerSeries ℂ) :
    HahnSeries.ofPowerSeries ℤ ℂ (c • P) = c • HahnSeries.ofPowerSeries ℤ ℂ P := by
  rw [PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

theorem intSeriesC_eq_smul_of_coe_eq_smul {w : ℤ} (Φ Φσ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w)
    {P : PowerSeries ℤ} (hP : IsIntegralQExp Φ P) (c : ℂ) (h : (⇑Φ : UpperHalfPlane → ℂ) = c • (⇑Φσ : UpperHalfPlane → ℂ)) :
    intSeriesC ℂ P = c • HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Φσ) := by
  rw [intSeriesC_complex_eq Φ hP, h, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods T_mem_GammaH) c Φσ,
    ofPowerSeries_smul]

theorem ofPowerSeries_qExpansion_ne_zero {w : ℤ} (g Gσ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) w)
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ))
    (hGσ : (⇑Gσ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[w] γ)) :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Gσ) ≠ 0 := by
  intro h0
  have hq : UpperHalfPlane.qExpansion 1 ⇑Gσ = 0 := by
    rw [← (HahnSeries.ofPowerSeries ℤ ℂ).map_zero] at h0
    exact HahnSeries.ofPowerSeries_injective h0
  have hG : (⇑Gσ : UpperHalfPlane → ℂ) = 0 := by
    have := (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods T_mem_GammaH) Gσ).mp hq
    rw [this]; rfl
  have hg' : (⇑g : UpperHalfPlane → ℂ) = 0 := by
    have e : (⇑g : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[w] γ) ∣[w] γ⁻¹ := by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
    rw [e, ← hGσ, hG, SlashAction.zero_slash]
  exact hg0 (intSeriesC_eq_zero_of_eq_zero g hg hg')

end ModularCurve.DiaFFBody

open ModularCurve.DiaFFBody in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ρ : Gamma0 M →* RingAut ↥(xHFunctionField M H))
    (hρH : ∀ γ : Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1)
    (hρslash : ∀ (γ : Gamma0 M) {k : ℤ}
      (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
      {pf pg pf₁ pg₁ : PowerSeries ℤ} (c : ℂ) (_ : c ≠ 0)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
      (_ : IsIntegralQExp f₁ pf₁) (_ : IsIntegralQExp g₁ pg₁)
      (_ : (⇑f₁ : UpperHalfPlane → ℂ) = c • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (_ : (⇑g₁ : UpperHalfPlane → ℂ) = c • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ)))
      (hg0 : intSeriesC ℚ pg ≠ 0) (_ : intSeriesC ℚ pg₁ ≠ 0),
      ((ρ γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ : ↥(xHFunctionField M H)) :
          LaurentSeries ℚ) = intSeriesC ℚ pf₁ / intSeriesC ℚ pg₁)
    (d : (ZMod M)ˣ) (γ : Gamma0 M) (hγ : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    (x : ↥(xHFunctionField M H)) :
    ((diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) x.2⟩ : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((ρ γ x : ↥(xHFunctionField M H)) : LaurentSeries ℚ) := by

  obtain ⟨τ, hτ⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ) (xHFunctionField M H) (ρ γ)

  have hpin : ∀ (σ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)), IsDiamondAutHBar M H d σ →
      ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
        (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
        (Fσ Gσ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
        (hFσ : (⇑Fσ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
        (hGσ : (⇑Gσ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ)))),
        ∃ y : LaurentSeries ℚ,
          ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ :
                ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
          coeffMap (algebraMap ℚ ℂ) y =
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Fσ) /
              HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑Gσ) := by
    intro σ hσ k f g pf pg hf hg hg0 Fσ Gσ hFσ hGσ
    obtain ⟨y, -, hy1, hy2⟩ := hσ k f g pf pg hf hg hg0 (γ : SL(2, ℤ)) γ.2 hγ
    refine ⟨y, hy1, ?_⟩
    have hB := ofPowerSeries_qExpansion_ne_zero g Gσ hg hg0 (γ : SL(2, ℤ)) hGσ
    rw [← ModularForm.SL_slash, ← ModularForm.SL_slash, ← hGσ, ← hFσ] at hy2
    exact (eq_div_iff hB).mpr hy2

  have hA : IsDiamondAutHBar M H d τ := by
    intro k f g pf pg hf hg hg0 γ' hγ'0 hγ'd
    set γ'' : Gamma0 M := ⟨γ', hγ'0⟩ with hγ''
    have hρeq : ρ γ'' = ρ γ := by
      have hmem : ((γ * γ''⁻¹ : Gamma0 M) : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
        Gamma1_le_GammaH (mul_inv_mem_Gamma1 γ γ'' (by rw [hγ]; exact hγ'd.symm))
      have h1 := hρH (γ * γ''⁻¹) hmem
      rw [map_mul, map_inv, mul_inv_eq_one] at h1
      exact h1.symm
    obtain ⟨a, F₁', P₁, Fσ, hF₁', hFσ, hF₁'eq⟩ := exists_integral_smul_slash f hf γ' hγ'0
    obtain ⟨b, G₁', Q₁, Gσ, hG₁', hGσ, hG₁'eq⟩ := exists_integral_smul_slash g hg γ' hγ'0
    set F₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k := ((M : ℝ) ^ b) • F₁' with hF₁def
    set G₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k := ((M : ℝ) ^ a) • G₁' with hG₁def
    have hF₁ : IsIntegralQExp F₁ (PowerSeries.C ((M : ℤ) ^ b) * P₁) := by
      rw [hF₁def, coe_real_pow_smul]; exact isIntegralQExp_pow_smul T_mem_GammaH F₁' hF₁' b
    have hG₁ : IsIntegralQExp G₁ (PowerSeries.C ((M : ℤ) ^ a) * Q₁) := by
      rw [hG₁def, coe_real_pow_smul]; exact isIntegralQExp_pow_smul T_mem_GammaH G₁' hG₁' a
    have hc0 : ((M : ℂ) ^ (a + b)) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne M))
    have hslF : (⇑F₁ : UpperHalfPlane → ℂ) =
        ((M : ℂ) ^ (a + b)) • ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((γ'' : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
      rw [hF₁def, coe_real_pow_smul, hF₁'eq, smul_smul, ← _root_.pow_add, add_comm]
    have hslG : (⇑G₁ : UpperHalfPlane → ℂ) =
        ((M : ℂ) ^ (a + b)) • ((⇑g : UpperHalfPlane → ℂ) ∣[k] ((γ'' : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
      rw [hG₁def, coe_real_pow_smul, hG₁'eq, smul_smul, ← _root_.pow_add]
    have hF₁σ : (⇑F₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ (a + b)) • (⇑Fσ : UpperHalfPlane → ℂ) := by
      rw [hslF, hFσ, ModularForm.SL_slash]
    have hG₁σ : (⇑G₁ : UpperHalfPlane → ℂ) = ((M : ℂ) ^ (a + b)) • (⇑Gσ : UpperHalfPlane → ℂ) := by
      rw [hslG, hGσ, ModularForm.SL_slash]
    have hB := ofPowerSeries_qExpansion_ne_zero g Gσ hg hg0 γ' hGσ
    have hG₁0 : intSeriesC ℚ (PowerSeries.C ((M : ℤ) ^ a) * Q₁) ≠ 0 := by
      intro h0
      have := congrArg (coeffMap (algebraMap ℚ ℂ)) h0
      rw [coeffMap_intSeriesC, map_zero, intSeriesC_eq_smul_of_coe_eq_smul G₁ Gσ hG₁ _ hG₁σ] at this
      exact (smul_ne_zero hc0 hB) this
    have hyq := hρslash γ'' f g F₁ G₁ ((M : ℂ) ^ (a + b)) hc0 hf hg hF₁ hG₁ hslF hslG hg0 hG₁0
    rw [hρeq] at hyq
    refine ⟨_, (ρ γ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩).2,
      hτ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩, ?_⟩
    rw [hyq, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC,
      intSeriesC_eq_smul_of_coe_eq_smul F₁ Fσ hF₁ _ hF₁σ, intSeriesC_eq_smul_of_coe_eq_smul G₁ Gσ hG₁ _ hG₁σ,
      ← ModularForm.SL_slash, ← ModularForm.SL_slash, ← hGσ, ← hFσ,
      ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, mul_div_mul_left _ _ (HahnSeries.C_ne_zero hc0),
      div_mul_cancel₀ _ hB]

  have hD : IsDiamondAutHBar M H d (diamondAutHBar M H d) := isDiamondAutHBar_diamondAutHBar ⟨τ, hA⟩

  suffices key : ∀ (y : LaurentSeries ℚ) (hy : y ∈ xHFunctionField M H),
      diamondAutHBar M H d ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ =
        τ ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ by
    rw [key x.1 x.2]
    exact hτ x
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
      obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hy
      obtain ⟨Fσ, hFσ⟩ := ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH M H f (γ : SL(2, ℤ)) γ.2
      obtain ⟨Gσ, hGσ⟩ := ModularForm.exists_coe_eq_slash_of_mem_gamma0_gammaH M H g (γ : SL(2, ℤ)) γ.2
      obtain ⟨y₁, hy₁, hy₁'⟩ := hpin _ hD k f g pf pg hf hg hg0 Fσ Gσ hFσ hGσ
      obtain ⟨y₂, hy₂, hy₂'⟩ := hpin _ hA k f g pf pg hf hg hg0 Fσ Gσ hFσ hGσ
      have hyy : y₁ = y₂ := (coeffMap (algebraMap ℚ ℂ)).injective (by rw [hy₁', hy₂'])
      apply Subtype.ext
      change ((diamondAutHBar M H d _ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((τ _ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
      rw [hy₁, hy₂, hyy]
  | algebraMap c =>
      have e : (⟨coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (IntermediateField.algebraMap_mem _ c)⟩ : ↥(xHFunctionFieldBar M H)) =
          algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (algebraMap ℚ (AlgebraicClosure ℚ) c) := by
        apply Subtype.ext
        change coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c) =
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (algebraMap ℚ (AlgebraicClosure ℚ) c)
        rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single]
      rw [e, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z hy hz ihy ihz =>
      have e : (⟨coeffEmb (AlgebraicClosure ℚ) (y + z), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (IntermediateField.add_mem _ hy hz)⟩ : ↥(xHFunctionFieldBar M H)) =
          ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ +
          ⟨coeffEmb (AlgebraicClosure ℚ) z, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hz⟩ :=
        Subtype.ext (map_add _ _ _)
      rw [e, map_add, map_add, ihy, ihz]
  | inv y hy ihy =>
      have e : (⟨coeffEmb (AlgebraicClosure ℚ) y⁻¹, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (IntermediateField.inv_mem _ hy)⟩ : ↥(xHFunctionFieldBar M H)) =
          (⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ : ↥(xHFunctionFieldBar M H))⁻¹ :=
        Subtype.ext (map_inv₀ _ _)
      rw [e, map_inv₀, map_inv₀, ihy]
  | mul y z hy hz ihy ihz =>
      have e : (⟨coeffEmb (AlgebraicClosure ℚ) (y * z), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (IntermediateField.mul_mem _ hy hz)⟩ : ↥(xHFunctionFieldBar M H)) =
          ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩ *
          ⟨coeffEmb (AlgebraicClosure ℚ) z, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hz⟩ :=
        Subtype.ext (map_mul _ _ _)
      rw [e, map_mul, map_mul, ihy, ihz]

#print axioms solution

end S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
end P2MW
export P2MW.S_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply (solution)
