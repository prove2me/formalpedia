-- Prove2me | solution 1 for ModularCurve.exists_modularForm_eq_tsum_of_discreteTopology
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/83a051a7-1ae4-5b89-ac11-e0b63e3ba96e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology

set_option autoImplicit false

open UpperHalfPlane Complex MeasureTheory
open scoped MatrixGroups Topology Manifold ENNReal

namespace PoincareAux

noncomputable def term (k : ℤ) (φ : ℍ → ℂ) (γ : GL (Fin 2) ℝ) (τ : ℍ) : ℂ :=
  φ (γ • τ) * denom γ τ ^ (-k)

theorem σ_eq_self_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ)) (z : ℂ) :
    σ g z = z := by
  have hg' : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rwa [Matrix.GeneralLinearGroup.val_det_apply] at hg
  simp [σ, hg']

theorem slash_term (k : ℤ) (φ : ℍ → ℂ) (γ : GL (Fin 2) ℝ) {g : GL (Fin 2) ℝ}
    (hdg : Matrix.GeneralLinearGroup.det g = 1) :
    SlashAction.map k g (term k φ γ) = term k φ (γ * g) := by
  funext τ
  have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ) := by rw [hdg]; simp
  rw [ModularForm.slash_def]
  simp only [term, σ_eq_self_of_det_pos hdetpos, hdg, Units.val_one, abs_one, Complex.ofReal_one, one_zpow,
    mul_one]
  rw [mul_smul, denom_cocycle' γ g τ, σ_eq_self_of_det_pos hdetpos]
  have : smulAux g τ = g • τ := rfl
  rw [this, mul_zpow, mul_assoc]

noncomputable def poincareSIF (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] (k : ℤ) (φ : ℍ → ℂ) :
    SlashInvariantForm Γ k where
  toFun τ := ∑' γ : Γ, term k φ (γ : GL (Fin 2) ℝ) τ
  slash_action_eq' g hg := by
    have hdg : Matrix.GeneralLinearGroup.det g = 1 := Subgroup.HasDetOne.det_eq hg
    have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ) := by rw [hdg]; simp
    funext τ
    rw [ModularForm.slash_def]
    simp only [σ_eq_self_of_det_pos hdetpos, hdg, Units.val_one, abs_one, Complex.ofReal_one, one_zpow, mul_one]
    rw [← tsum_mul_right]
    have hterm : ∀ γ : Γ, term k φ (γ : GL (Fin 2) ℝ) (g • τ) * denom g τ ^ (-k) =
        term k φ ((γ * ⟨g, hg⟩ : Γ) : GL (Fin 2) ℝ) τ := by
      intro γ
      have := congrFun (slash_term k φ (γ : GL (Fin 2) ℝ) hdg) τ
      rw [ModularForm.slash_def] at this
      simp only [σ_eq_self_of_det_pos hdetpos, hdg, Units.val_one, abs_one, Complex.ofReal_one, one_zpow,
        mul_one] at this
      simpa [Subgroup.coe_mul] using this
    simp_rw [hterm]
    exact (Equiv.mulRight (⟨g, hg⟩ : Γ)).tsum_eq (fun γ : Γ => term k φ (γ : GL (Fin 2) ℝ) τ)

theorem mdifferentiable_tsum_term {Γ : Subgroup (GL (Fin 2) ℝ)}
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (k : ℤ) {φ : ℍ → ℂ} (hφ : MDiff φ)
    (hloc : ∀ τ₀ : ℍ, ∃ U : Set ℍ, IsOpen U ∧ τ₀ ∈ U ∧ ∃ u : ↥Γ → ℝ, Summable u ∧
      ∀ (γ : ↥Γ) (τ : ℍ), τ ∈ U → ‖term k φ (γ : GL (Fin 2) ℝ) τ‖ ≤ u γ) :
    MDiff (fun τ : ℍ => ∑' γ : ↥Γ, term k φ (γ : GL (Fin 2) ℝ) τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z₀ hz₀
  obtain ⟨U, hUo, hτU, u, hu, hbound⟩ := hloc ⟨z₀, hz₀⟩

  let V : Set ℂ := ((↑) : ℍ → ℂ) '' U
  have hVo : IsOpen V := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap U hUo
  have hz₀V : z₀ ∈ V := ⟨⟨z₀, hz₀⟩, hτU, rfl⟩
  have hVim : ∀ z ∈ V, 0 < z.im := by rintro z ⟨τ, _, rfl⟩; exact τ.im_pos
  have hVU : ∀ z (hz : z ∈ V), ofComplex z ∈ U := by
    rintro z ⟨τ, hτ, rfl⟩; rwa [ofComplex_apply]

  have hterm : ∀ γ : ↥Γ, DifferentiableOn ℂ (fun z : ℂ => term k φ (γ : GL (Fin 2) ℝ) (ofComplex z)) V := by
    intro γ
    have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ)) : ℝ) := by
      rw [hdet _ γ.2]; simp
    have h1 : DifferentiableOn ℂ ((fun τ : ℍ => φ ((γ : GL (Fin 2) ℝ) • τ)) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
      (UpperHalfPlane.mdifferentiable_iff).1 (hφ.comp (mdifferentiable_smul hdetpos))
    have h2 : DifferentiableOn ℂ (fun z : ℂ => denom (γ : GL (Fin 2) ℝ) z ^ (-k)) V := by
      refine DifferentiableOn.zpow ?_ (Or.inl ?_)
      · intro z _
        unfold denom
        fun_prop
      · intro z hz
        have := denom_ne_zero (γ : GL (Fin 2) ℝ) (ofComplex z)
        rwa [ofComplex_apply_of_im_pos (hVim z hz)] at this
    have h12 := (h1.mono (fun z hz => hVim z hz)).mul h2
    refine h12.congr ?_
    intro z hz
    show term k φ _ (ofComplex z) = φ (_ • ofComplex z) * denom _ z ^ (-k)
    simp only [term]
    rw [ofComplex_apply_of_im_pos (hVim z hz)]
  have hV : DifferentiableOn ℂ (fun z : ℂ => ∑' γ : ↥Γ, term k φ (γ : GL (Fin 2) ℝ) (ofComplex z)) V :=
    Complex.differentiableOn_tsum_of_summable_norm hu hterm hVo (fun γ z hz => hbound γ _ (hVU z hz))
  exact ((hV z₀ hz₀V).differentiableAt (hVo.mem_nhds hz₀V)).differentiableWithinAt

noncomputable def poincareMF (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] (k : ℤ) (φ : ℍ → ℂ)
    (hP : MDiff (fun τ : ℍ => ∑' γ : ↥Γ, term k φ (γ : GL (Fin 2) ℝ) τ))
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ) : ModularForm Γ k where
  toSlashInvariantForm := poincareSIF Γ k φ
  holo' := hP
  bdd_at_cusps' hc := absurd hc (hcusp _)

theorem det_restrictScalars_toSpanSingleton (μ : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ μ).restrictScalars ℝ).det = ‖μ‖ ^ 2 := by
  have h1 : ((ContinuousLinearMap.toSpanSingleton ℂ μ).restrictScalars ℝ : ℂ →ₗ[ℝ] ℂ) =
      LinearMap.restrictScalars ℝ ((ContinuousLinearMap.toSpanSingleton ℂ μ : ℂ →ₗ[ℂ] ℂ)) := rfl
  rw [ContinuousLinearMap.det, h1, LinearMap.det_restrictScalars]
  have h2 : (ContinuousLinearMap.toSpanSingleton ℂ μ : ℂ →ₗ[ℂ] ℂ) = μ • LinearMap.id := by
    ext x; simp [mul_comm]
  rw [h2, LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one,
    Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]

noncomputable def moeb (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := num g z / denom g z

theorem det_entries {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 1 := by
  have := congrArg (fun u : ℝˣ => (u : ℝ)) hg
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_two] at this
  exact this

theorem hasDerivAt_moeb {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) {z : ℂ}
    (hz : denom g z ≠ 0) : HasDerivAt (moeb g) ((denom g z) ^ 2)⁻¹ z := by
  have hd := det_entries hg
  have hnum : HasDerivAt (fun z : ℂ => num g z) ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) z := by
    unfold num
    simpa using ((hasDerivAt_id z).const_mul ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ)).add_const
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)
  have hden : HasDerivAt (fun z : ℂ => denom g z) ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) z := by
    unfold denom
    simpa using ((hasDerivAt_id z).const_mul ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)).add_const
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)
  have h := hnum.div hden hz
  have hd' : ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) -
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast hd
  have key : ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * denom g z - num g z * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    unfold num denom; linear_combination hd'
  rw [key, one_div] at h
  exact h

theorem injOn_moeb {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) :
    Set.InjOn (moeb g) {z : ℂ | denom g z ≠ 0} := by
  intro z hz z' hz' h
  have hd := det_entries hg
  have hd' : ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) -
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) = 1 := by
    exact_mod_cast hd
  simp only [Set.mem_setOf_eq] at hz hz'
  unfold moeb at h
  rw [div_eq_div_iff hz hz'] at h
  unfold num denom at h
  have : (z - z') * 1 = 0 := by rw [← hd']; linear_combination h
  simpa [sub_eq_zero] using this

theorem lintegral_image_moeb {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1)
    {B : Set ℂ} (hB : MeasurableSet B) (hBd : ∀ z ∈ B, denom g z ≠ 0) (F : ℂ → ℝ≥0∞) :
    ∫⁻ w in moeb g '' B, F w = ∫⁻ z in B, ENNReal.ofReal ((‖denom g z‖ ^ 4)⁻¹) * F (moeb g z) := by
  have hderiv : ∀ z ∈ B, HasFDerivWithinAt (moeb g)
      ((ContinuousLinearMap.toSpanSingleton ℂ ((denom g z) ^ 2)⁻¹).restrictScalars ℝ) B z := by
    intro z hz
    exact ((hasDerivAt_moeb hg (hBd z hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB hderiv ((injOn_moeb hg).mono (fun z hz => hBd z hz))]
  refine setLIntegral_congr_fun hB (fun z hz => ?_)
  rw [det_restrictScalars_toSpanSingleton, abs_of_nonneg (by positivity), norm_inv, norm_pow, inv_pow]
  congr 1
  rw [← pow_mul]

noncomputable def Lf (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)) * z +
    (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ))

theorem Lf_eq (g : GL (Fin 2) ℝ) (z : ℂ) : Lf g z = num g z + Complex.I * denom g z := by
  unfold Lf num denom; ring

theorem moeb_add_I_mul_denom (g : GL (Fin 2) ℝ) {z : ℂ} (hz : denom g z ≠ 0) :
    (moeb g z + Complex.I) * denom g z = Lf g z := by
  rw [Lf_eq, add_mul, moeb, div_mul_cancel₀ _ hz]

theorem Lf_sub (g : GL (Fin 2) ℝ) (z z' : ℂ) :
    Lf g z' - Lf g z = (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)) * (z' - z) := by
  unfold Lf; ring

theorem normSq_Lf {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) (z : ℂ) :
    Complex.normSq (Lf g z) = Complex.normSq (num g z) + Complex.normSq (denom g z) + 2 * z.im := by
  have hd := det_entries hg
  simp only [Lf, num, denom, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring_nf
  linear_combination (2 * z.im) * hd

theorem two_im_le_normSq_Lf {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) (z : ℂ) :
    2 * z.im ≤ Complex.normSq (Lf g z) := by
  rw [normSq_Lf hg]
  have h1 := Complex.normSq_nonneg (num g z)
  have h2 := Complex.normSq_nonneg (denom g z)
  linarith

theorem norm_coeff_mul_im_le {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) {z : ℂ} (hz : 0 < z.im) :
    ‖(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ))‖ * z.im ≤ ‖Lf g z‖ := by

  have hsq : (‖(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ))‖ * z.im) ^ 2 ≤
      ‖Lf g z‖ ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, normSq_Lf hg]
    have ha : ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.im) ^ 2 ≤ Complex.normSq (num g z) := by
      rw [Complex.normSq_apply]
      have : (num g z).im = (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * z.im := by simp [num]
      rw [← this]; nlinarith [sq_nonneg (num g z).re]
    have hc : ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * z.im) ^ 2 ≤ Complex.normSq (denom g z) := by
      rw [Complex.normSq_apply]
      have : (denom g z).im = (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * z.im := by simp [denom]
      rw [← this]; nlinarith [sq_nonneg (denom g z).re]
    have hn : Complex.normSq (((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ)) =
        (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ^ 2 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 ^ 2 := by
      simp [Complex.normSq_apply]; ring
    rw [hn]
    nlinarith [hz.le]
  have h0 : 0 ≤ ‖(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ))‖ * z.im :=
    mul_nonneg (norm_nonneg _) hz.le
  exact (pow_le_pow_iff_left₀ h0 (norm_nonneg _) two_ne_zero).1 hsq

theorem norm_Lf_le_two_mul {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) {z z' : ℂ}
    (hz : 0 < z.im) (hzz' : ‖z' - z‖ ≤ z.im / 2) : ‖Lf g z‖ ≤ 2 * ‖Lf g z'‖ := by
  have hcoef := norm_coeff_mul_im_le hg hz
  have hdiff : ‖Lf g z' - Lf g z‖ ≤ ‖Lf g z‖ / 2 := by
    rw [Lf_sub, norm_mul]
    calc ‖(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ))‖ * ‖z' - z‖
        ≤ ‖(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ))‖ * (z.im / 2) :=
          mul_le_mul_of_nonneg_left hzz' (norm_nonneg _)
      _ = (‖(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) + Complex.I * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ))‖ * z.im) / 2 := by ring
      _ ≤ ‖Lf g z‖ / 2 := by linarith
  have := norm_sub_norm_le (Lf g z) (Lf g z')
  have h2 : ‖Lf g z - Lf g z'‖ = ‖Lf g z' - Lf g z‖ := norm_sub_rev _ _
  linarith

theorem norm_add_I_bound {z : ℂ} (hz : 0 < z.im) :
    (‖z + Complex.I‖ ^ 4)⁻¹ ≤ 4 * (1 + ‖z‖) ^ (-(4 : ℝ)) := by
  have h1 : 1 + ‖z‖ ^ 2 ≤ ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, add_zero]
    nlinarith [hz.le]
  have h2 : (1 + ‖z‖) ^ 2 ≤ 2 * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖z‖), norm_nonneg z]
  have h3 : 0 < 1 + ‖z‖ := by positivity
  have h5 : (1 + ‖z‖) ^ 2 / 2 ≤ ‖z + Complex.I‖ ^ 2 := by linarith
  have h6 : 0 < (1 + ‖z‖) ^ 2 / 2 := by positivity
  rw [Real.rpow_neg h3.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h7 : ((1 + ‖z‖) ^ 2 / 2) ^ 2 ≤ (‖z + Complex.I‖ ^ 2) ^ 2 := pow_le_pow_left₀ h6.le h5 2
  have h8 : 0 < ((1 + ‖z‖) ^ 2 / 2) ^ 2 := by positivity
  calc (‖z + Complex.I‖ ^ 4)⁻¹ = ((‖z + Complex.I‖ ^ 2) ^ 2)⁻¹ := by ring
    _ ≤ (((1 + ‖z‖) ^ 2 / 2) ^ 2)⁻¹ := by
        exact inv_anti₀ h8 h7
    _ = 4 * ((1 + ‖z‖) ^ 4)⁻¹ := by field_simp; ring

theorem lintegral_upperHalf_lt_top :
    ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal ((‖z + Complex.I‖ ^ 4)⁻¹) < ⊤ := by
  have hfin : ∫⁻ z : ℂ, ENNReal.ofReal ((1 + ‖z‖) ^ (-(4 : ℝ))) < ⊤ := by
    apply finite_integral_one_add_norm
    rw [Complex.finrank_real_complex]; norm_num
  have hmeas : MeasurableSet {z : ℂ | 0 < z.im} := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  calc ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal ((‖z + Complex.I‖ ^ 4)⁻¹)
      ≤ ∫⁻ z in {z : ℂ | 0 < z.im}, ENNReal.ofReal (4 * (1 + ‖z‖) ^ (-(4 : ℝ))) :=
        setLIntegral_mono' hmeas (fun z hz => ENNReal.ofReal_le_ofReal (norm_add_I_bound hz))
    _ ≤ ∫⁻ z : ℂ, ENNReal.ofReal (4 * (1 + ‖z‖) ^ (-(4 : ℝ))) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ z : ℂ, 4 * ENNReal.ofReal ((1 + ‖z‖) ^ (-(4 : ℝ))) := by
        congr 1; funext z; rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ = 4 * ∫⁻ z : ℂ, ENNReal.ofReal ((1 + ‖z‖) ^ (-(4 : ℝ))) := lintegral_const_mul 4 (by fun_prop)
    _ < ⊤ := ENNReal.mul_lt_top (by simp) hfin

theorem sum_setLIntegral_le_of_card_filter_le {X : Type*} [MeasurableSpace X] (μ : Measure X) {ι : Type*}
    (A : ι → Set X) (H : Set X) (hH : MeasurableSet H) (hA : ∀ i, MeasurableSet (A i)) (hAH : ∀ i, A i ⊆ H)
    (N : ℕ) (hN : ∀ (w : X) (T : Finset ι), (∀ i ∈ T, w ∈ A i) → T.card ≤ N)
    (G : X → ℝ≥0∞) (hG : Measurable G) (T : Finset ι) :
    ∑ i ∈ T, ∫⁻ w in A i, G w ∂μ ≤ N * ∫⁻ w in H, G w ∂μ := by
  classical
  have h1 : ∑ i ∈ T, ∫⁻ w in A i, G w ∂μ = ∫⁻ w, ∑ i ∈ T, (A i).indicator G w ∂μ := by
    rw [lintegral_finsetSum]
    · congr 1; funext i
      rw [lintegral_indicator (hA i)]
    · intro i _
      exact (hG.indicator (hA i))
  rw [h1, ← lintegral_indicator hH, ← lintegral_const_mul _ (hG.indicator hH)]
  · refine lintegral_mono fun w => ?_
    by_cases hw : w ∈ H
    · rw [Set.indicator_of_mem hw]
      calc ∑ i ∈ T, (A i).indicator G w = ∑ i ∈ T.filter (fun i => w ∈ A i), G w := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases hi : w ∈ A i <;> simp [hi]
        _ = (T.filter (fun i => w ∈ A i)).card * G w := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ N * G w := by
            gcongr
            exact_mod_cast hN w _ (fun i hi => (Finset.mem_filter.1 hi).2)
    · have : ∀ i ∈ T, (A i).indicator G w = 0 := fun i _ =>
        Set.indicator_of_notMem (fun h => hw (hAH i h)) _
      rw [Finset.sum_eq_zero this, Set.indicator_of_notMem hw]
      simp

theorem isCompact_det_one_bounded (R : ℝ) :
    IsCompact {g : GL (Fin 2) ℝ | Matrix.GeneralLinearGroup.det g = 1 ∧
      ∀ i j, |(g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R} := by
  let C' : Set (Matrix (Fin 2) (Fin 2) ℝ) := {m | m.det = 1} ∩ {m | ∀ i j, |m i j| ≤ R}
  have hbox : IsCompact {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ R} := by
    have : {m : Matrix (Fin 2) (Fin 2) ℝ | ∀ i j, |m i j| ≤ R} =
        Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-R) R)) := by
      ext m
      change (∀ i j, |m i j| ≤ R) ↔ ∀ i, i ∈ Set.univ → ∀ j, j ∈ Set.univ → m i j ∈ Set.Icc (-R) R
      simp [abs_le]
    rw [this]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hC'cpt : IsCompact C' :=
    hbox.inter_left (isClosed_eq (continuous_id.matrix_det) continuous_const)

  have hdet : ∀ m ∈ C', m.det ≠ 0 := fun m hm => by rw [hm.1]; exact one_ne_zero
  let ψ : C' → GL (Fin 2) ℝ := fun m => Matrix.GeneralLinearGroup.mkOfDetNeZero m.1 (hdet m.1 m.2)
  have hψc : Continuous ψ := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val
    ·
      have : (fun m : C' => (((ψ m)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) = fun m => (m.1).adjugate := by
        funext m
        have h1 : ((ψ m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = m.1 := rfl
        rw [Matrix.coe_units_inv, h1, Matrix.inv_def, m.2.1, Ring.inverse_one, one_smul]
      rw [this]
      exact Continuous.matrix_adjugate continuous_subtype_val
  have himage : {g : GL (Fin 2) ℝ | Matrix.GeneralLinearGroup.det g = 1 ∧
      ∀ i j, |(g : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R} = Set.range ψ := by
    ext g
    constructor
    · rintro ⟨hg1, hg2⟩
      have hg1' : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
        rw [← Matrix.GeneralLinearGroup.val_det_apply, hg1, Units.val_one]
      refine ⟨⟨(g : Matrix (Fin 2) (Fin 2) ℝ), hg1', hg2⟩, ?_⟩
      exact Units.ext rfl
    · rintro ⟨m, rfl⟩
      refine ⟨Units.ext ?_, m.2.2⟩
      simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact m.2.1
  rw [himage]
  haveI : CompactSpace C' := isCompact_iff_compactSpace.1 hC'cpt
  exact isCompact_range hψc

theorem finite_det_one_bounded {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : DiscreteTopology ↥Γ] (R : ℝ) :
    Set.Finite {γ : ↥Γ | Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ) = 1 ∧
      ∀ i j, |((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ R} := by
  have hclosed : IsClosed (Γ : Set (GL (Fin 2) ℝ)) := Subgroup.isClosed_of_discrete
  have hemb : Topology.IsClosedEmbedding ((↑) : ↥Γ → GL (Fin 2) ℝ) := hclosed.isClosedEmbedding_subtypeVal
  have hcpt := hemb.isCompact_preimage (isCompact_det_one_bounded R)
  exact hcpt.finite_of_discrete

theorem coeff_bound {α β : ℝ} {z : ℂ} {y R₀ W : ℝ} (hy0 : 0 < y) (hy : y ≤ z.im) (hz : ‖z‖ ≤ R₀)
    (hw : ‖(α : ℂ) * z + β‖ ≤ W) : |α| ≤ W / y ∧ |β| ≤ W + W / y * R₀ := by
  have him : ((α : ℂ) * z + β).im = α * z.im := by simp
  have hre : ((α : ℂ) * z + β).re = α * z.re + β := by simp
  have h1 : |α| * z.im ≤ W := by
    have := Complex.abs_im_le_norm ((α : ℂ) * z + β)
    rw [him, abs_mul, abs_of_pos (hy0.trans_le hy)] at this
    exact this.trans hw
  have hα : |α| ≤ W / y := by
    rw [le_div_iff₀ hy0]
    calc |α| * y ≤ |α| * z.im := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ ≤ W := h1
  refine ⟨hα, ?_⟩
  have h2 : |α * z.re + β| ≤ W := by
    have := Complex.abs_re_le_norm ((α : ℂ) * z + β)
    rw [hre] at this
    exact this.trans hw
  have h3 : |z.re| ≤ R₀ := (Complex.abs_re_le_norm z).trans hz
  have hW : 0 ≤ W := (norm_nonneg _).trans hw
  calc |β| = |(α * z.re + β) - α * z.re| := by ring_nf
    _ ≤ |α * z.re + β| + |α * z.re| := abs_sub _ _
    _ ≤ W + |α| * |z.re| := by rw [abs_mul]; linarith
    _ ≤ W + W / y * R₀ := by
        gcongr

theorem finite_smul_mem {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (K : Set ℍ) {y R₀ : ℝ} (hy0 : 0 < y) (hK : ∀ τ ∈ K, y ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ R₀) :
    Set.Finite {γ : ↥Γ | ∃ τ ∈ K, (γ : GL (Fin 2) ℝ) • τ ∈ K} := by

  have hR₀ : ∀ τ ∈ K, 0 ≤ R₀ := fun τ hτ => (norm_nonneg _).trans (hK τ hτ).2
  set D : ℝ := Real.sqrt (R₀ / y) with hD
  set W : ℝ := R₀ * D with hW
  set R : ℝ := max (max (D / y) (D + D / y * R₀)) (max (W / y) (W + W / y * R₀)) with hRdef
  refine (finite_det_one_bounded (Γ := Γ) R).subset ?_
  rintro γ ⟨τ, hτ, hτ'⟩
  have hγdet := hdet _ γ.2
  have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ)) : ℝ) := by rw [hγdet]; simp
  refine ⟨hγdet, ?_⟩
  obtain ⟨hy1, hn1⟩ := hK τ hτ
  obtain ⟨hy2, hn2⟩ := hK _ hτ'
  have hR₀' : 0 ≤ R₀ := hR₀ τ hτ

  have him := UpperHalfPlane.im_smul_eq_div_normSq (γ : GL (Fin 2) ℝ) τ
  rw [hγdet, Units.val_one, abs_one, one_mul] at him
  have hnsq_pos : 0 < Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) :=
    Complex.normSq_pos.2 (denom_ne_zero _ _)
  have hdenom_sq : Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) ≤ R₀ / y := by
    have h1 : Complex.normSq (denom (γ : GL (Fin 2) ℝ) τ) = τ.im / ((γ : GL (Fin 2) ℝ) • τ).im := by
      rw [him]; field_simp
    rw [h1]
    have hτim : τ.im ≤ R₀ := (Complex.abs_im_le_norm (τ : ℂ)).trans hn1 |> le_trans (le_abs_self _)
    exact div_le_div₀ hR₀' hτim hy0 hy2
  have hdenom : ‖denom (γ : GL (Fin 2) ℝ) τ‖ ≤ D := by
    rw [hD, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm]
    exact Real.sqrt_le_sqrt hdenom_sq
  have hD0 : 0 ≤ D := by rw [hD]; exact Real.sqrt_nonneg _
  have hnum : ‖num (γ : GL (Fin 2) ℝ) τ‖ ≤ W := by
    have hcoe := UpperHalfPlane.coe_smul_of_det_pos hdetpos τ
    have : num (γ : GL (Fin 2) ℝ) τ = (((γ : GL (Fin 2) ℝ) • τ : ℍ) : ℂ) * denom (γ : GL (Fin 2) ℝ) τ := by
      rw [hcoe, div_mul_cancel₀ _ (denom_ne_zero _ _)]
    rw [this, norm_mul, hW]
    exact mul_le_mul hn2 hdenom (norm_nonneg _) hR₀'

  have hc := coeff_bound (α := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0)
    (β := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1) hy0 hy1 hn1 (by simpa [denom] using hdenom)
  have ha := coeff_bound (α := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0)
    (β := ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hy0 hy1 hn1 (by simpa [num] using hnum)
  intro i j
  fin_cases i <;> fin_cases j
  · exact ha.1.trans (by rw [hRdef]; apply le_max_of_le_right; exact le_max_left _ _)
  · exact ha.2.trans (by rw [hRdef]; apply le_max_of_le_right; exact le_max_right _ _)
  · exact hc.1.trans (by rw [hRdef]; apply le_max_of_le_left; exact le_max_left _ _)
  · exact hc.2.trans (by rw [hRdef]; apply le_max_of_le_left; exact le_max_right _ _)

theorem measurableSet_image_moeb {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1)
    {B : Set ℂ} (hB : MeasurableSet B) (hBd : ∀ z ∈ B, denom g z ≠ 0) : MeasurableSet (moeb g '' B) := by
  refine hB.image_of_continuousOn_injOn ?_ ((injOn_moeb hg).mono fun z hz => hBd z hz)
  intro z hz
  unfold moeb num denom
  exact ((continuous_const.mul continuous_id).add continuous_const).continuousAt.continuousWithinAt.div
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt.continuousWithinAt (hBd z hz)

theorem denom_ne_zero_of_im_pos (g : GL (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) : denom g z ≠ 0 :=
  denom_ne_zero g ⟨z, hz⟩

theorem moeb_eq_coe_smul {g : GL (Fin 2) ℝ} (hg : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ)) {z : ℂ}
    (hz : 0 < z.im) : moeb g z = (((g • (⟨z, hz⟩ : ℍ)) : ℍ) : ℂ) := by
  rw [coe_smul_of_det_pos hg]; rfl

theorem moeb_im_pos {g : GL (Fin 2) ℝ} (hg : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ)) {z : ℂ}
    (hz : 0 < z.im) : 0 < (moeb g z).im := by
  rw [moeb_eq_coe_smul hg hz]; exact UpperHalfPlane.im_pos _

theorem norm_Lf_pos {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) {z : ℂ} (hz : 0 < z.im) :
    0 < ‖Lf g z‖ := by
  have h := two_im_le_normSq_Lf hg z
  have h2 : 0 < Complex.normSq (Lf g z) := by linarith
  exact norm_pos_iff.2 (Complex.normSq_pos.1 h2)

theorem norm_term_le {g : GL (Fin 2) ℝ} (hg : Matrix.GeneralLinearGroup.det g = 1) (k : ℤ) {φ : ℍ → ℂ} {M : ℝ}
    (hM : ∀ w : ℍ, ‖φ w‖ * ‖(w : ℂ) + Complex.I‖ ^ k ≤ M) (τ : ℍ) :
    ‖φ (g • τ) * denom g τ ^ (-k)‖ ≤ M * ‖Lf g τ‖ ^ (-k) := by
  have hdetpos : 0 < ((Matrix.GeneralLinearGroup.det g) : ℝ) := by rw [hg]; simp
  have hd : denom g τ ≠ 0 := denom_ne_zero g τ
  have hwI : 0 < ‖(((g • τ : ℍ)) : ℂ) + Complex.I‖ := by
    apply norm_pos_iff.2
    intro h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
    have := (g • τ).im_pos
    rw [← UpperHalfPlane.coe_im] at this
    linarith
  have hL : Lf g τ = ((((g • τ : ℍ)) : ℂ) + Complex.I) * denom g τ := by
    rw [← moeb_add_I_mul_denom g hd, moeb_eq_coe_smul hdetpos τ.im_pos]
  have hφ : ‖φ (g • τ)‖ ≤ M * ‖(((g • τ : ℍ)) : ℂ) + Complex.I‖ ^ (-k) := by
    have := hM (g • τ)
    rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ (zpow_pos hwI k)]
    exact this
  rw [norm_mul, norm_zpow, hL, norm_mul, mul_zpow, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hφ (zpow_nonneg (norm_nonneg _) _)

theorem local_majorant {Γ : Subgroup (GL (Fin 2) ℝ)} [hΓ : DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1) (k : ℤ) (hk : 4 ≤ k)
    {φ : ℍ → ℂ} {M : ℝ} (hM : ∀ w : ℍ, ‖φ w‖ * ‖(w : ℂ) + Complex.I‖ ^ k ≤ M) (τ₀ : ℍ) :
    ∃ U : Set ℍ, IsOpen U ∧ τ₀ ∈ U ∧ ∃ u : ↥Γ → ℝ, Summable u ∧
      ∀ (γ : ↥Γ) (τ : ℍ), τ ∈ U → ‖φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)‖ ≤ u γ := by
  classical
  have hγdet : ∀ γ : ↥Γ, Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ) = 1 := fun γ => hdet _ γ.2
  have hγpos : ∀ γ : ↥Γ, 0 < ((Matrix.GeneralLinearGroup.det (γ : GL (Fin 2) ℝ)) : ℝ) := fun γ => by
    rw [hγdet γ]; simp

  set z₀ : ℂ := (τ₀ : ℂ) with hz₀
  have hy₀ : 0 < z₀.im := by rw [hz₀, UpperHalfPlane.coe_im]; exact τ₀.im_pos
  set r : ℝ := z₀.im / 4 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  set B : Set ℂ := Metric.ball z₀ r with hB
  have him_sub : ∀ z : ℂ, |z.im - z₀.im| ≤ ‖z - z₀‖ := fun z => by
    simpa using Complex.abs_im_le_norm (z - z₀)
  have hBim : ∀ z ∈ B, z₀.im / 2 < z.im ∧ ‖z - z₀‖ < r := by
    intro z hz
    have hd : ‖z - z₀‖ < r := by simpa [hB, Metric.mem_ball, dist_eq_norm] using hz
    have := him_sub z
    refine ⟨?_, hd⟩
    have : -(z₀.im / 4) < z.im - z₀.im := by
      have h1 := neg_abs_le (z.im - z₀.im); rw [hr] at hd; linarith
    linarith
  have hBpos : ∀ z ∈ B, 0 < z.im := fun z hz => by have := (hBim z hz).1; linarith

  set f : ↥Γ → ℝ := fun γ => (‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ 4)⁻¹ with hf
  have hf0 : ∀ γ, 0 ≤ f γ := fun γ => by rw [hf]; positivity

  set K : Set ℍ := {τ : ℍ | ‖(τ : ℂ) - z₀‖ ≤ r} with hKdef
  have hK : ∀ τ ∈ K, z₀.im / 2 ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ ‖z₀‖ + r := by
    intro τ hτ
    have hd : ‖(τ : ℂ) - z₀‖ ≤ r := hτ
    refine ⟨?_, ?_⟩
    · have h1 := neg_abs_le ((τ : ℂ).im - z₀.im)
      have h2 := him_sub (τ : ℂ)
      rw [UpperHalfPlane.coe_im] at h1 h2
      rw [hr] at hd
      linarith
    · calc ‖(τ : ℂ)‖ = ‖z₀ + ((τ : ℂ) - z₀)‖ := by ring_nf
        _ ≤ ‖z₀‖ + ‖(τ : ℂ) - z₀‖ := norm_add_le _ _
        _ ≤ ‖z₀‖ + r := by linarith
  have hFfin := finite_smul_mem hdet K (by positivity : (0 : ℝ) < z₀.im / 2) hK
  set N : ℕ := hFfin.toFinset.card with hN

  have hmult : ∀ (w : ℂ) (T : Finset ↥Γ), (∀ γ ∈ T, w ∈ moeb (γ : GL (Fin 2) ℝ) '' B) → T.card ≤ N := by
    intro w T hT
    rcases T.eq_empty_or_nonempty with h | ⟨γ₁, hγ₁⟩
    · simp [h]
    · obtain ⟨z₁, hz₁B, hz₁w⟩ := hT γ₁ hγ₁
      have hsub : ∀ γ ∈ T, γ₁⁻¹ * γ ∈ hFfin.toFinset := by
        intro γ hγ
        obtain ⟨z₂, hz₂B, hz₂w⟩ := hT γ hγ
        rw [Set.Finite.mem_toFinset]
        refine ⟨⟨z₂, hBpos z₂ hz₂B⟩, le_of_lt (hBim z₂ hz₂B).2, ?_⟩
        have heq : ((γ₁⁻¹ * γ : ↥Γ) : GL (Fin 2) ℝ) • (⟨z₂, hBpos z₂ hz₂B⟩ : ℍ) = ⟨z₁, hBpos z₁ hz₁B⟩ := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, inv_smul_eq_iff]
          apply UpperHalfPlane.ext
          rw [← moeb_eq_coe_smul (hγpos γ) (hBpos z₂ hz₂B), ← moeb_eq_coe_smul (hγpos γ₁) (hBpos z₁ hz₁B),
            hz₂w, hz₁w]
        rw [heq]
        exact le_of_lt (hBim z₁ hz₁B).2
      rw [hN]
      refine Finset.card_le_card_of_injOn (fun γ => γ₁⁻¹ * γ) hsub ?_
      intro a _ b _ hab
      exact mul_left_cancel hab

  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ((‖w + Complex.I‖ ^ 4)⁻¹) with hG
  have hGm : Measurable G := by
    rw [hG]
    exact ENNReal.measurable_ofReal.comp ((continuous_norm.comp (continuous_id.add continuous_const)).pow 4 |>.measurable.inv)
  have hint : ∀ γ : ↥Γ, ENNReal.ofReal (f γ / 16) * volume B ≤ ∫⁻ w in moeb (γ : GL (Fin 2) ℝ) '' B, G w := by
    intro γ
    rw [lintegral_image_moeb (hγdet γ) Metric.isOpen_ball.measurableSet
      (fun z hz => denom_ne_zero_of_im_pos _ (hBpos z hz)) G, ← setLIntegral_const]
    refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun z hz => ?_
    rw [hG, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : denom (γ : GL (Fin 2) ℝ) z ≠ 0 := denom_ne_zero_of_im_pos _ (hBpos z hz)
    have hprod : ‖denom (γ : GL (Fin 2) ℝ) z‖ * ‖moeb (γ : GL (Fin 2) ℝ) z + Complex.I‖ = ‖Lf (γ : GL (Fin 2) ℝ) z‖ := by
      rw [← norm_mul, mul_comm, moeb_add_I_mul_denom _ hd]
    have hcmp : ‖Lf (γ : GL (Fin 2) ℝ) z‖ ≤ 2 * ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ := by
      refine norm_Lf_le_two_mul (hγdet γ) (hBpos z hz) ?_
      have h1 := (hBim z hz).1; have h2 := (hBim z hz).2
      rw [norm_sub_rev]; rw [hr] at h2; linarith
    have hL0 : 0 < ‖Lf (γ : GL (Fin 2) ℝ) z‖ := norm_Lf_pos (hγdet γ) (hBpos z hz)
    rw [hf]
    calc (‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ 4)⁻¹ / 16 = ((2 * ‖Lf (γ : GL (Fin 2) ℝ) z₀‖) ^ 4)⁻¹ := by ring
      _ ≤ (‖Lf (γ : GL (Fin 2) ℝ) z‖ ^ 4)⁻¹ := by
          apply inv_anti₀ (by positivity)
          exact pow_le_pow_left₀ hL0.le hcmp 4
      _ = (‖denom (γ : GL (Fin 2) ℝ) z‖ ^ 4)⁻¹ * (‖moeb (γ : GL (Fin 2) ℝ) z + Complex.I‖ ^ 4)⁻¹ := by
          rw [← hprod, mul_pow, mul_inv]

  set H : Set ℂ := {z : ℂ | 0 < z.im} with hHdef
  have hHm : MeasurableSet H := (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hAm : ∀ γ : ↥Γ, MeasurableSet (moeb (γ : GL (Fin 2) ℝ) '' B) := fun γ =>
    measurableSet_image_moeb (hγdet γ) Metric.isOpen_ball.measurableSet (fun z hz => denom_ne_zero_of_im_pos _ (hBpos z hz))
  have hAH : ∀ γ : ↥Γ, moeb (γ : GL (Fin 2) ℝ) '' B ⊆ H := by
    rintro γ w ⟨z, hz, rfl⟩
    exact moeb_im_pos (hγpos γ) (hBpos z hz)
  have hsum : ∀ T : Finset ↥Γ, ∑ γ ∈ T, ∫⁻ w in moeb (γ : GL (Fin 2) ℝ) '' B, G w ≤ N * ∫⁻ w in H, G w :=
    fun T => sum_setLIntegral_le_of_card_filter_le volume (fun γ : ↥Γ => moeb (γ : GL (Fin 2) ℝ) '' B) H hHm hAm hAH N
      hmult G hGm T
  have hIH : ∫⁻ w in H, G w < ⊤ := lintegral_upperHalf_lt_top
  have hV0 : volume B ≠ 0 := (Metric.measure_ball_pos volume z₀ hr0).ne'
  have hVtop : volume B ≠ ⊤ := by rw [hB, Complex.volume_ball]; exact ENNReal.mul_ne_top (by simp) (by simp)

  set Cb : ℝ≥0∞ := (N : ℝ≥0∞) * (∫⁻ w in H, G w) / volume B with hCb
  have hCbtop : Cb ≠ ⊤ := by
    rw [hCb]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hIH.ne) hV0
  have hfsum : ∀ T : Finset ↥Γ, ∑ γ ∈ T, f γ ≤ 16 * Cb.toReal := by
    intro T
    have h1 : (∑ γ ∈ T, ENNReal.ofReal (f γ / 16)) * volume B ≤ (N : ℝ≥0∞) * ∫⁻ w in H, G w := by
      rw [Finset.sum_mul]
      exact (Finset.sum_le_sum fun γ _ => hint γ).trans (hsum T)
    have h2 : ∑ γ ∈ T, ENNReal.ofReal (f γ / 16) ≤ Cb := by
      rw [hCb, ENNReal.le_div_iff_mul_le (Or.inl hV0) (Or.inl hVtop)]
      exact h1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun γ _ => by have := hf0 γ; positivity)] at h2
    have h3 := (ENNReal.ofReal_le_iff_le_toReal hCbtop).1 h2
    rw [← Finset.sum_div] at h3
    linarith [(div_le_iff₀ (by norm_num : (0:ℝ) < 16)).1 h3]
  have hfS : Summable f := summable_of_sum_le hf0 hfsum

  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hn4 : 4 ≤ n := by omega
  set m₀ : ℝ := Real.sqrt (2 * z₀.im) with hm₀
  have hm₀pos : 0 < m₀ := by rw [hm₀]; exact Real.sqrt_pos.2 (by positivity)
  have hm₀le : ∀ γ : ↥Γ, m₀ ≤ ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ := by
    intro γ
    rw [hm₀, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm]
    exact Real.sqrt_le_sqrt (two_im_le_normSq_Lf (hγdet γ) z₀)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM τ₀)
  set C₂ : ℝ := 2 ^ n / m₀ ^ (n - 4) with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity

  refine ⟨{τ : ℍ | ‖(τ : ℂ) - z₀‖ < r}, ?_, ?_, fun γ => M * C₂ * f γ, (hfS.mul_left (M * C₂)), ?_⟩
  · exact isOpen_lt (continuous_norm.comp (UpperHalfPlane.continuous_coe.sub continuous_const)) continuous_const
  · show ‖(τ₀ : ℂ) - z₀‖ < r
    rw [hz₀, sub_self, norm_zero]; exact hr0
  · intro γ τ hτ
    have hτ' : ‖(τ : ℂ) - z₀‖ < r := hτ
    have h1 := norm_term_le (hγdet γ) k hM τ
    have hcmp : ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ≤ 2 * ‖Lf (γ : GL (Fin 2) ℝ) τ‖ :=
      norm_Lf_le_two_mul (hγdet γ) hy₀ (by rw [hr] at hτ'; linarith)
    have hLτ : 0 < ‖Lf (γ : GL (Fin 2) ℝ) τ‖ := norm_Lf_pos (hγdet γ) (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
    have hL0 : 0 < ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ := lt_of_lt_of_le hm₀pos (hm₀le γ)
    refine h1.trans ?_
    show M * ‖Lf (γ : GL (Fin 2) ℝ) (τ : ℂ)‖ ^ (-k) ≤ M * C₂ * f γ
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hM0

    rw [← hn, zpow_neg, zpow_natCast, hf, hC₂]
    have hpow : (‖Lf (γ : GL (Fin 2) ℝ) z₀‖ / 2) ^ n ≤ ‖Lf (γ : GL (Fin 2) ℝ) τ‖ ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have hsplit : ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ n = ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ (n - 4) * ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ 4 := by
      rw [← pow_add, Nat.sub_add_cancel hn4]
    have hmpow : m₀ ^ (n - 4) ≤ ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ (n - 4) := pow_le_pow_left₀ hm₀pos.le (hm₀le γ) _
    calc (‖Lf (γ : GL (Fin 2) ℝ) τ‖ ^ n)⁻¹ ≤ ((‖Lf (γ : GL (Fin 2) ℝ) z₀‖ / 2) ^ n)⁻¹ := inv_anti₀ (by positivity) hpow
      _ = 2 ^ n / (‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ (n - 4) * ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ 4) := by
          rw [div_pow, inv_div, hsplit]
      _ ≤ 2 ^ n / (m₀ ^ (n - 4) * ‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ 4) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hmpow (by positivity)
      _ = 2 ^ n / m₀ ^ (n - 4) * (‖Lf (γ : GL (Fin 2) ℝ) z₀‖ ^ 4)⁻¹ := by
          rw [div_mul_eq_div_div, div_eq_mul_inv]

end PoincareAux

open PoincareAux in

theorem solution
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ]
    (hcusp : ∀ c : OnePoint ℝ, ¬ IsCusp c Γ)
    (k : ℤ) (hk : 4 ≤ k)
    (φ : ℍ → ℂ) (hφ : MDiff φ)
    (hdecay : ∃ M : ℝ, ∀ w : ℍ, ‖φ w‖ * ‖(w : ℂ) + Complex.I‖ ^ k ≤ M) :

    (∀ τ₀ : ℍ, ∃ U : Set ℍ, IsOpen U ∧ τ₀ ∈ U ∧ ∃ u : ↥Γ → ℝ, Summable u ∧
        ∀ (γ : ↥Γ) (τ : ℍ), τ ∈ U → ‖φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)‖ ≤ u γ) ∧

    ∃ P : ModularForm Γ k, ∀ τ : ℍ, P τ = ∑' γ : ↥Γ, φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k) := by
  obtain ⟨M, hM⟩ := hdecay
  have hloc : ∀ τ₀ : ℍ, ∃ U : Set ℍ, IsOpen U ∧ τ₀ ∈ U ∧ ∃ u : ↥Γ → ℝ, Summable u ∧
      ∀ (γ : ↥Γ) (τ : ℍ), τ ∈ U → ‖φ ((γ : GL (Fin 2) ℝ) • τ) * denom (γ : GL (Fin 2) ℝ) τ ^ (-k)‖ ≤ u γ :=
    fun τ₀ => local_majorant hdet k hk hM τ₀
  refine ⟨hloc, ?_⟩
  haveI : Γ.HasDetOne := ⟨fun hg => hdet _ hg⟩
  have hP : MDiff (fun τ : ℍ => ∑' γ : ↥Γ, term k φ (γ : GL (Fin 2) ℝ) τ) :=
    mdifferentiable_tsum_term hdet k hφ hloc
  exact ⟨poincareMF Γ k φ hP hcusp, fun τ => rfl⟩

end S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology
end P2MW
export P2MW.S_ModularCurve_exists_modularForm_eq_tsum_of_discreteTopology (solution)
