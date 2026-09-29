-- Prove2me | solution 1 for ModularCurve.integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c78ff667-3ab2-506e-99ad-0fb86f858a84

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Theorems.Thm_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt
import Theorems.Thm_ModularCurve_gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
import Theorems.Thm_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "UpperHalfPlane~I"
open Filter Complex MeasureTheory Asymptotics
open scoped MatrixGroups Topology ModularForm ComplexConjugate Real NNReal Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add"
namespace GreenSidePairing
p2m_open "ModularCurve"

theorem coe_ofComplex {z : ℂ} (hz : 0 < z.im) : ((ofComplex z : ℍ) : ℂ) = z := by
  rw [ofComplex_apply_of_im_pos hz]

def sm (σ : SL(2, ℤ)) (z : ℂ) : ℂ := ((σ • ofComplex z : ℍ) : ℂ)

theorem sm_coe (σ : SL(2, ℤ)) (τ : ℍ) : sm σ τ = ((σ • τ : ℍ) : ℂ) := by
  simp [sm]

theorem im_sm_pos (σ : SL(2, ℤ)) (z : ℂ) : 0 < (sm σ z).im := (σ • ofComplex z).im_pos

theorem det_coe' (σ : SL(2, ℤ)) : ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
  (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) σ).det_coe

theorem det_pos (σ : SL(2, ℤ)) : 0 < ((σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [det_coe']; exact one_pos

def dsm (σ : SL(2, ℤ)) (z : ℂ) : ℂ := 1 / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2

theorem dsm_coe (σ : SL(2, ℤ)) (τ : ℍ) : dsm σ τ = 1 / denom (σ : GL (Fin 2) ℝ) τ ^ 2 := by
  simp [dsm]

theorem hasDerivAt_sm (σ : SL(2, ℤ)) (τ : ℍ) : HasDerivAt (sm σ) (dsm σ τ) τ := by
  have h := (UpperHalfPlane.hasStrictDerivAt_smul (g := (σ : GL (Fin 2) ℝ)) (det_pos σ) τ).hasDerivAt
  rw [det_coe'] at h
  rw [dsm_coe]
  simp at h ⊢
  exact h

theorem hasFDerivAt_sm (σ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (sm σ) (dsm σ z • (1 : ℂ →L[ℝ] ℂ)) z := by
  have := (hasDerivAt_sm σ ⟨z, hz⟩).complexToReal_fderiv
  exact this

theorem continuousOn_sm (σ : SL(2, ℤ)) : ContinuousOn (sm σ) {z : ℂ | 0 < z.im} :=
  fun z hz => (hasFDerivAt_sm σ hz).continuousAt.continuousWithinAt

theorem mapsTo_sm (σ : SL(2, ℤ)) : Set.MapsTo (sm σ) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} :=
  fun z _ => im_sm_pos σ z

theorem continuousOn_dsm (σ : SL(2, ℤ)) : ContinuousOn (dsm σ) {z : ℂ | 0 < z.im} := by
  have h : ∀ z ∈ {z : ℂ | 0 < z.im}, dsm σ z = 1 / (((σ 1 0 : ℤ) : ℂ) * z + ((σ 1 1 : ℤ) : ℂ)) ^ 2 := by
    intro z hz
    rw [dsm, ModularGroup.denom_apply, coe_ofComplex hz]
  refine ContinuousOn.congr ?_ h
  refine continuousOn_const.div (by fun_prop) fun z hz => ?_
  have := UpperHalfPlane.denom_ne_zero (σ : GL (Fin 2) ℝ) (ofComplex z)
  rw [ModularGroup.denom_apply, coe_ofComplex hz] at this
  exact pow_ne_zero _ this

def dbarL (T : ℂ →L[ℝ] ℂ) : ℂ := (T 1 + I * T I) / 2

theorem norm_dbarL_le (T : ℂ →L[ℝ] ℂ) : ‖dbarL T‖ ≤ ‖T‖ := by
  unfold dbarL
  rw [norm_div, Complex.norm_two]
  have h1 : ‖T 1‖ ≤ ‖T‖ := by simpa using T.le_opNorm 1
  have h2 : ‖I * T I‖ ≤ ‖T‖ := by rw [norm_mul, Complex.norm_I, one_mul]; simpa using T.le_opNorm I
  have := norm_add_le (T 1) (I * T I)
  linarith

theorem dbarL_comp_smul (T : ℂ →L[ℝ] ℂ) (d : ℂ) :
    dbarL (T.comp (d • (1 : ℂ →L[ℝ] ℂ))) = conj d * dbarL T := by
  have hlin : ∀ w : ℂ, T w = (w.re : ℂ) * T 1 + (w.im : ℂ) * T I := by
    intro w
    conv_lhs => rw [← Complex.re_add_im w]
    rw [map_add]
    have h1 : T (w.re : ℂ) = (w.re : ℂ) * T 1 := by
      rw [show ((w.re : ℂ)) = (w.re : ℝ) • (1 : ℂ) by simp, T.map_smul]; simp
    have h2 : T ((w.im : ℂ) * I) = (w.im : ℂ) * T I := by
      rw [show ((w.im : ℂ) * I) = (w.im : ℝ) • I by simp, T.map_smul]; simp
    rw [h1, h2]
  simp only [dbarL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  rw [hlin d, hlin (d * I)]
  apply Complex.ext <;> simp <;> ring

theorem I_smul_sub_eq (T : ℂ →L[ℝ] ℂ) : I • T 1 - T I = 2 * I * dbarL T := by
  simp only [dbarL, smul_eq_mul]
  have : (2 : ℂ) * I * ((T 1 + I * T I) / 2) = I * T 1 + I * I * T I := by ring
  rw [this, Complex.I_mul_I]; ring

variable {Γ : Subgroup SL(2, ℤ)}

def slashC (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  φ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2

theorem slashC_eq_slash (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) :
    slashC φ σ z = (φ ∣[(2 : ℤ)] σ) (ofComplex z) := by
  rw [slashC, ModularForm.SL_slash_apply, zpow_neg, div_eq_mul_inv]
  norm_cast

theorem slashC_coe (φ : ℍ → ℂ) (σ : SL(2, ℤ)) (τ : ℍ) :
    slashC φ σ τ = (φ ∣[(2 : ℤ)] σ) τ := by
  rw [slashC_eq_slash, ofComplex_apply]

section CuspAnalytics

variable [Γ.FiniteIndex] (f : CuspForm Γ 2) (σ : SL(2, ℤ))

scoped instance isArithmetic_conj :
    (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  have h__af := (Subgroup.IsArithmetic.conj ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
      (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹)
  simp [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv,
    Matrix.SpecialLinearGroup.map_mapGL] at h__af
  exact h__af

def tr : CuspForm (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
    ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) 2 :=
  CuspForm.translate f (σ : GL (Fin 2) ℝ)

theorem coe_tr : ⇑(tr f σ) = (⇑f ∣[(2 : ℤ)] σ) := rfl

theorem slashC_eq_tr : slashC f σ = fun z => tr f σ (ofComplex z) := by
  funext z; rw [slashC_eq_slash, coe_tr]

theorem differentiableOn_slashC : DifferentiableOn ℂ (slashC f σ) {z : ℂ | 0 < z.im} := by
  rw [slashC_eq_tr]
  exact UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo (tr f σ))

theorem hasDerivAt_slashC {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (slashC f σ) (deriv (slashC f σ) z) z :=
  ((differentiableOn_slashC f σ).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasDerivAt

theorem continuousOn_slashC : ContinuousOn (slashC f σ) {z : ℂ | 0 < z.im} :=
  (differentiableOn_slashC f σ).continuousOn

theorem continuousOn_deriv_slashC :
    ContinuousOn (deriv (slashC f σ)) {z : ℂ | 0 < z.im} :=
  ((differentiableOn_slashC f σ).analyticOnNhd isOpen_upperHalfPlaneSet).deriv.continuousOn

theorem tr_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ τ : ℍ, a ≤ τ.im → ‖tr f σ τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hO⟩ := CuspFormClass.exp_decay_atImInfty' (tr f σ)
  obtain ⟨C₁, hC₁⟩ := hO.bound
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hC₁
  obtain ⟨C₂, hC₂⟩ := CuspFormClass.exists_bound (tr f σ)
  refine ⟨c, hc, max (max C₁ 0) (|C₂| / a * Real.exp (c * max A 0)), ?_, fun τ hτ => ?_⟩
  · exact le_max_of_le_left (le_max_right _ _)
  rcases le_or_gt A τ.im with h | h
  · have := hA τ h
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, Real.abs_exp] at this
    refine this.trans ?_
    gcongr
    exact le_max_of_le_left (le_max_left _ _)
  · have h2 := hC₂ τ
    have hk : ((2 : ℤ) : ℝ) / 2 = 1 := by norm_num
    rw [hk, Real.rpow_one] at h2
    have hpos := τ.im_pos
    calc ‖tr f σ τ‖ ≤ C₂ / τ.im := h2
      _ ≤ |C₂| / a := by
        rw [div_le_div_iff₀ hpos ha]
        calc C₂ * a ≤ |C₂| * a := by gcongr; exact le_abs_self _
          _ ≤ |C₂| * τ.im := by gcongr
      _ ≤ |C₂| / a * Real.exp (c * max A 0) * Real.exp (-c * τ.im) := by
        rw [mul_assoc, ← Real.exp_add]
        have : 0 ≤ c * max A 0 + -c * τ.im := by
          have : τ.im ≤ max A 0 := h.le.trans (le_max_left _ _)
          nlinarith
        calc |C₂| / a = |C₂| / a * 1 := (mul_one _).symm
          _ ≤ |C₂| / a * Real.exp (c * max A 0 + -c * τ.im) := by
            gcongr; exact Real.one_le_exp this
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem slashC_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.im → ‖slashC f σ z‖ ≤ C * Real.exp (-c * z.im) := by
  obtain ⟨c, hc, C, hC0, hC⟩ := tr_decay f σ ha
  refine ⟨c, hc, C, hC0, fun z hz => ?_⟩
  have hz0 : 0 < z.im := ha.trans_le hz
  have him : (ofComplex z).im = z.im := by rw [ofComplex_apply_of_im_pos hz0]; rfl
  have := hC (ofComplex z) (by rw [him]; exact hz)
  rw [him] at this
  simpa [slashC_eq_tr] using this

theorem decay_weaken {φ : ℂ → ℂ} {a c δ C : ℝ} (hC : 0 ≤ C) (hδ : δ ≤ c) (ha : 0 ≤ a)
    (h : ∀ z : ℂ, a ≤ z.im → ‖φ z‖ ≤ C * Real.exp (-c * z.im)) :
    ∀ z : ℂ, a ≤ z.im → ‖φ z‖ ≤ C * Real.exp (-δ * z.im) := by
  intro z hz
  refine (h z hz).trans ?_
  gcongr
  nlinarith [ha.trans hz]

theorem deriv_slashC_decay {a : ℝ} (ha : 0 < a) :
    ∃ c > 0, ∃ C, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.im →
      ‖deriv (slashC f σ) z‖ ≤ C * Real.exp (-c * z.im) := by
  have ha2 : 0 < a / 2 := by linarith
  obtain ⟨c, hc, C, hC0, hC⟩ := slashC_decay f σ ha2
  refine ⟨c, hc, C * Real.exp (c * (a / 2)) / (a / 2), by positivity, fun z hz => ?_⟩
  have hball : Metric.closedBall z (a / 2) ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp (h1.trans hw)).1
    simp only [Complex.sub_im] at this
    show 0 < w.im
    linarith
  have hd : DiffContOnCl ℂ (slashC f σ) (Metric.ball z (a / 2)) :=
    ((differentiableOn_slashC f σ).mono hball).diffContOnCl_ball (subset_refl _)
  have hsph : ∀ w ∈ Metric.sphere z (a / 2),
      ‖slashC f σ w‖ ≤ C * Real.exp (c * (a / 2)) * Real.exp (-c * z.im) := by
    intro w hw
    have h1 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
    rw [Metric.mem_sphere, dist_eq_norm] at hw
    have him := (abs_le.mp (h1.trans hw.le)).1
    simp only [Complex.sub_im] at him
    have hwa : a / 2 ≤ w.im := by linarith
    refine (hC w hwa).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    gcongr
    nlinarith
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ha2 hd hsph
  refine this.trans (le_of_eq ?_)
  ring

end CuspAnalytics

section Quasi

variable (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
  (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
  (hL' : ContinuousOn L' {z : ℂ | 0 < z.im}) (σ : SL(2, ℤ))

def Lt (L : ℂ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := L (sm σ z)

def Fd (L' : ℂ → ℂ →L[ℝ] ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (L' (sm σ z)).comp (dsm σ z • (1 : ℂ →L[ℝ] ℂ))

include hL in
theorem hasFDerivAt_Lt {z : ℂ} (hz : 0 < z.im) : HasFDerivAt (Lt L σ) (Fd L' σ z) z :=
  (hL _ (im_sm_pos σ z)).comp z (hasFDerivAt_sm σ hz)

include hL in
theorem continuousOn_Lt : ContinuousOn (Lt L σ) {z : ℂ | 0 < z.im} :=
  fun z hz => (hasFDerivAt_Lt L L' hL σ hz).continuousAt.continuousWithinAt

include hL' in
theorem continuousOn_Fd : ContinuousOn (Fd L' σ) {z : ℂ | 0 < z.im} := by
  unfold Fd
  refine ContinuousOn.clm_comp (hL'.comp (continuousOn_sm σ) (mapsTo_sm σ)) ?_
  exact (continuousOn_dsm σ).smul continuousOn_const

theorem dbarL_Fd (z : ℂ) : dbarL (Fd L' σ z) = conj (dsm σ z) * dbarL (L' (sm σ z)) := by
  rw [Fd, dbarL_comp_smul]

theorem isCompact_box (M : ℝ) : IsCompact (Set.Icc (-1 : ℝ) 1 ×ℂ Set.Icc (1 / 2 : ℝ) M) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))

theorem box_subset (M : ℝ) : Set.Icc (-1 : ℝ) 1 ×ℂ Set.Icc (1 / 2 : ℝ) M ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  have := (Complex.mem_reProdIm.mp hz).2.1
  show 0 < z.im
  linarith

theorem bound_of_compact_and_cusp {F : ℂ → ℝ} {C₁ C₂ Y : ℝ}
    (h1 : ∀ z ∈ Set.Icc (-1 : ℝ) 1 ×ℂ Set.Icc (1 / 2 : ℝ) (max Y 1), F z ≤ C₁)
    (h2 : ∀ z : ℂ, Y ≤ z.im → F z ≤ C₂) :
    ∀ z : ℂ, 1 / 2 ≤ z.im → |z.re| ≤ 1 → F z ≤ max C₁ C₂ := by
  intro z hz hre
  rcases le_or_gt z.im (max Y 1) with h | h
  · exact (h1 z (Complex.mem_reProdIm.mpr ⟨abs_le.mp hre, hz, h⟩)).trans (le_max_left _ _)
  · exact (h2 z ((le_max_left Y 1).trans h.le)).trans (le_max_right _ _)

variable (hbd : ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
    ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧ ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)

include hL hbd in

theorem Lt_bound : ∃ C, ∀ z : ℂ, 1 / 2 ≤ z.im → |z.re| ≤ 1 → ‖Lt L σ z‖ ≤ C := by
  obtain ⟨C, Y, hC⟩ := hbd
  obtain ⟨C₁, hC₁⟩ := (isCompact_box (max Y 1)).exists_bound_of_continuousOn
    ((continuousOn_Lt L L' hL σ).mono (box_subset _))
  exact ⟨max C₁ C, bound_of_compact_and_cusp hC₁ fun z hz => (hC z hz).1⟩

include hL hL' hbd in

theorem Fd_bound : ∃ C, ∀ z : ℂ, 1 / 2 ≤ z.im → |z.re| ≤ 1 → ‖Fd L' σ z‖ ≤ C := by
  obtain ⟨C, Y, hC⟩ := hbd
  obtain ⟨C₁, hC₁⟩ := (isCompact_box (max (max Y 1) 1)).exists_bound_of_continuousOn
    ((continuousOn_Fd L' hL' σ).mono (box_subset _))
  refine ⟨max C₁ C, bound_of_compact_and_cusp hC₁ fun z hz => ?_⟩
  have hz0 : 0 < z.im := lt_of_lt_of_le (lt_of_lt_of_le one_pos (le_max_right Y 1)) hz
  have hd : fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z = Fd L' σ z :=
    (hasFDerivAt_Lt L L' hL σ hz0).fderiv
  rw [← hd]
  exact (hC z ((le_max_left _ _).trans hz)).2

end Quasi

section Tile

def fdC : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}

def Ubox : Set ℂ := {z : ℂ | 1 / 2 < z.im ∧ |z.re| < 1}

theorem measurableSet_fdC : MeasurableSet fdC :=
  (measurableSet_le (continuous_abs.comp Complex.continuous_re).measurable measurable_const).inter
    ((measurableSet_le measurable_const continuous_norm.measurable).inter
      (measurableSet_lt measurable_const Complex.continuous_im.measurable))

theorem isOpen_Ubox : IsOpen Ubox :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)

theorem im_gt_of_mem_fdC {z : ℂ} (hz : z ∈ fdC) : 1 / 2 < z.im := by
  obtain ⟨hre, hn, him⟩ := hz
  have h1 : 1 ≤ z.re * z.re + z.im * z.im := by
    have := Complex.normSq_eq_norm_sq z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have h2 : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.mp hre
    nlinarith
  nlinarith

theorem fdC_subset_Ubox : fdC ⊆ Ubox := fun z hz =>
  ⟨im_gt_of_mem_fdC hz, by have := hz.1; linarith⟩

theorem im_pos_of_mem_Ubox {z : ℂ} (hz : z ∈ Ubox) : 0 < z.im := by
  have := hz.1; linarith

variable [Γ.FiniteIndex] (g : CuspForm Γ 2) (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
  (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
  (hL' : ContinuousOn L' {z : ℂ | 0 < z.im}) (σ : SL(2, ℤ))
  (hbd : ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
    ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
      ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)

def Φt (L : ℂ → ℂ) (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := Lt L σ z * slashC g σ z

def Gd (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ →L[ℝ] ℂ := deriv (slashC g σ) z • (1 : ℂ →L[ℝ] ℂ)

def Φt' (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ) (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  Lt L σ z • Gd g σ z + slashC g σ z • Fd L' σ z

include hL in
theorem hasFDerivAt_Φt {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (Φt L g σ) (Φt' L L' g σ z) z :=
  (hasFDerivAt_Lt L L' hL σ hz).mul (hasDerivAt_slashC g σ hz).complexToReal_fderiv

include hL hL' in
theorem continuousOn_Φt' : ContinuousOn (Φt' L L' g σ) {z : ℂ | 0 < z.im} := by
  have h1 : ContinuousOn (Gd g σ) {z : ℂ | 0 < z.im} :=
    (continuousOn_deriv_slashC g σ).smul continuousOn_const
  exact ((continuousOn_Lt L L' hL σ).smul h1).add
    ((continuousOn_slashC g σ).smul (continuousOn_Fd L' hL' σ))

theorem norm_Gd_le (z : ℂ) : ‖Gd g σ z‖ ≤ ‖deriv (slashC g σ) z‖ := by
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  simp

theorem I_smul_Φt'_sub (z : ℂ) :
    I • Φt' L L' g σ z 1 - Φt' L L' g σ z I =
      2 * I * (slashC g σ z * (conj (dsm σ z) * dbarL (L' (sm σ z)))) := by
  rw [I_smul_sub_eq, ← dbarL_Fd]
  congr 1
  simp only [dbarL, Φt', Gd, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  have : I * I = -1 := Complex.I_mul_I
  linear_combination (Lt L σ z * deriv (slashC g σ) z / 2) * this

include hL hL' hbd in
theorem Φt_bounds : ∃ δ > 0,
    (∃ C : ℝ, ∀ z ∈ Ubox, ‖Φt L g σ z‖ ≤ C * Real.exp (-δ * z.im)) ∧
    (∃ C : ℝ, ∀ z ∈ Ubox, ‖Φt' L L' g σ z‖ ≤ C * Real.exp (-δ * z.im)) := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨c₁, hc₁, C₁, hC₁0, hC₁⟩ := slashC_decay g σ h2
  obtain ⟨c₂, hc₂, C₂, hC₂0, hC₂⟩ := deriv_slashC_decay g σ h2
  obtain ⟨CL, hCL⟩ := Lt_bound L L' hL σ hbd
  obtain ⟨CF, hCF⟩ := Fd_bound L L' hL hL' σ hbd
  set δ := min c₁ c₂ with hδ
  have hδ₁ : δ ≤ c₁ := min_le_left _ _
  have hδ₂ : δ ≤ c₂ := min_le_right _ _
  have hG := decay_weaken hC₁0 hδ₁ h2.le hC₁
  have hG' := decay_weaken hC₂0 hδ₂ h2.le hC₂
  refine ⟨δ, lt_min hc₁ hc₂, ⟨CL * C₁, fun z hz => ?_⟩, ⟨CL * C₂ + C₁ * CF, fun z hz => ?_⟩⟩
  · have hzi : 1 / 2 ≤ z.im := hz.1.le
    have hV := hCL z hzi hz.2.le
    rw [Φt, norm_mul, mul_assoc]
    exact mul_le_mul hV (hG z hzi) (norm_nonneg _) ((norm_nonneg _).trans hV)
  · have hzi : 1 / 2 ≤ z.im := hz.1.le
    have hV := hCL z hzi hz.2.le
    have hF := hCF z hzi hz.2.le
    have hCL0 : 0 ≤ CL := (norm_nonneg _).trans hV
    have hCF0 : 0 ≤ CF := (norm_nonneg _).trans hF
    refine (norm_add_le _ _).trans ?_
    rw [add_mul]
    refine add_le_add ?_ ?_
    · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul hV ((norm_Gd_le g σ z).trans (hG' z hzi)) (norm_nonneg _) hCL0
    · refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
      calc ‖slashC g σ z‖ * ‖Fd L' σ z‖ ≤ C₁ * Real.exp (-δ * z.im) * CF :=
            mul_le_mul (hG z hzi) hF (norm_nonneg _) (by positivity)
        _ = C₁ * CF * Real.exp (-δ * z.im) := by ring

include hL hL' hbd in

theorem tile_identity :
    (∫ z in fdC, 2 * I * (slashC g σ z * (conj (dsm σ z) * dbarL (L' (sm σ z))))) =
      I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φt L g σ (1 / 2 + y * I)) -
        I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φt L g σ (-(1 / 2) + y * I)) -
        ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          Φt L g σ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) := by
  obtain ⟨δ, hδ, hΦ, hΦ'⟩ := Φt_bounds g L L' hL hL' σ hbd
  have hE := Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt (Φt L g σ)
    (Φt' L L' g σ) Ubox δ hδ isOpen_Ubox fdC_subset_Ubox
    (fun z hz => hasFDerivAt_Φt g L L' hL σ (im_pos_of_mem_Ubox hz))
    ((continuousOn_Φt' g L L' hL hL' σ).mono fun z hz => im_pos_of_mem_Ubox hz) hΦ hΦ'
  rw [← hE]
  refine setIntegral_congr_fun measurableSet_fdC fun z _ => ?_
  rw [I_smul_Φt'_sub]

end Tile

section Edges

theorem sqrt3_div_two_gt : (1 : ℝ) / 2 < Real.sqrt 3 / 2 := by
  have : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem ray_mem_Ubox {y : ℝ} (hy : y ∈ Set.Ioi (Real.sqrt 3 / 2)) :
    (-(1 / 2) + y * I : ℂ) ∈ Ubox := by
  refine ⟨?_, ?_⟩
  · show 1 / 2 < (-(1 / 2) + y * I : ℂ).im
    simpa using sqrt3_div_two_gt.trans hy
  · show |(-(1 / 2) + y * I : ℂ).re| < 1
    rw [show (-(1 / 2) + y * I : ℂ).re = -(1 / 2) by simp, abs_neg,
      abs_of_pos (by norm_num)]
    norm_num

theorem integrableOn_ray {F : ℂ → ℂ} (hc : ContinuousOn F {z : ℂ | 0 < z.im}) {C δ : ℝ}
    (hδ : 0 < δ) (hb : ∀ z ∈ Ubox, ‖F z‖ ≤ C * Real.exp (-δ * z.im)) :
    IntegrableOn (fun y : ℝ => F (-(1 / 2) + y * I)) (Set.Ioi (Real.sqrt 3 / 2)) := by
  have hpath : Continuous fun y : ℝ => (-(1 / 2) + y * I : ℂ) := by fun_prop
  have hcont : ContinuousOn (fun y : ℝ => F (-(1 / 2) + y * I))
      (Set.Ioi (Real.sqrt 3 / 2)) :=
    hc.comp hpath.continuousOn fun y hy => im_pos_of_mem_Ubox (ray_mem_Ubox hy)
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi _ hδ).const_mul C)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
  have := hb _ (ray_mem_Ubox hy)
  simpa using this

theorem intervalIntegrable_arc {F : ℂ → ℂ} (hc : ContinuousOn F {z : ℂ | 0 < z.im}) :
    IntervalIntegrable (fun θ : ℝ => F (Complex.exp (θ * I)) *
      (I * Complex.exp (θ * I))) volume (Real.pi / 3) (2 * Real.pi / 3) := by
  refine ContinuousOn.intervalIntegrable ?_
  have hpath : Continuous fun θ : ℝ => Complex.exp (θ * I) := by fun_prop
  have hmem : ∀ θ ∈ Set.uIcc (Real.pi / 3) (2 * Real.pi / 3),
      Complex.exp (θ * I) ∈ {z : ℂ | 0 < z.im} := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    show 0 < (Complex.exp (θ * I)).im
    rw [Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
      (by linarith [Real.pi_pos, hθ.2])
  have h2 : Continuous fun θ : ℝ => I * Complex.exp (θ * I) := by fun_prop
  exact (hc.comp hpath.continuousOn hmem).mul h2.continuousOn

end Edges

section Pairing

variable [Fintype (SL(2, ℤ) ⧸ Γ)] [Γ.FiniteIndex] (g : CuspForm Γ 2) (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
  (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
  (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
  (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
  (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
    ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
      ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)

theorem g_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ := by
  have := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  simpa using this

include hLc in

theorem twist_law (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    L ((γ • τ : ℍ) : ℂ) * g (γ • τ) / denom (γ : GL (Fin 2) ℝ) τ ^ 2 =
      L τ * g τ + c γ * g τ := by
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  rw [hLc γ hγ τ, g_smul g hγ]
  field_simp

theorem Φt_eq (σ : SL(2, ℤ)) (z : ℂ) :
    Φt L g σ z = L ((σ • ofComplex z : ℍ) : ℂ) * g (σ • ofComplex z) /
      denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2 := by
  rw [Φt, Lt, sm, slashC, mul_div_assoc]

include hL hL' hLc hbd in

theorem side_pairing :
    ((∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in Set.Ioi (Real.sqrt 3 / 2),
        Φt L g (Quotient.out q)⁻¹ (1 / 2 + y * I)) =
      (∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in Set.Ioi (Real.sqrt 3 / 2),
        Φt L g (Quotient.out q)⁻¹ (-(1 / 2) + y * I)) +
      ∑ q : SL(2, ℤ) ⧸ Γ,
        c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
          ∫ y in Set.Ioi (Real.sqrt 3 / 2),
            slashC g (Quotient.out q)⁻¹ (-(1 / 2) + y * I)) ∧
    2 * (∑ q : SL(2, ℤ) ⧸ Γ, ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        Φt L g (Quotient.out q)⁻¹ (Complex.exp (θ * I)) *
          (I * Complex.exp (θ * I))) =
      -∑ q : SL(2, ℤ) ⧸ Γ,
        c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
          ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            slashC g (Quotient.out q)⁻¹ (Complex.exp (θ * I)) *
              (I * Complex.exp (θ * I)) := by
  refine ModularCurve.gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
    Γ (fun τ => L τ * g τ) g c
    (fun γ hγ τ => twist_law g L c hLc γ hγ τ) (fun σ z => Φt L g σ z) (fun σ z => slashC g σ z)
    (fun σ z => Φt_eq g L σ z) (fun σ z => rfl) (Set.Ioi (Real.sqrt 3 / 2)) measurableSet_Ioi
    (Set.Ioi_subset_Ioi (by positivity)) (fun q => ?_) (fun q => ?_) (fun q => ?_) (fun q => ?_)
  · obtain ⟨δ, hδ, ⟨C, hC⟩, -⟩ := Φt_bounds g L L' hL hL' (Quotient.out q)⁻¹ (hbd _)
    have hc : ContinuousOn (Φt L g (Quotient.out q)⁻¹) {z : ℂ | 0 < z.im} :=
      (continuousOn_Lt L L' hL _).mul (continuousOn_slashC g _)
    exact integrableOn_ray hc hδ hC
  · obtain ⟨c, hc, C, -, hC⟩ := slashC_decay g (Quotient.out q)⁻¹ (by norm_num : (0 : ℝ) < 1 / 2)
    exact integrableOn_ray (continuousOn_slashC g _) hc fun z hz => hC z hz.1.le
  · exact intervalIntegrable_arc ((continuousOn_Lt L L' hL _).mul (continuousOn_slashC g _))
  · exact intervalIntegrable_arc (continuousOn_slashC g _)

end Pairing

section LHS

theorem measurableSet_fd : MeasurableSet ModularGroup.fd :=
  (measurableSet_le measurable_const
    (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe).measurable).inter
    (measurableSet_le (continuous_abs.comp UpperHalfPlane.continuous_re).measurable
      measurable_const)

theorem preimage_fdC : UpperHalfPlane.coe ⁻¹' fdC = ModularGroup.fd := by
  ext τ
  simp only [fdC, Set.mem_preimage, Set.mem_setOf_eq, ModularGroup.fd, UpperHalfPlane.coe_im,
    UpperHalfPlane.coe_re]
  rw [Complex.normSq_eq_norm_sq, one_le_sq_iff₀ (norm_nonneg _)]
  exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, τ.im_pos⟩⟩

theorem coe_mem_fdC_of_mem_fd {τ : ℍ} (hτ : τ ∈ ModularGroup.fd) : (τ : ℂ) ∈ fdC := by
  rw [← preimage_fdC] at hτ; exact hτ

theorem fdC_subset_range : fdC ⊆ Set.range UpperHalfPlane.coe := by
  rw [UpperHalfPlane.range_coe]; exact fun z hz => hz.2.2

theorem setIntegral_fd_mul_im_sq (H : ℍ → ℂ) :
    ∫ τ in ModularGroup.fd, H τ * ((τ.im : ℝ) : ℂ) ^ 2 = ∫ z in fdC, H (ofComplex z) := by
  have mp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hmeas : Measurable fun z : ℍ => (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 := by
    refine Measurable.pow_const (Measurable.const_div ?_ 1) 2
    exact UpperHalfPlane.continuous_im.measurable.subtype_mk
  calc ∫ τ in ModularGroup.fd, H τ * ((τ.im : ℝ) : ℂ) ^ 2
      = ∫ τ in ModularGroup.fd, (1 / NNReal.mk τ.im τ.im_pos.le : ℝ≥0) ^ 2 •
          (H τ * ((τ.im : ℝ) : ℂ) ^ 2) ∂(volume.comap UpperHalfPlane.coe) := by
        rw [UpperHalfPlane.volume_def]
        exact setIntegral_withDensity_eq_setIntegral_smul hmeas _ measurableSet_fd
    _ = ∫ τ in ModularGroup.fd, H (ofComplex (τ : ℂ)) ∂(volume.comap UpperHalfPlane.coe) := by
        refine setIntegral_congr_fun measurableSet_fd fun τ _ => ?_
        have h0 : (τ.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr τ.im_pos.ne'
        rw [ofComplex_apply, NNReal.smul_def, Complex.real_smul]
        push_cast
        field_simp
    _ = ∫ z in fdC, H (ofComplex z) ∂(volume.restrict (Set.range UpperHalfPlane.coe)) := by
        rw [← mp.setIntegral_preimage_emb measurableEmbedding_coe (fun z => H (ofComplex z)) fdC,
          preimage_fdC]
    _ = ∫ z in fdC, H (ofComplex z) := by
        rw [Measure.restrict_restrict measurableSet_fdC,
          Set.inter_eq_left.mpr fdC_subset_range]

variable [Fintype (SL(2, ℤ) ⧸ Γ)] [Γ.FiniteIndex] (g : CuspForm Γ 2) (L : ℂ → ℂ)
  (L' : ℂ → ℂ →L[ℝ] ℂ)
  (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
  (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
  (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
  (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
    ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
      ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)

def Pd (L' : ℂ → ℂ →L[ℝ] ℂ) (g : ℍ → ℂ) (τ : ℍ) : ℂ :=
  dbarL (L' τ) * g τ * ((τ.im : ℂ) ^ 2)

def Hd (L' : ℂ → ℂ →L[ℝ] ℂ) (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ :=
  slashC g σ z * (conj (dsm σ z) * dbarL (L' (sm σ z)))

include hL hLc in

theorem dbarL_smul (γ : SL(2, ℤ)) (hγ : γ ∈ Γ) (τ : ℍ) :
    dbarL (L' ((γ • τ : ℍ) : ℂ)) = conj (denom (γ : GL (Fin 2) ℝ) τ) ^ 2 * dbarL (L' τ) := by
  have hτ : 0 < (τ : ℂ).im := τ.im_pos

  have hev : (fun u => L (sm γ u)) =ᶠ[𝓝 (τ : ℂ)] fun u => L u + c γ := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hτ] with u hu
    have := hLc γ hγ (ofComplex u)
    rw [coe_ofComplex hu] at this
    exact this
  have h1 : HasFDerivAt (fun u => L (sm γ u)) (L' τ) τ := by
    refine HasFDerivAt.congr_of_eventuallyEq ?_ hev
    exact (hL _ hτ).add_const _
  have h2 : HasFDerivAt (fun u => L (sm γ u)) (Fd L' γ τ) τ := hasFDerivAt_Lt L L' hL γ hτ
  have heq : Fd L' γ τ = L' τ := h2.unique h1
  have h3 := dbarL_Fd L' γ τ
  rw [heq, sm_coe, dsm_coe] at h3
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcD : conj (denom (γ : GL (Fin 2) ℝ) τ) ≠ 0 := (map_ne_zero _).2 hD
  rw [h3, map_div₀, map_one, map_pow]
  field_simp

theorem Pd_smul (σ : SL(2, ℤ)) (τ : ℍ) : Pd L' g (σ • τ) = Hd L' g σ τ * ((τ.im : ℂ) ^ 2) := by
  simp only [Pd, Hd]
  have hD : denom (σ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hcD : conj (denom (σ : GL (Fin 2) ℝ) τ) ≠ 0 := (map_ne_zero _).2 hD
  have hg : g (σ • τ) = slashC g σ τ * denom (σ : GL (Fin 2) ℝ) τ ^ 2 := by
    rw [slashC_coe, ModularForm.SL_slash_apply, zpow_neg]
    norm_cast
    field_simp
  have him : ((σ • τ).im : ℂ) = (τ.im : ℂ) / (Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) : ℂ) := by
    rw [ModularGroup.im_smul_eq_div_normSq]; push_cast; rfl
  have hns : (Complex.normSq (denom (σ : GL (Fin 2) ℝ) τ) : ℂ) =
      conj (denom (σ : GL (Fin 2) ℝ) τ) * denom (σ : GL (Fin 2) ℝ) τ := by
    rw [Complex.normSq_eq_conj_mul_self]
  rw [← sm_coe, hg, him, hns, sm_coe, dsm_coe, map_div₀, map_one, map_pow]
  rw [← sm_coe]
  field_simp

theorem measurableSet_gammaFundamentalSet :
    MeasurableSet (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) :=
  MeasurableSet.iUnion fun q => (ModularGroup.isClosed_fd.smul _).measurableSet

include hL' in
theorem continuous_Pd : Continuous (Pd L' g) := by
  unfold Pd
  have h1 : Continuous fun τ : ℍ => L' (τ : ℂ) :=
    hL'.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.im_pos
  have h2 : Continuous fun τ : ℍ => dbarL (L' (τ : ℂ)) := by
    unfold dbarL
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp h1).add
      (continuous_const.mul ((ContinuousLinearMap.apply ℝ ℂ I).continuous.comp h1))).div_const _
  exact (h2.mul (CuspFormClass.holo g).continuous).mul
    ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow 2)

theorem sq_mul_exp_neg_le {c : ℝ} (hc : 0 < c) {v : ℝ} (hv : 0 ≤ v) :
    v ^ 2 * Real.exp (-c * v) ≤ 2 / c ^ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le hv)
  have hexp : 0 < Real.exp (c * v) := Real.exp_pos _
  have h1 : (c * v) ^ 2 / 2 ≤ Real.exp (c * v) := by nlinarith [mul_nonneg hc.le hv]
  rw [show -c * v = -(c * v) by ring, Real.exp_neg]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < c ^ 2)]
  have : v ^ 2 * (Real.exp (c * v))⁻¹ * c ^ 2 = (c * v) ^ 2 / Real.exp (c * v) := by
    field_simp
  rw [this, div_le_iff₀ hexp]
  linarith

include hL hL' hbd in

theorem Pd_bound_tile (σ : SL(2, ℤ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℍ, u ∈ ModularGroup.fd → ‖Pd L' g (σ • u)‖ ≤ M := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨c₁, hc₁, C₁, hC₁0, hC₁⟩ := slashC_decay g σ h2
  obtain ⟨CF, hCF⟩ := Fd_bound L L' hL hL' σ (hbd σ)
  refine ⟨C₁ * (2 / c₁ ^ 2) * max CF 0, by positivity, fun u hu => ?_⟩
  have huC : (u : ℂ) ∈ fdC := coe_mem_fdC_of_mem_fd hu
  have hui : 1 / 2 ≤ (u : ℂ).im := (im_gt_of_mem_fdC huC).le
  have hure : |(u : ℂ).re| ≤ 1 := huC.1.trans (by norm_num)
  rw [Pd_smul, Hd, ← dbarL_Fd, norm_mul, norm_mul]
  have hF : ‖dbarL (Fd L' σ u)‖ ≤ max CF 0 :=
    ((norm_dbarL_le _).trans (hCF _ hui hure)).trans (le_max_left _ _)
  have hG : ‖slashC g σ u‖ ≤ C₁ * Real.exp (-c₁ * (u : ℂ).im) := hC₁ _ hui
  have hsq : ‖((u.im : ℂ)) ^ 2‖ = u.im ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos u.im_pos]
  rw [hsq]
  have hv := sq_mul_exp_neg_le hc₁ u.im_pos.le
  have him : (u : ℂ).im = u.im := rfl
  rw [him] at hG
  calc ‖slashC g σ u‖ * ‖dbarL (Fd L' σ u)‖ * u.im ^ 2
      ≤ (C₁ * Real.exp (-c₁ * u.im)) * max CF 0 * u.im ^ 2 := by gcongr
    _ = C₁ * (u.im ^ 2 * Real.exp (-c₁ * u.im)) * max CF 0 := by ring
    _ ≤ C₁ * (2 / c₁ ^ 2) * max CF 0 := by gcongr

include hL hL' hbd in

theorem integrableOn_Pd :
    IntegrableOn (Pd L' g) (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) := by
  choose M hM0 hM using fun q : SL(2, ℤ) ⧸ Γ => Pd_bound_tile g L L' hL hL' hbd (Quotient.out q)⁻¹
  refine Measure.integrableOn_of_bounded (M := ∑ q, M q)
    (FLT.Gamma0FundamentalSet.volume_gammaFundamentalSet_lt_top Γ).ne
    (continuous_Pd g L' hL').aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_gammaFundamentalSet fun τ hτ => ?_
  obtain ⟨q, hq⟩ := FLT.Gamma0FundamentalSet.mem_gammaFundamentalSet_iff.1 hτ
  have hτeq : τ = (Quotient.out q)⁻¹ • (Quotient.out q • τ) := by rw [inv_smul_smul]
  rw [hτeq]
  refine (hM q _ hq).trans ?_
  exact Finset.single_le_sum (f := M) (fun q _ => hM0 q) (Finset.mem_univ q)

variable (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)

include hL hL' hbd hΓ in

theorem lhs_unfold :
    ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, Pd L' g τ =
      ∑ q : SL(2, ℤ) ⧸ Γ, ∫ z in fdC, Hd L' g (Quotient.out q)⁻¹ z := by
  rw [FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd hΓ _
    (integrableOn_Pd g L L' hL hL' hbd), finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  set σ : SL(2, ℤ) := (Quotient.out q)⁻¹
  calc ∫ τ in ModularGroup.fd, Pd L' g (σ • τ)
      = ∫ τ in ModularGroup.fd, Hd L' g σ τ * ((τ.im : ℝ) : ℂ) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_fd fun τ _ => ?_
        rw [Pd_smul]
    _ = ∫ z in fdC, Hd L' g σ (ofComplex z) := setIntegral_fd_mul_im_sq _
    _ = ∫ z in fdC, Hd L' g σ z := by
        refine setIntegral_congr_fun measurableSet_fdC fun z hz => ?_
        rw [coe_ofComplex hz.2.2]

end LHS

theorem main (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
    (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
    (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
    (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
    (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)
    (g : CuspForm Γ 2) (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    IntegrableOn (fun τ : ℍ => (L' τ 1 + I * L' τ I) / 2 * g τ * ((τ.im : ℂ) ^ 2))
      (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) ∧
    (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        (L' τ 1 + I * L' τ I) / 2 * g τ * ((τ.im : ℂ) ^ 2)) =
      1 / (2 * I) *
        (I * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * I)) +
          1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
              (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                G q (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)))) := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hG' : G = fun q => slashC g (Quotient.out q)⁻¹ := by
    funext q z; exact hG q z
  subst hG'
  beta_reduce
  refine ⟨integrableOn_Pd g L L' hL hL' hbd, ?_⟩
  obtain ⟨e2, e3⟩ := side_pairing g L L' hL hL' c hLc hbd
  have e1 : ∀ q : SL(2, ℤ) ⧸ Γ,
      2 * I * ∫ z in fdC, Hd L' g (Quotient.out q)⁻¹ z =
        I * (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            Φt L g (Quotient.out q)⁻¹ (1 / 2 + y * I)) -
          I * (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            Φt L g (Quotient.out q)⁻¹ (-(1 / 2) + y * I)) -
          ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φt L g (Quotient.out q)⁻¹ (Complex.exp (θ * I)) *
              (I * Complex.exp (θ * I)) := fun q => by
    rw [← smul_eq_mul I, ← smul_eq_mul I,
      ← tile_identity g L L' hL hL' (Quotient.out q)⁻¹ (hbd _), ← integral_const_mul]
    rfl
  have e1s := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => e1 q
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at e1s
  have hlhs := lhs_unfold g L L' hL hL' hbd hΓ
  change (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, Pd L' g τ) = _
  rw [hlhs]
  have key : 2 * I * (∑ q : SL(2, ℤ) ⧸ Γ, ∫ z in fdC, Hd L' g (Quotient.out q)⁻¹ z) =
      I * (∑ q : SL(2, ℤ) ⧸ Γ,
          c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
            ∫ y in Set.Ioi (Real.sqrt 3 / 2), slashC g (Quotient.out q)⁻¹ (-(1 / 2) + y * I)) +
        1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
          c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
            ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              slashC g (Quotient.out q)⁻¹ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) := by
    linear_combination e1s + I * e2 - (1 / 2 : ℂ) * e3
  have h2I : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  rw [← key]
  field_simp

end ModularCurve.GreenSidePairing
p2m_reactivate "P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.ModularCurve P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.ModularCurve.GreenSidePairing"
p2m_reactivate "P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.ModularCurve P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing.ModularCurve.GreenSidePairing"

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem solution
    (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (L : ℂ → ℂ) (L' : ℂ → ℂ →L[ℝ] ℂ)
    (hL : ∀ z : ℂ, 0 < z.im → HasFDerivAt L (L' z) z)
    (hL' : ContinuousOn L' {z : ℂ | 0 < z.im})
    (c : SL(2, ℤ) → ℂ) (hLc : ∀ γ ∈ Γ, ∀ τ : ℍ, L ((γ • τ : ℍ) : ℂ) = L τ + c γ)
    (hbd : ∀ σ : SL(2, ℤ), ∃ C Y : ℝ, ∀ z : ℂ, Y ≤ z.im →
      ‖L ((σ • ofComplex z : ℍ) : ℂ)‖ ≤ C ∧
        ‖fderiv ℝ (fun u : ℂ => L ((σ • ofComplex u : ℍ) : ℂ)) z‖ ≤ C)
    (g : CuspForm Γ 2) (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    IntegrableOn (fun τ : ℍ => (L' τ 1 + Complex.I * L' τ Complex.I) / 2 * g τ * ((τ.im : ℂ) ^ 2))
      (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) ∧
    (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        (L' τ 1 + Complex.I * L' τ Complex.I) / 2 * g τ * ((τ.im : ℂ) ^ 2)) =
      1 / (2 * Complex.I) *
        (Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
          1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
              (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
                G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))) :=
  ModularCurve.GreenSidePairing.main Γ hΓ L L' hL hL' c hLc hbd g G hG

end S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing
end P2MW
export P2MW.S_ModularCurve_integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing (solution)
