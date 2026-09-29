-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/98c634b4-56d6-533a-89a4-20ec10f6e23e

import Mathlib
import Theorems.Thm_MeasureTheory_exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

noncomputable section

namespace ParamLogPotC

section CLM

theorem det_eq (T : ℂ →L[ℝ] ℂ) :
    LinearMap.det (T : ℂ →ₗ[ℝ] ℂ) = (T 1).re * (T Complex.I).im - (T Complex.I).re * (T 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.coe_coe]

theorem injective_of (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) :
    Function.Injective (T : ℂ →ₗ[ℝ] ℂ) := by
  intro a b hab
  have : T (a - b) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hab
  exact sub_eq_zero.mp (h _ this)

def equivOfInj (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) : ℂ ≃L[ℝ] ℂ :=
  (LinearMap.linearEquivOfInjective (T : ℂ →ₗ[ℝ] ℂ) (injective_of T h) rfl).toContinuousLinearEquiv

theorem equivOfInj_apply (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) (z : ℂ) :
    equivOfInj T h z = T z := rfl

theorem coe_equivOfInj (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) :
    (equivOfInj T h : ℂ →L[ℝ] ℂ) = T := by
  ext z; rfl

theorem det_ne_zero (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) :
    LinearMap.det (T : ℂ →ₗ[ℝ] ℂ) ≠ 0 := by
  have hu := LinearEquiv.isUnit_det' ((equivOfInj T h).toLinearEquiv)
  have hc : ((equivOfInj T h).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = (T : ℂ →ₗ[ℝ] ℂ) := by
    ext z; rfl
  rw [hc] at hu
  exact hu.ne_zero

theorem inverse_eq (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) :
    T.inverse = ((equivOfInj T h).symm : ℂ →L[ℝ] ℂ) := by
  conv_lhs => rw [← coe_equivOfInj T h]
  exact ContinuousLinearMap.inverse_equiv _

theorem inverse_apply_apply (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) (z : ℂ) :
    T.inverse (T z) = z := by
  rw [inverse_eq T h]
  exact (equivOfInj T h).symm_apply_apply z

theorem apply_inverse_apply (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) (u : ℂ) :
    T (T.inverse u) = u := by
  rw [inverse_eq T h]
  exact (equivOfInj T h).apply_symm_apply u

theorem contDiff_det {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → (ℂ →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L) :
    ContDiff ℝ (⊤ : ℕ∞) fun p => LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ) := by
  have hfun : (fun p => LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ)) =
      fun p => (L p 1).re * (L p Complex.I).im - (L p Complex.I).re * (L p 1).im := by
    funext p; exact det_eq (L p)
  rw [hfun]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p => L p 1 := hL.clm_apply contDiff_const
  have hI : ContDiff ℝ (⊤ : ℕ∞) fun p => L p Complex.I := hL.clm_apply contDiff_const
  have hre : ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ => z.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ (⊤ : ℕ∞) fun z : ℂ => z.im := Complex.imCLM.contDiff
  exact ((hre.comp h1).mul (him.comp hI)).sub ((hre.comp hI).mul (him.comp h1))

theorem contDiff_inverse {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (L : P → (ℂ →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0) :
    ContDiff ℝ (⊤ : ℕ∞) fun p => (L p).inverse := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have h := contDiffAt_map_inverse (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (equivOfInj (L p) (hL0 p))
  rw [coe_equivOfInj] at h
  exact h.comp p hL.contDiffAt

theorem integral_comp_clm {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) (G : ℂ → F) :
    ∫ z, G (T z) = |(LinearMap.det (T : ℂ →ₗ[ℝ] ℂ))⁻¹| • ∫ u, G u := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) (det_ne_zero T h)
  have h1 : ∫ z, G (T z) = ∫ u, G u ∂(Measure.map ((equivOfInj T h).toHomeomorph.toMeasurableEquiv) volume) :=
    (integral_map_equiv ((equivOfInj T h).toHomeomorph.toMeasurableEquiv) G).symm
  have h2 : ((equivOfInj T h).toHomeomorph.toMeasurableEquiv : ℂ → ℂ) = ((T : ℂ →ₗ[ℝ] ℂ) : ℂ → ℂ) := by
    funext z; rfl
  rw [h1, h2, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

theorem integrable_comp_clm {F : Type} [NormedAddCommGroup F]
    (T : ℂ →L[ℝ] ℂ) (h : ∀ z : ℂ, T z = 0 → z = 0) {G : ℂ → F} (hG : Integrable G (volume : Measure ℂ)) :
    Integrable (fun z => G (T z)) (volume : Measure ℂ) := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure ℂ) (det_ne_zero T h)
  have h2 : ((equivOfInj T h).toHomeomorph.toMeasurableEquiv : ℂ → ℂ) = ((T : ℂ →ₗ[ℝ] ℂ) : ℂ → ℂ) := by
    funext z; rfl
  have h3 : Integrable G (Measure.map ((equivOfInj T h).toHomeomorph.toMeasurableEquiv) volume) := by
    rw [h2, hmap]; exact hG.smul_measure (by simp)
  exact (integrable_map_equiv _ G).mp h3

end CLM

section Bump
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_bump {S U : Set E} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ S, χ x = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball 0
  set U' : Set E := U ∩ Metric.ball 0 R with hU'
  have hU'o : IsOpen U' := hU.inter Metric.isOpen_ball
  have hd : Disjoint U'ᶜ S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hx ⟨hSU hxS, hR hxS⟩
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hU'o.isClosed_compl hS.isClosed hd
  obtain ⟨V, hVo, hsV, hV⟩ := eventually_nhdsSet_iff_exists.mp hf0
  have hts : tsupport (⇑f) ⊆ U' := by
    refine (closure_minimal (fun x hx => ?_) hVo.isClosed_compl).trans (Set.compl_subset_comm.mp hsV)
    exact fun hxV => hx (hV x hxV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, fun x hx => hf1.self_of_nhdsSet x hx,
    hts.trans Set.inter_subset_left⟩
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport _)
    (hts.trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
end Bump

theorem contDiff_paramIntegral
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (F : Q × Y → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (w : Y → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Q => ∫ y, (w y : ℝ) • F (q, y) ∂μ) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  let χ' : ContDiffBump q₀ := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨w', hw', hw'c, hw'1, -⟩ := exists_smooth_bump (E := Y) hwc isOpen_univ (Set.subset_univ _)
  let Ψ : Y × Q → ℂ := fun z => ((w' z.1 * (χ' : Q → ℝ) z.2 : ℝ)) • F (z.2, z.1)
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    refine ContDiff.smul ((hw'.comp contDiff_fst).mul (χ'.contDiff.comp contDiff_snd)) ?_
    exact hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hΨc : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro (hw'c.prod χ'.hasCompactSupport) fun z hz => ?_
    simp only [Set.mem_prod, not_and_or] at hz
    show ((w' z.1 * (χ' : Q → ℝ) z.2 : ℝ)) • F (z.2, z.1) = 0
    rcases hz with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport h, mul_zero, zero_smul]
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun q : Q => ∫ y, (w y) • Ψ (id y, q) ∂μ) :=
    MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport μ id continuous_id
      w hw.continuous hwc Ψ hΨ hΨc
  have hGI : ∀ q : Q, (∫ y, (w y) • Ψ (id y, q) ∂μ) =
      (((χ' : Q → ℝ) q : ℝ) : ℂ) * ∫ y, (w y : ℝ) • F (q, y) ∂μ := by
    intro q
    rw [← Complex.real_smul, ← integral_smul]
    congr 1
    funext y
    show (w y) • (((w' y * (χ' : Q → ℝ) q : ℝ)) • F (q, y)) = ((χ' : Q → ℝ) q) • ((w y : ℝ) • F (q, y))
    by_cases hy : w y = 0
    · rw [hy, zero_smul, zero_smul, smul_zero]
    · rw [hw'1 y (subset_tsupport _ hy), one_mul, smul_comm]
  have hev : (fun q : Q => ∫ y, (w y : ℝ) • F (q, y) ∂μ) =ᶠ[nhds q₀]
      fun q : Q => ∫ y, (w y) • Ψ (id y, q) ∂μ := by
    filter_upwards [Metric.closedBall_mem_nhds q₀ one_pos] with q hq
    rw [hGI q, χ'.one_of_mem_closedBall hq, Complex.ofReal_one, one_mul]
  exact hG.contDiffAt.congr_of_eventuallyEq hev

theorem integrableOn_log_normSq_add_sq (R c : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log (‖z‖ ^ 2 + c ^ 2)) (Metric.closedBall (0 : ℂ) R) volume := by
  by_cases hc : c ≠ 0
  · have hcont : Continuous fun z : ℂ => Real.log (‖z‖ ^ 2 + c ^ 2) := by
      refine continuous_iff_continuousAt.mpr fun z => ?_
      exact (Real.continuousAt_log (by positivity)).comp
        (by fun_prop : Continuous fun z : ℂ => ‖z‖ ^ 2 + c ^ 2).continuousAt
    exact hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)
  · push Not at hc
    subst hc
    have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 (R + 1) := fun z hz => by
      rw [Metric.mem_closedBall] at hz; rw [Metric.mem_ball]; linarith
    refine IntegrableOn.mono_set ?_ hsub
    set C : ℝ := 2 * (1 + (R + 1) ^ 2) with hC
    have hmeas : AEStronglyMeasurable (fun z : ℂ => Real.log (‖z‖ ^ 2 + (0 : ℝ) ^ 2)) volume :=
      (Real.measurable_log.comp (by fun_prop)).aestronglyMeasurable
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (by rw [Complex.finrank_real_complex]; norm_num)
      (α := 1) (C := C) (by rw [Complex.finrank_real_complex]; norm_num) ?_ hmeas
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.norm_eq_abs]
    by_cases hz0 : z = 0
    · subst hz0; simp
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    rw [Real.log_pow, Nat.cast_ofNat, Real.rpow_neg_one, ← div_eq_mul_inv, le_div_iff₀ hpos, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    by_cases h1 : ‖z‖ ≤ 1
    · have := Real.abs_log_mul_self_lt ‖z‖ hpos h1
      rw [abs_mul, abs_of_pos hpos] at this
      have : 0 ≤ (R + 1) ^ 2 := sq_nonneg _
      nlinarith
    · push Not at h1
      have hl : |Real.log ‖z‖| = Real.log ‖z‖ := abs_of_pos (Real.log_pos h1)
      rw [hl]
      have h2 : Real.log ‖z‖ ≤ ‖z‖ := (Real.log_le_sub_one_of_pos hpos).trans (by linarith)
      have h3 : ‖z‖ ^ 2 ≤ (R + 1) ^ 2 := by
        have : 0 ≤ R + 1 := by linarith [norm_nonneg z]
        nlinarith
      nlinarith

section Shear
variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]

def shear (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ)) : (P × V) × ℂ → P × (ℂ × V) :=
  fun y => (y.1.1, ((L y.1.1).inverse (y.2 - φ y.1.1 y.1.2), y.1.2))

def unshear (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ)) : P × (ℂ × V) → (P × V) × ℂ :=
  fun x => ((x.1, x.2.2), L x.1 x.2.1 + φ x.1 x.2.2)

theorem shear_unshear (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ))
    (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0) (x : P × (ℂ × V)) :
    shear L φ (unshear L φ x) = x := by
  obtain ⟨p, z, v⟩ := x
  show (p, ((L p).inverse (L p z + φ p v - φ p v), v)) = (p, (z, v))
  rw [add_sub_cancel_right, inverse_apply_apply (L p) (hL0 p)]

theorem unshear_shear (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ))
    (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0) (y : (P × V) × ℂ) :
    unshear L φ (shear L φ y) = y := by
  obtain ⟨⟨p, v⟩, u⟩ := y
  show ((p, v), L p ((L p).inverse (u - φ p v)) + φ p v) = ((p, v), u)
  rw [apply_inverse_apply (L p) (hL0 p), sub_add_cancel]

theorem shear_apply (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ))
    (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0) (p : P) (z : ℂ) (v : V) :
    shear L φ ((p, v), L p z + φ p v) = (p, (z, v)) :=
  shear_unshear L φ hL0 (p, (z, v))

theorem contDiff_shear (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (shear L φ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun y : (P × V) × ℂ => φ y.1.1 y.1.2 :=
    (hφ.comp (contDiff_fst.comp contDiff_fst)).clm_apply (contDiff_snd.comp contDiff_fst)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun y : (P × V) × ℂ => (L y.1.1).inverse :=
    (contDiff_inverse L hL hL0).comp (contDiff_fst.comp contDiff_fst)
  exact (contDiff_fst.comp contDiff_fst).prodMk
    ((h2.clm_apply (contDiff_snd.sub h1)).prodMk (contDiff_snd.comp contDiff_fst))

theorem contDiff_unshear (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (unshear L φ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : P × (ℂ × V) => φ x.1 x.2.2 :=
    (hφ.comp contDiff_fst).clm_apply (contDiff_snd.comp contDiff_snd)
  exact (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).prodMk
    (((hL.comp contDiff_fst).clm_apply (contDiff_fst.comp contDiff_snd)).add h1)

def shearHomeomorph (L : P → (ℂ →L[ℝ] ℂ)) (φ : P → (V →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L)
    (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    (P × V) × ℂ ≃ₜ P × (ℂ × V) where
  toFun := shear L φ
  invFun := unshear L φ
  left_inv := unshear_shear L φ hL0
  right_inv := shear_unshear L φ hL0
  continuous_toFun := (contDiff_shear L φ hL hL0 hφ).continuous
  continuous_invFun := (contDiff_unshear L φ hL hφ).continuous

end Shear

end ParamLogPotC

end

open ParamLogPotC in
theorem solution
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℂ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (L : P → (ℂ →L[ℝ] ℂ)) (hL : ContDiff ℝ (⊤ : ℕ∞) L) (hL0 : ∀ (p : P) (z : ℂ), L p z = 0 → z = 0)
    (φ : P → (V →L[ℝ] ℂ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∃ A B : P × ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (r : ℂ),
        Integrable (fun zv : ℂ × V =>
          g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ)) ((volume : Measure ℂ).prod μ) ∧
        ∫ zv : ℂ × V, g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ) ∂((volume : Measure ℂ).prod μ) =
          A (p, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B (p, r) := by
  classical

  set g₀ : (P × V) × ℂ → ℂ := g ∘ shear L φ with hg₀
  have hg₀s : ContDiff ℝ (⊤ : ℕ∞) g₀ := hg.comp (contDiff_shear L φ hL hL0 hφ)
  have hg₀c : HasCompactSupport g₀ := hgc.comp_homeomorph (shearHomeomorph L φ hL hL0 hφ)
  have hg₀_apply : ∀ (p : P) (z : ℂ) (v : V), g₀ ((p, v), L p z + φ p v) = g (p, (z, v)) := by
    intro p z v
    show g (shear L φ ((p, v), L p z + φ p v)) = g (p, (z, v))
    rw [shear_apply L φ hL0]

  obtain ⟨A₀, B₀, hA₀, hB₀, hD0⟩ :=
    MeasureTheory.exists_contDiff_integral_mul_log_normSq_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
      g₀ hg₀s hg₀c

  obtain ⟨SV, hSV⟩ : ∃ SV : Set V, SV = (fun x : P × (ℂ × V) => x.2.2) '' tsupport g := ⟨_, rfl⟩
  have hSVc : IsCompact SV := by rw [hSV]; exact hgc.image (continuous_snd.comp continuous_snd)
  have hgz : ∀ (p : P) (z : ℂ) (v : V), v ∉ SV → g (p, (z, v)) = 0 := by
    intro p z v hv
    exact image_eq_zero_of_notMem_tsupport fun h => hv (by rw [hSV]; exact ⟨_, h, rfl⟩)
  obtain ⟨χ, hχ, hχc, hχ1, -⟩ := exists_smooth_bump hSVc isOpen_univ (Set.subset_univ _)

  have hκs : ContDiff ℝ (⊤ : ℕ∞) fun p : P => |LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ)|⁻¹ := by
    rw [contDiff_iff_contDiffAt]
    intro p
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => |x|) (LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ)) :=
      contDiffAt_abs (det_ne_zero (L p) (hL0 p))
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) ((fun x : ℝ => |x|) ∘ fun p : P => LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ)) p :=
      ContDiffAt.comp p h1 (contDiff_det L hL).contDiffAt
    exact h2.inv (abs_ne_zero.mpr (det_ne_zero (L p) (hL0 p)))
  obtain ⟨IA, hIA⟩ : ∃ IA : P × ℂ → ℂ, IA = fun q => ∫ v, (χ v : ℝ) • A₀ ((q.1, v), q.2) ∂μ := ⟨_, rfl⟩
  obtain ⟨IB, hIB⟩ : ∃ IB : P × ℂ → ℂ, IB = fun q => ∫ v, (χ v : ℝ) • B₀ ((q.1, v), q.2) ∂μ := ⟨_, rfl⟩
  have hq : ContDiff ℝ (⊤ : ℕ∞) fun z : (P × ℂ) × V => ((z.1.1, z.2), z.1.2) :=
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).prodMk (contDiff_snd.comp contDiff_fst)
  have hIAs : ContDiff ℝ (⊤ : ℕ∞) IA := by
    rw [hIA]
    exact contDiff_paramIntegral μ (fun z : (P × ℂ) × V => A₀ ((z.1.1, z.2), z.1.2)) (hA₀.comp hq) χ hχ hχc
  have hIBs : ContDiff ℝ (⊤ : ℕ∞) IB := by
    rw [hIB]
    exact contDiff_paramIntegral μ (fun z : (P × ℂ) × V => B₀ ((z.1.1, z.2), z.1.2)) (hB₀.comp hq) χ hχ hχc
  refine ⟨fun q => ((|LinearMap.det (L q.1 : ℂ →ₗ[ℝ] ℂ)|⁻¹ : ℝ) : ℂ) * IA q,
    fun q => ((|LinearMap.det (L q.1 : ℂ →ₗ[ℝ] ℂ)|⁻¹ : ℝ) : ℂ) * IB q, ?_, ?_, fun p r => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp (hκs.comp contDiff_fst)).mul hIAs
  · exact (Complex.ofRealCLM.contDiff.comp (hκs.comp contDiff_fst)).mul hIBs

  set κ : ℝ := |LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ)|⁻¹ with hκ
  set f : ℂ × V → ℂ := fun zv : ℂ × V =>
    g (p, zv) * (Real.log (‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2) : ℂ) with hf
  set h : V → ℂ → ℂ := fun v u => g₀ ((p, v), u) * (Real.log (‖u‖ ^ 2 + ‖r‖ ^ 2) : ℂ) with hh
  have hfh : ∀ (v : V) (z : ℂ), f (z, v) = h v (L p z + φ p v) := by
    intro v z
    show g (p, (z, v)) * _ = g₀ ((p, v), L p z + φ p v) * _
    rw [hg₀_apply]

  obtain ⟨Cg, hCg⟩ := hg₀s.continuous.bounded_above_of_compact_support hg₀c
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  obtain ⟨R, hR⟩ := ((hg₀c.image continuous_snd).isBounded).subset_closedBall (0 : ℂ)
  have hsuppu : ∀ (v : V) (u : ℂ), g₀ ((p, v), u) ≠ 0 → u ∈ Metric.closedBall (0 : ℂ) R := by
    intro v u hne
    have hmem : ((p, v), u) ∈ tsupport g₀ := by
      by_contra hc; exact hne (image_eq_zero_of_notMem_tsupport hc)
    exact hR ⟨_, hmem, rfl⟩
  set Bnd : ℂ → ℝ := fun u => Cg * ‖Real.log (‖u‖ ^ 2 + ‖r‖ ^ 2)‖ with hBnd
  have hBnd0 : ∀ u, 0 ≤ Bnd u := fun u => mul_nonneg hCg0 (norm_nonneg _)
  have hbnd' : IntegrableOn Bnd (Metric.closedBall (0 : ℂ) R) (volume : Measure ℂ) :=
    (integrableOn_log_normSq_add_sq R ‖r‖).norm.const_mul Cg
  have hbnd : Integrable ((Metric.closedBall (0 : ℂ) R).indicator Bnd) (volume : Measure ℂ) :=
    hbnd'.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hh_le : ∀ (v : V) (u : ℂ), ‖h v u‖ ≤ (Metric.closedBall (0 : ℂ) R).indicator Bnd u := by
    intro v u
    by_cases hne : g₀ ((p, v), u) = 0
    · have : h v u = 0 := by show g₀ ((p, v), u) * _ = 0; rw [hne, zero_mul]
      rw [this, norm_zero]
      exact Set.indicator_nonneg (fun s _ => hBnd0 s) _
    · rw [Set.indicator_of_mem (hsuppu v u hne)]
      show ‖g₀ ((p, v), u) * (Real.log (‖u‖ ^ 2 + ‖r‖ ^ 2) : ℂ)‖ ≤ Cg * ‖Real.log (‖u‖ ^ 2 + ‖r‖ ^ 2)‖
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hCg _) (norm_nonneg _)
  have hh_meas : ∀ v : V, AEStronglyMeasurable (h v) (volume : Measure ℂ) := by
    intro v
    refine (((hg₀s.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul ?_)
    exact (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_log.comp (by fun_prop : Measurable fun u : ℂ => ‖u‖ ^ 2 + ‖r‖ ^ 2))).aestronglyMeasurable
  have hh_int : ∀ v : V, Integrable (h v) (volume : Measure ℂ) := fun v =>
    hbnd.mono' (hh_meas v) (Filter.Eventually.of_forall (hh_le v))

  have hf_slice : ∀ v : V, Integrable (fun z : ℂ => f (z, v)) (volume : Measure ℂ) := by
    intro v
    have h1 := integrable_comp_clm (L p) (hL0 p) ((hh_int v).comp_add_right (φ p v))
    refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
    exact (hfh v z).symm
  have hinner : ∀ v : V, ∫ z, f (z, v) =
      ((κ : ℝ) : ℂ) * (A₀ ((p, v), r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B₀ ((p, v), r)) := by
    intro v
    calc ∫ z, f (z, v) = ∫ z, (fun x : ℂ => h v (x + φ p v)) (L p z) := by
          congr 1; funext z; exact hfh v z
      _ = |(LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ))⁻¹| • ∫ x, h v (x + φ p v) :=
          integral_comp_clm (L p) (hL0 p) (fun x : ℂ => h v (x + φ p v))
      _ = |(LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ))⁻¹| • ∫ u, h v u := by
          rw [integral_add_right_eq_self (h v) (φ p v)]
      _ = ((κ : ℝ) : ℂ) * (A₀ ((p, v), r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B₀ ((p, v), r)) := by
          rw [abs_inv, Complex.real_smul]
          congr 1
          exact hD0 (p, v) r
  have hinner_norm : ∀ v : V, ∫ z, ‖f (z, v)‖ = κ * ∫ u, ‖h v u‖ := by
    intro v
    calc ∫ z, ‖f (z, v)‖ = ∫ z, (fun x : ℂ => ‖h v (x + φ p v)‖) (L p z) := by
          congr 1; funext z; rw [hfh v z]
      _ = |(LinearMap.det (L p : ℂ →ₗ[ℝ] ℂ))⁻¹| • ∫ x, ‖h v (x + φ p v)‖ :=
          integral_comp_clm (L p) (hL0 p) (fun x : ℂ => ‖h v (x + φ p v)‖)
      _ = κ * ∫ u, ‖h v u‖ := by
          rw [smul_eq_mul, abs_inv]
          congr 1
          exact integral_add_right_eq_self (fun u => ‖h v u‖) (φ p v)

  have hκ0 : 0 ≤ κ := inv_nonneg.mpr (abs_nonneg _)
  set M' : ℝ := κ * ∫ u, (Metric.closedBall (0 : ℂ) R).indicator Bnd u with hM'
  have hprof : ∀ v : V, ∫ z, ‖f (z, v)‖ ≤ SV.indicator (fun _ => M') v := by
    intro v
    by_cases hv : v ∈ SV
    · rw [Set.indicator_of_mem hv, hinner_norm v]
      refine mul_le_mul_of_nonneg_left ?_ hκ0
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbnd
        (Filter.Eventually.of_forall (hh_le v))
    · rw [Set.indicator_of_notMem hv]
      have : ∀ z : ℂ, f (z, v) = 0 := by
        intro z; show g (p, (z, v)) * _ = 0; rw [hgz p z v hv, zero_mul]
      simp [this]

  have hfm : Measurable f := by
    refine Measurable.mul ?_ ?_
    · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).measurable
    · have hc : Continuous fun zv : ℂ × V => ‖L p zv.1 + φ p zv.2‖ ^ 2 + ‖r‖ ^ 2 :=
        ((((L p).continuous.comp continuous_fst).add ((φ p).continuous.comp continuous_snd)).norm.pow 2).add
          continuous_const
      exact Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp hc.measurable)
  have hInt : Integrable f ((volume : Measure ℂ).prod μ) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hf_slice, ?_⟩
    have hconst : Integrable (SV.indicator fun _ => M') μ :=
      (integrableOn_const (hs := hSVc.measure_lt_top.ne)).integrable_indicator hSVc.isClosed.measurableSet
    refine hconst.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (hfm.stronglyMeasurable.norm.integral_prod_left (μ := (volume : Measure ℂ))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hprof v
  refine ⟨hInt, ?_⟩

  show ∫ z, f z ∂((volume : Measure ℂ).prod μ) =
    ((κ : ℝ) : ℂ) * IA (p, r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * (((κ : ℝ) : ℂ) * IB (p, r))
  rw [integral_prod_symm f hInt]
  have hiA : Integrable (fun v => (χ v : ℝ) • A₀ ((p, v), r)) μ :=
    ((hχ.continuous.smul (hA₀.continuous.comp ((continuous_const.prodMk continuous_id).prodMk
      continuous_const)))).integrable_of_hasCompactSupport hχc.smul_right
  have hiB : Integrable (fun v => (χ v : ℝ) • B₀ ((p, v), r)) μ :=
    ((hχ.continuous.smul (hB₀.continuous.comp ((continuous_const.prodMk continuous_id).prodMk
      continuous_const)))).integrable_of_hasCompactSupport hχc.smul_right
  have hG1 : ∫ v, ∫ z, f (z, v) ∂volume ∂μ = ∫ v, (χ v : ℝ) • ∫ z, f (z, v) ∂volume ∂μ := by
    congr 1; funext v
    by_cases hv : v ∈ SV
    · rw [hχ1 v hv, one_smul]
    · have : ∀ z : ℂ, f (z, v) = 0 := by
        intro z; show g (p, (z, v)) * _ = 0; rw [hgz p z v hv, zero_mul]
      simp [this]
  rw [hG1]
  simp_rw [hinner]
  have hpt : ∀ v : V, (χ v : ℝ) • (((κ : ℝ) : ℂ) *
      (A₀ ((p, v), r) + ((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * B₀ ((p, v), r))) =
      ((κ : ℝ) : ℂ) * ((χ v : ℝ) • A₀ ((p, v), r)) +
        (((‖r‖ ^ 2 * Real.log ‖r‖ : ℝ) : ℂ) * ((κ : ℝ) : ℂ)) * ((χ v : ℝ) • B₀ ((p, v), r)) := by
    intro v; simp only [Complex.real_smul]; ring
  simp_rw [hpt]
  rw [integral_add (hiA.const_mul _) (hiB.const_mul _), integral_const_mul, integral_const_mul, hIA, hIB]
  ring

end S_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_normSq_clm_add_normSq_eq_add_normSq_mul_log_mul_of_hasCompactSupport (solution)
