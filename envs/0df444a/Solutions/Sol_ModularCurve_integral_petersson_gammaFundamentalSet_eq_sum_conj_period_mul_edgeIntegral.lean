-- Prove2me | solution 1 for ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/f6fc3e1c-3956-53a3-8327-1da96ba78458

import Mathlib
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Definitions.Def_AutomorphicForm_Gamma0ExactVolume
import Theorems.Thm_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt
import Theorems.Thm_ModularCurve_gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
import Theorems.Thm_FLT_Gamma0FundamentalSet_integral_gammaFundamentalSet_eq_finsum_integral_fd
import Theorems.Thm_ModularCurve_exists_hasEquivariantPrimitive
import Theorems.Thm_ModularCurve_period_apply_eq_sub_of_hasEquivariantPrimitive
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral

noncomputable section

open UpperHalfPlane Filter Complex MeasureTheory Asymptotics
open scoped MatrixGroups Topology ModularForm ComplexConjugate Real NNReal Pointwise

namespace ModularCurve
p2m_export "ModularCurve" "period HasEquivariantPrimitive gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add exists_hasEquivariantPrimitive period_apply_eq_sub_of_hasEquivariantPrimitive"
namespace BilinearUnfolded
p2m_open "ModularCurve"

theorem det_entries (γ : SL(2, ℤ)) :
    ((γ 0 0 : ℤ) : ℂ) * γ 1 1 - ((γ 0 1 : ℤ) : ℂ) * γ 1 0 = 1 := by
  have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact_mod_cast this

theorem denom_eq (γ : SL(2, ℤ)) (z : ℂ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  simp [denom]

theorem num_eq (γ : SL(2, ℤ)) (z : ℂ) :
    num γ z = ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) := by
  simp [num]

theorem denom_ne_zero' (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : denom γ z ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hz.ne'

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem hasDerivAt_denom (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (denom (γ : GL (Fin 2) ℝ)) ((γ 1 0 : ℤ) : ℂ) z := by
  have : denom (γ : GL (Fin 2) ℝ) = fun z => ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) :=
    funext (denom_eq γ)
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((γ 1 0 : ℤ) : ℂ)).add_const ((γ 1 1 : ℤ) : ℂ)

theorem hasDerivAt_num (γ : SL(2, ℤ)) (z : ℂ) :
    HasDerivAt (num (γ : GL (Fin 2) ℝ)) ((γ 0 0 : ℤ) : ℂ) z := by
  have : num (γ : GL (Fin 2) ℝ) = fun z => ((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ) :=
    funext (num_eq γ)
  rw [this]
  simpa using ((hasDerivAt_id z).const_mul ((γ 0 0 : ℤ) : ℂ)).add_const ((γ 0 1 : ℤ) : ℂ)

theorem hasDerivAt_mob (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    HasDerivAt (mob γ) (1 / denom γ z ^ 2) z := by
  have hD := denom_ne_zero' γ hz
  have h := (hasDerivAt_num γ z).div (hasDerivAt_denom γ z) hD
  convert h using 1
  all_goals try rfl
  rw [num_eq, denom_eq, ← det_entries γ]
  simp only [denom_eq] at hD ⊢
  field_simp
  ring

theorem continuousOn_mob (γ : SL(2, ℤ)) : ContinuousOn (mob γ) {z : ℂ | 0 < z.im} :=
  fun z hz => (hasDerivAt_mob γ hz).continuousAt.continuousWithinAt

theorem coe_smul_ofComplex (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) :
    ((γ • ofComplex z : ℍ) : ℂ) = mob γ z := by
  rw [coe_smul, ofComplex_apply_of_im_pos hz]

theorem im_mob_pos (γ : SL(2, ℤ)) {z : ℂ} (hz : 0 < z.im) : 0 < (mob γ z).im := by
  rw [← coe_smul_ofComplex γ hz]; exact (γ • ofComplex z).im_pos

variable {N : ℕ}

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

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (f : CuspForm Γ 2) (σ : SL(2, ℤ))

scoped instance isArithmetic_conj :
    (ConjAct.toConjAct ((σ : GL (Fin 2) ℝ)⁻¹) •
      ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
  have h := Subgroup.IsArithmetic.conj ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
    (Matrix.SpecialLinearGroup.mapGL ℚ σ)⁻¹
  simp only [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv,
    Matrix.SpecialLinearGroup.map_mapGL] at h
  exact h

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

section Primitive

variable {U : ℍ → ℂ} {k : ℍ → ℂ} (σ : SL(2, ℤ))

def V (U : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := U (σ • ofComplex z)

theorem V_eventuallyEq {z : ℂ} (hz : 0 < z.im) :
    V U σ =ᶠ[𝓝 z] (U ∘ ofComplex) ∘ mob σ := by
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply, V]
  rw [← coe_smul_ofComplex σ hw, ofComplex_apply]

theorem hasDerivAt_V (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (k τ) τ) {z : ℂ}
    (hz : 0 < z.im) : HasDerivAt (V U σ) (slashC k σ z) z := by
  have h1 : HasDerivAt (U ∘ ofComplex) (k (σ • ofComplex z)) (mob σ z) := by
    have := hU (σ • ofComplex z); rwa [coe_smul_ofComplex σ hz] at this
  have h2 := (h1.comp z (hasDerivAt_mob σ hz)).congr_of_eventuallyEq (V_eventuallyEq σ hz)
  refine h2.congr_deriv ?_
  rw [slashC, mul_one_div, ofComplex_apply_of_im_pos hz]

theorem continuousOn_V (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (k τ) τ) :
    ContinuousOn (V U σ) {z : ℂ | 0 < z.im} :=
  fun _ hz => (hasDerivAt_V σ hU hz).continuousAt.continuousWithinAt

theorem V_bound (hU : ∀ τ : ℍ, HasDerivAt (U ∘ ofComplex) (k τ) τ)
    (hL : ∃ L : ℂ, Tendsto (fun w : ℍ => U (σ • w)) atImInfty (𝓝 L)) :
    ∃ C, ∀ z : ℂ, 1 / 2 ≤ z.im → |z.re| ≤ 1 → ‖V U σ z‖ ≤ C := by
  obtain ⟨L, hL⟩ := hL
  have hev : ∀ᶠ w : ℍ in atImInfty, ‖U (σ • w)‖ ≤ ‖L‖ + 1 := by
    have := (hL.norm.eventually (gt_mem_nhds (lt_add_one ‖L‖)))
    exact this.mono fun w hw => hw.le
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  set M : ℝ := max A 1
  set Kc : Set ℂ := Set.Icc (-1 : ℝ) 1 ×ℂ Set.Icc (1 / 2 : ℝ) M
  have hKc : IsCompact Kc :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
      ((Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _))
  have hsub : Kc ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have := (Complex.mem_reProdIm.mp hz).2.1
    show 0 < z.im
    linarith
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn ((continuousOn_V σ hU).mono hsub)
  refine ⟨max C₁ (‖L‖ + 1), fun z hz hre => ?_⟩
  have hz0 : 0 < z.im := by linarith
  rcases le_or_gt z.im M with h | h
  · refine (hC₁ z ?_).trans (le_max_left _ _)
    exact Complex.mem_reProdIm.mpr ⟨abs_le.mp hre, hz, h⟩
  · have hA' : A ≤ (ofComplex z).im := by
      rw [ofComplex_apply_of_im_pos hz0]
      exact (le_max_left A 1).trans h.le
    exact (hA (ofComplex z) hA').trans (le_max_right _ _)

def D (a b : ℂ) : ℂ →L[ℝ] ℂ :=
  a • ContinuousLinearMap.id ℝ ℂ + b • (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[scoped simp] theorem D_apply (a b v : ℂ) : D a b v = a * v + b * conj v := by
  simp [D]

theorem norm_D_le (a b : ℂ) : ‖D a b‖ ≤ ‖a‖ + ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [D_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul]
  · rw [norm_mul, Complex.norm_conj]

theorem continuous_D : Continuous fun p : ℂ × ℂ => D p.1 p.2 :=
  (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem I_smul_D_sub (a b : ℂ) : Complex.I • D a b 1 - D a b Complex.I = 2 * Complex.I * b := by
  simp only [D_apply, smul_eq_mul, map_one, Complex.conj_I]
  ring

theorem hasFDerivAt_conj_mul {V₀ G : ℂ → ℂ} {z K G' : ℂ} (hV : HasDerivAt V₀ K z)
    (hG : HasDerivAt G G' z) :
    HasFDerivAt (fun w => conj (V₀ w) * G w) (D (conj (V₀ z) * G') (G z * conj K)) z := by
  have h1 : HasFDerivAt (fun w => conj (V₀ w))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
        ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) K).restrictScalars ℝ)) z :=
    Complex.conjCLE.hasFDerivAt.comp z (hV.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt G ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) G').restrictScalars ℝ)
      z := hG.hasFDerivAt.restrictScalars ℝ
  refine (h1.mul h2).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp [D, mul_comm, mul_left_comm, mul_assoc]

end Primitive

section Tile

variable {N : ℕ} [NeZero N] (k g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {U : ℍ → ℂ}
  (σ : SL(2, ℤ))

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
  ⟨im_gt_of_mem_fdC hz, by have := hz.1; beta_reduce at this ⊢; linarith⟩

theorem im_pos_of_mem_Ubox {z : ℂ} (hz : z ∈ Ubox) : 0 < z.im := by
  have := hz.1; linarith

def Φt (U : ℍ → ℂ) (g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ := conj (V U σ z) * slashC g σ z

def Φt' (U : ℍ → ℂ) (k g : ℍ → ℂ) (σ : SL(2, ℤ)) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  D (conj (V U σ z) * deriv (slashC g σ) z) (slashC g σ z * conj (slashC k σ z))

variable (hU : ModularCurve.HasEquivariantPrimitive N k U)
include hU

theorem hasFDerivAt_Φt {z : ℂ} (hz : 0 < z.im) :
    HasFDerivAt (Φt U g σ) (Φt' U k g σ z) z :=
  hasFDerivAt_conj_mul (hasDerivAt_V σ hU.1 hz) (hasDerivAt_slashC g σ hz)

theorem continuousOn_deriv_slashC :
    ContinuousOn (deriv (slashC g σ)) {z : ℂ | 0 < z.im} :=
  ((differentiableOn_slashC g σ).analyticOnNhd isOpen_upperHalfPlaneSet).deriv.continuousOn

theorem continuousOn_Φt' : ContinuousOn (Φt' U k g σ) {z : ℂ | 0 < z.im} := by
  have h1 : ContinuousOn (fun z => conj (V U σ z)) {z : ℂ | 0 < z.im} :=
    Complex.continuous_conj.comp_continuousOn' (continuousOn_V σ hU.1)
  have h2 : ContinuousOn (fun z => conj (slashC k σ z)) {z : ℂ | 0 < z.im} :=
    Complex.continuous_conj.comp_continuousOn' (continuousOn_slashC k σ)
  have ha : ContinuousOn (fun z => conj (V U σ z) * deriv (slashC g σ) z) {z : ℂ | 0 < z.im} :=
    h1.mul (continuousOn_deriv_slashC k g σ hU)
  have hb : ContinuousOn (fun z => slashC g σ z * conj (slashC k σ z)) {z : ℂ | 0 < z.im} :=
    (continuousOn_slashC g σ).mul h2
  have hp := ha.prodMk hb
  have e : Φt' U k g σ = (fun p : ℂ × ℂ => D p.1 p.2) ∘ fun z =>
      (conj (V U σ z) * deriv (slashC g σ) z, slashC g σ z * conj (slashC k σ z)) := rfl
  rw [e]
  exact continuous_D.comp_continuousOn hp

theorem Φt_bounds : ∃ δ > 0,
    (∃ C : ℝ, ∀ z ∈ Ubox, ‖Φt U g σ z‖ ≤ C * Real.exp (-δ * z.im)) ∧
    (∃ C : ℝ, ∀ z ∈ Ubox, ‖Φt' U k g σ z‖ ≤ C * Real.exp (-δ * z.im)) := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  obtain ⟨c₁, hc₁, C₁, hC₁0, hC₁⟩ := slashC_decay g σ h2
  obtain ⟨c₂, hc₂, C₂, hC₂0, hC₂⟩ := deriv_slashC_decay g σ h2
  obtain ⟨c₃, hc₃, C₃, hC₃0, hC₃⟩ := slashC_decay k σ h2
  obtain ⟨CV, hCV⟩ := V_bound σ hU.1 (hU.2.2.2 σ)
  set δ := min c₁ (min c₂ c₃) with hδ
  have hδ₁ : δ ≤ c₁ := min_le_left _ _
  have hδ₂ : δ ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₃ : δ ≤ c₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hG := decay_weaken hC₁0 hδ₁ h2.le hC₁
  have hG' := decay_weaken hC₂0 hδ₂ h2.le hC₂
  have hK := decay_weaken hC₃0 hδ₃ h2.le hC₃
  refine ⟨δ, lt_min hc₁ (lt_min hc₂ hc₃), ⟨CV * C₁, fun z hz => ?_⟩, ⟨CV * C₂ + C₁ * C₃, fun z hz => ?_⟩⟩
  · have hzi : 1 / 2 ≤ z.im := hz.1.le
    have hV := hCV z hzi hz.2.le
    rw [Φt, norm_mul, Complex.norm_conj, mul_assoc]
    exact mul_le_mul hV (hG z hzi) (norm_nonneg _) ((norm_nonneg _).trans hV)
  · have hzi : 1 / 2 ≤ z.im := hz.1.le
    have hV := hCV z hzi hz.2.le
    have hCV0 : 0 ≤ CV := (norm_nonneg _).trans hV
    have he : Real.exp (-δ * z.im) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 < δ := lt_min hc₁ (lt_min hc₂ hc₃)
      nlinarith
    refine (norm_D_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, add_mul]
    refine add_le_add ?_ ?_
    · rw [mul_assoc]
      exact mul_le_mul hV (hG' z hzi) (norm_nonneg _) hCV0
    · calc ‖slashC g σ z‖ * ‖slashC k σ z‖
          ≤ C₁ * (C₃ * Real.exp (-δ * z.im)) :=
            mul_le_mul ((hG z hzi).trans (by nlinarith)) (hK z hzi) (norm_nonneg _) hC₁0
        _ = C₁ * C₃ * Real.exp (-δ * z.im) := by ring

theorem tile_identity :
    (∫ z in fdC, 2 * Complex.I * (slashC g σ z * conj (slashC k σ z))) =
      Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φt U g σ (1 / 2 + y * Complex.I)) -
        Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φt U g σ (-(1 / 2) + y * Complex.I)) -
        ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          Φt U g σ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) := by
  obtain ⟨δ, hδ, hΦ, hΦ'⟩ := Φt_bounds k g σ hU
  have hE := Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt (Φt U g σ)
    (Φt' U k g σ) Ubox δ hδ isOpen_Ubox fdC_subset_Ubox
    (fun z hz => hasFDerivAt_Φt k g σ hU (im_pos_of_mem_Ubox hz))
    ((continuousOn_Φt' k g σ hU).mono fun z hz => im_pos_of_mem_Ubox hz) hΦ hΦ'
  rw [← hE]
  refine setIntegral_congr_fun measurableSet_fdC fun z _ => ?_
  simp only [Φt']
  rw [I_smul_D_sub]

end Tile

section Edges

theorem sqrt3_div_two_gt : (1 : ℝ) / 2 < Real.sqrt 3 / 2 := by
  have : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem ray_mem_Ubox {y : ℝ} (hy : y ∈ Set.Ioi (Real.sqrt 3 / 2)) :
    (-(1 / 2) + y * Complex.I : ℂ) ∈ Ubox := by
  refine ⟨?_, ?_⟩
  · show 1 / 2 < (-(1 / 2) + y * Complex.I : ℂ).im
    simpa using sqrt3_div_two_gt.trans hy
  · show |(-(1 / 2) + y * Complex.I : ℂ).re| < 1
    rw [show (-(1 / 2) + y * Complex.I : ℂ).re = -(1 / 2) by simp, abs_neg,
      abs_of_pos (by norm_num)]
    norm_num

theorem integrableOn_ray {F : ℂ → ℂ} (hc : ContinuousOn F {z : ℂ | 0 < z.im}) {C δ : ℝ}
    (hδ : 0 < δ) (hb : ∀ z ∈ Ubox, ‖F z‖ ≤ C * Real.exp (-δ * z.im)) :
    IntegrableOn (fun y : ℝ => F (-(1 / 2) + y * Complex.I)) (Set.Ioi (Real.sqrt 3 / 2)) := by
  have hpath : Continuous fun y : ℝ => (-(1 / 2) + y * Complex.I : ℂ) := by fun_prop
  have hcont : ContinuousOn (fun y : ℝ => F (-(1 / 2) + y * Complex.I))
      (Set.Ioi (Real.sqrt 3 / 2)) :=
    hc.comp hpath.continuousOn fun y hy => im_pos_of_mem_Ubox (ray_mem_Ubox hy)
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi _ hδ).const_mul C)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy => ?_
  have := hb _ (ray_mem_Ubox hy)
  simpa using this

theorem intervalIntegrable_arc {F : ℂ → ℂ} (hc : ContinuousOn F {z : ℂ | 0 < z.im}) :
    IntervalIntegrable (fun θ : ℝ => F (Complex.exp (θ * Complex.I)) *
      (Complex.I * Complex.exp (θ * Complex.I))) volume (Real.pi / 3) (2 * Real.pi / 3) := by
  refine ContinuousOn.intervalIntegrable ?_
  have hpath : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I) := by fun_prop
  have hmem : ∀ θ ∈ Set.uIcc (Real.pi / 3) (2 * Real.pi / 3),
      Complex.exp (θ * Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
    show 0 < (Complex.exp (θ * Complex.I)).im
    rw [Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos, hθ.1])
      (by linarith [Real.pi_pos, hθ.2])
  have h2 : Continuous fun θ : ℝ => Complex.I * Complex.exp (θ * Complex.I) := by fun_prop
  exact (hc.comp hpath.continuousOn hmem).mul h2.continuousOn

end Edges

section Pairing

variable {N : ℕ} [NeZero N] (k g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) {U : ℍ → ℂ}

open Classical in

def cχ (N : ℕ) [NeZero N] (k : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (γ : SL(2, ℤ)) : ℂ :=
  if h : γ ∈ CongruenceSubgroup.Gamma0 N then conj (ModularCurve.period N ⟨γ, h⟩ k) else 0

theorem cχ_coe (γ : CongruenceSubgroup.Gamma0 N) : cχ N k γ = conj (ModularCurve.period N γ k) := by
  simp [cχ, γ.2]

theorem g_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    g (γ • τ) = denom (γ : GL (Fin 2) ℝ) τ ^ 2 * g τ := by
  have := SlashInvariantForm.slash_action_eqn_SL'' g hγ τ
  simpa using this

variable (hU : ModularCurve.HasEquivariantPrimitive N k U)
include hU

theorem U_smul {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    U (γ • τ) = U τ + ModularCurve.period N ⟨γ, hγ⟩ k := by
  have h1 := hU.2.2.1.sub_eq_period ⟨γ, hγ⟩ τ
  have h2 := ModularCurve.period_apply_eq_sub_of_hasEquivariantPrimitive N k hU ⟨γ, hγ⟩
  rw [h2]
  change U (γ • τ) - U τ = U (γ • UpperHalfPlane.I) - U UpperHalfPlane.I at h1
  change U (γ • τ) = U τ + (U (γ • UpperHalfPlane.I) - U UpperHalfPlane.I)
  rw [← h1]; ring

theorem twist_law (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    conj (U (γ • τ)) * g (γ • τ) / denom (γ : GL (Fin 2) ℝ) τ ^ 2 =
      conj (U τ) * g τ + cχ N k γ * g τ := by
  have hD : denom (γ : GL (Fin 2) ℝ) τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  rw [U_smul k hU hγ, g_smul g hγ, map_add, cχ, dif_pos hγ]
  field_simp

theorem Φt_eq (σ : SL(2, ℤ)) (z : ℂ) :
    Φt U g σ z = conj (U (σ • ofComplex z)) * g (σ • ofComplex z) /
      denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2 := by
  rw [Φt, V, slashC, mul_div_assoc]

variable [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]

theorem side_pairing :
    ((∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∫ y in Set.Ioi (Real.sqrt 3 / 2),
        Φt U g (Quotient.out q)⁻¹ (1 / 2 + y * Complex.I)) =
      (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∫ y in Set.Ioi (Real.sqrt 3 / 2),
        Φt U g (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) +
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        cχ N k ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
          ∫ y in Set.Ioi (Real.sqrt 3 / 2),
            slashC g (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) ∧
    2 * (∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
        Φt U g (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
          (Complex.I * Complex.exp (θ * Complex.I))) =
      -∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
        cχ N k ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
          ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            slashC g (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
              (Complex.I * Complex.exp (θ * Complex.I)) := by
  refine ModularCurve.gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
    (CongruenceSubgroup.Gamma0 N) (fun τ => conj (U τ) * g τ) g (cχ N k)
    (fun γ hγ τ => twist_law k g hU γ hγ τ) (fun σ z => Φt U g σ z) (fun σ z => slashC g σ z)
    (fun σ z => Φt_eq k g hU σ z) (fun σ z => rfl) (Set.Ioi (Real.sqrt 3 / 2)) measurableSet_Ioi
    (Set.Ioi_subset_Ioi (by positivity)) (fun q => ?_) (fun q => ?_) (fun q => ?_) (fun q => ?_)
  · obtain ⟨δ, hδ, ⟨C, hC⟩, -⟩ := Φt_bounds k g (Quotient.out q)⁻¹ hU
    have hc : ContinuousOn (Φt U g (Quotient.out q)⁻¹) {z : ℂ | 0 < z.im} :=
      (Complex.continuous_conj.comp_continuousOn' (continuousOn_V _ hU.1)).mul
        (continuousOn_slashC g _)
    exact integrableOn_ray hc hδ hC
  · obtain ⟨c, hc, C, -, hC⟩ := slashC_decay g (Quotient.out q)⁻¹ (by norm_num : (0 : ℝ) < 1 / 2)
    exact integrableOn_ray (continuousOn_slashC g _) hc fun z hz => hC z hz.1.le
  · exact intervalIntegrable_arc
      ((Complex.continuous_conj.comp_continuousOn' (continuousOn_V _ hU.1)).mul
        (continuousOn_slashC g _))
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

variable {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
  (k g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)

theorem integrableOn_petersson :
    IntegrableOn (UpperHalfPlane.petersson 2 k g)
      (FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left 2 _ k g
  have hc : Continuous (UpperHalfPlane.petersson 2 k g) :=
    UpperHalfPlane.petersson_continuous 2 (CuspFormClass.holo k).continuous
      (CuspFormClass.holo g).continuous
  exact Measure.integrableOn_of_bounded
    (FLT.Gamma0FundamentalSet.volume_gamma0_lt_top N).ne hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem lhs_unfold :
    ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N),
        UpperHalfPlane.petersson 2 k g τ =
      ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ∫ z in fdC,
        slashC g (Quotient.out q)⁻¹ z * conj (slashC k (Quotient.out q)⁻¹ z) := by
  rw [FLT.Gamma0FundamentalSet.integral_gammaFundamentalSet_eq_finsum_integral_fd
    (FLT.Gamma0ExactVolume.neg_one_mem_Gamma0_all N) _ (integrableOn_petersson k g),
    finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun q _ => ?_
  set σ : SL(2, ℤ) := (Quotient.out q)⁻¹
  calc ∫ τ in ModularGroup.fd, UpperHalfPlane.petersson 2 k g (σ • τ)
      = ∫ τ in ModularGroup.fd, (slashC g σ τ * conj (slashC k σ τ)) * ((τ.im : ℝ) : ℂ) ^ 2 := by
        refine setIntegral_congr_fun measurableSet_fd fun τ _ => ?_
        rw [← UpperHalfPlane.petersson_slash_SL 2 k g σ τ, UpperHalfPlane.petersson, slashC_coe,
          slashC_coe]
        simp only [zpow_ofNat]
        ring
    _ = ∫ z in fdC, slashC g σ (ofComplex z) * conj (slashC k σ (ofComplex z)) :=
        setIntegral_fd_mul_im_sq _
    _ = ∫ z in fdC, slashC g σ z * conj (slashC k σ z) := by
        refine setIntegral_congr_fun measurableSet_fdC fun z hz => ?_
        have : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hz.2.2]
        rw [this]

end LHS

end ModularCurve.BilinearUnfolded
p2m_reactivate "P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.ModularCurve P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.ModularCurve.BilinearUnfolded"
p2m_reactivate "P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral.ModularCurve"

open ModularCurve.BilinearUnfolded in
theorem solution
    {N : ℕ} [NeZero N] [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (k g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (γT γS : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → CongruenceSubgroup.Gamma0 N)
    (hT : ∀ q, ((γT q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : CongruenceSubgroup.Gamma0 N) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (G : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet (CongruenceSubgroup.Gamma0 N),
        UpperHalfPlane.petersson 2 k g τ) =
      Complex.I / 2 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          conj (ModularCurve.period N (γT q) k) *
            (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
        1 / 4 * ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
          conj (ModularCurve.period N (γS q) k) *
            (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) := by
  obtain ⟨U, hU⟩ := ModularCurve.exists_hasEquivariantPrimitive N k
  have hG' : G = fun q => slashC g (Quotient.out q)⁻¹ := by
    funext q z; exact hG q z
  subst hG'
  beta_reduce
  have hcT : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      cχ N k ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) =
        conj (ModularCurve.period N (γT q) k) := fun q => by
    rw [← hT q, cχ_coe]
  have hcS : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      cχ N k ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) =
        conj (ModularCurve.period N (γS q) k) := fun q => by
    rw [← hS q, cχ_coe]
  obtain ⟨e2, e3⟩ := side_pairing k g hU
  simp only [hcT, hcS] at e2 e3
  have e1 : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      2 * Complex.I * ∫ z in fdC, slashC g (Quotient.out q)⁻¹ z *
          conj (slashC k (Quotient.out q)⁻¹ z) =
        Complex.I * (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            Φt U g (Quotient.out q)⁻¹ (1 / 2 + y * Complex.I)) -
          Complex.I * (∫ y in Set.Ioi (Real.sqrt 3 / 2),
            Φt U g (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) -
          ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φt U g (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
              (Complex.I * Complex.exp (θ * Complex.I)) := fun q => by
    rw [← smul_eq_mul Complex.I, ← smul_eq_mul Complex.I,
      ← tile_identity k g (Quotient.out q)⁻¹ hU, ← integral_const_mul]
  have e1s := Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => e1 q
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum] at e1s
  rw [lhs_unfold k g]
  linear_combination (1 / 2 : ℂ) * e1s + (Complex.I / 2) * e2 - (1 / 4 : ℂ) * e3

end
end S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral
end P2MW
export P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_period_mul_edgeIntegral (solution)
