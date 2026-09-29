-- Prove2me | solution 1 for ModularForm.exists_gamma0_coe_eq_serreDerivative
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1df35735-e6a9-5904-9c24-88b92209da1d

import Definitions.Def_CuspForm_ModPForms
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_coe_eq_serreDerivative

set_option autoImplicit false

p2m_open "UpperHalfPlane~I"
open Complex Real Matrix.SpecialLinearGroup EisensteinSeries Function
open ModularForm Derivative
open scoped MatrixGroups ModularForm Manifold Topology ArithmeticFunction.sigma

namespace E34S

section DSlash

variable {f : ℍ → ℂ} (γ : SL(2, ℤ)) (k : ℤ)

private lemma det_mapGL_eq_one : ((γ : GL (Fin 2) ℝ)).val.det = 1 := by
  show ((↑γ : Matrix (Fin 2) (Fin 2) ℤ).map ((Int.cast : ℤ → ℝ))).det = 1
  have h := γ.det_coe
  simp only [Matrix.det_fin_two, Matrix.map_apply] at h ⊢
  exact_mod_cast h

private lemma det_mapGL_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ)).val.det := by
  rw [det_mapGL_eq_one]; exact one_pos

private lemma SL_smul_eq_GL_smul (τ : ℍ) : γ • τ = (γ : GL (Fin 2) ℝ) • τ := rfl

private lemma mdiff_smul_comp (hf : MDiff f) : MDiff (fun τ : ℍ ↦ f (γ • τ)) := by
  have hg := UpperHalfPlane.mdifferentiable_smul (det_mapGL_pos γ)
  exact fun τ ↦ (hf (γ • τ)).comp τ (hg τ)

private lemma SL_slash_eq_mul : (f ∣[k] γ)
    = (fun τ : ℍ ↦ f (γ • τ)) * (fun τ : ℍ ↦ (UpperHalfPlane.denom γ τ) ^ (-k : ℤ)) :=
  funext fun τ ↦ ModularForm.SL_slash_apply (f := f) (k := k) γ τ

private lemma D_smul_comp (hf : MDiff f) (τ : ℍ) :
    D (fun z : ℍ ↦ f (γ • z)) τ
      = (D f) (γ • τ) * (UpperHalfPlane.denom γ τ)⁻¹ ^ 2 := by
  unfold normalizedDerivOfComplex

  have hchain : ((fun z : ℍ ↦ f (γ • z)) ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (f ∘ ofComplex) ∘ (fun z ↦ (↑((γ : GL (Fin 2) ℝ) • ofComplex z) : ℂ)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    show f (γ • ofComplex z) = (f ∘ ofComplex) ↑((γ : GL (Fin 2) ℝ) • ofComplex z)
    rw [Function.comp_apply, ofComplex_apply, ← SL_smul_eq_GL_smul]
  rw [hchain.deriv_eq]

  have hF : DifferentiableAt ℂ (f ∘ ofComplex) ↑((γ : GL (Fin 2) ℝ) • τ) := by
    have := UpperHalfPlane.mdifferentiableAt_iff.mp (hf (γ • τ))
    rwa [SL_smul_eq_GL_smul] at this
  have hmobdiff : DifferentiableAt ℂ
      (fun z ↦ (↑((γ : GL (Fin 2) ℝ) • ofComplex z) : ℂ)) ↑τ :=
    (UpperHalfPlane.hasStrictDerivAt_smul (det_mapGL_pos γ) τ).hasDerivAt.differentiableAt
  have heval : (fun z ↦ (↑((γ : GL (Fin 2) ℝ) • ofComplex z) : ℂ)) ↑τ
      = ↑((γ : GL (Fin 2) ℝ) • τ) := by
    show (↑((γ : GL (Fin 2) ℝ) • (ofComplex ↑τ : ℍ)) : ℂ) = _
    rw [ofComplex_apply]
  rw [deriv_comp_of_eq (x := (τ : ℂ)) hF hmobdiff heval,
    UpperHalfPlane.deriv_smul (det_mapGL_pos γ) τ,
    show ofComplex (↑τ : ℂ) = τ from ofComplex_apply τ, ← SL_smul_eq_GL_smul,
    show ((((γ : GL (Fin 2) ℝ)).val.det : ℂ)) = 1 by exact_mod_cast det_mapGL_eq_one γ]
  rw [one_div, inv_pow]; ring

private lemma D_denom_zpow (τ : ℍ) :
    D (fun z : ℍ ↦ (UpperHalfPlane.denom γ z) ^ (-k : ℤ)) τ
      = (2 * π * I)⁻¹ *
          ((-k : ℂ) * ((γ : GL (Fin 2) ℝ) 1 0 : ℝ)
            * (UpperHalfPlane.denom γ τ) ^ (-k - 1 : ℤ)) := by
  unfold normalizedDerivOfComplex
  have hee : ((fun z : ℍ ↦ (UpperHalfPlane.denom γ z) ^ (-k : ℤ)) ∘ ofComplex)
      =ᶠ[𝓝 (τ : ℂ)] fun z ↦ (UpperHalfPlane.denom γ z) ^ (-k : ℤ) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    show (UpperHalfPlane.denom γ (↑(ofComplex z) : ℂ)) ^ (-k : ℤ)
      = (UpperHalfPlane.denom γ z) ^ (-k : ℤ)
    rw [ofComplex_apply_of_im_pos hz]
  rw [hee.deriv_eq]
  have hdz := UpperHalfPlane.denom_ne_zero γ τ
  have hd : HasDerivAt (fun z ↦ UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z)
      (((γ : GL (Fin 2) ℝ) 1 0 : ℝ) : ℂ) (τ : ℂ) := by
    have := ((hasDerivAt_id (τ : ℂ)).const_mul
      (((γ : GL (Fin 2) ℝ) 1 0 : ℝ) : ℂ)).add_const (((γ : GL (Fin 2) ℝ) 1 1 : ℝ) : ℂ)
    simpa [UpperHalfPlane.denom] using this
  have hcomp := (hasDerivAt_zpow (-k) _ (Or.inl hdz)).comp (τ : ℂ) hd
  have : (fun z ↦ (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ) z) ^ (-k : ℤ))
      = (fun x ↦ x ^ (-k : ℤ)) ∘ (UpperHalfPlane.denom (γ : GL (Fin 2) ℝ)) := rfl
  rw [this, hcomp.deriv]
  push_cast
  ring

private theorem D_SL_slash (hf : MDiff f) (τ : ℍ) :
    D (f ∣[k] γ) τ
      = ((D f) ∣[(k + 2 : ℤ)] γ) τ
          - (k : ℂ) * ((2 * π * I)⁻¹) ^ 2 * D2 γ τ * (f ∣[k] γ) τ := by
  have hfγ := mdiff_smul_comp γ hf
  have hjγ := UpperHalfPlane.mdifferentiable_denom_zpow (γ : GL (Fin 2) ℝ) (-k)
  have hprod := congrFun (normalizedDerivOfComplex_mul _ _ hfγ hjγ) τ
  rw [show (f ∣[k] γ) = _ from SL_slash_eq_mul γ k, hprod, Pi.add_apply, Pi.mul_apply,
    Pi.mul_apply, D_smul_comp γ hf τ, D_denom_zpow γ k τ,
    ModularForm.SL_slash_apply (f := D f) (k := k + 2) γ τ]
  simp only [Pi.mul_apply]
  have hdz := UpperHalfPlane.denom_ne_zero γ τ
  have h2πi : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hcast : (((γ : GL (Fin 2) ℝ) 1 0 : ℝ) : ℂ) = ((γ 1 0 : ℤ) : ℂ) := rfl
  have hD2eq : D2 γ τ = (2 * π * I) * ((γ 1 0 : ℤ) : ℂ)
      * (UpperHalfPlane.denom γ τ)⁻¹ := by
    unfold D2; field_simp
  rw [hD2eq, hcast]
  have hzk2 : (UpperHalfPlane.denom γ τ) ^ (-(k + 2) : ℤ)
      = (UpperHalfPlane.denom γ τ) ^ (-k : ℤ) * ((UpperHalfPlane.denom γ τ)⁻¹) ^ 2 := by
    rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hdz]; ring_nf
  have hzk1 : (UpperHalfPlane.denom γ τ) ^ (-k - 1 : ℤ)
      = (UpperHalfPlane.denom γ τ) ^ (-k : ℤ) * (UpperHalfPlane.denom γ τ)⁻¹ := by
    rw [← zpow_neg_one, ← zpow_add₀ hdz]; ring_nf
  rw [hzk2, hzk1]
  field_simp
  ring

end DSlash

section Invariance

variable {f : ℍ → ℂ} (γ : SL(2, ℤ)) (k : ℤ)

private lemma twelve_inv_zeta_two_inv :
    (12 : ℂ)⁻¹ * (2 * riemannZeta 2)⁻¹ = -((2 * π * I)⁻¹) ^ 2 := by
  rw [riemannZeta_two]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp
  rw [Complex.I_sq]; ring

private theorem serreDerivative_SL_slash (hf : MDiff f) :
    (serreDerivative (k : ℂ) f) ∣[(k + 2 : ℤ)] γ = serreDerivative (k : ℂ) (f ∣[k] γ) := by
  have hfslash : MDiff (f ∣[k] γ) := by
    rw [SL_slash_eq_mul]
    exact (mdiff_smul_comp γ hf).mul
      (UpperHalfPlane.mdifferentiable_denom_zpow (γ : GL (Fin 2) ℝ) (-k))
  ext τ
  simp only [serreDerivative_eq]
  rw [show ((fun z ↦ D f z - (k : ℂ) * 12⁻¹ * E2 z * f z) : ℍ → ℂ)
      = D f - ((k : ℂ) * 12⁻¹) • (E2 * f) by ext z; simp; ring,
    sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    ModularForm.SL_smul_slash, show (k + 2 : ℤ) = (2 : ℤ) + k by ring,
    ModularForm.mul_slash_SL2, E2_slash_action]
  have hnum := twelve_inv_zeta_two_inv
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, Pi.mul_apply, Pi.sub_apply,
    smul_eq_mul, one_div]
  rw [D_SL_slash γ k hf τ]
  ring_nf
  linear_combination ((k : ℂ) * D2 γ τ * (f ∣[k] γ) τ) * hnum

end Invariance

section Bounded

private theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]

  set r₀ : ℝ := Real.exp (-Real.pi) with hr₀
  have hr₀0 : 0 ≤ r₀ := (Real.exp_pos _).le
  have hr₀1 : ‖r₀‖ < 1 := by
    rw [Real.norm_of_nonneg hr₀0, hr₀, Real.exp_lt_one_iff, neg_lt_zero]
    exact Real.pi_pos
  have hg : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ) :=
    (summable_pow_mul_geometric_of_norm_lt_one 2 hr₀1).comp_injective PNat.coe_injective
  refine ⟨1 + 24 * ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ), 1 / 2, fun z hz => ?_⟩

  have hq : ‖cexp (2 * Real.pi * I * (z : ℂ))‖ ≤ r₀ := by
    have h := Function.Periodic.norm_qParam_le_of_one_half_le_im (ξ := (z : ℂ)) (by simpa using hz)
    simpa [Function.Periodic.qParam] using h

  have hle : ∀ n : ℕ+, ‖(σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ ≤
      ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ) := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    gcongr
    · exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
  have hf : Summable fun n : ℕ+ => ‖(σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle hg
  rw [E2_eq_tsum_cexp z]
  calc ‖1 - 24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖
      ≤ ‖(1 : ℂ)‖ + ‖24 * ∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ :=
        norm_sub_le _ _
    _ = 1 + 24 * ‖∑' n : ℕ+, (σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ := by
        rw [norm_one, norm_mul, Complex.norm_ofNat]
    _ ≤ 1 + 24 * ∑' n : ℕ+, ‖(σ 1 n : ℂ) * cexp (2 * Real.pi * I * (z : ℂ)) ^ (n : ℕ)‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm hf
    _ ≤ 1 + 24 * ∑' n : ℕ+, ((n : ℕ) : ℝ) ^ 2 * r₀ ^ (n : ℕ) := by
        have h := hf.tsum_le_tsum hle hg
        linarith

private lemma hasDerivAt_qParam (p : ℝ) (z : ℂ) :
    HasDerivAt (Periodic.qParam p) ((2 * π * I / p) * Periodic.qParam p z) z := by
  have h1 : HasDerivAt (fun w ↦ 2 * π * I * w / p) (2 * π * I / p) z := by
    have := ((hasDerivAt_id z).const_mul (2 * π * I)).div_const (p : ℂ)
    simpa using this
  have h2 := h1.cexp
  refine h2.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · exact Filter.Eventually.of_forall fun w ↦ by simp only [Periodic.qParam]
  · simp only [Periodic.qParam]; ring

private theorem isBoundedAtImInfty_D {h : ℍ → ℂ} {p : ℝ} (hp : 0 < p)
    (hper : Periodic (h ∘ ofComplex) p) (hhol : MDiff h) (hbdd : IsBoundedAtImInfty h) :
    IsBoundedAtImInfty (D h) := by
  set F := cuspFunction p h with hF_def
  have hFdiff := differentiableOn_cuspFunction_ball hp hper hhol hbdd
  have hF'diff : DifferentiableOn ℂ (deriv F) (Metric.ball 0 1) :=
    (hFdiff.analyticOnNhd Metric.isOpen_ball).deriv.differentiableOn
  have hsub : Metric.closedBall (0 : ℂ) 2⁻¹ ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball (by norm_num)
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 2⁻¹) := isCompact_closedBall 0 _
  have hF'cont : ContinuousOn (fun q ↦ ‖deriv F q‖) (Metric.closedBall 0 2⁻¹) :=
    ((hF'diff.mono hsub).continuousOn).norm
  obtain ⟨C, hC⟩ : ∃ C, ∀ q ∈ Metric.closedBall (0 : ℂ) 2⁻¹, ‖deriv F q‖ ≤ C := by
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hF'cont
    exact ⟨C, fun q hq ↦ hC ⟨q, hq, rfl⟩⟩
  rw [isBoundedAtImInfty_iff]
  refine ⟨C / p, p * Real.log 2 / (2 * π), fun τ hτ ↦ ?_⟩
  have h2π : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have hqτ : ‖Periodic.qParam p (τ : ℂ)‖ ≤ 2⁻¹ := by
    rw [Periodic.norm_qParam]
    have : Real.log 2 ≤ 2 * π * τ.im / p := by
      have hτ' : p * Real.log 2 ≤ τ.im * (2 * π) := by
        have := (div_le_iff₀ h2π).mp hτ; linarith
      rw [le_div_iff₀ hp]; linarith
    calc Real.exp (-2 * π * τ.im / p) = Real.exp (-(2 * π * τ.im / p)) := by ring_nf
      _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (neg_le_neg this)
      _ = 2⁻¹ := by rw [Real.exp_neg, Real.exp_log two_pos]
  have hqmem : Periodic.qParam p (τ : ℂ) ∈ Metric.closedBall (0 : ℂ) 2⁻¹ := by
    rwa [Metric.mem_closedBall, dist_zero_right]

  have hcomp : (h ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)] F ∘ (Periodic.qParam p) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with z hz
    show h (ofComplex z) = F (Periodic.qParam p z)
    rw [ofComplex_apply_of_im_pos hz]
    exact (eq_cuspFunction (⟨z, hz⟩ : ℍ) hp.ne' hper).symm

  have hqd := hasDerivAt_qParam p (τ : ℂ)
  have hFd : DifferentiableAt ℂ F (Periodic.qParam p (τ : ℂ)) :=
    (hFdiff (Periodic.qParam p τ)
      (mem_ball_zero_iff.mpr (lt_of_le_of_lt hqτ (by norm_num)))).differentiableAt
      (Metric.isOpen_ball.mem_nhds
        (mem_ball_zero_iff.mpr (lt_of_le_of_lt hqτ (by norm_num))))
  have hderiv : deriv (h ∘ ofComplex) (τ : ℂ)
      = deriv F (Periodic.qParam p τ) * ((2 * π * I / p) * Periodic.qParam p τ) := by
    rw [hcomp.deriv_eq, ← hqd.deriv]
    exact deriv_comp (τ : ℂ) hFd hqd.differentiableAt

  have h2πi : (2 * π * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  calc ‖D h τ‖ = ‖(2 * π * I : ℂ)⁻¹ * deriv (h ∘ ofComplex) (τ : ℂ)‖ := rfl
    _ = ‖(2 * π * I : ℂ)⁻¹‖ * ‖deriv F (Periodic.qParam p τ)‖
          * (‖(2 * π * I : ℂ) / (p : ℂ)‖ * ‖Periodic.qParam p (τ : ℂ)‖) := by
        rw [hderiv, norm_mul, norm_mul, norm_mul]; ring
    _ = (1 / p) * ‖Periodic.qParam p (τ : ℂ)‖ * ‖deriv F (Periodic.qParam p τ)‖ := by
        have hn := norm_ne_zero_iff.mpr h2πi
        have hnp : ‖(p : ℂ)‖ = p := by
          rw [Complex.norm_real]; exact abs_of_pos hp
        rw [norm_inv, norm_div, hnp]; field_simp
    _ ≤ (1 / p) * 1 * C := by
        have h1p : (0:ℝ) ≤ 1 / p := div_nonneg zero_le_one hp.le
        have hq1 : ‖Periodic.qParam p (τ : ℂ)‖ ≤ 1 := le_trans hqτ (by norm_num)
        have hF' := hC _ hqmem
        have hq0 : (0:ℝ) ≤ ‖Periodic.qParam p (τ : ℂ)‖ := norm_nonneg _
        nlinarith [mul_le_mul hq1 hF' (norm_nonneg _) (by linarith)]
    _ = C / p := by ring

private theorem isBoundedAtImInfty_serreDerivative {h : ℍ → ℂ} {p : ℝ} (hp : 0 < p) (k : ℤ)
    (hper : Periodic (h ∘ ofComplex) p) (hhol : MDiff h) (hbdd : IsBoundedAtImInfty h) :
    IsBoundedAtImInfty (serreDerivative (k : ℂ) h) := by
  have hDh := isBoundedAtImInfty_D hp hper hhol hbdd
  have hE2h : IsBoundedAtImInfty (((k : ℂ) * 12⁻¹ : ℂ) • (E2 * h)) :=
    (isBoundedAtImInfty_E2.mul hbdd).const_smul_left _
  have heq : serreDerivative (k : ℂ) h = D h - ((k : ℂ) * 12⁻¹ : ℂ) • (E2 * h) := by
    ext τ; simp only [serreDerivative_eq, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
      smul_eq_mul]; ring
  rw [heq, sub_eq_add_neg]
  exact hDh.add hE2h.neg_left

end Bounded

section Assembly

open CongruenceSubgroup

variable (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (Gamma0 N') k)

private noncomputable def serreDerivativeSIF : SlashInvariantForm (Gamma0 N') (k + 2) where
  toFun := serreDerivative (k : ℂ) ⇑f
  slash_action_eq' := by
    intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := Subgroup.mem_map.mp hγ
    calc (serreDerivative (k : ℂ) ⇑f) ∣[(k + 2 : ℤ)] (mapGL ℝ δ : GL (Fin 2) ℝ)
        = (serreDerivative (k : ℂ) ⇑f) ∣[(k + 2 : ℤ)] δ := rfl
      _ = serreDerivative (k : ℂ) (⇑f ∣[k] δ) :=
          serreDerivative_SL_slash (f := ⇑f) δ k (ModularFormClass.holo f)
      _ = serreDerivative (k : ℂ) ⇑f := by
          congr 1
          exact f.slash_action_eq' _ (Subgroup.mem_map_of_mem _ hδ)

private theorem S_M3a_serreDerivative (N' : ℕ) [NeZero N'] (k : ℤ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N') (k + 2),
      ⇑g = Derivative.serreDerivative (k : ℂ) ⇑f := by
  refine ⟨⟨serreDerivativeSIF N' k f, ?_, ?_⟩, rfl⟩
  ·
    exact serreDerivative_mdifferentiable (k : ℂ) (ModularFormClass.holo f)
  ·
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ :=
      (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc
    rw [OnePoint.isBoundedAt_iff_exists_SL2Z hcSL]
    obtain ⟨γ, hγc⟩ := isCusp_SL2Z_iff'.mp hcSL
    refine ⟨γ, hγc.symm, ?_⟩
    show IsBoundedAtImInfty ((serreDerivative (k : ℂ) ⇑f) ∣[(k + 2 : ℤ)] γ)
    rw [serreDerivative_SL_slash (f := ⇑f) γ k (ModularFormClass.holo f)]

    have hfγbdd : IsBoundedAtImInfty (⇑f ∣[k] γ) := by
      have hcγ : IsCusp ((mapGL ℝ γ : GL (Fin 2) ℝ) • (OnePoint.infty : OnePoint ℝ))
          ((Gamma0 N' : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; exact hγc ▸ hcSL
      have := (ModularFormClass.bdd_at_cusps f hcγ)
      rw [OnePoint.IsBoundedAt.smul_iff, OnePoint.isBoundedAt_infty_iff] at this
      exact this
    have hfγhol : MDiff (⇑f ∣[k] γ) := (ModularFormClass.holo f).slash k γ

    have hΓle : ∀ δ ∈ CongruenceSubgroup.Gamma N', δ ∈ Gamma0 N' := fun δ hδ ↦
      Gamma0_mem.mpr (Gamma_mem.mp hδ).2.2.1
    have hTmat : ((ModularGroup.T ^ (N' : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![1, (N' : ℤ); 0, 1] := ModularGroup.coe_T_zpow (N' : ℤ)
    have h00 : ((ModularGroup.T ^ (N':ℤ) : SL(2,ℤ)) 0 0 : ℤ) = 1 := by rw [hTmat]; rfl
    have h01 : ((ModularGroup.T ^ (N':ℤ) : SL(2,ℤ)) 0 1 : ℤ) = (N':ℤ) := by rw [hTmat]; rfl
    have h10 : ((ModularGroup.T ^ (N':ℤ) : SL(2,ℤ)) 1 0 : ℤ) = 0 := by rw [hTmat]; rfl
    have h11 : ((ModularGroup.T ^ (N':ℤ) : SL(2,ℤ)) 1 1 : ℤ) = 1 := by rw [hTmat]; rfl
    have hTN : (ModularGroup.T ^ (N' : ℤ) : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma N' :=
      Gamma_mem.mpr ⟨by rw [h00]; norm_num,
        by rw [h01]; exact_mod_cast ZMod.natCast_self N',
        by rw [h10]; norm_num, by rw [h11]; norm_num⟩
    have hconj : γ * ModularGroup.T ^ (N' : ℤ) * γ⁻¹ ∈ Gamma0 N' :=
      hΓle _ ((CongruenceSubgroup.Gamma_normal N').conj_mem _ hTN γ)

    set toGLR : SL(2, ℤ) →* GL (Fin 2) ℝ :=
      (Matrix.SpecialLinearGroup.toGL).comp
        (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) with htoGLR
    have hcoe : ∀ δ : SL(2, ℤ), (δ : GL (Fin 2) ℝ) = toGLR δ := fun _ ↦ rfl
    have hslashT : (⇑f ∣[k] γ) ∣[k] (ModularGroup.T ^ (N' : ℤ) : SL(2, ℤ)) = (⇑f ∣[k] γ) := by
      change (⇑f ∣[k] toGLR γ) ∣[k] toGLR (ModularGroup.T ^ (N' : ℤ)) = ⇑f ∣[k] toGLR γ
      rw [← SlashAction.slash_mul, ← map_mul,
        show γ * ModularGroup.T ^ (N' : ℤ)
          = (γ * ModularGroup.T ^ (N' : ℤ) * γ⁻¹) * γ from by group,
        map_mul, SlashAction.slash_mul]
      congr 1
      have hmem : toGLR (γ * ModularGroup.T ^ (N' : ℤ) * γ⁻¹) ∈
          Subgroup.map (mapGL ℝ) (Gamma0 N') :=
        ⟨_, hconj, rfl⟩
      exact SlashInvariantFormClass.slash_action_eq f _ hmem
    have hfγper : Periodic ((⇑f ∣[k] γ) ∘ ofComplex) (N' : ℝ) := by
      intro z
      simp only [comp_apply]
      rcases le_or_gt z.im 0 with him | him
      · rw [ofComplex_apply_of_im_nonpos (by simpa using him),
          ofComplex_apply_of_im_nonpos him]
      · have him' : 0 < (z + (N' : ℝ)).im := by simpa using him
        rw [ofComplex_apply_of_im_pos him', ofComplex_apply_of_im_pos him]
        have heq : (⟨z + (N' : ℝ), him'⟩ : ℍ)
            = (ModularGroup.T ^ (N' : ℤ) : SL(2, ℤ)) • (⟨z, him⟩ : ℍ) := by
          rw [modular_T_zpow_smul]
          refine UpperHalfPlane.ext_iff.mpr ?_
          rw [UpperHalfPlane.coe_vadd]
          push_cast; ring
        rw [heq]
        have hpt := congrFun hslashT (⟨z, him⟩ : ℍ)
        rw [ModularForm.SL_slash_apply] at hpt
        have hden : UpperHalfPlane.denom (ModularGroup.T ^ (N' : ℤ) : SL(2, ℤ))
            (⟨z, him⟩ : ℍ) = 1 := by

          show ((((ModularGroup.T ^ (N':ℤ) : SL(2,ℤ)) 1 0 : ℤ) : ℂ)) * (z : ℂ)
              + ((((ModularGroup.T ^ (N':ℤ) : SL(2,ℤ)) 1 1 : ℤ) : ℂ)) = 1
          rw [h10, h11]; simp
        rw [hden, one_zpow, mul_one] at hpt
        exact hpt
    exact isBoundedAtImInfty_serreDerivative (Nat.cast_pos.mpr (NeZero.pos N')) k
      hfγper hfγhol hfγbdd

end Assembly

end E34S

theorem solution (N' : ℕ) [NeZero N'] (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma0 N') k) :
    ∃ g : ModularForm (CongruenceSubgroup.Gamma0 N') (k + 2),
      ⇑g = Derivative.serreDerivative (k : ℂ) ⇑f :=
  E34S.S_M3a_serreDerivative N' k f

end S_ModularForm_exists_gamma0_coe_eq_serreDerivative
end P2MW
export P2MW.S_ModularForm_exists_gamma0_coe_eq_serreDerivative (solution)
