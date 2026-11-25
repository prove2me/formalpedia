-- Prove2me | solution 1 for GlobalTheory.TensorLat.l2_comp_flat_symm_eq_l2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:45:05.493827+00:00
-- url     : https://prove2.me/submissions/0e3ab5af-1adc-405e-898c-682954f034c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Theorems.Thm_GlobalTheory_TensorLat_setAverage_comp_equiv
import Theorems.Thm_GlobalTheory_TensorLat_pointwiseNorm_comp_flatten_symm_eq
import Theorems.Thm_GlobalTheory_TensorLat_HC_add_left
import Theorems.Thm_GlobalTheory_TensorLat_HC_add_right
import Theorems.Thm_GlobalTheory_TensorLat_HC_conj
import Theorems.Thm_GlobalTheory_TensorLat_flat_eq_eT
import Theorems.Thm_GlobalTheory_TensorLat_flat_symm_eq_eT_symm
import Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TiledBoundaries_fd_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply



set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
namespace GlobalTheory.TensorLat
theorem _root_.solution (X : PT E) (Y : GT (Fin n × Idx X.dim))
    (hY : ∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) (q : ℕ) {F : (Fin n → Vsp X.dim) → ℂ}
    (hF : F ∈ X.Sec q n) : Y.l2 q (F ∘ flat.symm) = X.l2 q F := by
  have hper : ∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → ∀ v,
      X.ptN2 q F (v + γ) = X.ptN2 q F v := by
    intro γ hγ v
    have hFv := hF.2 γ hγ v
    have heps : ‖(∏ k, (X.eps (γ k) : ℂ))‖ = 1 := by
      rw [norm_prod]
      refine Finset.prod_eq_one fun k _ => ?_
      rcases X.eps_pm _ (hγ k) with h | h <;> simp [h]
    have hre : (HC (v + γ) (v + γ)).re = (HC v v).re + 2 * (HC v γ).re + (HC γ γ).re := by
      rw [HC_add_left, HC_add_right, HC_add_right, HC_conj v γ]
      simp only [Complex.add_re, Complex.conj_re]
      ring
    have hsq : ∀ a b c : ℝ, (Real.exp a * c) ^ 2 * Real.exp b = c ^ 2 * Real.exp (2 * a + b) := by
      intro a b c
      rw [show 2 * a + b = a + a + b by ring, Real.exp_add, Real.exp_add]
      ring
    unfold PT.ptN2
    rw [hFv, norm_mul, norm_mul, norm_pow, heps, one_pow, one_mul, Complex.norm_exp, hsq, hre]
    congr 2
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
      Complex.natCast_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, mul_zero,
      zero_mul, sub_zero, add_zero]
    ring
  have hlat : lat Y.b = lat (TiledBoundaries.bT X n) := by
    ext w
    have h := hY (flat.symm w)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    rw [h, TiledBoundaries.mem_latT, ← flat_symm_eq_eT_symm]
  have hg : ∀ v, Y.ptN2 q (F ∘ flat.symm) (flat v) = X.ptN2 q F v :=
    pointwiseNorm_comp_flatten_symm_eq X Y q F
  have hgc : Continuous (Y.ptN2 q (F ∘ flat.symm)) := by
    have hFc : Continuous F := hF.1.continuous
    unfold GT.ptN2
    exact ((hFc.comp flat.symm.continuous).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hgper : ∀ γ ∈ lat Y.b, ∀ w,
      Y.ptN2 q (F ∘ flat.symm) (w + γ) = Y.ptN2 q (F ∘ flat.symm) w := by
    intro γ hγ w
    have hγ' : ∀ k, flat.symm γ k ∈ X.L := by
      rw [← hY, ContinuousLinearEquiv.apply_symm_apply]
      exact hγ
    have h := hper (flat.symm γ) hγ' (flat.symm w)
    rw [← hg, ← hg, map_add, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.apply_symm_apply] at h
    exact h
  have h1 : Y.l2 q (F ∘ flat.symm) =
      ⨍ w in ZSpan.fundamentalDomain (TiledBoundaries.bT X n), Y.ptN2 q (F ∘ flat.symm) w := by
    have h := average_fundamentalDomain_eq_real volume Y.b (TiledBoundaries.bT X n)
      (Y.ptN2 q (F ∘ flat.symm)) hgc hgper hlat.symm.le 0
    simp only [add_zero] at h
    rw [GT.l2]
    exact h.symm
  let e : (Fin n → Vsp X.dim) ≃L[ℝ] EuclideanSpace ℂ (Fin n × Idx X.dim) :=
    { toLinearEquiv := (flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℝ
      continuous_toFun := (flat (n := n) (ι := Idx X.dim)).continuous
      continuous_invFun := (flat (n := n) (ι := Idx X.dim)).symm.continuous }
  have hpre : e ⁻¹' ZSpan.fundamentalDomain (TiledBoundaries.bT X n) = X.fd n := by
    rw [TiledBoundaries.fd_eq]
    unfold TiledBoundaries.bT
    rw [ZSpan.fundamentalDomain_reindex, ← ZSpan.map_fundamentalDomain]
    ext v
    rw [Set.mem_preimage, show e v = ((TiledBoundaries.eT X n).restrictScalars ℝ) v from flat_eq_eT X v]
    exact (LinearEquiv.injective _).mem_set_image
  rw [h1, setAverage_comp_equiv (volume : Measure (Fin n → Vsp X.dim)) volume e, hpre, PT.l2]
  congr 1
  funext v
  exact hg v
end GlobalTheory.TensorLat
