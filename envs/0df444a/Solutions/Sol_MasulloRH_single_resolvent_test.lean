-- Prove2me | solution 1 for MasulloRH.single_resolvent_test
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:41:36.668187+00:00
-- url     : https://prove2.me/submissions/eaa70854-8b74-41d4-aa64-7fee74546f60

import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six

set_option autoImplicit false

open MasulloRH Set

private theorem ordinate_bound (ρ : ZetaZerosInTraceStrip (1/2)) : 6 < |ρ.val.im| :=
  lt_of_not_ge fun h => ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six
    ρ.prop.2.1 ρ.prop.2.2.1 h ρ.prop.1

private theorem multiplicity_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < analyticOrderNatAt riemannZeta ρ.val := by
  have h1 : ρ.val ≠ 1 := fun h => by
    have hr := congrArg Complex.re h
    simp only [Complex.one_re] at hr
    linarith [ρ.prop.2.2.1]
  have hA := analyticOn_riemannZeta
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))
  have hfin := hA.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1:ℂ)).isPreconnected
    (show (2:ℂ) ∈ ({1}:Set ℂ)ᶜ by norm_num) h1 (htwo ▸ ENat.zero_ne_top)
  apply Nat.pos_of_ne_zero
  unfold analyticOrderNatAt
  exact fun h => (ENat.toNat_eq_zero.mp h).elim
    ((hA _ h1).analyticOrderAt_ne_zero.mpr ρ.prop.1) hfin

private theorem resolvent_norm_bound (ρ : ZetaZerosInTraceStrip (1/2)) :
    ‖zeroResolventTerm (1/2) 3 ρ‖ ≤ zeroDecayWeight (1/2) ρ := by
  let z := ρ.val
  have hy : 6 < |z.im| := ordinate_bound ρ
  have ha : |z.im| ≤ ‖3-z‖ := by simpa using Complex.abs_im_le_norm (3-z)
  have hb : |z.im| ≤ ‖5/2-z‖ := by simpa using Complex.abs_im_le_norm (5/2-z)
  have ha0 : 0 < ‖3-z‖ := by linarith
  have hb0 : 0 < ‖5/2-z‖ := by linarith
  have hid : 1/(3-z) - 1/(5/2-z) = (-1/2)/((3-z)*(5/2-z)) := by
    rw [div_sub_div _ _ (norm_pos_iff.mp ha0) (norm_pos_iff.mp hb0)]
    congr 1
    ring
  change ‖(analyticOrderNatAt riemannZeta z : ℂ) * _‖ ≤ _
  rw [hid, norm_mul, Complex.norm_natCast, norm_div, norm_mul]
  change _ ≤ (analyticOrderNatAt riemannZeta z : ℝ)/(1+z.im^2)
  rw [div_eq_mul_one_div]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [show ‖(-1/2 : ℂ)‖ = (1/2 : ℝ) by norm_num [norm_div]]
  rw [← div_eq_mul_one_div, ← one_div (1 + z.im^2)]
  apply (div_le_div_iff₀ (mul_pos ha0 hb0) (by positivity)).mpr
  have hmul := mul_le_mul ha hb (abs_nonneg _) ha0.le
  have hy' : 1 ≤ z.im^2 := by nlinarith [sq_abs z.im, sq_nonneg (|z.im|-1)]
  nlinarith [sq_abs z.im]

private theorem kernel_pos {β γ : ℝ} (hβ : 0 < β) (hβ' : β < 1) (hγ : 6 < |γ|) :
    0 < (3-β)/((3-β)^2+γ^2) - (5/2-β)/((5/2-β)^2+γ^2) := by
  have hγ' : 36 < γ^2 := by nlinarith [sq_abs γ, sq_nonneg (|γ|-6)]
  have ha : 0 < (3-β)^2+γ^2 := by positivity
  have hb : 0 < (5/2-β)^2+γ^2 := by positivity
  rw [sub_pos, div_lt_div_iff₀ hb ha]
  nlinarith [mul_pos hβ (sub_pos.mpr hβ')]

private theorem term_re_pos (ρ : ZetaZerosInTraceStrip (1/2)) :
    0 < (zeroResolventTerm (1/2) 3 ρ).re := by
  rw [zeroResolventTerm, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  apply mul_pos (by exact_mod_cast multiplicity_pos ρ)
  simp only [one_div, Complex.sub_re, Complex.inv_re, Complex.normSq_apply, Complex.sub_im]
  convert kernel_pos ρ.prop.2.1 ρ.prop.2.2.1 (ordinate_bound ρ) using 1 <;> norm_num [pow_two, Complex.div_ofNat_re, Complex.div_ofNat_im]
  rfl

/-- Equality of the real parts at one ordinary real argument detects every omitted zero. -/
theorem solution (α : ℝ) :
    (regularizedTraceRHS (1/2) 3).re ≤ (regularizedTraceRHS α 3).re ↔
      ∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re - 1/2| < α := by
  let Z := ZetaZerosInTraceStrip (1/2)
  let inside : Set Z := {r | |r.val.re - 1/2| < α}
  let f := zeroResolventTerm (1/2) 3
  have hf : Summable f := (weighted_zero_summability (1/2) (by norm_num)).of_norm_bounded resolvent_norm_bound
  let e : ZetaZerosInTraceStrip α ≃ inside :=
    { toFun := fun r => ⟨⟨r.val, r.prop.1, r.prop.2.1, r.prop.2.2.1, abs_lt.mpr
        ⟨by linarith [r.prop.2.1], by linarith [r.prop.2.2.1]⟩⟩, r.prop.2.2.2⟩
      invFun := fun r => ⟨r.val.val, r.val.prop.1, r.val.prop.2.1, r.val.prop.2.2.1, r.prop⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hin := e.tsum_eq (fun r => f r.val)
  have hsplit := hf.tsum_subtype_add_tsum_subtype_compl inside
  rw [← hin] at hsplit
  change regularizedSpectral α 3 + _ = regularizedSpectral (1/2) 3 at hsplit
  have hout : Summable (fun r : (insideᶜ : Set Z) => f r.val) := hf.subtype (· ∈ insideᶜ)
  have hh := congrArg Complex.re hsplit
  rw [Complex.add_re, Complex.re_tsum hout] at hh
  simp only [regularizedTraceRHS, Complex.add_re, add_le_add_iff_left]
  constructor
  · intro h r
    by_contra hr
    have hpos := (Complex.hasSum_re hout.hasSum).summable.tsum_pos
      (fun i => (term_re_pos i.val).le) (⟨r,hr⟩ : (insideᶜ : Set Z)) (term_re_pos r)
    linarith
  · intro h
    have : IsEmpty (insideᶜ : Set Z) := ⟨fun r => r.prop (h r.val)⟩
    rw [tsum_empty, add_zero] at hh
    exact hh.ge
