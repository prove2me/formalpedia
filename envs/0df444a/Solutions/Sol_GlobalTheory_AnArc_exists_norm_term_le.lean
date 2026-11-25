-- Prove2me | solution 1 for GlobalTheory.AnArc.exists_norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:36.503128+00:00
-- url     : https://prove2.me/submissions/ce77a4ea-c9e9-4a36-b558-e0e93d050984

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SummableExpNegSumAbs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HasSumLocallyUniformlyOnTerm
import Theorems.Thm_GlobalTheory_AnArc_norm_e
import Theorems.Thm_GlobalTheory_AnArc_size_nonneg
import Theorems.Thm_GlobalTheory_AnArc_exists_norm_le_mul_size
import Theorems.Thm_GlobalTheory_AnArc_norm_apply_le_size
import Theorems.Thm_GlobalTheory_AnArc_exists_norm_H_le
import Theorems.Thm_GlobalTheory_AnArc_H_add_self_re
import Theorems.Thm_GlobalTheory_AnArc_norm_psi
import Theorems.Thm_GlobalTheory_AnArc_exists_norm_theta_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT
namespace GlobalTheory.AnArc
theorem _root_.solution (hj : j ≠ 0) (h : th ∈ A.Theta j α) {T₁ : ℝ} (h₁ : T₀ ≤ T₁) (R : ℝ) :
    ∃ K D : ℝ, ∀ μ (w : ℂ) (v : A.V), T₁ ≤ w.im → |w.im| ≤ R → ‖v‖ ≤ R →
      ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ ≤
        K * Real.exp (-(Real.pi * (T₁ - T₀) * A.be μ μ) + D * A.size μ) := by
  obtain ⟨M, hM, hth⟩ := A.exists_norm_theta_le h
  obtain ⟨CH, hCH, hH⟩ := A.exists_norm_H_le
  obtain ⟨Cc, hCc, hc⟩ := A.exists_norm_le_mul_size A.ct
  obtain ⟨Cb, hCb, hb⟩ := A.exists_norm_le_mul_size (A.be α).toAddMonoidHom
  refine ⟨M * Real.exp (Real.pi * (2 * (R * A.size α) + j * (CH * R * R) / 2 + CH * ‖A.ct α‖ * R)),
    Real.pi * (2 * ‖A.T α‖ + 2 * (j * R) + j * (CH * R * Cc) + CH * ‖A.ct α‖ * Cc + 2 * (R * Cb)),
    fun μ w v hw hwR hv => ?_⟩
  obtain ⟨l, z⟩ := v
  have hl : ‖l‖ ≤ R := (norm_fst_le (l, z)).trans hv
  have hz : ‖z‖ ≤ R := (norm_snd_le (l, z)).trans hv
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hs := A.size_nonneg μ
  have hsα := A.size_nonneg α
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  have hB : (0 : ℝ) ≤ A.be μ μ := by exact_mod_cast A.be_self_nonneg μ
  have im_le : ∀ (f : A.X →+ ℂ) (x : A.X), -(f x).im ≤ ‖f‖ * A.size x := fun f x =>
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (A.norm_apply_le_size f x))
  have re_le : ∀ a b, (A.H a b).re ≤ CH * ‖a‖ * ‖b‖ := fun a b => (Complex.re_le_norm _).trans (hH a b)
  have e1 : -(A.T μ α).im ≤ ‖A.T α‖ * A.size μ := by rw [A.T_symm]; exact im_le _ _
  have e2 : -(l α).im ≤ R * A.size α := (im_le l α).trans (by gcongr)
  have e3 : j * -(l μ).im ≤ j * (R * A.size μ) :=
    mul_le_mul_of_nonneg_left ((im_le l μ).trans (by gcongr)) hj0
  have e4 : j * (A.H z z).re ≤ j * (CH * R * R) :=
    mul_le_mul_of_nonneg_left ((re_le z z).trans (by gcongr)) hj0
  have e5 : j * (A.H z (A.ct μ)).re ≤ j * (CH * R * (Cc * A.size μ)) :=
    mul_le_mul_of_nonneg_left ((re_le _ _).trans (by gcongr; exact hc μ)) hj0
  have e6 : (A.H (A.ct α) z).re ≤ CH * ‖A.ct α‖ * R := (re_le _ _).trans (by gcongr)
  have e7 : (A.H (A.ct α) (A.ct μ)).re ≤ CH * ‖A.ct α‖ * (Cc * A.size μ) :=
    (re_le _ _).trans (by gcongr; exact hc μ)
  have e8 : -(w.im * A.be μ α) ≤ R * (Cb * A.size μ) := by
    refine (neg_le_abs _).trans ?_
    rw [abs_mul, A.be_symm]
    have := hb μ
    rw [Int.norm_eq_abs] at this
    exact mul_le_mul hwR this (abs_nonneg _) hR
  have e9 : j * ((A.H (A.ct μ) (A.ct μ)).re / 2 - (A.T μ μ).im - w.im * A.be μ μ) ≤ -((T₁ - T₀) * A.be μ μ) := by
    have a1 : (A.H (A.ct μ) (A.ct μ)).re / 2 - (A.T μ μ).im - w.im * A.be μ μ ≤ -((T₁ - T₀) * A.be μ μ) := by
      have := hT μ
      have := mul_le_mul_of_nonneg_right hw hB
      linarith
    have a2 : 0 ≤ (T₁ - T₀) * A.be μ μ := mul_nonneg (sub_nonneg.2 h₁) hB
    nlinarith [mul_le_mul_of_nonneg_left a1 hj0]
  have hex : (A.exponent j α μ : ℝ) = j * A.be μ μ / 2 + A.be μ α := by
    have : (2 : ℝ) * A.exponent j α μ = j * A.be μ μ + 2 * A.be μ α := by exact_mod_cast A.two_mul_exponent j α μ
    linarith
  have i1 : (l (α + j • μ)).im = (l α).im + j * (l μ).im := by simp
  have i2 : (w * A.exponent j α μ).im = w.im * (j * A.be μ μ / 2 + A.be μ α) := by simp [hex]
  rw [term, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_psi, norm_e, norm_e, norm_e, i1, i2,
    ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, mul_right_comm, ← Real.exp_add]
  refine (mul_le_mul_of_nonneg_left (hth _) (Real.exp_pos _).le).trans ?_
  rw [mul_left_comm, ← Real.exp_add, mul_assoc M, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM
  rw [H_add_self_re, H_add_right, Complex.add_re]
  have key := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add e1 e1)
    (add_le_add e2 e2)) (add_le_add (add_le_add e3 e3) (div_le_div_of_nonneg_right e4 zero_le_two)))
    (add_le_add (add_le_add e5 e6) (add_le_add e7 (add_le_add e8 e8)))) e9) Real.pi_pos.le
  linarith
end GlobalTheory.AnArc
