-- Prove2me | solution 1 for GlobalTheory.ext_all_inputs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:29.720497+00:00
-- url     : https://prove2.me/submissions/df33fe72-8a2a-4ddd-8a37-00f7c7d39809

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_GaussTailOfCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EnormPowLeInvMeasureMulLintegralBall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsOrthonormalOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NearestPlaneRounding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExtAllInputs
import Theorems.Thm_GlobalTheory_Hadamard_norm_det_le_prod_col
import Theorems.Thm_GlobalTheory_exists_two_rpow_le_norm_minor
import Theorems.Thm_GlobalTheory_gaussTail_of_card_le
import Theorems.Thm_GlobalTheory_nearestPlane_rounding
import Theorems.Thm_GlobalTheory_packingCount
import Theorems.Thm_GlobalTheory_volume_ball_of_finrank_eq_two_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory
private theorem ext_ballVolume : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.BallVolume := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.BallVolume
  intro D rr hr
  exact _root_.GlobalTheory.volume_ball_of_finrank_eq_two_mul (by simp) 0 hr
private theorem ext_gHadamard : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.GHadamard := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.GHadamard
  intro n M
  simpa [Real.norm_eq_abs, sq_abs] using _root_.GlobalTheory.Hadamard.norm_det_le_prod_col M
private theorem ext_cauchyBinetMax' : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.CauchyBinetMax := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.CauchyBinetMax
  intro i N r M hM hr
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.exists_two_rpow_le_norm_minor M hM (r := r) (by simpa using hr)
  refine ⟨_root_.GlobalTheory.subsetEnum S, ?_, hS⟩
  unfold _root_.GlobalTheory.subsetEnum
  exact (Finset.orderEmbOfFin _ _).strictMono
private theorem ext_detPerturbation : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbation := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbation
  intro 𝕜 _ i κ _ w σ₀ ε Δmax hΔ
  classical
  set f := (Matrix.detRowAlternating : (Fin i → 𝕜) [⋀^Fin i]→ₗ[𝕜] 𝕜).toMultilinearMap with hf
  have hD : ∀ cols : Fin i → Fin i → 𝕜, (Matrix.of fun a j => cols j a).det = f cols := by
    intro cols
    rw [show (Matrix.of fun a j => cols j a) = (Matrix.of cols).transpose from rfl, Matrix.det_transpose]
    rfl
  have hΔ0 : 0 ≤ Δmax := (norm_nonneg _).trans (hΔ σ₀)
  set coef : Fin i → Option κ → 𝕜 := fun j o => Option.elim o 1 (ε j) with hcoef
  set pick : Fin i → Option κ → κ := fun j o => Option.elim o (σ₀ j) id with hpick
  have hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, coef j o • w (pick j o) := by
    funext j
    rw [Fintype.sum_option]
    simp [hcoef, hpick]
  have hexp : f (fun j => w (σ₀ j) + ∑ k, ε j k • w k)
      = ∑ r : Fin i → Option κ, (∏ j, coef j (r j)) • f (fun j => w (pick j (r j))) := by
    rw [hcol, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    exact f.map_smul_univ (fun j => coef j (r j)) (fun j => w (pick j (r j)))
  set r0 : Fin i → Option κ := fun _ => none with hr0
  have hterm0 : (∏ j, coef j (r0 j)) • f (fun j => w (pick j (r0 j))) = f (fun j => w (σ₀ j)) := by
    simp [hr0, hcoef, hpick]
  rw [hD, hD, hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hterm0, add_sub_cancel_left]
  have hbound : ∀ r : Fin i → Option κ, ‖(∏ j, coef j (r j)) • f (fun j => w (pick j (r j)))‖
      ≤ (∏ j, ‖coef j (r j)‖) * Δmax := by
    intro r
    rw [norm_smul, norm_prod]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hD]
    exact hΔ (fun j => pick j (r j))
  have hsum : ∑ r : Fin i → Option κ, ∏ j, ‖coef j (r j)‖ = ∏ j, (1 + ∑ k, ‖ε j k‖) := by
    have hps : ∏ j, ∑ o, ‖coef j o‖ = ∑ r : Fin i → Option κ, ∏ j, ‖coef j (r j)‖ := by
      rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rw [← hps]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.sum_option]
    simp [hcoef]
  have hone : ∏ j, ‖coef j (r0 j)‖ = 1 := by simp [hr0, hcoef]
  calc ‖∑ r ∈ Finset.univ.erase r0, (∏ j, coef j (r j)) • f (fun j => w (pick j (r j)))‖
      ≤ ∑ r ∈ Finset.univ.erase r0, (∏ j, ‖coef j (r j)‖) * Δmax :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hbound r)
    _ = (∏ j, (1 + ∑ k, ‖ε j k‖) - 1) * Δmax := by
        rw [← Finset.sum_mul, ← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hone]
        ring
private theorem ext_detPerturbNumeric : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbNumeric := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetPerturbNumeric
  intro ρ hρ
  have hρ1 : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hle : (ρ : ℝ) ^ (-3 / 2 : ℝ) ≤ (ρ : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hρ1 (by norm_num)
  have hmul : (ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10) ≤ 1 / 10 := by
    rw [Real.rpow_neg_one] at hle
    have : (ρ : ℝ) * (ρ : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    nlinarith
  have h1 : (1 + (ρ : ℝ) ^ (-3 / 2 : ℝ) / 10) ^ ρ
      ≤ Real.exp ((ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by linarith [Real.add_one_le_exp ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)]) ρ
  have h2 : Real.exp ((ρ : ℝ) * ((ρ : ℝ) ^ (-3 / 2 : ℝ) / 10)) ≤ Real.exp (1 / 10) :=
    Real.exp_le_exp.2 hmul
  have h3 : Real.exp (1 / 10) ≤ 3 / 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := 1 / 10) (by norm_num [abs_of_pos])
    rw [abs_le] at this
    nlinarith [this.2]
  linarith
private theorem two_pow_add_pow_sub_two_pow_mul_le (c : ℕ) (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ i : ℕ, ((2 : ℝ) ^ c + ε) ^ i - 2 ^ (c * i) ≤ i * ε * (2 ^ c + 1) ^ i
  | 0 => by simp
  | i + 1 => by
    have ih := two_pow_add_pow_sub_two_pow_mul_le c ε h0 h1 i
    have hb : (0 : ℝ) ≤ 2 ^ c := by positivity
    have hB1 : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
    have hbB : (2 : ℝ) ^ (c * i) ≤ (2 ^ c + 1) ^ (i + 1) := by
      rw [pow_mul]
      calc ((2 : ℝ) ^ c) ^ i ≤ (2 ^ c + 1) ^ i := pow_le_pow_left₀ hb (by linarith) i
        _ ≤ (2 ^ c + 1) ^ (i + 1) := pow_le_pow_right₀ hB1 (Nat.le_succ i)
    have ha : 0 ≤ (2 : ℝ) ^ c + ε := by linarith
    have hpos : 0 ≤ (i : ℝ) * ε * (2 ^ c + 1) ^ i := by positivity
    have e : ((2 : ℝ) ^ c + ε) ^ (i + 1) - 2 ^ (c * (i + 1))
        = (2 ^ c + ε) * ((2 ^ c + ε) ^ i - 2 ^ (c * i)) + ε * 2 ^ (c * i) := by
      rw [mul_add_one, pow_add, pow_succ]
      ring
    rw [e]
    have k1 := mul_le_mul_of_nonneg_left ih ha
    have k2 := mul_le_mul_of_nonneg_right (show (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1 by linarith) hpos
    have k3 := mul_le_mul_of_nonneg_left hbB h0
    have k4 : ((i + 1 : ℕ) : ℝ) * ε * (2 ^ c + 1) ^ (i + 1)
        = (2 ^ c + 1) * (i * ε * (2 ^ c + 1) ^ i) + ε * (2 ^ c + 1) ^ (i + 1) := by
      push_cast
      ring
    rw [k4]
    linarith
private theorem ext_detProductRest : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetProductRest := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.DetProductRest
  intro i c ε h0 h1
  exact two_pow_add_pow_sub_two_pow_mul_le c ε h0 h1 i
end GlobalTheory
end

set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Ext.All
  exact ⟨_root_.GlobalTheory.packingCount, _root_.GlobalTheory.gaussTail_of_card_le, ext_ballVolume, ext_gHadamard,
    _root_.GlobalTheory.nearestPlane_rounding, ext_cauchyBinetMax', ext_detPerturbation,
    ext_detPerturbNumeric, ext_detProductRest⟩
end _root_.GlobalTheory
end GlobalTheory
