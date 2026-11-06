-- Prove2me | solution 1 for LinParamBandits.LowerBound.bayes_risk_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:25:35.350475+00:00
-- url     : https://prove2.me/submissions/6aa4abc6-7790-47fa-b0af-94981647612d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model
import Theorems.Thm_LinParamBandits_LowerBound_risk_decomposition
import Theorems.Thm_LinParamBandits_LowerBound_min_directional_risk

open MeasureTheory ProbabilityTheory

namespace LPBLowerAux
open LinParamBandits.LowerBound

/-- Householder-type reflection along `u` (identity when `u = 0`, by `x / 0 = 0`). -/
noncomputable def refl {r : ℕ} (u x : Vec r) : Vec r :=
  x - (2 * inner ℝ u x / inner ℝ u u) • u

lemma refl_inner {r : ℕ} (u x y : Vec r) :
    inner ℝ (refl u x) (refl u y) = inner ℝ x y := by
  unfold refl
  by_cases hu : inner ℝ u u = (0 : ℝ)
  · rw [hu]; simp
  · simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [real_inner_comm x u]
    field_simp
    ring

lemma refl_perp {r : ℕ} (w e x : Vec r) (hw : ‖w‖ = 1) (he : ‖e‖ = 1)
    (hx : inner ℝ x e = (0 : ℝ)) : inner ℝ (refl (w - e) x) w = (0 : ℝ) := by
  have hww : inner ℝ w w = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hw]; norm_num
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  unfold refl
  by_cases hc : inner ℝ (w - e) (w - e) = (0 : ℝ)
  · have : w - e = 0 := by
      rw [real_inner_self_eq_norm_sq] at hc
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg (w - e)])
    have hwe : w = e := sub_eq_zero.mp this
    subst hwe
    simp [hx]
  · have hc' : inner ℝ (w - e) (w - e) = 2 - 2 * inner ℝ w e := by
      simp only [inner_sub_left, inner_sub_right, hww, hee]
      rw [real_inner_comm e w]; ring
    have hux : inner ℝ (w - e) x = inner ℝ w x := by
      rw [inner_sub_left, real_inner_comm x e, hx, sub_zero]
    have huw : inner ℝ (w - e) w = 1 - inner ℝ w e := by
      rw [inner_sub_left, hww, real_inner_comm e w]
    rw [inner_sub_left, inner_smul_left, hux, huw, hc', RCLike.conj_to_real]
    rw [hc'] at hc
    have h1 : (1 - inner ℝ w e) ≠ 0 := by intro h; apply hc; linarith
    rw [real_inner_comm x w]
    field_simp
    ring

noncomputable def ek {r : ℕ} (i : Fin r) : Vec r := EuclideanSpace.single i 1

lemma ek_inner {r : ℕ} (i j : Fin r) :
    inner ℝ (ek i) (ek j) = if i = j then (1 : ℝ) else 0 := by
  unfold ek
  rw [EuclideanSpace.inner_single_left]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The direction family: reflect the first `r - 1` basis vectors along the reflection taking the
last basis vector to `v / ‖v‖`. -/
noncomputable def dirs {r : ℕ} (hr : 2 ≤ r) (v : Vec r) (k : Fin (r - 1)) : Vec r :=
  refl (‖v‖⁻¹ • v - ek (⟨r - 1, by omega⟩ : Fin r))
    (ek (Fin.castLE (by omega) k))

lemma dirs_orth {r : ℕ} (hr : 2 ≤ r) (v : Vec r) : Orthonormal ℝ (dirs hr v) := by
  rw [orthonormal_iff_ite]
  intro i j
  unfold dirs
  rw [refl_inner, ek_inner]
  by_cases h : i = j
  · simp [h]
  · have : Fin.castLE (by omega : r - 1 ≤ r) i ≠ Fin.castLE (by omega) j := by
      intro h'; exact h (Fin.castLE_injective _ h')
    simp [h, this]

lemma dirs_perp {r : ℕ} (hr : 2 ≤ r) (v : Vec r) (k : Fin (r - 1)) :
    inner ℝ (dirs hr v k) v = (0 : ℝ) := by
  by_cases hv : v = 0
  · simp [hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hw : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have he : ‖ek (⟨r - 1, by omega⟩ : Fin r)‖ = 1 := by simp [ek]
    have hx : inner ℝ (ek (Fin.castLE (by omega : r - 1 ≤ r) k)) (ek (⟨r - 1, by omega⟩ : Fin r))
        = (0 : ℝ) := by
      rw [ek_inner, if_neg]
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have key := refl_perp _ _ _ hw he hx
    have hv' : v = ‖v‖ • (‖v‖⁻¹ • v) := by
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    unfold dirs
    rw [hv', inner_smul_right, ← hv', key, mul_zero]

lemma measurable_dirs {r : ℕ} (hr : 2 ≤ r) (k : Fin (r - 1)) :
    Measurable (fun v : Vec r => dirs hr v k) := by
  unfold dirs refl
  fun_prop

end LPBLowerAux

open LinParamBandits.LowerBound LPBLowerAux in
theorem solution (r : ℕ) (hr : 2 ≤ r) (ψ : SpherePolicy r) (T : ℕ) (hT : r ^ 2 ≤ T) :
    ENNReal.ofReal (0.006 * r * Real.sqrt T) ≤ risk ψ T ∧
      ∃ z : Vec r, ENNReal.ofReal (0.006 * r * Real.sqrt T) ≤ regret ψ z T := by
  -- a measurable version of `Ẑ_T` as a function of the history
  have hsm : StronglyMeasurable[(inferInstance : MeasurableSpace (History r T)).comap
      (fun ω : Ω r => hist ψ ω.1 ω.2 T)] (zhat ψ T) := by
    unfold zhat
    exact stronglyMeasurable_condExp
  obtain ⟨g, hg, hgeq⟩ := hsm.exists_eq_measurable_comp
  have hgm : Measurable g := hg.measurable
  let S : Fin (r - 1) → History r T → Vec r := fun k h => dirs hr (g h) k
  have hS_meas : ∀ k, Measurable (S k) := fun k => (measurable_dirs hr k).comp hgm
  have hS_orth : ∀ h, Orthonormal ℝ (fun k => S k h) := fun h => dirs_orth hr (g h)
  have hS_perp : ∀ᵐ ω ∂(P r), ∀ k, inner ℝ (S k (hist ψ ω.1 ω.2 T)) (zhat ψ T ω) = 0 := by
    refine Filter.Eventually.of_forall (fun ω k => ?_)
    rw [hgeq]
    exact dirs_perp hr _ k
  have hT1 : 1 ≤ T := by nlinarith
  have hdec := risk_decomposition r hr ψ T hT1 S hS_meas hS_orth hS_perp
  have hmin := fun k => min_directional_risk r hr ψ T hT S hS_meas hS_orth hS_perp k
  -- the lower bound `0.0135 (r-1) √T`
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < T))
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlow : ENNReal.ofReal (0.0135 * ((r : ℝ) - 1) * Real.sqrt T) ≤ risk ψ T := by
    refine le_trans ?_ hdec
    have hsum : (∑ _k : Fin (r - 1), ENNReal.ofReal (0.027 * Real.sqrt T)) ≤ ∑ k, _ :=
      Finset.sum_le_sum (fun k _ => hmin k)
    refine le_trans ?_ (by gcongr : (2:ENNReal)⁻¹ * (∑ _k : Fin (r - 1), ENNReal.ofReal (0.027 * Real.sqrt T)) ≤ 2⁻¹ * _)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hcast : ((r - 1 : ℕ) : ENNReal) = ENNReal.ofReal ((r : ℝ) - 1) := by
      rw [← ENNReal.ofReal_natCast]
      congr 1
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hcast, ← ENNReal.ofReal_mul (by linarith),
      show (2 : ENNReal)⁻¹ = ENNReal.ofReal (1 / 2) by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply le_of_eq
    congr 1
    ring
  have hlt : ENNReal.ofReal (0.006 * r * Real.sqrt T)
      < ENNReal.ofReal (0.0135 * ((r : ℝ) - 1) * Real.sqrt T) := by
    rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith)]
    nlinarith
  refine ⟨le_trans hlt.le hlow, ?_⟩
  -- `risk ≤ sup_z regret` since the prior is a probability measure
  have hprob : (prior r) Set.univ ≤ 1 := by
    unfold prior
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp
  have hsup : risk ψ T ≤ ⨆ z, regret ψ z T := by
    unfold risk
    calc ∫⁻ z, regret ψ z T ∂(prior r) ≤ ∫⁻ _z, (⨆ z, regret ψ z T) ∂(prior r) :=
          lintegral_mono (fun z => le_iSup (fun z => regret ψ z T) z)
      _ = (⨆ z, regret ψ z T) * (prior r) Set.univ := lintegral_const _
      _ ≤ (⨆ z, regret ψ z T) * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨z, hz⟩ := lt_iSup_iff.mp (lt_of_lt_of_le hlt (le_trans hlow hsup))
  exact ⟨z, hz.le⟩
