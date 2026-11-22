-- Prove2me | solution 1 for MasulloAudit.truncated_convolution_not_compact
-- status  : ACCEPTED   (prove)
-- author  : @deleted
-- created : 2026-11-21T00:30:10.808968+00:00
-- url     : https://prove2.me/submissions/8e12c5de-4771-472f-bf1f-d36739ca1557

import Definitions.Def_MasulloAudit_TruncConv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Compact.Basic

open Filter Topology MasulloAudit

namespace MasulloAuditB

theorem not_isCompactOperator_of_weakly_null {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {T : E →L[𝕜] F} {x : ℕ → E} {R c : ℝ}
    (hb : ∀ n, ‖x n‖ ≤ R)
    (hw : ∀ y : E, Tendsto (fun n => (inner 𝕜 y (x n) : 𝕜)) atTop (𝓝 0))
    (hc0 : 0 < c) (hc : ∀ᶠ n in atTop, c ≤ ‖T (x n)‖) :
    ¬ IsCompactOperator T := by
  intro hT
  obtain ⟨K, hK, hsub⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := (T : E →ₗ[𝕜] F)) hT R
  have hmem : ∀ n, T (x n) ∈ K := fun n =>
    hsub ⟨x n, by simpa using hb n, rfl⟩
  obtain ⟨z, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have h1 : Tendsto (fun n => (inner 𝕜 z (T (x (φ n))) : 𝕜)) atTop (𝓝 (inner 𝕜 z z)) :=
    tendsto_const_nhds.inner hlim
  have h2 : Tendsto (fun n => (inner 𝕜 z (T (x (φ n))) : 𝕜)) atTop (𝓝 0) := by
    have := (hw (ContinuousLinearMap.adjoint T z)).comp hφ.tendsto_atTop
    refine this.congr fun n => ?_
    simp [Function.comp, ContinuousLinearMap.adjoint_inner_left]
  have hz : z = 0 := inner_self_eq_zero.mp (tendsto_nhds_unique h1 h2)
  subst hz
  have h3 : Tendsto (fun n => ‖T (x (φ n))‖) atTop (𝓝 0) := by
    simpa using hlim.norm
  obtain ⟨n, hn1, hn2⟩ :=
    ((hφ.tendsto_atTop.eventually hc).and (h3.eventually (gt_mem_nhds hc0))).exists
  exact absurd hn1 (not_le.mpr hn2)

end MasulloAuditB

theorem solution (a : ℤ →₀ ℂ) (ha : a ≠ 0) : ¬ IsCompactOperator (MasulloAudit.truncConv a) := by
  classical
  obtain ⟨k₀, hk₀⟩ : ∃ k, a k ≠ 0 := by
    by_contra h; push Not at h; exact ha (Finsupp.ext h)
  let e : ℕ → L2Z := fun m => lp.single 2 (-(m : ℤ)) (1 : ℂ)
  refine MasulloAuditB.not_isCompactOperator_of_weakly_null (x := e) (R := 1) (c := ‖a k₀‖)
    (fun m => ?_) (fun y => ?_) (norm_pos_iff.mpr hk₀) ?_
  · simp [e, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  · -- weak nullity: `⟪y, e_m⟫ = conj (y (-m)) → 0`
    simp only [e, lp.inner_single_right]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hs := ((lp.memℓp y).summable two_toReal_pos).tendsto_cofinite_zero
    have hneg : Tendsto (fun m : ℕ => -(m : ℤ)) atTop cofinite := by
      rw [← Nat.cofinite_eq_atTop]
      exact (neg_injective.comp Nat.cast_injective).tendsto_cofinite
    have hc := (Real.continuousAt_rpow_const 0 (1 / (2 : ENNReal).toReal)
      (Or.inr (by norm_num))).tendsto.comp (hs.comp hneg)
    rw [Real.zero_rpow (by norm_num)] at hc
    refine hc.congr fun m => ?_
    simp only [Function.comp]
    rw [← Real.rpow_mul (norm_nonneg _)]
    simp
  · refine eventually_atTop.2 ⟨k₀.toNat, fun m hm => ?_⟩
    have hm' : k₀ ≤ (m : ℤ) := by omega
    refine le_trans (le_of_eq ?_) (lp.norm_apply_le_norm (by norm_num) _ (k₀ - m))
    rw [truncConv_apply, if_pos (by omega), Finset.sum_eq_single k₀]
    · simp [e, lp.single_apply]
    · intro k _ hk
      simp [e, lp.single_apply, Pi.single_apply]
      omega
    · intro h; exact absurd (Finsupp.mem_support_iff.mpr hk₀) h

