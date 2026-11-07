-- Prove2me | solution 1 for KingRockAsymp.Distribution.thm_2_6_display_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T15:33:33.062745+00:00
-- url     : https://prove2.me/submissions/3e7eba6c-72aa-43ff-bfb8-c594237026d9

import Mathlib
import Definitions.Def_KingRockAsymp_Distribution_Basic
import Theorems.Thm_KingRockAsymp_Distribution_thm_2_4_display_upper_lipschitz

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open KingRockAsymp.Distribution

namespace KRLipAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma slice {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) (w : E) :
    Tendsto (fun t : ℝ => t⁻¹ • (g (z + t • w) - g z)) (𝓝[>] (0 : ℝ)) (𝓝 (D w)) := by
  have h2 : Tendsto (fun t : ℝ => (t, w)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
    tendsto_id.prodMk tendsto_const_nhds
  exact (hB w).comp h2

lemma zero_eq {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) : D 0 = 0 := by
  have h := slice hB 0
  simp only [smul_zero, add_zero, sub_self] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma homog {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) {c : ℝ} (hc : 0 < c)
    (w : E) : D (c • w) = c • D w := by
  have h1 := slice hB (c • w)
  have hmul : Tendsto (fun t : ℝ => t * c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => t * c) (𝓝 (0 : ℝ)) (𝓝 (0 * c)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos ht hc
  have h2 := ((slice hB w).comp hmul).const_smul c
  have heq : (fun t : ℝ => t⁻¹ • (g (z + t • (c • w)) - g z)) =
      (fun t : ℝ => c • ((fun t : ℝ => t⁻¹ • (g (z + t • w) - g z)) ∘ (fun t => t * c)) t) := by
    funext t
    simp only [Function.comp, smul_smul, mul_inv]
    rw [show c * (t⁻¹ * c⁻¹) = t⁻¹ by field_simp, mul_comm t c]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

lemma bound {g : E → F} {D : E → F} {z : E} (hB : HasBDerivAt g D z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w, ‖D w‖ ≤ C * ‖w‖ := by
  have hD0 := zero_eq hB
  have h := hB 0 (ball_mem_nhds (D 0) one_pos)
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp ht₂
  have hloc : ∀ w' : E, ‖w'‖ < δ → ‖D w'‖ ≤ 1 := by
    intro w' hw'
    have hs := (slice hB w').norm
    apply le_of_tendsto hs
    filter_upwards [ht₁] with t ht
    have hmem := hsub (mk_mem_prod ht (hδsub (by simpa using hw')))
    simp only [mem_preimage, mem_ball, hD0, dist_zero_right] at hmem
    exact hmem.le
  refine ⟨2 / δ, by positivity, fun w => ?_⟩
  by_cases hw : w = 0
  · simp [hw, hD0]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set c : ℝ := 2 * ‖w‖ / δ with hc_def
  have hc : 0 < c := by positivity
  have hw' : w = c • (c⁻¹ • w) := by rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hn : ‖c⁻¹ • w‖ < δ := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hc, hc_def]
    field_simp
    nlinarith
  rw [hw', homog hB hc, norm_smul, Real.norm_eq_abs, abs_of_pos hc, ← hw']
  calc c * ‖D (c⁻¹ • w)‖ ≤ c * 1 := mul_le_mul_of_nonneg_left (hloc _ hn) hc.le
    _ = 2 / δ * ‖w‖ := by rw [hc_def]; ring

end KRLipAux

theorem solution {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z] [TopologicalSpace.SeparableSpace Z] {n m : ℕ}
    (f : Z → Rn n → Rn m) (N : Rn n → Set (Rn m)) (z₀ : Z) (x₀ : Rn n) (Dz : Z → Rn m)
    (hM : AnalyticalAssumptions f N z₀ x₀ Dz) :
    ∃ U : Set (Rn n), IsCompact U ∧ U ∈ 𝓝 x₀ ∧ ∃ lam : ℝ, 0 ≤ lam ∧
      ∀ᶠ z in 𝓝 z₀, ∀ x ∈ U ∩ solMap f N z, ‖x - x₀‖ ≤ lam * ‖z - z₀‖ := by
  set F := fPlusN f N z₀ with hF_def
  have h0 : (0 : Rn m) ∈ F x₀ := hM.subinv.1
  have hD : contingentDeriv (svInv F) 0 x₀ 0 = {0} := by
    apply Set.Subsingleton.eq_singleton_of_mem (hM.single 0)
    simp only [contingentDeriv, setLimsup, mem_setOf_eq]
    intro ε hε
    apply Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with t _
    refine ⟨((0 : Rn m), (0 : Rn n)), ⟨((0 : Rn m), x₀), h0, by ext <;> simp⟩, by simpa using hε⟩
  obtain ⟨U₁, hU₁, lam, hlam, hev⟩ := thm_2_4_display_upper_lipschitz F x₀ h0 hD
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨Ωz, hΩz, U₂, hU₂, hL⟩ := hM.strong_z.2 1 one_pos
  obtain ⟨C, hC0, hC⟩ := KRLipAux.bound hM.strong_z.1
  have hD0 : Dz 0 = 0 := KRLipAux.zero_eq hM.strong_z.1
  obtain ⟨ρ, hρ, hρsub⟩ := (nhds_basis_closedBall.mem_iff).mp (inter_mem hU₁ hU₂)
  refine ⟨closedBall x₀ ρ, isCompact_closedBall _ _, closedBall_mem_nhds _ hρ,
    lam * (1 + C), by positivity, ?_⟩
  have hsmall : ∀ᶠ z in 𝓝 z₀, (1 + C) * ‖z - z₀‖ < r := by
    have : Tendsto (fun z => (1 + C) * ‖z - z₀‖) (𝓝 z₀) (𝓝 ((1 + C) * ‖z₀ - z₀‖)) :=
      ((continuous_id.sub continuous_const).norm.const_mul (1 + C)).tendsto z₀
    rw [sub_self, norm_zero, mul_zero] at this
    exact this (Iio_mem_nhds hr)
  filter_upwards [hΩz, hsmall] with z hzΩ hzr
  rintro x ⟨hxB, v, hvN, hv0⟩
  have hxU := hρsub hxB
  have hlz := (hL x hxU.2).dist_le_mul z hzΩ z₀ (mem_of_mem_nhds hΩz)
  rw [sub_self, sub_self, hD0, sub_zero, dist_eq_norm, dist_eq_norm, sub_zero,
    Real.coe_toNNReal _ zero_le_one, one_mul] at hlz
  set y : Rn m := f z₀ x - f z x with hy_def
  have hyF : x ∈ svInv F y := by
    refine ⟨v, hvN, ?_⟩
    have : v = -f z x := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hv0.symm
    rw [hy_def, this, sub_eq_add_neg]
  have hyb : ‖y‖ ≤ (1 + C) * ‖z - z₀‖ := by
    have e : y = -((f z x - f z₀ x - Dz (z - z₀)) + Dz (z - z₀)) := by
      rw [hy_def]; abel
    rw [e, norm_neg]
    calc ‖(f z x - f z₀ x - Dz (z - z₀)) + Dz (z - z₀)‖
        ≤ ‖f z x - f z₀ x - Dz (z - z₀)‖ + ‖Dz (z - z₀)‖ := norm_add_le _ _
      _ ≤ ‖z - z₀‖ + C * ‖z - z₀‖ := by
          have := hC (z - z₀)
          have hlz' : ‖f z x - f z₀ x - Dz (z - z₀)‖ ≤ ‖z - z₀‖ := by
            exact hlz
          linarith
      _ = (1 + C) * ‖z - z₀‖ := by ring
  have hin := hball (show dist y 0 < r by rw [dist_zero_right]; linarith) ⟨hxU.1, hyF⟩
  rw [mem_closedBall, dist_eq_norm] at hin
  calc ‖x - x₀‖ ≤ lam * ‖y‖ := hin
    _ ≤ lam * ((1 + C) * ‖z - z₀‖) := mul_le_mul_of_nonneg_left hyb hlam
    _ = lam * (1 + C) * ‖z - z₀‖ := by ring
