-- Prove2me | solution 1 for GlobalTheory.hasFDerivAt_of_continuous_partials
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:42.764356+00:00
-- url     : https://prove2.me/submissions/f8672cca-0345-4efa-bc2b-2d873965ad2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HasFDerivAtOfContinuousPartials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology
namespace GlobalTheory
open Filter Topology in
private theorem norm_update_sub_update_sub_smul_le {k : ℕ} (F : (Fin k → ℝ) → ℂ)
    (d : Fin k → (Fin k → ℝ) → ℂ)
    (hF : ∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i))
    (i : Fin k) (t y : Fin k → ℝ) {ε δ : ℝ} (hδ : 0 < δ)
    (hgood : ∀ z, dist z t < δ → ‖d i z - d i t‖ ≤ ε) (hy : dist y t < δ) {a b : ℝ}
    (ha : dist a (t i) < δ) (hb : dist b (t i) < δ) :
    ‖F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t‖ ≤ ε * |b - a| := by
  set g : ℝ → ℂ := fun s => F (Function.update y i s) - s • d i t with hg
  have hmem : ∀ s ∈ Metric.ball (t i) δ, dist (Function.update y i s) t < δ := by
    intro s hs
    rw [dist_pi_lt_iff hδ]
    intro m
    by_cases hm : m = i
    · subst hm
      simpa using hs
    · rw [Function.update_of_ne hm]
      exact lt_of_le_of_lt (dist_le_pi_dist y t m) hy
  have hderiv : ∀ s ∈ Metric.ball (t i) δ,
      HasDerivWithinAt g (d i (Function.update y i s) - d i t) (Metric.ball (t i) δ) s := by
    intro s _
    have h1 := hF i (Function.update y i s)
    simp only [Function.update_idem, Function.update_self] at h1
    have h2 : HasDerivAt (fun u : ℝ => u • d i t) ((1 : ℝ) • d i t) s :=
      (hasDerivAt_id s).smul_const (d i t)
    rw [one_smul] at h2
    exact (h1.sub h2).hasDerivWithinAt
  have hbound : ∀ s ∈ Metric.ball (t i) δ, ‖d i (Function.update y i s) - d i t‖ ≤ ε :=
    fun s hs => hgood _ (hmem s hs)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_ball (t i) δ) (Metric.mem_ball.2 ha) (Metric.mem_ball.2 hb)
  have hdiff : g b - g a = F (Function.update y i b) - F (Function.update y i a) - (b - a) • d i t := by
    simp only [hg, sub_smul]
    abel
  rw [hdiff, Real.norm_eq_abs] at key
  exact key
end GlobalTheory
end

set_option autoImplicit false
open Filter Topology
open GlobalTheory
open Filter Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (d : Fin k → (Fin k → ℝ) → ℂ),
      (∀ i t, HasDerivAt (fun s : ℝ => F (Function.update t i s)) (d i t) (t i)) →
      (∀ i, Continuous (d i)) →
      ∀ t, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) t := by
  intro k F d hF hd t
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set ε : ℝ := c / (k + 1) with hε
  have hεpos : 0 < ε := div_pos hc (by positivity)
  have hev : ∀ᶠ z in 𝓝 t, ∀ i, dist (d i z) (d i t) < ε :=
    eventually_all.2 fun i => (hd i).continuousAt.eventually (Metric.ball_mem_nhds (d i t) hεpos)
  obtain ⟨δ, hδ, hδgood⟩ := Metric.eventually_nhds_iff.1 hev
  have hgood : ∀ i z, dist z t < δ → ‖d i z - d i t‖ ≤ ε := fun i z hz =>
    (dist_eq_norm (d i z) (d i t) ▸ (hδgood hz i)).le
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  set p : ℕ → (Fin k → ℝ) := fun j m => if (m : ℕ) < j then t m + h m else t m with hp
  set a : ℕ → ℂ := fun j => if hj : j < k then h ⟨j, hj⟩ • d ⟨j, hj⟩ t else 0 with ha
  have hp0 : p 0 = t := by
    funext m
    simp [hp]
  have hpk : p k = t + h := by
    funext m
    simp [hp, m.isLt]
  have hsumL : (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h =
      ∑ j ∈ Finset.range k, a j := by
    rw [Finset.sum_range]
    simp [ha, ContinuousLinearMap.sum_apply]
  have htel : F (t + h) - F t = ∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j)) := by
    rw [Finset.sum_range_sub (fun j => F (p j)) k, hpk, hp0]
  have hpdist : ∀ j, dist (p j) t < δ := by
    intro j
    rw [dist_pi_lt_iff hδ]
    intro m
    simp only [hp]
    split_ifs
    · rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h m) hh
    · simpa using hδ
  have hstep : ∀ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ ≤ ε * ‖h‖ := by
    intro j hj
    have hjk : j < k := Finset.mem_range.1 hj
    set i : Fin k := ⟨j, hjk⟩ with hi
    have haj : a j = ((t i + h i) - t i) • d i t := by
      simp [ha, hjk, hi]
    have hnext : p (j + 1) = Function.update (p j) i (t i + h i) := by
      funext m
      by_cases hm : m = i
      · subst hm
        simp [hp, hi]
      · have hm' : (m : ℕ) ≠ j := fun e => hm (Fin.ext e)
        rw [Function.update_of_ne hm]
        simp only [hp]
        have : (m : ℕ) < j + 1 ↔ (m : ℕ) < j := by omega
        simp only [this]
    have hcur : p j = Function.update (p j) i (t i) := by
      symm
      rw [Function.update_eq_self_iff]
      simp [hp, hi]
    have hx : dist (t i + h i) (t i) < δ := by
      rw [Real.dist_eq, add_sub_cancel_left]
      exact lt_of_le_of_lt (by simpa using norm_le_pi_norm h i) hh
    have hmain := norm_update_sub_update_sub_smul_le F d hF i t (p j) hδ (hgood i) (hpdist j)
      (a := t i) (b := t i + h i) (by rw [dist_self]; exact hδ) hx
    rw [haj, hnext]
    conv_lhs => rw [hcur]
    rw [Function.update_idem]
    refine hmain.trans ?_
    gcongr
    rw [add_sub_cancel_left]
    simpa using norm_le_pi_norm h i
  calc ‖F (t + h) - F t - (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (d i t)) h‖
      = ‖∑ j ∈ Finset.range k, (F (p (j + 1)) - F (p j) - a j)‖ := by
        rw [hsumL, htel, ← Finset.sum_sub_distrib]
    _ ≤ ∑ j ∈ Finset.range k, ‖F (p (j + 1)) - F (p j) - a j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range k, ε * ‖h‖ := Finset.sum_le_sum hstep
    _ = k * (ε * ‖h‖) := by simp
    _ ≤ c * ‖h‖ := by
        rw [← mul_assoc]
        gcongr
        rw [hε, mul_div_assoc']
        rw [div_le_iff₀ (by positivity)]
        nlinarith
end _root_.GlobalTheory
end GlobalTheory
