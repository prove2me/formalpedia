-- Prove2me | solution 1 for JHolomorphic.uniformCauchySeqOn_normed_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:34:04.71204+00:00
-- url     : https://prove2.me/submissions/ece7742a-2d64-46d2-bd88-f2b6130f7bbb

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Theorems.Thm_JHolomorphic_enorm_le_of_hasWeakPartialsOn_ball
import Theorems.Thm_JHolomorphic_fderiv_normed_convolution_eq_of_hasWeakPartialsOn
import Theorems.Thm_JHolomorphic_eLpNorm_normed_convolution_le
import Theorems.Thm_JHolomorphic_tendsto_eLpNorm_normed_convolution_sub
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.MetricSpace.Thickening



namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal

theorem uniformCauchySeqOn_normed_convolution_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {Y Ys Yt : ℂ → E} (hYc : HasCompactSupport Y) (hY : MemLp Y (ENNReal.ofReal p) volume)
    (h : HasWeakPartialsOn Set.univ Y Ys Yt) (hs : MemLp Ys (ENNReal.ofReal p) volume)
    (ht : MemLp Yt (ENNReal.ofReal p) volume) :
    UniformCauchySeqOn (fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Y) atTop Set.univ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set q := ENNReal.ofReal p with hq
  have hq1 : 1 ≤ q := by rw [hq]; exact ENNReal.one_le_ofReal.2 (by linarith)
  have hqt : q ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨C, hC⟩ := enorm_le_of_hasWeakPartialsOn_ball (E := E) p hp
  obtain ⟨R0, hR0⟩ := hYc.isCompact.isBounded.subset_ball (0 : ℂ)
  set Rb := |R0| + 2 with hRb
  have hRb0 : 0 < Rb := by positivity
  set B := ball (0 : ℂ) Rb with hB
  set F : ℕ → ℂ → E := fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Y with hF
  have hYli : LocallyIntegrable Y volume := hY.locallyIntegrable hq1
  have hYsli : LocallyIntegrable Ys volume := hs.locallyIntegrable hq1
  have hYtli : LocallyIntegrable Yt volume := ht.locallyIntegrable hq1
  have hFcd : ∀ n, ContDiff ℝ 1 (F n) := fun n =>
    (φ n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) (φ n).contDiff_normed hYli
  have hFd : ∀ n z, fderiv ℝ (F n) z 1 = ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Ys) z ∧
      fderiv ℝ (F n) z Complex.I = ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Yt) z :=
    fun n z => fderiv_normed_convolution_eq_of_hasWeakPartialsOn (φ n) h hYli z
  -- mollified partials are in `L^p`
  have hconvL : ∀ n {G : ℂ → E}, MemLp G q volume →
      MemLp ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] G) q volume := by
    intro n G hG
    refine ⟨((φ n).hasCompactSupport_normed.continuous_convolution_left _ (φ n).continuous_normed
      (hG.locallyIntegrable hq1)).aestronglyMeasurable, ?_⟩
    exact (eLpNorm_normed_convolution_le (φ n) hq1 hqt hG.1).trans_lt hG.2
  -- support of the mollifications
  have hFsupp : ∀ n, (φ n).rOut < 1 → tsupport (F n) ⊆ closedBall 0 (|R0| + 1) := by
    intro n hn
    refine closure_minimal ?_ isClosed_closedBall
    intro x hx
    obtain ⟨a, ha, b, hb, hab⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
    rw [(φ n).support_normed_eq, mem_ball, dist_zero_right] at ha
    have hb' := hR0 (subset_tsupport _ hb)
    rw [mem_ball, dist_zero_right] at hb'
    rw [mem_closedBall, dist_zero_right, ← hab]
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ ≤ 1 + |R0| := add_le_add (ha.trans hn).le (hb'.le.trans (le_abs_self _))
      _ = |R0| + 1 := add_comm _ _
  have hcB : closedBall (0 : ℂ) (|R0| + 1) ⊆ B := closedBall_subset_ball (by linarith)
  -- the key estimate
  set a : ℕ → ℝ≥0∞ := fun n =>
    eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Ys - Ys) q volume +
      eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Yt - Yt) q volume with ha
  set K : ℝ≥0∞ := ENNReal.ofReal (C * Rb ^ (1 - 2 / p)) with hK
  have hdiffL : ∀ n m {G : ℂ → E}, MemLp G q volume →
      eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] G -
        (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] G) q (volume.restrict B) ≤
      eLpNorm ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] G - G) q volume +
        eLpNorm ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] G - G) q volume := by
    intro n m G hG
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have e : (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] G -
        (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] G =
        ((φ n).normed volume ⋆[lsmul ℝ ℝ, volume] G - G) -
          ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] G - G) := by abel
    rw [e]
    exact eLpNorm_sub_le ((hconvL n hG).1.sub hG.1) ((hconvL m hG).1.sub hG.1) hq1
  have hest : ∀ n m, (φ n).rOut < 1 → (φ m).rOut < 1 → ∀ z,
      ‖F n z - F m z‖ₑ ≤ K * (a n + a m) := by
    intro n m hn hm z
    set ξ : ℂ → E := F n - F m with hξ
    have hξcd : ContDiff ℝ 1 ξ := (hFcd n).sub (hFcd m)
    have hξsupp : tsupport ξ ⊆ B := by
      refine (closure_minimal (fun x hx => ?_) isClosed_closedBall).trans hcB
      by_contra hxc
      apply hx
      have h1 : F n x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hxc (hFsupp n hn h'))
      have h2 : F m x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hxc (hFsupp m hm h'))
      simp [hξ, h1, h2]
    have hξd : ∀ (v : ℂ) z, fderiv ℝ ξ z v = fderiv ℝ (F n) z v - fderiv ℝ (F m) z v := by
      intro v z
      rw [hξ, fderiv_sub ((hFcd n).differentiable one_ne_zero z)
        ((hFcd m).differentiable one_ne_zero z)]
      rfl
    have hW := HasWeakPartialsOn.of_contDiffOn isOpen_ball (U := B) hξcd.contDiffOn
    have es : (fun z => fderiv ℝ ξ z 1) = (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Ys -
        (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] Ys := by
      funext z; rw [hξd, (hFd n z).1, (hFd m z).1]; rfl
    have et : (fun z => fderiv ℝ ξ z Complex.I) =
        (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Yt -
          (φ m).normed volume ⋆[lsmul ℝ ℝ, volume] Yt := by
      funext z; rw [hξd, (hFd n z).2, (hFd m z).2]; rfl
    rw [es, et] at hW
    have hb := hC 0 Rb hRb0 ξ _ _ hξcd.continuous hξsupp hW
      (((hconvL n hs).sub (hconvL m hs)).mono_measure Measure.restrict_le_self)
      (((hconvL n ht).sub (hconvL m ht)).mono_measure Measure.restrict_le_self) z
    refine hb.trans ?_
    rw [← hK]
    gcongr K * ?_
    calc _ ≤ _ := add_le_add (hdiffL n m hs) (hdiffL n m ht)
      _ = a n + a m := by rw [ha]; ring
  -- `a n → 0`
  have ha0 : Tendsto (fun n => K * a n) atTop (𝓝 0) := by
    have h1 := tendsto_eLpNorm_normed_convolution_sub hq1 hqt φ hφ hs
    have h2 := tendsto_eLpNorm_normed_convolution_sub hq1 hqt φ hφ ht
    have := ENNReal.Tendsto.const_mul (a := K) (h1.add h2) (Or.inr ENNReal.ofReal_ne_top)
    simpa [ha] using this
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((ha0.eventually (gt_mem_nhds hε2)).and (hφ.eventually (gt_mem_nhds one_pos)))
  refine ⟨N, fun m hm n hn z _ => ?_⟩
  rw [← edist_lt_ofReal, edist_eq_enorm_sub]
  calc ‖F m z - F n z‖ₑ ≤ K * (a m + a n) := hest m n (hN m hm).2 (hN n hn).2 z
    _ = K * a m + K * a n := mul_add _ _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        ENNReal.add_lt_add (hN m hm).1 (hN n hn).1
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

end JHolomorphic

open JHolomorphic

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (φ : ℕ → ContDiffBump (0 : ℂ)) (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    {Y Ys Yt : ℂ → E} (hYc : HasCompactSupport Y) (hY : MemLp Y (ENNReal.ofReal p) volume)
    (h : HasWeakPartialsOn Set.univ Y Ys Yt) (hs : MemLp Ys (ENNReal.ofReal p) volume)
    (ht : MemLp Yt (ENNReal.ofReal p) volume) :
    UniformCauchySeqOn (fun n => (φ n).normed volume ⋆[lsmul ℝ ℝ, volume] Y) atTop Set.univ :=
  uniformCauchySeqOn_normed_convolution_aux p hp φ hφ hYc hY h hs ht
