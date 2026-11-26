-- Prove2me | solution 1 for Kyprianou.Ch04.weightedCompensatorRightV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:42:16.924075+00:00
-- url     : https://prove2.me/submissions/6eb932ff-873e-4db7-bf37-f4c5c5cfb13c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_boundedPrimitiveLipschitzV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Right continuity of a weighted mark compensator along a measurable left-limit path. -/
theorem solution (ν : Measure ℝ) (B : Set ℝ) (L : NNReal → ℝ)
    (hL : Measurable L) (f : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici 0 ×ˢ univ))
    (hb : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K) :
    ∀ t : NNReal, Tendsto
      (fun v : NNReal => ∫ s in Icc (0 : ℝ) (v : ℝ),
        (∫ x in B, x * f s (L s.toNNReal) ∂ν) ∂volume)
      (𝓝[>] t) (𝓝 (∫ s in Icc (0 : ℝ) (t : ℝ),
        (∫ x in B, x * f s (L s.toNNReal) ∂ν) ∂volume)) := by
  let c := ∫ x in B, x ∂ν
  let g (s : ℝ) := c * f (max 0 s) (L s.toNNReal)
  have hf : Continuous (fun z : ℝ × ℝ => f (max 0 z.1) z.2) :=
    hc.comp_continuous (f := fun z : ℝ × ℝ => (max 0 z.1,z.2))
      (by fun_prop) (fun z => ⟨show (0 : ℝ) ≤ max 0 z.1 from le_max_left _ _, mem_univ _⟩)
  have hg : Measurable g :=
    measurable_const.mul (hf.measurable.comp
      (measurable_id.prodMk (hL.comp measurable_real_toNNReal)))
  have hgb : ∀ s : ℝ, 0 ≤ s → |g s| ≤ |c| * K := by
    intro s hs
    dsimp [g]
    rw [abs_mul, max_eq_right hs]
    exact mul_le_mul_of_nonneg_left (hb s _ hs) (abs_nonneg _)
  let A (t : NNReal) := ∫ s in Icc (0 : ℝ) (t : ℝ), g s ∂volume
  have hA (t : NNReal) : (∫ s in Icc (0 : ℝ) (t : ℝ),
      (∫ x in B, x * f s (L s.toNNReal) ∂ν) ∂volume) = A t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    change (∫ x in B, x * f s (L s.toNNReal) ∂ν) = g s
    rw [integral_mul_const]
    simp [g,c,max_eq_right hs.1]
  simp only [hA]
  intro t
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  let C := |c| * K
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) hK
  refine ⟨ε/(C+1), div_pos hε (by linarith), ?_⟩
  intro v hv hdist
  have htv : t ≤ v := (show t < v from hv).le
  have h := Kyprianou.Ch04.boundedPrimitiveLipschitzV1 g C hC hg hgb t v htv
  have hv' : (t : ℝ) ≤ (v : ℝ) := NNReal.coe_le_coe.mpr htv
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv')] at hdist
  rw [Real.dist_eq]
  change |A v - A t| < ε
  apply h.trans_lt
  have hmul := (lt_div_iff₀ (show 0 < C+1 by linarith)).mp hdist
  nlinarith [sub_nonneg.mpr hv']
