-- Prove2me | solution 1 for GlobalTheory.CosetIntegral.integral_sum_indicator_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:00:02.50275+00:00
-- url     : https://prove2.me/submissions/97df9548-4e5b-499e-9d69-b161e2a9cb03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralSumIndicatorTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CosetIntegral
namespace GlobalTheory.CosetIntegral
theorem _root_.solution {G ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulRightInvariant] (H : Set G) (hH : IsOpen H) (hm : m H = 1) (T : Finset ι)
    (r : ι → G) (c : ι → ℂ) :
    ∫ x, ∑ q ∈ T, ((fun y => y * (r q)⁻¹) ⁻¹' H).indicator (fun _ => c q) x ∂m
      = ∑ q ∈ T, c q := by
  have hmeas : ∀ q, MeasurableSet ((fun y => y * (r q)⁻¹) ⁻¹' H) := fun q =>
    (hH.preimage (continuous_mul_right _)).measurableSet
  have hmq : ∀ q, m ((fun y => y * (r q)⁻¹) ⁻¹' H) = 1 := fun q => by
    rw [measure_preimage_mul_right, hm]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), measureReal_def, hmq q]
    simp
  · intro q _
    exact (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hmq q]; simp))
end GlobalTheory.CosetIntegral
