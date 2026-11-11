-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:11.125953+00:00
-- url     : https://prove2.me/submissions/590494f1-fb7d-4872-b07c-a214a0639c1a

import Mathlib

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactTimeIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory Set Filter
open scoped Topology
variable {V : Type*} [TopologicalSpace V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [IsFiniteMeasureOnCompacts μ]

lemma hasDerivAt_integral_compact_positive_oai (F F' : ℝ → V → ℝ)
    (K : Set V) (hK : IsCompact K)
    (hF : ∀ t, 0 < t → Continuous (F t))
    (hF' : ContinuousOn (fun p : ℝ × V => F' p.1 p.2) (Ioi 0 ×ˢ univ))
    (hsupp : ∀ t, 0 < t → Function.support (F t) ⊆ K)
    (hsupp' : ∀ t, 0 < t → Function.support (F' t) ⊆ K)
    (hd : ∀ t, 0 < t → ∀ x, HasDerivAt (fun s => F s x) (F' t x) t)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, F s x ∂μ) (∫ x, F' t x ∂μ) t := by
  have hF'c (s : ℝ) (hs : 0 < s) : Continuous (F' s) :=
    continuousOn_univ.mp (hF'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ _ => ⟨hs,mem_univ _⟩))
  have hFc (s : ℝ) (hs : 0 < s) : HasCompactSupport (F s) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hsupp s hs) hK.isClosed)
  have hIc : IsCompact (Icc (t/2) (2*t) ×ˢ K) := isCompact_Icc.prod hK
  have hIsub : Icc (t/2) (2*t) ×ˢ K ⊆ Ioi 0 ×ˢ (univ : Set V) := by
    intro p hp
    exact ⟨lt_of_lt_of_le (by linarith) hp.1.1,mem_univ _⟩
  obtain ⟨C,hC⟩ := hIc.exists_bound_of_continuousOn (hF'.mono hIsub)
  let b : V → ℝ := K.indicator (fun _ => max C 0)
  have hb : Integrable b μ :=
    (integrableOn_const (hK.measure_lt_top.ne)).integrable_indicator hK.isClosed.measurableSet
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := b) (s := Icc (t/2) (2*t))
    (Icc_mem_nhds (by linarith) (by linarith)) ?_
    ((hF t ht).integrable_of_hasCompactSupport (hFc t ht))
    (hF'c t ht).aestronglyMeasurable ?_ hb ?_).2
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact (hF s hs).aestronglyMeasurable
  · filter_upwards [] with x
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by linarith) hs.1
    by_cases hx : x ∈ K
    · exact (hC (s,x) ⟨hs,hx⟩).trans (by simp only [b,indicator_of_mem hx]; exact le_max_left _ _)
    · have hz : F' s x = 0 := by
        by_contra hn
        exact hx (hsupp' s hspos hn)
      simp [b,indicator_of_notMem hx,hz]
  · filter_upwards [] with x
    intro s hs
    exact hd s (lt_of_lt_of_le (by linarith) hs.1) x

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive_oai.{u_1} := @OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.hasDerivAt_integral_compact_positive_oai.{u_1}
