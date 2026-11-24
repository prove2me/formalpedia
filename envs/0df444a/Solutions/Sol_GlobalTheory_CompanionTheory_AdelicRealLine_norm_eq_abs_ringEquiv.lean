-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:24.554432+00:00
-- url     : https://prove2.me/submissions/bab647d9-75f2-47e9-9d84-98a323663681

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealContinuousEmbeddingInfiniteAdeles

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdelicRealLine
namespace GlobalTheory.CompanionTheory.AdelicRealLine
theorem _root_.solution {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  rw [h0, dist_zero_right, dist_zero_right] at h
  rw [← h, Real.norm_eq_abs]
  rfl
end GlobalTheory.CompanionTheory.AdelicRealLine
