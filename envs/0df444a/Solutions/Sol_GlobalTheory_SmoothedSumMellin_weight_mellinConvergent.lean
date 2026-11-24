-- Prove2me | solution 1 for GlobalTheory.SmoothedSumMellin.weight_mellinConvergent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:39.272671+00:00
-- url     : https://prove2.me/submissions/90c7c231-6593-437f-9f59-58d3855f9fda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEntireMellinSmoothedDirichletSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open Set Filter Asymptotics Topology
open GlobalTheory GlobalTheory.SmoothedSumMellin
namespace GlobalTheory.SmoothedSumMellin
theorem _root_.solution {wt : ℝ → ℂ} (hc : Continuous wt) {a b : ℝ} (ha : 0 < a)
    (hs : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) (s : ℂ) : MellinConvergent wt s := by
  have hev0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), wt t = 0 := by
    filter_upwards [Ioo_mem_nhdsGT ha] with t ht
    by_contra h
    exact absurd (hs t h).1 (not_le.2 ht.2)
  have hevT : ∀ᶠ t in atTop, wt t = 0 := by
    filter_upwards [eventually_gt_atTop b] with t ht
    by_contra h
    exact absurd (hs t h).2 (not_le.2 ht)
  exact mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    (hc.locallyIntegrable.locallyIntegrableOn _)
    ((Asymptotics.isBigO_zero _ _).congr' (hevT.mono fun t ht => ht.symm) EventuallyEq.rfl)
    (by linarith)
    ((Asymptotics.isBigO_zero _ _).congr' (hev0.mono fun t ht => ht.symm) EventuallyEq.rfl)
    (by linarith)
end GlobalTheory.SmoothedSumMellin
