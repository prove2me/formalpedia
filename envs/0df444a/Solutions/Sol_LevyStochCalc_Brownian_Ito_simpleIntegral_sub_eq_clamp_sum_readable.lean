-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.simpleIntegral_sub_eq_clamp_sum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:12.689557+00:00
-- url     : https://prove2.me/submissions/4ab3f827-f687-40be-a8c8-20235c1ab22f

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionCompensator

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionCompensator.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **Clamped-increment identity.** For `s ≤ t`,
`simpleIntegral W H t − simpleIntegral W H s = ∑ᵢ ξᵢ·(W_{cᵢ₊₁} − W_{cᵢ})` where
`cᵢ = max s (min pᵢ t)` clamps the partition points into `[s, t]`. The increment
of the simple integral between `s` and `t` rebuilds as a single sum of increments
over the `[s,t]`-clamped partition — the starting point for the conditional
(set-level) Itô isometry. -/
lemma solution
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : LevyStochCalc.Brownian.Ito.SimplePredictable Ω T) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    LevyStochCalc.Brownian.Ito.simpleIntegral W H t ω - LevyStochCalc.Brownian.Ito.simpleIntegral W H s ω
      = ∑ i : Fin H.N, H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
          - W.W (max s (min (H.partition i.castSucc) t)) ω) := by
  have key : ∀ p : ℝ,
      W.W (min p t) ω - W.W (min p s) ω = W.W (max s (min p t)) ω - W.W s ω := by
    intro p
    rcases le_or_gt s p with hsp | hps
    · rw [min_eq_right hsp, max_eq_right (le_min hsp hst)]
    · rw [min_eq_left (le_of_lt hps), min_eq_left (le_of_lt (lt_of_lt_of_le hps hst)),
        max_eq_left (le_of_lt hps), sub_self, sub_self]
  unfold LevyStochCalc.Brownian.Ito.simpleIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 := key (H.partition i.succ)
  have e2 := key (H.partition i.castSucc)
  rw [← mul_sub]
  congr 1
  rw [show W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω
        - (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω)
      = (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.succ) s) ω)
        - (W.W (min (H.partition i.castSucc) t) ω
            - W.W (min (H.partition i.castSucc) s) ω) from by ring]
  rw [e1, e2]; ring
