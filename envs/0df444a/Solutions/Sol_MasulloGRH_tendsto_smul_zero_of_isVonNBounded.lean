-- Prove2me | solution 1 for MasulloGRH.tendsto_smul_zero_of_isVonNBounded
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:28:14.689247+00:00
-- url     : https://prove2.me/submissions/c4be8f64-14e6-4d8f-ac05-1dbdf20e31e2

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hL : IsHLCS G)
    (w : ℕ → G) (hw : Bornology.IsVonNBounded ℂ (Set.range w))
    (r : ℕ → ℂ) (hr : Filter.Tendsto r Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => r n • w n) Filter.atTop (nhds (0 : G)) :=
  hw.smul_tendsto_zero (Filter.Eventually.of_forall fun n => Set.mem_range_self n) hr
