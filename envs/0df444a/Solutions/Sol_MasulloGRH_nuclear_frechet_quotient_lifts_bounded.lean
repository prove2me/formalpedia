-- Prove2me | solution 1 for MasulloGRH.nuclear_frechet_quotient_lifts_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:57:53.107236+00:00
-- url     : https://prove2.me/submissions/1153288c-adc3-46ab-a342-164eff256626

import Theorems.Thm_MasulloGRH_nuclear_frechet_quotient_bounded_totallyBounded
import Theorems.Thm_MasulloGRH_frechet_quotient_lifts_totallyBounded

open MasulloGRH

theorem solution (X : Type*) [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (hF : IsFrechet X) (hN : IsNuclear X) (W : Submodule ℂ X)
    (hW : IsClosed (W : Set X)) : LiftsBoundedSets (W.mkQ : X → X ⧸ W) := by
  intro B hB
  exact frechet_quotient_lifts_totallyBounded X hF W hW B
    (nuclear_frechet_quotient_bounded_totallyBounded X hF hN W hW B hB)
