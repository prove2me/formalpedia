-- Prove2me | solution 1 for Intersectionality.Generic.lemma_1_a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:43:41.689001+00:00
-- url     : https://prove2.me/submissions/358f1e49-3a43-46d7-aca6-2f19c6eae77f

import Mathlib
import Definitions.Def_Intersectionality_Generic_Setting

set_option autoImplicit false
open Intersectionality.Generic

theorem solution (X : Set ℝ) (hX : X.OrdConnected) [Nonempty ↥X] (Q : Set (↥X → ↥X))
    (hQ : IsPolicyFamily Q) : ∀ q ∈ Q, Continuous q := by
  intro q hq
  haveI : X.OrdConnected := hX
  exact (StrictMono.orderIsoOfSurjective q (hQ.strictMono q hq)
    (hQ.bijective q hq).2).continuous
