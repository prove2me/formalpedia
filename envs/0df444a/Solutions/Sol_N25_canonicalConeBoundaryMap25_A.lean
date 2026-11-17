-- Prove2me | solution 1 for N25.canonicalConeBoundaryMap25_A
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:02.5944+00:00
-- url     : https://prove2.me/submissions/662f7e4b-1c1a-4e51-9efb-a6b2a48ba31e

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

/-! Regularity of the normalizing linear form in the monic cone presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

theorem _root_.solution :
    canonicalConeBoundaryMap25 K (canonicalConeBaseA25 K) = 0 :=
  Ideal.Quotient.mk_singleton_self _

end N25
