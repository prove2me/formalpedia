-- Prove2me | solution 1 for N25.canonicalConeBoundaryMap25_X_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:03.202851+00:00
-- url     : https://prove2.me/submissions/4c90f817-7300-4154-87b9-35c4c9d4aee5

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

/-! Regularity of the normalizing linear form in the monic cone presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

theorem _root_.solution :
    canonicalConeBoundaryMap25 K (canonicalConeBaseX25 K) ≠ 0 := by
  intro h
  have hd := (Ideal.Quotient.eq_zero_iff_dvd (canonicalConeBaseA25 K) (canonicalConeBaseX25 K)).mp h
  have he := Polynomial.X_dvd_iff.mp hd
  simpa [canonicalConeBaseX25] using he

end N25
