-- Prove2me | solution 1 for N25.canonicalConeBoundaryMap25_Z_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:04.075007+00:00
-- url     : https://prove2.me/submissions/8674948a-4139-42b0-beed-dcfdfa6108f5

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

/-! Regularity of the normalizing linear form in the monic cone presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

theorem _root_.solution :
    canonicalConeBoundaryMap25 K (canonicalConeBaseZ25 K) ≠ 0 := by
  intro h
  have hd := (Ideal.Quotient.eq_zero_iff_dvd (canonicalConeBaseA25 K) (canonicalConeBaseZ25 K)).mp h
  have he := Polynomial.X_dvd_iff.mp hd
  simpa [canonicalConeBaseZ25] using he

end N25
