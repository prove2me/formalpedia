-- Prove2me | solution 1 for N25.canonicalConeQuadricPolynomial25_monic
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:04.769845+00:00
-- url     : https://prove2.me/submissions/264d2fe7-5c12-4fbf-a5bb-9e943538cc82

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary

/-! Regularity of the normalizing linear form in the monic cone presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

theorem _root_.solution : (canonicalConeQuadricPolynomial25 K).Monic := by
  let a := canonicalConeBaseA25 K
  let x := canonicalConeBaseX25 K
  let z := canonicalConeBaseZ25 K
  have h : degree (C (2*z-x)*X+C (z^2-2*x*z+a*(x-z))) < 2 := by compute_degree; norm_num
  convert monic_X_pow_add h using 1
  unfold canonicalConeQuadricPolynomial25
  dsimp [a,x,z]
  ring

end N25
