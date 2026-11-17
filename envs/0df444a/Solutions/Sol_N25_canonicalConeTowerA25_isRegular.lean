-- Prove2me | solution 1 for N25.canonicalConeTowerA25_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:33.698955+00:00
-- url     : https://prove2.me/submissions/8e2eaac7-2e1c-4dab-a833-87339b5aad8e

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Theorems.Thm_N25_isRegular_scalar_mod_root_relation
import Definitions.Def_N25_CanonicalConeBoundary
import Theorems.Thm_N25_canonicalConeCubicRemainder25_mod_A_isRegular
import Theorems.Thm_N25_canonicalConeQuadricPolynomial25_monic

/-! Regularity of the normalizing linear form in the monic cone presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- The scalar A stays regular after imposing both canonical equations. -/
theorem _root_.solution :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span ({AdjoinRoot.mk (canonicalConeQuadricPolynomial25 K)
        (canonicalConeCubicRemainder25 K)} : Set (CanonicalConeQuadricRoot25 K)))
      (AdjoinRoot.of (canonicalConeQuadricPolynomial25 K) (canonicalConeBaseA25 K))) :=
  isRegular_scalar_mod_root_relation (canonicalConeQuadricPolynomial25 K)
    (canonicalConeCubicRemainder25 K) (canonicalConeBaseA25 K)
    (canonicalConeQuadricPolynomial25_monic K) X_ne_zero
    (canonicalConeCubicRemainder25_mod_A_isRegular K)

end N25
