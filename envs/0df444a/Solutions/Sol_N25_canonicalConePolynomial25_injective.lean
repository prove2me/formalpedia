-- Prove2me | solution 1 for N25.canonicalConePolynomial25_injective
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:45.538241+00:00
-- url     : https://prove2.me/submissions/c6df582d-b808-42a2-a8a1-1b5ad33b25f5

import Definitions.Def_N25_CanonicalProjectiveCharts
import Definitions.Def_N25_CanonicalChartDehomogenization
import Definitions.Def_N25_CanonicalProjectivePrincipalOpen
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_CanonicalOpenChart
import Definitions.Def_N25_UnitPlaneAlgebraOverRing
import Definitions.Def_N25_BirationalIdentities
import Definitions.Def_N25_CanonicalOpenAlgebraOverRing
import Definitions.Def_N25_CanonicalPrincipalOpenChart
import Definitions.Def_N25_CanonicalConePolynomial
import Theorems.Thm_N25_canonicalConeFractionPiece25_injective
import Theorems.Thm_N25_canonicalConeDirectSumPolynomial25_coeff

/-! A graded polynomial representation of the canonical cone, normalized by A. -/

noncomputable section

universe u

namespace N25

open HomogeneousLocalization DirectSum

variable (K : Type u) [Field K]

/-- The polynomial representation is injective whenever A is regular. -/
theorem _root_.solution (ha : IsRegular (canonicalConeA25 K)) :
    Function.Injective (canonicalConePolynomial25 K) := by
  intro x y hxy
  apply (DirectSum.decomposeRingEquiv (canonicalConePiece25 K)).injective
  apply DirectSum.ext
  intro n
  apply canonicalConeFractionPiece25_injective K ha n
  have hc := congrArg (fun p : Polynomial (CanonicalAProjRing25 K) => p.coeff n) hxy
  exact (canonicalConeDirectSumPolynomial25_coeff K _ n).symm.trans
    (hc.trans (canonicalConeDirectSumPolynomial25_coeff K _ n))

end N25
