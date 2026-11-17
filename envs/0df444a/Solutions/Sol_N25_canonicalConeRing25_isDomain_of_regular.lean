-- Prove2me | solution 1 for N25.canonicalConeRing25_isDomain_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:46.33889+00:00
-- url     : https://prove2.me/submissions/a6944700-ebd5-4fbb-aa40-762fce097ea5

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
import Theorems.Thm_N25_canonicalConePolynomial25_injective

/-! A graded polynomial representation of the canonical cone, normalized by A. -/

noncomputable section

universe u

namespace N25

open HomogeneousLocalization DirectSum

variable (K : Type u) [Field K]

/-- A regular degree-one normalizer and a domain A-chart imply a domain cone. -/
theorem _root_.solution
    (ha : IsRegular (canonicalConeA25 K)) [IsDomain (CanonicalAProjRing25 K)] :
    IsDomain (CanonicalConeRing25 K) :=
  Function.Injective.isDomain (canonicalConePolynomial25 K) (canonicalConePolynomial25_injective K ha)

end N25
