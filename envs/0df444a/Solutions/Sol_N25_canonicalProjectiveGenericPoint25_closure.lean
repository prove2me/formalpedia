-- Prove2me | solution 1 for N25.canonicalProjectiveGenericPoint25_closure
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:38.227494+00:00
-- url     : https://prove2.me/submissions/ac5e3829-60ac-41b0-8f64-ae31f2214176

import Mathlib
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
import Theorems.Thm_N25_canonicalConeToTower25_coordinate
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Definitions.Def_N25_CanonicalConeTower
import Definitions.Def_N25_CanonicalConeBoundary
import Definitions.Def_N25_CanonicalConeTowerEquiv
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_canonicalAChartToTower25_coordinate
import Definitions.Def_N25_CanonicalAChartTowerEquiv
import Mathlib.AlgebraicGeometry.Properties
import Definitions.Def_N25_CanonicalProjectiveGenericPoint

/-! Reducedness and irreducibility of the literal Proj from its homogeneous cone. -/

noncomputable section

universe u

namespace N25

open AlgebraicGeometry HomogeneousLocalization

variable (K : Type u) [Field K]

/-- The generic point specializes to every point of the literal projective spectrum. -/
theorem _root_.solution [IsDomain (CanonicalConeRing25 K)]
    (ha : canonicalConeA25 K ≠ 0) :
    closure ({canonicalProjectiveGenericPoint25 K ha} : Set (ProjectiveSpectrum (canonicalConePiece25 K))) =
      Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure (canonicalConePiece25 K) _ x).mp
  change (⊥ : HomogeneousIdeal (canonicalConePiece25 K)) ≤ x.asHomogeneousIdeal
  exact bot_le

end N25
