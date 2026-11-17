-- Prove2me | solution 1 for N25.canonicalProjectiveCurve25_isReduced_of_coneDomain
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:07.921205+00:00
-- url     : https://prove2.me/submissions/16ce2c19-9ced-492d-a19f-ca6451233d7c

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

/-- Localizing a reduced cone and passing to degree zero preserves reducedness. -/
theorem _root_.solution [IsDomain (CanonicalConeRing25 K)] :
    AlgebraicGeometry.IsReduced (CanonicalProjectiveCurve25 K) := by
  let U := (Proj.affineOpenCover (canonicalConePiece25 K)).openCover
  haveI (i : U.I₀) : AlgebraicGeometry.IsReduced (U.X i) := by
    change AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (Away (canonicalConePiece25 K) (i.2 : CanonicalConeRing25 K))))
    letI : _root_.IsReduced (Away (canonicalConePiece25 K) (i.2 : CanonicalConeRing25 K)) :=
      isReduced_of_injective
        (algebraMap (Away (canonicalConePiece25 K) (i.2 : CanonicalConeRing25 K))
          (Localization.Away (i.2 : CanonicalConeRing25 K))) (HomogeneousLocalization.val_injective _)
    infer_instance
  exact AlgebraicGeometry.IsReduced.of_openCover (CanonicalProjectiveCurve25 K) U

end N25
