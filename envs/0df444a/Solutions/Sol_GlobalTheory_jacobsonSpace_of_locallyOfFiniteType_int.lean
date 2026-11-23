-- Prove2me | solution 1 for GlobalTheory.jacobsonSpace_of_locallyOfFiniteType_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:47.463075+00:00
-- url     : https://prove2.me/submissions/8b6171cd-5c07-4256-9d2c-47411e052983

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X : Scheme.{0}} (π : X ⟶ Sp ℤ)
    [LocallyOfFiniteType π] : JacobsonSpace X := by
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  exact LocallyOfFiniteType.jacobsonSpace π
end GlobalTheory
