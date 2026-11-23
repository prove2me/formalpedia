-- Prove2me | solution 1 for GlobalTheory.KernelNoTorsion.torsion_hom_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:38.055527+00:00
-- url     : https://prove2.me/submissions/04bc4180-385c-4db7-9599-a6f22a4aa351

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KernelNoTorsion
namespace GlobalTheory.KernelNoTorsion
theorem _root_.solution {S : Scheme.{0}} {Y G : Over S} [GrpObj G] {n : ℕ}
    {a b : Y ⟶ torsion G n} (h : a ≫ torsion.ι G n = b ≫ torsion.ι G n) : a = b :=
  pullback.hom_ext h (toUnit_unique _ _)
end GlobalTheory.KernelNoTorsion
