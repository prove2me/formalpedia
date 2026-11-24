-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.pullbackZeroCochains_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:04.857441+00:00
-- url     : https://prove2.me/submissions/cc7bc62d-7807-4a89-8a98-bb14beca94d0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution (m : CoefMap (RingHom.id R) F F') (r : R) :
    pullbackZeroCochains m (algebraMap R (C0 F) r) = algebraMap R (C0 F') r := by
  funext T
  change m.α T (algebraMap R _ r) = algebraMap R _ r
  rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, Algebra.algebraMap_eq_smul_one]
  rfl
end GlobalTheory.CompanionTheory.HodgeLow
