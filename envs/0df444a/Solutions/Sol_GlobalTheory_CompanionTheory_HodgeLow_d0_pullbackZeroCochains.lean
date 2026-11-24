-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.d0_pullbackZeroCochains
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:02.271804+00:00
-- url     : https://prove2.me/submissions/81bf59d2-827c-44d1-91f2-302d42c0ab96

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap

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
theorem _root_.solution (m : CoefMap (RingHom.id R) F F') (g : C0 F) :
    d0 F' (pullbackZeroCochains m g) = pullbackOneCochains m (d0 F g) := by
  funext T T' φ
  change m.α T' (g _) - mp F' φ (m.α T (g _)) = m.α T' (g _ - mp F (m.G.map φ) (g _))
  rw [map_sub, m.naturality]
end GlobalTheory.CompanionTheory.HodgeLow
