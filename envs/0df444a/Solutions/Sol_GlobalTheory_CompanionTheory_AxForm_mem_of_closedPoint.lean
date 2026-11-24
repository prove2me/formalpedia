-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.mem_of_closedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:25:56.780042+00:00
-- url     : https://prove2.me/submissions/c1741198-abf2-4956-b2f4-e781e8aba8f7

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ModuleHomCompSquareZeroSection

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
open KaehlerDifferential
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AxForm
variable {R : Type} [CommRing R] {X : Scheme.{0}}
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution {B : Type} [CommRing B] [IsLocalRing B] (w : Sp B ⟶ X) (W : X.Opens)
    (h : w (IsLocalRing.closedPoint B) ∈ W) (z : Sp B) : w z ∈ W := by
  have hz : (z : PrimeSpectrum B) ⤳ IsLocalRing.closedPoint B :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (PrimeSpectrum.asIdeal_le_asIdeal _ _ |>.1 (IsLocalRing.le_maximalIdeal z.isPrime.ne_top))
  exact (hz.map w.continuous).mem_open W.isOpen h
end GlobalTheory.CompanionTheory.AxForm
