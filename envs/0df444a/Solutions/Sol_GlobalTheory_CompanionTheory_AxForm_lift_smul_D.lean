-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AxForm.lift_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:26:09.02149+00:00
-- url     : https://prove2.me/submissions/0d2d9fc4-2c56-4552-ae18-2b9fc61322a2

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
variable {R S S' B M N : Type} [CommRing R] [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S'] [CommRing B]
  [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  [AddCommGroup N] [Module B N] [Module Bᵐᵒᵖ N] [IsCentralScalar B N]
namespace GlobalTheory.CompanionTheory.AxForm
theorem _root_.solution {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (d : Derivation R S M) (a b : S) :
    d.liftKaehlerDifferential (a • D R S b) = a • d b := by
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]
end GlobalTheory.CompanionTheory.AxForm
