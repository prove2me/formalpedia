-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.meet_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:17.733138+00:00
-- url     : https://prove2.me/submissions/f0afd1a0-7d01-4d26-b219-e1647d2237fb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Descent
variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (hi : ∀ U V : X.affineOpens, IsAffineOpen (U.1 ⊓ V.1))
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution {U U' V V' : X.affineOpens} (h : U.1 ≤ U'.1) (h' : V.1 ≤ V'.1) :
    meet hi U V ≤ meet hi U' V' := by
  change U.1 ⊓ V.1 ≤ U'.1 ⊓ V'.1
  exact inf_le_inf h h'
end GlobalTheory.CompanionTheory.Descent
