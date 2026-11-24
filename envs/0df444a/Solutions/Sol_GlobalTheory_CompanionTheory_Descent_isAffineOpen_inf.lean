-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.isAffineOpen_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:14.506054+00:00
-- url     : https://prove2.me/submissions/24ac27ac-be67-4420-be8a-d323d8552f84

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
namespace GlobalTheory.CompanionTheory.Descent
theorem _root_.solution (hs : IsSeparated s) (U V : X.affineOpens) : IsAffineOpen (U.1 ⊓ V.1) := by
  haveI : X.IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from s]
    infer_instance⟩
  exact U.2.inf V.2
end GlobalTheory.CompanionTheory.Descent
