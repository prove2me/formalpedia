-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.pull_rm_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:39:00.131739+00:00
-- url     : https://prove2.me/submissions/dfab6b7d-85e3-49b4-98aa-75106395607e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_res_self

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
theorem _root_.solution (f : C ⥤ AffOp X) (h) (i : ℕ) (z : Cn (f ⋙ OAff s) i) :
    pulln (rm s f f (𝟭 C) h) i z = z := by
  funext c
  exact res_self s _ _
end GlobalTheory.CompanionTheory.Descent
