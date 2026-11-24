-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.acyc_pt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:38:12.053662+00:00
-- url     : https://prove2.me/submissions/21406b68-6d32-498a-81a0-ce76b0686947

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_fin

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
theorem _root_.solution (hA : AffAcycSt) (W : X.affineOpens) :
    Acyc s (pt W) W.1 (fun _ ↦ le_rfl) :=
  acyc_fin s hA (v₀ W) W (fun _ ↦ le_rfl) (fun _ _ ↦ (inf_idem _).symm)
    (le_antisymm (iSup_le fun _ ↦ le_rfl) (le_iSup (fun a ↦ (v₀ W a).1) 0))
end GlobalTheory.CompanionTheory.Descent
