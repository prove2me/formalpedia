-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.d_aug
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:51:34.649906+00:00
-- url     : https://prove2.me/submissions/8517bf53-8743-4927-8031-848748692add

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_d
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_pt
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_pull_aug

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
theorem _root_.solution (hCx : CxSt) (hA : AffAcycSt) (f : E ⥤ AffOp X) (W : X.affineOpens) (hle) (w : Sec s W.1) :
    dn (f ⋙ OAff s) 0 (aug s f W.1 hle w) = 0 := by
  have k := pull_aug s (pt W) f ((Functor.const E).obj (op (0 : Fin 1))) hle W.1 (fun _ ↦ le_rfl) hle w
  have z := ((acyc_pt s hA W).2.1 (aug s (pt W) W.1 (fun _ ↦ le_rfl) w)).2 ⟨w, rfl⟩
  rw [← k, ← pull_d hCx, z, map_zero]
end GlobalTheory.CompanionTheory.Descent
