-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.pull_rm_rm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:04.326398+00:00
-- url     : https://prove2.me/submissions/f421e516-07f9-457c-85ff-4ea28d34770b

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
theorem _root_.solution (f : C ⥤ AffOp X) (g : D ⥤ AffOp X) (k : E ⥤ AffOp X) (σ : D ⥤ C) (τ : E ⥤ D) (h h')
    (h'' : ∀ T, (k.obj T).unop.1 ≤ (f.obj ((τ ⋙ σ).obj T)).unop.1) (i : ℕ) (z : Cn (f ⋙ OAff s) i) :
    pulln (rm s g k τ h') i (pulln (rm s f g σ h) i z) = pulln (rm s f k (τ ⋙ σ) h'') i z := by
  funext c
  exact (Sec.res_res s (h _) (h' _) _).symm
end GlobalTheory.CompanionTheory.Descent
