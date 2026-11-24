-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.acyc_member
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:28.507743+00:00
-- url     : https://prove2.me/submissions/55fa4b08-faa2-4a1b-abe2-4f398ad2d554

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsFiniteCover
import Theorems.Thm_GlobalTheory_CompanionTheory_Descent_acyc_of_cone

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
theorem _root_.solution (hCx : CxSt) (hHt : HtpySt) (hA : AffAcycSt) {L : Type} [SemilatticeInf L]
    (f : Lᵒᵖ ⥤ AffOp X) (W : X.affineOpens) (hle) (t : L) (ht : W.1 ≤ (f.obj (op t)).unop.1)
    (he : ∀ a, (f.obj (op a)).unop.1 ≤ (f.obj (op (a ⊓ t))).unop.1) : Acyc s f W.1 hle :=
  acyc_of_cone s hCx hHt hA f W hle (op t) ht
    (Monotone.functor (f := fun a : L ↦ a ⊓ t) fun _ _ h ↦ inf_le_inf_right t h).op
    (fun T ↦ (homOfLE inf_le_left).op) (fun T ↦ (homOfLE inf_le_right).op) (fun T ↦ he T.unop)
end GlobalTheory.CompanionTheory.Descent
