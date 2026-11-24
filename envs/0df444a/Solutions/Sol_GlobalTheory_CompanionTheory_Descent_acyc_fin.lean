-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Descent.acyc_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:10.157799+00:00
-- url     : https://prove2.me/submissions/8a850c86-7384-4dfd-8b6e-bec83dd5a439

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
theorem _root_.solution (hA : AffAcycSt) {Q : Type} [SemilatticeInf Q] [Finite Q] (v : Q →o X.affineOpens)
    (W : X.affineOpens) (hle : ∀ a, (v a).1 ≤ W.1) (hinf : ∀ a b, (v (a ⊓ b)).1 = (v a).1 ⊓ (v b).1)
    (hcov : ⨆ a, (v a).1 = W.1) : Acyc s v.monotone.functor.op W.1 (fun T ↦ hle T.unop) := by
  have k := hA R X s W Q v hle hinf hcov
  exact k
end GlobalTheory.CompanionTheory.Descent
