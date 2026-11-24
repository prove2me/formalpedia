-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.uf_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:58.824811+00:00
-- url     : https://prove2.me/submissions/7e048737-2702-42f3-b59c-cf3b071aa4e2

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_AffAcyc_res_bij

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AffAcyc
variable {R : Type} [CommRing R] {X : Scheme.{0}} {P : Type} [SemilatticeInf P]
variable (s : X ⟶ Sp R) (W : X.affineOpens) (u : P →o X.affineOpens) (hle : ∀ a, (u a).1 ≤ W.1)
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution (hinf : ∀ a b, (u (a ⊓ b)).1 = (u a).1 ⊓ (u b).1) (f : Γ(X, W.1)) (a₀ : P)
    (hf : X.basicOpen f ≤ (u a₀).1) (T : Pᵒᵖ) :
    Function.Bijective (mp (FF s (uf s W u hle f)) ((th a₀).app T)) := by
  refine res_bij s _ ?_
  change X.basicOpen _ = X.basicOpen _
  rw [basicOpen_rf, basicOpen_rf]
  change _ = (u (T.unop ⊓ a₀)).1 ⊓ _
  rw [hinf, inf_assoc, inf_eq_right.2 hf]
  rfl
end GlobalTheory.CompanionTheory.AffAcyc
