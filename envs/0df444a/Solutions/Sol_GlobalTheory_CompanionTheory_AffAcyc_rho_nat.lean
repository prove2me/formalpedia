-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.rho_nat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:12.135716+00:00
-- url     : https://prove2.me/submissions/f96283bb-5f2d-4639-8f3f-167c9ddbda74

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExactOfSpan

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
theorem _root_.solution (f : Γ(X, W.1)) {T T' : Pᵒᵖ} (φ : T ⟶ T') (b : (FF s u).obj T) :
    rho s W u hle f T' (mp (FF s u) φ b) = mp (FF s (uf s W u hle f)) φ (rho s W u hle f T b) :=
  (Sec.res_res _ _ _ b).symm.trans (Sec.res_res _ _ _ b)
end GlobalTheory.CompanionTheory.AffAcyc
