-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.loc1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:09.497827+00:00
-- url     : https://prove2.me/submissions/d4f8b0c3-0cd2-438a-90b3-7f6c998f1630

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
theorem _root_.solution (f : Γ(X, W.1)) (T : Pᵒᵖ) (y' : (FF s (uf s W u hle f)).obj T) :
    ∃ (N : ℕ) (y : (FF s u).obj T), rho s W u hle f T y =
      rho s W u hle f T (gF s W u hle f T) ^ N * y' := by
  haveI := IsAffineOpen.isLocalization_basicOpen (u T.unop).2 (rf s W u hle f T.unop)
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := Γ(X, X.basicOpen (rf s W u hle f T.unop)))
    (rf s W u hle f T.unop) y'
  exact ⟨n, a, (h.symm.trans (mul_comm _ _))⟩
end GlobalTheory.CompanionTheory.AffAcyc
