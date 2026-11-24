-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AffAcyc.common_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:29:08.513714+00:00
-- url     : https://prove2.me/submissions/56696fc8-145e-4b5f-bce6-fcd7d954e61f

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
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]
namespace GlobalTheory.CompanionTheory.AffAcyc
theorem _root_.solution {J : Type} [Finite J] (p : J → ℕ → Prop) (hp : ∀ i, ∃ N, ∀ M, N ≤ M → p i M) :
    ∃ N, ∀ i, p i N := by
  choose N hN using hp
  obtain ⟨B, hB⟩ := (Set.finite_range N).bddAbove
  exact ⟨B, fun i ↦ hN i B (hB ⟨i, rfl⟩)⟩
end GlobalTheory.CompanionTheory.AffAcyc
