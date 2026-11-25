-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs.DetCond.swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:39.378324+00:00
-- url     : https://prove2.me/submissions/986a0969-6381-425c-89f4-e003190291ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
variable {S : Scheme.{0}} {k : Type} [Field k]
variable (G : Over S) [GrpObj G]
variable {G}
variable {O : Type} [CommRing O]
variable [IsCommMonObj G]
namespace GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs
namespace DetCond
theorem _root_.solution [IsAlgClosed k] [CharZero k] {ρ : OAct O G} {t : Spec (CommRingCat.of k) ⟶ S}
    {s : O} {δ : k} {p q : ℕ} (h : DetCond ρ t s δ p q) : DetCond ρ t s (-δ) q p := by
  obtain ⟨⟨d, hd, hs, hδ⟩, Ψ, Ψ', h1, h2, h3⟩ := h
  refine ⟨⟨d, hd, hs, by simpa using hδ⟩, Ψ', Ψ, h2, by simpa using h1, ?_⟩
  simpa only [mul_comm] using h3
end DetCond
end GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs
