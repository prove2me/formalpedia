-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs.IsRootPair.side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:52:44.982909+00:00
-- url     : https://prove2.me/submissions/9e32d63c-0535-4fb0-aa3c-ee0e063302d9

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
namespace IsRootPair
theorem _root_.solution [CharZero k] {s : O} {δ : k} (h : IsRootPair s δ) (τ : O →+* k) :
    Xor' (τ s = δ) (τ s = -δ) := by
  obtain ⟨d, hd, hs, hδ⟩ := h
  have h0 : δ ≠ 0 := by
    rintro rfl
    have : (d : k) = 0 := by simpa using hδ
    exact hd.ne' (by exact_mod_cast this)
  have h1 : (τ s) ^ 2 = δ ^ 2 := by rw [← map_pow, hs, hδ]; simp
  have h2 : δ ≠ -δ := fun h => h0 (by linear_combination h / 2)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exact Or.inl ⟨h, fun h' => h2 (h.symm.trans h')⟩
  · exact Or.inr ⟨h, fun h' => h2 (h'.symm.trans h)⟩
end IsRootPair
end GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs
