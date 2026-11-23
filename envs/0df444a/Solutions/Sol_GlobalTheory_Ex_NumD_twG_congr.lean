-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.twG_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:17.704928+00:00
-- url     : https://prove2.me/submissions/fd9a5033-f9c2-4025-90ee-1e012d4ec7ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TwistTerms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.NumD
theorem _root_.solution {k : ℕ} (β : N.Form k) (u : Oˣ) (g : N.Gt) (l l' : N.X → ℤ) (hl : ∀ a b, l (a + b) = l a + l b)
    (hl' : ∀ a b, l' (a + b) = l' a + l' b) (h : ∀ z, l z = l' z) : N.twG β u g l hl = N.twG β u g l' hl' := by
  obtain rfl : l = l' := funext h
  rfl
end GlobalTheory.Ex.NumD
