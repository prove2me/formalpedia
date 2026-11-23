-- Prove2me | solution 1 for GlobalTheory.HeckeCompare.IsAct.nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:46.141701+00:00
-- url     : https://prove2.me/submissions/42f81f40-39bc-4ad4-846c-bba2ac753980

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NatCastMemConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HeckeCompare
variable {O Q : Type} [CommRing O] [CommGroup Q] {ρ : O → Q →* Q}
namespace GlobalTheory.HeckeCompare
namespace IsAct
theorem _root_.solution (h : IsAct ρ) (n : ℕ) (x : Q) : ρ n x = x ^ n := by
  induction n with
  | zero =>
    have := h.2.2 0 0 x
    rw [add_zero] at this
    rw [Nat.cast_zero, pow_zero, left_eq_mul.1 this]
  | succ n ih => rw [Nat.cast_succ, h.2.2, ih, h.1, pow_succ]
end IsAct
end GlobalTheory.HeckeCompare
