-- Prove2me | solution 1 for GlobalTheory.Ex.WpPairing.s_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:49.80084+00:00
-- url     : https://prove2.me/submissions/a2ae7e8b-aace-4264-9d10-08d0ac087677

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingProperties
import Theorems.Thm_GlobalTheory_Ex_NumD_c_nsmul


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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.WpPairing
variable {O : Type} [CommRing O] (N : NumD O)
open scoped BigOperators
variable {O : Type} [CommRing O] (N : _root_.GlobalTheory.Ex.NumD O)
namespace GlobalTheory.Ex.WpPairing
namespace _root_.GlobalTheory.Ex.WpPairing
theorem _root_.solution (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, _root_.GlobalTheory.Ex.NumD.Gt.s_zero]
  | succ n ih =>
    have hm := g.mult (n • y) y
    rw [succ_nsmul, pow_succ, ← ih]
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.cubN, Finset.prod_range_succ, one_mul]
    rw [← N.c_nsmul, ← mul_assoc, mul_right_comm, hm]
    exact mul_right_comm _ _ _
end _root_.GlobalTheory.Ex.WpPairing
end GlobalTheory.Ex.WpPairing
