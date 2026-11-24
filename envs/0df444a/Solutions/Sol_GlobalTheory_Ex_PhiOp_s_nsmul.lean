-- Prove2me | solution 1 for GlobalTheory.Ex.PhiOp.s_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:40.118632+00:00
-- url     : https://prove2.me/submissions/2cefc111-d01c-4626-aa76-89f8dd107a74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FeOfPhiTriv
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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.PhiOp
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.PhiOp
theorem _root_.solution (g : N.Gt) (k : ℕ) (y : N.X) : g.s (k • y) * cubN N.θ k 1 (N.c y) g.b = g.s y ^ k := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have m := g.mult (k • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, one_mul, succ_nsmul, pow_succ, ← ih, ← mul_assoc, mul_right_comm, m,
      mul_right_comm]
end GlobalTheory.Ex.PhiOp
