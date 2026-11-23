-- Prove2me | solution 1 for GlobalTheory.PsiQuadratic.s_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:38:24.898232+00:00
-- url     : https://prove2.me/submissions/51be1230-76dc-449c-af88-dfad9e093bdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinear
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
open GlobalTheory GlobalTheory.PsiQuadratic
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.PsiQuadratic
theorem _root_.solution (g : N.Gt) (n : ℕ) (y : N.X) : g.s (n • y) * cubN N.θ n 1 (N.c y) g.b = g.s y ^ n := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    have m := g.mult (n • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [succ_nsmul, cubN, Finset.prod_range_succ, one_mul, pow_succ, ← ih, mul_right_comm _ _ (g.s y), ← m,
      ← mul_assoc, mul_right_comm]
end GlobalTheory.PsiQuadratic
