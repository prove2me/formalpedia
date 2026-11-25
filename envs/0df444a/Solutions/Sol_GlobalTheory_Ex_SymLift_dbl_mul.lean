-- Prove2me | solution 1 for GlobalTheory.Ex.SymLift.dbl_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:32:09.191986+00:00
-- url     : https://prove2.me/submissions/2e890b7e-1df2-4d66-bd50-f54a1016bea0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationWeilPairingPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormalisingFactor
import Theorems.Thm_GlobalTheory_T_mulq_dbl_cubN_relations


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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.SymLift
variable {O : Type} [CommRing O] (N : NumD O)
namespace GlobalTheory.Ex.SymLift
theorem _root_.solution (x y : N.A) :
    dbl N.θ N.σ (x * y) * (N.θ (x * y) x y * N.θ x x y * N.θ y x y) = dbl N.θ N.σ x * dbl N.θ N.σ y := by
  have a := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB 2 0 x y).2.1
  have c := N.cub.coc x y y x
  rw [N.cub.s12 (x * y), N.cub.s12 x y x, N.cub.s12 x (y * y), N.cub.s12 y y x] at c
  simp only [mulq, cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, one_mul, mul_one,
    N.cub.face, div_one, sq] at a
  rw [N.cub.s12 y y x] at a
  replace a := congrArg Additive.ofMul a
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_one] at a c ⊢
  linear_combination (norm := abel) c - a
end GlobalTheory.Ex.SymLift
