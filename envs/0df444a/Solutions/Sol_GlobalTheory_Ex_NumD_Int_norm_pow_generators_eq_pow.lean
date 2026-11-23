-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.norm_pow_generators_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:11.881642+00:00
-- url     : https://prove2.me/submissions/c8d4b634-460a-4a6e-a3f9-6693b85c50d8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_cubN
import Theorems.Thm_GlobalTheory_Ex_NumD_Gt_pow_s


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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
namespace GlobalTheory.Ex.NumD.Int
theorem _root_.solution (h : N.Int q) (g : N.Gt) (k : ℕ) (χ : N.X) :
    ‖((g ^ k).s χ : C)‖ = ‖(g.s χ : C)‖ ^ k := by
  have := congrArg (fun u : Cˣ => ‖(u : C)‖) (g.pow_s k χ)
  simpa only [Units.val_mul, norm_mul, h.norm_cubN, mul_one, Units.val_pow_eq_pow_val, norm_pow] using this
end GlobalTheory.Ex.NumD.Int
