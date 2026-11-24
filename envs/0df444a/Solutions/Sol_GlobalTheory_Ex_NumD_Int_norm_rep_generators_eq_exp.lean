-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.norm_rep_generators_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:44.570377+00:00
-- url     : https://prove2.me/submissions/0f808f62-0fb5-4998-ad3b-2d0265ad92ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Theorems.Thm_P2M_GlobalTheory_Ex_NumD_Int_norm___8f2d6a954aa8
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_pow_generators_eq_pow

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
theorem _root_.solution (h : N.Int q) {k : ℕ} (p : N.QT k) (hk : k ≠ 0) (χ : N.X) :
    ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k)) := by
  have e := h.norm_pow_generators_eq_pow p.1.2 k χ
  rw [N.mem_QT.1 p.2, NumD.io_s, h.norm_τ] at e
  refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le hk).1 ?_
  rw [← e, ← Real.exp_nat_mul]
  congr 1
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp
end GlobalTheory.Ex.NumD.Int
