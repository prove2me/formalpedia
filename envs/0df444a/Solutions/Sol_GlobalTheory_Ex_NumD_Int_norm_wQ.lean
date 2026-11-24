-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.norm_wQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:33.647029+00:00
-- url     : https://prove2.me/submissions/be1270b4-edd5-4805-a8af-dcdaf6ac9653

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_cubN
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_dbl
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_mulq
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_rep_generators_eq_exp

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
theorem _root_.solution (h : N.Int q) {k : ℕ} (hk : Odd k) (p : N.QT k) :
    ‖(N.wQ p : C)‖ = Real.exp (-(q p.1.1.toAdd / k)) := by
  have hk0 : k ≠ 0 := hk.pos.ne'
  rw [NumD.wQ, NumB.wS]
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, norm_div, norm_mul, norm_pow,
    h.norm_cubN, h.norm_dbl, h.norm_mulq, h.ψ, h.norm_rep_generators_eq_exp p hk0, mul_one, one_pow, div_one]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, QuadraticMap.polar_self]
  congr 1
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  have : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  rw [e, two_smul]
  field_simp
  push_cast
  ring
end GlobalTheory.Ex.NumD.Int
