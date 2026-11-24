-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.norm_txT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:03.155818+00:00
-- url     : https://prove2.me/submissions/2f0fcd86-19f6-438d-8b4d-0983c21963a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_mulq
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_pow_generators_eq_pow
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_rep_generators_eq_exp
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_wQ

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
theorem _root_.solution (h : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [NumD.txT, NumD.vt]
  simp only [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, h.norm_mulq, h.ψ,
    h.norm_wQ hm.pow, h.norm_pow_generators_eq_pow, h.norm_rep_generators_eq_exp p (pow_ne_zero 2 hm0), div_one, NumD.Gt.pow_b]
  rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have e : q (p.1.1.toAdd + m • χ) =
      q p.1.1.toAdd + (m : ℝ) ^ 2 * q χ + m * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (m • χ) = m * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (m • χ) = (m : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0
  rw [e]
  push_cast
  field_simp
  ring
end GlobalTheory.Ex.NumD.Int
