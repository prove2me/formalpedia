-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.norm_vt_QT_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:32.054993+00:00
-- url     : https://prove2.me/submissions/eafa26c9-31a3-43dc-a35d-f55e5d8ee1b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
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
theorem _root_.solution (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) (χ : N.X) :
    ‖N.vt p.1.2 χ‖ ≤ Real.exp (-((q (p.1.1.toAdd + k • χ) - q p.1.1.toAdd) / (k : ℝ) ^ 2)) := by
  rw [NumD.vt]
  simp only [Units.val_mul, norm_mul, h.ψ, h.norm_rep_generators_eq_exp p hk]
  refine (mul_le_of_le_one_right (by positivity) (h.th _)).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  have e : q (p.1.1.toAdd + k • χ) =
      q p.1.1.toAdd + (k : ℝ) ^ 2 * q χ + k * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (k • χ) = k * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (k • χ) = (k : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  rw [e]
  field_simp
  ring
end GlobalTheory.Ex.NumD.Int
