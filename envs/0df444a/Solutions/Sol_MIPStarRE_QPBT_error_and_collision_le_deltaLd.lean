-- Prove2me | solution 1 for MIPStarRE.QPBT.error_and_collision_le_deltaLd
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.827557+00:00
-- url     : https://prove2.me/submissions/177d188e-ab02-4d23-9629-ca2685c180ab

-- Generated proof for MIPStarRE.QPBT.error_and_collision_le_deltaLd.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Error absorption for seed compression

The recovery of global polynomial consistency after seed compression costs a
square root of the direct soundness error. Halving its exponent preserves the
error function of blueprint `lem:ld-soundness`.

## References

* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
-/



open MIPStarRE.QPBT

theorem solution (D : _root_.MIPStarRE.QPBT.DirectLdParams) {a b ε : ℝ}
    (ha : 1 ≤ a) (hb : b ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k ∧
      (D.m : ℝ) * D.d / D.q ≤ _root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k := by
  let N : ℝ := (D.d * D.m * D.k : ℕ)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ D.d * D.m * D.k from
      Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hNa : N ≤ N ^ a := by
    simpa using Real.rpow_le_rpow_of_exponent_le hN ha
  have hP : N ≤ a * N ^ a := hNa.trans
    (le_mul_of_one_le_left (by positivity) ha)
  have hmd : (D.m : ℝ) * D.d ≤ N := by
    dsimp [N]
    push_cast
    nlinarith [le_mul_of_one_le_right (by positivity : 0 ≤ (D.d : ℝ) * D.m)
      (show (1 : ℝ) ≤ D.k by exact_mod_cast D.hk)]
  have he : ε ≤ ε ^ b := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 hb
  have hq1 : (1 : ℝ) ≤ D.q := by exact_mod_cast D.toLDTParameters.hq
  have hq : (D.q : ℝ)⁻¹ ≤ (D.q : ℝ) ^ (-b) := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg hb)
  have hx : 0 ≤ (ε ^ b : ℝ) := Real.rpow_nonneg hε.le _
  have hy : 0 ≤ ((D.q : ℝ) ^ (-b)) := Real.rpow_nonneg (by positivity) _
  have hz : 0 ≤ (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ))) :=
    Real.rpow_nonneg (by norm_num) _
  unfold _root_.MIPStarRE.QPBT.deltaLd
  simp only [Real.rpow_eq_pow]
  change ε ≤ a * N ^ a * _ ∧ (D.m : ℝ) * D.d / D.q ≤ a * N ^ a * _
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr (hN.trans hP)) hx,
      mul_nonneg (by linarith : 0 ≤ a * N ^ a) (add_nonneg hy hz)]
  · have hprod := mul_le_mul (hmd.trans hP) hq (by positivity)
      (by linarith : 0 ≤ a * N ^ a)
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (by linarith : 0 ≤ a * N ^ a) (add_nonneg hx hz)]
