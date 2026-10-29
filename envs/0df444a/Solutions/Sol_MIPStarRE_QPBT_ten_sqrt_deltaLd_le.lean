-- Prove2me | solution 1 for MIPStarRE.QPBT.ten_sqrt_deltaLd_le
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T21:28:22.862409+00:00
-- url     : https://prove2.me/submissions/3417e918-ef1f-4de2-863c-579fbce8dd5d

-- Generated proof for MIPStarRE.QPBT.ten_sqrt_deltaLd_le.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
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
    (ha : 1 ≤ a) (hε : 0 ≤ ε) :
    10 * Real.sqrt (_root_.MIPStarRE.QPBT.deltaLd a b ε D.q D.m D.d D.k) ≤
      _root_.MIPStarRE.QPBT.deltaLd (10 * a) (b / 2) ε D.q D.m D.d D.k := by
  let N : ℝ := (D.d * D.m * D.k : ℕ)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ ((D.d * D.m * D.k : ℕ) : ℝ)
    exact_mod_cast (show 1 ≤ D.d * D.m * D.k from
      Nat.mul_pos (Nat.mul_pos D.hd D.hm) D.hk)
  have hNa : 1 ≤ N ^ a := Real.one_le_rpow hN (by linarith)
  have hP : 1 ≤ a * N ^ a := by nlinarith
  have hP0 : 0 ≤ a * N ^ a := by linarith
  have hsP : Real.sqrt (a * N ^ a) ≤ a * N ^ a :=
    Real.sqrt_le_self_iff.mpr (Or.inr hP)
  have hs (x r : ℝ) (hx : 0 ≤ x) : Real.sqrt (x ^ r) = x ^ (r / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    congr 1
    ring
  have hx : 0 ≤ (ε ^ b : ℝ) := Real.rpow_nonneg hε _
  have hy : 0 ≤ ((D.q : ℝ) ^ (-b)) := Real.rpow_nonneg (by positivity) _
  have hz : 0 ≤ (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hsum : Real.sqrt (ε ^ b + (D.q : ℝ) ^ (-b) +
      (2 : ℝ) ^ (-(b * (D.m * D.d : ℕ)))) ≤
      ε ^ (b / 2) + (D.q : ℝ) ^ (-(b / 2)) +
        (2 : ℝ) ^ (-((b / 2) * (D.m * D.d : ℕ))) := by
    calc
      _ ≤ Real.sqrt (ε ^ b) + Real.sqrt ((D.q : ℝ) ^ (-b)) +
          Real.sqrt ((2 : ℝ) ^ (-(b * (D.m * D.d : ℕ)))) :=
        _root_.LIDT.MIPStarRE.LDT.sqrt_add3_le_add3_sqrt hx hy hz
      _ = _ := by
        rw [hs ε b hε, hs (D.q : ℝ) (-b) (by positivity),
          hs 2 (-(b * (D.m * D.d : ℕ))) (by norm_num)]
        congr 2 <;> congr 1 <;> ring
  have hmono : a * N ^ a ≤ a * N ^ (10 * a) := by
    apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by linarith)
  unfold _root_.MIPStarRE.QPBT.deltaLd
  simp only [Real.rpow_eq_pow]
  change 10 * Real.sqrt (a * N ^ a * _) ≤ 10 * a * N ^ (10 * a) * _
  rw [Real.sqrt_mul hP0]
  have hbound := mul_le_mul (hsP.trans hmono) hsum (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ a * N ^ (10 * a))
  nlinarith
