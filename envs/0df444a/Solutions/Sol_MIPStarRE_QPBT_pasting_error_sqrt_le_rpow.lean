-- Prove2me | solution 1 for MIPStarRE.QPBT.pasting_error_sqrt_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:38:59.386017+00:00
-- url     : https://prove2.me/submissions/659eb96a-3cf5-456a-b972-a2543d615d62

-- Generated proof for MIPStarRE.QPBT.pasting_error_sqrt_le_rpow.
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/Sandwich/Pasting/Assembly.lean. -/
/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open DistanceCalculus























/-- A square root is bounded by any nonnegative number whose square dominates
the radicand. Formalization-only arithmetic auxiliary. -/
private theorem sqrt_le_of_sq_le (X B : ℝ) (hB : 0 ≤ B) (h : X ≤ B ^ 2) :
    Real.sqrt X ≤ B := by
  calc Real.sqrt X ≤ Real.sqrt (B ^ 2) := Real.sqrt_le_sqrt h
    _ = B := Real.sqrt_sq hB

/-- The assembled error of the pasting estimate, written in the variables
`u = δ ^ (1/8)` and `v = η ^ (1/4)`, is at most `(3 * C + 19) * (v + u)` on the
unit square. Every summand of the radicand is dominated by `u ^ 2` or by
`v ^ 2`, and the square root of `(3 * C + 18) * u ^ 2 + 6 * v ^ 2` is at most
`(3 * C + 19) / 2 * u + 3 * v`. Formalization-only arithmetic auxiliary of
`lem:pasting`, blueprint `ch12_qpbt_games.tex:960-990`. -/
private theorem pasting_error_numeric_aux (C u v : ℝ) (hC : 1 ≤ C)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    2 * u ^ 8 + Real.sqrt (C * u ^ 8 +
      (2 * Real.sqrt (2 * u ^ 8) + 2 * u ^ 8 + 2 * Real.sqrt (C * u ^ 8) +
        C * u ^ 8) + 2 * v ^ 4 +
      2 * Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) +
      2 * Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)))) ≤
      (3 * C + 19) * (v + u) := by
  have hC0 : (0:ℝ) ≤ C := le_trans zero_le_one hC
  have hu82 : u ^ 8 ≤ u ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu84 : u ^ 8 ≤ u ^ 4 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu42 : u ^ 4 ≤ u ^ 2 := pow_le_pow_of_le_one hu0 hu1 (by norm_num)
  have hu81 : u ^ 8 ≤ u := by
    simpa using pow_le_pow_of_le_one hu0 hu1 (show 1 ≤ 8 by norm_num)
  have hv42 : v ^ 4 ≤ v ^ 2 := pow_le_pow_of_le_one hv0 hv1 (by norm_num)
  have h1 : Real.sqrt (2 * u ^ 8) ≤ 3 / 2 * u ^ 4 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [pow_nonneg hu0 8]
  have h2 : Real.sqrt (C * u ^ 8) ≤ (C + 1) / 2 * u ^ 4 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [sq_nonneg (C - 1), pow_nonneg hu0 8]
  have h3 : Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8))) ≤ 3 * u ^ 2 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [h1, hu84, pow_nonneg hu0 4]
  have h4 : Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) ≤
      3 * u ^ 2 + 2 * v ^ 2 := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [h1, hu84, pow_nonneg hu0 4, pow_nonneg hv0 4,
      mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  have hCu8 : C * u ^ 8 ≤ C * u ^ 2 := mul_le_mul_of_nonneg_left hu82 hC0
  have hC1u : (C + 1) * u ^ 4 ≤ (C + 1) * u ^ 2 :=
    mul_le_mul_of_nonneg_left hu42 (by linarith)
  have hK : C * u ^ 8 +
      (2 * Real.sqrt (2 * u ^ 8) + 2 * u ^ 8 + 2 * Real.sqrt (C * u ^ 8) +
        C * u ^ 8) + 2 * v ^ 4 +
      2 * Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) +
      2 * Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8))) ≤
      (3 * C + 18) * u ^ 2 + 6 * v ^ 2 := by
    nlinarith [h1, h2, h3, h4, hu82, hu42, hv42, hCu8, hC1u]
  have hsK : Real.sqrt (C * u ^ 8 +
      (2 * Real.sqrt (2 * u ^ 8) + 2 * u ^ 8 + 2 * Real.sqrt (C * u ^ 8) +
        C * u ^ 8) + 2 * v ^ 4 +
      2 * Real.sqrt (2 * ((u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)) + v ^ 4)) +
      2 * Real.sqrt (2 * (u ^ 8 + 2 * Real.sqrt (2 * u ^ 8)))) ≤
      (3 * C + 19) / 2 * u + 3 * v := by
    refine sqrt_le_of_sq_le _ _ (by positivity) ?_
    nlinarith [hK, mul_nonneg hu0 hv0, sq_nonneg u, sq_nonneg v,
      sq_nonneg (C * u), mul_nonneg (mul_nonneg hC0 hu0) hv0,
      mul_nonneg hC0 (sq_nonneg u)]
  nlinarith [hsK, hu81, mul_nonneg (sub_nonneg.mpr hC) hu0,
    mul_nonneg (sub_nonneg.mpr hC) hv0]



end MIPStarRE.QPBT

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution (C δ η : ℝ) (hC : 1 ≤ C) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    2 * δ + Real.sqrt (C * δ +
      (2 * Real.sqrt (2 * δ) + 2 * δ + 2 * Real.sqrt (C * δ) + C * δ) + 2 * η +
      2 * Real.sqrt (2 * ((δ + 2 * Real.sqrt (2 * δ)) + η)) +
      2 * Real.sqrt (2 * (δ + 2 * Real.sqrt (2 * δ)))) ≤
      (3 * C + 19) * (η ^ (1/4 : ℝ) + δ ^ (1/8 : ℝ)) := by
  have hu0' : 0 ≤ δ ^ (1/8 : ℝ) := Real.rpow_nonneg hδ0 _
  have hv0' : 0 ≤ η ^ (1/4 : ℝ) := Real.rpow_nonneg hη0 _
  have hu1' : δ ^ (1/8 : ℝ) ≤ 1 := Real.rpow_le_one hδ0 hδ1 (by norm_num)
  have hv1' : η ^ (1/4 : ℝ) ≤ 1 := Real.rpow_le_one hη0 hη1 (by norm_num)
  have hδu' : δ = (δ ^ (1/8 : ℝ)) ^ 8 := by
    rw [← Real.rpow_natCast (δ ^ (1/8 : ℝ)) 8, ← Real.rpow_mul hδ0]
    norm_num
  have hηv' : η = (η ^ (1/4 : ℝ)) ^ 4 := by
    rw [← Real.rpow_natCast (η ^ (1/4 : ℝ)) 4, ← Real.rpow_mul hη0]
    norm_num
  obtain ⟨u, hu0, hu1, hδu, hue⟩ :
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ δ = u ^ 8 ∧ δ ^ (1/8 : ℝ) = u :=
    ⟨δ ^ (1/8 : ℝ), hu0', hu1', hδu', rfl⟩
  obtain ⟨v, hv0, hv1, hηv, hve⟩ :
      ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧ η = v ^ 4 ∧ η ^ (1/4 : ℝ) = v :=
    ⟨η ^ (1/4 : ℝ), hv0', hv1', hηv', rfl⟩
  rw [hue, hve, hδu, hηv]
  exact pasting_error_numeric_aux C u v hC hu0 hu1 hv0 hv1
