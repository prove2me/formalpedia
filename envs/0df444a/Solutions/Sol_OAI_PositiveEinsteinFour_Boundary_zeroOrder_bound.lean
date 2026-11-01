-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T18:48:20.410221+00:00
-- url     : https://prove2.me/submissions/2b7f4444-dde3-48d0-9024-097fea4baa71

import Mathlib
import Definitions.Def_OAIQ091C001
import Definitions.Def_OAIQ091C004

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Coupling
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra and integration in the one-block vanishing argument

The scalar one-block vanishing argument in Section 8 of
*Positively curved Einstein four-manifolds* (23 September 2026). -/

namespace PositiveEinsteinFour

open MeasureTheory Filter

noncomputable section

theorem couplingCoefficient_lower {v b : ℝ}
    (hvb : v + b ≤ 2) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    1 / 10 ≤ couplingCoefficient v b := by
  have hsum : (v + b) ^ 2 ≤ 4 := by nlinarith
  have hprod : v * b ≤ 1 := by nlinarith [sq_nonneg (v - b)]
  unfold couplingCoefficient
  nlinarith

end

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Potential
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The potential polynomial certificate

The five quotient polynomials and their quarter-interval Bernstein certificates
are those of Section 7, Lemma "The polynomial F" of the manuscript.
The polynomial identities and inequalities hold over the real numbers.
-/

namespace PositiveEinsteinFour.Potential

noncomputable section

private theorem q0_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 61440 * q0 n =
      2625536 * (1 - (4 * n - 0)) ^ 4 +
      5151296 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 3 +
      3261264 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 2 +
      964412 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) +
      282419 * (4 * n - 0) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q0_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 61440 * q0 n =
      282419 * (1 - (4 * n - 1)) ^ 4 +
      1294940 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 3 +
      4252848 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 2 +
      5358224 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) +
      2171408 * (4 * n - 1) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q0_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 61440 * q0 n =
      2171408 * (1 - (4 * n - 2)) ^ 4 +
      12013040 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 3 +
      24217296 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 2 +
      20902820 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) +
      6580667 * (4 * n - 2) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q0_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q0 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 61440 * q0 n =
      6580667 * (1 - (4 * n - 3)) ^ 4 +
      31742516 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 3 +
      56736384 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 2 +
      44603648 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) +
      13082624 * (4 * n - 3) ^ 4 := by
    unfold q0
    ring
  have hnonneg : 0 ≤ 61440 * q0 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q0_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q0 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q0_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q0_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q0_quarter2 h2 h3
  · exact q0_quarter3 h3 (by simpa using hn1)

private theorem q1_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 491520 * q1 n =
      21635072 * (1 - (4 * n - 0)) ^ 6 +
      159106048 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 5 +
      426549504 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 4 +
      571195392 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 3 +
      415062688 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 2 +
      157590852 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) +
      24662089 * (4 * n - 0) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q1_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 491520 * q1 n =
      24662089 * (1 - (4 * n - 1)) ^ 6 +
      138354216 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 5 +
      318879508 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 4 +
      391606272 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 3 +
      272514864 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 2 +
      102606208 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) +
      16527296 * (4 * n - 1) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q1_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 491520 * q1 n =
      16527296 * (1 - (4 * n - 2)) ^ 6 +
      95721344 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 5 +
      238090544 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 4 +
      328631680 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 3 +
      267653012 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 2 +
      123108392 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) +
      25207625 * (4 * n - 2) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q1_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q1 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 491520 * q1 n =
      25207625 * (1 - (4 * n - 3)) ^ 6 +
      179383108 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 5 +
      549026592 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 4 +
      921476736 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 3 +
      891131392 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 2 +
      469149696 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) +
      104660992 * (4 * n - 3) ^ 6 := by
    unfold q1
    ring
  have hnonneg : 0 ≤ 491520 * q1 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q1_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q1 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q1_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q1_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q1_quarter2 h2 h3
  · exact q1_quarter3 h3 (by simpa using hn1)

private theorem q2_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 11796480 * q2 n =
      2424832 * (1 - (4 * n - 0)) ^ 7 +
      466812928 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 6 +
      2033946624 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 5 +
      4141778944 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 4 +
      4911514816 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 3 +
      3459239472 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) ^ 2 +
      1332713460 * (4 * n - 0) ^ 6 * (1 - (4 * n - 0)) +
      215332845 * (4 * n - 0) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q2_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 11796480 * q2 n =
      215332845 * (1 - (4 * n - 1)) ^ 7 +
      1681946370 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 6 +
      5554636932 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 5 +
      10011268904 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 4 +
      10571478896 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 3 +
      6531970656 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) ^ 2 +
      2191187648 * (4 * n - 1) ^ 6 * (1 - (4 * n - 1)) +
      310014848 * (4 * n - 1) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q2_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 11796480 * q2 n =
      310014848 * (1 - (4 * n - 2)) ^ 7 +
      2149020224 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 6 +
      6278966112 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 5 +
      10081126224 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 4 +
      9736555176 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 3 +
      5800077804 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) ^ 2 +
      2047576786 * (4 * n - 2) ^ 6 * (1 - (4 * n - 2)) +
      345453127 * (4 * n - 2) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q2_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q2 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 11796480 * q2 n =
      345453127 * (1 - (4 * n - 3)) ^ 7 +
      2788766992 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 6 +
      10247219040 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 5 +
      22136491264 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 4 +
      30033262336 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 3 +
      25262764032 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) ^ 2 +
      12071387136 * (4 * n - 3) ^ 6 * (1 - (4 * n - 3)) +
      2511863808 * (4 * n - 3) ^ 7 := by
    unfold q2
    ring
  have hnonneg : 0 ≤ 11796480 * q2 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q2_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q2 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q2_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q2_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q2_quarter2 h2 h3
  · exact q2_quarter3 h3 (by simpa using hn1)

private theorem q3_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 1966080 * q3 n =
      4898816 * (1 - (4 * n - 0)) ^ 7 +
      221659136 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 6 +
      706062336 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 5 +
      1022492928 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 4 +
      906219840 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 3 +
      541440384 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) ^ 2 +
      200503936 * (4 * n - 0) ^ 6 * (1 - (4 * n - 0)) +
      33386881 * (4 * n - 0) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q3_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 1966080 * q3 n =
      33386881 * (1 - (4 * n - 1)) ^ 7 +
      266912398 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 6 +
      939891156 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 5 +
      1826274520 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 4 +
      2046373168 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 3 +
      1309889184 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) ^ 2 +
      444087744 * (4 * n - 1) ^ 6 * (1 - (4 * n - 1)) +
      61957248 * (4 * n - 1) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q3_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 1966080 * q3 n =
      61957248 * (1 - (4 * n - 2)) ^ 7 +
      423313728 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 6 +
      1185245088 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 5 +
      1755283472 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 4 +
      1492876376 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 3 +
      750146748 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) ^ 2 +
      221835614 * (4 * n - 2) ^ 6 * (1 - (4 * n - 2)) +
      34464779 * (4 * n - 2) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q3_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q3 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 1966080 * q3 n =
      34464779 * (1 - (4 * n - 3)) ^ 7 +
      260671292 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 6 +
      983160816 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 5 +
      2348592384 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 4 +
      3624720384 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 3 +
      3448946688 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) ^ 2 +
      1833213952 * (4 * n - 3) ^ 6 * (1 - (4 * n - 3)) +
      418643968 * (4 * n - 3) ^ 7 := by
    unfold q3
    ring
  have hnonneg : 0 ≤ 1966080 * q3 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q3_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q3 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q3_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q3_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q3_quarter2 h2 h3
  · exact q3_quarter3 h3 (by simpa using hn1)

private theorem q4_quarter0 {n : ℝ}
    (hlo : (0 : ℝ) / 4 ≤ n) (hhi : n ≤ (1 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 0) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 0) := by linarith
  have hcert : 3932160 * q4 n =
      16252928 * (1 - (4 * n - 0)) ^ 7 +
      917766144 * (4 * n - 0) * (1 - (4 * n - 0)) ^ 6 +
      2639790080 * (4 * n - 0) ^ 2 * (1 - (4 * n - 0)) ^ 5 +
      3039076352 * (4 * n - 0) ^ 3 * (1 - (4 * n - 0)) ^ 4 +
      1790831168 * (4 * n - 0) ^ 4 * (1 - (4 * n - 0)) ^ 3 +
      640144976 * (4 * n - 0) ^ 5 * (1 - (4 * n - 0)) ^ 2 +
      175832124 * (4 * n - 0) ^ 6 * (1 - (4 * n - 0)) +
      31029203 * (4 * n - 0) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q4_quarter1 {n : ℝ}
    (hlo : (1 : ℝ) / 4 ≤ n) (hhi : n ≤ (2 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 1) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 1) := by linarith
  have hcert : 3932160 * q4 n =
      31029203 * (1 - (4 * n - 1)) ^ 7 +
      258576718 * (4 * n - 1) * (1 - (4 * n - 1)) ^ 6 +
      1136612540 * (4 * n - 1) ^ 2 * (1 - (4 * n - 1)) ^ 5 +
      2748867992 * (4 * n - 1) ^ 3 * (1 - (4 * n - 1)) ^ 4 +
      3561439888 * (4 * n - 1) ^ 4 * (1 - (4 * n - 1)) ^ 3 +
      2478232736 * (4 * n - 1) ^ 5 * (1 - (4 * n - 1)) ^ 2 +
      873837888 * (4 * n - 1) ^ 6 * (1 - (4 * n - 1)) +
      122552448 * (4 * n - 1) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q4_quarter2 {n : ℝ}
    (hlo : (2 : ℝ) / 4 ≤ n) (hhi : n ≤ (3 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 2) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 2) := by linarith
  have hcert : 3932160 * q4 n =
      122552448 * (1 - (4 * n - 2)) ^ 7 +
      841896384 * (4 * n - 2) * (1 - (4 * n - 2)) ^ 6 +
      2286583712 * (4 * n - 2) ^ 2 * (1 - (4 * n - 2)) ^ 5 +
      3105299632 * (4 * n - 2) ^ 3 * (1 - (4 * n - 2)) ^ 4 +
      2201967128 * (4 * n - 2) ^ 4 * (1 - (4 * n - 2)) ^ 3 +
      774808916 * (4 * n - 2) ^ 5 * (1 - (4 * n - 2)) ^ 2 +
      117707134 * (4 * n - 2) ^ 6 * (1 - (4 * n - 2)) +
      12115865 * (4 * n - 2) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

private theorem q4_quarter3 {n : ℝ}
    (hlo : (3 : ℝ) / 4 ≤ n) (hhi : n ≤ (4 : ℝ) / 4) : 0 ≤ q4 n := by
  have hz : 0 ≤ (4 * n - 3) := by linarith
  have hw : 0 ≤ 1 - (4 * n - 3) := by linarith
  have hcert : 3932160 * q4 n =
      12115865 * (1 - (4 * n - 3)) ^ 7 +
      51914976 * (4 * n - 3) * (1 - (4 * n - 3)) ^ 6 +
      380055968 * (4 * n - 3) ^ 2 * (1 - (4 * n - 3)) ^ 5 +
      1876136192 * (4 * n - 3) ^ 3 * (1 - (4 * n - 3)) ^ 4 +
      4433662208 * (4 * n - 3) ^ 4 * (1 - (4 * n - 3)) ^ 3 +
      5374865408 * (4 * n - 3) ^ 5 * (1 - (4 * n - 3)) ^ 2 +
      3309060096 * (4 * n - 3) ^ 6 * (1 - (4 * n - 3)) +
      837287936 * (4 * n - 3) ^ 7 := by
    unfold q4
    ring
  have hnonneg : 0 ≤ 3932160 * q4 n := by
    rw [hcert]
    positivity
  nlinarith only [hnonneg]

theorem q4_nonneg {n : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1) : 0 ≤ q4 n := by
  rcases le_total n (1 / 4) with h | h
  · exact q4_quarter0 (by simpa using hn0) h
  rcases le_total n (2 / 4) with h2 | h2
  · exact q4_quarter1 h h2
  rcases le_total n (3 / 4) with h3 | h3
  · exact q4_quarter2 h2 h3
  · exact q4_quarter3 h3 (by simpa using hn1)

theorem potential_normalForm (n t : ℝ) :
    potential (1 - n + t) (1 - n - t) = normalForm n t := by
  unfold potential zeroOrder theta kappa normalForm f0 f1 f2 f3
  ring

/-- Homogeneous Bernstein identity; clearing the denominator avoids any
division at the boundary `n = 1`. -/
theorem normalForm_certificate (n t : ℝ) :
    (1 - n) ^ 8 * normalForm n t =
      n ^ 3 * (1 - n) * q0 n * ((1 - n) ^ 2 - t ^ 2) ^ 4 +
      4 * n * (1 - n) * q1 n * t ^ 2 * ((1 - n) ^ 2 - t ^ 2) ^ 3 +
      6 * (1 - n) * q2 n * t ^ 4 * ((1 - n) ^ 2 - t ^ 2) ^ 2 +
      4 * (1 - n) * q3 n * t ^ 6 * ((1 - n) ^ 2 - t ^ 2) +
      (1 - n) * q4 n * t ^ 8 := by
  unfold normalForm f0 f1 f2 f3 q0 q1 q2 q3 q4
  ring

theorem normalForm_nonneg {n t : ℝ} (hn0 : 0 ≤ n) (hn1 : n ≤ 1)
    (ht : t ^ 2 ≤ (1 - n) ^ 2) : 0 ≤ normalForm n t := by
  rcases eq_or_lt_of_le hn1 with hn | hn
  · subst n
    have ht0 : t = 0 := by nlinarith [sq_nonneg t]
    subst t
    norm_num [normalForm, f0, f1, f2, f3]
  have hd : 0 ≤ 1 - n := sub_nonneg.mpr hn1
  have hx : 0 ≤ (1 - n) ^ 2 - t ^ 2 := sub_nonneg.mpr ht
  have h0 := q0_nonneg hn0 hn1
  have h1 := q1_nonneg hn0 hn1
  have h2 := q2_nonneg hn0 hn1
  have h3 := q3_nonneg hn0 hn1
  have h4 := q4_nonneg hn0 hn1
  have hproduct : 0 ≤ (1 - n) ^ 8 * normalForm n t := by
    rw [normalForm_certificate]
    positivity
  exact nonneg_of_mul_nonneg_right hproduct (pow_pos (sub_pos.mpr hn) 8)

/-- Lemma 7.4 of the manuscript, including every boundary of its triangle. -/
theorem potential_nonneg {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hsum : v + b ≤ 2) : 0 ≤ potential v b := by
  let n := (2 - v - b) / 2
  let t := (v - b) / 2
  have hn0 : 0 ≤ n := by dsimp [n]; linarith
  have hn1 : n ≤ 1 := by dsimp [n]; linarith
  have ht : t ^ 2 ≤ (1 - n) ^ 2 := by
    dsimp [n, t]
    nlinarith [mul_nonneg hv hb]
  have hvn : 1 - n + t = v := by dsimp [n, t]; ring
  have hbn : 1 - n - t = b := by dsimp [n, t]; ring
  have h := normalForm_nonneg hn0 hn1 ht
  rwa [← potential_normalForm, hvn, hbn] at h

end

end PositiveEinsteinFour.Potential

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Boundary
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact triangle certificates and the full zeroth-order coupling bound. -/

namespace PositiveEinsteinFour.Boundary

open Potential

noncomputable section

private theorem spectral_coefficient_triangle {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) :
    0 ≤ spectralCoefficient (z + 2 * w) z := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcert : 36 * spectralCoefficient (z + 2 * w) z =
      1597 * (1 - z - w) ^ 6 +
      202 * w * (1 - z - w) ^ 5 +
      1895 * w ^ 2 * (1 - z - w) ^ 4 +
      16404 * w ^ 3 * (1 - z - w) ^ 3 +
      21811 * w ^ 4 * (1 - z - w) ^ 2 +
      10562 * w ^ 5 * (1 - z - w) +
      1865 * w ^ 6 +
      8899 * z * (1 - z - w) ^ 5 +
      14289 * z * w * (1 - z - w) ^ 4 +
      45098 * z * w ^ 2 * (1 - z - w) ^ 3 +
      81382 * z * w ^ 3 * (1 - z - w) ^ 2 +
      51939 * z * w ^ 4 * (1 - z - w) +
      10265 * z * w ^ 5 +
      16125 * z ^ 2 * (1 - z - w) ^ 4 +
      36612 * z ^ 2 * w * (1 - z - w) ^ 3 +
      91530 * z ^ 2 * w ^ 2 * (1 - z - w) ^ 2 +
      86676 * z ^ 2 * w ^ 3 * (1 - z - w) +
      21537 * z ^ 2 * w ^ 4 +
      13165 * z ^ 3 * (1 - z - w) ^ 3 +
      37489 * z ^ 3 * w * (1 - z - w) ^ 2 +
      60935 * z ^ 3 * w ^ 2 * (1 - z - w) +
      21635 * z ^ 3 * w ^ 3 +
      5566 * z ^ 4 * (1 - z - w) ^ 2 +
      16860 * z ^ 4 * w * (1 - z - w) +
      10394 * z ^ 4 * w ^ 2 +
      1224 * z ^ 5 * (1 - z - w) +
      1896 * z ^ 5 * w := by
    unfold spectralCoefficient kappa
    ring
  have hp : 0 ≤ 36 * spectralCoefficient (z + 2 * w) z := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem corrected_potential_left {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) :
    0 ≤ correctedPotential (z + w) w := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcert : 61440 * correctedPotential (z + w) w =
      52330496 * (1 - z - w) ^ 9 +
      357015552 * w * (1 - z - w) ^ 8 +
      815244288 * w ^ 2 * (1 - z - w) ^ 7 +
      810256384 * w ^ 3 * (1 - z - w) ^ 6 +
      394554624 * w ^ 4 * (1 - z - w) ^ 5 +
      107510016 * w ^ 5 * (1 - z - w) ^ 4 +
      12652544 * w ^ 6 * (1 - z - w) ^ 3 +
      556486656 * z * (1 - z - w) ^ 8 +
      2680071168 * z * w * (1 - z - w) ^ 7 +
      4303378944 * z * w ^ 2 * (1 - z - w) ^ 6 +
      2903831040 * z * w ^ 3 * (1 - z - w) ^ 5 +
      908160768 * z * w ^ 4 * (1 - z - w) ^ 4 +
      154624512 * z * w ^ 5 * (1 - z - w) ^ 3 +
      11212800 * z * w ^ 6 * (1 - z - w) ^ 2 +
      2195206400 * z ^ 2 * (1 - z - w) ^ 7 +
      7890980864 * z ^ 2 * w * (1 - z - w) ^ 6 +
      9038312320 * z ^ 2 * w ^ 2 * (1 - z - w) ^ 5 +
      3989635200 * z ^ 2 * w ^ 3 * (1 - z - w) ^ 4 +
      717011840 * z ^ 2 * w ^ 4 * (1 - z - w) ^ 3 +
      82824064 * z ^ 2 * w ^ 5 * (1 - z - w) ^ 2 +
      4427776 * z ^ 2 * w ^ 6 * (1 - z - w) +
      4629191296 * z ^ 3 * (1 - z - w) ^ 6 +
      12449319040 * z ^ 3 * w * (1 - z - w) ^ 5 +
      9970116736 * z ^ 3 * w ^ 2 * (1 - z - w) ^ 4 +
      2689352704 * z ^ 3 * w ^ 3 * (1 - z - w) ^ 3 +
      261153280 * z ^ 3 * w ^ 4 * (1 - z - w) ^ 2 +
      28723840 * z ^ 3 * w ^ 5 * (1 - z - w) +
      992256 * z ^ 3 * w ^ 6 +
      5937790992 * z ^ 4 * (1 - z - w) ^ 5 +
      11767844624 * z ^ 4 * w * (1 - z - w) ^ 4 +
      6335324928 * z ^ 4 * w ^ 2 * (1 - z - w) ^ 3 +
      957916992 * z ^ 4 * w ^ 3 * (1 - z - w) ^ 2 +
      65841872 * z ^ 4 * w ^ 4 * (1 - z - w) +
      6269328 * z ^ 4 * w ^ 5 +
      4893653872 * z ^ 5 * (1 - z - w) ^ 4 +
      6929290400 * z ^ 5 * w * (1 - z - w) ^ 3 +
      2344739296 * z ^ 5 * w ^ 2 * (1 - z - w) ^ 2 +
      190004832 * z ^ 5 * w ^ 3 * (1 - z - w) +
      12840720 * z ^ 5 * w ^ 4 +
      2625756488 * z ^ 6 * (1 - z - w) ^ 3 +
      2499901720 * z ^ 6 * w * (1 - z - w) ^ 2 +
      476640184 * z ^ 6 * w ^ 2 * (1 - z - w) +
      20443560 * z ^ 6 * w ^ 3 +
      890265000 * z ^ 7 * (1 - z - w) ^ 2 +
      506723984 * z ^ 7 * w * (1 - z - w) +
      42511368 * z ^ 7 * w ^ 2 +
      173232449 * z ^ 8 * (1 - z - w) +
      44351457 * z ^ 8 * w +
      14720001 * z ^ 9 := by
    unfold correctedPotential potential zeroOrder theta spectralCoefficient couplingCoefficient kappa
    ring
  have hp : 0 ≤ 61440 * correctedPotential (z + w) w := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem corrected_potential_right {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) :
    0 ≤ correctedPotential (1 + w) z := by
  have hu : 0 ≤ 1 - z - w := by linarith
  have hcert : 61440 * correctedPotential (1 + w) z =
      14720001 * (1 - z - w) ^ 9 +
      91727569 * w * (1 - z - w) ^ 8 +
      238225960 * w ^ 2 * (1 - z - w) ^ 7 +
      327759896 * w ^ 3 * (1 - z - w) ^ 6 +
      234220880 * w ^ 4 * (1 - z - w) ^ 5 +
      58259600 * w ^ 5 * (1 - z - w) ^ 4 +
      2556928 * w ^ 6 * (1 - z - w) ^ 3 +
      39006208 * w ^ 7 * (1 - z - w) ^ 2 +
      27283456 * w ^ 8 * (1 - z - w) +
      253952 * w ^ 9 +
      44351457 * z * (1 - z - w) ^ 8 +
      202899328 * z * w * (1 - z - w) ^ 7 +
      373129128 * z * w ^ 2 * (1 - z - w) ^ 6 +
      374168320 * z * w ^ 3 * (1 - z - w) ^ 5 +
      259960144 * z * w ^ 4 * (1 - z - w) ^ 4 +
      218477056 * z * w ^ 5 * (1 - z - w) ^ 3 +
      215812096 * z * w ^ 6 * (1 - z - w) ^ 2 +
      104497152 * z * w ^ 7 * (1 - z - w) +
      1478656 * z * w ^ 8 +
      42511368 * z ^ 2 * (1 - z - w) ^ 7 +
      118518968 * z ^ 2 * w * (1 - z - w) ^ 6 +
      196012000 * z ^ 2 * w ^ 2 * (1 - z - w) ^ 5 +
      416840032 * z ^ 2 * w ^ 3 * (1 - z - w) ^ 4 +
      621025792 * z ^ 2 * w ^ 4 * (1 - z - w) ^ 3 +
      487728640 * z ^ 2 * w ^ 5 * (1 - z - w) ^ 2 +
      170454016 * z ^ 2 * w ^ 6 * (1 - z - w) +
      2140160 * z ^ 2 * w ^ 7 +
      20443560 * z ^ 3 * (1 - z - w) ^ 6 +
      55317888 * z ^ 3 * w * (1 - z - w) ^ 5 +
      284482272 * z ^ 3 * w ^ 2 * (1 - z - w) ^ 4 +
      644759552 * z ^ 3 * w ^ 3 * (1 - z - w) ^ 3 +
      549594624 * z ^ 3 * w ^ 4 * (1 - z - w) ^ 2 +
      160598016 * z ^ 3 * w ^ 5 * (1 - z - w) +
      1218560 * z ^ 3 * w ^ 6 +
      12840720 * z ^ 4 * (1 - z - w) ^ 5 +
      62565328 * z ^ 4 * w * (1 - z - w) ^ 4 +
      248047104 * z ^ 4 * w ^ 2 * (1 - z - w) ^ 3 +
      296960512 * z ^ 4 * w ^ 3 * (1 - z - w) ^ 2 +
      94270464 * z ^ 4 * w ^ 4 * (1 - z - w) +
      378880 * z ^ 4 * w ^ 5 +
      6269328 * z ^ 5 * (1 - z - w) ^ 4 +
      21430784 * z ^ 5 * w * (1 - z - w) ^ 3 +
      60944896 * z ^ 5 * w ^ 2 * (1 - z - w) ^ 2 +
      32604160 * z ^ 5 * w ^ 3 * (1 - z - w) +
      75776 * z ^ 5 * w ^ 4 +
      992256 * z ^ 6 * (1 - z - w) ^ 3 +
      1525760 * z ^ 6 * w * (1 - z - w) ^ 2 +
      5408768 * z ^ 6 * w ^ 2 * (1 - z - w) := by
    unfold correctedPotential potential zeroOrder theta spectralCoefficient couplingCoefficient kappa
    ring
  have hp : 0 ≤ 61440 * correctedPotential (1 + w) z := by
    rw [hcert]
    positivity
  nlinarith only [hp]

/-- The first boundary certificate in equation (23), including the vertex
where its value is zero. -/
theorem spectralCoefficient_nonneg {v b : ℝ}
    (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2) :
    0 ≤ spectralCoefficient v b := by
  have h := spectral_coefficient_triangle (z := b) (w := (v - b) / 2)
    hb (by linarith) (by linarith)
  simpa only [show b + 2 * ((v - b) / 2) = v by ring] using h

/-- The last boundary certificate in equation (23). The two triangle proofs
meet along `v = 1`, so no strict-domain hypothesis is required. -/
theorem correctedPotential_nonneg {v b : ℝ}
    (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2) :
    0 ≤ correctedPotential v b := by
  by_cases hv1 : v ≤ 1
  · have h := corrected_potential_left (z := v - b) (w := b)
      (by linarith) hb (by linarith)
    simpa only [sub_add_cancel] using h
  · have h := corrected_potential_right (z := b) (w := v - 1)
      hb (by linarith) (by linarith)
    simpa only [show 1 + (v - 1) = v by ring] using h

private theorem ordered_zeroOrder_bound {v b σ τ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (horder : b ≤ v) (hsum : v + b ≤ 2)
    (hσ : σ ≤ 1) (hτ : τ ≤ 1)
    (hdefect : b ^ 2 * (1 - τ) ≤ 2 * (2 - v - b) ^ 2) :
    zeroOrderIntegrand v b σ τ ≤ -theta v b ^ 2 / couplingCoefficient v b := by
  have hc : 0 < couplingCoefficient v b :=
    lt_of_lt_of_le (by norm_num) (couplingCoefficient_lower hsum hv hb)
  have hcform : couplingCoefficient v b = 2 / 5 - 3 * v * b / 10 := by
    unfold couplingCoefficient
    ring
  have hlv := spectralCoefficient_nonneg hb horder hsum
  have hplus : 0 ≤ 6 * v ^ 2 * (1 - σ) * spectralCoefficient v b := by positivity
  by_cases hlb : 0 ≤ spectralCoefficient b v
  · have hminus : 0 ≤ 6 * b ^ 2 * (1 - τ) * spectralCoefficient b v := by positivity
    have hI : zeroOrderIntegrand v b σ τ ≤ -zeroOrder v b := by
      unfold zeroOrderIntegrand
      linarith
    apply hI.trans
    apply (le_div_iff₀ hc).2
    have hF := potential_nonneg hv hb hsum
    unfold potential at hF
    rw [← hcform] at hF
    nlinarith
  · have hprod := mul_le_mul_of_nonpos_right hdefect
      (show 6 * spectralCoefficient b v ≤ 0 by linarith)
    have hI : zeroOrderIntegrand v b σ τ ≤
        -zeroOrder v b - 12 * (2 - v - b) ^ 2 * spectralCoefficient b v := by
      unfold zeroOrderIntegrand
      nlinarith only [hplus, hprod]
    apply hI.trans
    apply (le_div_iff₀ hc).2
    have hF := correctedPotential_nonneg hb horder hsum
    unfold correctedPotential potential at hF
    rw [← hcform] at hF
    nlinarith

theorem zeroOrderIntegrand_swap (v b σ τ : ℝ) :
    zeroOrderIntegrand b v τ σ = zeroOrderIntegrand v b σ τ := by
  unfold zeroOrderIntegrand zeroOrder
  ring

theorem theta_swap (v b : ℝ) : theta b v = theta v b := by
  unfold theta
  ring

/-- The full potential estimate `I₀ ≤ -Θ²/c`, on the closed spectral triangle
and for either ordering of the blocks. All polynomial certificates required
by equation (23) are proved in this development. -/
theorem zeroOrder_bound_oai {v b σ τ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσ : σ ≤ 1) (hτ : τ ≤ 1)
    (hvdefect : v ^ 2 * (1 - σ) ≤ 2 * (2 - v - b) ^ 2)
    (hbdefect : b ^ 2 * (1 - τ) ≤ 2 * (2 - v - b) ^ 2) :
    zeroOrderIntegrand v b σ τ ≤ -theta v b ^ 2 / couplingCoefficient v b := by
  rcases le_total b v with horder | horder
  · exact ordered_zeroOrder_bound hv hb horder hsum hσ hτ hbdefect
  · have h := ordered_zeroOrder_bound hb hv horder (by linarith) hτ hσ
      (by convert hvdefect using 1; ring)
    rw [zeroOrderIntegrand_swap, theta_swap] at h
    have hc : couplingCoefficient b v = couplingCoefficient v b := by
      unfold couplingCoefficient
      ring
    rwa [hc] at h

end

end PositiveEinsteinFour.Boundary

end OAI
end

theorem solution : type_of% @OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound_oai := @OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound_oai
