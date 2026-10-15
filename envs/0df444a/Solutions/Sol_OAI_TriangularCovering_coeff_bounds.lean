-- Prove2me | solution 1 for OAI.TriangularCovering.coeff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:02:30.087991+00:00
-- url     : https://prove2.me/submissions/b8bc7b4e-5375-4da7-8f02-54242e931230

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L66-L85
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.coeff_bounds. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CoordinateCover ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

theorem d_bounds {q : ℝ} (hq : |q| ≤ 1) : 0 ≤ d q ∧ d q ≤ 1 / 8 := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith [abs_le.mp hq, sq_abs q]
  constructor
  · unfold d; positivity
  · unfold d
    nlinarith [sq_nonneg q, mul_self_le_mul_self (sq_nonneg q) hq2]

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    0 ≤ alpha a b ∧ alpha a b ≤ 1 / 2 ∧ |beta a b| ≤ 1 / 2 ∧
    η ≤ cutoffCoeff a b ∧ cutoffCoeff a b ≤ 1 / 8 + η := by
  have hab : |a * b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have ht : |a + b| ≤ 2 := (abs_add_le a b).trans (by linarith)
  have da := d_bounds ha
  have db := d_bounds hb
  dsimp [alpha, beta, cutoffCoeff]
  constructor
  · linarith [(abs_le.mp hab).1]
  constructor
  · linarith [(abs_le.mp hab).2]
  constructor
  · rw [abs_div]; norm_num
    linarith
  constructor
  · have := le_max_left (d a) (d b); linarith
  · have := max_le da.2 db.2; linarith
