-- Prove2me | solution 1 for OAI.TriangularCovering.finiteFamily_total
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:17:40.81825+00:00
-- url     : https://prove2.me/submissions/978bac72-506f-4b93-9e8c-d2ddcea69914

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CylinderFamily.lean:L212-L231
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.finiteFamily_total. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Projection ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma projectedCylinder_area (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) :
    area (projectedCylinder u hu a b c h).base = |inner ℝ u (cross3 (b-a) (c-a))|/2 := by
  unfold area
  rw [projectedCylinder, projection_triangle_measure hu, ENNReal.toReal_ofReal (by positivity)]

end TriangularCovering

end

end OAI

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CylinderFamily ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_sq : H^2 = 2 := by norm_num [H]

lemma tiltV_norm (ε A B : ℝ) : ‖tiltV ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltV]
  congr 1
  nlinarith only [H_sq]

lemma tiltW_norm (ε A B : ℝ) : ‖tiltW ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltW]
  congr 1
  nlinarith only [H_sq]

lemma lowerCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    area (lowerCylinder hab hT ε A B).base =
      H*(b-a)*T^2 / (2*Real.sqrt (1+ε^2*(A^2+2*B^2))) := by
  rw [lowerCylinder, projectedCylinder_area, lower_triple, tiltV_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

lemma upperCylinder_area {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    area (upperCylinder hab hT ε A B).base =
      H*(b-a)*T^2 / (2*Real.sqrt (1+ε^2*(A^2+2*B^2))) := by
  rw [upperCylinder, projectedCylinder_area, upper_triple, tiltW_norm]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos H_pos,
    abs_of_neg (sub_neg.mpr hab), abs_sq, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution (ε : ℝ) (he : 0 < ε) :
    totalArea (finiteFamily ε he) / H =
      ∑ j : Fin (n ε), normalizedTerm ε (mesh (n ε) j) (mesh (n ε) (j+1)) := by
  have hs : totalArea (finiteFamily ε he) =
      (∑ j : Fin (n ε), area (lowerFamily ε he j).base) +
      (∑ j : Fin (n ε), area (upperFamily ε he j).base) := by
    change (∑ i : Fin (2*n ε),
      (fun k : Fin (n ε+n ε) => area (Fin.append (lowerFamily ε he) (upperFamily ε he) k).base)
        ((finCongr (two_mul (n ε))) i)) = _
    rw [Equiv.sum_comp (finCongr (two_mul (n ε)))
      (fun k => area (Fin.append (lowerFamily ε he) (upperFamily ε he) k).base)]
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  rw [hs, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [lowerFamily, upperFamily, lowerCylinder_area, upperCylinder_area]
  dsimp [normalizedTerm, speedSq, n]
  field_simp [H_ne_zero]
  ring
