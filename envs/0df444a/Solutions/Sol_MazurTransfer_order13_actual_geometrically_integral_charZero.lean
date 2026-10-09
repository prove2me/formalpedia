-- Prove2me | solution 1 for MazurTransfer.order13_actual_geometrically_integral_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T09:32:09.32611+00:00
-- url     : https://prove2.me/submissions/2bdfd723-a3a2-43cf-85f9-4aaa4fc9a434

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: geometric integrality of the actual two-chart order-13
curve over every characteristic-zero field. Named downstream consumer:
rational finite-map data and the exact rational Picard representation.
Uses the exact official Anthropic FLT global-section criterion at commit
6e837e75355538c7f80bab5b956861e86c4eacc2 and the user's actual curve at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c, with retained Apache-2.0 attribution.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_MazurTransfer_order13_actual_curveModel_exists
import Theorems.Thm_MazurTransfer_order13_actual_global_sections_all_algebras_charZero
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem solution.{u} (K : Type u) [Field K] [CharZero K] :
    GeometricallyIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) := by
  obtain ⟨F, hF, hAlg, M, e, he⟩ := MazurTransfer.order13_actual_curveModel_exists K
  letI := hF
  letI := hAlg
  letI : Smooth (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) := by
    haveI : Smooth M.toBase := SmoothOfRelativeDimension.smooth 1 M.toBase
    have hc : e.inv ≫ M.toBase = MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K := by
      rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    rw [← hc]
    infer_instance
  exact AlgebraicGeometry.geometricallyIntegral_of_bijective_algebraMap_sections_of_smooth (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)
    (fun A _ _ => MazurTransfer.order13_actual_global_sections_all_algebras_charZero K A)

#print axioms solution
