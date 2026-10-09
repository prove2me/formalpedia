-- Prove2me | solution 1 for MazurTransfer.order13_actual_finite_map_data_arbitrarily_large_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T09:39:24.137975+00:00
-- url     : https://prove2.me/submissions/574f1ca0-da21-452f-ba2c-083729eb330c

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: genuine finite-map data of arbitrarily large degree on
this actual curve over every characteristic-zero field. Named downstream
consumer: finite etale Picard charts and rational Picard representability.
The two-affine-open cover is constructed from the actual unchanged gluing.
The field-independent finite-map criterion is reused from official Anthropic
FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0; the curve source
is the user's WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_MazurTransfer_order13_actual_curveModel_exists
import Theorems.Thm_MazurTransfer_order13_actual_geometrically_integral_charZero
import Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_finiteMapData_le_isUnit_of_twoAffineOpenCover
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra

theorem solution.{u} (K : Type u) [Field K] [CharZero K]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) (m₀ : ℕ) :
    ∃ 𝔉 : SmoothProperCurve.FiniteMapData
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε,
      m₀ ≤ 𝔉.m ∧ IsUnit (𝔉.m : K) := by
  obtain ⟨F, hF, hAlg, M, e, he⟩ := MazurTransfer.order13_actual_curveModel_exists K
  letI := hF
  letI := hAlg
  have hc : e.inv ≫ M.toBase = MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  letI : IsProper (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) := by
    rw [← hc]
    infer_instance
  letI : SmoothOfRelativeDimension 1
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) := by
    rw [← hc]
    exact smoothOfRelativeDimension_comp 0 1 e.inv M.toBase
  letI := MazurTransfer.order13_actual_geometrically_integral_charZero K
  let W : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).TwoAffineOpenCover := by
    haveI : (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).IsSeparated := by
      have h : IsSeparated (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K ≫
        terminal.from (Spec (CommRingCat.of K))) := inferInstance
      refine ⟨?_⟩
      simpa only [terminal.comp_from] using h
    refine {
      U0 := (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap K).opensRange
      U1 := (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap K).opensRange
      isAffineOpen_U0 := isAffineOpen_opensRange _
      isAffineOpen_U1 := isAffineOpen_opensRange _
      sup_eq_top := ?_
      isAffineOpen_inf := (isAffineOpen_opensRange
        (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap K)).inf
        (isAffineOpen_opensRange
          (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap K)) }
    apply top_unique
    intro x _
    change x ∈ Set.range (MazurTorsion.XOneThirteenProjectiveCurve.ordinaryChartMap K) ∨
      x ∈ Set.range (MazurTorsion.XOneThirteenProjectiveCurve.reciprocalChartMap K)
    obtain ⟨i, y, hy⟩ := (MazurTorsion.XOneThirteenProjectiveCurve.glueData K).ι_jointly_surjective x
    cases i
    · exact Or.inl ⟨y, hy⟩
    · exact Or.inr ⟨y, hy⟩
  exact AlgebraicGeometry.SmoothProperCurve.exists_finiteMapData_le_isUnit_of_twoAffineOpenCover K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε W m₀

#print axioms solution
