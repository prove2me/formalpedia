-- Prove2me | solution 1 for MazurTransfer.order13_actual_dyadic_smooth_proper_whole_generic_fibre_model
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T05:18:15.238449+00:00
-- url     : https://prove2.me/submissions/ac6ac45a-401d-47c9-95c8-b57a77ed4cd5

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the actual WHOLE generic fibre of the smooth
proper mixed quadratic Z_(2)-family with the SAME existing rational curve,
over Spec Q. Named downstream consumer: good reduction at two and the
compatible integral Picard and norm families. Picard data are separate.
-/
import Definitions.Def_MazurTransfer_Order13ActualDyadicOriginalWholeGenericFibreIsomorphismData20261019
import Theorems.Thm_MazurTransfer_order13_actual_dyadic_glued_curve_geometry
import Theorems.Thm_MazurTransfer_order13_actual_mixed_quadratic_curve_proper
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MazurTransfer
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve Order13ActualDyadicMixedQuadraticGenericFibre
namespace MazurTransfer.ActualDyadicOriginalSmoothProperGenericFibreInterface20261019
end MazurTransfer.ActualDyadicOriginalSmoothProperGenericFibreInterface20261019
theorem solution : (IsProper (curveToBase BaseRing) ∧ Smooth (curveToBase BaseRing) ∧
      Flat (curveToBase BaseRing) ∧ LocallyOfFinitePresentation (curveToBase BaseRing)) ∧ (IsFinite (Order13MixedQuadraticProperCurve.hyperellipticMap BaseRing)) ∧ (IsProper (curveToBase BaseRing) ∧ Smooth (curveToBase BaseRing) ∧
      Flat (curveToBase BaseRing) ∧ LocallyOfFinitePresentation (curveToBase BaseRing) ∧
      ∃ e : pullback (Spec.map (CommRingCat.ofHom (algebraMap BaseRing ℚ))) (curveToBase BaseRing) ≅
          MazurTorsion.XOneThirteenProjectiveCurve.curveScheme ℚ,
        e.inv ≫ pullback.fst _ _ = MazurTorsion.XOneThirteenProjectiveCurve.curveToBase ℚ) := by
  exact ⟨⟨MazurTransfer.order13_actual_mixed_quadratic_curve_proper BaseRing,MazurTransfer.order13_actual_dyadic_glued_curve_geometry⟩,inferInstance,MazurTransfer.order13_actual_mixed_quadratic_curve_proper BaseRing,MazurTransfer.order13_actual_dyadic_glued_curve_geometry.1,MazurTransfer.order13_actual_dyadic_glued_curve_geometry.2.1,MazurTransfer.order13_actual_dyadic_glued_curve_geometry.2.2,dyadicGenericFibreIso,dyadicGenericFibreIso_inv_fst⟩
#print axioms solution
