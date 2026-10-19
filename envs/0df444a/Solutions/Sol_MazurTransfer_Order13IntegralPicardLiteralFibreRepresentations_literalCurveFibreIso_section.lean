-- Prove2me | solution 1 for MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations.literalCurveFibreIso_section
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T04:20:25.956393+00:00
-- url     : https://prove2.me/submissions/85859229-0dd8-41d3-9b2a-df9fbcf94aa2

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual literal fibre isomorphism carries the positive
infinity section to its base change. Named downstream consumer: transport
of the actual integral Picard representation to the literal field fibre.
The original projection proof is preserved. -/
import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_Order13LiteralCurveFibreIsomorphism
import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
import Theorems.Thm_MazurTransfer_Order13IntegralSections_infinityMorphism_baseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections MazurTransfer.Order13ActualCurveBaseChange
open MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
universe u
theorem solution (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    (positiveInfinitySection S).val ≫ (literalCurveFibreIso R S).hom =
      (sectionBaseChange S (positiveInfinitySection R)).val := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    change (positiveInfinitySection S).val ≫
      (wholeCurve_isPullback R S).isoPullback.hom ≫ pullback.fst _ _ = _
    rw [(wholeCurve_isPullback R S).isoPullback_hom_fst,sectionBaseChange_coe_fst]
    simpa only [positiveInfinitySection,infinitySection,map_one] using
      infinityMorphism_baseChange R S 1 (by simp)
  · rw [Category.assoc]
    change (positiveInfinitySection S).val ≫
      ((literalCurveFibreIso R S).hom ≫ baseChange R (curveToBase R) S) = _
    rw [literalCurveFibreIso_over,sectionBaseChange_coe_snd]
    exact (positiveInfinitySection S).property
#print axioms solution
