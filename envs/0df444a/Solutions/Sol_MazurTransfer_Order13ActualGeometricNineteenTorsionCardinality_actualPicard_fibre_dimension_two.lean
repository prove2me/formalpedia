-- Prove2me | solution 1 for MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actualPicard_fibre_dimension_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T10:09:38.337403+00:00
-- url     : https://prove2.me/submissions/20562b64-5b3a-46e0-a570-9a9bc61234a6

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: relative dimension two for the SAME rational Picard
scheme, deduced from its checked geometric base change and connectedness.
Named downstream consumer: actual nineteen-torsion cardinality over
algebraically closed extensions of the rational base.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Theorems.Thm_MazurTransfer_Order13ActualPicardRationalDimensionTwo_actualPicard_abelian
import Theorems.Thm_MazurTransfer_Order13ActualPicardDimensionTwo_actualPicard_baseChange_smooth_dimension_two
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardRationalDimensionTwo Order13ActualPicardDimensionTwo

private theorem rationalPicardDimensionTwoOriginalProof20261018 : SmoothOfRelativeDimension 2 actualPicard.toBase := by
  letI : Smooth actualPicard.toBase := actualPicard_abelian.smooth
  have hs : actualPicard.toBase.base ⁻¹' {IsLocalRing.closedPoint ℚ} =
      (Set.univ : Set actualPicard.P) :=
    Set.eq_univ_of_forall fun _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  have hc : _root_.IsConnected (Set.univ : Set actualPicard.P) := by
    rw [← hs]
    exact actualPicard_abelian.connectedFibres (IsLocalRing.closedPoint ℚ)
  letI : PreconnectedSpace actualPicard.P := ⟨hc.2⟩
  obtain ⟨g, hg⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace actualPicard.toBase
  let Ω := AlgebraicClosure ℚ
  let D := actualPicard.baseChange Ω
  letI : SmoothOfRelativeDimension g actualPicard.toBase := hg
  letI := smoothOfRelativeDimension_isStableUnderBaseChange g
  letI : SmoothOfRelativeDimension g D.toBase :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g)
      (IsPullback.of_hasPullback actualPicard.toBase (SmoothProperCurve.specMap ℚ Ω)) hg
  letI : SmoothOfRelativeDimension 2 D.toBase := actualPicard_baseChange_smooth_dimension_two Ω
  letI : Nonempty D.P := ⟨D.zeroSection (IsLocalRing.closedPoint Ω)⟩
  have heqg : topologicalKrullDim D.P = g := le_antisymm
    (SmoothOfRelativeDimension.topologicalKrullDim_le D.toBase g)
    (SmoothOfRelativeDimension.le_topologicalKrullDim D.toBase g)
  have heq2 : topologicalKrullDim D.P = 2 := le_antisymm
    (SmoothOfRelativeDimension.topologicalKrullDim_le D.toBase 2)
    (SmoothOfRelativeDimension.le_topologicalKrullDim D.toBase 2)
  have hg2 : g = 2 := by exact_mod_cast heqg.symm.trans heq2
  exact hg2 ▸ hg

theorem solution (s : Spec (CommRingCat.of ℚ)) :
    topologicalKrullDim ↥(actualPicard.toBase.base ⁻¹' {s}) = 2 := by
  letI : SmoothOfRelativeDimension 2 actualPicard.toBase := rationalPicardDimensionTwoOriginalProof20261018
  letI : Nonempty actualPicard.P := ⟨actualPicard.zeroSection (IsLocalRing.closedPoint ℚ)⟩
  have heq : actualPicard.toBase.base ⁻¹' {s} = Set.univ :=
    Set.eq_univ_of_forall fun _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  rw [heq]
  have hdim := le_antisymm
    (SmoothOfRelativeDimension.topologicalKrullDim_le actualPicard.toBase 2)
    (SmoothOfRelativeDimension.le_topologicalKrullDim actualPicard.toBase 2)
  exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).trans hdim


#print axioms solution
