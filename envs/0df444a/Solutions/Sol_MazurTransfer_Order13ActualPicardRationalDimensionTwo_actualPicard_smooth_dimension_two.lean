-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardRationalDimensionTwo.actualPicard_smooth_dimension_two
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T10:25:39.233664+00:00
-- url     : https://prove2.me/submissions/25d8f57a-30d1-4cad-88fb-cac116f92f64

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: relative dimension two for the SAME rational Picard
scheme, deduced from its checked geometric base change and connectedness.
Named downstream consumer: actual nineteen-torsion cardinality over
algebraically closed extensions of the rational base.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Theorems.Thm_MazurTransfer_Order13ActualPicardRationalDimensionTwo_actualPicard_abelian
import Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actualPicard_fibre_dimension_two
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardRationalDimensionTwo Order13ActualGeometricNineteenTorsionCardinality

theorem solution : SmoothOfRelativeDimension 2 actualPicard.toBase := by
  letI : Smooth actualPicard.toBase := actualPicard_abelian.smooth
  have hs : actualPicard.toBase.base ⁻¹' {IsLocalRing.closedPoint ℚ} =
      (Set.univ : Set actualPicard.P) :=
    Set.eq_univ_of_forall fun _ => Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)
  have hc : _root_.IsConnected (Set.univ : Set actualPicard.P) := by
    rw [← hs]
    exact actualPicard_abelian.connectedFibres (IsLocalRing.closedPoint ℚ)
  letI : PreconnectedSpace actualPicard.P := ⟨hc.2⟩
  obtain ⟨g, hg⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace actualPicard.toBase
  letI : SmoothOfRelativeDimension g actualPicard.toBase := hg
  letI : Nonempty actualPicard.P := ⟨actualPicard.zeroSection (IsLocalRing.closedPoint ℚ)⟩
  have heqg : topologicalKrullDim actualPicard.P = g := le_antisymm
    (SmoothOfRelativeDimension.topologicalKrullDim_le actualPicard.toBase g)
    (SmoothOfRelativeDimension.le_topologicalKrullDim actualPicard.toBase g)
  have hf := actualPicard_fibre_dimension_two (IsLocalRing.closedPoint ℚ)
  have heq2 : topologicalKrullDim actualPicard.P = 2 :=
    have e : ↥(actualPicard.toBase.base ⁻¹' {IsLocalRing.closedPoint ℚ}) ≃ₜ actualPicard.P :=
      (Homeomorph.setCongr hs).trans (Homeomorph.Set.univ _)
    (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm.trans hf
  have hg2 : g = 2 := by exact_mod_cast heqg.symm.trans heq2
  exact hg2 ▸ hg

#print axioms solution
