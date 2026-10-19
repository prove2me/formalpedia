-- Prove2me | solution 1 for MazurTransfer.IntegralSurjectiveOverGeometricPointLifting.exists_over_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T21:30:27.774858+00:00
-- url     : https://prove2.me/submissions/78b97e46-c205-4a9d-9bdf-d4c8cedd9ee0

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete Anthropic FLT field-point lifting proof at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: lift a geometric point along an integral surjective
endomorphism while preserving its specified map to the base scheme.
Named downstream consumer: the two actual order-13 Picard norm maps.
-/
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_comp_eq_of_isIntegralHom_of_surjective

noncomputable section
open CategoryTheory AlgebraicGeometry

theorem solution {S X : Scheme.{0}} (t : X ⟶ S)
    (φ : Over.mk t ⟶ Over.mk t) [IsIntegralHom φ.left] [Surjective φ.left]
    (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Over.mk s ⟶ Over.mk t) :
    ∃ b : Over.mk s ⟶ Over.mk t, b ≫ φ = a := by
  obtain ⟨b, hb⟩ := Scheme.Hom.exists_comp_eq_of_isIntegralHom_of_surjective φ.left K a.left
  have hwφ : φ.left ≫ t = t := Over.w φ
  have hwa : a.left ≫ t = s := Over.w a
  have hw : b ≫ t = s := by
    calc
      b ≫ t = b ≫ φ.left ≫ t := by rw [hwφ]
      _ = a.left ≫ t := by rw [← Category.assoc, hb]
      _ = s := hwa
  refine ⟨Over.homMk b hw, ?_⟩
  apply Over.OverMorphism.ext
  exact hb


#print axioms solution
