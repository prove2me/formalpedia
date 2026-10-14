-- Prove2me | solution 1 for NewtonGravitation.gravField_at_origin_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-14T06:50:00.681588+00:00
-- url     : https://prove2.me/submissions/b4749f92-e38b-4562-9eab-fb2907d4f4ef

import Definitions.Def_NewtonGravitation_Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory NewtonGravitation

theorem solution (μ : Measure Space)
    (hμ : IsSphericallySymmetric μ) : gravField μ (0 : Space) = 0 := by
  classical
  let A : Space ≃ₗᵢ[ℝ] Space := LinearIsometryEquiv.neg ℝ
  let f : Space → Space := fun y =>
    -(G / ‖(0 : Space) - y‖ ^ 3) • ((0 : Space) - y)
  have hA : μ.map A = μ := hμ A
  have hme : MeasurableEmbedding (A : Space → Space) :=
    A.toHomeomorph.measurableEmbedding
  have hfodd (y : Space) : f (A y) = -f y := by
    change f (-y) = -f y
    simp [f, norm_neg, smul_neg, neg_smul]
  have hneg : (∫ y, f y ∂μ) = -(∫ y, f y ∂μ) := by
    calc
      (∫ y, f y ∂μ) = ∫ y, f y ∂(μ.map A) := by rw [hA]
      _ = ∫ y, f (A y) ∂μ := hme.integral_map f
      _ = ∫ y, -f y ∂μ := by simp_rw [hfodd]
      _ = -(∫ y, f y ∂μ) := by exact integral_neg f
  have htwo : (∫ y, f y ∂μ) + (∫ y, f y ∂μ) = 0 := by
    calc
      _ = -(∫ y, f y ∂μ) + (∫ y, f y ∂μ) := by
        exact congrArg (fun z : Space => z + (∫ y, f y ∂μ)) hneg
      _ = 0 := neg_add_cancel _
  have hsmul : (2 : ℝ) • (∫ y, f y ∂μ) = 0 := by
    simpa only [two_smul] using htwo
  change (∫ y, f y ∂μ) = 0
  exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
