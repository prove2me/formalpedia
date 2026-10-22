-- Prove2me | solution 1 for JHolomorphic.eLpNorm_fderiv_lift_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T22:40:15.241909+00:00
-- url     : https://prove2.me/submissions/2426ac2a-9ea8-4638-ad70-79ad4aea8544

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Analysis.Calculus.FDeriv.Measurable



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem norm_fderiv_lift_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℂ → E)
    (z e : ℂ) (he : ‖e‖ ≤ 1) (hd1 : DifferentiableAt ℝ u z)
    (hd2 : DifferentiableAt ℝ (fderiv ℝ u) z) :
    ‖fderiv ℝ (fun z => (u z, fderiv ℝ u z e)) z‖ ≤
      ‖fderiv ℝ u z‖ + ‖fderiv ℝ (fderiv ℝ u) z‖ := by
  have h := hd1.hasFDerivAt.prodMk (hd2.hasFDerivAt.clm_apply (hasFDerivAt_const e z))
  rw [h.fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply]
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · calc ‖fderiv ℝ u z w‖ ≤ ‖fderiv ℝ u z‖ * ‖w‖ := (fderiv ℝ u z).le_opNorm w
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (norm_nonneg (fderiv ℝ (fderiv ℝ u) z))
  · calc ‖fderiv ℝ (fderiv ℝ u) z w e‖ ≤ ‖fderiv ℝ (fderiv ℝ u) z w‖ * ‖e‖ :=
          (fderiv ℝ (fderiv ℝ u) z w).le_opNorm e
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) z w‖ := mul_le_of_le_one_right (norm_nonneg _) he
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) z‖ * ‖w‖ := (fderiv ℝ (fderiv ℝ u) z).le_opNorm w
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left (norm_nonneg (fderiv ℝ u z))

theorem eLpNorm_fderiv_lift_le_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 ≤ p) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E)
    (hu : ContDiffOn ℝ ∞ u U) (e : ℂ) (he : ‖e‖ ≤ 1) (K' : Set ℂ) (hK'U : K' ⊆ U)
    (hK' : IsCompact K') (C₁ C₂ : ℝ≥0)
    (h1 : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict K') ≤ C₁)
    (h2 : eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict K') ≤ C₂) :
    eLpNorm (fderiv ℝ (fun z => (u z, fderiv ℝ u z e))) (ENNReal.ofReal p)
      (volume.restrict K') ≤ (C₁ + C₂ : ℝ≥0) := by
  have hDu : ContDiffOn ℝ ∞ (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (show (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) from le_of_eq (by norm_cast))
  have hpt : ∀ z ∈ K', ‖fderiv ℝ (fun z => (u z, fderiv ℝ u z e)) z‖ ≤
      ‖fderiv ℝ u z‖ + ‖fderiv ℝ (fderiv ℝ u) z‖ := fun z hz =>
    norm_fderiv_lift_le_aux u z e he
      ((hu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hK'U hz)))
      ((hDu.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hK'U hz)))
  have hm1 : AEStronglyMeasurable (fun z => ‖fderiv ℝ u z‖) (volume.restrict K') :=
    (measurable_fderiv ℝ u).norm.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun z => ‖fderiv ℝ (fderiv ℝ u) z‖) (volume.restrict K') :=
    (measurable_fderiv ℝ (fderiv ℝ u)).norm.aestronglyMeasurable
  calc eLpNorm (fderiv ℝ (fun z => (u z, fderiv ℝ u z e))) (ENNReal.ofReal p)
        (volume.restrict K')
      ≤ eLpNorm (fun z => ‖fderiv ℝ u z‖ + ‖fderiv ℝ (fderiv ℝ u) z‖)
          (ENNReal.ofReal p) (volume.restrict K') := by
        refine eLpNorm_mono_ae ?_
        filter_upwards [ae_restrict_mem hK'.measurableSet] with z hz
        exact (hpt z hz).trans (le_abs_self _)
    _ ≤ eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p) (volume.restrict K') +
        eLpNorm (fun z => ‖fderiv ℝ (fderiv ℝ u) z‖) (ENNReal.ofReal p) (volume.restrict K') :=
        eLpNorm_add_le hm1 hm2 (by rw [ENNReal.one_le_ofReal]; linarith)
    _ ≤ C₁ + C₂ := by
        have e1 : eLpNorm (fun z => ‖fderiv ℝ u z‖) (ENNReal.ofReal p) (volume.restrict K') ≤ C₁ :=
          (eLpNorm_norm (fderiv ℝ u)).trans_le h1
        have e2 : eLpNorm (fun z => ‖fderiv ℝ (fderiv ℝ u) z‖) (ENNReal.ofReal p)
            (volume.restrict K') ≤ C₂ :=
          (eLpNorm_norm (fderiv ℝ (fderiv ℝ u))).trans_le h2
        exact add_le_add e1 e2
    _ = ((C₁ + C₂ : ℝ≥0) : ℝ≥0∞) := (ENNReal.coe_add _ _).symm

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 ≤ p) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E)
    (hu : ContDiffOn ℝ ∞ u U) (e : ℂ) (he : ‖e‖ ≤ 1) (K' : Set ℂ) (hK'U : K' ⊆ U)
    (hK' : IsCompact K') (C₁ C₂ : ℝ≥0)
    (h1 : eLpNorm (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict K') ≤ C₁)
    (h2 : eLpNorm (fderiv ℝ (fderiv ℝ u)) (ENNReal.ofReal p) (volume.restrict K') ≤ C₂) :
    eLpNorm (fderiv ℝ (fun z => (u z, fderiv ℝ u z e))) (ENNReal.ofReal p)
      (volume.restrict K') ≤ (C₁ + C₂ : ℝ≥0) :=
  eLpNorm_fderiv_lift_le_aux p hp U hU u hu e he K' hK'U hK' C₁ C₂ h1 h2
