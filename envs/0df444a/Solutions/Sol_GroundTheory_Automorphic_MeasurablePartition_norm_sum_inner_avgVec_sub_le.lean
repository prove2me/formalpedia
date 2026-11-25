-- Prove2me | solution 1 for GroundTheory.Automorphic.MeasurablePartition.norm_sum_inner_avgVec_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:40.34919+00:00
-- url     : https://prove2.me/submissions/14b37484-7e69-45b2-863f-2942f64ed4cc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TraceStrongLimit
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtKernel
import Definitions.Def_GroundTheory_AutomorphicForms_KernelTrace
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_measureReal_pos
import Theorems.Thm_GroundTheory_Automorphic_integrable_of_continuous_compact
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_inner_avgVec_contKernelOp
import Theorems.Thm_GroundTheory_Automorphic_MeasurablePartition_biUnion_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Filter Topology Uniformity Set
open scoped InnerProductSpace ENNReal ComplexConjugate NNReal
noncomputable section
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
open GroundTheory.Automorphic.MeasurablePartition
variable (p : MeasurablePartition X)
namespace GroundTheory.Automorphic.MeasurablePartition
theorem _root_.solution (k : C(X × X, ℂ)) {ε : ℝ}
    (hk : ∀ i, ∀ x ∈ p.E i, ∀ y ∈ p.E i, ‖k (x, y) - k (x, x)‖ ≤ ε) :
    ‖∑ i : p.nonnull μ, ⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
      ∫ x, k (x, x) ∂μ‖ ≤ ε * μ.real univ := by
  have hkm : StronglyMeasurable (k : X × X → ℂ) :=
    (measurable_of_continuous_compactProd k.continuous).stronglyMeasurable
  have hdiag : Continuous fun x => k (x, x) := k.continuous.comp (continuous_id.prodMk continuous_id)
  have hrow : ∀ x, Continuous fun y => k (x, y) := fun x => k.continuous.comp
    (continuous_const.prodMk continuous_id)

  have hsplit : ∫ x, k (x, x) ∂μ = ∑ i : p.nonnull μ, ∫ x in p.E i, k (x, x) ∂μ := by
    rw [← setIntegral_univ, ← p.biUnion_eq, integral_biUnion_finset _
      (fun i _ => p.measurableSet i) (fun i _ j _ hij => p.disjoint hij)
      (fun i _ => (integrable_of_continuous_compact hdiag μ).integrableOn),
      Finset.sum_coe_sort (p.nonnull μ) (fun i => ∫ x in p.E i, k (x, x) ∂μ), nonnull,
      Finset.sum_filter_of_ne]
    intro i _ hne hzero
    exact hne (setIntegral_measure_zero _ hzero)
  rw [hsplit, ← Finset.sum_sub_distrib]

  have hpiece : ∀ i : p.nonnull μ, ‖(((μ.real (p.E i))⁻¹ : ℝ) : ℂ) *
      (∫ x in p.E i, ∫ y in p.E i, k (x, y) ∂μ ∂μ) - ∫ x in p.E i, k (x, x) ∂μ‖ ≤
      ε * μ.real (p.E i) := by
    intro i
    set E := p.E i
    set m := μ.real E
    have hm : 0 < m := measureReal_pos i
    have hEfin : μ E < ∞ := measure_lt_top μ E
    let F : X → ℂ := fun x => ∫ y in E, k (x, y) ∂μ
    have hFint : Integrable F (μ.restrict E) := by
      refine Integrable.of_bound (hkm.integral_prod_right' (ν := μ.restrict E)).aestronglyMeasurable
        (‖k‖ * m) (ae_of_all _ fun x => ?_)
      exact norm_setIntegral_le_of_norm_le_const hEfin fun y _ => k.norm_coe_le_norm _
    have hGint : Integrable (fun x => (m : ℂ) * k (x, x)) (μ.restrict E) :=
      (integrable_of_continuous_compact hdiag _).const_mul _
    have hdiagE : ∫ x in E, k (x, x) ∂μ =
        ((m⁻¹ : ℝ) : ℂ) * ∫ x in E, (m : ℂ) * k (x, x) ∂μ := by
      rw [integral_const_mul, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne',
        Complex.ofReal_one, one_mul]
    rw [hdiagE, ← mul_sub, ← integral_sub hFint hGint, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 hm)]
    have hbound : ‖∫ x in E, (F x - (m : ℂ) * k (x, x)) ∂μ‖ ≤ (ε * m) * m := by
      refine norm_setIntegral_le_of_norm_le_const hEfin fun x hx => ?_
      have hrowE : Integrable (fun y => k (x, y)) (μ.restrict E) :=
        integrable_of_continuous_compact (hrow x) _
      have hconst : (m : ℂ) * k (x, x) = ∫ _ in E, k (x, x) ∂μ := by
        rw [setIntegral_const, Complex.real_smul]
      simp only [F]
      rw [hconst, ← integral_sub hrowE (integrable_const _)]
      exact norm_setIntegral_le_of_norm_le_const hEfin fun y hy => hk i x hx y hy
    calc m⁻¹ * ‖∫ x in E, (F x - (m : ℂ) * k (x, x)) ∂μ‖ ≤ m⁻¹ * ((ε * m) * m) := by
          gcongr
      _ = ε * m := by field_simp
  calc ‖∑ i : p.nonnull μ, (⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
        ∫ x in p.E i, k (x, x) ∂μ)‖
      ≤ ∑ i : p.nonnull μ, ‖⟪p.avgVec μ i, contKernelOp μ k (p.avgVec μ i)⟫_ℂ -
        ∫ x in p.E i, k (x, x) ∂μ‖ := norm_sum_le _ _
    _ ≤ ∑ i : p.nonnull μ, ε * μ.real (p.E i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [inner_avgVec_contKernelOp]
        exact hpiece i
    _ = ε * ∑ i ∈ p.nonnull μ, μ.real (p.E i) := by
        rw [← Finset.mul_sum, Finset.sum_coe_sort (p.nonnull μ) (fun i => μ.real (p.E i))]
    _ = ε * μ.real univ := by
        congr 1
        rw [nonnull, Finset.sum_filter_of_ne, ← measureReal_biUnion_finset
          (fun i _ j _ hij => p.disjoint hij) (fun i _ => p.measurableSet i), p.biUnion_eq]
        intro i _ hne hzero
        exact hne (by simp [Measure.real, hzero])
end GroundTheory.Automorphic.MeasurablePartition
