-- Prove2me | solution 1 for MeasureTheory.L2.convolutionCLM_isSymmetric_of_conj_neg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/484c0a85-27ad-5ea1-ad4f-4bea15e1240c

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Normed.Operator.Mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg

open scoped Convolution InnerProductSpace ENNReal
open MeasureTheory
set_option autoImplicit false

theorem solution
    (G : Type*) [MeasurableSpace G] [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [T2Space G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure] [MeasureTheory.IsFiniteMeasure μ]
    (f : C(G, ℂ)) (hf : ∀ x, f (-x) = star (f x))
    (T : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (hT : ∀ φ : MeasureTheory.Lp ℂ 2 μ, (T φ : G → ℂ) =ᵐ[μ]
      ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ))) :
    LinearMap.IsSymmetric (T : MeasureTheory.Lp ℂ 2 μ →ₗ[ℂ] MeasureTheory.Lp ℂ 2 μ) := by
  classical
  let toLp₂ : C(G, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp (p := 2) (μ := μ) (𝕜 := ℂ)
  have htoLp_coe : ∀ ψ : C(G, ℂ), (toLp₂ ψ : G → ℂ) =ᵐ[μ] (ψ : G → ℂ) :=
    ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℂ)
  have hp2 : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hdense : DenseRange (toLp₂ : C(G, ℂ) → Lp ℂ 2 μ) :=
    ContinuousMap.toLp_denseRange (p := 2) (μ := μ) (𝕜 := ℂ) (E := ℂ) hp2
  have hconv_ae : ∀ (φ : Lp ℂ 2 μ) (p : G → ℂ), ((φ : G → ℂ) =ᵐ[μ] p) →
      ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (φ : G → ℂ)) =
      ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] p) := by
    intro φ p hφp; ext x
    simp only [convolution, ContinuousLinearMap.mul_apply']
    refine integral_congr_ae ?_
    filter_upwards [(Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving.ae_eq_comp hφp]
      with t ht
    simp only [Function.comp_apply] at ht; rw [ht]

  have hCG : ∀ p q : C(G, ℂ),
      (⟪T (toLp₂ p), toLp₂ q⟫_ℂ : ℂ) = ⟪toLp₂ p, T (toLp₂ q)⟫_ℂ := by
    intro p q
    have hTp : (T (toLp₂ p) : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (p : G → ℂ)) := by
      rw [← hconv_ae (toLp₂ p) p (htoLp_coe p)]; exact hT (toLp₂ p)
    have hTq : (T (toLp₂ q) : G → ℂ) =ᵐ[μ]
        ((f : G → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (q : G → ℂ)) := by
      rw [← hconv_ae (toLp₂ q) q (htoLp_coe q)]; exact hT (toLp₂ q)

    have hLHS : (⟪T (toLp₂ p), toLp₂ q⟫_ℂ : ℂ)
        = ∫ x, (∫ t, starRingEnd ℂ (f t) * starRingEnd ℂ (p (x-t)) * q x ∂μ) ∂μ := by
      calc (⟪T (toLp₂ p), toLp₂ q⟫_ℂ : ℂ)
          = ∫ x, starRingEnd ℂ (((f:G→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (p:G→ℂ)) x) * q x ∂μ := by
            rw [L2.inner_def]
            refine integral_congr_ae ?_
            filter_upwards [hTp, htoLp_coe q] with x h1 h2
            rw [RCLike.inner_apply, h1, h2]; try ring
        _ = ∫ x, (∫ t, starRingEnd ℂ (f t) * starRingEnd ℂ (p (x-t)) * q x ∂μ) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            dsimp only
            rw [convolution, ← integral_conj, ← integral_mul_const]
            refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
            dsimp only
            simp only [ContinuousLinearMap.mul_apply', map_mul]; try ring

    have hRHS : (⟪toLp₂ p, T (toLp₂ q)⟫_ℂ : ℂ)
        = ∫ s, (∫ t, starRingEnd ℂ (f t) * starRingEnd ℂ (p s) * q (s+t) ∂μ) ∂μ := by
      calc (⟪toLp₂ p, T (toLp₂ q)⟫_ℂ : ℂ)
          = ∫ s, starRingEnd ℂ (p s) * (((f:G→ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ, μ] (q:G→ℂ)) s) ∂μ := by
            rw [L2.inner_def]
            refine integral_congr_ae ?_
            filter_upwards [htoLp_coe p, hTq] with x h1 h2
            rw [RCLike.inner_apply, h1, h2]; try ring
        _ = ∫ s, (∫ t, starRingEnd ℂ (f t) * starRingEnd ℂ (p s) * q (s+t) ∂μ) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
          dsimp only
          simp only [convolution, ContinuousLinearMap.mul_apply']

          have hneg : MeasurePreserving (⇑(MeasurableEquiv.neg G)) μ μ :=
            Measure.measurePreserving_neg μ
          rw [← hneg.integral_comp' (g := fun u => f u * q (s - u))]
          simp only [MeasurableEquiv.neg_apply, sub_neg_eq_add]

          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          dsimp only
          rw [show (f (-t) : ℂ) = starRingEnd ℂ (f t) from by
            rw [hf t, starRingEnd_apply]]
          ring
    rw [hLHS, hRHS]

    rw [integral_integral_swap_of_hasCompactSupport
        (f := fun x t => starRingEnd ℂ (f t) * starRingEnd ℂ (p (x-t)) * q x)
        (μ := μ) (ν := μ)
        (((Complex.continuous_conj.comp (f.continuous.comp continuous_snd)).mul
          (Complex.continuous_conj.comp (p.continuous.comp
            (continuous_fst.sub continuous_snd)))).mul (q.continuous.comp continuous_fst))
        (HasCompactSupport.of_compactSpace _),
      integral_integral_swap_of_hasCompactSupport
        (f := fun s t => starRingEnd ℂ (f t) * starRingEnd ℂ (p s) * q (s+t))
        (μ := μ) (ν := μ)
        (((Complex.continuous_conj.comp (f.continuous.comp continuous_snd)).mul
          (Complex.continuous_conj.comp (p.continuous.comp continuous_fst))).mul
          (q.continuous.comp (continuous_fst.add continuous_snd)))
        (HasCompactSupport.of_compactSpace _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    have haddt : MeasurePreserving (⇑(MeasurableEquiv.addRight t)) μ μ :=
      measurePreserving_add_right μ t
    rw [← haddt.integral_comp'
        (g := fun x => starRingEnd ℂ (f t) * starRingEnd ℂ (p (x-t)) * q x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    have haddt_coe : ∀ s, (MeasurableEquiv.addRight t : G → G) s = s + t := fun s => rfl
    simp only [haddt_coe, add_sub_cancel_right]

  intro φ ψ
  have hcl : IsClosed {xy : Lp ℂ 2 μ × Lp ℂ 2 μ |
      (⟪T xy.1, xy.2⟫_ℂ : ℂ) = ⟪xy.1, T xy.2⟫_ℂ} := by
    refine isClosed_eq ?_ ?_
    · exact continuous_inner.comp ((T.continuous.comp continuous_fst).prodMk continuous_snd)
    · exact continuous_inner.comp (continuous_fst.prodMk (T.continuous.comp continuous_snd))
  have hdense2 : Dense (Set.range (Prod.map (toLp₂ : C(G,ℂ)→_) (toLp₂ : C(G,ℂ)→_))) := by
    rw [Set.range_prodMap]; exact hdense.prod hdense
  have hsub : Set.range (Prod.map (toLp₂:C(G,ℂ)→_) (toLp₂:C(G,ℂ)→_)) ⊆
      {xy | (⟪T xy.1, xy.2⟫_ℂ : ℂ) = ⟪xy.1, T xy.2⟫_ℂ} := by
    rintro xy ⟨⟨p,q⟩,heq⟩; rw [← heq]; exact hCG p q
  exact (hcl.closure_subset_iff.mpr hsub) (hdense2 (φ,ψ))

end S_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg
end P2MW
export P2MW.S_MeasureTheory_L2_convolutionCLM_isSymmetric_of_conj_neg (solution)
