-- Prove2me | solution 1 for GlobalTheory.HeckeStrip.completed_pSeries_entire_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:29:52.943955+00:00
-- url     : https://prove2.me/submissions/a1e5e556-7fb0-4f14-b161-a2bb6cf39708

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplaceIntegralEntireBoundedInVerticalStripsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMeasurablePartitionOfUnityUnitLogTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpaceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodicBoundedGaussianSummableCmTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeThetaKernelPoissonSummationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ArchFactorMulPSeriesEqIntegralStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MellinIntegralSplitFunctionalEquationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompletedHeckePartialLSeriesEntireBoundedStrips
import Theorems.Thm_GlobalTheory_CMVal_Model_IntAt_add
import Theorems.Thm_GlobalTheory_CMVal_Model_IntAt_mul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_T_archFactor_mul_pSeries_eq_integral_alt
import Theorems.Thm_GlobalTheory_T_exists_measurable_partitionOfUnity_unitLogTranslates
import Theorems.Thm_GlobalTheory_T_heckeThetaKernel_poisson_summation
import Theorems.Thm_GlobalTheory_T_integrable_weighted_heckeThetaKernel_halfSpace
import Theorems.Thm_GlobalTheory_T_laplace_integral_entire_boundedInVerticalStrips
import Theorems.Thm_GlobalTheory_T_mellin_integral_split_functional_equation
import Theorems.Thm_GlobalTheory_T_periodic_bounded_gaussian_summable_cmType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeStrip
namespace GlobalTheory.HeckeStrip
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := GlobalTheory.T.periodic_bounded_gaussian_summable_cmType K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := GlobalTheory.T.heckeThetaKernel_poisson_summation K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]
end GlobalTheory.HeckeStrip
