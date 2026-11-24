-- Prove2me | solution 1 for GlobalTheory.JR.SelfDualLat.planch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:02:59.116884+00:00
-- url     : https://prove2.me/submissions/6d08fff9-7835-4ea0-b7d1-0256e4ddbaae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherel
import Theorems.Thm_GlobalTheory_T_selfDual_measure_exists_unique_fourier_inversion
import Theorems.Thm_GlobalTheory_T_unramifiedStandardAddChar_conductor_properties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.SelfDualLat
namespace GlobalTheory.JR.SelfDualLat
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [IsTopologicalAddGroup V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → ∀ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) → ∀ f, IsTest f → ∫ y, ‖fourB μ (fun x y => ψ (β x y)) f y‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  intro F E _ _ _ _ _ ψ hψ V _ _ _ _ _ _ _ _ _ _ _ β hβs hβn μ hsd f hf
  haveI := hsd.1
  have hψ' := (GlobalTheory.T.unramifiedStandardAddChar_conductor_properties F E).2 ψ hψ
  have hI := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ V β hβs hβn
  set B : V → V → ℂ := fun x y => ψ (β x y) with hB
  set g := fourB μ B f with hgdef
  have hg : IsTest g := hI.2 μ hsd.1 f hf
  have hψc : Continuous (fun t : F => ψ t) := hψ'.1.continuous
  have hβc : Continuous (fun p : V × V => β p.1 p.2) := IsModuleTopology.continuous_bilinear_of_finite_left β
  have hfc : Continuous f := hf.1.continuous
  have hgc : Continuous g := hg.1.continuous
  have hfi : Integrable f μ := hfc.integrable_of_hasCompactSupport hf.2
  have hgi : Integrable g μ := hgc.integrable_of_hasCompactSupport hg.2
  have key : ∀ h : V → ℂ, ((∫ y, ‖h y‖ ^ 2 ∂μ : ℝ) : ℂ) = ∫ y, h y * (starRingEnd ℂ) (h y) ∂μ := by
    intro h
    rw [← integral_complex_ofReal]
    congr 1; ext y
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hconj : ∀ t : F, (starRingEnd ℂ) (ψ t) = ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv]
    have h1 : ‖ψ t‖ = 1 := hψ'.2.1 t
    have h0 : ψ t ≠ 0 := by intro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
  have hinner : ∀ x, ∫ y, ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ = (starRingEnd ℂ) (f x) := by
    intro x
    have := hsd.2 f hf (-x)
    rw [neg_neg] at this
    rw [← this]
    show _ = (starRingEnd ℂ) (∫ y, g y * B y (-x) ∂μ)
    rw [← integral_conj]
    congr 1; ext y
    rw [map_mul, hconj]
    simp only [map_neg, neg_neg, hβs.eq x y]
    ring
  have hint : Integrable (Function.uncurry fun y x => f x * ψ (β x y) * (starRingEnd ℂ) (g y)) (μ.prod μ) := by
    refine Integrable.mono' ((hgi.norm).mul_prod hfi.norm) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hfc.comp continuous_snd).mul (hψc.comp (hβc.comp continuous_swap))).mul
        (Complex.continuous_conj.comp (hgc.comp continuous_fst))
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, norm_mul, hψ'.2.1, mul_one, Complex.norm_conj]
      rw [mul_comm]
  apply Complex.ofReal_injective
  rw [key, key]
  calc ∫ y, g y * (starRingEnd ℂ) (g y) ∂μ
      = ∫ y, ∫ x, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := by
        congr 1; ext y
        rw [hgdef]; unfold fourB
        rw [← integral_mul_const]
    _ = ∫ x, ∫ y, f x * ψ (β x y) * (starRingEnd ℂ) (g y) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ x, f x * (starRingEnd ℂ) (f x) ∂μ := by
        congr 1; ext x
        simp_rw [mul_assoc]
        rw [integral_const_mul, hinner]
end GlobalTheory.JR.SelfDualLat
