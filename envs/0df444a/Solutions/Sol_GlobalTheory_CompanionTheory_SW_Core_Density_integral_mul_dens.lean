-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Density.integral_mul_dens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:29:30.025452+00:00
-- url     : https://prove2.me/submissions/53aa7c19-1c56-466f-ad99-69449ecbd9ff

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_chi_neg_left
import Theorems.Thm_GlobalTheory_T_fourier_inversion_schwartz_bruhat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
variable [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
  [BorelSpace V]
namespace GlobalTheory.CompanionTheory.SW.Core.Density
theorem _root_.solution {χ : V → V → ℂ} {μ m : Measure V} [μ.IsAddHaarMeasure] [IsFiniteMeasure m]
    (h : NADual V χ μ) (hc : Continuous (fun p : V × V => χ p.1 p.2)) (hs : ∀ x y, χ x y = χ y x)
    (hn : ∀ x y, ‖χ x y‖ = 1) (ha : ∀ x x' y, χ (x + x') y = χ x y * χ x' y)
    (hint : Integrable (mhat χ m) μ) {φ : V → ℂ} (hφ : SB φ) :
    ∫ x, φ x * dens χ μ m x ∂μ = ∫ z, φ z ∂m := by
  obtain ⟨hsb, hinv⟩ := GlobalTheory.T.fourier_inversion_schwartz_bruhat V χ μ h φ hφ
  have hφi : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  have hfi : Integrable (fou χ μ φ) μ := hsb.1.continuous.integrable_of_hasCompactSupport hsb.2
  have hfni : Integrable (fun y => fou χ μ φ (-y)) μ := hfi.comp_neg
  have hF : Integrable (Function.uncurry fun x y => φ x * (mhat χ m y * χ (-x) y)) (μ.prod μ) := by
    have h1 : Integrable (fun p : V × V => φ p.1 * mhat χ m p.2) (μ.prod μ) := hφi.mul_prod hint
    have h2 := h1.mul_bdd (c := 1) (g := fun p : V × V => χ (-p.1) p.2)
      (hc.comp ((continuous_neg.comp continuous_fst).prodMk continuous_snd)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simp [hn])
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry, mul_assoc]
  have hH : Integrable (Function.uncurry fun y z => fou χ μ φ (-y) * χ z y) (μ.prod m) := by
    have h1 : Integrable (fun p : V × V => fou χ μ φ (-p.1) * (1 : ℂ)) (μ.prod m) :=
      hfni.mul_prod (integrable_const (1 : ℂ))
    have h2 := h1.mul_bdd (c := 1) (g := fun p : V × V => χ p.2 p.1)
      (hc.comp (continuous_snd.prodMk continuous_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by simp [hn])
    refine h2.congr (Filter.Eventually.of_forall fun p => ?_)
    simp [Function.uncurry]
  calc ∫ x, φ x * dens χ μ m x ∂μ
      = ∫ x, ∫ y, φ x * (mhat χ m y * χ (-x) y) ∂μ ∂μ := by
        simp only [dens, integral_const_mul]
    _ = ∫ y, ∫ x, φ x * (mhat χ m y * χ (-x) y) ∂μ ∂μ := integral_integral_swap hF
    _ = ∫ y, ∫ z, fou χ μ φ (-y) * χ z y ∂m ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        have e1 : ∀ x, φ x * (mhat χ m y * χ (-x) y) = mhat χ m y * (φ x * χ x (-y)) := fun x => by
          rw [chi_neg_left hs hn ha]; ring
        simp only [e1]
        rw [integral_const_mul, integral_const_mul, mul_comm]
        rfl
    _ = ∫ z, ∫ y, fou χ μ φ (-y) * χ z y ∂μ ∂m := integral_integral_swap hH
    _ = ∫ z, φ z ∂m := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        have e2 : ∫ y, fou χ μ φ (-y) * χ z y ∂μ = ∫ y, fou χ μ φ y * χ z (-y) ∂μ := by
          rw [← integral_neg_eq_self (fun y => fou χ μ φ y * χ z (-y)) μ]
          simp
        have e3 : ∀ y, χ z (-y) = χ y (-z) := fun y => by
          rw [← chi_neg_left hs hn ha, hs]
        simp only [e2, e3]
        have := hinv (-z)
        simpa [fou] using this
end GlobalTheory.CompanionTheory.SW.Core.Density
