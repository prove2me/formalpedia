-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:36:19.600071+00:00
-- url     : https://prove2.me/submissions/ed61cae3-1165-4b64-97dc-6d697468b561

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_density_of_pairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WhitFree.AvgInf GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {T : Type} [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousSMul ℝ T] [T2Space T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  {X H : Type} [MeasurableSpace X] [MeasurableSpace H]
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
theorem _root_.solution (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0)
    (μ : Measure X) (ν : Measure H) (Ψ : H ≃ᵐ T) (hν : (ν.map Ψ).IsAddHaarMeasure)
    (q : X → H) (hq : Measurable q) (P : X → ℝ≥0) (hP : Measurable P)
    (hfin : ∫⁻ x, P x ∂μ ≠ ⊤) (S : Set X) (hS : ∀ x ∈ S, 1 ≤ P x)
    (hi : Integrable (fun b => ∫ x, (P x : ℂ) * Complex.exp (2 * π * I * ((B (Ψ b) (Ψ (q x)) : ℝ) : ℂ)) ∂μ) ν) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ Y, MeasurableSet Y → μ (S ∩ q ⁻¹' Y) ≤ C * ν Y := by
  have hΨq : Measurable fun x => Ψ (q x) := Ψ.measurable.comp hq
  let μP : Measure X := μ.withDensity fun x => (P x : ℝ≥0∞)
  let m : Measure T := μP.map fun x => Ψ (q x)
  haveI : IsFiniteMeasure μP := isFiniteMeasure_withDensity hfin
  haveI : IsFiniteMeasure m := Measure.isFiniteMeasure_map μP _
  have hcont : ∀ u : T, Continuous fun y : T => Complex.exp (2 * π * I * ((B u y : ℝ) : ℂ)) := by
    intro u
    have : Continuous fun y : T => B u y := (B u).continuous_of_finiteDimensional
    fun_prop
  have hG : ∀ b : H, ∫ y, Complex.exp (2 * π * I * ((B (Ψ b) y : ℝ) : ℂ)) ∂m =
      ∫ x, (P x : ℂ) * Complex.exp (2 * π * I * ((B (Ψ b) (Ψ (q x)) : ℝ) : ℂ)) ∂μ := by
    intro b
    rw [integral_map hΨq.aemeasurable (hcont _).aestronglyMeasurable,
      integral_withDensity_eq_integral_smul hP]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [NNReal.smul_def, Complex.real_smul]
  have hint : Integrable (fun u => ∫ y, Complex.exp (2 * π * I * ((B u y : ℝ) : ℂ)) ∂m) (ν.map Ψ) := by
    rw [Ψ.measurableEmbedding.integrable_map_iff]
    refine hi.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hG b).symm
  obtain ⟨C, hC, h⟩ := density_of_pairing B hB m (ν.map Ψ) hint
  refine ⟨C, hC, fun Y hY => ?_⟩
  have hY' : MeasurableSet (Ψ.symm ⁻¹' Y) := Ψ.symm.measurable hY
  have h1 := h _ hY'
  rw [Measure.map_apply Ψ.measurable hY', Measure.map_apply hΨq hY'] at h1
  have e1 : Ψ ⁻¹' (Ψ.symm ⁻¹' Y) = Y := by ext y; simp
  have e2 : (fun x => Ψ (q x)) ⁻¹' (Ψ.symm ⁻¹' Y) = q ⁻¹' Y := by ext y; simp
  rw [e1, e2] at h1
  refine le_trans ?_ h1
  have hYq : MeasurableSet (q ⁻¹' Y) := hq hY
  rw [withDensity_apply _ hYq, ← lintegral_indicator hYq]
  calc μ (S ∩ q ⁻¹' Y) ≤ μ ({x | 1 ≤ P x} ∩ q ⁻¹' Y) :=
        measure_mono (Set.inter_subset_inter_left _ fun x hx => hS x hx)
    _ = ∫⁻ x, ({x | 1 ≤ P x} ∩ q ⁻¹' Y).indicator 1 x ∂μ :=
        (lintegral_indicator_one ((measurableSet_le measurable_const hP).inter hYq)).symm
    _ ≤ _ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ {x | 1 ≤ P x} ∩ q ⁻¹' Y
        · have hx1 : (1 : ℝ≥0∞) ≤ P x := by exact_mod_cast hx.1
          simpa [Set.indicator_of_mem hx, Set.indicator_of_mem hx.2] using hx1
        · simp [Set.indicator_of_notMem hx]
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
