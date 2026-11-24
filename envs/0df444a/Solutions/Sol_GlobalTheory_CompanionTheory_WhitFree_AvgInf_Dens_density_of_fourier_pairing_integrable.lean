-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens.density_of_fourier_pairing_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:58.08634+00:00
-- url     : https://prove2.me/submissions/d92f05b9-02bf-4b7f-a7d8-7c78002b3450

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_WhitFree_AvgInf_Dens_measure_le

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
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
theorem _root_.solution (e : T ≃ₗ[ℝ] V) (B : T →ₗ[ℝ] T →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0)
    (m : Measure T) [IsFiniteMeasure m] (ν : Measure T) [ν.IsAddHaarMeasure]
    (hi : Integrable (fun u => ∫ y, Complex.exp (2 * π * I * ((B u y : ℝ) : ℂ)) ∂m) ν) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ Y, MeasurableSet Y → m Y ≤ C * ν Y := by
  let eC : T ≃L[ℝ] V := e.toContinuousLinearEquiv
  have hDinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    exact hB u fun v => by rw [hu]; rfl
  let D : T ≃ₗ[ℝ] Module.Dual ℝ T :=
    LinearMap.linearEquivOfInjective B hDinj (Subspace.dual_finrank_eq).symm
  let L0 : V →ₗ[ℝ] T := D.symm.toLinearMap ∘ₗ ((innerₗ V).compl₂ e.toLinearMap)
  have hL0 : ∀ ξ y, B (L0 ξ) y = ⟪ξ, e y⟫ := by
    intro ξ y
    have h : B (L0 ξ) = (innerₗ V).compl₂ e.toLinearMap ξ := D.apply_symm_apply _
    rw [h]
    rfl
  have hinj : Function.Injective L0 := by
    rw [injective_iff_map_eq_zero]
    intro ξ hξ
    have h := hL0 ξ (e.symm ξ)
    rw [hξ, map_zero, LinearMap.zero_apply, e.apply_symm_apply] at h
    exact inner_self_eq_zero.1 h.symm
  let L : V ≃ₗ[ℝ] T := LinearMap.linearEquivOfInjective L0 hinj e.finrank_eq.symm
  let LC : V ≃L[ℝ] T := L.toContinuousLinearEquiv
  have hLC : ∀ ξ y, B (LC ξ) y = ⟪ξ, e y⟫ := hL0
  set G : T → ℂ := fun u => ∫ y, Complex.exp (2 * π * I * ((B u y : ℝ) : ℂ)) ∂m with hG
  let m' : Measure V := m.map eC
  haveI : IsFiniteMeasure m' := Measure.isFiniteMeasure_map m _
  have hchf : chf m' = fun ξ => G (LC ξ) := by
    funext ξ
    rw [chf, integral_map eC.continuous.measurable.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hLC, real_inner_comm]
    rfl
  have hint : Integrable (chf m') := by
    have h1 : ((volume : Measure V).map LC).IsAddHaarMeasure := LC.isAddHaarMeasure_map _
    have h2 := Measure.isAddLeftInvariant_eq_smul ((volume : Measure V).map LC) ν
    have h3 : Integrable G ((volume : Measure V).map LC) := by
      rw [h2]
      exact hi.smul_measure_nnreal
    have h4 := (LC.toHomeomorph.measurableEmbedding.integrable_map_iff).1 h3
    rw [hchf]
    exact h4
  refine ⟨ENNReal.ofReal (∫ ξ, ‖chf m' ξ‖) *
    (Measure.addHaarScalarFactor ((volume : Measure V).map eC.symm) ν : ℝ≥0∞), ?_, fun Y hY => ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have h1 : ((volume : Measure V).map eC.symm).IsAddHaarMeasure := eC.symm.isAddHaarMeasure_map _
  have h2 := Measure.isAddLeftInvariant_eq_smul ((volume : Measure V).map eC.symm) ν
  have hY' : MeasurableSet (eC.symm ⁻¹' Y) := eC.symm.continuous.measurable hY
  have h3 : m Y = m' (eC.symm ⁻¹' Y) := by
    rw [Measure.map_apply eC.continuous.measurable hY']
    congr 1
    ext y
    simp
  have h4 : volume (eC.symm ⁻¹' Y) = (Measure.addHaarScalarFactor ((volume : Measure V).map eC.symm) ν : ℝ≥0∞) * ν Y := by
    rw [← Measure.map_apply eC.symm.continuous.measurable hY]
    exact (congrArg (fun μ : Measure T => μ Y) h2).trans (Measure.nnreal_smul_coe_apply _ _ _)
  rw [h3, mul_assoc, ← h4]
  exact measure_le m' hint hY'
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
