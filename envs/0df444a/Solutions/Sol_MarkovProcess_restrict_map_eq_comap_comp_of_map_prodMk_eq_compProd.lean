-- Prove2me | solution 1 for MarkovProcess.restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T17:57:46.410439+00:00
-- url     : https://prove2.me/submissions/b26e56b9-8b66-4171-9c5e-5175325fbae4

import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.CompNotation
open MeasureTheory ProbabilityTheory
variable {Omega beta gamma : Type*} {mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta} {mGamma : MeasurableSpace gamma}

theorem solution
    (mu : @Measure Omega mOmega) [SFinite mu]
    (X : Omega → beta) (hX : @Measurable Omega beta mOmega mBeta X)
    (Y : Omega → gamma) (hY : @Measurable Omega gamma mOmega mGamma Y)
    (kappa : @Kernel beta gamma mBeta mGamma) [IsSFiniteKernel kappa]
    (hJoint : mu.map (fun omega ↦ (X omega, Y omega)) = (mu.map X) ⊗ₘ kappa) :
    ∀ A : Set Omega, MeasurableSet[mBeta.comap X] A →
      (mu.restrict A).map Y =
        (Kernel.comap kappa X hX) ∘ₘ (mu.restrict A) := by
  intro A hA
  obtain ⟨B, hB, rfl⟩ := hA
  ext S hS
  rw [Measure.map_apply hY hS, Measure.restrict_apply (hY hS),
    Measure.bind_apply hS (Kernel.aemeasurable _)]
  have h1 : mu (Y ⁻¹' S ∩ X ⁻¹' B) = (mu.map (fun omega ↦ (X omega, Y omega))) (B ×ˢ S) := by
    rw [Measure.map_apply (hX.prodMk hY) (hB.prod hS)]
    congr 1; ext ω; simp [and_comm]
  rw [h1, hJoint, Measure.compProd_apply_prod hB hS,
    setLIntegral_map hB (kappa.measurable_coe hS) hX]
  simp [Kernel.comap_apply]
