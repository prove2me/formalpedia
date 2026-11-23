-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Averaging.setLIntegral_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:43.647779+00:00
-- url     : https://prove2.me/submissions/89dfb7b4-f3af-44e2-a16a-d2fc0065cec6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ClosedSubgroupQuotientMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuotientMeasureTower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Averaging
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {G₁ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁]
namespace GlobalTheory.CompanionTheory.SW.Averaging
theorem _root_.solution (μ₁ : Measure G₁) [SFinite μ₁] [μ₁.IsMulLeftInvariant]
    [μ₁.IsMulRightInvariant] (Γ₁ : Subgroup G₁) [Countable Γ₁] (𝓕₁ : Set G₁)
    (h𝓕₁ : IsFundamentalDomain Γ₁ 𝓕₁ μ₁) (f : G₁ → ℝ≥0∞)
    (hf : ∀ γ ∈ Γ₁, ∀ u, f (γ * u) = f u) (u₀ : G₁) :
    ∫⁻ u in 𝓕₁, f (u * u₀) ∂μ₁ = ∫⁻ u in 𝓕₁, f u ∂μ₁ := by
  rw [(measurePreserving_mul_right μ₁ u₀).setLIntegral_comp_emb
    (MeasurableEquiv.mulRight u₀).measurableEmbedding f 𝓕₁]
  have h2 : IsFundamentalDomain Γ₁ ((Equiv.mulRight u₀) '' 𝓕₁) μ₁ :=
    h𝓕₁.image_of_equiv (Equiv.mulRight u₀)
      (by
        rw [Equiv.mulRight_symm]
        exact (measurePreserving_mul_right μ₁ u₀⁻¹).quasiMeasurePreserving)
      (Equiv.refl _) (fun g => by
        intro x
        simp only [Equiv.coe_mulRight, Equiv.refl_apply, Subgroup.smul_def, smul_eq_mul, mul_assoc])
  exact h2.setLIntegral_eq h𝓕₁ f (fun g x => by
    rw [Subgroup.smul_def, smul_eq_mul]
    exact hf g g.2 x)
end GlobalTheory.CompanionTheory.SW.Averaging
