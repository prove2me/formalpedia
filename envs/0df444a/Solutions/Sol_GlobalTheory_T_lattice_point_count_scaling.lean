-- Prove2me | solution 1 for GlobalTheory.T.lattice_point_count_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:17:15.170808+00:00
-- url     : https://prove2.me/submissions/cc8b4efb-2d0c-4b49-b8e1-610e78db61e4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScaling
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LatticePointCountScalingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RiemannCore_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (Λ : AddSubgroup G) [Countable Λ] (D K₀ : Set G) (R : Finset G) (T : ℝ → G →+ G) (M : ℕ), MeasurableSet D → IsCompact K₀ → D ⊆ K₀ → μ D = 1 → (∀ y : G, ∃! p : G × G, p.1 ∈ R ∧ p.2 ∈ Λ ∧ y - p.1 - p.2 ∈ D) → (∀ ε : ℝ, 0 < ε → Continuous (T ε)) → (∀ ε : ℝ, 0 < ε → ∀ y, T ε⁻¹ (T ε y) = y ∧ T ε (T ε⁻¹ y) = y) → (∀ ε : ℝ, 0 < ε → Measure.map (T ε) μ = ENNReal.ofReal ((ε ^ M)⁻¹) • μ) → (∀ B : Set G, IsCompact B → ∀ U ∈ 𝓝 (0 : G), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ b ∈ B, T ε b ∈ U) → ∀ (x0 : G) (φ : G → ℝ), Continuous φ → HasCompactSupport φ → (∀ ε : ℝ, 0 < ε → Summable fun l : Λ => φ (T ε (x0 + l))) ∧ Tendsto (fun ε : ℝ => ε ^ M * ∑' l : Λ, φ (T ε (x0 + l))) (𝓝[>] 0) (𝓝 ((R.card : ℝ)⁻¹ * ∫ y, φ y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.RiemannCore.main | exact GlobalTheory.CompanionTheory.RiemannCore.main | (intros; apply GlobalTheory.CompanionTheory.RiemannCore.main <;> assumption)
end _root_.GlobalTheory.T
