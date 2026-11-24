-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_sum_of_counting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:11:04.348922+00:00
-- url     : https://prove2.me/submissions/90312119-66d3-4bed-bfd3-715ad74fa186

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_gaussian_sum_le

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution :
    ∀ (n : ℕ) (c t₀ C : ℝ), 0 < c → 0 < t₀ → ∃ C' : ℝ, ∀ (X Ω : Type) [MeasurableSpace Ω]
      [Countable X] (Pr : Measure Ω) (s : Ω → X → ℝ) (p : Ω → X → Prop),
      (∀ x, Measurable fun ω => s ω x) → (∀ x, MeasurableSet {ω | p ω x}) →
      (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal (C' * (Real.sqrt t ^ n)⁻¹) :=
  fun n c t₀ C hc ht₀ => ⟨_, gaussian_sum_le n c t₀ C hc ht₀⟩
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
