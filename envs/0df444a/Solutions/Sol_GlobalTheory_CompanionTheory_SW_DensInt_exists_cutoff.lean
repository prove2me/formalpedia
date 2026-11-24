-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DensInt.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:15:06.941227+00:00
-- url     : https://prove2.me/submissions/457eaa13-bab0-493b-a5db-bd938e22b6ff

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivity
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DensInt
namespace GlobalTheory.CompanionTheory.SW.DensInt
theorem _root_.solution (V : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] :
    ∃ χ : ℕ → V → ℝ, (∀ k, Continuous (χ k)) ∧ (∀ k, HasCompactSupport (χ k)) ∧
      (∀ k x, 0 ≤ χ k x ∧ χ k x ≤ 1) ∧ ∀ x, ∀ᶠ k in Filter.atTop, χ k x = 1 := by
  have h : ∀ k : ℕ, ∃ f : C(V, ℝ), Set.EqOn f 1 (compactCovering V k) ∧ Set.EqOn f 0 (∅ : Set V) ∧
      HasCompactSupport f ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := fun k =>
    exists_continuous_one_zero_of_isCompact (isCompact_compactCovering V k) isClosed_empty
      (Set.disjoint_empty _)
  choose f h1 _ h3 h4 using h
  refine ⟨fun k => f k, fun k => (f k).continuous, h3, fun k x => h4 k x, fun x => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_mem_compactCovering x
  filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
  exact h1 k (compactCovering_subset V hk hk₀)
end GlobalTheory.CompanionTheory.SW.DensInt
