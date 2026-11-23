-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreDensity.exists_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:48.745852+00:00
-- url     : https://prove2.me/submissions/8f6d8c6f-1142-4817-b548-578d9b719ec8

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuousStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreDensity
variable {V X Y : Type}
  [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y} {B : Set X}
  {fib : X → Measure V}
namespace GlobalTheory.CompanionTheory.SW.FibreDensity
theorem _root_.solution (hg : Continuous g) (hB : IsOpen B) {K : Set X} (hK : IsCompact K)
    (hKB : K ⊆ B) {φ : V → ℂ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ ψ : V → ℂ, Continuous ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ g ⁻¹' B ∧
      ∀ v, g v ∈ K → ψ v = φ v := by
  obtain ⟨χ, h1, -, hsupp, -⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hB hKB
  refine ⟨fun v => (χ (g v) : ℂ) * φ v, ?_, ?_, ?_, ?_⟩
  · exact (Complex.continuous_ofReal.comp (χ.continuous.comp hg)).mul hc
  · exact hs.mono (fun v hv hv0 => hv (by simp [show φ v = 0 from hv0]))
  · have hsub : Function.support (fun v => (χ (g v) : ℂ) * φ v) ⊆ g ⁻¹' tsupport χ := by
      intro v hv
      apply subset_tsupport
      intro h0
      exact hv (by simp [show χ (g v) = 0 from h0])
    exact (closure_minimal hsub ((isClosed_tsupport _).preimage hg)).trans
      (Set.preimage_mono hsupp)
  · intro v hv
    have : χ (g v) = 1 := h1 hv
    simp [this]
end GlobalTheory.CompanionTheory.SW.FibreDensity
