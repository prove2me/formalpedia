-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreShift.comp_shift_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:21:23.701835+00:00
-- url     : https://prove2.me/submissions/2b3df20d-ee1e-413b-9477-3f6249018ffb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityExists
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompactsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DisintegrationHaarBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreShift
namespace GlobalTheory.CompanionTheory.SW.FibreShift
theorem _root_.solution {V : Type} [TopologicalSpace V] [T2Space V] {W : Set V} (hW : IsOpen W)
    {T T' : V → V} (hT : ContinuousOn T W) (hT' : ContinuousOn T' W)
    (hmem : ∀ v, T v ∈ W ↔ v ∈ W) (hmem' : ∀ v, T' v ∈ W ↔ v ∈ W)
    (hinv : ∀ v ∈ W, T' (T v) = v) {φ : V → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ W) :
    Continuous (fun v => φ (T v)) ∧ HasCompactSupport (fun v => φ (T v)) ∧
      tsupport (fun v => φ (T v)) ⊆ W := by
  have hC : IsCompact (T' '' tsupport φ) := hc.isCompact.image_of_continuousOn (hT'.mono hs)
  have hCW : T' '' tsupport φ ⊆ W := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hmem' w).2 (hs hw)
  have hsup : ∀ v, v ∉ T' '' tsupport φ → φ (T v) = 0 := by
    intro v hv
    by_contra h
    have h1 : T v ∈ tsupport φ := subset_tsupport _ h
    exact hv ⟨T v, h1, hinv v ((hmem v).1 (hs h1))⟩
  have hts : tsupport (fun v => φ (T v)) ⊆ T' '' tsupport φ := by
    refine closure_minimal ?_ hC.isClosed
    intro v hv
    by_contra h
    exact hv (hsup v h)
  refine ⟨continuous_of_tsupport fun v hv => ?_, HasCompactSupport.intro hC hsup, hts.trans hCW⟩
  exact ContinuousAt.comp (g := φ) hφ.continuousAt (hT.continuousAt (hW.mem_nhds (hCW (hts hv))))
end GlobalTheory.CompanionTheory.SW.FibreShift
