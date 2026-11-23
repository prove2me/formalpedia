-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.exists_bump
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:51.569646+00:00
-- url     : https://prove2.me/submissions/cb6741bb-cac7-4f95-8eb3-438160981549

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V : Type} [TopologicalSpace V]
namespace GlobalTheory.CompanionTheory.SW.FibreFam
theorem _root_.solution [LocallyCompactSpace V] [T2Space V] {K O : Set V} (hK : IsCompact K)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ φ : V → ℝ, Continuous φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ O ∧ (∀ v, 0 ≤ φ v) ∧
      (∀ v, φ v ≤ 1) ∧ ∀ v ∈ K, φ v = 1 := by
  obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hO hKO
  exact ⟨f, f.continuous, hfc, hfs, fun v => (hf01 v).1, fun v => (hf01 v).2, fun v hv => hf1 hv⟩
end GlobalTheory.CompanionTheory.SW.FibreFam
