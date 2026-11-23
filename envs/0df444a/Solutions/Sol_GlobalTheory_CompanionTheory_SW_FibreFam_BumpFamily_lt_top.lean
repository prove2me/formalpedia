-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:58.474847+00:00
-- url     : https://prove2.me/submissions/784b8e4b-80dd-49cc-8a69-25be39966028

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_exists_bump
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_le_lintegral_bump

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
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
namespace GlobalTheory.CompanionTheory.SW.FibreFam
namespace BumpFamily
theorem _root_.solution [LocallyCompactSpace V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hU : IsOpen U) {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) (b : X) :
    fib b K < ∞ := by
  by_cases hb : b ∈ B
  · obtain ⟨φ, hc, hcs, hs, h0, -, hK1⟩ := exists_bump hK hU hKU
    have hint := (h.2 φ hc hcs hs).1 b hb
    exact lt_of_le_of_lt (le_lintegral_bump (fib b) hK h0 hK1) hint.lintegral_lt_top
  · rw [h.1 b hb]
    simp
end BumpFamily
end GlobalTheory.CompanionTheory.SW.FibreFam
