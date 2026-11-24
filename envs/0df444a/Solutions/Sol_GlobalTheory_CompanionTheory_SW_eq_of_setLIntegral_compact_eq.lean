-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:56:17.429775+00:00
-- url     : https://prove2.me/submissions/f340ca59-a250-4a6d-9157-440f416d0105

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_not_lt_of_setLIntegral_compact_eq

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution :
    ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
      [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
      [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B →
      ContinuousOn D' B →
      (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) →
      ∀ b ∈ B, D b = D' b := by
  intro X _ _ _ _ _ _ ν _ _ B hB D D' hD hD' h b hb
  exact le_antisymm
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD' hD (fun S hS hSB => (h S hS hSB).symm) hb))
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD hD' h hb))
end GlobalTheory.CompanionTheory.SW
