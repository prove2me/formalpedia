-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocFv.isOpenEmbedding_units_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:11:36.553109+00:00
-- url     : https://prove2.me/submissions/f4f4c680-fb46-484f-aaa9-4294263915b7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocFv
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
namespace GlobalTheory.CompanionTheory.SW.LocFv
theorem _root_.solution (K : Type) [Field K] [TopologicalSpace K] [ContinuousInv₀ K]
    [ContinuousMul K] [T1Space K] : IsOpenEmbedding (Units.val : Kˣ → K) := by
  refine ⟨Units.isEmbedding_val₀, ?_⟩
  have : Set.range (Units.val : Kˣ → K) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 x h, rfl⟩⟩
  rw [this]
  exact isOpen_compl_singleton
end GlobalTheory.CompanionTheory.SW.LocFv
