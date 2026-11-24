-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.Nf_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:10:20.647099+00:00
-- url     : https://prove2.me/submissions/9adab9a5-7d5f-4d96-bcad-89c1dff33da0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {L K : Type*} [NormedField L] [ProperSpace L]
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution {D : L} (hD : ∀ s, s * s ≠ D) {p : L × L} (hp : p ≠ 0) : Nf D p ≠ 0 := by
  intro h
  simp only [Nf] at h
  by_cases hc : p.2 = 0
  · apply hp
    refine Prod.ext ?_ hc
    rw [hc] at h
    simpa using h
  · apply hD (p.1 / p.2)
    field_simp
    linear_combination h
end GlobalTheory.CompanionTheory.SW.PrimV
