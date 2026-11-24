-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_of_ringEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:56.176804+00:00
-- url     : https://prove2.me/submissions/de3d1d80-9b0c-4115-a77e-5e197ac6117b

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
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B] {M : ℕ}
    (e : A ≃+* B) (hc : Continuous e.symm) (h : UniP B M) : UniP A M := by
  obtain ⟨Ω, c, p⟩ := h
  refine ⟨(fun w i => e.symm (w i)) '' Ω,
    c.image (continuous_pi fun i => hc.comp (continuous_apply i)), ?_⟩
  rintro y ⟨z, hz⟩
  have h1 : (fun i => e (z i)) ⬝ᵥ (fun i => e (y i)) = 1 := by
    have := congrArg e hz
    simpa [dotProduct, map_sum, map_mul] using this
  obtain ⟨a, w, m1, m2, m3⟩ := p _ ⟨_, h1⟩
  refine ⟨Units.map (e.symm : B →* A) a, fun i => e.symm (w i), ⟨_, m1, ?_⟩, ⟨w, m2, rfl⟩, ?_⟩
  · ext i; simp
  · apply e.injective
    simpa [dotProduct, map_sum, map_mul] using m3
end GlobalTheory.CompanionTheory.SW.PrimV
