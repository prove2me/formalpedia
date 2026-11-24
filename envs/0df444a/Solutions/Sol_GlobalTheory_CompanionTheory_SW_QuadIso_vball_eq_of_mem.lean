-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.vball_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:34.652699+00:00
-- url     : https://prove2.me/submissions/9ccafa58-0d5e-4442-be35-f431d4ababda

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
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
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution {x y : K} {γ : ℤᵐ⁰} (h : y ∈ vball x γ) : vball y γ = vball x γ := by
  ext z
  simp only [vball, Set.mem_setOf_eq] at h ⊢
  constructor
  · intro hz
    have : z - x = (z - y) + (y - x) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hz h
  · intro hz
    have : z - y = (z - x) + (-(y - x)) := by ring
    rw [this]
    exact Valuation.map_add_lt _ hz (by rwa [Valuation.map_neg])
end GlobalTheory.CompanionTheory.SW.QuadIso
