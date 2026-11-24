-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.basis_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:55.219772+00:00
-- url     : https://prove2.me/submissions/1475a4a9-43f0-4bac-b61c-4aa93464ef4e

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
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution (h2 : Module.finrank F E = 2) {d : E} (hd : d ∉ (algebraMap F E).range) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = d := by
  have hli : LinearIndependent F ![(1 : E), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have ht : t = 0 := by
      by_contra ht
      apply hd
      refine ⟨-(s / t), ?_⟩
      have hht : algebraMap F E t ≠ 0 := by simpa using ht
      simp only [Algebra.smul_def, mul_one] at hst
      have h3 : algebraMap F E t * (algebraMap F E s / algebraMap F E t) = algebraMap F E s := by
        field_simp
      apply mul_left_cancel₀ hht
      rw [map_neg, map_div₀, mul_neg, h3]
      linear_combination -hst
    subst ht
    simpa using hst
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2]), ?_, ?_⟩ <;> simp
end GlobalTheory.CompanionTheory.SW.PrimV
