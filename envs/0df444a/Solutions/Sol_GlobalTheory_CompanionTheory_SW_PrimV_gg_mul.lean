-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.gg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:41.635719+00:00
-- url     : https://prove2.me/submissions/0be52749-9f8e-4df9-bd58-1cd8c7e30bd0

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
variable {L K : Type*} [Field L] [CommRing K] [Algebra L K]
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution {d : K} {D : L} (hd : d * d = algebraMap L K D) (p q : L × L) :
    gg d p * gg d q = gg d (p.1 * q.1 + D * (p.2 * q.2), p.1 * q.2 + p.2 * q.1) := by
  simp only [gg, Algebra.smul_def, map_add, map_mul, mul_one]
  linear_combination (algebraMap L K p.2 * algebraMap L K q.2) * hd
end GlobalTheory.CompanionTheory.SW.PrimV
