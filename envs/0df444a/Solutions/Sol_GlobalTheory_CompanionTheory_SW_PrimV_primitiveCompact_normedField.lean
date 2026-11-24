-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_normedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:28:21.958954+00:00
-- url     : https://prove2.me/submissions/49aa5700-5cf2-459f-8119-097a16052e34

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_of_multiplicative
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
variable [CommRing K] [Algebra L K] [TopologicalSpace K] (bs : Module.Basis (Fin 2) L K)
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution (M : ℕ) : UniP L M := by
  refine primitiveCompact_of_multiplicative M (fun x => ‖x‖) norm_zero norm_one norm_mul (fun _ => norm_nonneg _)
    (fun x hx => ⟨isUnit_iff_ne_zero.2 hx, norm_pos_iff.2 hx⟩) ?_
  have : {x : L | ‖x‖ ≤ 1} = Metric.closedBall 0 1 := by
    ext x; simp
  rw [this]
  exact isCompact_closedBall _ _
end GlobalTheory.CompanionTheory.SW.PrimV
