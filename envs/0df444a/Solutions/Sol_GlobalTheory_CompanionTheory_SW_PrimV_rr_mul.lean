-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.rr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:28:27.527854+00:00
-- url     : https://prove2.me/submissions/e9c16fe7-5fe2-4ccf-9083-1a3dc853ece2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_gg_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_gg_rr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_gg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {L K : Type*} [Field L] [CommRing K] [Algebra L K]
variable (bs : Module.Basis (Fin 2) L K)
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D) (x y : K) :
    rr bs (x * y) = ((rr bs x).1 * (rr bs y).1 + D * ((rr bs x).2 * (rr bs y).2),
      (rr bs x).1 * (rr bs y).2 + (rr bs x).2 * (rr bs y).1) := by
  conv_lhs => rw [← gg_rr bs h0 x, ← gg_rr bs h0 y, gg_mul hd, rr_gg bs h0]
end GlobalTheory.CompanionTheory.SW.PrimV
