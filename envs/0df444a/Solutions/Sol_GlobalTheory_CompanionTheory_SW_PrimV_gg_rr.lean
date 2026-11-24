-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.gg_rr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:08:13.576373+00:00
-- url     : https://prove2.me/submissions/4e5012f2-dcef-4307-8bd1-6c5d1bd441ab

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale

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
theorem _root_.solution (h0 : bs 0 = 1) (x : K) : gg (bs 1) (rr bs x) = x := by
  have := bs.sum_repr x
  rw [Fin.sum_univ_two, h0] at this
  exact this
end GlobalTheory.CompanionTheory.SW.PrimV
