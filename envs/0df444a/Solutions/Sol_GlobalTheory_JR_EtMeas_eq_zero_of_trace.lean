-- Prove2me | solution 1 for GlobalTheory.JR.EtMeas.eq_zero_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:15.520065+00:00
-- url     : https://prove2.me/submissions/eeafbe68-927a-4d65-9eb0-0046569aa6a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousDistribHaarCharUnitsOfCompactOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsHaarQuotientIntegralFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtMeas
namespace GlobalTheory.JR.EtMeas
theorem _root_.solution (F : Type) [Field F] [CharZero F] (K : Type) [CommRing K] [Algebra F K]
    [Module.Finite F K] [IsReduced K] (x : K) (hx : ∀ y, Algebra.trace F K (x * y) = 0) : x = 0 := by
  have : IsArtinianRing K := IsArtinianRing.of_finite F K
  have : IsSemisimpleRing K := IsArtinianRing.isSemisimpleRing_of_isReduced K
  obtain ⟨e, he, hI⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span {x})
  have h1 : e ∈ Ideal.span {x} := hI ▸ Ideal.mem_span_singleton_self e
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h1
  have h2 : IsIdempotentElem (Algebra.lmul F K e) := he.map _
  have h3 : LinearMap.trace F K (Algebra.lmul F K e) = 0 := by
    have := hx y
    rwa [mul_comm, hy, Algebra.trace_apply] at this
  have h4 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff h2).1 h3
  have h5 : e = 0 := by simpa using LinearMap.congr_fun h4 1
  have h6 : x ∈ Ideal.span {e} := hI ▸ Ideal.mem_span_singleton_self x
  simpa [h5] using h6
end GlobalTheory.JR.EtMeas
