-- Prove2me | solution 1 for GlobalTheory.trace_eq_sum_coords_of_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:34.185275+00:00
-- url     : https://prove2.me/submissions/0a1570f4-a3e2-4857-ae65-63b0bdf5a02c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceEqSumCoordsOfAlgEquiv
import Theorems.Thm_GlobalTheory_trace_pi_fin_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F K : Type} [Field F] [CommRing K] [Algebra F K] (r : ℕ)
    (e : K ≃ₐ[F] (Fin r → F)) (k : K) : Algebra.trace F K k = ∑ i, e k i := by
  rw [← Algebra.trace_eq_of_algEquiv e k, trace_pi_fin_self]
end GlobalTheory
