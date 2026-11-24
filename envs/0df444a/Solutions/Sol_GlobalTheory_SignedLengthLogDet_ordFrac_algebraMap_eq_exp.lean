-- Prove2me | solution 1 for GlobalTheory.SignedLengthLogDet.ordFrac_algebraMap_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:18.560283+00:00
-- url     : https://prove2.me/submissions/5b78de70-9f15-4bbc-91c4-9258fb347bc2

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module
namespace GlobalTheory.SignedLengthLogDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R} (hx : x ≠ 0) {n : ℕ}
    (hn : Ring.ord R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R hx,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hx) hn]
  rfl
end GlobalTheory.SignedLengthLogDet
