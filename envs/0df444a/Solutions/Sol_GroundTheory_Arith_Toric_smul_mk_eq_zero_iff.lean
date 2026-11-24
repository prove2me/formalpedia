-- Prove2me | solution 1 for GroundTheory.Arith.Toric.smul_mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:36.486296+00:00
-- url     : https://prove2.me/submissions/56909312-f6c5-4e09-b1b6-8c26287a8fcf

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {b r y : A} :
    r • (Ideal.Quotient.mk (Ideal.span {b}) y) = 0 ↔ b ∣ r * y := by
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
end GroundTheory.Arith.Toric
