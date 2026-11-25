-- Prove2me | solution 1 for GlobalTheory.Nef.RatDilation.natDegree_comp_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:03:59.049878+00:00
-- url     : https://prove2.me/submissions/44ffdd3f-4a8e-4b01-b979-ea78f71a4551

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeEqZeroOfSqDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
open GlobalTheory GlobalTheory.Nef
open Polynomial
open GlobalTheory.Nef.RatDilation
namespace GlobalTheory.Nef.RatDilation
theorem _root_.solution {F : Type} [Field F] [CharZero F] (f : F[X]) :
    (f.comp (C (2:F) * X)).natDegree = f.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_X _ two_ne_zero, mul_one]
end GlobalTheory.Nef.RatDilation
