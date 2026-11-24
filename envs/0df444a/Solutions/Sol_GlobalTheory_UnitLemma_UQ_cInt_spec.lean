-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UQ.cInt_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:01:46.262361+00:00
-- url     : https://prove2.me/submissions/cd59c3fe-0c7e-4519-8be9-d774a04b121f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallConjFixedOfValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.UnitLemma
namespace GlobalTheory.UnitLemma
namespace UQ
theorem _root_.solution (K : UQ) (x : K.O) :
    algebraMap K.O K.E (K.cInt x) = K.c (algebraMap K.O K.E x) :=
  (Classical.choose_spec (K.c_int x)).symm
end UQ
end GlobalTheory.UnitLemma
