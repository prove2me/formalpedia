-- Prove2me | solution 1 for GlobalTheory.HermClass.trace_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:41.832549+00:00
-- url     : https://prove2.me/submissions/2d1dcc2b-c3f9-43c2-8571-1fead9100c48

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HermClass
theorem _root_.solution (a : E) : Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) a
end GlobalTheory.HermClass
