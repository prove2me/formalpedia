-- Prove2me | solution 1 for GlobalTheory.HermClass.fg_integers
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:07.152802+00:00
-- url     : https://prove2.me/submissions/45bf3a93-a7ea-4a10-a983-2f39e0f0712d

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
variable (E : Type) [Field E] [NumberField E]
namespace GlobalTheory.HermClass
theorem _root_.solution : (Subalgebra.toSubmodule (integralClosure ℤ E)).FG :=
  Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite ℤ (𝓞 E)))
end GlobalTheory.HermClass
