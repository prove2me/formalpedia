-- Prove2me | solution 1 for GlobalTheory.HermClass.isIntegral_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:34.842979+00:00
-- url     : https://prove2.me/submissions/538c57c7-b357-4756-ad00-4d81cabfc532

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
theorem _root_.solution {a : E} (ha : IsIntegral ℤ a) : IsIntegral ℤ (star a) :=
  ha.map (starRingEnd E).toIntAlgHom
end GlobalTheory.HermClass
