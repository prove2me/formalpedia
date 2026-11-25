-- Prove2me | solution 1 for GlobalTheory.HermSpace.unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:47:14.612477+00:00
-- url     : https://prove2.me/submissions/7453ccf4-065a-4d9c-8c11-a2e38490d864

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_HermForm_IsometryEquiv_unimodular
import Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_unimodular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
namespace GlobalTheory
namespace HermSpace
theorem _root_.solution {K : Type u} [Field K] [StarRing K] (V : HermSpace.{u, v} K) :
    V.form.Unimodular := V.nondegenerate.unimodular
end HermSpace
end GlobalTheory
