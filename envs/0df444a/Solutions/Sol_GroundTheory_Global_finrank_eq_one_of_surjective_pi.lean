-- Prove2me | solution 1 for GroundTheory.Global.finrank_eq_one_of_surjective_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:29.810936+00:00
-- url     : https://prove2.me/submissions/c72e371f-216a-46d8-b2b7-727bc65adb89

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Finite
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Galois
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Theorems.Thm_GroundTheory_Global_mem_range_algebraMap_of_surjective_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module
open scoped TensorProduct
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} [Fintype ι]
    (f : (ι → F) →ₐ[F] E) (hf : Function.Surjective f) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  exact eq_top_iff.2 fun e _ ↦ Algebra.mem_bot.2 (mem_range_algebraMap_of_surjective_pi f hf e)
end GroundTheory.Global
