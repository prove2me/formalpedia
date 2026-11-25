-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.incl_swap_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:51.923716+00:00
-- url     : https://prove2.me/submissions/8fd99ec7-e009-4129-b9a6-552e0093ab4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution (G : PDivGroup p O) : incl G G ≫ swap G ≫ fst G G = 0 :=
  hom_ext fun n => BialgHom.ext fun a => by
    change (incl G G).app n ((swap G).app n (inl _ _ a)) = algebraMap O _ (counit a)
    rw [inl_apply]
    change counit (R := O) a • (1 : G.A n) = _
    rw [Algebra.algebraMap_eq_smul_one]
end GlobalTheory.PDivGroup.Test
