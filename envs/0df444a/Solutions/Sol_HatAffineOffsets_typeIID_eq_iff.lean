-- Prove2me | solution 1 for HatAffineOffsets.typeIID_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:43.35713+00:00
-- url     : https://prove2.me/submissions/9cc9823c-8be4-4c17-b547-a631659ce196

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_typeIRoot_eq_iff


set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} {I : Type*} [Field K]
    {alpha b x : I -> K} {i : I} {z : K}
    (halpha : alpha i ≠ 0) :
    typeIID alpha b x i = z ↔ alpha i * z + b i = x i := by
  exact typeIRoot_eq_iff halpha
end HatAffineOffsets
