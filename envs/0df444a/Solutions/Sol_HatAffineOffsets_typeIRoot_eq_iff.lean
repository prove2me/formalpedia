-- Prove2me | solution 1 for HatAffineOffsets.typeIRoot_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:39.562547+00:00
-- url     : https://prove2.me/submissions/131f2402-9164-400a-891f-13997802eee0

import Definitions.Def_HatAffineFactorAlignment_FactorAlignment
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Definitions.Def_HatAffineOffsets_TypeI

set_option autoImplicit true
open HatAffineOffsets
universe u v w
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_8d02a9c2cf_10
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Field K]
    {alpha b x y : K} (halpha : alpha ≠ 0) :
    (x - b) / alpha = y <-> alpha * y + b = x := by
  rw [div_eq_iff halpha]
  constructor
  · intro h
    calc
      alpha * y + b = y * alpha + b := by rw [mul_comm]
      _ = (x - b) + b := by rw [h]
      _ = x := sub_add_cancel x b
  · intro h
    calc
      x - b = (alpha * y + b) - b := by rw [h]
      _ = alpha * y := add_sub_cancel_right _ _
      _ = y * alpha := by rw [mul_comm]
end HatAffineOffsets
