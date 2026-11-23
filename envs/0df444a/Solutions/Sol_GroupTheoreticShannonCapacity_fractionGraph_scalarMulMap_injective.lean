-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.fractionGraph_scalarMulMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:27:49.691368+00:00
-- url     : https://prove2.me/submissions/48ad57ec-add2-4756-93e9-ff263b87d905

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (p' p : ℕ) [NeZero p'] [NeZero (p' * p)] :
    Function.Injective (fractionGraph_scalarMulMap p' p) := by
  have hp_pos := p_pos_of_neZero_prod p' p
  intro x y hxy
  have hxval_lt : p * x.val < p' * p := by
    calc p * x.val < p * p' := Nat.mul_lt_mul_of_pos_left x.val_lt hp_pos
      _ = p' * p := Nat.mul_comm p p'
  have hyval_lt : p * y.val < p' * p := by
    calc p * y.val < p * p' := Nat.mul_lt_mul_of_pos_left y.val_lt hp_pos
      _ = p' * p := Nat.mul_comm p p'
  simp only [fractionGraph_scalarMulMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hxy
  have hval_eq : (↑(p * x.val) : ZMod (p' * p)).val = (↑(p * y.val) : ZMod (p' * p)).val :=
    congrArg ZMod.val hxy
  rw [ZMod.val_cast_of_lt hxval_lt, ZMod.val_cast_of_lt hyval_lt] at hval_eq
  have : x.val = y.val := Nat.eq_of_mul_eq_mul_left hp_pos hval_eq
  exact ZMod.val_injective p' this
end GroupTheoreticShannonCapacity
