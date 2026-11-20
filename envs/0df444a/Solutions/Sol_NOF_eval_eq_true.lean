-- Prove2me | solution 1 for NOF.eval_eq_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:16:26.938916+00:00
-- url     : https://prove2.me/submissions/1f3f0814-b8b6-4057-a800-23e349a0ea5f

module
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_ChandraFurstLipton_LowerBoundEval
public import Theorems.Thm_NOF_Protocol_broadcast_zero
public import Theorems.Thm_NOF_Protocol_le_complexity
public import Theorems.Thm_NOF_Protocol_length_broadcast
public import Theorems.Thm_NOF_le_funComplexity
attribute [local simp] NOF.Protocol.broadcast_zero
attribute [local simp] NOF.Protocol.le_complexity
attribute [local simp] NOF.Protocol.length_broadcast
attribute [local simp] NOF.le_funComplexity



set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : ZMod d → ZMod d → G} [Fintype ι]
namespace NOF
theorem _root_.solution {x : ι → G} : eval x = true ↔ ∑ i, x i = 0 := by simp [eval]
end NOF
