-- Prove2me | solution 1 for NOF.trivial_of_isForbiddenPattern_of_isValid_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T18:17:00.505618+00:00
-- url     : https://prove2.me/submissions/88a861dc-fa62-4303-bda8-8abbe616bff7

module
public import Definitions.Def_ChandraFurstLipton_NOFModel
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.ZMod.Basic
public import Definitions.Def_ChandraFurstLipton_LowerBoundEval
public import Theorems.Thm_NOF_eval_eq_true
public import Theorems.Thm_NOF_IsForbiddenPatternWithTip_broadcast_eq
public import Theorems.Thm_NOF_Protocol_broadcast_zero
public import Theorems.Thm_NOF_Protocol_le_complexity
public import Theorems.Thm_NOF_Protocol_length_broadcast
public import Theorems.Thm_NOF_le_funComplexity
attribute [local simp] NOF.Protocol.broadcast_zero
attribute [local simp] NOF.Protocol.le_complexity
attribute [local simp] NOF.Protocol.length_broadcast
attribute [local simp] NOF.le_funComplexity


attribute [local simp] NOF.eval_eq_true

set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} [NeZero d]
  {P : Protocol G d} {t : ℕ} {B : List Bool} {a : ZMod d → ZMod d → G} [Fintype ι]
variable [DecidableEq ι]
namespace NOF
theorem _root_.solution (ha : IsForbiddenPattern a)
    (hP : P.IsValid eval t) (hE : ∀ i, eval (a i) = true) (hB : ∀ i, P.broadcast (a i) t = B) :
    ∀ i j, a i = a j := by
  obtain ⟨v, ha⟩ := ha
  have : P.broadcast v t = B := ha.broadcast_eq hB
  have h i : eval (a i) = eval v :=
    calc
      _ = P.guess i (forget i (a i)) (P.broadcast (a i) t) := by rw [hP]
      _ = P.guess i (forget i v) (P.broadcast v t) := by rw [hB, ha.broadcast_eq hB, ha.forget]
      _ = eval v := by rw [hP]
  suffices h : ∀ i, a i = v by simp [h]
  intro i
  ext j
  obtain hij | rfl := ne_or_eq i j
  · exact ha hij
  simp only [hE, Bool.true_eq, eval_eq_true, forall_const] at h
  rw [← sub_eq_zero]
  calc
    a i i - v i = ∑ j, (a i j - v j) := by
      rw [Fintype.sum_eq_single]; simpa [eq_comm, sub_eq_zero] using @ha i
    _ = ∑ j, a i j - ∑ j, v j := by rw [Finset.sum_sub_distrib]
    _ = 0 := by simpa [h] using hE i
end NOF
