-- Prove2me | solution 1 for GlobalTheory.RestrictScalarsSpan.mul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:56:33.177099+00:00
-- url     : https://prove2.me/submissions/3bab4e4b-8de1-49f6-a140-a3f3637967c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_RestrictScalarsMapEqSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.RestrictScalarsSpan
namespace GlobalTheory.RestrictScalarsSpan
theorem _root_.solution {K : Type u_1} {L : Type u_2} {A : Type u_3} {B : Type u_4} [Field K] [Field L]
    [Algebra K L] [Ring A] [Ring B] [Algebra K A] [Algebra K B] [Algebra L B]
    [IsScalarTower K L B] {j : A →ₐ[K] B} (h : IsBaseChange L (AlgHom.toLinearMap j))
    (I : Ideal A) (b x : B) (hx : x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) :
    b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
  have key : ∀ a : A, j a * x ∈ Submodule.span L ((j : A → B) '' (I : Set A)) := by
    intro a
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      exact Submodule.subset_span ⟨a * i, I.mul_mem_left a hi, map_mul j a i⟩
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul l y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ l hy
  refine h.inductionOn b
    (motive := fun b => b * x ∈ Submodule.span L ((j : A → B) '' (I : Set A))) ?_ ?_ ?_ ?_
  · simp
  · exact key
  · intro l b hb
    rw [smul_mul_assoc]; exact Submodule.smul_mem _ l hb
  · intro b c hb hc
    rw [add_mul]; exact add_mem hb hc
end GlobalTheory.RestrictScalarsSpan
