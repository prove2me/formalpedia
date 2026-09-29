-- Prove2me | solution 1 for NonmonotoneSubmod.SmoothLS.phi_between_zero_opt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:22:36.099114+00:00
-- url     : https://prove2.me/submissions/b37644fd-bc33-406e-a160-e5e8c16482cf

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample

namespace NonmonotoneSubmod.SmoothLS

theorem aux_pbzo_weight_sum {X : Type} [Fintype X] [DecidableEq X] (x : X → ℝ) :
    ∑ S : Finset X, ∏ i : X, (if i ∈ S then x i else 1 - x i) = 1 := by
  have h := Fintype.prod_add x (fun i => 1 - x i)
  simp only [add_sub_cancel, Finset.prod_const_one] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl fun S _ => ?_
  have := Finset.prod_piecewise (Finset.univ : Finset X) S x (fun i => 1 - x i)
  simp only [Finset.univ_inter, ← Finset.compl_eq_univ_sdiff] at this
  rw [← this]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Finset.piecewise]

theorem aux_pbzo_weight_nonneg {X : Type} [Fintype X] [DecidableEq X] (x : X → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) (S : Finset X) :
    0 ≤ ∏ i : X, (if i ∈ S then x i else 1 - x i) := by
  refine Finset.prod_nonneg fun i _ => ?_
  split_ifs
  · exact h0 i
  · linarith [h1 i]

end NonmonotoneSubmod.SmoothLS

open NonmonotoneSubmod.SmoothLS

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S, 0 ≤ f S) (δ : ℝ) (hδ0 : -1 ≤ δ) (hδ1 : δ ≤ 1)
    (A : Finset X) :
    0 ≤ Phi f δ A ∧ Phi f δ A ≤ NonmonotoneSubmod.Shared.OPT f := by
  have hx0 : ∀ i, 0 ≤ biasPt A δ i := by
    intro i; unfold biasPt; split_ifs <;> linarith
  have hx1 : ∀ i, biasPt A δ i ≤ 1 := by
    intro i; unfold biasPt; split_ifs <;> linarith
  have hw := aux_pbzo_weight_nonneg (biasPt A δ) hx0 hx1
  have hs := aux_pbzo_weight_sum (biasPt A δ)
  unfold Phi NonmonotoneSubmod.Shared.F
  constructor
  · exact Finset.sum_nonneg fun S _ => mul_nonneg (hf0 S) (hw S)
  · calc ∑ S : Finset X, f S * ∏ i : X, (if i ∈ S then biasPt A δ i else 1 - biasPt A δ i)
        ≤ ∑ S : Finset X, NonmonotoneSubmod.Shared.OPT f *
            ∏ i : X, (if i ∈ S then biasPt A δ i else 1 - biasPt A δ i) := by
          refine Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_right ?_ (hw S)
          exact Finset.le_sup' f (Finset.mem_univ S)
      _ = NonmonotoneSubmod.Shared.OPT f := by
          rw [← Finset.mul_sum, hs, mul_one]
