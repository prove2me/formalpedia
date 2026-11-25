-- Prove2me | solution 1 for GlobalTheory.tensor_dual_standard_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:21:41.92013+00:00
-- url     : https://prove2.me/submissions/c668d326-da72-4597-970d-067ce4fc3eaf

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TensorDualStandardRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
open GlobalTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))), _root_.Formalism.REAL.GlRel E → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) - if c = b then y a else 0) → (∀ y a, Om y a = ∑ c, E a c (y c)) → _root_.Formalism.REAL.GlRel Et ∧ (∀ a b x y, inner ℂ (Et a b x) y = inner ℂ x (Et b a y)) ∧ Om.IsSymmetric ∧ ∀ a b, Om * Et a b = Et a b * Om := by
  intro V _ _ _ n E Et Om hE hsym hEt hOm
  have hE' : ∀ a b c d (v : V), E a b (E c d v) - E c d (E a b v) = (if b = c then E a d v else 0) - if d = a then E c b v else 0 := by
    intro a b c d v
    have := congrArg (fun T : Module.End ℂ V => T v) (hE a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
    rw [this]; split_ifs <;> simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b c d
    ext y e
    have key : E a b (E c d (y.ofLp e)) = E c d (E a b (y.ofLp e)) + ((if b = c then E a d (y.ofLp e) else 0) - if d = a then E c b (y.ofLp e) else 0) := by
      have h := hE' a b c d (y.ofLp e); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have hR : (((if b = c then Et a d else 0) - if d = a then Et c b else 0) y).ofLp e = (if b = c then (Et a d y).ofLp e else 0) - (if d = a then (Et c b y).ofLp e else 0) := by
      split_ifs <;> simp
    rw [hR]
    simp only [LinearMap.sub_apply, Module.End.mul_apply]
    rw [WithLp.ofLp_sub, Pi.sub_apply, hEt, hEt, hEt, hEt, hEt, hEt, map_sub, map_sub, key]
    split_ifs <;> simp only [hEt, map_zero, sub_zero, zero_sub] <;> subst_vars <;>
      first | abel1 | (exfalso; tauto) | (simp_all; done) | (split_ifs <;> subst_vars <;> first | abel1 | (exfalso; tauto) | (simp_all; done) | (simp_all; abel1))
  · intro a b x y
    simp only [PiLp.inner_apply, hEt, inner_sub_left, inner_sub_right, Finset.sum_sub_distrib, hsym]
    have h1 : ∀ i, inner ℂ (if i = b then x.ofLp a else 0) (y.ofLp i) = if i = b then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    have h2 : ∀ i, inner ℂ (x.ofLp i) (if i = a then y.ofLp b else 0) = if i = a then inner ℂ (x.ofLp a) (y.ofLp b) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [h1, h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro x y
    simp only [PiLp.inner_apply, hOm, sum_inner, inner_sum, hsym]
    exact Finset.sum_comm
  · intro a b
    ext y e
    simp only [Module.End.mul_apply, hOm, hEt, map_sub, map_sum]
    have key : ∀ i, E e i (E a b (y.ofLp i)) = E a b (E e i (y.ofLp i)) + (if i = a then E e b (y.ofLp i) else 0) - (if b = e then E a i (y.ofLp i) else 0) := by
      intro i; have h := hE' e i a b (y.ofLp i); rw [sub_eq_iff_eq_add] at h; rw [h]; abel
    have h3 : ∀ i, E e i (if i = b then y.ofLp a else 0) = if i = b then E e b (y.ofLp a) else 0 := by
      intro i; split_ifs with h <;> simp [h]
    simp only [key, h3, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases h : e = b
    · subst h; simp only [if_true]; abel
    · simp only [h, Ne.symm h, if_false, Finset.sum_const_zero]; abel
end _root_.GlobalTheory
end GlobalTheory
