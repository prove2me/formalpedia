-- Prove2me | solution 1 for GlobalTheory.finrank_add_two_mul_of_hyperbolic_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:50:10.864214+00:00
-- url     : https://prove2.me/submissions/32006ca5-8bce-416d-b7cc-5f397041aaf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FinrankAddTwoMulOfHyperbolicPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E V : Type) [Field E] [StarRing E] [AddCommGroup V] [Module E V] [FiniteDimensional E V] (h : V →ₗ⋆[E] V →ₗ[E] E), h.IsSymm → ∀ (W : Submodule E V) (i : ℕ) (e f : Fin i → V), (∀ a b, h (e a) (e b) = 0) → (∀ a b, h (f a) (f b) = 0) → (∀ a b, h (f a) (e b) = if a = b then 1 else 0) → (∀ a, ∀ x ∈ W, h x (e a) = 0 ∧ h x (f a) = 0) → W ⊔ Submodule.span E (Set.range e ∪ Set.range f) = ⊤ → LinearIndependent E e ∧ Module.finrank E W + 2 * i = Module.finrank E V := by
  intro E V _ _ _ _ _ h hS W i e f hee hff hfe hW hspan
  classical

  have hef : ∀ a b, h (e a) (f b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hS.eq (f b) (e a), hfe]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Ne.symm hab]

  have coeff_e : ∀ (c : Fin i ⊕ Fin i → E) (a : Fin i),
      h (e a) (∑ j, c j • Sum.elim e f j) = c (Sum.inr a) := by
    intro c a
    simp [map_sum, map_smul, Fintype.sum_sum_type, hee, hef]
  have coeff_f : ∀ (c : Fin i ⊕ Fin i → E) (a : Fin i),
      h (f a) (∑ j, c j • Sum.elim e f j) = c (Sum.inl a) := by
    intro c a
    simp [map_sum, map_smul, Fintype.sum_sum_type, hff, hfe]
  have hli : LinearIndependent E (Sum.elim e f) := by
    refine Fintype.linearIndependent_iff.2 fun c hc j => ?_
    rcases j with a | a
    · rw [← coeff_f c a, hc, map_zero]
    · rw [← coeff_e c a, hc, map_zero]
  have hrange : Set.range e ∪ Set.range f = Set.range (Sum.elim e f) :=
    (Set.Sum.elim_range e f).symm
  rw [hrange] at hspan
  set U := Submodule.span E (Set.range (Sum.elim e f)) with hU
  have hinf : W ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    obtain ⟨huW, huU⟩ := Submodule.mem_inf.1 hu
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 huU
    have hc : ∀ j, c j = 0 := by
      rintro (a | a)
      · rw [← coeff_f c a, ← hS.eq _ (f a), (hW a _ huW).2, map_zero]
      · rw [← coeff_e c a, ← hS.eq _ (e a), (hW a _ huW).1, map_zero]
    simp [hc]
  have hUdim : Module.finrank E U = 2 * i := by
    rw [hU, finrank_span_eq_card hli, Fintype.card_sum, Fintype.card_fin]
    ring
  refine ⟨by simpa using hli.comp Sum.inl Sum.inl_injective, ?_⟩
  have key := Submodule.finrank_sup_add_finrank_inf_eq W U
  rw [hspan, hinf, finrank_top, finrank_bot, add_zero, hUdim] at key
  exact key.symm
end GlobalTheory
