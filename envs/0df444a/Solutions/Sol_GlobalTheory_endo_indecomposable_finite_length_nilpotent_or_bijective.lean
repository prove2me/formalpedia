-- Prove2me | solution 1 for GlobalTheory.endo_indecomposable_finite_length_nilpotent_or_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:07.17524+00:00
-- url     : https://prove2.me/submissions/d24886df-d621-4607-9f85-b58aad1cdaac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EndomorphismIndecomposableNilpotentOrBijective

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
    ∀ (R P : Type) [Ring R] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P],
      (∀ A B : Submodule R P, IsCompl A B → A = ⊥ ∨ B = ⊥) →
      ∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f := by
  intro R P _ _ _ _ _ hind f
  obtain ⟨n, hn⟩ := (LinearMap.eventually_isCompl_ker_pow_range_pow f).exists_forall_of_atTop
  have hc := hn (n + 1) (Nat.le_succ n)
  rcases hind _ _ hc with hk | hr
  · right
    have hk1 : LinearMap.ker f = ⊥ := by
      rw [eq_bot_iff, ← hk]
      intro x hx
      have hx' : f x = 0 := hx
      rw [LinearMap.mem_ker, pow_succ, Module.End.mul_apply, hx', map_zero]
    have hr1 : LinearMap.range (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hk, bot_sup_eq] at this
    have hs : LinearMap.range f = ⊤ := by
      rw [eq_top_iff, ← hr1]
      rintro _ ⟨x, rfl⟩
      rw [pow_succ', Module.End.mul_apply]
      exact ⟨_, rfl⟩
    exact ⟨LinearMap.ker_eq_bot.mp hk1, LinearMap.range_eq_top.mp hs⟩
  · left
    refine ⟨n + 1, ?_⟩
    have hk1 : LinearMap.ker (f ^ (n + 1)) = ⊤ := by
      have := hc.sup_eq_top
      rwa [hr, sup_bot_eq] at this
    exact LinearMap.ker_eq_top.mp hk1
end GlobalTheory
