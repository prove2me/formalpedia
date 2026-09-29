-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.opt_le_card_mul_max_singleton
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:54:17.475708+00:00
-- url     : https://prove2.me/submissions/68f7592f-7f74-49bf-a661-1a816a68d4ff

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm

namespace NonmonotoneSubmod.LocalSearch

theorem aux_olcm_nonempty_bound {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (v : X) (hv : IsMaxSingleton f v) (S : Finset X) (hS : S.Nonempty) :
    f S ≤ (S.card : ℝ) * f {v} := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hv a
  | cons a s ha hs ih =>
    have h1 := hf {a} s
    have h2 := hf0 ({a} ∩ s)
    have h3 := hv a
    rw [Finset.cons_eq_insert, Finset.card_insert_of_notMem ha]
    rw [Finset.insert_eq]
    push_cast
    nlinarith

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch

theorem solution {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hn : 2 ≤ Fintype.card X) (v : X) (hv : IsMaxSingleton f v) :
    NonmonotoneSubmod.Shared.OPT f ≤ (Fintype.card X : ℝ) * f {v} := by
  unfold NonmonotoneSubmod.Shared.OPT
  apply Finset.sup'_le
  intro S _
  have hv0 := hf0 {v}
  rcases S.eq_empty_or_nonempty with h | h
  · subst h
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card X)
    have h1 := hf {a} {b}
    have hi : ({a} : Finset X) ∩ {b} = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨rfl, rfl⟩; exact hab rfl
    rw [hi] at h1
    have h2 := hf0 ({a} ∪ {b})
    have ha := hv a
    have hb := hv b
    have hn' : (2 : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hn
    nlinarith
  · have := aux_olcm_nonempty_bound f hf0 hf v hv S h
    have hc : (S.card : ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast Finset.card_le_univ S
    nlinarith
