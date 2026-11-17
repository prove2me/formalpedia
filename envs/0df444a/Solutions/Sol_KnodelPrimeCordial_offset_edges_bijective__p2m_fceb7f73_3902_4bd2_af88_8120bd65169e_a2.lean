-- Prove2me | solution 1 for KnodelPrimeCordial.offset_edges_bijective__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:19:46.376343+00:00
-- url     : https://prove2.me/submissions/8c530a30-029a-4bd4-a5d4-92c8c617e7ce

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel
theorem KnodelPrimeCordial.offset_edges_bijective__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2 (n : ℕ) (h4 : 4 ≤ n / 2) :
    Set.BijOn
      (fun p : Fin (n / 2) × Fin 3 =>
        s(⟨(0 : Fin 2), p.1⟩,
          ⟨(1 : Fin 2),
            ⟨(p.1.val + 2 ^ p.2.val - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩⟩))
      Set.univ
      (↑((KnodelPrimeCordial.knodel 3 n).edgeFinset) :
        Set (Sym2 (Fin 2 × Fin (n / 2)))) := by
  have mc : ∀ a N : ℕ, a < 2 * N → (a < N ∧ a % N = a) ∨ (N ≤ a ∧ a % N = a - N) := by
    intro a N h
    rcases Nat.lt_or_ge a N with h1 | h1
    · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
    · refine Or.inr ⟨h1, ?_⟩
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · intro p _
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    left
    exact ⟨rfl, rfl, p.2.val, p.2.isLt, rfl⟩
  · rintro ⟨j, k⟩ - ⟨j', k'⟩ - h
    simp only [Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨⟨-, hj⟩, ⟨-, hv⟩⟩ | ⟨⟨h01, -⟩, -⟩
    · subst hj
      have hv' := congrArg Fin.val hv
      simp only at hv'
      have hjl := j.isLt
      have E : j.val % (n / 2) = j.val := Nat.mod_eq_of_lt hjl
      have A := mc (j.val + 1) (n / 2) (by omega)
      have B := mc (j.val + 3) (n / 2) (by omega)
      have key : ∀ k : Fin 3, (j.val + 2 ^ k.val - 1) % (n / 2) =
          if k.val = 0 then j.val else if k.val = 1 then (j.val + 1) % (n / 2) else (j.val + 3) % (n / 2) := by
        intro k; fin_cases k <;> simp [E]
      rw [key k, key k'] at hv'
      have hk := k.isLt
      have hk' := k'.isLt
      have : k.val = k'.val := by split_ifs at hv' <;> omega
      exact Prod.ext rfl (Fin.ext this)
    · exact absurd h01 (by decide)
  · intro e he
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨u1, u2⟩ := u
      obtain ⟨v1, v2⟩ := v
      rcases he with ⟨hu, hv, k, hk, hval⟩ | ⟨hv, hu, k, hk, hval⟩
      · simp only at hu hv hval
        subst hu hv
        refine ⟨(u2, ⟨k, hk⟩), Set.mem_univ _, ?_⟩
        exact Sym2.eq_iff.mpr (Or.inl ⟨rfl, Prod.ext rfl (Fin.ext hval.symm)⟩)
      · simp only at hu hv hval
        subst hu hv
        refine ⟨(v2, ⟨k, hk⟩), Set.mem_univ _, ?_⟩
        exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, Prod.ext rfl (Fin.ext hval.symm)⟩)

theorem solution (n : ℕ) (h4 : 4 ≤ n / 2) :
    Set.BijOn
      (fun p : Fin (n / 2) × Fin 3 =>
        s(⟨(0 : Fin 2), p.1⟩,
          ⟨(1 : Fin 2),
            ⟨(p.1.val + 2 ^ p.2.val - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩⟩))
      Set.univ
      (↑((KnodelPrimeCordial.knodel 3 n).edgeFinset) :
        Set (Sym2 (Fin 2 × Fin (n / 2)))) := by
  have mc : ∀ a N : ℕ, a < 2 * N → (a < N ∧ a % N = a) ∨ (N ≤ a ∧ a % N = a - N) := by
    intro a N h
    rcases Nat.lt_or_ge a N with h1 | h1
    · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
    · refine Or.inr ⟨h1, ?_⟩
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · intro p _
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    left
    exact ⟨rfl, rfl, p.2.val, p.2.isLt, rfl⟩
  · rintro ⟨j, k⟩ - ⟨j', k'⟩ - h
    simp only [Sym2.eq_iff, Prod.mk.injEq] at h
    rcases h with ⟨⟨-, hj⟩, ⟨-, hv⟩⟩ | ⟨⟨h01, -⟩, -⟩
    · subst hj
      have hv' := congrArg Fin.val hv
      simp only at hv'
      have hjl := j.isLt
      have E : j.val % (n / 2) = j.val := Nat.mod_eq_of_lt hjl
      have A := mc (j.val + 1) (n / 2) (by omega)
      have B := mc (j.val + 3) (n / 2) (by omega)
      have key : ∀ k : Fin 3, (j.val + 2 ^ k.val - 1) % (n / 2) =
          if k.val = 0 then j.val else if k.val = 1 then (j.val + 1) % (n / 2) else (j.val + 3) % (n / 2) := by
        intro k; fin_cases k <;> simp [E]
      rw [key k, key k'] at hv'
      have hk := k.isLt
      have hk' := k'.isLt
      have : k.val = k'.val := by split_ifs at hv' <;> omega
      exact Prod.ext rfl (Fin.ext this)
    · exact absurd h01 (by decide)
  · intro e he
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      obtain ⟨u1, u2⟩ := u
      obtain ⟨v1, v2⟩ := v
      rcases he with ⟨hu, hv, k, hk, hval⟩ | ⟨hv, hu, k, hk, hval⟩
      · simp only at hu hv hval
        subst hu hv
        refine ⟨(u2, ⟨k, hk⟩), Set.mem_univ _, ?_⟩
        exact Sym2.eq_iff.mpr (Or.inl ⟨rfl, Prod.ext rfl (Fin.ext hval.symm)⟩)
      · simp only at hu hv hval
        subst hu hv
        refine ⟨(v2, ⟨k, hk⟩), Set.mem_univ _, ?_⟩
        exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, Prod.ext rfl (Fin.ext hval.symm)⟩)

