-- Prove2me | solution 1 for KnodelPrimeCordial.case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:19:47.490025+00:00
-- url     : https://prove2.me/submissions/c6a162cc-ca64-4d30-a323-8e68422d9221

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

open scoped BigOperators
theorem KnodelPrimeCordial.case_mod_6_edge_count_by_offsets__p2m_8a6c92bd_7c8f_41ac_9c83_07dd1e357c6c_a1 (n : ℕ) (h4 : 4 ≤ n / 2) (f : Fin 2 × Fin (n / 2) → ℕ) :
    (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) f).card =
      ∑ k : Fin 3,
        (Finset.univ.filter fun j : Fin (n / 2) =>
          Nat.Coprime
            (f ⟨(0 : Fin 2), j⟩)
            (f
              ⟨(1 : Fin 2),
                ⟨(j.val + 2 ^ k.val - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩⟩)).card := by
  have FCP : ∀ {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (e : Fin m × Fin 3 → α) (s : Finset α) (P : α → Prop)
      [DecidablePred P] (he : Set.BijOn e Set.univ (↑s : Set α)),
      (s.filter P).card = ∑ k : Fin 3, (Finset.univ.filter fun j : Fin m => P (e (j, k))).card := by
    intro α _ _ m e s P _ he
    classical
    have h1 : (s.filter P).card = (Finset.univ.filter fun x : Fin m × Fin 3 => P (e x)).card := by
      symm
      apply Finset.card_bij (fun x _ => e x)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨he.mapsTo (Set.mem_univ x), hx⟩
      · intro a _ b _ hab
        exact he.injOn (Set.mem_univ a) (Set.mem_univ b) hab
      · intro y hy
        simp only [Finset.mem_filter] at hy
        obtain ⟨x, -, rfl⟩ := he.surjOn hy.1
        exact ⟨x, by simp [hy.2], rfl⟩
    rw [h1, Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [Finset.card_filter]
  have OEB : Set.BijOn
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
  unfold KnodelPrimeCordial.edgesLabelOne
  rw [FCP (n / 2) _ _ _ OEB]
  apply Finset.sum_congr rfl
  intro k _
  congr 1

theorem solution (n : ℕ) (h4 : 4 ≤ n / 2) (f : Fin 2 × Fin (n / 2) → ℕ) :
    (KnodelPrimeCordial.edgesLabelOne (KnodelPrimeCordial.knodel 3 n) f).card =
      ∑ k : Fin 3,
        (Finset.univ.filter fun j : Fin (n / 2) =>
          Nat.Coprime
            (f ⟨(0 : Fin 2), j⟩)
            (f
              ⟨(1 : Fin 2),
                ⟨(j.val + 2 ^ k.val - 1) % (n / 2), Nat.mod_lt _ (by omega)⟩⟩)).card := by
  have FCP : ∀ {α : Type} [Fintype α] [DecidableEq α] (m : ℕ) (e : Fin m × Fin 3 → α) (s : Finset α) (P : α → Prop)
      [DecidablePred P] (he : Set.BijOn e Set.univ (↑s : Set α)),
      (s.filter P).card = ∑ k : Fin 3, (Finset.univ.filter fun j : Fin m => P (e (j, k))).card := by
    intro α _ _ m e s P _ he
    classical
    have h1 : (s.filter P).card = (Finset.univ.filter fun x : Fin m × Fin 3 => P (e x)).card := by
      symm
      apply Finset.card_bij (fun x _ => e x)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨he.mapsTo (Set.mem_univ x), hx⟩
      · intro a _ b _ hab
        exact he.injOn (Set.mem_univ a) (Set.mem_univ b) hab
      · intro y hy
        simp only [Finset.mem_filter] at hy
        obtain ⟨x, -, rfl⟩ := he.surjOn hy.1
        exact ⟨x, by simp [hy.2], rfl⟩
    rw [h1, Finset.card_filter, Fintype.sum_prod_type_right]
    simp only [Finset.card_filter]
  have OEB : Set.BijOn
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
  unfold KnodelPrimeCordial.edgesLabelOne
  rw [FCP (n / 2) _ _ _ OEB]
  apply Finset.sum_congr rfl
  intro k _
  congr 1

