-- Prove2me | solution 1 for NonmonotoneSubmod.LocalSearch.ls_approximation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:24:25.426604+00:00
-- url     : https://prove2.me/submissions/49fe96cb-7483-4957-9fe3-6585fc4f8014

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_SymmetricSetFun
import Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm
import Definitions.Def_NonmonotoneSubmod_LocalSearch_IsApproxLocalOptimum



namespace NonmonotoneSubmod.LocalSearch

theorem nsls_sub_chain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (c : ℝ)
    (hc : ∀ a, a ∈ S → f (S.erase a) - f S ≤ c) :
    ∀ D : Finset X, D ⊆ S → f (S \ D) - f S ≤ D.card * c := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert a D ha ih =>
    intro hD
    have haS : a ∈ S := hD (Finset.mem_insert_self a D)
    have hDS : D ⊆ S := fun x hx => hD (Finset.mem_insert_of_mem hx)
    have h1 := ih hDS
    have h2 := hf (S \ D) (S.erase a)
    have e1 : S \ D ∪ S.erase a = S := by
      ext x
      by_cases hx : x = a
      · subst hx; simp [haS, ha]
      · simp [hx]; tauto
    have e2 : S \ D ∩ S.erase a = S \ insert a D := by
      ext x; simp; tauto
    rw [e1, e2] at h2
    rw [Finset.card_insert_of_notMem ha]; push_cast
    have := hc a haS
    linarith

theorem nsls_sup_chain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (c : ℝ)
    (hc : ∀ a, a ∉ S → f (insert a S) - f S ≤ c) :
    ∀ D : Finset X, Disjoint S D → f (S ∪ D) - f S ≤ D.card * c := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert a D ha ih =>
    intro hD
    have haS : a ∉ S := fun h => Finset.disjoint_left.mp hD h (Finset.mem_insert_self a D)
    have hDS : Disjoint S D := Finset.disjoint_of_subset_right (Finset.subset_insert a D) hD
    have h1 := ih hDS
    have h2 := hf (S ∪ D) (insert a S)
    have e1 : S ∪ D ∪ insert a S = S ∪ insert a D := by
      ext x; simp; tauto
    have e2 : (S ∪ D) ∩ insert a S = S := by
      ext x
      by_cases hx : x = a
      · subst hx; simp [haS, ha]
      · simp [hx]; tauto
    rw [e1, e2] at h2
    rw [Finset.card_insert_of_notMem ha]; push_cast
    have := hc a haS
    linarith

theorem nsls_both {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf : NonmonotoneSubmod.Shared.Submodular f) (S : Finset X) (c : ℝ)
    (hc1 : ∀ a, a ∈ S → f (S.erase a) - f S ≤ c) (hc2 : ∀ a, a ∉ S → f (insert a S) - f S ≤ c)
    (T : Finset X) (hT : T ⊆ S ∨ S ⊆ T) : ∃ D : Finset X, f T - f S ≤ D.card * c := by
  rcases hT with h | h
  · refine ⟨S \ T, ?_⟩
    have := nsls_sub_chain f hf S c hc1 (S \ T) Finset.sdiff_subset
    rwa [Finset.sdiff_sdiff_eq_self h] at this
  · refine ⟨T \ S, ?_⟩
    have := nsls_sup_chain f hf S c hc2 (T \ S) Finset.disjoint_sdiff
    rwa [Finset.union_sdiff_of_subset h] at this

theorem lemma33_core {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (T : Finset X)
    (hT : T ⊆ S ∨ S ⊆ T) :
    f T ≤ (1 + (Fintype.card X : ℝ) * α) * f S := by
  obtain ⟨D, hD⟩ := nsls_both f hf S (α * f S) (fun a ha => by linarith [hS.1 a ha])
    (fun a ha => by linarith [hS.2 a ha]) T hT
  have hcard : (D.card : ℝ) ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ D
  have h0 : 0 ≤ α * f S := mul_nonneg hα (hf0 S)
  have : (D.card : ℝ) * (α * f S) ≤ Fintype.card X * (α * f S) := mul_le_mul_of_nonneg_right hcard h0
  nlinarith


theorem nsls_term {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ)
    (f : Finset X → ℝ) (S : Finset X) (hS : IsLSTerminal ε f S) :
    IsApproxLocalOptimum f (ε / (Fintype.card X : ℝ) ^ 2) S := by
  have hadd : ∀ a, a ∉ S → f (insert a S) ≤ lsFactor X ε * f S := by
    intro a ha
    by_contra h
    exact hS (insert a S) (Or.inl ⟨a, ha, not_le.mp h, rfl⟩)
  refine ⟨?_, ?_⟩
  · intro v hv
    by_contra h
    exact hS (S.erase v) (Or.inr ⟨hadd, v, hv, not_le.mp h, rfl⟩)
  · intro v hv
    exact hadd v hv

theorem nsls_any {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (α : ℝ) (hα : 0 ≤ α) (S : Finset X) (hS : IsApproxLocalOptimum f α S) (C : Finset X) :
    f C ≤ 2 * (1 + (Fintype.card X : ℝ) * α) * f S + f Sᶜ := by
  have h1 := lemma33_core f hf0 hf α hα S hS (C ∩ S) (Or.inl Finset.inter_subset_right)
  have h2 := lemma33_core f hf0 hf α hα S hS (S ∪ C) (Or.inr Finset.subset_union_left)
  have h3 := hf (C ∩ S) (C ∩ Sᶜ)
  have e1 : C ∩ S ∪ C ∩ Sᶜ = C := by ext x; simp; tauto
  have e2 : C ∩ S ∩ (C ∩ Sᶜ) = ∅ := by ext x; simp; tauto
  rw [e1, e2] at h3
  have h4 := hf (S ∪ C) Sᶜ
  have e3 : S ∪ C ∪ Sᶜ = Finset.univ := by ext x; simp; tauto
  have e4 : (S ∪ C) ∩ Sᶜ = C ∩ Sᶜ := by ext x; simp; tauto
  rw [e3, e4] at h4
  have := hf0 ∅
  have := hf0 Finset.univ
  linarith

theorem nsls_any_sym {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hsym : NonmonotoneSubmod.Shared.SymmetricSetFun f) (α : ℝ) (hα : 0 ≤ α) (S : Finset X)
    (hS : IsApproxLocalOptimum f α S) (C : Finset X) :
    f C ≤ 2 * (1 + (Fintype.card X : ℝ) * α) * f S := by
  have h1 := lemma33_core f hf0 hf α hα S hS (C ∩ S) (Or.inl Finset.inter_subset_right)
  have h2 := lemma33_core f hf0 hf α hα S hS (S ∪ Cᶜ) (Or.inr Finset.subset_union_left)
  have h3 := hf (C ∩ S) (C ∩ Sᶜ)
  have e1 : C ∩ S ∪ C ∩ Sᶜ = C := by ext x; simp; tauto
  have e2 : C ∩ S ∩ (C ∩ Sᶜ) = ∅ := by ext x; simp; tauto
  rw [e1, e2] at h3
  have h4 := hsym (C ∩ Sᶜ)
  have e3 : (C ∩ Sᶜ)ᶜ = S ∪ Cᶜ := by ext x; simp; tauto
  rw [e3] at h4
  have := hf0 ∅
  linarith

theorem nsls_insert_le {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (a : X) (A : Finset X) : f (insert a A) ≤ f {a} + f A := by
  have h := hf {a} A
  rw [Finset.insert_eq]
  linarith [hf0 ({a} ∩ A)]

theorem nsls_opt {X : Type} [Fintype X] [DecidableEq X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hn : 2 ≤ Fintype.card X) (v : X) (hv : IsMaxSingleton f v) :
    NonmonotoneSubmod.Shared.OPT f ≤ (Fintype.card X : ℝ) * f {v} := by
  have hne : ∀ A : Finset X, A.Nonempty → f A ≤ A.card * f {v} := by
    intro A hA
    induction A using Finset.induction_on with
    | empty => exact absurd hA (by simp)
    | insert a A ha ih =>
      rcases A.eq_empty_or_nonempty with h | h
      · subst h; simp [hv a]
      · have := ih h
        rw [Finset.card_insert_of_notMem ha]; push_cast
        linarith [nsls_insert_le f hf0 hf a A, hv a]
  have hv0 : 0 ≤ f {v} := hf0 _
  unfold NonmonotoneSubmod.Shared.OPT
  apply Finset.sup'_le
  intro A _
  rcases A.eq_empty_or_nonempty with h | h
  · subst h
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card X)
    have h := hf {a} {b}
    have e : ({a} : Finset X) ∩ {b} = ∅ := by
      ext x; simp; intro h1 h2; exact hab (h1.symm.trans h2)
    rw [e] at h
    have h2 : (2:ℝ) ≤ Fintype.card X := by exact_mod_cast hn
    nlinarith [hv a, hv b, hf0 ({a} ∪ {b})]
  · have := hne A h
    have hc : (A.card : ℝ) ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ A
    nlinarith

theorem nsls_growth {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (hε : 0 < ε)
    (f : Finset X → ℝ) (S : ℕ → Finset X) (k : ℕ) (hrun : IsLSRun ε f S k) (v : X)
    (hv : S 0 = {v}) : ∀ i, i ≤ k → lsFactor X ε ^ i * f {v} ≤ f (S i) := by
  have hstep : ∀ S S' : Finset X, lsStep ε f S S' → lsFactor X ε * f S < f S' := by
    intro S S' h
    rcases h with ⟨a, _, hlt, rfl⟩ | ⟨_, a, _, hlt, rfl⟩
    · exact hlt
    · exact hlt
  have hc : 0 ≤ lsFactor X ε := by
    unfold lsFactor
    have : 0 ≤ ε / (Fintype.card X : ℝ) ^ 2 := div_nonneg hε.le (sq_nonneg _)
    linarith
  intro i
  induction i with
  | zero => intro _; simp [hv]
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hstep _ _ (hrun.2 i (by omega))
    calc lsFactor X ε ^ (i + 1) * f {v} = lsFactor X ε * (lsFactor X ε ^ i * f {v}) := by ring
      _ ≤ lsFactor X ε * f (S i) := mul_le_mul_of_nonneg_left h1 hc
      _ ≤ f (S (i + 1)) := h2.le

theorem nsls_le_opt {X : Type} [Fintype X] (f : Finset X → ℝ) (A : Finset X) :
    f A ≤ NonmonotoneSubmod.Shared.OPT f :=
  Finset.le_sup' f (Finset.mem_univ A)

theorem ls_core {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k → IsLSTerminal ε f (S k) →
        (1 / 3 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ lsOutput f (S k)) ∧
    (NonmonotoneSubmod.Shared.SymmetricSetFun f → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        IsLSTerminal ε f (S k) →
        (1 / 2 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ f (S k)) ∧
    (2 ≤ Fintype.card X → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k ≤ (Fintype.card X : ℝ)) := by
  have hnpos : (0:ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card X : ℝ) with hn
  have hα : 0 ≤ ε / n ^ 2 := div_nonneg hε.le (sq_nonneg _)
  have hnα : n * (ε / n ^ 2) = ε / n := by field_simp
  have hen : 0 < ε / n := div_pos hε hnpos
  have hopt0 : 0 ≤ NonmonotoneSubmod.Shared.OPT f := le_trans (hf0 ∅) (nsls_le_opt f ∅)
  obtain ⟨C, -, hC⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Finset X)) f
  have hCopt : NonmonotoneSubmod.Shared.OPT f = f C := hC
  refine ⟨?_, ?_, ?_⟩
  · intro S k _ hterm
    have hA := nsls_term ε f (S k) hterm
    have h := nsls_any f hf0 hf _ hα (S k) hA C
    rw [hnα] at h
    unfold lsOutput
    have m1 := le_max_left (f (S k)) (f (S k)ᶜ)
    have m2 := le_max_right (f (S k)) (f (S k)ᶜ)
    set M := max (f (S k)) (f (S k)ᶜ)
    have hM : 0 ≤ M := le_trans (hf0 _) m1
    rw [hCopt]
    have hO : f C ≤ (3 + 2 * (ε / n)) * M := by nlinarith
    rcases le_or_gt (1/3 - ε/n) 0 with hc | hc
    · nlinarith [hf0 C]
    · have : (1/3 - ε/n) * (3 + 2 * (ε / n)) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hO hc.le]
  · intro hsym S k _ hterm
    have hA := nsls_term ε f (S k) hterm
    have h := nsls_any_sym f hf0 hf hsym _ hα (S k) hA C
    rw [hnα] at h
    have hM := hf0 (S k)
    rw [hCopt]
    rcases le_or_gt (1/2 - ε/n) 0 with hc | hc
    · nlinarith [hf0 C]
    · have : (1/2 - ε/n) * (2 * (1 + ε / n)) ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h hc.le]
  · intro h2 S k hrun
    obtain ⟨v, hv, hS0⟩ := hrun.1
    have hopt := nsls_opt f hf0 hf h2 v hv
    have hg := nsls_growth ε hε f S k hrun v hS0 k le_rfl
    have hk := nsls_le_opt f (S k)
    unfold lsFactor at hg
    rw [← hn] at hg
    rcases (hf0 {v}).lt_or_eq with hp | hz
    · have : (1 + ε / n ^ 2) ^ k * f {v} ≤ n * f {v} := by linarith
      exact le_of_mul_le_mul_right this hp
    · rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0; simp; have : (2:ℝ) ≤ n := by rw [hn]; exact_mod_cast h2
        linarith
      · exfalso
        have hs := hrun.2 0 hk0
        have h1 : lsFactor X ε * f (S 0) < f (S 1) := by
          rcases hs with ⟨a, _, hlt, h⟩ | ⟨_, a, _, hlt, h⟩
          · rw [h]; exact hlt
          · rw [h]; exact hlt
        rw [hS0, ← hz] at h1
        have := nsls_le_opt f (S 1)
        rw [← hz, mul_zero] at hopt
        linarith

end NonmonotoneSubmod.LocalSearch

open NonmonotoneSubmod.LocalSearch


theorem solution {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (f : Finset X → ℝ) (hf0 : ∀ S : Finset X, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k → IsLSTerminal ε f (S k) →
        (1 / 3 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ lsOutput f (S k)) ∧
    (NonmonotoneSubmod.Shared.SymmetricSetFun f → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        IsLSTerminal ε f (S k) →
        (1 / 2 - ε / (Fintype.card X : ℝ)) * NonmonotoneSubmod.Shared.OPT f ≤ f (S k)) ∧
    (2 ≤ Fintype.card X → ∀ (S : ℕ → Finset X) (k : ℕ), IsLSRun ε f S k →
        (1 + ε / (Fintype.card X : ℝ) ^ 2) ^ k ≤ (Fintype.card X : ℝ)) := by
  exact ls_core f hf0 hf ε hε
