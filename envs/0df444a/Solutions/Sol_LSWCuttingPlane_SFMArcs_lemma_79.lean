-- Prove2me | solution 1 for LSWCuttingPlane.SFMArcs.lemma_79
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T21:01:42.909347+00:00
-- url     : https://prove2.me/submissions/2023df3a-62c1-4550-969d-037631cf42b4

import Mathlib
import Definitions.Def_LSWCuttingPlane_SFMArcs_Setting

set_option autoImplicit false

namespace LSW79Aux

open Finset LSWCuttingPlane.SFMArcs

/-- Diminishing returns extended to adding a whole set `D`. -/
theorem sub_ext {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f)
    (X Y : Finset (Fin n)) (hXY : X ⊆ Y) :
    ∀ D : Finset (Fin n), Disjoint D Y → f (Y ∪ D) - f Y ≤ f (X ∪ D) - f X := by
  intro D
  induction D using Finset.induction_on with
  | empty => intro _; simp
  | insert i D hi ih =>
    intro hdis
    have hiY : i ∉ Y := by
      intro h; exact Finset.disjoint_left.mp hdis (Finset.mem_insert_self i D) h
    have hdis' : Disjoint D Y := Finset.disjoint_of_subset_left (Finset.subset_insert i D) hdis
    have hiYD : i ∉ Y ∪ D := by
      simp only [Finset.mem_union, not_or]; exact ⟨hiY, hi⟩
    have h1 := hf (X ∪ D) (Y ∪ D) i (Finset.union_subset_union hXY (le_refl D)) hiYD
    have e1 : Y ∪ insert i D = insert i (Y ∪ D) := by
      ext x; simp [Finset.mem_union, Finset.mem_insert]
    have e2 : X ∪ insert i D = insert i (X ∪ D) := by
      ext x; simp [Finset.mem_union, Finset.mem_insert]
    rw [e1, e2]
    have := ih hdis'
    linarith

theorem lattice_ineq {n : ℕ} (f : Finset (Fin n) → ℤ) (hf : Submodular f)
    (S T : Finset (Fin n)) : f (S ∪ T) + f (S ∩ T) ≤ f S + f T := by
  have h := sub_ext f hf (S ∩ T) S Finset.inter_subset_left (T \ S) Finset.sdiff_disjoint
  have e1 : S ∪ (T \ S) = S ∪ T := Finset.union_sdiff_self_eq_union
  have e2 : S ∩ T ∪ (T \ S) = T := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [e1, e2] at h
  linarith

theorem R_sub {n : ℕ} (A : Fin n → Fin n → Prop) (p : Fin n) (S : Finset (Fin n))
    (hS : S ∈ ringFamily A) (hp : p ∈ S) : R A p ⊆ S := by
  intro j hj
  classical
  have hj' : Relation.ReflTransGen A p j := by
    simpa [R] using hj
  induction hj' with
  | refl => exact hp
  | tail _ hbc ih => exact hS _ _ hbc (ih (by simp [R]; assumption))

theorem mem_R {n : ℕ} (A : Fin n → Fin n → Prop) (p j : Fin n) :
    j ∈ R A p ↔ Relation.ReflTransGen A p j := by
  classical
  simp [R]

theorem Rerase_ring {n : ℕ} (A : Fin n → Fin n → Prop) (hA : Acyclic A) (p : Fin n) :
    (R A p).erase p ∈ ringFamily A := by
  intro i j hij hi
  rw [Finset.mem_erase, mem_R] at hi ⊢
  refine ⟨?_, hi.2.tail hij⟩
  rintro rfl
  exact hA j (Relation.TransGen.tail' hi.2 hij)

theorem inter_ring {n : ℕ} (A : Fin n → Fin n → Prop) (S T : Finset (Fin n))
    (hS : S ∈ ringFamily A) (hT : T ∈ ringFamily A) : S ∩ T ∈ ringFamily A := by
  intro i j hij hi
  rw [Finset.mem_inter] at hi ⊢
  exact ⟨hS i j hij hi.1, hT i j hij hi.2⟩

theorem union_ring {n : ℕ} (A : Fin n → Fin n → Prop) (S T : Finset (Fin n))
    (hS : S ∈ ringFamily A) (hT : T ∈ ringFamily A) : S ∪ T ∈ ringFamily A := by
  intro i j hij hi
  rw [Finset.mem_union] at hi ⊢
  rcases hi with h | h
  · exact Or.inl (hS i j hij h)
  · exact Or.inr (hT i j hij h)

theorem inter_min {n : ℕ} (A : Fin n → Fin n → Prop) (f : Finset (Fin n) → ℤ) (hf : Submodular f)
    (S T : Finset (Fin n)) (hS : IsMinimizer A f S) (hT : IsMinimizer A f T) :
    IsMinimizer A f (S ∩ T) := by
  refine ⟨inter_ring A S T hS.1 hT.1, fun U hU => ?_⟩
  have h1 := lattice_ineq f hf S T
  have h2 := hS.2 _ (union_ring A S T hS.1 hT.1)
  have h3 := hT.2 _ hS.1
  have h4 := hS.2 U hU
  linarith

theorem consistent_le {n : ℕ} (A : Fin n → Fin n → Prop) (σ : Equiv.Perm (Fin n))
    (hσ : Consistent A σ) (p j : Fin n) (h : Relation.ReflTransGen A p j) : σ j ≤ σ p := by
  induction h with
  | refl => exact le_refl _
  | tail _ hbc ih => exact le_trans (le_of_lt (hσ _ _ hbc)) ih

/-- Existence of a minimizer containing `p` inside `R p`, by strong induction on the cardinality. -/
theorem exists_small {n : ℕ} (A : Fin n → Fin n → Prop) (f : Finset (Fin n) → ℤ) (hf : Submodular f)
    (p : Fin n)
    (h : ∀ q, q ∉ R A p → ∃ S : Finset (Fin n), IsMinimizer A f S ∧ p ∈ S ∧ q ∉ S) :
    ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k → IsMinimizer A f S → p ∈ S →
      ∃ T : Finset (Fin n), IsMinimizer A f T ∧ p ∈ T ∧ T ⊆ R A p := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S hk hS hpS
    by_cases hsub : S ⊆ R A p
    · exact ⟨S, hS, hpS, hsub⟩
    · obtain ⟨q, hqS, hqR⟩ := Finset.not_subset.mp hsub
      obtain ⟨S', hS', hpS', hqS'⟩ := h q hqR
      have hlt : (S ∩ S').card < k := by
        rw [← hk]
        apply Finset.card_lt_card
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
        intro heq
        have : q ∈ S ∩ S' := by rw [heq]; exact hqS
        exact hqS' (Finset.mem_inter.mp this).2
      exact ih _ hlt (S ∩ S') rfl (inter_min A f hf S S' hS hS')
        (Finset.mem_inter.mpr ⟨hpS, hpS'⟩)

end LSW79Aux

open Finset LSWCuttingPlane.SFMArcs in
theorem solution {n : ℕ} [NeZero n] (f : Finset (Fin n) → ℤ) (hf : Submodular f) (hf0 : f ∅ = 0)
    (A : Fin n → Fin n → Prop) (hA : Acyclic A)
    {ι : Type} [Fintype ι] (lam : ι → ℝ) (σs : ι → Equiv.Perm (Fin n))
    (hcomb : IsConsistentComb A lam σs) (hnd : NonDegenerate (combo f lam σs))
    (p : Fin n) (hp : (n : ℝ) ^ 4 * ymax (combo f lam σs) < (upper f A p : ℝ)) :
    ∃ q, q ∉ R A p ∧ ∀ S : Finset (Fin n), IsMinimizer A f S → p ∈ S → q ∈ S := by
  classical
  -- ymax is positive
  obtain ⟨i0, hi0⟩ := hnd.1
  have hle : ∀ j, combo f lam σs j ≤ ymax (combo f lam σs) := fun j =>
    Finset.le_sup' (combo f lam σs) (Finset.mem_univ j)
  have hypos : 0 < ymax (combo f lam σs) := lt_of_lt_of_le hi0 (hle i0)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by
      have := NeZero.pos n
      exact_mod_cast this
    exact one_le_pow₀ this
  by_contra hcon
  push Not at hcon
  by_cases hRu : R A p = Finset.univ
  · -- every element is a descendant of p, so p is last in every σ_k
    have hbefore : ∀ k, before (σs k) p = Finset.univ.erase p := by
      intro k
      ext u
      simp only [before, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true]
      constructor
      · intro h heq; rw [heq] at h; exact lt_irrefl _ h
      · intro hne
        have hu : u ∈ R A p := by rw [hRu]; exact Finset.mem_univ u
        have hle' := LSW79Aux.consistent_le A (σs k) (hcomb.2.2 k) p u
          ((LSW79Aux.mem_R A p u).mp hu)
        exact lt_of_le_of_ne hle' (fun h => hne ((σs k).injective h))
    have hbfs : ∀ k, bfs f (σs k) p = (upper f A p : ℝ) := by
      intro k
      unfold bfs upper
      rw [hbefore k, hRu, Finset.insert_erase (Finset.mem_univ p)]
    have hyp : combo f lam σs p = (upper f A p : ℝ) := by
      unfold combo
      simp_rw [hbfs]
      rw [← Finset.sum_mul, hcomb.2.1, one_mul]
    have h1 := hle p
    have h2 : ymax (combo f lam σs) ≤ (n : ℝ) ^ 4 * ymax (combo f lam σs) := by
      nlinarith
    linarith
  · obtain ⟨q0, hq0⟩ : ∃ q, q ∉ R A p := by
      by_contra hall
      push Not at hall
      exact hRu (Finset.eq_univ_iff_forall.mpr hall)
    obtain ⟨S0, hS0, hpS0, -⟩ := hcon q0 hq0
    obtain ⟨T, hT, hpT, hTR⟩ :=
      LSW79Aux.exists_small A f hf p hcon S0.card S0 rfl hS0 hpS0
    have hRT : R A p ⊆ T := LSW79Aux.R_sub A p T hT.1 hpT
    have hTeq : T = R A p := Finset.Subset.antisymm hTR hRT
    have hup := hT.2 _ (LSW79Aux.Rerase_ring A hA p)
    rw [hTeq] at hup
    have hup' : upper f A p ≤ 0 := by unfold upper; linarith
    have hup'' : (upper f A p : ℝ) ≤ 0 := by exact_mod_cast hup'
    have : 0 ≤ (n : ℝ) ^ 4 * ymax (combo f lam σs) := by positivity
    linarith
