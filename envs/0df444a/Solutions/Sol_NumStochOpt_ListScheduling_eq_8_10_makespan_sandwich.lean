-- Prove2me | solution 1 for NumStochOpt.ListScheduling.eq_8_10_makespan_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T20:33:02.698349+00:00
-- url     : https://prove2.me/submissions/c840e416-7ab5-46dd-9935-aec31d5f18c6

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule

set_option autoImplicit false

open NumStochOpt.ListScheduling in
theorem de116494_fa_some {m : ℕ} (hm : 1 ≤ m) (ℓ : Fin m → ℝ) :
    ∃ i, firstAvailable ℓ = some i := by
  have hne : (Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).Nonempty := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin m)) ℓ
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => hi k (Finset.mem_univ _)⟩⟩
  exact ⟨_, by unfold firstAvailable; rw [dif_pos hne]⟩

open NumStochOpt.ListScheduling in
theorem de116494_fa_min {m : ℕ} (ℓ : Fin m → ℝ) (i : Fin m) (h : firstAvailable ℓ = some i) :
    ∀ k, ℓ i ≤ ℓ k := by
  unfold firstAvailable at h
  split_ifs at h with hne
  · cases h
    have := Finset.min'_mem _ hne
    exact (Finset.mem_filter.1 this).2

open NumStochOpt.ListScheduling in
theorem de116494_sum_loads {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (k : ℕ) :
    ∑ i, lsLoads m p k i = ∑ j ∈ Finset.range k, p j := by
  induction k with
  | zero => simp [lsLoads]
  | succ k ih =>
    obtain ⟨i0, hi0⟩ := de116494_fa_some hm (lsLoads m p k)
    have : ∀ i, lsLoads m p (k + 1) i = lsLoads m p k i + (if i0 = i then p k else 0) := by
      intro i
      simp only [lsLoads, hi0, Option.some.injEq]
      split_ifs <;> simp
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ih,
      Finset.sum_range_succ]

open NumStochOpt.ListScheduling in
theorem de116494_upper {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (M : ℝ) (n : ℕ)
    (hM : ∀ j, j < n → p j ≤ M) (hM0 : 0 ≤ M) :
    ∀ k, k ≤ n → ∀ i, lsLoads m p k i ≤ (∑ j ∈ Finset.range k, p j) / m + M := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  intro k
  induction k with
  | zero => intro _ i; simp [lsLoads, hM0]
  | succ k ih =>
    intro hk i
    have ih' := ih (by omega)
    obtain ⟨i0, hi0⟩ := de116494_fa_some hm (lsLoads m p k)
    have hmin := de116494_fa_min _ _ hi0
    have hS : ∑ j ∈ Finset.range (k+1), p j = ∑ j ∈ Finset.range k, p j + p k :=
      Finset.sum_range_succ _ _
    have hpk := hp k
    have hpkM := hM k (by omega)
    simp only [lsLoads, hi0, Option.some.injEq]
    split_ifs with h
    · subst h
      -- m * ℓ i0 ≤ ∑ ℓ = S_k
      have hsum := de116494_sum_loads hm p k
      have hle : (m : ℝ) * lsLoads m p k i0 ≤ ∑ j ∈ Finset.range k, p j := by
        rw [← hsum]
        have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin m)) (lsLoads m p k)
          (lsLoads m p k i0) (fun x _ => hmin x)
        simpa [nsmul_eq_mul] using this
      have h1 : lsLoads m p k i0 ≤ (∑ j ∈ Finset.range k, p j) / m := by
        rw [le_div_iff₀ hmpos]; linarith
      rw [hS]
      have : (∑ j ∈ Finset.range k, p j) / m ≤ (∑ j ∈ Finset.range k, p j + p k) / m := by
        apply div_le_div_of_nonneg_right _ hmpos.le; linarith
      linarith
    · rw [hS]
      have : (∑ j ∈ Finset.range k, p j) / m ≤ (∑ j ∈ Finset.range k, p j + p k) / m := by
        apply div_le_div_of_nonneg_right _ hmpos.le; linarith
      linarith [ih' i]

open NumStochOpt.ListScheduling in
theorem de116494_assign {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (k : ℕ) (i : Fin m) :
    lsLoads m p k i = ∑ j ∈ Finset.range k,
      (if (firstAvailable (lsLoads m p j)).getD ⟨0, hm⟩ = i then p j else 0) := by
  induction k with
  | zero => simp [lsLoads]
  | succ k ih =>
    obtain ⟨i0, hi0⟩ := de116494_fa_some hm (lsLoads m p k)
    rw [Finset.sum_range_succ, ← ih]
    simp only [lsLoads, hi0, Option.some.injEq, Option.getD_some]
    split_ifs <;> simp

open NumStochOpt.ListScheduling in
theorem de116494_bdd {α : Type} [Finite α] (f : α → ℝ) : BddAbove (Set.range f) ∧ BddBelow (Set.range f) :=
  ⟨(Set.finite_range f).bddAbove, (Set.finite_range f).bddBelow⟩

open NumStochOpt.ListScheduling in
theorem de116494_main (n m : ℕ) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.range n, p j) ≤ m * optMakespan n m p ∧
      optMakespan n m p ≤ listMakespan n m p ∧
      m * listMakespan n m p ≤ (∑ j ∈ Finset.range n, p j) + m * maxProcTime n p := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_⟩
  · -- averaging bound
    have key : ∀ σ : Fin n → Fin m, (∑ j ∈ Finset.range n, p j) ≤ m * makespan p σ := by
      intro σ
      have hsum : ∑ i, machineLoad p σ i = ∑ j ∈ Finset.range n, p j := by
        unfold machineLoad
        rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp
      rw [← hsum]
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin m)) (machineLoad p σ)
        (makespan p σ) (fun i _ => le_ciSup (de116494_bdd _).1 i)
      simpa [nsmul_eq_mul] using this
    have h : (∑ j ∈ Finset.range n, p j) / m ≤ optMakespan n m p := by
      unfold optMakespan
      apply le_ciInf
      intro σ
      rw [div_le_iff₀ hmpos]; linarith [key σ]
    rw [div_le_iff₀ hmpos] at h; linarith
  · -- the list schedule is one assignment
    let σ : Fin n → Fin m := fun j => (firstAvailable (lsLoads m p j)).getD ⟨0, hm⟩
    have heq : makespan p σ = listMakespan n m p := by
      unfold makespan listMakespan
      congr 1; funext i
      unfold machineLoad
      rw [de116494_assign hm p n i, ← Fin.sum_univ_eq_sum_range
        (fun j => if (firstAvailable (lsLoads m p j)).getD ⟨0, hm⟩ = i then p j else 0)]
    rw [← heq]
    unfold optMakespan
    exact ciInf_le (de116494_bdd _).2 σ
  · -- Graham bound
    have hM : ∀ j, j < n → p j ≤ maxProcTime n p := fun j hj =>
      le_ciSup (f := fun j : Fin n => p (j : ℕ)) (de116494_bdd _).1 ⟨j, hj⟩
    have hM0 : 0 ≤ maxProcTime n p := le_trans (hp 0) (hM 0 (by omega))
    have hup := de116494_upper hm p hp (maxProcTime n p) n hM hM0 n le_rfl
    have : listMakespan n m p ≤ (∑ j ∈ Finset.range n, p j) / m + maxProcTime n p := by
      unfold listMakespan
      exact ciSup_le hup
    have h2 : (m : ℝ) * ((∑ j ∈ Finset.range n, p j) / m) = ∑ j ∈ Finset.range n, p j := by
      field_simp
    nlinarith

open NumStochOpt.ListScheduling in
theorem solution (n m : ℕ) (p : ℕ → ℝ) (μ : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hn : 1 ≤ n) (hm : 1 ≤ m) (hμ : 0 < μ) :
    ((∑ j ∈ Finset.range n, p j) - n * μ) / (n * μ) + 1
        ≤ optMakespan n m p / (n * μ / m) ∧
      optMakespan n m p / (n * μ / m) ≤ listMakespan n m p / (n * μ / m) ∧
      listMakespan n m p / (n * μ / m)
        ≤ ((∑ j ∈ Finset.range n, p j) - n * μ) / (n * μ) + 1
            + m * maxProcTime n p / (n * μ) := by
  obtain ⟨h1, h2, h3⟩ := de116494_main n m p hp hn hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnμ : (0 : ℝ) < n * μ := mul_pos hnpos hμ
  set S := ∑ j ∈ Finset.range n, p j
  have e1 : (S - n * μ) / (n * μ) + 1 = S / (n * μ) := by
    field_simp; ring
  have e2 : ∀ X : ℝ, X / (n * μ / m) = (m * X) / (n * μ) := by
    intro X; field_simp
  rw [e1, e2, e2]
  refine ⟨?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right h1 hnμ.le
  · apply div_le_div_of_nonneg_right _ hnμ.le
    exact mul_le_mul_of_nonneg_left h2 hmpos.le
  · rw [← add_div]
    exact div_le_div_of_nonneg_right h3 hnμ.le
