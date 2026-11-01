-- Prove2me | solution 1 for JobShopLTAS.Core.Pmax_le_optMakespan
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T12:16:49.128463+00:00
-- url     : https://prove2.me/submissions/1c3430be-8978-48a7-9235-59e8cd5ed201

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

open JobShopLTAS.Core

private def beforeOp {m n : ℕ} {inst : Instance m n} (o₁ o₂ : inst.Op) : Prop :=
  o₁.1.val < o₂.1.val ∨ (o₁.1.val = o₂.1.val ∧ o₁.2.val < o₂.2.val)

private instance {m n : ℕ} {inst : Instance m n} : DecidableRel (beforeOp (inst := inst)) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

private noncomputable def sSer {m n : ℕ} (inst : Instance m n) (o : inst.Op) : ℝ :=
  ∑ o' ∈ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o), inst.proc o'

private lemma sSer_step {m n : ℕ} (inst : Instance m n) {o₁ o₂ : inst.Op}
    (h : beforeOp o₁ o₂) :
    sSer inst o₁ + inst.proc o₁ ≤ sSer inst o₂ := by
  have hnot : o₁ ∉ Finset.univ.filter (fun o' : inst.Op => beforeOp o' o₁) := by
    simp [beforeOp]
  unfold sSer
  rw [add_comm, ← Finset.sum_insert hnot]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro o' ho'
    rw [Finset.mem_insert, Finset.mem_filter] at ho'
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ho' with rfl | ⟨_, h'⟩
    · exact h
    · unfold beforeOp at h h' ⊢
      omega
  · intro o' _ _
    exact inst.p_nonneg o'.1 o'.2

private lemma sSer_feasible {m n : ℕ} (inst : Instance m n) :
    inst.IsFeasibleSchedule Finset.univ (sSer inst) where
  start_nonneg o _ := Finset.sum_nonneg (fun o' _ => inst.p_nonneg o'.1 o'.2)
  precedence j _ i i' hii' := by
    apply sSer_step inst (o₁ := ⟨j, i⟩) (o₂ := ⟨j, i'⟩)
    exact Or.inr ⟨rfl, by dsimp; omega⟩
  machine_disjoint o o' _ _ hne _ := by
    have htrich : beforeOp o o' ∨ beforeOp o' o := by
      unfold beforeOp
      by_cases h1 : o.1.val = o'.1.val
      · have h2 : o.2.val ≠ o'.2.val := by
          intro h2
          apply hne
          rcases o with ⟨j₁, i₁⟩
          rcases o' with ⟨j₂, i₂⟩
          have hj : j₁ = j₂ := Fin.ext h1
          subst hj
          congr
          exact Fin.ext h2
        omega
      · omega
    rcases htrich with h | h
    · exact Or.inl (sSer_step inst h)
    · exact Or.inr (sSer_step inst h)

private lemma makespan_nonneg {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ)
    (hs : inst.IsFeasibleSchedule Finset.univ s) :
    0 ≤ inst.makespan Finset.univ s := by
  unfold Instance.makespan
  by_cases h : Nonempty {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))}
  · rcases h with ⟨⟨o₀, ho₀⟩⟩
    have h0 : 0 ≤ s o₀ + inst.proc o₀ :=
      add_nonneg (hs.start_nonneg o₀ ho₀) (inst.p_nonneg o₀.1 o₀.2)
    exact le_trans h0 (le_ciSup (f := fun o : {o : inst.Op // o.1 ∈ (Finset.univ : Finset (Fin n))} => s o.1 + inst.proc o.1) (Set.finite_range _).bddAbove ⟨o₀, ho₀⟩)
  · rw [not_nonempty_iff] at h
    simp

private lemma sum_disjoint_le {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ)
    (hs : inst.IsFeasibleSchedule Finset.univ s) (t : Fin m) :
    ∀ k : ℕ, ∀ S : Finset inst.Op, S.card = k →
      (∀ o ∈ S, inst.mach o = t ∧ 0 < inst.proc o) →
      ∀ M : ℝ, 0 ≤ M → (∀ o ∈ S, s o + inst.proc o ≤ M) →
      ∑ o ∈ S, inst.proc o ≤ M
  | 0, S, hcard, _, M, hM, _ => by
    rw [Finset.card_eq_zero.mp hcard]
    simpa using hM
  | k + 1, S, hcard, hS, M, _, hSM => by
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    rcases Finset.exists_max_image S s hne with ⟨oStar, hoStar, hmax⟩
    have hoStar_prop := hS oStar hoStar
    have hM' : 0 ≤ s oStar := hs.start_nonneg oStar (Finset.mem_univ _)
    have hS' : ∀ o ∈ S.erase oStar, inst.mach o = t ∧ 0 < inst.proc o :=
      fun o ho => hS o (Finset.mem_of_mem_erase ho)
    have hSM' : ∀ o ∈ S.erase oStar, s o + inst.proc o ≤ s oStar := by
      intro o ho
      have hne_o : o ≠ oStar := Finset.ne_of_mem_erase ho
      have ho_in : o ∈ S := Finset.mem_of_mem_erase ho
      have hmach : inst.mach o = inst.mach oStar := by
        rw [(hS o ho_in).1, hoStar_prop.1]
      rcases hs.machine_disjoint o oStar (Finset.mem_univ _) (Finset.mem_univ _) hne_o hmach with h1 | h2
      · exact h1
      · have hle := hmax o ho_in
        linarith [hoStar_prop.2]
    have hcard' : (S.erase oStar).card = k := by
      rw [Finset.card_erase_of_mem hoStar, hcard]
      rfl
    have ih := sum_disjoint_le inst s hs t k (S.erase oStar) hcard' hS' (s oStar) hM' hSM'
    have hsum := (Finset.add_sum_erase S inst.proc hoStar).symm
    have htop := hSM oStar hoStar
    linarith

private lemma load_le_makespan {m n : ℕ} (inst : Instance m n) (s : inst.Op → ℝ)
    (hs : inst.IsFeasibleSchedule Finset.univ s) (t : Fin m) :
    inst.load t ≤ inst.makespan Finset.univ s := by
  set S₀ := (Finset.univ.filter (fun o : inst.Op => inst.mach o = t)).filter (fun o => 0 < inst.proc o)
  have hload : inst.load t = ∑ o ∈ S₀, inst.proc o := by
    unfold Instance.load
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro o ho hnot
    rw [Finset.mem_filter] at hnot
    push_neg at hnot
    exact le_antisymm (hnot ho) (inst.p_nonneg o.1 o.2)
  rw [hload]
  apply sum_disjoint_le inst s hs t S₀.card S₀ rfl
  · intro o ho
    rw [Finset.mem_filter, Finset.mem_filter] at ho
    exact ⟨ho.1.2, ho.2⟩
  · exact makespan_nonneg inst s hs
  · intro o _
    exact le_ciSup (f := fun o' : {o' : inst.Op // o'.1 ∈ (Finset.univ : Finset (Fin n))} => s o'.1 + inst.proc o'.1) (Set.finite_range _).bddAbove ⟨o, Finset.mem_univ _⟩

theorem solution {m n : ℕ} (inst : Instance m n) :
    inst.Pmax ≤ inst.optMakespan Finset.univ := by
  unfold Instance.optMakespan
  apply le_csInf
  · exact ⟨inst.makespan Finset.univ (sSer inst), sSer inst, sSer_feasible inst, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    unfold Instance.Pmax
    by_cases hm : Nonempty (Fin m)
    · exact ciSup_le (fun t => load_le_makespan inst s hs t)
    · rw [not_nonempty_iff] at hm
      simp [makespan_nonneg inst s hs]
