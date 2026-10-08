-- Prove2me | solution 1 for KelsoCrawford.FirmOptimal.equilibrium_is_discrete_strict_core
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:02:32.758444+00:00
-- url     : https://prove2.me/submissions/ef7d6583-90ba-41a5-85af-ed401a18f79d

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model
import Definitions.Def_KelsoCrawford_FirmOptimal_Process
import Definitions.Def_KelsoCrawford_FirmOptimal_NoTies
open KelsoCrawford.FirmOptimal KelsoCrawford.Process

private theorem grid_gap {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : KelsoCrawford.FirmOptimal.Market W F)
    {δ : ℝ} (hδ : 0 < δ) {i : W} {j : F} {s r : ℝ}
    (hs : s ∈ M.grid δ i j) (hr : r ∈ M.grid δ i j) (hlt : s < r) : s + δ ≤ r := by
  obtain ⟨a, rfl⟩ := hs
  obtain ⟨b, rfl⟩ := hr
  have hab : (a : ℝ) < b := by nlinarith
  have habN : a < b := by exact_mod_cast hab
  have hnext : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
  nlinarith

private theorem run_facts {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hu : M.UtilityRegular)
    (ρ : Run W F) (hr : M.IsRun δ ρ) :
    ∀ t, (∀ i, i ∈ ρ.offers t (ρ.choice t i)) ∧
      (∀ i j, ρ.sal t i j ∈ M.grid δ i j) ∧
      (∀ i, M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i)) ≤
        M.u i (ρ.choice (t+1) i) (ρ.sal (t+1) i (ρ.choice (t+1) i))) := by
  have h0 := hr.1.1
  have ho := hr.1.2
  have hretain := hr.2.1
  have hchoice := hr.2.2.1
  have hsal := hr.2.2.2
  have hav : ∀ t i, i ∈ ρ.offers t (ρ.choice t i) := by
    intro t
    induction t with
    | zero => intro i; rw [ho]; simp
    | succ t ih =>
      intro i
      have hm : i ∈ ρ.offers (t+1) (ρ.choice t i) :=
        (hretain t (ρ.choice t i)).2 (by simp [Run.Rejects, ih i])
      exact (hchoice (t+1) i ⟨_, hm⟩).1
  have hg : ∀ t i j, ρ.sal t i j ∈ M.grid δ i j := by
    intro t
    induction t with
    | zero => intro i j; exact ⟨0, by simp [h0]⟩
    | succ t ih =>
      intro i j
      rw [hsal]
      split_ifs
      · obtain ⟨k, hk⟩ := ih i j
        exact ⟨k+1, by rw [hk]; push_cast; ring⟩
      · exact ih i j
  intro t
  refine ⟨hav t, hg t, ?_⟩
  intro i
  have hm : i ∈ ρ.offers (t+1) (ρ.choice t i) :=
    (hretain t (ρ.choice t i)).2 (by simp [Run.Rejects, hav t i])
  have heq : ρ.sal (t+1) i (ρ.choice t i) = ρ.sal t i (ρ.choice t i) := by
    rw [hsal]; simp [Run.Rejects]
  simpa [heq] using (hchoice (t+1) i ⟨_, hm⟩).2 (ρ.choice t i) hm

private theorem strict_available {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hδ : 0 < δ)
    (hu : M.UtilityRegular) (ρ : Run W F) (hr : M.IsRun δ ρ) :
    ∀ t i j r, r ∈ M.grid δ i j →
      M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i)) < M.u i j r → ρ.sal t i j ≤ r := by
  intro t
  induction t with
  | zero =>
    intro i j r hrg hlt
    obtain ⟨k, hk⟩ := hrg
    rw [hr.1.1, hk]
    have hn : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    linarith
  | succ t ih =>
    intro i j r hrg hlt
    have huinc := (run_facts M δ hu ρ hr t).2.2 i
    have hprev := lt_of_le_of_lt huinc hlt
    have hle := ih i j r hrg hprev
    rw [hr.2.2.2]
    split_ifs with hrej
    · have hbest := (hr.2.2.1 t i ⟨j, hrej.1⟩).2 j hrej.1
      have hsr : ρ.sal t i j < r := (hu i j).1.lt_iff_lt.mp (lt_of_le_of_lt hbest hprev)
      exact grid_gap M hδ ((run_facts M δ hu ρ hr t).2.1 i j) hrg hsr
    · exact hle

private theorem demand_at_stop {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hu : M.UtilityRegular)
    (hMP : M.MP) (ρ : Run W F) (hr : M.IsRun δ ρ) (T : ℕ) (hstop : ρ.Stopped T) :
    ∀ j, IsDemanded (M.y j) (fun i => ρ.sal T i j) ((ρ.outcome T).hired j) := by
  have heq : ∀ j, (ρ.outcome T).hired j = ρ.offers T j := by
    intro j
    ext i
    change (i ∈ Finset.univ.filter (fun a => ρ.choice T a = j)) ↔ i ∈ ρ.offers T j
    rw [Finset.mem_filter_univ]
    constructor
    · intro hij; rw [← hij]; exact (run_facts M δ hu ρ hr T).1 i
    · intro hi
      by_contra hne
      exact hstop i j ⟨hi, hne⟩
  intro j
  rw [heq]
  cases T with
  | succ t => exact (hr.2.1 t j).1
  | zero =>
    rw [hr.1.1, hr.1.2]
    intro C
    have hadd : ∀ D : Finset W, profit (M.y j) C (fun i => M.σ i j) ≤
        profit (M.y j) (C ∪ D) (fun i => M.σ i j) := by
      intro D
      induction D using Finset.induction_on with
      | empty => simp
      | @insert i D hi ih =>
        by_cases hic : i ∈ C ∪ D
        · simpa [Finset.union_insert, Finset.insert_eq_of_mem hic] using ih
        · have hmp := hMP i j (C ∪ D) hic
          have hsum : profit (M.y j) (C ∪ D) (fun i => M.σ i j) ≤
              profit (M.y j) (insert i (C ∪ D)) (fun i => M.σ i j) := by
            simp only [profit, Finset.sum_insert hic]
            linarith
          simpa [Finset.union_insert] using le_trans ih hsum
    have hU : C ∪ Finset.univ = (Finset.univ : Finset W) := by ext i; simp
    simpa only [hU] using hadd Finset.univ

private theorem stopped_core {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hδ : 0 < δ)
    (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (ρ : Run W F) (hr : M.IsRun δ ρ) (T : ℕ) (hstop : ρ.Stopped T) :
    M.IsCore (M.grid δ) (ρ.outcome T) := by
  have hd := demand_at_stop M δ hu hMP ρ hr T hstop
  have hg := (run_facts M δ hu ρ hr T).2.1
  have hprof : ∀ j, profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal =
      profit (M.y j) ((ρ.outcome T).hired j) (fun i => ρ.sal T i j) := by
    intro j
    unfold profit
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : ρ.choice T i = j := (Finset.mem_filter.mp hi).2
    simp [Run.outcome, hij]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i
    obtain ⟨k, hk⟩ := hg i (ρ.choice T i)
    change M.σ i (ρ.choice T i) ≤ ρ.sal T i (ρ.choice T i)
    rw [hk]
    have hn : 0 ≤ (k : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    linarith
  · intro j
    rw [hprof j]
    have h := hd j ∅
    simpa [profit, hNFL j] using h
  · intro i; exact hg i (ρ.choice T i)
  · rintro ⟨j, C, r, hrg, hworker, hfirm⟩
    have hle : ∀ i ∈ C, ρ.sal T i j ≤ r i := by
      intro i hi
      exact strict_available M δ hδ hu ρ hr T i j (r i) (hrg i hi) (hworker i hi)
    have hsum := Finset.sum_le_sum hle
    have hdem := hd j C
    rw [hprof j] at hfirm
    unfold profit at hfirm hdem
    linarith

theorem solution
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ T, ρ.Stopped T → M.IsStrictCore (M.grid δ) (ρ.outcome T) := by
  intro ρ hr T hstop
  have hc := stopped_core M δ hδ hu hMP hNFL ρ hr T hstop
  have hd := demand_at_stop M δ hu hMP ρ hr T hstop
  refine ⟨hc.1, hc.2.1, ?_⟩
  rintro ⟨j, C, r, hrg, hw, hp, hstrict⟩
  have hle : ∀ i ∈ C, ρ.sal T i j ≤ r i := by
    intro i hi
    by_cases hij : j = ρ.choice T i
    · subst j
      exact (hu i (ρ.choice T i)).1.le_iff_le.mp (hw i hi)
    · have hne := hNTW _ hc i j hij (r i) (hrg i hi)
      have hlt := lt_of_le_of_ne (hw i hi) hne
      exact strict_available M δ hδ hu ρ hr T i j (r i) (hrg i hi) hlt
  have hprof : profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal =
      profit (M.y j) ((ρ.outcome T).hired j) (fun i => ρ.sal T i j) := by
    unfold profit
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hij : ρ.choice T i = j := (Finset.mem_filter.mp hi).2
    simp [Run.outcome, hij]
  have hupper : profit (M.y j) C r ≤ profit (M.y j) ((ρ.outcome T).hired j) (ρ.outcome T).sal := by
    rw [hprof]
    apply le_trans _ (hd j C)
    unfold profit
    exact sub_le_sub_left (Finset.sum_le_sum hle) _
  have heq := le_antisymm hp hupper
  rcases hstrict with hwstrict | hpstrict
  · obtain ⟨i, hi, hwi⟩ := hwstrict
    have hCh : C = (ρ.outcome T).hired j := by
      by_contra hneq
      let r' : W → ℝ := fun a => if a ∈ C then r a else M.σ a j
      have hgrid : r' ∈ M.gridVectors δ j := by
        intro a
        dsimp [r']
        split_ifs with ha
        · exact hrg a ha
        · exact ⟨0, by simp⟩
      have hpeq : profit (M.y j) C r' = profit (M.y j) C r := by
        unfold profit
        congr 1
        apply Finset.sum_congr rfl
        intro a ha; simp [r', ha]
      exact (hNTF _ hc j C ⟨i, hi⟩ hneq r' hgrid) (heq.trans hpeq.symm)
    have hij : ρ.choice T i = j := by
      have hi' : i ∈ (ρ.outcome T).hired j := hCh ▸ hi
      change i ∈ Finset.univ.filter (fun a => ρ.choice T a = j) at hi'
      exact (Finset.mem_filter.mp hi').2
    have hri : (ρ.outcome T).sal i < r i := by
      apply (hu i j).1.lt_iff_lt.mp
      simpa [Run.outcome, hij] using hwi
    have hsumlt : (∑ a ∈ C, (ρ.outcome T).sal a) < ∑ a ∈ C, r a := by
      apply Finset.sum_lt_sum
      · intro a ha
        have haj : ρ.choice T a = j := by
          have ha' : a ∈ (ρ.outcome T).hired j := hCh ▸ ha
          change a ∈ Finset.univ.filter (fun b => ρ.choice T b = j) at ha'
          exact (Finset.mem_filter.mp ha').2
        simpa [Run.outcome, haj] using hle a ha
      · exact ⟨i, hi, hri⟩
    rw [← hCh] at heq
    unfold profit at heq
    linarith
  · exact (not_lt_of_ge hupper) hpstrict

#print axioms solution
