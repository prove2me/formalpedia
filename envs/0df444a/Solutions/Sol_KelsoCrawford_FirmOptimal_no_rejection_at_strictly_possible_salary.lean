-- Prove2me | solution 1 for KelsoCrawford.FirmOptimal.no_rejection_at_strictly_possible_salary
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:05:45.279649+00:00
-- url     : https://prove2.me/submissions/00e10fc9-9000-4b9c-8e2e-814ecfac4379

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

private theorem strict_core_core {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : KelsoCrawford.FirmOptimal.Market W F)
    {δ : ℝ} {A : KelsoCrawford.FirmOptimal.Allocation W F}
    (hA : M.IsStrictCore (M.grid δ) A) : M.IsCore (M.grid δ) A := by
  refine ⟨hA.1, hA.2.1, ?_⟩
  rintro ⟨j, C, r, hg, hw, hp⟩
  exact hA.2.2 ⟨j, C, r, hg, fun i hi => (hw i hi).le, hp.le, Or.inr hp⟩

private theorem run_demand {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : KelsoCrawford.FirmOptimal.Market W F)
    (δ : ℝ) (hMP : M.MP) (ρ : Run W F) (hr : M.IsRun δ ρ) (t : ℕ) (j : F) :
    IsDemanded (M.y j) (fun i => ρ.sal t i j) (ρ.offers t j) := by
  cases t with
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

private theorem large_salary {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : KelsoCrawford.FirmOptimal.Market W F)
    (δ : ℝ) (hδ : 0 < δ) (i : W) (j : F) (s : ℝ) :
    ∃ r ∈ M.grid δ i j, s ≤ r ∧ ∀ C : Finset W, M.y j (insert i C) - M.y j C < r := by
  classical
  obtain ⟨B, hB⟩ := (Set.finite_range (fun C : Finset W => M.y j (insert i C) - M.y j C)).bddAbove
  obtain ⟨n, hn⟩ := exists_nat_gt ((max s B - M.σ i j) / δ)
  have hb : max s B < M.σ i j + (n : ℝ) * δ := by
    have := (div_lt_iff₀ hδ).mp hn
    linarith
  refine ⟨M.σ i j + n * δ, ⟨n, rfl⟩, le_trans (le_max_left _ _) hb.le, ?_⟩
  intro C
  exact lt_of_le_of_lt (hB (Set.mem_range_self C)) (lt_of_le_of_lt (le_max_right _ _) hb)

private theorem blocking_from_offer {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : KelsoCrawford.FirmOptimal.Market W F)
    (δ : ℝ) (hδ : 0 < δ)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (A : KelsoCrawford.FirmOptimal.Allocation W F) (hA : M.IsStrictCore (M.grid δ) A)
    (j : F) (s : W → ℝ) (hs : s ∈ M.gridVectors δ j)
    (hb : ∀ a, A.assign a = j → s a ≤ A.sal a)
    (C : Finset W) (hC : IsDemanded (M.y j) s C)
    (i : W) (hi : i ∈ C) (hij : A.assign i ≠ j)
    (hbetter : M.u i (A.assign i) (A.sal i) < M.u i j (s i)) : False := by
  classical
  have hchoose : ∀ a : W, ∃ r : ℝ, r ∈ M.grid δ a j ∧ s a ≤ r ∧
      (A.assign a = j → r = A.sal a) ∧ (a = i → r = s a) ∧
      (M.u a (A.assign a) (A.sal a) ≤ M.u a j r ∨
        ∀ D : Finset W, M.y j (insert a D) - M.y j D < r) := by
    intro a
    by_cases hai : a = i
    · subst a
      refine ⟨s i, hs i, le_rfl, ?_, (by intro _; rfl), Or.inl hbetter.le⟩
      intro hh; exact (hij hh).elim
    by_cases haj : A.assign a = j
    · refine ⟨A.sal a, ?_, hb a haj, (by intro _; rfl), ?_, ?_⟩
      · simpa [haj] using hA.2.1 a
      · intro he; exact (hai he).elim
      · exact Or.inl (by simp [haj])
    by_cases hex : ∃ r ∈ M.grid δ a j, s a ≤ r ∧ M.u a (A.assign a) (A.sal a) ≤ M.u a j r
    · obtain ⟨r, hrg, hsr, hur⟩ := hex
      exact ⟨r, hrg, hsr, (by intro hh; exact (haj hh).elim),
        (by intro hh; exact (hai hh).elim), Or.inl hur⟩
    · obtain ⟨r, hrg, hsr, hlarge⟩ := large_salary M δ hδ a j (s a)
      exact ⟨r, hrg, hsr, (by intro hh; exact (haj hh).elim),
        (by intro hh; exact (hai hh).elim), Or.inr hlarge⟩
  choose r hr using hchoose
  have hrg : r ∈ M.gridVectors δ j := fun a => (hr a).1
  have hsr : s ≤ r := fun a => (hr a).2.1
  have hri : r i = s i := (hr i).2.2.2.1 rfl
  obtain ⟨D, hD, hkeep⟩ := hGS j s hs r hrg hsr C hC
  have hiD : i ∈ D := hkeep (Finset.mem_filter.mpr ⟨hi, hri⟩)
  have hutils : ∀ a ∈ D, M.u a (A.assign a) (A.sal a) ≤ M.u a j (r a) := by
    intro a ha
    rcases (hr a).2.2.2.2 with hu | hlarge
    · exact hu
    · have hdem := hD (D.erase a)
      have hins : insert a (D.erase a) = D := Finset.insert_erase ha
      have hsum : ∑ b ∈ D, r b = r a + ∑ b ∈ D.erase a, r b := by
        rw [← hins, Finset.sum_insert (by simp)]
        simp
      have hh := hlarge (D.erase a)
      rw [hins] at hh
      unfold profit at hdem
      rw [hsum] at hdem
      linarith
  have hprofit : profit (M.y j) (A.hired j) A.sal = profit (M.y j) (A.hired j) r := by
    unfold profit
    congr 1
    apply Finset.sum_congr rfl
    intro a ha
    have haj : A.assign a = j := (Finset.mem_filter.mp ha).2
    exact ((hr a).2.2.1 haj).symm
  apply hA.2.2
  refine ⟨j, D, r, fun a ha => hrg a, hutils, ?_, ?_⟩
  · rw [hprofit]; exact hD (A.hired j)
  · exact Or.inl ⟨i, hiD, by simpa [hri] using hbetter⟩

private theorem salary_bound {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hδ : 0 < δ)
    (hu : M.UtilityRegular) (hMP : M.MP)
    (hGS : ∀ j, GrossSubstitutesOn (M.y j) (M.gridVectors δ j)) (hNTW : M.NTW δ)
    (ρ : Run W F) (hr : M.IsRun δ ρ) :
    ∀ t (A : KelsoCrawford.FirmOptimal.Allocation W F), M.IsStrictCore (M.grid δ) A →
      ∀ i, ρ.sal t i (A.assign i) ≤ A.sal i := by
  intro t
  induction t with
  | zero =>
    intro A hA i
    rw [hr.1.1]
    exact hA.1.1 i
  | succ t ih =>
    intro A hA i
    rw [hr.2.2.2]
    split_ifs with hrej
    · have hle := ih A hA i
      by_cases heq : ρ.sal t i (A.assign i) = A.sal i
      · have hchoice := (hr.2.2.1 t i ⟨_, hrej.1⟩).2 (A.assign i) hrej.1
        have hk : ρ.choice t i ≠ A.assign i := hrej.2
        have hne := hNTW A (strict_core_core M hA) i (ρ.choice t i) hk
          (ρ.sal t i (ρ.choice t i)) ((run_facts M δ hu ρ hr t).2.1 i _)
        rw [heq] at hchoice
        have hbetter := lt_of_le_of_ne hchoice hne
        exact (blocking_from_offer M δ hδ hGS A hA (ρ.choice t i)
          (fun a => ρ.sal t a (ρ.choice t i)) ((run_facts M δ hu ρ hr t).2.1 · _)
          (fun a ha => by simpa [ha] using ih A hA a)
          (ρ.offers t (ρ.choice t i)) (run_demand M δ hMP ρ hr t _)
          i ((run_facts M δ hu ρ hr t).1 i) (Ne.symm hk) hbetter).elim
      · exact grid_gap M hδ ((run_facts M δ hu ρ hr t).2.1 i _) (hA.2.1 i)
          (lt_of_le_of_ne hle heq)
    · exact ih A hA i

theorem solution
    {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F] [Nonempty F]
    (M : KelsoCrawford.FirmOptimal.Market W F) (δ : ℝ) (hδ : 0 < δ) (hu : M.UtilityRegular) (hMP : M.MP) (hNFL : M.NFL)
    (hGS : ∀ j, KelsoCrawford.Process.GrossSubstitutesOn (M.y j) (M.gridVectors δ j))
    (hNTW : M.NTW δ) (hNTF : M.NTF δ) :
    ∀ ρ : Run W F, M.IsRun δ ρ → ∀ t i j, ρ.Rejects t i j →
      ¬ M.StrictlyPossible δ i j (ρ.sal t i j) := by
  intro ρ hr t i j hrej hpossible
  obtain ⟨A, hA, hij, hsal⟩ := hpossible
  have hchoice := (hr.2.2.1 t i ⟨_, hrej.1⟩).2 j hrej.1
  have hk : ρ.choice t i ≠ A.assign i := by simpa [hij] using hrej.2
  have hne := hNTW A (strict_core_core M hA) i (ρ.choice t i) hk
    (ρ.sal t i (ρ.choice t i)) ((run_facts M δ hu ρ hr t).2.1 i _)
  have hbetter : M.u i (A.assign i) (A.sal i) < M.u i (ρ.choice t i) (ρ.sal t i (ρ.choice t i)) := by
    rw [hij, hsal]
    exact lt_of_le_of_ne hchoice (by simpa [hij, hsal] using hne)
  exact blocking_from_offer M δ hδ hGS A hA (ρ.choice t i)
    (fun a => ρ.sal t a (ρ.choice t i)) ((run_facts M δ hu ρ hr t).2.1 · _)
    (fun a ha => by simpa [ha] using salary_bound M δ hδ hu hMP hGS hNTW ρ hr t A hA a)
    (ρ.offers t (ρ.choice t i)) (run_demand M δ hMP ρ hr t _)
    i ((run_facts M δ hu ρ hr t).1 i) (Ne.symm hk) hbetter

#print axioms solution
