-- Prove2me | solution 1 for MetricalTaskSystem.Deterministic.ctsa_to_dtsa
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:04:20.015321+00:00
-- url     : https://prove2.me/submissions/6fc23b1f-46ae-4e48-ae6a-19c57ba7f02d

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime



namespace MetricalTaskSystem.Deterministic

theorem pathCost_cons_cons {S : Type} (d : S → S → ℝ) (a b : S) (l : List S) :
    pathCost d (a :: b :: l) = d a b + pathCost d (b :: l) := by
  simp [pathCost]

theorem pathCost_single {S : Type} (d : S → S → ℝ) (a : S) :
    pathCost d [a] = 0 := by
  simp [pathCost]

theorem pathCost_nonneg' {S : Type} (d : S → S → ℝ) (hd : IsTaskSystem d) (l : List S) :
    0 ≤ pathCost d l := by
  have hnn : ∀ i j, 0 ≤ d i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hd.diag]
    · exact (hd.pos i j h).le
  unfold pathCost
  apply List.sum_nonneg
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  simp only [List.getElem_zipWith]
  exact hnn _ _

theorem pathCost_sublist {S : Type} (d : S → S → ℝ) (hd : IsTaskSystem d)
    {l l' : List S} (h : l.Sublist l') : ∀ a, pathCost d (a :: l) ≤ pathCost d (a :: l') := by
  have hnn : ∀ i j, 0 ≤ d i j := by
    intro i j
    by_cases h : i = j
    · subst h; rw [hd.diag]
    · exact (hd.pos i j h).le
  induction h with
  | slnil => intro a; exact le_rfl
  | @cons l₁ l₂ x h ih =>
    intro a
    rw [pathCost_cons_cons]
    have h1 := ih x
    have h2 : pathCost d (a :: l₁) ≤ d a x + pathCost d (x :: l₁) := by
      cases l₁ with
      | nil => rw [pathCost_single, pathCost_single]; linarith [hnn a x]
      | cons y l₃ =>
        rw [pathCost_cons_cons, pathCost_cons_cons]
        linarith [hd.triangle a x y]
    linarith
  | @cons_cons l₁ l₂ x h ih =>
    intro a
    rw [pathCost_cons_cons, pathCost_cons_cons]
    linarith [ih x]

theorem pathCost_ofFn {S : Type} (d : S → S → ℝ) : ∀ (m : ℕ) (σ : Fin (m + 1) → S),
    pathCost d (List.ofFn σ) = ∑ i : Fin m, d (σ i.castSucc) (σ i.succ)
  | 0, σ => by simp [pathCost]
  | m + 1, σ => by
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    have := pathCost_ofFn d m (fun i : Fin (m+1) => σ i.succ)
    rw [List.ofFn_succ] at this
    rw [List.ofFn_succ, pathCost_cons_cons, this]
    rfl

theorem ofFn_sublist_flatten {α : Type} : ∀ (m : ℕ) (x : Fin m → α) (L : Fin m → List α),
    (∀ i, x i ∈ L i) → (List.ofFn x).Sublist (List.ofFn L).flatten
  | 0, x, L, _ => by simp
  | m + 1, x, L, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons]
    have h1 : [x 0].Sublist (L 0) := List.singleton_sublist.mpr (h 0)
    exact h1.append (ofFn_sublist_flatten m (fun i => x i.succ) (fun i => L i.succ)
      (fun i => h i.succ))

open Classical in
noncomputable def ctsaChoose {S : Type} (A' : CTSA S) (s₀ : S) (l : List (S → ℝ)) : S :=
  if h : ∃ p ∈ A' s₀ l, ∀ q ∈ A' s₀ l, l.getLastD 0 p.1 ≤ l.getLastD 0 q.1 then
    (Classical.choose h).1 else s₀

theorem ctsaChoose_spec {S : Type} (A' : CTSA S) (s₀ : S) (l : List (S → ℝ))
    (hne : A' s₀ l ≠ []) :
    (∃ p ∈ A' s₀ l, p.1 = ctsaChoose A' s₀ l) ∧
      ∀ q ∈ A' s₀ l, l.getLastD 0 (ctsaChoose A' s₀ l) ≤ l.getLastD 0 q.1 := by
  classical
  have hex : ∃ p ∈ A' s₀ l, ∀ q ∈ A' s₀ l, l.getLastD 0 p.1 ≤ l.getLastD 0 q.1 := by
    have hne' : (A' s₀ l).toFinset.Nonempty := by
      obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨a, by simpa using ha⟩
    obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun p : S × ℝ => l.getLastD 0 p.1) hne'
    exact ⟨p, by simpa using hp, fun q hq => hmin q (by simpa using hq)⟩
  unfold ctsaChoose
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := Classical.choose_spec hex
  exact ⟨⟨_, h1, rfl⟩, h2⟩

theorem getLastD_take_ofFn {α : Type} (m : ℕ) (T : Fin m → α) (i : Fin m) (z : α) :
    ((List.ofFn T).take ((i : ℕ) + 1)).getLastD z = T i := by
  rw [List.getLastD_eq_getLast?]
  rw [List.getLast?_take]
  simp

theorem ctsa_core {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A' : CTSA S) (hA' : IsCTSA A') :
    ∃ A : OnlineAlgorithm S, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      onlineCost d A s₀ T ≤ ctsaCost d A' s₀ T := by
  refine ⟨ctsaChoose A', ?_⟩
  intro s₀ m T _
  have hne : ∀ i : Fin m, (List.ofFn T).take ((i : ℕ) + 1) ≠ [] := by
    intro i; have := i.pos; simp; omega
  have hwf := fun i => hA' s₀ _ (hne i)
  have hpne : ∀ i : Fin m, ctsaPiecesAt A' s₀ T i ≠ [] := by
    intro i h
    have := (hwf i).2
    unfold ctsaPiecesAt at h
    rw [h] at this
    simp at this
  have hsched : ∀ i : Fin m, onlineSchedule (ctsaChoose A') s₀ T i.succ =
      ctsaChoose A' s₀ ((List.ofFn T).take ((i : ℕ) + 1)) := by
    intro i
    simp [onlineSchedule]
  unfold onlineCost schedCost ctsaCost
  rw [Finset.sum_add_distrib]
  apply add_le_add
  · rw [← pathCost_ofFn]
    rw [List.ofFn_succ]
    have h0 : onlineSchedule (ctsaChoose A') s₀ T 0 = s₀ := by simp [onlineSchedule]
    rw [h0]
    apply pathCost_sublist d hd
    rw [List.map_flatten, List.map_ofFn]
    apply ofFn_sublist_flatten
    intro i
    rw [hsched i]
    obtain ⟨⟨p, hp, hpe⟩, _⟩ := ctsaChoose_spec A' s₀ _ (hpne i)
    simp only [Function.comp_apply, List.mem_map]
    exact ⟨p, hp, hpe⟩
  · apply Finset.sum_le_sum
    intro i _
    rw [hsched i]
    obtain ⟨_, hmin⟩ := ctsaChoose_spec A' s₀ _ (hpne i)
    have hmin' : ∀ q ∈ ctsaPiecesAt A' s₀ T i,
        T i (ctsaChoose A' s₀ ((List.ofFn T).take ((i : ℕ) + 1))) ≤ T i q.1 := by
      intro q hq
      have := hmin q hq
      rwa [getLastD_take_ofFn] at this
    have hsum := (hwf i).2
    have hnn := (hwf i).1
    set c := T i (ctsaChoose A' s₀ ((List.ofFn T).take ((i : ℕ) + 1)))
    have : ((ctsaPiecesAt A' s₀ T i).map (fun p => p.2 * c)).sum = c := by
      rw [List.sum_map_mul_right]
      unfold ctsaPiecesAt
      rw [hsum, one_mul]
    rw [← this]
    apply List.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (hmin' p hp) (hnn p hp)

end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic


theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A' : CTSA S) (hA' : IsCTSA A') :
    ∃ A : OnlineAlgorithm S, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      onlineCost d A s₀ T ≤ ctsaCost d A' s₀ T := by
  exact ctsa_core d hd A' hA'
