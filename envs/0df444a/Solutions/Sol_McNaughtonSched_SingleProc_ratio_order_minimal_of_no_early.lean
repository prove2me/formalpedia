-- Prove2me | solution 1 for McNaughtonSched.SingleProc.ratio_order_minimal_of_no_early
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T21:13:04.819275+00:00
-- url     : https://prove2.me/submissions/bd812891-09e0-4e6c-9225-34717ea75073

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model



namespace McNaughtonSched.SingleProc

theorem completion_nonneg' {m : ℕ} (S : Schedule m) (i : Fin m) : 0 ≤ completion S i := by
  unfold completion
  induction ((S.filter fun g => g.task = i).map Piece.stop) with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

theorem loss_diff_core2 {m : ℕ} (a p d : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i)
    (S' : Schedule m) :
    totalLoss p 0 S' - totalLoss p 0 (seqSchedule a σ) ≤
      totalLoss p d S' - totalLoss p d (seqSchedule a σ) := by
  unfold totalLoss
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  unfold taskLoss
  have h1 := completion_nonneg' S' i
  have h2 := completion_nonneg' (seqSchedule a σ) i
  have h3 := hlate i
  simp only [Pi.zero_apply, sub_zero]
  rw [max_eq_right h1, max_eq_right h2, max_eq_right (show 0 ≤ completion (seqSchedule a σ) i - d i by linarith)]
  have := hp i
  have h4 : completion S' i - d i ≤ max 0 (completion S' i - d i) := le_max_right _ _
  nlinarith [mul_le_mul_of_nonneg_left h4 (hp i)]


theorem foldr_max_nonneg (l : List ℝ) : 0 ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.foldr_cons]; exact le_trans ih (le_max_right _ _)

theorem le_foldr_max (l : List ℝ) (x : ℝ) (hx : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem foldr_max_le (l : List ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ x ∈ l, x ≤ B) :
    l.foldr max 0 ≤ B := by
  induction l with
  | nil => simpa using hB
  | cons y l ih =>
    simp only [List.foldr_cons]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem stop_le_completion {m : ℕ} (S : Schedule m) (g : Piece m) (hg : g ∈ S) :
    g.stop ≤ completion S g.task := by
  unfold completion
  apply le_foldr_max
  exact List.mem_map.2 ⟨g, List.mem_filter.2 ⟨hg, by simp⟩, rfl⟩

theorem sum_filter_map_eq {α β : Type*} [AddCommMonoid β] (l : List α) (P : α → Bool)
    (f : α → β) :
    ((l.filter P).map f).sum = (l.map fun x => if P x then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases h : P x
    · simp [h, ih]
    · simp [h, ih]

theorem sum_split {α : Type*} (l : List α) (P : α → Bool) (f : α → ℝ) :
    (l.map f).sum = ((l.filter P).map f).sum + ((l.filter fun x => !P x).map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    by_cases h : P x
    · simp [h, ih]; ring
    · simp [h, ih]; ring

/-- total length of disjoint intervals in [lo, hi] -/
theorem sum_len_le {m : ℕ} : ∀ (n : ℕ) (L : List (Piece m)) (lo hi : ℝ), L.length = n →
    (∀ g ∈ L, lo ≤ g.start ∧ g.start ≤ g.stop ∧ g.stop ≤ hi) →
    L.Pairwise Piece.Disjoint → lo ≤ hi →
    (L.map fun g => g.stop - g.start).sum ≤ hi - lo := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L lo hi hn hin hd hlh
  match L, hin, hd, hn with
  | [], _, _, _ => simpa using hlh
  | g :: L', hin, hd, hn =>
    have hg := hin g (by simp)
    have hd' := (List.pairwise_cons.1 hd)
    let P : Piece m → Bool := fun h => decide (h.stop ≤ g.start)
    rw [List.map_cons, List.sum_cons, sum_split L' P]
    have hlen1 : (L'.filter P).length < n := by
      have := List.length_filter_le P L'; simp at hn; omega
    have hlen2 : (L'.filter fun x => !P x).length < n := by
      have := List.length_filter_le (fun x => !P x) L'; simp at hn; omega
    have h1 := ih _ hlen1 (L'.filter P) lo g.start rfl (by
      intro h hh
      rw [List.mem_filter] at hh
      have h3 := hin h (by simp [hh.1])
      have h4 : h.stop ≤ g.start := by simpa [P] using hh.2
      exact ⟨h3.1, h3.2.1, h4⟩) (hd'.2.filter _) hg.1
    have h2 := ih _ hlen2 (L'.filter fun x => !P x) g.stop hi rfl (by
      intro h hh
      rw [List.mem_filter] at hh
      have hh3 := hin h (by simp [hh.1])
      have hns : ¬ h.stop ≤ g.start := by simpa [P] using hh.2
      have := hd'.1 h hh.1
      rcases this with h5 | h5
      · exact ⟨h5, hh3.2.1, hh3.2.2⟩
      · exact absurd (by linarith [hh3.2.1, hg.2.1]) hns) (hd'.2.filter _) hg.2.2
    linarith


theorem sum_processed {m : ℕ} (S : Schedule m) (T : Finset (Fin m)) :
    ∑ i ∈ T, processed S i =
      ((S.filter fun g => decide (g.task ∈ T)).map fun g => g.stop - g.start).sum := by
  unfold processed
  simp_rw [sum_filter_map_eq]
  induction S with
  | nil => simp
  | cons g S ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
    congr 1
    simp only [decide_eq_true_eq]
    rw [Finset.sum_ite_eq]

theorem key_sum_le {m : ℕ} (a : Fin m → ℝ) (S : Schedule m) (hS : IsFeasible a S) (C : ℝ)
    (hC : 0 ≤ C) :
    ∑ i ∈ Finset.univ.filter (fun i => completion S i ≤ C), a i ≤ C := by
  obtain ⟨h1, h2, h3⟩ := hS
  have : ∑ i ∈ Finset.univ.filter (fun i => completion S i ≤ C), a i =
      ∑ i ∈ Finset.univ.filter (fun i => completion S i ≤ C), processed S i := by
    simp [h3]
  rw [this, sum_processed]
  have := sum_len_le _ (S.filter fun g => decide (g.task ∈ Finset.univ.filter
      (fun i => completion S i ≤ C))) 0 C rfl (by
    intro g hg
    rw [List.mem_filter] at hg
    have hc : completion S g.task ≤ C := by simpa using hg.2
    exact ⟨(h1 g hg.1).1, (h1 g hg.1).2, le_trans (stop_le_completion S g hg.1) hc⟩)
    (h2.filter _) hC
  simpa using this


theorem stop_sub_start {m : ℕ} (a : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin m => l ≤ k), a (σ l) -
      ∑ l ∈ Finset.univ.filter (fun l : Fin m => l < k), a (σ l) = a (σ k) := by
  have : Finset.univ.filter (fun l : Fin m => l ≤ k) =
      insert k (Finset.univ.filter (fun l : Fin m => l < k)) := by
    ext l; simp [le_iff_lt_or_eq, or_comm]
  rw [this, Finset.sum_insert (by simp)]
  ring

theorem seq_feasible {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (σ : Equiv.Perm (Fin m)) :
    IsFeasible a (seqSchedule a σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    unfold seqSchedule at hg
    rw [List.mem_ofFn] at hg
    obtain ⟨k, rfl⟩ := hg
    dsimp only
    refine ⟨Finset.sum_nonneg fun l _ => ha _, ?_⟩
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro l; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact le_of_lt
    · intro l _ _; exact ha _
  · unfold seqSchedule
    rw [List.pairwise_ofFn]
    intro k l hkl
    left
    dsimp only
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hx; exact lt_of_le_of_lt hx hkl
    · intro l _ _; exact ha _
  · intro i
    unfold processed seqSchedule
    rw [sum_filter_map_eq, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, decide_eq_true_eq, stop_sub_start]
    rw [Equiv.sum_comp σ (fun j => if j = i then a j else 0)]
    simp

theorem seq_completion {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (σ : Equiv.Perm (Fin m))
    (k : Fin m) :
    completion (seqSchedule a σ) (σ k) =
      ∑ l ∈ Finset.univ.filter (fun l : Fin m => l ≤ k), a (σ l) := by
  apply le_antisymm
  · unfold completion
    apply foldr_max_le _ _ (Finset.sum_nonneg fun l _ => ha _)
    intro x hx
    simp only [List.mem_map, List.mem_filter, seqSchedule, List.mem_ofFn, Set.mem_range,
      decide_eq_true_eq] at hx
    obtain ⟨g, ⟨⟨k', rfl⟩, hk'⟩, rfl⟩ := hx
    simp only at hk'
    have := σ.injective hk'
    subst this
    exact le_rfl
  · have := stop_le_completion (seqSchedule a σ)
      ⟨σ k, ∑ l ∈ Finset.univ.filter (fun l : Fin m => l < k), a (σ l),
        ∑ l ∈ Finset.univ.filter (fun l : Fin m => l ≤ k), a (σ l)⟩
      (by unfold seqSchedule; rw [List.mem_ofFn]; exact ⟨k, rfl⟩)
    simpa using this

theorem seq_noSplit {m : ℕ} (a : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    NoSplit (seqSchedule a σ) := by
  intro i
  have h : ∀ l : List (Piece m), l.length = (l.map fun _ => (1 : ℕ)).sum := by
    intro l; induction l with
    | nil => simp
    | cons x l ih => rw [List.length_cons, List.map_cons, List.sum_cons, ih]; ring
  rw [h, sum_filter_map_eq]
  unfold seqSchedule
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, decide_eq_true_eq]
  rw [Equiv.sum_comp σ (fun j => if j = i then 1 else 0)]
  simp

theorem seq_length {m : ℕ} (a : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    (seqSchedule a σ).length = m := by
  simp [seqSchedule]


theorem exists_seq_le {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (S : Schedule m)
    (hS : IsFeasible a S) :
    ∃ τ : Equiv.Perm (Fin m), ∀ i, completion (seqSchedule a τ) i ≤ completion S i := by
  set c := completion S with hc
  refine ⟨Tuple.sort c, fun i => ?_⟩
  have hmono := Tuple.monotone_sort c
  obtain ⟨k, rfl⟩ := (Tuple.sort c).surjective i
  rw [seq_completion a ha]
  refine le_trans ?_ (key_sum_le a S hS (c (Tuple.sort c k)) (completion_nonneg' S _))
  rw [show (∑ l ∈ Finset.univ.filter (fun l : Fin m => l ≤ k), a (Tuple.sort c l)) =
      ∑ j ∈ (Finset.univ.filter (fun l : Fin m => l ≤ k)).map (Tuple.sort c).toEmbedding, a j
      by rw [Finset.sum_map]; rfl]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding] at hj ⊢
    obtain ⟨l, hl, rfl⟩ := hj
    rw [← hc]
    exact hmono hl
  · intro j _ _; exact ha j

theorem taskLoss_mono {m : ℕ} (p d : Fin m → ℝ) (hp : ∀ i, 0 ≤ p i) (i : Fin m) {s t : ℝ}
    (h : s ≤ t) : taskLoss p d i s ≤ taskLoss p d i t := by
  unfold taskLoss
  exact mul_le_mul_of_nonneg_left (max_le_max le_rfl (sub_le_sub_right h _)) (hp i)

theorem exists_seq_loss_le {m : ℕ} (a p d : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hp : ∀ i, 0 ≤ p i) (S : Schedule m) (hS : IsFeasible a S) :
    ∃ τ : Equiv.Perm (Fin m), totalLoss p d (seqSchedule a τ) ≤ totalLoss p d S := by
  obtain ⟨τ, hτ⟩ := exists_seq_le a ha S hS
  exact ⟨τ, Finset.sum_le_sum fun i _ => taskLoss_mono p d hp i (hτ i)⟩

theorem split_reduction_core {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (S : Schedule m) (hS : IsFeasible a S) (hsplit : m < S.length) :
    ∃ S' : Schedule m, IsFeasible a S' ∧ S'.length < S.length ∧
      totalLoss p d S' ≤ totalLoss p d S := by
  have ha' : ∀ i, 0 ≤ a i := fun i => (ha i).le
  obtain ⟨τ, hτ⟩ := exists_seq_loss_le a p d ha' hp S hS
  exact ⟨_, seq_feasible a ha' τ, by rw [seq_length]; exact hsplit, hτ⟩

theorem exists_optimal_noSplit_core {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i) :
    ∃ S₀ : Schedule m, IsFeasible a S₀ ∧ NoSplit S₀ ∧
      ∀ S : Schedule m, IsFeasible a S → totalLoss p d S₀ ≤ totalLoss p d S := by
  have ha' : ∀ i, 0 ≤ a i := fun i => (ha i).le
  obtain ⟨σ, -, hσ⟩ := Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin m)))
    (fun τ => totalLoss p d (seqSchedule a τ)) Finset.univ_nonempty
  refine ⟨_, seq_feasible a ha' σ, seq_noSplit a σ, fun S hS => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_seq_loss_le a p d ha' hp S hS
  exact le_trans (hσ τ (Finset.mem_univ _)) hτ

/-- completion of seq as a sum over tasks -/
theorem seq_completion' {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (σ : Equiv.Perm (Fin m))
    (i : Fin m) :
    completion (seqSchedule a σ) i =
      ∑ j, if σ.symm j ≤ σ.symm i then a j else 0 := by
  obtain ⟨k, rfl⟩ := σ.surjective i
  rw [seq_completion a ha, Finset.sum_filter,
    ← Equiv.sum_comp σ (fun j => if σ.symm j ≤ σ.symm (σ k) then a j else 0)]
  simp

theorem smith {m : ℕ} (a p : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (σ τ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ) :
    ∑ i, ∑ j, (if σ.symm j ≤ σ.symm i then p i * a j else 0) ≤
      ∑ i, ∑ j, (if τ.symm j ≤ τ.symm i then p i * a j else 0) := by
  have key : ∀ ρ : Equiv.Perm (Fin m), 2 * ∑ i, ∑ j, (if ρ.symm j ≤ ρ.symm i then p i * a j else 0)
      = ∑ i, ∑ j, ((if ρ.symm j ≤ ρ.symm i then p i * a j else 0) +
          (if ρ.symm i ≤ ρ.symm j then p j * a i else 0)) := by
    intro ρ
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if ρ.symm i ≤ ρ.symm j then p j * a i else 0)]
    ring
  suffices h : 2 * ∑ i, ∑ j, (if σ.symm j ≤ σ.symm i then p i * a j else 0) ≤
      2 * ∑ i, ∑ j, (if τ.symm j ≤ τ.symm i then p i * a j else 0) by linarith
  rw [key σ, key τ]
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  by_cases hij : i = j
  · subst hij; simp
  have hs : σ.symm i ≠ σ.symm j := fun h => hij (σ.symm.injective h)
  have ht : τ.symm i ≠ τ.symm j := fun h => hij (τ.symm.injective h)
  have hai := ha i
  have haj := ha j
  -- τ value is ≥ min
  have hτv : min (p i * a j) (p j * a i) ≤
      (if τ.symm j ≤ τ.symm i then p i * a j else 0) +
        (if τ.symm i ≤ τ.symm j then p j * a i else 0) := by
    rcases lt_or_gt_of_ne ht with h | h
    · rw [if_neg (not_le.2 h), if_pos h.le]; simp
    · rw [if_pos h.le, if_neg (not_le.2 h)]; simp
  refine le_trans ?_ hτv
  rcases lt_or_gt_of_ne hs with h | h
  · -- σ.symm i < σ.symm j : i earlier, ratio i ≥ ratio j
    have hr := hσ (σ.symm i) (σ.symm j) h.le
    simp only [Equiv.apply_symm_apply] at hr
    rw [div_le_div_iff₀ haj hai] at hr
    rw [if_neg (not_le.2 h), if_pos h.le]
    simp only [zero_add, le_min_iff]
    constructor
    · linarith
    · exact le_rfl
  · have hr := hσ (σ.symm j) (σ.symm i) h.le
    simp only [Equiv.apply_symm_apply] at hr
    rw [div_le_div_iff₀ hai haj] at hr
    rw [if_pos h.le, if_neg (not_le.2 h)]
    simp only [add_zero, le_min_iff]
    constructor
    · exact le_rfl
    · linarith

theorem zero_deadlines_core {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i) (hd : ∀ i, d i = 0)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by
  have ha' : ∀ i, 0 ≤ a i := fun i => (ha i).le
  refine ⟨seq_feasible a ha' σ, fun S hS => ?_⟩
  obtain ⟨τ, hτ⟩ := exists_seq_loss_le a p d ha' hp S hS
  refine le_trans ?_ hτ
  have e : ∀ ρ : Equiv.Perm (Fin m), totalLoss p d (seqSchedule a ρ) =
      ∑ i, ∑ j, (if ρ.symm j ≤ ρ.symm i then p i * a j else 0) := by
    intro ρ
    unfold totalLoss taskLoss
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i, sub_zero, max_eq_right (completion_nonneg' _ _), seq_completion' a ha',
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [e, e]
  exact smith a p ha σ τ hσ

theorem goal_core {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ)
    (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by
  obtain ⟨h1, h2⟩ := zero_deadlines_core a p 0 ha hp (fun _ => rfl) σ hσ
  refine ⟨h1, fun S hS => ?_⟩
  have h3 := h2 S hS
  have h4 := loss_diff_core2 a p d hp σ hlate S
  linarith

end McNaughtonSched.SingleProc

open McNaughtonSched.SingleProc


theorem solution {m : ℕ} (a p d : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hp : ∀ i, 0 ≤ p i)
    (σ : Equiv.Perm (Fin m)) (hσ : InRatioOrder a p σ)
    (hlate : ∀ i, d i ≤ completion (seqSchedule a σ) i) :
    IsFeasible a (seqSchedule a σ) ∧
      ∀ S : Schedule m, IsFeasible a S →
        totalLoss p d (seqSchedule a σ) ≤ totalLoss p d S := by
  exact goal_core a p d ha hp σ hσ hlate
