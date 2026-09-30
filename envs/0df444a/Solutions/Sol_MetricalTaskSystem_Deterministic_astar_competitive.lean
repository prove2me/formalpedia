-- Prove2me | solution 1 for MetricalTaskSystem.Deterministic.astar_competitive
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:48:44.517069+00:00
-- url     : https://prove2.me/submissions/9893f0db-4c6b-44b1-a0ad-98e971c39e9d

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime
import Definitions.Def_MetricalTaskSystem_Deterministic_AstarD



namespace MetricalTaskSystem.Deterministic

theorem flo_pathCost_cons_cons {S : Type} (d : S → S → ℝ) (a b : S) (l : List S) :
    pathCost d (a :: b :: l) = d a b + pathCost d (b :: l) := by
  simp [pathCost]

theorem flo_pathCost_snoc {S : Type} (d : S → S → ℝ) (b : S) :
    ∀ (l : List S) (a : S), pathCost d (a :: (l ++ [b])) = pathCost d (a :: l) + d (l.getLastD a) b
  | [], a => by simp [pathCost]
  | c :: l, a => by
    rw [List.cons_append, flo_pathCost_cons_cons, flo_pathCost_cons_cons, flo_pathCost_snoc d b l c]
    rw [List.getLastD_cons]
    ring

theorem flo_pathCost_nonneg {S : Type} (d : S → S → ℝ) (hd : IsTaskSystem d) (l : List S) :
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

theorem flo_interval_add (a b c f e : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hfe : f ≤ e) :
    max 0 (min c e - max a f) = max 0 (min b e - max a f) + max 0 (min c e - max b f) := by
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem flo_proc_add {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (s : S) (a b c : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) : proc T s a c = proc T s a b + proc T s b c := by
  unfold proc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [flo_interval_add a b c ((i : ℝ) + 1) ((i : ℝ) + 2) hab hbc (by linarith)]
  ring

theorem flo_proc_nonneg {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (s : S) (a b : ℝ) : 0 ≤ proc T s a b := by
  unfold proc
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (hT i s) (le_max_left _ _)

theorem flo_proc_self {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (s : S) (a : ℝ) :
    proc T s a a = 0 := by
  have := flo_proc_add T s a a a le_rfl le_rfl
  linarith

theorem flo_proc_mono {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (s : S) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) : proc T s a b ≤ proc T s a c := by
  rw [flo_proc_add T s a b c hab hbc]
  linarith [flo_proc_nonneg T hT s b c]

theorem flo_piecesProc_nonneg {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x) :
    ∀ (P : List (S × ℝ)) (a : ℝ), 0 ≤ piecesProc T a P
  | [], a => by simp [piecesProc]
  | p :: P, a => by
    simp only [piecesProc]
    linarith [flo_proc_nonneg T hT p.1 a (a + p.2), flo_piecesProc_nonneg T hT P (a + p.2)]

theorem flo_piecesProc_snoc {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (q : S × ℝ) :
    ∀ (P : List (S × ℝ)) (a : ℝ), piecesProc T a (P ++ [q]) =
      piecesProc T a P + proc T q.1 (a + (P.map Prod.snd).sum) (a + (P.map Prod.snd).sum + q.2)
  | [], a => by simp [piecesProc]
  | p :: P, a => by
    simp only [List.cons_append, piecesProc]
    rw [flo_piecesProc_snoc T q P (a + p.2)]
    simp only [List.map_cons, List.sum_cons]
    rw [show a + p.2 + (P.map Prod.snd).sum = a + (p.2 + (P.map Prod.snd).sum) by ring]
    ring

/-- cost of an offline piece list -/
noncomputable def floCost {S : Type} (d : S → S → ℝ) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ)
    (P : List (S × ℝ)) : ℝ :=
  pathCost d (s₀ :: P.map Prod.fst) + piecesProc T 1 P

theorem flo_cost_nonneg {S : Type} (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x) (P : List (S × ℝ)) : 0 ≤ floCost d s₀ T P := by
  unfold floCost
  linarith [flo_pathCost_nonneg d hd (s₀ :: P.map Prod.fst), flo_piecesProc_nonneg T hT P 1]

theorem flo_cost_snoc {S : Type} (d : S → S → ℝ) (s₀ : S) {m : ℕ}
    (T : Fin m → S → ℝ) (Q : List (S × ℝ)) (z : S) (ℓ : ℝ) :
    floCost d s₀ T (Q ++ [(z, ℓ)]) = floCost d s₀ T Q + d ((Q.map Prod.fst).getLastD s₀) z +
      proc T z (1 + (Q.map Prod.snd).sum) (1 + (Q.map Prod.snd).sum + ℓ) := by
  unfold floCost
  rw [List.map_append, List.map_singleton, flo_pathCost_snoc, flo_piecesProc_snoc]
  ring

theorem flo_nextTime {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (s : S) (c t t' : ℝ)
    (h : nextTime T s c t = some t') : t ≤ t' ∧ c ≤ proc T s t t' := by
  classical
  unfold nextTime at h
  split_ifs at h with hex
  obtain ⟨u, htu, _, hcu⟩ := hex
  have heq := (Option.some.inj h).symm
  set U := {u : ℝ | t ≤ u ∧ c ≤ proc T s t u} with hU
  have hne : U.Nonempty := ⟨u, htu, hcu⟩
  have hbdd : BddBelow U := ⟨t, fun x hx => hx.1⟩
  have hcont : Continuous (fun u => proc T s t u) := by
    unfold proc
    fun_prop
  have hclosed : IsClosed U := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const continuous_id
    · exact isClosed_le continuous_const hcont
  have hmem := hclosed.csInf_mem hne hbdd
  rw [heq]
  exact hmem

theorem flo_entry_succ {S : Type} (s : ℕ → S) (c : ℕ → ℝ) {m : ℕ} (T : Fin m → S → ℝ) (k : ℕ)
    (t' : ℝ) (h : entryTime s c T (k + 1) = some t') :
    ∃ tk, entryTime s c T k = some tk ∧ nextTime T (s k) (c k) tk = some t' := by
  cases hk : entryTime s c T k with
  | none => simp [entryTime, hk] at h
  | some tk =>
    refine ⟨tk, rfl, ?_⟩
    simpa [entryTime, hk] using h

theorem flo_entry_ge_one {S : Type} (s : ℕ → S) (c : ℕ → ℝ) {m : ℕ} (T : Fin m → S → ℝ) :
    ∀ (k : ℕ) (tk : ℝ), entryTime s c T k = some tk → 1 ≤ tk
  | 0, tk, h => by simp [entryTime] at h; linarith
  | k + 1, t', h => by
    obtain ⟨tk, h1, h2⟩ := flo_entry_succ s c T k t' h
    have := flo_entry_ge_one s c T k tk h1
    have := (flo_nextTime T _ _ _ _ h2).1
    linarith

/-- Stage claim D. -/
theorem flo_stage {S : Type} [DecidableEq S] (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S)
    (s : ℕ → S) (hs : IsAstarSeq d s₀ s) {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (k : ℕ) (tk : ℝ) (htk1 : 1 ≤ tk)
    (C : ∀ t, tk ≤ t → ∀ x P, IsOfflinePieces s₀ t x P → fSeq d s k x ≤ floCost d s₀ T P) :
    ∀ P : List (S × ℝ), ∀ t, IsOfflinePieces s₀ t (s k) P → tk ≤ t →
      min (fSeq d s k (s k) + proc T (s k) tk t)
        (fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k)) ≤ floCost d s₀ T P := by
  intro P
  induction P using List.reverseRecOn with
  | nil =>
    intro t hP htk
    obtain ⟨_, hsum, hlast⟩ := hP
    simp at hsum hlast
    have ht : t = 1 := by linarith
    have htk' : tk = t := by linarith
    have h0 := C t htk (s k) [] ⟨by simp, by simp; linarith, by simp [hlast]⟩
    rw [htk', flo_proc_self]
    exact (min_le_left _ _).trans (by linarith)
  | append_singleton Q q ih =>
    intro t hP htk
    obtain ⟨z, ℓ⟩ := q
    obtain ⟨hnn, hsum, hlast⟩ := hP
    simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      List.getLastD_concat] at hsum hlast
    have hℓ : 0 ≤ ℓ := hnn (z, ℓ) (by simp)
    have hQnn : ∀ p ∈ Q, 0 ≤ p.2 := fun p hp => hnn p (by simp [hp])
    subst hlast
    rw [flo_cost_snoc]
    set a := 1 + (Q.map Prod.snd).sum with ha
    have hta : a + ℓ = t := by rw [ha]; linarith
    rw [hta]
    set y' := (Q.map Prod.fst).getLastD s₀ with hy'
    have hQ : IsOfflinePieces s₀ a y' Q := ⟨hQnn, by rw [ha]; ring, rfl⟩
    have hdnn : 0 ≤ d y' (s k) := by
      by_cases h : y' = s k
      · rw [h, hd.diag]
      · exact (hd.pos _ _ h).le
    rcases le_or_gt a tk with hatk | hatk
    · -- truncated schedule
      have hP' : IsOfflinePieces s₀ tk (s k) (Q ++ [(s k, tk - a)]) := by
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | hp
          · exact hQnn p hp
          · rw [hp]; simp; linarith
        · simp only [List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
          linarith
        · simp
      have h1 := C tk le_rfl (s k) _ hP'
      rw [flo_cost_snoc] at h1
      rw [← ha, show a + (tk - a) = tk by ring] at h1
      rw [flo_proc_add T (s k) a tk t hatk htk]
      exact (min_le_left _ _).trans (by linarith)
    · by_cases hy : y' = s k
      · have hQa := ih a (hy ▸ hQ) hatk.le
        rw [hy, hd.diag]
        rw [flo_proc_add T (s k) tk a t hatk.le (by linarith)] 
        have hp := flo_proc_nonneg T hT (s k) a t
        have := min_le_left (fSeq d s k (s k) + (proc T (s k) tk a + proc T (s k) a t))
          (fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k))
        have := min_le_right (fSeq d s k (s k) + (proc T (s k) tk a + proc T (s k) a t))
          (fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k))
        rcases min_choice (fSeq d s k (s k) + proc T (s k) tk a)
          (fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k)) with h | h <;> rw [h] at hQa <;> linarith
      · have h1 := C a hatk.le y' Q hQ
        have h2 := (hs.2 k).2 y' hy
        have hp := flo_proc_nonneg T hT (s k) a t
        exact (min_le_right _ _).trans (by linarith)

theorem flo_claim {S : Type} [DecidableEq S] (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S)
    (s : ℕ → S) (hs : IsAstarSeq d s₀ s) {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x) :
    ∀ (k : ℕ) (tk : ℝ), entryTime s (cSeq d s) T k = some tk →
      ∀ t, tk ≤ t → ∀ x P, IsOfflinePieces s₀ t x P → fSeq d s k x ≤ floCost d s₀ T P
  | 0, tk, _ => by
    intro t _ x P _
    simp only [fSeq]
    exact flo_cost_nonneg d hd s₀ T hT P
  | k + 1, t', h => by
    obtain ⟨tk, h1, h2⟩ := flo_entry_succ s _ T k t' h
    obtain ⟨htt', hc⟩ := flo_nextTime T _ _ _ _ h2
    have C := flo_claim d hd s₀ s hs T hT k tk h1
    have htk1 := flo_entry_ge_one s _ T k tk h1
    intro t ht x P hP
    by_cases hx : x = s k
    · subst hx
      have D := flo_stage d hd s₀ s hs T hT k tk htk1 C P t hP (by linarith)
      have hmono := flo_proc_mono T hT (s k) tk t' t htt' ht
      have hcS : cSeq d s k = fSeq d s (k + 1) (s k) - fSeq d s k (s k) := rfl
      have hf : fSeq d s (k + 1) (s k) = fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) := by
        simp [fSeq]
      rcases min_choice (fSeq d s k (s k) + proc T (s k) tk t)
        (fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k)) with hm | hm <;> rw [hm] at D <;>
        linarith
    · have hf : fSeq d s (k + 1) x = fSeq d s k x := by simp [fSeq, hx]
      rw [hf]
      exact C t (by linarith) x P hP


theorem ac_dnn {S : Type} (d : S → S → ℝ) (hd : IsTaskSystem d) (a b : S) : 0 ≤ d a b := by
  by_cases h : a = b
  · subst h; rw [hd.diag]
  · exact le_of_lt (hd.pos a b h)

theorem ac_fsub {S : Type} [DecidableEq S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) : ∀ x y : S, fSeq d s k x - fSeq d s k y ≤ d y x := by
  induction k with
  | zero =>
    intro x y
    simp only [fSeq, sub_self]
    exact ac_dnn d hd y x
  | succ k ih =>
    intro x y
    obtain ⟨hne, hmin⟩ := hs.2 k
    have ex : ∀ z, fSeq d s (k + 1) z =
        if z = s k then fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) else fSeq d s k z :=
      fun z => rfl
    rw [ex x, ex y]
    by_cases hx : x = s k <;> by_cases hy : y = s k
    · rw [if_pos hx, if_pos hy, sub_self, hx, hy, hd.diag]
    · rw [if_pos hx, if_neg hy, hx]
      have := hmin y hy
      linarith
    · rw [if_neg hx, if_pos hy, hy]
      have h1 := ih x (s (k + 1))
      have h2 := hd.triangle (s (k + 1)) (s k) x
      linarith
    · rw [if_neg hx, if_neg hy]
      exact ih x y

theorem ac_sum_step {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) (s : ℕ → S) (k : ℕ) :
    (∑ x, fSeq d s (k + 1) x) =
      (∑ x, fSeq d s k x) + (fSeq d s (k + 1) (s k) - fSeq d s k (s k)) := by
  have h1 := Finset.add_sum_erase Finset.univ (fSeq d s (k + 1)) (Finset.mem_univ (s k))
  have h2 := Finset.add_sum_erase Finset.univ (fSeq d s k) (Finset.mem_univ (s k))
  have h3 : ∑ x ∈ Finset.univ.erase (s k), fSeq d s (k + 1) x =
      ∑ x ∈ Finset.univ.erase (s k), fSeq d s k x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_erase] at hx
    simp [fSeq, hx.1]
  linarith

theorem ac_potential {S : Type} [Fintype S] [DecidableEq S]
    (d : S → S → ℝ) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (k : ℕ) :
    2 * ∑ x ∈ Finset.univ.erase (s k), fSeq d s k x + fSeq d s k (s k) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by
  have hf : ∀ k, fSeq d s (k + 1) (s (k + 1)) = fSeq d s k (s (k + 1)) := fun k => by
    simp [fSeq, (hs.2 k).1]
  have hfk : ∀ k, fSeq d s (k + 1) (s k) = fSeq d s k (s (k + 1)) + d (s (k + 1)) (s k) :=
    fun k => by simp [fSeq]
  have main : ∀ k, 2 * (∑ x, fSeq d s k x) - fSeq d s k (s k) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by
    intro k
    induction k with
    | zero => simp [fSeq]
    | succ k ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ac_sum_step, hf]
      have hc : cSeq d s k = fSeq d s (k + 1) (s k) - fSeq d s k (s k) := rfl
      have := hfk k
      linarith
  have h2 := Finset.add_sum_erase Finset.univ (fSeq d s k) (Finset.mem_univ (s k))
  have := main k
  linarith

theorem ac_c_nonneg {S : Type} [DecidableEq S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (j : ℕ) : 0 ≤ cSeq d s j := by
  have hc : cSeq d s j = fSeq d s j (s (j + 1)) + d (s (j + 1)) (s j) - fSeq d s j (s j) := by
    simp [cSeq, fSeq]
  have := ac_fsub d hd s₀ s hs j (s j) (s (j + 1))
  linarith

theorem ac_c_le {S : Type} [DecidableEq S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (j : ℕ) : cSeq d s j ≤ d (s j) (s (j + 1)) + d (s (j + 1)) (s j) := by
  have hc : cSeq d s j = fSeq d s j (s (j + 1)) + d (s (j + 1)) (s j) - fSeq d s j (s j) := by
    simp [cSeq, fSeq]
  have := ac_fsub d hd s₀ s hs j (s (j + 1)) (s j)
  linarith

/-- Lipschitz bound for proc. -/
theorem ac_proc_le {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (s : S) (u b : ℝ) (hub : u ≤ b) : proc T s u b ≤ (∑ i, T i s) * (b - u) := by
  unfold proc
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hT i s)
  apply max_le (by linarith)
  have := min_le_left b ((i : ℝ) + 2)
  have := le_max_left u ((i : ℝ) + 1)
  linarith

theorem ac_proc_bound {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (s : S) (a b c : ℝ) (hab : a ≤ b) (hc : 0 ≤ c)
    (h : ∀ u, a ≤ u → u < b → proc T s a u < c) : proc T s a b ≤ c := by
  by_contra hcon
  push_neg at hcon
  rcases eq_or_lt_of_le hab with heq | hlt
  · subst heq; rw [flo_proc_self] at hcon; linarith
  set L := ∑ i, T i s with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun i _ => hT i s)
  set e := proc T s a b - c with he
  have he0 : 0 < e := by linarith
  set u := max a (b - e / (L + 1)) with hu
  have hau : a ≤ u := le_max_left _ _
  have hδ : 0 < e / (L + 1) := div_pos he0 (by linarith)
  have hub : u < b := max_lt hlt (by linarith)
  have hsplit := flo_proc_add T s a u b hau hub.le
  have hlip := ac_proc_le T hT s u b hub.le
  have hbu : b - u ≤ e / (L + 1) := by
    have := le_max_right a (b - e / (L + 1)); linarith
  have hLe : L * (b - u) < e := by
    calc L * (b - u) ≤ L * (e / (L + 1)) := mul_le_mul_of_nonneg_left hbu hL0
      _ < (L + 1) * (e / (L + 1)) := by nlinarith
      _ = e := by field_simp
  have := h u hau hub
  linarith

theorem ac_nt_some {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (s : S) (c t t' : ℝ) (hc : 0 ≤ c)
    (h : nextTime T s c t = some t') : t ≤ t' ∧ t' < (m : ℝ) + 1 ∧ proc T s t t' ≤ c := by
  classical
  unfold nextTime at h
  split_ifs at h with hex
  obtain ⟨u, htu, hum, hcu⟩ := hex
  have heq := (Option.some.inj h).symm
  set U := {u : ℝ | t ≤ u ∧ c ≤ proc T s t u} with hU
  have hne : U.Nonempty := ⟨u, htu, hcu⟩
  have hbdd : BddBelow U := ⟨t, fun x hx => hx.1⟩
  have h1 : t ≤ t' := by rw [heq]; exact le_csInf hne (fun x hx => hx.1)
  have h2 : t' ≤ u := by rw [heq]; exact csInf_le hbdd ⟨htu, hcu⟩
  refine ⟨h1, by linarith, ?_⟩
  apply ac_proc_bound T hT s t t' c h1 hc
  intro v htv hvt
  by_contra hh
  push_neg at hh
  have : t' ≤ v := by rw [heq]; exact csInf_le hbdd ⟨htv, hh⟩
  linarith

theorem ac_nt_none {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (s : S) (c t : ℝ) (hc : 0 ≤ c) (htm : t ≤ (m : ℝ) + 1)
    (h : nextTime T s c t = none) : proc T s t ((m : ℝ) + 1) ≤ c := by
  classical
  unfold nextTime at h
  split_ifs at h with hex
  push_neg at hex
  apply ac_proc_bound T hT s t _ c htm hc
  intro u htu hum
  exact hex u htu hum

noncomputable def acP {S : Type} (τ : ℕ → S) (j : ℕ) : List (S × ℝ) :=
  (List.range j).map (fun i => (τ (i + 1), (1 : ℝ)))

theorem ac_P_succ {S : Type} (τ : ℕ → S) (j : ℕ) :
    acP τ (j + 1) = acP τ j ++ [(τ (j + 1), 1)] := by
  simp [acP, List.range_succ]

theorem ac_P_sum {S : Type} (τ : ℕ → S) (j : ℕ) : ((acP τ j).map Prod.snd).sum = j := by
  induction j with
  | zero => simp [acP]
  | succ j ih => rw [ac_P_succ, List.map_append, List.sum_append, ih]; simp

theorem ac_P_last {S : Type} (τ : ℕ → S) (j : ℕ) :
    ((acP τ j).map Prod.fst).getLastD (τ 0) = τ j := by
  cases j with
  | zero => simp [acP]
  | succ j => rw [ac_P_succ, List.map_append]; simp

theorem ac_proc_unit {S : Type} {m : ℕ} (T : Fin m → S → ℝ) (z : S) (j : ℕ) :
    proc T z ((j : ℝ) + 1) ((j : ℝ) + 2) = if h : j < m then T ⟨j, h⟩ z else 0 := by
  unfold proc
  have key : ∀ i : Fin m, T i z * max 0 (min ((j : ℝ) + 2) ((i : ℝ) + 2) - max ((j : ℝ) + 1) ((i : ℝ) + 1))
      = if (i : ℕ) = j then T i z else 0 := by
    intro i
    rcases lt_trichotomy (i : ℕ) j with h | h | h
    · have h' : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [if_neg (by omega)]
      have : max 0 (min ((j : ℝ) + 2) ((i : ℝ) + 2) - max ((j : ℝ) + 1) ((i : ℝ) + 1)) = 0 := by
        apply max_eq_left
        have := min_le_right ((j : ℝ) + 2) ((i : ℝ) + 2)
        have := le_max_left ((j : ℝ) + 1) ((i : ℝ) + 1)
        linarith
      rw [this, mul_zero]
    · rw [if_pos h]
      have h' : (i : ℝ) = j := by exact_mod_cast h
      rw [h']; norm_num
    · have h' : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [if_neg (by omega)]
      have : max 0 (min ((j : ℝ) + 2) ((i : ℝ) + 2) - max ((j : ℝ) + 1) ((i : ℝ) + 1)) = 0 := by
        apply max_eq_left
        have := min_le_left ((j : ℝ) + 2) ((i : ℝ) + 2)
        have := le_max_right ((j : ℝ) + 1) ((i : ℝ) + 1)
        linarith
      rw [this, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; exact Fin.ext h
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    have := i.2
    omega

theorem ac_P_cost {S : Type} (d : S → S → ℝ) (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ)
    (τ : ℕ → S) (hτ : τ 0 = s₀) : ∀ j, floCost d s₀ T (acP τ j) =
      ∑ i ∈ Finset.range j, (d (τ i) (τ (i + 1)) + proc T (τ (i + 1)) ((i : ℝ) + 1) ((i : ℝ) + 2))
  | 0 => by simp [floCost, acP, pathCost, piecesProc]
  | j + 1 => by
    rw [ac_P_succ, flo_cost_snoc, ac_P_cost d s₀ T τ hτ j, ac_P_sum, Finset.sum_range_succ]
    have hl := ac_P_last τ j
    rw [hτ] at hl
    rw [hl]
    rw [show (1 : ℝ) + j = j + 1 by ring, show (j : ℝ) + 1 + 1 = j + 2 by ring]
    ring

theorem ac_sched_eq {S : Type} (d : S → S → ℝ) {m : ℕ} (T : Fin m → S → ℝ)
    (σ : Fin (m + 1) → S) (s₀ : S) :
    schedCost d T σ = ∑ i ∈ Finset.range m,
      (d ((fun n => if h : n < m + 1 then σ ⟨n, h⟩ else s₀) i)
        ((fun n => if h : n < m + 1 then σ ⟨n, h⟩ else s₀) (i + 1)) +
       proc T ((fun n => if h : n < m + 1 then σ ⟨n, h⟩ else s₀) (i + 1)) ((i : ℝ) + 1) ((i : ℝ) + 2)) := by
  unfold schedCost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : (i : ℕ) < m + 1 := by omega
  have h2 : (i : ℕ) + 1 < m + 1 := by omega
  simp only [dif_pos h1, dif_pos h2]
  rw [ac_proc_unit, dif_pos i.2]
  rfl

theorem ac_D_le {S : Type} [Fintype S] (d : S → S → ℝ) (hd : IsTaskSystem d) (a b : S) :
    d a b ≤ ∑ x, ∑ y, d x y := by
  have h1 : d a b ≤ ∑ y, d a y :=
    Finset.single_le_sum (f := fun y => d a y) (fun y _ => ac_dnn d hd a y) (Finset.mem_univ b)
  have h2 : ∑ y, d a y ≤ ∑ x, ∑ y, d x y :=
    Finset.single_le_sum (f := fun x => ∑ y, d x y)
      (fun x _ => Finset.sum_nonneg (fun y _ => ac_dnn d hd x y)) (Finset.mem_univ a)
  linarith

theorem ac_opt_nonneg {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ) (hd : IsTaskSystem d)
    (s₀ : S) {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x) : 0 ≤ offlineOpt d s₀ T := by
  unfold offlineOpt
  apply Finset.le_inf'
  intro σ _
  unfold schedCost
  exact Finset.sum_nonneg (fun i _ => add_nonneg (ac_dnn d hd _ _) (hT _ _))

theorem ac_entry_le {S : Type} [DecidableEq S] (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S)
    (s : ℕ → S) (hs : IsAstarSeq d s₀ s) {m : ℕ} (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x) :
    ∀ k t, entryTime s (cSeq d s) T k = some t → t ≤ (m : ℝ) + 1
  | 0, t, h => by
    simp [entryTime] at h
    rw [← h]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  | k + 1, t', h => by
    obtain ⟨tk, _, h2⟩ := flo_entry_succ s _ T k t' h
    exact (ac_nt_some T hT _ _ _ _ (ac_c_nonneg d hd s₀ s hs k) h2).2.1.le

theorem ac_f_le_opt {S : Type} [Fintype S] [DecidableEq S] (d : S → S → ℝ) (hd : IsTaskSystem d)
    (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s) {m : ℕ} (T : Fin m → S → ℝ)
    (hT : ∀ i x, 0 ≤ T i x) (k : ℕ) (t : ℝ) (h : entryTime s (cSeq d s) T k = some t) (x : S) :
    fSeq d s k x ≤ offlineOpt d s₀ T + ∑ a, ∑ b, d a b := by
  obtain ⟨σ, hσ, hopt⟩ := Finset.exists_mem_eq_inf'
    (⟨fun _ => s₀, by simp⟩ : (Finset.univ.filter (fun σ : Fin (m + 1) → S => σ 0 = s₀)).Nonempty)
    (fun σ => schedCost d T σ)
  have hσ0 : σ 0 = s₀ := (Finset.mem_filter.mp hσ).2
  set τ : ℕ → S := fun n => if h : n < m + 1 then σ ⟨n, h⟩ else s₀ with hτdef
  have hτ : τ 0 = s₀ := by simp [τ, ← hσ0]
  have hP : IsOfflinePieces s₀ ((m : ℝ) + 1) (τ m) (acP τ m) := by
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [acP, List.mem_map] at hp
      obtain ⟨a, _, rfl⟩ := hp
      norm_num
    · rw [ac_P_sum]; ring
    · have := ac_P_last τ m
      rw [hτ] at this
      exact this
  have htm := ac_entry_le d hd s₀ s hs T hT k t h
  have h1 := flo_claim d hd s₀ s hs T hT k t h ((m : ℝ) + 1) htm (τ m) (acP τ m) hP
  have h2 : floCost d s₀ T (acP τ m) = offlineOpt d s₀ T := by
    rw [ac_P_cost d s₀ T τ hτ m]
    unfold offlineOpt
    rw [hopt, ac_sched_eq d T σ s₀]
  have h3 := ac_fsub d hd s₀ s hs k x (τ m)
  have h4 := ac_D_le d hd (τ m) x
  linarith

noncomputable def acδ {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ) : ℝ :=
  ((Finset.univ : Finset (S × S)).filter (fun p => p.1 ≠ p.2)).inf'
    (by obtain ⟨a, b, h⟩ := exists_pair_ne S; exact ⟨(a, b), by simp [h]⟩) (fun p => d p.1 p.2)

theorem ac_δ_le {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ)
    {a b : S} (h : a ≠ b) : acδ d ≤ d a b := by
  unfold acδ
  exact Finset.inf'_le (f := fun p : S × S => d p.1 p.2) (b := (a, b)) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)

theorem ac_δ_pos {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ)
    (hd : IsTaskSystem d) : 0 < acδ d := by
  unfold acδ
  rw [Finset.lt_inf'_iff]
  rintro ⟨a, b⟩ hp
  simp at hp
  exact hd.pos a b hp

theorem ac_psi_bdd {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ)
    (hd : IsTaskSystem d) :
    BddAbove {r : ℝ | ∃ (k : ℕ) (v : Fin (k + 1) → S), v 0 = v (Fin.last k) ∧
      0 < ∑ i : Fin k, d (v i.succ) (v i.castSucc) ∧
      r = (∑ i : Fin k, d (v i.castSucc) (v i.succ)) / ∑ i : Fin k, d (v i.succ) (v i.castSucc)} := by
  refine ⟨(∑ x, ∑ y, d x y) / acδ d, ?_⟩
  rintro r ⟨k, v, _, hpos, rfl⟩
  rw [div_le_div_iff₀ hpos (ac_δ_pos d hd), Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : v i.castSucc = v i.succ
  · rw [h, hd.diag]; simp
  · have h1 := ac_D_le d hd (v i.castSucc) (v i.succ)
    have h2 := ac_δ_le d (Ne.symm h)
    have h3 := ac_δ_pos d hd
    have h4 := ac_dnn d hd (v i.castSucc) (v i.succ)
    have hD : 0 ≤ ∑ x, ∑ y, d x y := le_trans h4 h1
    calc d (v i.castSucc) (v i.succ) * acδ d ≤ (∑ x, ∑ y, d x y) * acδ d :=
          mul_le_mul_of_nonneg_right h1 h3.le
      _ ≤ (∑ x, ∑ y, d x y) * d (v i.succ) (v i.castSucc) := mul_le_mul_of_nonneg_left h2 hD

theorem ac_psi_mem {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ)
    (hd : IsTaskSystem d) (k : ℕ) (v : Fin (k + 1) → S) (h0 : v 0 = v (Fin.last k))
    (hpos : 0 < ∑ i : Fin k, d (v i.succ) (v i.castSucc)) :
    ∑ i : Fin k, d (v i.castSucc) (v i.succ) ≤
      cycleOffsetRatio d * ∑ i : Fin k, d (v i.succ) (v i.castSucc) := by
  have := le_csSup (ac_psi_bdd d hd) ⟨k, v, h0, hpos, rfl⟩
  rw [div_le_iff₀ hpos] at this
  exact this

theorem ac_psi_ge1 {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ)
    (hd : IsTaskSystem d) : 1 ≤ cycleOffsetRatio d := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne S
  have hpos : 0 < ∑ i : Fin 2, d ((![a, b, a] : Fin 3 → S) i.succ) ((![a, b, a] : Fin 3 → S) i.castSucc) := by
    simp [Fin.sum_univ_two]
    linarith [hd.pos a b hab, hd.pos b a (Ne.symm hab)]
  have := ac_psi_mem d hd 2 ![a, b, a] (by simp) hpos
  simp [Fin.sum_univ_two] at this hpos
  by_contra hc
  push_neg at hc
  nlinarith

theorem ac_walk {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S] (d : S → S → ℝ)
    (hd : IsTaskSystem d) (s : ℕ → S) (hs1 : ∀ i, s (i + 1) ≠ s i) (k : ℕ) :
    ∑ i ∈ Finset.range k, d (s i) (s (i + 1)) ≤
      cycleOffsetRatio d * ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) +
        cycleOffsetRatio d * ∑ x, ∑ y, d x y := by
  have hψ := ac_psi_ge1 d hd
  have hD : 0 ≤ ∑ x, ∑ y, d x y :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ac_dnn d hd x y))
  have hBnn : 0 ≤ ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) :=
    Finset.sum_nonneg (fun i _ => ac_dnn d hd _ _)
  cases k with
  | zero =>
    simp
    exact mul_nonneg (by linarith) hD
  | succ j =>
    let g : ℕ → S := fun n => if n ≤ j + 1 then s n else s 0
    let v : Fin (j + 3) → S := fun i => g i
    have hfwd : ∑ i : Fin (j + 2), d (v i.castSucc) (v i.succ) =
        ∑ i ∈ Finset.range (j + 1), d (s i) (s (i + 1)) + d (s (j + 1)) (s 0) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · rw [← Fin.sum_univ_eq_sum_range (fun i => d (s i) (s (i + 1)))]
        apply Finset.sum_congr rfl
        intro i _
        have h1 : (i : ℕ) ≤ j + 1 := by omega
        have h2 : (i : ℕ) + 1 ≤ j + 1 := by omega
        simp [v, g, h1, h2]
      · simp [v, g]
    have hback : ∑ i : Fin (j + 2), d (v i.succ) (v i.castSucc) =
        ∑ i ∈ Finset.range (j + 1), d (s (i + 1)) (s i) + d (s 0) (s (j + 1)) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · rw [← Fin.sum_univ_eq_sum_range (fun i => d (s (i + 1)) (s i))]
        apply Finset.sum_congr rfl
        intro i _
        have h1 : (i : ℕ) ≤ j + 1 := by omega
        have h2 : (i : ℕ) + 1 ≤ j + 1 := by omega
        simp [v, g, h1, h2]
      · simp [v, g]
    have h0 : v 0 = v (Fin.last (j + 2)) := by simp [v, g]
    have hB1 : d (s 1) (s 0) ≤ ∑ i ∈ Finset.range (j + 1), d (s (i + 1)) (s i) :=
      Finset.single_le_sum (f := fun i => d (s (i + 1)) (s i)) (fun i _ => ac_dnn d hd _ _)
        (Finset.mem_range.mpr (by omega))
    have hpos1 := hd.pos (s 1) (s 0) (hs1 0)
    have hpos : 0 < ∑ i : Fin (j + 2), d (v i.succ) (v i.castSucc) := by
      rw [hback]; linarith [ac_dnn d hd (s 0) (s (j + 1))]
    have hm := ac_psi_mem d hd (j + 2) v h0 hpos
    rw [hfwd, hback] at hm
    have e1 := ac_dnn d hd (s (j + 1)) (s 0)
    have e2 := ac_D_le d hd (s 0) (s (j + 1))
    have e3 := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ cycleOffsetRatio d)
    nlinarith

theorem ac_bound {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (w : ℝ) (hw : (2 * (Fintype.card S : ℝ) - 1) * cycleOffsetRatio d < w)
    (m : ℕ) (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x) :
    astarCost d s T ≤ ENNReal.ofReal (w * offlineOpt d s₀ T +
      ((2 * (Fintype.card S : ℝ) - 1) * cycleOffsetRatio d * (∑ x, ∑ y, d x y) +
        cycleOffsetRatio d * (∑ x, ∑ y, d x y) + 2 * (∑ x, ∑ y, d x y))) := by
  classical
  have hψ1 := ac_psi_ge1 d hd
  have hD : 0 ≤ ∑ x, ∑ y, d x y :=
    Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => ac_dnn d hd x y))
  have hOPT := ac_opt_nonneg d hd s₀ T hT
  have hc0 : ∀ j, 0 ≤ cSeq d s j := ac_c_nonneg d hd s₀ s hs
  have hn : 1 ≤ Fintype.card S := Fintype.card_pos
  have hn2 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast hn
  have hCB : ∀ k t, entryTime s (cSeq d s) T k = some t →
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) ≤
        (2 * (Fintype.card S : ℝ) - 1) * (offlineOpt d s₀ T + ∑ x, ∑ y, d x y) := by
    intro k t h
    rw [← ac_potential d s₀ s hs k]
    have hf := ac_f_le_opt d hd s₀ s hs T hT k t h
    have h1 := Finset.sum_le_card_nsmul (Finset.univ.erase (s k)) (fun x => fSeq d s k x)
      (offlineOpt d s₀ T + ∑ x, ∑ y, d x y) (fun x _ => hf x)
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul,
      Nat.cast_sub hn] at h1
    push_cast at h1
    have := hf (s k)
    linarith
  have hB : ∀ k : ℕ, (k : ℝ) * acδ d ≤ ∑ i ∈ Finset.range k, d (s (i + 1)) (s i) := by
    intro k
    have := Finset.card_nsmul_le_sum (Finset.range k) (fun i => d (s (i + 1)) (s i)) (acδ d)
      (fun i _ => ac_δ_le d ((hs.2 i).1))
    simpa using this
  have hδ := ac_δ_pos d hd
  have hex : ∃ N, entryTime s (cSeq d s) T N = none := by
    by_contra hcon
    push_neg at hcon
    set X := (2 * (Fintype.card S : ℝ) - 1) * (offlineOpt d s₀ T + ∑ x, ∑ y, d x y) with hX
    obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp (hcon (⌈X / acδ d⌉₊ + 1))
    have h1 := hCB _ t ht
    have h2 := hB (⌈X / acδ d⌉₊ + 1)
    have hC : 0 ≤ ∑ i ∈ Finset.range (⌈X / acδ d⌉₊ + 1), cSeq d s i :=
      Finset.sum_nonneg (fun i _ => hc0 i)
    have h3 : X / acδ d < ((⌈X / acδ d⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (X / acδ d)]
    have := (div_lt_iff₀ hδ).mp h3
    linarith
  have hk0 : entryTime s (cSeq d s) T (Nat.find hex) = none := Nat.find_spec hex
  have hk0pos : Nat.find hex ≠ 0 := by
    intro h; rw [h] at hk0; simp [entryTime] at hk0
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0pos
  have hsome : ∀ j ≤ k, ∃ t, entryTime s (cSeq d s) T j = some t := by
    intro j hj
    apply Option.ne_none_iff_exists'.mp
    exact Nat.find_min hex (by omega)
  have hnone : ∀ j, k + 1 ≤ j → entryTime s (cSeq d s) T j = none := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      have hk' : Nat.find hex = k + 1 := hk
      rw [← hk']; exact hk0
    | succ j _ ih => simp [entryTime, ih]
  unfold astarCost noCost
  rw [tsum_eq_sum (s := Finset.range (k + 1)) (fun j hj => by
    simp at hj
    simp only [stageCost, hnone j (by omega)])]
  have hstage : ∀ j ∈ Finset.range (k + 1), stageCost d s (cSeq d s) T j ≤
      ENNReal.ofReal (cSeq d s j + if j < k then d (s j) (s (j + 1)) else 0) := by
    intro j hj
    simp at hj
    obtain ⟨tj, htj⟩ := hsome j (by omega)
    by_cases hjk : j < k
    · obtain ⟨tj1, htj1⟩ := hsome (j + 1) (by omega)
      obtain ⟨tj', h1, h2⟩ := flo_entry_succ s _ T j tj1 htj1
      rw [htj] at h1
      obtain rfl : tj = tj' := Option.some.inj h1
      have := (ac_nt_some T hT _ _ _ _ (hc0 j) h2).2.2
      simp only [stageCost, htj, htj1, if_pos hjk]
      apply ENNReal.ofReal_le_ofReal
      linarith
    · have hjk' : j = k := by omega
      subst hjk'
      have hn1 := hnone (j + 1) le_rfl
      have hn' : nextTime T (s j) (cSeq d s j) tj = none := by
        simpa [entryTime, htj] using hn1
      have := ac_nt_none T hT _ _ _ (hc0 j) (ac_entry_le d hd s₀ s hs T hT j tj htj) hn'
      simp only [stageCost, htj, hn1, if_neg hjk]
      apply ENNReal.ofReal_le_ofReal
      linarith
  refine (Finset.sum_le_sum hstage).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hc0 j) (by
    split_ifs
    · exact ac_dnn d hd _ _
    · exact le_rfl))]
  apply ENNReal.ofReal_le_ofReal
  rw [Finset.sum_range_succ, if_neg (lt_irrefl k), add_zero]
  have hsplit : ∑ i ∈ Finset.range k, (cSeq d s i + if i < k then d (s i) (s (i + 1)) else 0) =
      ∑ i ∈ Finset.range k, cSeq d s i + ∑ i ∈ Finset.range k, d (s i) (s (i + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp at hi
    rw [if_pos hi]
  rw [hsplit]
  have hW := ac_walk d hd s (fun i => (hs.2 i).1) k
  obtain ⟨tk, htk⟩ := hsome k le_rfl
  have hCBk := hCB k tk htk
  have hck := ac_c_le d hd s₀ s hs k
  have hd1 := ac_D_le d hd (s k) (s (k + 1))
  have hd2 := ac_D_le d hd (s (k + 1)) (s k)
  have hC0 : 0 ≤ ∑ i ∈ Finset.range k, cSeq d s i := Finset.sum_nonneg (fun i _ => hc0 i)
  have p1 := mul_nonneg (sub_nonneg.mpr hψ1) hC0
  have p2 := mul_le_mul_of_nonneg_left hCBk (by linarith : (0 : ℝ) ≤ cycleOffsetRatio d)
  have p3 := mul_le_mul_of_nonneg_right hw.le hOPT
  linarith

theorem astar_core {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d)
    (seq : S → ℕ → S) (hseq : ∀ s₀, IsAstarSeq d s₀ (seq s₀))
    (w : ℝ) (hw : (2 * (Fintype.card S : ℝ) - 1) * cycleOffsetRatio d < w) :
    ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      astarCost d (seq s₀) T ≤ ENNReal.ofReal (w * offlineOpt d s₀ T + K) :=
  ⟨_, fun s₀ _ T hT => ac_bound d hd s₀ (seq s₀) (hseq s₀) w hw _ T hT⟩
end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic


theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d)
    (seq : S → ℕ → S) (hseq : ∀ s₀, IsAstarSeq d s₀ (seq s₀))
    (w : ℝ) (hw : (2 * (Fintype.card S : ℝ) - 1) * cycleOffsetRatio d < w) :
    ∃ K : ℝ, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      astarCost d (seq s₀) T ≤ ENNReal.ofReal (w * offlineOpt d s₀ T + K) := by
  exact astar_core d hd seq hseq w hw
