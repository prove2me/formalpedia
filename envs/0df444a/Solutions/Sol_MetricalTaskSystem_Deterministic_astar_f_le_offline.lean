-- Prove2me | solution 1 for MetricalTaskSystem.Deterministic.astar_f_le_offline
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:07:20.571952+00:00
-- url     : https://prove2.me/submissions/8c51d2b2-7571-4eab-a8a9-8330e18097fb

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

theorem flo_core {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (m : ℕ) (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (k : ℕ) (tk : ℝ) (htk : entryTime s (cSeq d s) T k = some tk) (x : S) :
    fSeq d s k x ≤ offlineCostTo d s₀ T tk x := by
  have h1 := flo_entry_ge_one s _ T k tk htk
  have : Nonempty {P : List (S × ℝ) // IsOfflinePieces s₀ tk x P} :=
    ⟨⟨[(x, tk - 1)], by
      refine ⟨?_, ?_, ?_⟩
      · intro p hp; simp at hp; rw [hp]; simp; linarith
      · simp
      · simp⟩⟩
  unfold offlineCostTo
  apply le_ciInf
  intro P
  exact flo_claim d hd s₀ s hs T hT k tk htk tk le_rfl x P.1 P.2

end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic


theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (s₀ : S) (s : ℕ → S) (hs : IsAstarSeq d s₀ s)
    (m : ℕ) (T : Fin m → S → ℝ) (hT : ∀ i x, 0 ≤ T i x)
    (k : ℕ) (tk : ℝ) (htk : entryTime s (cSeq d s) T k = some tk) (x : S) :
    fSeq d s k x ≤ offlineCostTo d s₀ T tk x := by
  exact flo_core d hd s₀ s hs m T hT k tk htk x
