-- Prove2me | solution 1 for KServer.wfaU_potential_criterion_univ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:05:06.493157+00:00
-- url     : https://prove2.me/submissions/2b70914f-d4f1-498a-b6d1-5ea031962030

import Mathlib
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_wfaU

open KServer


private theorem moveCost_triangle {k : ℕ} {M : Type*} [MetricSpace M]
    (A B C : Config k M) : moveCost A C ≤ moveCost A B + moveCost B C := by
  unfold moveCost
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

private theorem moveCost_nonneg {k : ℕ} {M : Type*} [MetricSpace M] (A B : Config k M) :
    0 ≤ moveCost A B := Finset.sum_nonneg fun i _ => dist_nonneg

private theorem moveCost_self {k : ℕ} {M : Type*} [MetricSpace M] (A : Config k M) :
    moveCost A A = 0 := by unfold moveCost; simp

private theorem sched_exists (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) : ∃ S : ℕ → Config k M, ServesFrom C₀ σ S := by
  classical
  have hk0 : (0 : ℕ) < k := hk
  refine ⟨fun j => if j = 0 then C₀ else fun _ => σ.getD (j - 1) (C₀ ⟨0, hk0⟩), by simp, ?_⟩
  intro j
  refine ⟨⟨0, hk0⟩, ?_⟩
  simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem σ _ j.2]
  simp

private def Wset {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : Set ℝ :=
  {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X}

private theorem workFn_eq {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn C₀ σ X = sInf (Wset C₀ σ X) := rfl

private theorem Wset_nonempty (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : (Wset C₀ σ X).Nonempty := by
  obtain ⟨S, hS⟩ := sched_exists k hk M C₀ σ
  exact ⟨_, ⟨S, hS, rfl⟩⟩

private theorem Wset_bdd {k : ℕ} {M : Type*} [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : BddBelow (Wset C₀ σ X) := by
  refine ⟨0, ?_⟩
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  have h2 := moveCost_nonneg (S σ.length) X
  linarith

/-- Nonnegativity. -/
private theorem wf_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by
  rw [workFn_eq]
  refine le_csInf (Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, -, rfl⟩
  have h1 : (0:ℝ) ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) :=
    Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  have h2 := moveCost_nonneg (S σ.length) X
  linarith

/-- Work-function values stay within the distance of their configurations. -/
private theorem wf_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by
  rw [workFn_eq, workFn_eq]
  have hkey : ∀ c ∈ Wset C₀ σ Y, sInf (Wset C₀ σ X) - moveCost Y X ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) X ∈ Wset C₀ σ X := ⟨S, hS, rfl⟩
    have h1 := csInf_le (Wset_bdd C₀ σ X) hmem
    have h2 := moveCost_triangle (S σ.length) Y X
    linarith
  have := le_csInf (Wset_nonempty k hk M C₀ σ Y) hkey
  linarith

/-- Serving one more request never decreases the work function. -/
private theorem wf_mono (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by
  rw [workFn_eq, workFn_eq]
  refine le_csInf (Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hlen : (σ ++ [r]).length = σ.length + 1 := by simp
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨j, by rw [hlen]; omega⟩
    exact ⟨i, by rw [hi]; simp [List.getElem_append_left j.2]⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) X ∈ Wset C₀ σ X := ⟨S, hserve, rfl⟩
  have h1 := csInf_le (Wset_bdd C₀ σ X) hmem
  have h2 := moveCost_triangle (S σ.length) (S (σ.length + 1)) X
  rw [hlen, Finset.sum_range_succ]
  linarith

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- Serving a request the target configuration already covers costs nothing. -/
private theorem wf_covered (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by
  classical
  refine le_antisymm ?_ (wf_mono k hk M C₀ σ r X)
  rw [workFn_eq, workFn_eq]
  refine csInf_le_csInf (Wset_bdd C₀ (σ ++ [r]) X) (Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  set S' : ℕ → Config k M := fun j => if j = n + 1 then X else S j with hS'def
  have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
    intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
  have hS'top : S' (n + 1) = X := by rw [hS'def]; simp
  have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
    refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
    intro j
    have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
    by_cases hjn : (j : ℕ) = n
    · obtain ⟨i0, hi0⟩ := hX
      refine ⟨i0, ?_⟩
      rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hi0]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp [hjn, hn]
    · obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by omega⟩
      refine ⟨i, ?_⟩
      rw [hS'ne _ (by omega), hi]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by omega)]
  refine ⟨S', hserves, ?_⟩
  rw [hlen, Finset.sum_range_succ]
  have e1 : ∀ j ∈ Finset.range n,
      moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [hS'ne _ (by omega), hS'ne _ (by omega)]
  rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, moveCost_self]
  ring

private theorem moveCost_update {k : ℕ} {M : Type*} [MetricSpace M]
    (X : Config k M) (i : Fin k) (v : M) :
    moveCost (Function.update X i v) X = dist v (X i) := by
  classical
  have h := sum_diff_single (fun j => dist (Function.update X i v j) (X j))
    (fun _ => (0:ℝ)) i (fun j hj => by
      show dist (Function.update X i v j) (X j) = 0
      rw [Function.update_of_ne hj]; simp)
  simp only [Finset.sum_const_zero, sub_zero, Function.update_self] at h
  simpa [moveCost] using h

/-- One direction of the work-function recurrence: ending at `X` after serving `r` costs at
most what it costs to end at `X` with server `i` parked on `r`, plus that server's trip. -/
private theorem wf_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFn C₀ (σ ++ [r]) X ≤ workFn C₀ σ (Function.update X i r) + dist r (X i) := by
  classical
  rw [workFn_eq, workFn_eq]
  set X' : Config k M := Function.update X i r with hX'def
  have hkey : ∀ c ∈ Wset C₀ σ X', sInf (Wset C₀ (σ ++ [r]) X) - dist r (X i) ≤ c := by
    rintro c ⟨S, hS, rfl⟩
    set n := σ.length with hn
    have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
    set S' : ℕ → Config k M := fun j => if j = n + 1 then X' else S j with hS'def
    have hS'ne : ∀ j, j ≠ n + 1 → S' j = S j := by
      intro j hj; rw [hS'def]; simp only []; rw [if_neg hj]
    have hS'top : S' (n + 1) = X' := by rw [hS'def]; simp
    have hserves : ServesFrom C₀ (σ ++ [r]) S' := by
      refine ⟨by rw [hS'ne 0 (by omega)]; exact hS.1, ?_⟩
      intro j
      have hjv : (j : ℕ) < n + 1 := by rw [← hlen]; exact j.2
      by_cases hjn : (j : ℕ) = n
      · refine ⟨i, ?_⟩
        rw [show ((j:ℕ) + 1) = n + 1 by omega, hS'top, hX'def, Function.update_self]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (by omega)]
        simp [hjn, hn]
      · obtain ⟨i2, hi2⟩ := hS.2 ⟨(j : ℕ), by omega⟩
        refine ⟨i2, ?_⟩
        rw [hS'ne _ (by omega), hi2]
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_left (by omega)]
    have hmem : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X ∈ Wset C₀ (σ ++ [r]) X := ⟨S', hserves, rfl⟩
    have hval : (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S' j) (S' (j + 1)))
        + moveCost (S' (σ ++ [r]).length) X
        = ((∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) X')
          + dist r (X i) := by
      rw [hlen, Finset.sum_range_succ]
      have e1 : ∀ j ∈ Finset.range n,
          moveCost (S' j) (S' (j + 1)) = moveCost (S j) (S (j + 1)) := by
        intro j hj
        simp only [Finset.mem_range] at hj
        rw [hS'ne _ (by omega), hS'ne _ (by omega)]
      rw [Finset.sum_congr rfl e1, hS'ne n (by omega), hS'top, hX'def, moveCost_update]
    rw [hval] at hmem
    have h1 := csInf_le (Wset_bdd C₀ (σ ++ [r]) X) hmem
    linarith
  have := le_csInf (Wset_nonempty k hk M C₀ σ X') hkey
  linarith

private theorem wf_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFn C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFn C₀ (σ ++ [r]) X := by
  classical
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
    refine ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_inf' hne
    (fun i => workFn C₀ σ (Function.update X i r) + dist r (X i))
  refine ⟨i₀, ?_⟩
  rw [← hi₀, workFn_eq]
  refine le_csInf (Wset_nonempty k hk M C₀ (σ ++ [r]) X) ?_
  rintro c ⟨S, hS, rfl⟩
  set n := σ.length with hn
  have hlen : (σ ++ [r]).length = n + 1 := by simp [hn]
  -- the algorithm has a server on the last request
  have hreq : (σ ++ [r]).get ⟨n, by rw [hlen]; omega⟩ = r := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (by omega)]
    simp [hn]
  obtain ⟨i₁, hi₁⟩ := hS.2 ⟨n, by rw [hlen]; omega⟩
  rw [hreq] at hi₁
  set Y : Config k M := Function.update X i₁ r with hYdef
  -- the same schedule serves the shorter sequence
  have hserve : ServesFrom C₀ σ S := by
    refine ⟨hS.1, ?_⟩
    intro j
    obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), by rw [hlen]; omega⟩
    refine ⟨i, ?_⟩
    rw [hi]
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_left (by omega)]
  have hmemY : (∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) Y
      ∈ Wset C₀ σ Y := ⟨S, hserve, rfl⟩
  have hwY : workFn C₀ σ Y
      ≤ (∑ j ∈ Finset.range n, moveCost (S j) (S (j + 1))) + moveCost (S n) Y := by
    rw [workFn_eq]; exact csInf_le (Wset_bdd C₀ σ Y) hmemY
  -- dropping the served index from the final move removes exactly `dist r (X i₁)`
  have hmv : moveCost (S (n + 1)) Y = moveCost (S (n + 1)) X - dist r (X i₁) := by
    have h : (∑ j, dist (S (n + 1) j) (Y j)) - (∑ j, dist (S (n + 1) j) (X j))
        = dist (S (n + 1) i₁) (Y i₁) - dist (S (n + 1) i₁) (X i₁) :=
      sum_diff_single (fun j => dist (S (n + 1) j) (Y j))
        (fun j => dist (S (n + 1) j) (X j)) i₁
        (fun j hj => by
          show dist (S (n + 1) j) (Y j) = dist (S (n + 1) j) (X j)
          rw [hYdef, Function.update_of_ne hj])
    rw [hYdef, Function.update_self, hi₁, dist_self] at h
    unfold moveCost
    linarith
  have htri := moveCost_triangle (S n) (S (n + 1)) Y
  have hfi : workFn C₀ σ (Function.update X i₁ r) + dist r (X i₁)
      ≤ (∑ j ∈ Finset.range (σ ++ [r]).length, moveCost (S j) (S (j + 1)))
        + moveCost (S (σ ++ [r]).length) X := by
    rw [hlen, Finset.sum_range_succ, ← hYdef]
    linarith
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ i₁)) hfi
private theorem wf_nil (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (X : Config k M) : workFn C₀ [] X = moveCost C₀ X := by
  classical
  have hset : Wset C₀ ([] : List M) X = {moveCost C₀ X} := by
    ext c
    constructor
    · rintro ⟨S, hS, rfl⟩
      simp [hS.1]
    · rintro rfl
      exact ⟨fun _ => C₀, ⟨rfl, fun j => j.elim0⟩, by simp⟩
  rw [workFn_eq, hset, csInf_singleton]

private theorem offlineCost_le_wf (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    offlineCost C₀ σ ≤ workFn C₀ σ X := by
  classical
  rw [workFn_eq]
  refine le_csInf (Wset_nonempty k hk M C₀ σ X) ?_
  rintro c ⟨S, hS, rfl⟩
  have hbdd : BddBelow {c : ℝ | ∃ T : ℕ → Config k M, ServesFrom C₀ σ T ∧
      c = ∑ j ∈ Finset.range σ.length, moveCost (T j) (T (j + 1))} := by
    refine ⟨0, ?_⟩
    rintro z ⟨T, -, rfl⟩
    exact Finset.sum_nonneg fun j _ => moveCost_nonneg _ _
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      ∈ {c : ℝ | ∃ T : ℕ → Config k M, ServesFrom C₀ σ T ∧
        c = ∑ j ∈ Finset.range σ.length, moveCost (T j) (T (j + 1))} := ⟨S, hS, rfl⟩
  have h1 : offlineCost C₀ σ
      ≤ ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)) := by
    unfold offlineCost
    exact csInf_le hbdd hmem
  have h2 := moveCost_nonneg (S σ.length) X
  linarith



private theorem wfU_le {k : ℕ} {M : Type*} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type*} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem wfU_self {k : ℕ} {M : Type*} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

private theorem mc_perm {k : ℕ} {M : Type*} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k))) = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem sum_perm {k : ℕ} {M : Type*} [MetricSpace M] (v : M) (Y : Config k M)
    (π : Equiv.Perm (Fin k)) : ∑ i, dist v (Y (π i)) = ∑ i, dist v (Y i) :=
  Fintype.sum_equiv π (fun i => dist v (Y (π i))) (fun i => dist v (Y i)) (fun i => rfl)

/-- **The Lipschitz property of the unified work function.** -/
private theorem wfU_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFnU C₀ σ X ≤ workFnU C₀ σ Y + moveCost Y X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ Y
  have h1 : workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ (π : Equiv.Perm (Fin k))) := wfU_le C₀ σ X π
  have h2 := wf_lipschitz k hk M C₀ σ (X ∘ (π : Equiv.Perm (Fin k)))
    (Y ∘ (π : Equiv.Perm (Fin k)))
  rw [hπ, mc_perm Y X π] at h2
  linarith



private theorem update_comp {k : ℕ} {M : Type*} (X : Config k M) (i : Fin k) (r : M)
    (π : Equiv.Perm (Fin k)) :
    (Function.update X i r) ∘ (π : Equiv.Perm (Fin k))
      = Function.update (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) r := by
  classical
  funext l
  by_cases h : l = π.symm i
  · subst h
    rw [Function.comp_apply, Equiv.apply_symm_apply, Function.update_self,
      Function.update_self]
  · have h2 : (π : Equiv.Perm (Fin k)) l ≠ i := by
      intro hc; exact h (by rw [← hc]; simp)
    simp [Function.update_of_ne h, Function.update_of_ne h2]

private theorem wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (Function.update X i r)
  have h1 := wfU_le C₀ (σ ++ [r]) X π
  have h2 := wf_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

private theorem wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := wf_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

private theorem wfU_covered (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFnU C₀ (σ ++ [r]) X = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  refine wf_covered k hk M C₀ σ r (X ∘ π) ?_
  obtain ⟨i, hi⟩ := hX
  exact ⟨π.symm i, by simpa using hi⟩

private theorem wfU_step_self (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (U : Config k M) :
    ∃ i : Fin k, workFnU C₀ (σ ++ [r]) U
      = workFnU C₀ (σ ++ [r]) (Function.update U i r) + dist r (U i) := by
  classical
  obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ σ r U
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    have := wfU_rec_le k hk M C₀ σ r U i
    rw [← hc] at this
    exact this
  · have hcov : ∃ l, (Function.update U i r) l = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ σ r (Function.update U i r) hcov
    rw [hc]
    exact hi

private theorem wfU_nil_self {k : ℕ} (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) : workFnU C₀ [] C₀ = 0 := by
  refine le_antisymm ?_ ?_
  · have h := wfU_le C₀ [] C₀ 1
    have h0 : workFn C₀ [] (C₀ ∘ (1 : Equiv.Perm (Fin k))) = 0 := by
      rw [wf_nil k hk M C₀ (C₀ ∘ (1 : Equiv.Perm (Fin k)))]
      unfold moveCost
      simp
    rw [h0] at h
    exact h
  · refine le_ciInf fun π => ?_
    rw [wf_nil k hk M C₀ (C₀ ∘ π)]
    exact Finset.sum_nonneg fun i _ => dist_nonneg

private theorem offlineCost_le_wfU (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    offlineCost C₀ σ ≤ workFnU C₀ σ X :=
  le_ciInf fun π => offlineCost_le_wf k hk M C₀ σ (X ∘ π)

/-- The classical Work Function Algorithm's move is exactly what the update operator
charges to the unlabelled work function. -/
private theorem wfaU_step_eq (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (l : List M) (Cprev : Config k M) (r : M) :
    workFnU C₀ (l ++ [r]) Cprev
      = workFnU C₀ (l ++ [r]) (wfaUStep hk C₀ l Cprev r)
        + moveCost Cprev (wfaUStep hk C₀ l Cprev r) := by
  refine le_antisymm ?_ ?_
  · have h := wfU_lipschitz k hk M C₀ (l ++ [r]) Cprev (wfaUStep hk C₀ l Cprev r)
    have hc : moveCost (wfaUStep hk C₀ l Cprev r) Cprev
        = moveCost Cprev (wfaUStep hk C₀ l Cprev r) := by
      unfold moveCost
      exact Finset.sum_congr rfl fun i _ => dist_comm _ _
    linarith [h, hc.symm ▸ h]
  · obtain ⟨i, hi⟩ := wfU_rec_ge k hk M C₀ l r Cprev
    have hcov : ∃ j, (Function.update Cprev i r) j = r := ⟨i, Function.update_self _ _ _⟩
    have hc := wfU_covered k hk M C₀ l r (Function.update Cprev i r) hcov
    have hmin := wfaUStep_min hk C₀ l Cprev r (Function.update Cprev i r) hcov
    have hmc : moveCost Cprev (Function.update Cprev i r) = dist r (Cprev i) := by
      unfold moveCost
      rw [Finset.sum_eq_single i]
      · rw [Function.update_self]; exact dist_comm _ _
      · intro j _ hj; rw [Function.update_of_ne hj, dist_self]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [← hc] at hi
    linarith

/-- **Lemma 2 of Bein, Chrobak and Larmore for the classical WFA.** -/
private theorem wfaU_growth (k : ℕ) (hk : 0 < k) (M : Type*) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (σ : List M) (u : ℕ → ℝ)
    (hu : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) :
    (WFAU hk C₀).cost σ + offlineCost C₀ σ ≤ ∑ t ∈ Finset.range σ.length, u t := by
  classical
  set S : ℕ → Config k M := fun t => (WFAU hk C₀).conf (σ.take t) with hSdef
  set f : ℕ → ℝ := fun t => workFnU C₀ (σ.take t) (S t) with hfdef
  have hsplit : ∀ (t : ℕ) (ht : t < σ.length), σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
    intro t ht
    rw [List.take_succ, List.getElem?_eq_getElem ht]
    rfl
  have hSsucc : ∀ (t : ℕ) (ht : t < σ.length),
      S (t + 1) = wfaUStep hk C₀ (σ.take t) (S t) (σ[t]'ht) := by
    intro t ht
    show (wfaUAux hk C₀ (σ.take (t + 1))).2
        = wfaUStep hk C₀ (σ.take t) ((wfaUAux hk C₀ (σ.take t)).2) (σ[t]'ht)
    rw [hsplit t ht, wfaUAux_append hk C₀ (σ.take t) (σ[t]'ht), wfaUAux_fst]
  have hstep : ∀ (t : ℕ) (ht : t < σ.length),
      workFnU C₀ (σ.take (t + 1)) (S t)
        = workFnU C₀ (σ.take (t + 1)) (S (t + 1)) + moveCost (S t) (S (t + 1)) := by
    intro t ht
    rw [hSsucc t ht]
    rw [hsplit t ht]
    exact wfaU_step_eq k hk M C₀ (σ.take t) (S t) (σ[t]'ht)
  have hbound : ∀ t ∈ Finset.range σ.length,
      moveCost (S t) (S (t + 1)) ≤ (f t + u t) - f (t + 1) := by
    intro t htm
    have ht : t < σ.length := Finset.mem_range.mp htm
    have h1 := hstep t ht
    have h2 := hu t ht (S t)
    rw [hfdef]
    simp only
    linarith
  have hcost : (WFAU hk C₀).cost σ ≤ ∑ t ∈ Finset.range σ.length, ((f t + u t) - f (t + 1)) := by
    refine le_of_eq_of_le ?_ (Finset.sum_le_sum hbound)
    rfl
  have hsplit2 : (∑ t ∈ Finset.range σ.length, ((f t + u t) - f (t + 1)))
      = (∑ t ∈ Finset.range σ.length, (f t - f (t + 1)))
        + ∑ t ∈ Finset.range σ.length, u t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have htel : (∑ t ∈ Finset.range σ.length, (f t - f (t + 1))) = f 0 - f σ.length :=
    Finset.sum_range_sub' f σ.length
  have hf0 : f 0 = 0 := by
    show workFnU C₀ (σ.take 0) ((WFAU hk C₀).conf (σ.take 0)) = 0
    rw [List.take_zero]
    have hc : (WFAU hk C₀).conf ([] : List M) = C₀ := rfl
    rw [hc]
    exact wfU_nil_self hk M C₀
  have hfn : offlineCost C₀ σ ≤ f σ.length := by
    have h := offlineCost_le_wfU k hk M C₀ σ (S σ.length)
    rw [hfdef]
    simpa using h
  rw [hsplit2, htel, hf0] at hcost
  linarith


private theorem wf_approx (k : ℕ) (hk : 1 ≤ k) (M : Type*) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Config k M, workFn C₀ σ X ≤ offlineCost C₀ σ + ε := by
  classical
  set T : Set ℝ := {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C₀ σ S ∧
    c = ∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))} with hT
  have hTne : T.Nonempty := by
    obtain ⟨S, hS⟩ := sched_exists k hk M C₀ σ
    exact ⟨_, ⟨S, hS, rfl⟩⟩
  have hoff : offlineCost C₀ σ = sInf T := rfl
  have hlt : sInf T < offlineCost C₀ σ + ε := by rw [hoff]; linarith
  obtain ⟨c, hcT, hclt⟩ := exists_lt_of_csInf_lt hTne hlt
  obtain ⟨S, hS, rfl⟩ := hcT
  refine ⟨S σ.length, ?_⟩
  have hmem : (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
      + moveCost (S σ.length) (S σ.length) ∈ Wset C₀ σ (S σ.length) := ⟨S, hS, rfl⟩
  have h1 : workFn C₀ σ (S σ.length)
      ≤ (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
        + moveCost (S σ.length) (S σ.length) := by
    rw [workFn_eq]; exact csInf_le (Wset_bdd C₀ σ (S σ.length)) hmem
  rw [moveCost_self] at h1
  linarith

/-- **The potential-function criterion for the unlabelled Work Function Algorithm,
universe-polymorphic version.** -/
theorem solution (k : ℕ) (hk : 0 < k) (M : Type*) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (C : ℝ) (hC : 0 ≤ C) (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFnU C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M),
      workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    IsCompetitive (WFAU hk C₀) C := by
  have hC1 : (0:ℝ) < C + 1 := by linarith
  refine ⟨Φ [], fun σ => ?_⟩
  have hgrowth : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFnU C₀ (σ.take (t + 1)) X
        ≤ workFnU C₀ (σ.take t) X + (Φ (σ.take t) - Φ (σ.take (t + 1))) := by
    intro t ht X
    have hsplit : σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
      rw [List.take_succ, List.getElem?_eq_getElem ht]
      rfl
    rw [hsplit]
    exact hUP (σ.take t) (σ[t]'ht) X
  have hmain := wfaU_growth k hk M C₀ σ
    (fun t => Φ (σ.take t) - Φ (σ.take (t + 1))) hgrowth
  have htel : (∑ t ∈ Finset.range σ.length, (Φ (σ.take t) - Φ (σ.take (t + 1))))
      = Φ (σ.take 0) - Φ (σ.take σ.length) :=
    Finset.sum_range_sub' (fun t => Φ (σ.take t)) σ.length
  have key : -Φ σ ≤ (C + 1) * offlineCost C₀ σ := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨X, hX⟩ := wf_approx k hk M C₀ σ (ε / (C + 1)) (div_pos hε hC1)
    have h1 := hOP σ X
    have h2 : workFnU C₀ σ X ≤ workFn C₀ σ X := wfU_self C₀ σ X
    have h3 : (C + 1) * workFnU C₀ σ X ≤ (C + 1) * (offlineCost C₀ σ + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left (le_trans h2 hX) (le_of_lt hC1)
    have h4 : (C + 1) * (offlineCost C₀ σ + ε / (C + 1))
        = (C + 1) * offlineCost C₀ σ + ε := by field_simp
    linarith
  have hconf : (WFAU hk C₀).conf [] = C₀ := WFAU_conf_nil hk C₀
  rw [hconf]
  simp only [htel, List.take_zero, List.take_length] at hmain
  linarith
