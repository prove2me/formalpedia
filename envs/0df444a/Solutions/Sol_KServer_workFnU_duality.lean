-- Prove2me | solution 1 for KServer.workFnU_duality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T08:10:23.646315+00:00
-- url     : https://prove2.me/submissions/59ab5775-bceb-480a-aaee-9a4641ef8bdb

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_workFnU_quasiconvex

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem update_comp {k : ℕ} {M : Type} (X : Config k M) (i : Fin k) (r : M)
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

private theorem wfU_rec_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (i : Fin k) :
    workFnU C₀ (σ ++ [r]) X ≤ workFnU C₀ σ (Function.update X i r) + dist r (X i) := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (Function.update X i r)
  have h1 := wfU_le C₀ (σ ++ [r]) X π
  have h2 := workFn_rec_le k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i)
  rw [← update_comp X i r π] at h2
  have h3 : (X ∘ (π : Equiv.Perm (Fin k))) (π.symm i) = X i := by simp
  rw [h3, hπ] at h2
  linarith

private theorem wfU_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFnU C₀ (σ ++ [r]) X := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) X
  obtain ⟨i', hi'⟩ := workFn_rec_ge k hk M C₀ σ r (X ∘ (π : Equiv.Perm (Fin k)))
  refine ⟨π i', ?_⟩
  have hup : Function.update (X ∘ (π : Equiv.Perm (Fin k))) i' r
      = (Function.update X (π i') r) ∘ (π : Equiv.Perm (Fin k)) := by
    rw [update_comp X (π i') r π]; simp
  rw [hup] at hi'
  have h1 := wfU_le C₀ σ (Function.update X (π i') r) π
  have h2 : (X ∘ (π : Equiv.Perm (Fin k))) i' = X (π i') := rfl
  rw [h2, hπ] at hi'
  linarith

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- **The duality property of work functions.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (A : Config k M)
    (hA : ∀ X : Config k M,
      workFnU C₀ σ A - ∑ i, dist r (A i) ≤ workFnU C₀ σ X - ∑ i, dist r (X i)) :
    (∀ X : Config k M,
        workFnU C₀ (σ ++ [r]) A - ∑ i, dist r (A i)
          ≤ workFnU C₀ (σ ++ [r]) X - ∑ i, dist r (X i)) ∧
    (∀ X : Config k M,
        workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
          ≤ workFnU C₀ (σ ++ [r]) A - workFnU C₀ σ A) := by
  classical
  -- `D` is the total distance from the request, `g` the shifted work function
  set D : Config k M → ℝ := fun V => ∑ i, dist r (V i) with hDdef
  set g : Config k M → ℝ := fun V => workFnU C₀ σ V - D V with hgdef
  have hgA : ∀ X : Config k M, g A ≤ g X := hA
  -- how `D` reacts to moving one server
  have hDupd : ∀ (V : Config k M) (m : Fin k) (u : M),
      D (Function.update V m u) = D V - dist r (V m) + dist r u := by
    intro V m u
    have h := sum_diff_single (fun i => dist r (Function.update V m u i))
      (fun i => dist r (V i)) m (fun i hi => by
        show dist r (Function.update V m u i) = dist r (V i)
        rw [Function.update_of_ne hi])
    simp only [Function.update_self] at h
    rw [hDdef]
    linarith
  have hDperm : ∀ (V : Config k M) (π : Equiv.Perm (Fin k)),
      D (V ∘ (π : Equiv.Perm (Fin k))) = D V := by
    intro V π
    rw [hDdef]
    exact Fintype.sum_equiv π (fun i => dist r (V (π i))) (fun i => dist r (V i))
      (fun i => rfl)
  -- the one-step recurrence, shifted
  have hup : ∀ (V : Config k M) (l : Fin k),
      workFnU C₀ (σ ++ [r]) V - D V ≤ g (Function.update V l r) := by
    intro V l
    have h := wfU_rec_le k hk M C₀ σ r V l
    have hd := hDupd V l r
    rw [hgdef]
    simp only []
    rw [hd]
    simp only [dist_self, add_zero]
    linarith
  have hlow : ∀ V : Config k M, ∃ l : Fin k,
      g (Function.update V l r) ≤ workFnU C₀ (σ ++ [r]) V - D V := by
    intro V
    obtain ⟨l, hl⟩ := wfU_rec_ge k hk M C₀ σ r V
    refine ⟨l, ?_⟩
    have hd := hDupd V l r
    rw [hgdef]
    simp only []
    rw [hd]
    simp only [dist_self, add_zero]
    linarith
  -- the single consequence of quasiconvexity that both halves need
  have hkey : ∀ (P Q : Config k M) (m : Fin k), Q m = r →
      ∃ l : Fin k, g (Function.update P l r) + g A ≤ g Q + g P := by
    intro P Q m hQm
    obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ Q P
    refine ⟨π m, ?_⟩
    set s : Finset (Fin k) := Finset.univ.erase m with hsdef
    have hmem : ∀ l : Fin k, (l ∈ s) ↔ l ≠ m := by
      intro l; rw [hsdef]; simp [Finset.mem_erase]
    have hZ : (fun l => if l ∈ s then Q l else P (π l))
        = Function.update Q m (P (π m)) := by
      funext l
      show (if l ∈ s then Q l else P (π l)) = Function.update Q m (P (π m)) l
      by_cases hl : l = m
      · rw [hl, if_neg (by simp [hmem]), Function.update_self]
      · rw [if_pos ((hmem l).mpr hl), Function.update_of_ne hl]
    have hW : (fun l => if l ∈ s then P (π l) else Q l)
        = (Function.update P (π m) r) ∘ (π : Equiv.Perm (Fin k)) := by
      funext l
      show (if l ∈ s then P (π l) else Q l)
        = Function.update P (π m) r (π l)
      by_cases hl : l = m
      · rw [hl, if_neg (by simp [hmem]), Function.update_self, hQm]
      · have hne : (π : Equiv.Perm (Fin k)) l ≠ π m := fun hc => hl (π.injective hc)
        rw [if_pos ((hmem l).mpr hl), Function.update_of_ne hne]
    have hq := hπ s
    rw [hZ, hW, workFnU_perm k M C₀ σ (Function.update P (π m) r) π] at hq
    have hDZ := hDupd Q m (P (π m))
    have hDW := hDupd P (π m) r
    have hgZ := hgA (Function.update Q m (P (π m)))
    rw [hgdef] at hgZ ⊢
    simp only [] at hgZ ⊢
    rw [hDZ, hDW, hQm] at *
    simp only [dist_self, sub_zero, add_zero] at *
    linarith
  constructor
  · -- `A` also minimises the new work function shifted by `D`
    intro X
    obtain ⟨l₀, hl₀⟩ := hlow X
    obtain ⟨l, hl⟩ := hkey A (Function.update X l₀ r) l₀ (Function.update_self _ _ _)
    have h1 := hup A l
    have h2 : g A ≤ g X := hgA X
    have h3 : g (Function.update X l₀ r) ≤ workFnU C₀ (σ ++ [r]) X - D X := hl₀
    simp only [hgdef, hDdef] at hl h1 h2 h3
    linarith
  · -- `A` maximises the increment
    intro X
    obtain ⟨m₀, hm₀⟩ := hlow A
    obtain ⟨l, hl⟩ := hkey X (Function.update A m₀ r) m₀ (Function.update_self _ _ _)
    have h1 := hup X l
    simp only [hgdef, hDdef] at hl h1 hm₀
    linarith
