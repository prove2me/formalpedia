-- Prove2me | solution 1 for KServer.workFnU_quasiconvex_three
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T15:30:44.550125+00:00
-- url     : https://prove2.me/submissions/00628611-eb83-4535-a319-4f69caf53119

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex

open KServer

private theorem fin3_cases : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide

section
variable {M : Type} [MetricSpace M]

private theorem hybZ_eq (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (π : Equiv.Perm (Fin 3)) (s : Finset (Fin 3)) (T : Config 3 M)
    (τ : Equiv.Perm (Fin 3))
    (h : ∀ i : Fin 3, (if i ∈ s then X i else Y (π i)) = T (τ i)) :
    workFnU C₀ σ (fun i => if i ∈ s then X i else Y (π i)) = workFnU C₀ σ T := by
  have hfun : (fun i => if i ∈ s then X i else Y (π i)) = T ∘ (τ : Equiv.Perm (Fin 3)) :=
    funext h
  rw [hfun]
  exact workFnU_perm 3 M C₀ σ T τ

private theorem hybW_eq (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (π : Equiv.Perm (Fin 3)) (s : Finset (Fin 3)) (T : Config 3 M)
    (τ : Equiv.Perm (Fin 3))
    (h : ∀ i : Fin 3, (if i ∈ s then Y (π i) else X i) = T (τ i)) :
    workFnU C₀ σ (fun i => if i ∈ s then Y (π i) else X i) = workFnU C₀ σ T := by
  have hfun : (fun i => if i ∈ s then Y (π i) else X i) = T ∘ (τ : Equiv.Perm (Fin 3)) :=
    funext h
  rw [hfun]
  exact workFnU_perm 3 M C₀ σ T τ

/-- One branch of the case analysis: a choice of the hybrid index set `s` together with
relabellings identifying the two hybrids with the two target configurations. -/
private theorem branch (C₀ : Config 3 M) (σ : List M) (X Y : Config 3 M)
    (π : Equiv.Perm (Fin 3))
    (hπ : ∀ s : Finset (Fin 3),
      workFnU C₀ σ (fun i => if i ∈ s then X i else Y (π i))
        + workFnU C₀ σ (fun i => if i ∈ s then Y (π i) else X i)
        ≤ workFnU C₀ σ X + workFnU C₀ σ Y)
    (s : Finset (Fin 3)) (TZ TW : Config 3 M) (τZ τW : Equiv.Perm (Fin 3))
    (hZ : ∀ i : Fin 3, (if i ∈ s then X i else Y (π i)) = TZ (τZ i))
    (hW : ∀ i : Fin 3, (if i ∈ s then Y (π i) else X i) = TW (τW i)) :
    workFnU C₀ σ TZ + workFnU C₀ σ TW ≤ workFnU C₀ σ X + workFnU C₀ σ Y := by
  have h := hπ s
  rw [hybZ_eq C₀ σ X Y π s TZ τZ hZ, hybW_eq C₀ σ X Y π s TW τW hW] at h
  exact h

end

/-- **Quasiconvexity of work functions in the three-server pairwise form** (equation (3) of
Bein–Chrobak–Larmore). -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r x y u v : M) :
    min (workFnU C₀ σ ![r, x, u] + workFnU C₀ σ ![r, y, v])
        (workFnU C₀ σ ![r, x, v] + workFnU C₀ σ ![r, y, u])
      ≤ workFnU C₀ σ ![r, x, y] + workFnU C₀ σ ![r, u, v] := by
  classical
  obtain ⟨π, hπ⟩ := workFnU_quasiconvex 3 (by norm_num) M C₀ σ ![r, x, y] ![r, u, v]
  have hne : ∀ i j : Fin 3, i ≠ j → π i ≠ π j := fun i j h hc => h (π.injective hc)
  set c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 0 2 with hc3
  have e1_0 : (1 : Equiv.Perm (Fin 3)) 0 = 0 := rfl
  have e1_1 : (1 : Equiv.Perm (Fin 3)) 1 = 1 := rfl
  have e1_2 : (1 : Equiv.Perm (Fin 3)) 2 = 2 := rfl
  have a0 : (Equiv.swap (1 : Fin 3) 2) 0 = 0 := by decide
  have a1 : (Equiv.swap (1 : Fin 3) 2) 1 = 2 := by decide
  have a2 : (Equiv.swap (1 : Fin 3) 2) 2 = 1 := by decide
  have b0 : (Equiv.swap (0 : Fin 3) 2) 0 = 2 := by decide
  have b1 : (Equiv.swap (0 : Fin 3) 2) 1 = 1 := by decide
  have b2 : (Equiv.swap (0 : Fin 3) 2) 2 = 0 := by decide
  have d0 : c3 0 = 2 := by rw [hc3]; decide
  have d1 : c3 1 = 0 := by rw [hc3]; decide
  have d2 : c3 2 = 1 := by rw [hc3]; decide
  rcases fin3_cases (π 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (π 1) with h1 | h1 | h1 <;>
      rcases fin3_cases (π 2) with h2 | h2 | h2
  all_goals try (exact absurd (h0.trans h1.symm) (hne 0 1 (by decide)))
  all_goals try (exact absurd (h0.trans h2.symm) (hne 0 2 (by decide)))
  all_goals try (exact absurd (h1.trans h2.symm) (hne 1 2 (by decide)))
  -- (0,1,2)
  · refine le_trans (min_le_right _ _) (branch C₀ σ _ _ π hπ {0, 1} _ _ 1 (Equiv.swap 1 2)
      ?_ ?_) <;>
      (intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2])
  -- (0,2,1)
  · refine le_trans (min_le_left _ _) (branch C₀ σ _ _ π hπ {0, 1} _ _ 1 (Equiv.swap 1 2)
      ?_ ?_) <;>
      (intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2])
  -- (1,0,2)
  · refine le_trans (min_le_right _ _) (branch C₀ σ _ _ π hπ {0, 1} _ _ 1 c3 ?_ ?_) <;>
      (intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2])
  -- (1,2,0)
  · have hZ : ∀ i : Fin 3,
        (if i ∈ ({0, 2} : Finset (Fin 3)) then ![r, x, y] i else ![r, u, v] (π i))
          = ![r, y, v] ((Equiv.swap 1 2) i) := by
      intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2]
    have hW : ∀ i : Fin 3,
        (if i ∈ ({0, 2} : Finset (Fin 3)) then ![r, u, v] (π i) else ![r, x, y] i)
          = ![r, x, u] ((Equiv.swap 0 2) i) := by
      intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2]
    have hb := branch C₀ σ _ _ π hπ {0, 2} _ _ _ _ hZ hW
    refine le_trans (min_le_left _ _) ?_
    linarith [hb]
  -- (2,0,1)
  · refine le_trans (min_le_left _ _) (branch C₀ σ _ _ π hπ {0, 1} _ _ 1 c3 ?_ ?_) <;>
      (intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2])
  -- (2,1,0)
  · have hZ : ∀ i : Fin 3,
        (if i ∈ ({0, 2} : Finset (Fin 3)) then ![r, x, y] i else ![r, u, v] (π i))
          = ![r, y, u] ((Equiv.swap 1 2) i) := by
      intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2]
    have hW : ∀ i : Fin 3,
        (if i ∈ ({0, 2} : Finset (Fin 3)) then ![r, u, v] (π i) else ![r, x, y] i)
          = ![r, x, v] ((Equiv.swap 0 2) i) := by
      intro i; rcases fin3_cases i with rfl | rfl | rfl <;> simp [h0, h1, h2, e1_0, e1_1, e1_2, a0, a1, a2, b0, b1, b2, d0, d1, d2]
    have hb := branch C₀ σ _ _ π hπ {0, 2} _ _ _ _ hZ hW
    refine le_trans (min_le_right _ _) ?_
    linarith [hb]
