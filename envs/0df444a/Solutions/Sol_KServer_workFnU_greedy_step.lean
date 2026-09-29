-- Prove2me | solution 1 for KServer.workFnU_greedy_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T21:50:40.072176+00:00
-- url     : https://prove2.me/submissions/6edcaa9e-c98d-4487-ba9b-7aaa7a77c98f

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_quasiconvex

open KServer

/-- **The greedy step for the work function.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M)
    (hX : ∀ Z : Config k M, workFnU C₀ σ X ≤ workFnU C₀ σ Z)
    (r : M) (Y : Config k M) (hY : ∃ j, Y j = r) :
    ∃ i : Fin k, workFnU C₀ σ (Function.update X i r) ≤ workFnU C₀ σ Y := by
  classical
  obtain ⟨j, hj⟩ := hY
  obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ X Y
  set i₀ : Fin k := π.symm j with hi₀
  have hπi : π i₀ = j := by rw [hi₀]; exact Equiv.apply_symm_apply π j
  refine ⟨i₀, ?_⟩
  have hmem : ∀ i : Fin k, i ∈ (Finset.univ.erase i₀) ↔ i ≠ i₀ := by
    intro i
    simp [Finset.mem_erase]
  have h := hπ (Finset.univ.erase i₀)
  have hA : (fun i => if i ∈ Finset.univ.erase i₀ then X i else Y (π i))
      = Function.update X i₀ r := by
    funext i
    by_cases hi : i = i₀
    · subst hi
      rw [if_neg (by simp [hmem])]
      rw [hπi, hj, Function.update_self]
    · rw [if_pos ((hmem i).mpr hi), Function.update_of_ne hi]
  rw [hA] at h
  have hge := hX (fun i => if i ∈ Finset.univ.erase i₀ then Y (π i) else X i)
  linarith
