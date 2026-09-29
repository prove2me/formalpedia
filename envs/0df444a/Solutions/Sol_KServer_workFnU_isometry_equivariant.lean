-- Prove2me | solution 1 for KServer.workFnU_isometry_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T08:08:01.215498+00:00
-- url     : https://prove2.me/submissions/5c0247b4-1427-4f17-8f0e-b89214854efd

import Mathlib
import Definitions.Def_KServer_workfunction
import Definitions.Def_KServer_workfunctionU

open KServer

private theorem mc_map {k : ℕ} {M N : Type*} [MetricSpace M] [MetricSpace N]
    (e : M → N) (he : ∀ x y : M, dist (e x) (e y) = dist x y) (A B : Config k M) :
    moveCost (fun i => e (A i)) (fun i => e (B i)) = moveCost A B := by
  unfold moveCost
  exact Finset.sum_congr rfl fun i _ => he _ _

private theorem dist_symm_eq {M N : Type*} [MetricSpace M] [MetricSpace N]
    (e : M ≃ N) (he : ∀ x y : M, dist (e x) (e y) = dist x y) (a b : N) :
    dist (e.symm a) (e.symm b) = dist a b := by
  have h := he (e.symm a) (e.symm b)
  rw [e.apply_symm_apply, e.apply_symm_apply] at h
  exact h.symm

private theorem wf_map {k : ℕ} {M N : Type*} [MetricSpace M] [MetricSpace N]
    (e : M ≃ N) (he : ∀ x y : M, dist (e x) (e y) = dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFn (fun i => e (C₀ i)) (σ.map ⇑e) (fun i => e (X i)) = workFn C₀ σ X := by
  classical
  have hmc : ∀ A B : Config k N,
      moveCost (fun i => e.symm (A i)) (fun i => e.symm (B i)) = moveCost A B := by
    intro A B
    unfold moveCost
    exact Finset.sum_congr rfl fun i _ => dist_symm_eq e he _ _
  have hlen : (σ.map ⇑e).length = σ.length := by simp
  unfold workFn
  congr 1
  ext c
  constructor
  · -- pull an N-schedule back along e.symm
    rintro ⟨S, hS, rfl⟩
    refine ⟨fun j i => e.symm (S j i), ⟨?_, ?_⟩, ?_⟩
    · funext i
      show e.symm (S 0 i) = C₀ i
      rw [hS.1]
      exact e.symm_apply_apply (C₀ i)
    · intro j
      have hj : (j : ℕ) < (σ.map ⇑e).length := by simpa using j.2
      obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), hj⟩
      refine ⟨i, ?_⟩
      show e.symm (S ((j : ℕ) + 1) i) = σ.get j
      rw [hi]
      have hget : (σ.map ⇑e).get ⟨(j : ℕ), hj⟩ = e (σ.get j) := by
        simp [List.get_eq_getElem]
      rw [hget]
      exact e.symm_apply_apply (σ.get j)
    · show (∑ j ∈ Finset.range (σ.map ⇑e).length, moveCost (S j) (S (j + 1)))
          + moveCost (S (σ.map ⇑e).length) (fun i => e (X i))
        = (∑ j ∈ Finset.range σ.length,
            moveCost (fun i => e.symm (S j i)) (fun i => e.symm (S (j + 1) i)))
          + moveCost (fun i => e.symm (S σ.length i)) X
      have hfin : moveCost (S σ.length) (fun i => e (X i))
          = moveCost (fun i => e.symm (S σ.length i)) X := by
        have hXeq : X = fun i => e.symm (e (X i)) := by
          funext i
          rw [e.symm_apply_apply]
        calc moveCost (S σ.length) (fun i => e (X i))
            = moveCost (fun i => e.symm (S σ.length i)) (fun i => e.symm (e (X i))) :=
              (hmc (S σ.length) (fun i => e (X i))).symm
          _ = moveCost (fun i => e.symm (S σ.length i)) X := by rw [← hXeq]
      rw [hlen, Finset.sum_congr rfl fun j (_ : j ∈ Finset.range σ.length) =>
        hmc (S j) (S (j + 1)), hfin]
  · -- push an M-schedule forward along e
    rintro ⟨S, hS, rfl⟩
    refine ⟨fun j i => e (S j i), ⟨?_, ?_⟩, ?_⟩
    · funext i
      show e (S 0 i) = e (C₀ i)
      rw [hS.1]
    · intro j
      have hj : (j : ℕ) < σ.length := by simpa using j.2
      obtain ⟨i, hi⟩ := hS.2 ⟨(j : ℕ), hj⟩
      refine ⟨i, ?_⟩
      show e (S ((j : ℕ) + 1) i) = (σ.map ⇑e).get j
      rw [hi]
      simp [List.get_eq_getElem]
    · show (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1)))
          + moveCost (S σ.length) X
        = (∑ j ∈ Finset.range (σ.map ⇑e).length,
            moveCost (fun i => e (S j i)) (fun i => e (S (j + 1) i)))
          + moveCost (fun i => e (S (σ.map ⇑e).length i)) (fun i => e (X i))
      rw [hlen, Finset.sum_congr rfl fun j (_ : j ∈ Finset.range σ.length) =>
        mc_map (⇑e) he (S j) (S (j + 1)), mc_map (⇑e) he (S σ.length) X]

/-- **Isometry-equivariance of the unlabelled work function.** -/
theorem solution (k : ℕ) (M N : Type*) [MetricSpace M] [MetricSpace N]
    (e : M ≃ N) (he : ∀ x y : M, dist (e x) (e y) = dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFnU (fun i => e (C₀ i)) (σ.map ⇑e) (fun i => e (X i)) = workFnU C₀ σ X := by
  unfold workFnU
  refine iInf_congr fun π => ?_
  have hcomp : (fun i => e (X i)) ∘ ⇑π = fun i => e ((X ∘ ⇑π) i) := rfl
  rw [hcomp]
  exact wf_map e he C₀ σ (X ∘ ⇑π)
