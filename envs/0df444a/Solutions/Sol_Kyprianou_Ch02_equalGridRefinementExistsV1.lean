-- Prove2me | solution 1 for Kyprianou.Ch02.equalGridRefinementExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:59:40.487138+00:00
-- url     : https://prove2.me/submissions/004c82db-49ca-4c9f-91e8-a8197bdd6c89

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (n m : ℕ) (t : Fin (m+1) → ℝ≥0) (ht : Monotone t) :
    ∃ v : Fin (m*(n+1)+1) → ℝ≥0, Monotone v ∧
      ∀ (i : Fin m) (j : Fin (n+1)),
        let k := finProdFinEquiv (i,j)
        let a := t i.castSucc
        let b := t i.succ
        v k.castSucc = a+(b-a)*(j.val : ℝ≥0)/((n+1 : ℕ) : ℝ≥0) ∧
        v k.succ = a+(b-a)*((j.val+1 : ℕ) : ℝ≥0)/((n+1 : ℕ) : ℝ≥0) := by
  let g (i : Fin m) (j : ℕ) : ℝ≥0 :=
    t i.castSucc+(t i.succ-t i.castSucc)*(j:ℝ≥0)/((n+1:ℕ):ℝ≥0)
  let E : Fin m × Fin (n+1) ≃ Fin (m*(n+1)) := finProdFinEquiv
  let v : Fin (m*(n+1)+1) → ℝ≥0 :=
    Fin.lastCases (t (Fin.last m)) (fun k => g (E.symm k).1 (E.symm k).2.val)
  have hl (i : Fin m) (j : Fin (n+1)) :
      v (E (i,j)).castSucc = g i j.val := by simp [v]
  have hg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hg0 (i : Fin m) : g i 0 = t i.castSucc := by simp [g]
  have hgn (i : Fin m) : g i (n+1) = t i.succ := by
    dsimp [g]
    rw [mul_div_cancel_right₀ _ (by positivity), add_tsub_cancel_of_le (hg i)]
  have hr (i : Fin m) (j : Fin (n+1)) :
      v (E (i,j)).succ = g i (j.val+1) := by
    by_cases hj : j.val+1 < n+1
    · let j' : Fin (n+1) := ⟨j.val+1,hj⟩
      have he : (E (i,j)).succ = (E (i,j')).castSucc := by
        apply Fin.ext
        change j.val+(n+1)*i.val+1 = j.val+1+(n+1)*i.val
        omega
      rw [he,hl]
    · have hje : j.val+1 = n+1 := by omega
      rw [hje,hgn]
      by_cases hi : Nat.succ i.val < m
      · let i' : Fin m := ⟨i.val+1,hi⟩
        have he : (E (i,j)).succ = (E (i',0)).castSucc := by
          apply Fin.ext
          change j.val+(n+1)*i.val+1 = 0+(n+1)*(i.val+1)
          rw [Nat.mul_succ]
          omega
        rw [he,hl]
        change g i' 0 = t i.succ
        rw [hg0]
        congr 1
      · have hie : i.val+1 = m := by omega
        have he : (E (i,j)).succ = Fin.last (m*(n+1)) := by
          apply Fin.ext
          change j.val+(n+1)*i.val+1 = m*(n+1)
          calc
            _ = (i.val+1)*(n+1) := by nlinarith
            _ = _ := congrArg (fun x : ℕ => x*(n+1)) hie
        rw [he]
        simp only [v, Fin.lastCases_last]
        congr 1
        exact Fin.ext hie.symm
  refine ⟨v, Fin.monotone_iff_le_succ.mpr ?_, fun i j => ⟨hl i j,hr i j⟩⟩
  intro k
  obtain ⟨⟨i,j⟩,rfl⟩ := E.surjective k
  rw [hl,hr]
  dsimp [g]
  gcongr
  exact_mod_cast Nat.le_succ j.val
