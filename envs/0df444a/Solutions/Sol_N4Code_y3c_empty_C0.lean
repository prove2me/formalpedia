-- Prove2me | solution 1 for N4Code.y3c_empty_C0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:22.419901+00:00
-- url     : https://prove2.me/submissions/3a0a42ec-085d-4025-8257-ae6dc056d7da

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_C0_pair_contradiction

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) :
    ∀ y : Word n, ¬ Y3c C s' hO hP t y := by
  intro y hy
  rcases hy with ⟨hyt, hEq⟩
  have hdisj : Disjoint (colZeros s') (colOnes s') := by
    rw [Finset.disjoint_left]
    intro k hk hk'
    exact (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hk').2
  have huniv : (Finset.univ : Finset (Fin 4)) = colZeros s' ∪ colOnes s' := by
    ext k
    simp [colZeros, colOnes]
  have hmemO := Finset.min'_mem ((colZeros s').image (fun i => dRow C i y))
    (hO.image (fun i => dRow C i y))
  rcases (Finset.mem_image.mp hmemO) with ⟨i, hiO, hdi⟩
  have hmemP := Finset.min'_mem ((colOnes s').image (fun i => dRow C i y))
    (hP.image (fun i => dRow C i y))
  rcases (Finset.mem_image.mp hmemP) with ⟨j, hjP, hdj⟩
  have hEqO : dRow C i y = dOc C s' hO y := by
    simpa [dOc, dRowMin] using hdi
  have hEqP : dRow C j y = dPc C s' hP y := by
    simpa [dPc, dRowMin] using hdj
  have hEq' : dRow C i y = dRow C j y := by
    rw [hEqO, hEq, hEqP]
  have hmin : ∀ k : Fin 4, dRow C i y ≤ dRow C k y := by
    intro k
    by_cases hk : k ∈ colZeros s'
    · have hle : dOc C s' hO y ≤ dRow C k y := by
        unfold dOc
        exact Finset.min'_le ((colZeros s').image (fun i => dRow C i y)) (dRow C k y)
          (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
      rw [hEqO]
      exact hle
    · have hk' : k ∈ colOnes s' := by
        have hunion : k ∈ colZeros s' ∪ colOnes s' := by
          simpa [huniv] using (Finset.mem_univ k)
        exact (Finset.mem_union.mp hunion).resolve_left hk
      have hle : dPc C s' hP y ≤ dRow C k y := by
        unfold dPc
        exact Finset.min'_le ((colOnes s').image (fun i => dRow C i y)) (dRow C k y)
          (Finset.mem_image.mpr ⟨k, hk', rfl⟩)
      rw [hEq', hEqP]
      exact hle
  have hij : i ≠ j := by
    intro h
    have : j ∈ colZeros s' := by simpa [h] using hiO
    exact (Finset.disjoint_left.mp hdisj) this hjP
  rcases C0_pair_contradiction C hC h5 h6 y with ⟨h02, h03, h12, h13, h01, h23⟩
  fin_cases i <;> fin_cases j
  · exfalso
    exact hij rfl
  · exfalso
    apply h01
    exact ⟨hEq', hmin 2, hmin 3⟩
  · exfalso
    exact h02 hEq'
  · exfalso
    exact h03 hEq'
  · exfalso
    apply h01
    refine ⟨hEq'.symm, ?_, ?_⟩
    · calc
        dRow C 0 y = dRow C 1 y := hEq'.symm
        _ ≤ dRow C 2 y := hmin 2
    · calc
        dRow C 0 y = dRow C 1 y := hEq'.symm
        _ ≤ dRow C 3 y := hmin 3
  · exfalso
    exact hij rfl
  · exfalso
    exact h12 hEq'
  · exfalso
    exact h13 hEq'
  · exfalso
    exact h02 hEq'.symm
  · exfalso
    exact h12 hEq'.symm
  · exfalso
    exact hij rfl
  · exfalso
    apply h23
    exact ⟨hEq', hmin 0, hmin 1⟩
  · exfalso
    exact h03 hEq'.symm
  · exfalso
    exact h13 hEq'.symm
  · exfalso
    apply h23
    refine ⟨hEq'.symm, ?_, ?_⟩
    · calc
        dRow C 2 y = dRow C 3 y := hEq'.symm
        _ ≤ dRow C 0 y := hmin 0
    · calc
        dRow C 2 y = dRow C 3 y := hEq'.symm
        _ ≤ dRow C 1 y := hmin 1
  · exfalso
    exact hij rfl
end N4Code
