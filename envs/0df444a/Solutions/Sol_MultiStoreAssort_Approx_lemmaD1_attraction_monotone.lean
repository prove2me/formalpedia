-- Prove2me | solution 1 for MultiStoreAssort.Approx.lemmaD1_attraction_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:18:59.052748+00:00
-- url     : https://prove2.me/submissions/5d42ad80-2d7f-4974-97dc-8bd462c69f51

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MultiStoreAssort_Approx_Model

set_option autoImplicit false

theorem solution {n : ℕ} (r v ε : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, 0 < ε i ∧ ε i < 1) :
    ∀ T : Finset (Fin n), ∃ S : Finset (Fin n),
      MultiStoreAssort.SMR.single r (fun i => ε i * v i) T ≤ MultiStoreAssort.SMR.single r v S := by
  classical
  intro T
  have hDpos : 0 < ∑ j ∈ T, ε j * v j + 1 := by
    have : 0 ≤ ∑ j ∈ T, ε j * v j :=
      Finset.sum_nonneg (fun j _ => (mul_pos (hε j).1 (hv j)).le)
    linarith
  set R' : ℝ := MultiStoreAssort.SMR.single r (fun i => ε i * v i) T with hR'
  have hR'def : R' = (∑ j ∈ T, r j * (ε j * v j)) / (∑ j ∈ T, ε j * v j + 1) := rfl
  have key : R' * (∑ j ∈ T, ε j * v j + 1) = ∑ j ∈ T, r j * (ε j * v j) := by
    rw [hR'def]; field_simp
  have h1 : ∑ j ∈ T, ε j * v j * (r j - R') = R' := by
    have : ∑ j ∈ T, ε j * v j * (r j - R') =
        ∑ j ∈ T, r j * (ε j * v j) - R' * ∑ j ∈ T, ε j * v j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this]; linarith
  refine ⟨T.filter (fun j => R' < r j), ?_⟩
  have h2 : ∑ j ∈ T, ε j * v j * (r j - R') ≤
      ∑ j ∈ T.filter (fun j => R' < r j), v j * (r j - R') := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j hj
    by_cases h : R' < r j
    · rw [if_pos h]
      have := (hε j).2
      have := hv j
      have hh : 0 < r j - R' := by linarith
      nlinarith [mul_pos hh (hv j), mul_pos (mul_pos hh (hv j)) (sub_pos.2 (hε j).2)]
    · rw [if_neg h]
      have : r j - R' ≤ 0 := by linarith
      have := mul_pos (hε j).1 (hv j)
      nlinarith
  have hSpos : 0 < ∑ j ∈ T.filter (fun j => R' < r j), v j + 1 := by
    have : 0 ≤ ∑ j ∈ T.filter (fun j => R' < r j), v j :=
      Finset.sum_nonneg (fun j _ => (hv j).le)
    linarith
  have h3 : ∑ j ∈ T.filter (fun j => R' < r j), v j * (r j - R') =
      ∑ j ∈ T.filter (fun j => R' < r j), r j * v j -
        R' * ∑ j ∈ T.filter (fun j => R' < r j), v j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  show R' ≤ (∑ j ∈ T.filter (fun j => R' < r j), r j * v j) /
      (∑ j ∈ T.filter (fun j => R' < r j), v j + 1)
  rw [le_div_iff₀ hSpos]
  nlinarith
