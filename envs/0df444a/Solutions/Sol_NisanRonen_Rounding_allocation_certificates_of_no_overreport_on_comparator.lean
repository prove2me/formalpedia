-- Prove2me | solution 1 for NisanRonen.Rounding.allocation_certificates_of_no_overreport_on_comparator
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:18:15.199795+00:00
-- url     : https://prove2.me/submissions/a7102c12-98e4-4bf9-973b-7a5f07012ebf

import Definitions.Def_NisanRonen_Rounding_CertificateCriterion
import Theorems.Thm_NisanRonen_Rounding_rounding_error_bound

open NisanRonen.Rounding

theorem solution {n k : ℕ} [NeZero n] {a b δ ε : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hstep : δ ≤ ε * a) (f : List (Fin n → ℕ) → List (Fin n))
    (t d : Fin n → Fin k → ℝ)
    (ht : ∀ i j, a ≤ t i j) (hd : ∀ i j, a ≤ d i j ∧ d i j ≤ b)
    (y : Fin k → Fin n) (hy : ∀ j, roundUp δ (d (y j) j) ≤ roundUp δ (t (y j) j)) :
    HasAllocationCertificates f δ a b t d ((1 + ε) * makespan y (corrStar y t)) := by
  classical
  intro i _
  refine ⟨d, hd, rfl, rfl, y, ?_⟩
  let t' := Function.update d i (t i)
  have hτ (j : Fin k) : roundUp δ (corrStar y t' j) ≤ roundUp δ (corrStar y t j) := by
    by_cases h : y j = i
    · simp [corrStar, h, t']
    · simpa [corrStar, h, t'] using hy j
  have hrounded : roundedMakespan δ y (corrStar y t') ≤ roundedMakespan δ y (corrStar y t) := by
    unfold roundedMakespan makespan
    apply Finset.sup'_le
    intro l hl
    refine le_trans ?_ (Finset.le_sup' _ hl)
    exact Finset.sum_le_sum (fun j _ => hτ j)
  have htrue := (rounding_error_bound ha hδ y (corrStar y t) (fun j => ht (y j) j)).2
  have hnonneg : 0 ≤ makespan y (corrStar y t) := by
    have hl : 0 ≤ load y (corrStar y t) (0 : Fin n) :=
      Finset.sum_nonneg (fun j _ => ha.le.trans (ht (y j) j))
    exact hl.trans (Finset.le_sup' _ (Finset.mem_univ _))
  exact hrounded.trans (htrue.trans (mul_le_mul_of_nonneg_right
    (add_le_add_right ((div_le_iff₀ ha).mpr hstep) 1) hnonneg))
