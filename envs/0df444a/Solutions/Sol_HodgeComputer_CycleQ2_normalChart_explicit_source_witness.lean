-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_explicit_source_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:37:20.031802+00:00
-- url     : https://prove2.me/submissions/78d05b3b-3db5-4206-937a-c641a26a312b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2ExplicitSource
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_sparse_source_witness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

lemma nat_coe (k : ℕ) : (k : AmbientPoly 5) = C (k : ℂ) := by
  simp

lemma coeff1 : (C ((1 / 2 : ℂ) ^ 2) * C (2 : ℂ) : AmbientPoly 5) = C (2⁻¹ : ℂ) := by
  rw [← RingHom.map_mul]
  norm_num

lemma coeff18 : (C (1 / 2 : ℂ) * C (18 : ℂ) : AmbientPoly 5) = C (9 : ℂ) := by
  rw [← RingHom.map_mul]
  norm_num

lemma coeff9 : (C (-9 : ℂ) : AmbientPoly 5) = -C (9 : ℂ) := by
  rw [← RingHom.map_neg]

lemma source_sparse : explicitSource = sparseSource := by
  let m1 : AmbientPoly 5 := X 0 * X 1 ^ 2 * X 2 ^ 6 * X 3 ^ 3 * X 4 ^ 2 * X 5 ^ 2
  let m2 : AmbientPoly 5 := X 0 ^ 6 * X 1 ^ 2 * X 2 ^ 3 * X 3 ^ 2 * X 4 ^ 2 * X 5
  have h2 : (2 : AmbientPoly 5) = C (2 : ℂ) := nat_coe 2
  have h18 : (18 : AmbientPoly 5) = C (18 : ℂ) := nat_coe 18
  have e1 : explicitSource =
      m1 * (C ((1 / 2 : ℂ) ^ 2) * C (2 : ℂ)) - m2 * (C (1 / 2 : ℂ) * C (18 : ℂ)) := by
    unfold explicitSource m1 m2
    rw [h2, h18]
    simp only [← map_pow]
    ring
  have e2 : sparseSource = m1 * C (2⁻¹ : ℂ) + m2 * C (-9 : ℂ) := by
    unfold sparseSource m1 m2
    ring
  rw [e1, e2, coeff1, coeff18, coeff9]
  ring

lemma residues_eq (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    explicitResidue S W = sparseResidue S W := by
  unfold explicitResidue sparseResidue
  rw [source_sparse]

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      explicitResidue S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_sparse_source_witness
  refine ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, ?_⟩
  exact (residues_eq S W).trans hchild
