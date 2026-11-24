-- Prove2me | solution 1 for HodgeComputer.CycleQ2.normalChart_integral_cofactor_witness
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T22:57:24.142904+00:00
-- url     : https://prove2.me/submissions/c6924702-c997-4efe-b23d-4e70be493f72
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_HodgeComputerCycleQ2
import Definitions.Def_HodgeComputerNormalChart
import Definitions.Def_HodgeComputerCycleQ2SparseSource
import Definitions.Def_HodgeComputerCycleQ2IntegralCofactor
import Theorems.Thm_HodgeComputer_CycleQ2_normalChart_sparse_source_witness
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2 MvPolynomial

lemma half_neg18 : (C (2⁻¹ : ℂ) * C (-18 : ℂ) : AmbientPoly 5) = C (-9 : ℂ) := by
  rw [← RingHom.map_mul]
  norm_num

lemma source_match : integralSource = sparseSource := by
  let a : AmbientPoly 5 := X 2 ^ 3 * X 3 * X 5
  let b : AmbientPoly 5 := X 0 ^ 5
  have e1 : integralSource =
      C (2⁻¹ : ℂ) * sourceMonomial * a + sourceMonomial * ((C (2⁻¹ : ℂ) * C (-18 : ℂ)) * b) := by
    unfold integralSource integralCofactor sourceMonomial a b
    ring
  have e2 : sparseSource =
      C (2⁻¹ : ℂ) * sourceMonomial * a + sourceMonomial * (C (-9 : ℂ) * b) := by
    unfold sparseSource sourceMonomial a b
    ring
  rw [e1, e2, half_neg18]

lemma residues_eq (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) :
    integralResidue S W = sparseResidue S W := by
  unfold integralResidue sparseResidue
  rw [source_match]

theorem solution :
    ∃ (S : AmbientPoly n) (W : Fin 5 → AmbientPoly n) (Q : AmbientPoly n),
      S ≠ 0 ∧ S.IsHomogeneous S.totalDegree ∧ 2 ≤ S.totalDegree ∧
      IsRelPrime F S ∧
      (∀ j, (W j).IsHomogeneous (S.totalDegree + 7)) ∧
      integralResidue S W = F ^ 2 * Q := by
  obtain ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, hchild⟩ :=
    HodgeComputer.CycleQ2.normalChart_sparse_source_witness
  refine ⟨S, W, Q, hS, hShom, hdeg, hFS, hW, ?_⟩
  exact (residues_eq S W).trans hchild
