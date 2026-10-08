-- Prove2me | solution 1 for NewMinimalStandardModel.seesawMassMatrix_rank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:58:27.562725+00:00
-- url     : https://prove2.me/submissions/fefd7e32-414a-44e3-9506-46fcf74e0396

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

set_option autoImplicit false

open NewMinimalStandardModel in
theorem e88b953c_rank (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ) :
    (seesawMassMatrix v hν M).rank ≤ 2 := by
  unfold seesawMassMatrix
  rw [← Matrix.neg_mul]
  calc _ ≤ (diracMass v hν).rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card (Fin 2) := Matrix.rank_le_card_height _
    _ = 2 := by simp

open NewMinimalStandardModel ComplexOrder in
theorem solution (v : ℝ) (hν : Matrix (Fin 2) (Fin 3) ℂ) (M : Fin 2 → ℝ)
    (hM : ∀ α, 0 < M α) :
    (seesawMassMatrix v hν M).rank ≤ 2 ∧
      ∃ i, majoranaMasses (seesawMassMatrix v hν M) i = 0 := by
  have hr := e88b953c_rank v hν M
  refine ⟨hr, ?_⟩
  set A := seesawMassMatrix v hν M
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  have h1 := hH.rank_eq_card_non_zero_eigs
  rw [Matrix.rank_conjTranspose_mul_self] at h1
  by_contra hcon
  push Not at hcon
  have hall : ∀ i, hH.eigenvalues i ≠ 0 := by
    intro i hi
    apply hcon i
    simp [majoranaMasses, hi]
  have : Fintype.card {i // hH.eigenvalues i ≠ 0} = 3 := by
    rw [Fintype.card_subtype]
    simp [hall]
  omega
