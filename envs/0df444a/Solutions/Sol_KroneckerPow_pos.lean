-- Prove2me | solution 1 for KroneckerPow_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:23:34.224036+00:00
-- url     : https://prove2.me/submissions/19029a7a-37a8-4ae8-9be2-7b7f57baee61

import Mathlib
import Definitions.Def_OAIQ093D001

section
-- module Solutions.OAIQ093_PR.MatrixSubsum
attribute [-instance] _root_.TangentSpace.instFiniteDimensionalCompat _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Eigenvalues of integer matrices and unipotence

That an integer matrix whose orbit grows polynomially has all eigenvalues of norm `1`, and is
therefore unipotent after passing to a power.

Root of the `Gromov.MatrixSubsum` hierarchy.
-/


open scoped Finset
open scoped Pointwise

lemma KroneckerPow_pos_oai {d: ℕ} (A: (Matrix (Fin d) (Fin d) ℤ)ˣ) (eigen_one_complex: ∀ k : Module.End.Eigenvalues ((A.val.map (Int.castRingHom ℂ ))).toLin', ‖k.val‖ = 1):
    0 < KroneckerPow A eigen_one_complex := by
  simp [KroneckerPow]
  intro k
  by_contra!
  simp at this

  simp [KroneckerPow_single] at this
  grind


open scoped Pointwise Finset
end

theorem solution : type_of% @KroneckerPow_pos_oai := @KroneckerPow_pos_oai
