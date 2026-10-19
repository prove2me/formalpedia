-- Prove2me | solution 1 for HarlowTASI.vonNeumann_block_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T15:21:00.912328+00:00
-- url     : https://prove2.me/submissions/97c36a0f-0774-4823-9a6b-915387a78e1f

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_fdStarAlgebra_exists_matrixUnits
import Theorems.Thm_HarlowTASI_matrixUnits_unitary_blockForm
import Theorems.Thm_HarlowTASI_centralizer_blockAlgebraLeft
import Theorems.Thm_HarlowTASI_blockAlgebraLeft_inter_right

open HarlowTASI

theorem solution {C : Type} [Fintype C] [DecidableEq C]
    (M : StarSubalgebra ℂ (Matrix C C ℂ)) :
    ∃ (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ),
      IsUnitaryMatrix U ∧ (∀ a, 0 < dr a ∧ 0 < drb a) ∧
      (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U ∧
      (StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) : Set (Matrix C C ℂ)) =
        blockAlgebraRight U ∧
      ((M ⊓ StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) :
          StarSubalgebra ℂ (Matrix C C ℂ)) : Set (Matrix C C ℂ)) = blockAlgebraCenter U := by
  obtain ⟨N, dr, e, hdr, hmul, horth, hstar, hne, hsum, hM⟩ :=
    fdStarAlgebra_exists_matrixUnits M
  obtain ⟨drb, U, hU, hdrb, hU_eq⟩ :=
    matrixUnits_unitary_blockForm dr e hmul horth hstar hne hsum
  have hL : (M : Set (Matrix C C ℂ)) = blockAlgebraLeft U := by
    rw [hM]
    ext X
    simp only [blockAlgebraLeft, Set.mem_setOf_eq, hU_eq]
  have hR : (StarSubalgebra.centralizer ℂ (M : Set (Matrix C C ℂ)) : Set (Matrix C C ℂ)) =
      blockAlgebraRight U := by
    rw [StarSubalgebra.coe_centralizer, StarMemClass.star_coe_eq, Set.union_self, hL,
      centralizer_blockAlgebraLeft U hU]
  refine ⟨N, dr, drb, U, hU, fun a => ⟨hdr a, hdrb a⟩, hL, hR, ?_⟩
  rw [StarSubalgebra.coe_inf, hR, hL, blockAlgebraLeft_inter_right U hU]
