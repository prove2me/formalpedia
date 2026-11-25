-- Prove2me | solution 1 for GlobalTheory.DiagBlock.det_diag_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:49:09.424806+00:00
-- url     : https://prove2.me/submissions/17f39555-1c8c-44a9-b061-9621755cbc30

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.DiagBlock
namespace GlobalTheory.DiagBlock
theorem _root_.solution {A : Type} [CommRing A] {n0 n : ℕ} (hn : n0 ≤ n) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ ρ c : Fin n, n0 ≤ ρ.val → c ≠ ρ → M ρ c = 0) :
    M.det = (M.submatrix (Fin.castLE hn) (Fin.castLE hn)).det *
      ∏ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val), M ρ ρ := by
  classical
  have hblock := Matrix.twoBlockTriangular_det M (fun i : Fin n => i.val < n0) (by
    intro i hi j hj
    refine hM i j (not_lt.1 hi) ?_
    rintro rfl
    exact hi hj)
  rw [hblock]
  congr 1
  · let e : Fin n0 ≃ {i : Fin n // i.val < n0} :=
      { toFun := fun b => ⟨Fin.castLE hn b, b.isLt⟩
        invFun := fun i => ⟨i.1.val, i.2⟩
        left_inv := fun b => rfl
        right_inv := fun i => rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  · have hdiag : (Matrix.toSquareBlockProp M fun i : Fin n => ¬ i.val < n0) =
        Matrix.diagonal fun i : {i : Fin n // ¬ i.val < n0} => M i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.toSquareBlockProp, Matrix.toBlock]
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact hM i j (not_lt.1 i.2) (fun h => hij (Subtype.ext h.symm))
    rw [hdiag, Matrix.det_diagonal]
    exact (Finset.prod_subtype _ (fun ρ => by simp) (fun ρ => M ρ ρ)).symm
end GlobalTheory.DiagBlock
