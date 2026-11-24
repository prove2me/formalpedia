-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.one_add_I_blkM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:38:55.4918+00:00
-- url     : https://prove2.me/submissions/b997999a-ffca-44f6-abae-aa937f3d3d2e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWBlockMatrixFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
theorem _root_.solution {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) + Complex.I • blkM b u d =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 + Complex.I • b) (Complex.I • Matrix.replicateCol (Fin 1) u)
          (Complex.I • Matrix.replicateRow (Fin 1) (star u))
          (Matrix.of fun _ _ => 1 + Complex.I * (d : ℂ))) := by
  ext i j
  obtain ⟨i', rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases i' with i' | i' <;> rcases j' with j' | j'
  · simp [blkM, Matrix.one_apply]
  · have h : ¬Fin.castAdd 1 i' = Fin.natAdd n j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · have h : ¬Fin.natAdd n i' = Fin.castAdd 1 j' := by
      rw [Fin.ext_iff]; simp; omega
    simp [blkM, Matrix.one_apply, h]
  · obtain rfl := Subsingleton.elim i' j'
    simp [blkM]
end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
