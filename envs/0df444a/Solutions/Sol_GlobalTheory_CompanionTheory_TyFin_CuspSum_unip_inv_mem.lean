-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspSum.unip_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:09:30.093148+00:00
-- url     : https://prove2.me/submissions/ec4c930e-3d48-419d-8e8c-2cef2094b6aa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_blk_unip
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspSum_entry_of_blk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspSum
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.CuspSum
theorem _root_.solution (b : ι → Fin s) {g : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) : g⁻¹ ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨inv_mem hg.1, entry_of_blk b fun c => ?_⟩
  have h := Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.2 hg.1.1
  rw [Units.inv_mul, blk_unip b c hg, mul_one] at h
  rw [← h]
  exact Matrix.submatrix_one _ Subtype.val_injective
end GlobalTheory.CompanionTheory.TyFin.CuspSum
