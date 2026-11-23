-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspSum.entry_of_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:07:33.185848+00:00
-- url     : https://prove2.me/submissions/7613fdfa-5adc-47a0-a548-36a79292f55c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZero

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
omit [Fintype K] [DecidableEq K] [Fintype ι]
namespace GlobalTheory.CompanionTheory.TyFin.CuspSum
theorem _root_.solution (b : ι → Fin s) {M : Matrix ι ι K}
    (h : ∀ c, Formalism.IrreducibleCountingLemmas.TYPES.blk K b c M = 1) (i j : ι) (hij : b i = b j) :
    M i j = if i = j then 1 else 0 := by
  have := congrFun (congrFun (h (b j)) ⟨i, hij⟩) ⟨j, rfl⟩
  simpa only [Formalism.IrreducibleCountingLemmas.TYPES.blk, Matrix.submatrix_apply, Matrix.one_apply,
    Subtype.mk.injEq] using this
end GlobalTheory.CompanionTheory.TyFin.CuspSum
