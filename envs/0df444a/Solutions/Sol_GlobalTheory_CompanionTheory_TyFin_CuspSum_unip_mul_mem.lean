-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspSum.unip_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:47:35.601617+00:00
-- url     : https://prove2.me/submissions/4c2b28f2-a532-4f38-9de7-e1d2db023032

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
theorem _root_.solution (b : ι → Fin s) {g h : GL ι K}
    (hg : g ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) (hh : h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b) :
    g * h ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K b := by
  refine ⟨mul_mem hg.1 hh.1, entry_of_blk b fun c => ?_⟩
  rw [Units.val_mul, Formalism.IrreducibleCountingLemmas.TYPES.blk_mul b c hg.1.1 hh.1.1, blk_unip b c hg, blk_unip b c hh,
    one_mul]
end GlobalTheory.CompanionTheory.TyFin.CuspSum
