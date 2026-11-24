-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.pm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:42.193367+00:00
-- url     : https://prove2.me/submissions/fc779db1-0dbc-4dd5-846c-03283aa3dcfb

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.BruhatInv
theorem _root_.solution (σ : Equiv.Perm ι) (i j : ι) :
    ((pm K σ : GL ι K) : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Equiv.Perm.inv_eq_iff_eq]
end GlobalTheory.CompanionTheory.BruhatInv
