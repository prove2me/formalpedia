-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.ind_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:25.103236+00:00
-- url     : https://prove2.me/submissions/225d9d3a-9abd-4b59-91b8-6da23c37d20d

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
theorem _root_.solution (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (ind K p * A) i j = (if p i then 1 else 0) * A i j := by
  simp [ind, Matrix.diagonal_mul]
end GlobalTheory.CompanionTheory.BruhatInv
