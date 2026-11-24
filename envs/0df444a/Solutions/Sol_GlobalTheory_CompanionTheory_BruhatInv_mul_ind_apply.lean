-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.mul_ind_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:03.214329+00:00
-- url     : https://prove2.me/submissions/951b3fe4-eb49-43c7-a0b5-53b18621571f

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
    (A * ind K p) i j = A i j * (if p j then 1 else 0) := by
  simp [ind, Matrix.mul_diagonal]
end GlobalTheory.CompanionTheory.BruhatInv
