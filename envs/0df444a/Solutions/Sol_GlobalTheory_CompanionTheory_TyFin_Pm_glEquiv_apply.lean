-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.glEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:26.41419+00:00
-- url     : https://prove2.me/submissions/26f4b269-d4e7-4d9a-97fc-95f0b9eeaa92

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Pm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.Pm
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) (i j : κ) :
    (glEquiv K e g : Matrix κ κ K) i j = (g : Matrix ι ι K) (e.symm i) (e.symm j) := rfl
end GlobalTheory.CompanionTheory.TyFin.Pm
