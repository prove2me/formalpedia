-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspIff.mem_stdRadical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:03.013896+00:00
-- url     : https://prove2.me/submissions/7099eece-8782-492f-83dd-96238b9bf2ec

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish

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
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspIff
namespace GlobalTheory.CompanionTheory.TyFin.CuspIff
theorem _root_.solution {K : Type} [Field K] [Fintype K] [DecidableEq K] {d a : ℕ} {u : GL (Fin d) K} :
    u ∈ stdRadical K d a ↔ ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
      ((i : ℕ) < a ∧ a ≤ (j : ℕ)) := Iff.rfl
end GlobalTheory.CompanionTheory.TyFin.CuspIff
