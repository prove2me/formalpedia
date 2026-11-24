-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.rankMap_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:12.377864+00:00
-- url     : https://prove2.me/submissions/8267d4a1-dc32-480c-8106-5d97610ef791

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.TyFin.CuspVan
theorem _root_.solution {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) (i j : κ) :
    rankMap β i < rankMap β j ↔ β i < β j := by
  simp only [rankMap]
  rw [OrderIso.lt_iff_lt]
  exact Iff.rfl
end GlobalTheory.CompanionTheory.TyFin.CuspVan
