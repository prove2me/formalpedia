-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:51:58.350894+00:00
-- url     : https://prove2.me/submissions/a8fb8b02-73ab-4638-9628-655583622248

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinSamePart_blkGL_of_mem

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinSamePart
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFinSamePart
theorem _root_.solution (b : ι → Fin s) (c : Fin s) {g : GL ι K} (h : g ∈ parab K b) :
    blkGL b c g⁻¹ = (leviHom b ⟨g, h⟩ c)⁻¹ := by
  rw [blkGL_of_mem b c (inv_mem h), ← Pi.inv_apply, ← map_inv]
  rfl
end GlobalTheory.CompanionTheory.TyFinSamePart
