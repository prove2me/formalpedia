-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinSamePart.blkGL_ren
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:51:59.237448+00:00
-- url     : https://prove2.me/submissions/6ddfbb76-8b0d-4254-815c-0aa046bec446

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
theorem _root_.solution {s' : ℕ} (b : ι → Fin s) (π : Fin s ≃ Fin s') (c : Fin s) {g : GL ι K}
    (h : g ∈ parab K b) (h' : g ∈ parab K (π ∘ b)) :
    blkGL (π ∘ b) (π c) g = glEquiv K (ren b π c) (leviHom b ⟨g, h⟩ c) := by
  rw [blkGL_of_mem _ _ h']
  apply Units.ext
  ext i j
  rfl
end GlobalTheory.CompanionTheory.TyFinSamePart
