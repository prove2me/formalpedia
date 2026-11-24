-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.glReindex_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:20.169802+00:00
-- url     : https://prove2.me/submissions/0ae6f0bc-2e86-417e-aa43-3a289926540f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_glReindex
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_refl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
omit [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (e : α ≃ β) (g : GL β K) :
    glReindex K e (glReindex K e.symm g) = g := by
  rw [glReindex_glReindex, Equiv.symm_trans_self, glReindex_refl]
end GlobalTheory.CompanionTheory.TyFin
