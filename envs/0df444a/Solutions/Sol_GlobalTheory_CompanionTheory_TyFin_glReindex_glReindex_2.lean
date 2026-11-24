-- Prove2me | solution 2 for GlobalTheory.CompanionTheory.TyFin.glReindex_glReindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:57.459016+00:00
-- url     : https://prove2.me/submissions/06dd8a2b-2ead-4307-996a-e066bdae42d5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Theorems.Thm_ReciprocityTheory_Ty_Fin_glReindex_val


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
theorem _root_.solution (e₁ : α ≃ β) (e₂ : β ≃ γ) (g : GL α K) :
    glReindex K e₂ (glReindex K e₁ g) = glReindex K (e₁.trans e₂) g := by
  ext i j
  simp [glReindex_val]
end GlobalTheory.CompanionTheory.TyFin
