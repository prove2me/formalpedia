-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.glReindex_glReindex
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:29:44.0575+00:00
-- url     : https://prove2.me/submissions/ab99b742-41b7-4923-b980-ccf30a90bbba

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
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


theorem solution (e₁ : α ≃ β) (e₂ : β ≃ γ) (g : GL α K) :
    glReindex K e₂ (glReindex K e₁ g) = glReindex K (e₁.trans e₂) g := by
  ext i j <;> rfl
