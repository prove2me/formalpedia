-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.isBlockUT_glEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:47:18.626413+00:00
-- url     : https://prove2.me/submissions/d68c71e0-b0c0-4457-bbe8-99dcae12604a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_apply

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
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    IsBlockUT K b (glEquiv K σ g : Matrix ι ι K) ↔ IsBlockUT K (b ∘ σ) (g : Matrix ι ι K) := by
  constructor
  · intro H i j hlt
    have := H (σ i) (σ j) hlt
    simpa [glEquiv_apply] using this
  · intro H i j hlt
    rw [glEquiv_apply]
    exact H _ _ (by simpa using hlt)
end GlobalTheory.CompanionTheory.TyFin.Pm
