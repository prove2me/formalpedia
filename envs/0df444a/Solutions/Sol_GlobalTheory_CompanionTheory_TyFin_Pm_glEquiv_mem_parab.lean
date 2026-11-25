-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.glEquiv_mem_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:25.964663+00:00
-- url     : https://prove2.me/submissions/d61f35fb-0def-4d1a-9a02-c1b13531dd6e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_isBlockUT_glEquiv

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
namespace GlobalTheory.CompanionTheory.TyFin.Pm
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    glEquiv K σ g ∈ parab K b ↔ g ∈ parab K (b ∘ σ) := by
  show (IsBlockUT K b _ ∧ IsBlockUT K b _) ↔ (IsBlockUT K (b ∘ σ) _ ∧ IsBlockUT K (b ∘ σ) _)
  rw [← map_inv, isBlockUT_glEquiv, isBlockUT_glEquiv]
end GlobalTheory.CompanionTheory.TyFin.Pm
