-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.cj_pm_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:39.687984+00:00
-- url     : https://prove2.me/submissions/cc21f0c0-179f-43e1-9b6a-5a0841000837

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pm_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_mem_parab
import Theorems.Thm_ReciprocityTheory_Ty_Fin_mem_cj


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
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) :
    cj (pm K σ) (parab K b) = parab K (b ∘ σ) := by
  ext h
  rw [mem_cj, pm_conj, glEquiv_mem_parab]
end GlobalTheory.CompanionTheory.TyFin.Pm
