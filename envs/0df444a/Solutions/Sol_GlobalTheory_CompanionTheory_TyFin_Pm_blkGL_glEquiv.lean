-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Pm.blkGL_glEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:47:37.227214+00:00
-- url     : https://prove2.me/submissions/0f38c3f1-7e7a-435d-bf72-1292255aae7c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_mem_parab

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
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (c : Fin s) (g : GL ι K)
    (e : {i // (b ∘ σ) i = c} ≃ {j // b j = c})
    (he : ∀ x, (e x : ι) = σ x) :
    blkGL b c (glEquiv K σ g) = glEquiv K e (blkGL (b ∘ σ) c g) := by
  unfold blkGL
  by_cases h : g ∈ parab K (b ∘ σ)
  · rw [dif_pos h, dif_pos ((glEquiv_mem_parab b σ g).2 h)]
    apply Units.ext
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [glEquiv_apply]
    have key : ∀ y : {j // b j = c}, ((e.symm y : {i // (b ∘ σ) i = c}) : ι) = σ.symm y := by
      intro y
      rw [Equiv.eq_symm_apply, ← he, Equiv.apply_symm_apply]
    show (glEquiv K σ g : Matrix ι ι K) i j = (g : Matrix ι ι K) _ _
    rw [glEquiv_apply]
    exact congrArg₂ (g : Matrix ι ι K) (key ⟨i, hi⟩).symm (key ⟨j, hj⟩).symm
  · rw [dif_neg h, dif_neg (fun h' => h ((glEquiv_mem_parab b σ g).1 h')), map_one]
end GlobalTheory.CompanionTheory.TyFin.Pm
