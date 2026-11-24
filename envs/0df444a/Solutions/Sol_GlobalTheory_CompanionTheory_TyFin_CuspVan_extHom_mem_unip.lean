-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_mem_unip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:22:09.288737+00:00
-- url     : https://prove2.me/submissions/b52e8cde-252f-49db-80bb-48ffea257048

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_rankMap_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_blockUT

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
theorem _root_.solution {s s' : ℕ} (b : ι → Fin s) (c : Fin s) (β : ι → Fin s')
    {v : GL {i // b i = c} K} (hv : v ∈ unip K (rankMap fun i : {i // b i = c} => β i.1)) :
    extHom b c v ∈ unip K β := by
  refine ⟨⟨extHom_blockUT b c β hv.1.1, ?_⟩, fun i j hij => ?_⟩
  · rw [← map_inv]
    exact extHom_blockUT b c β hv.1.2
  · rw [extHom_apply]
    by_cases h : b i = c ∧ b j = c
    · rw [dif_pos h, hv.2 _ _ ((rankMap_eq _ _ _).mpr hij)]
      simp [Subtype.ext_iff]
    · rw [dif_neg h]
end GlobalTheory.CompanionTheory.TyFin.CuspVan
