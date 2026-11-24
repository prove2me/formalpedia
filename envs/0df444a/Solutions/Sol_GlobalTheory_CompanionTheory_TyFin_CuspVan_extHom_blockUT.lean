-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_blockUT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:04:07.13374+00:00
-- url     : https://prove2.me/submissions/d7b45bcb-cc6f-4c2f-8aa8-5bff14c21769

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_rankMap_lt
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_extHom_apply

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
    {w : GL {i // b i = c} K}
    (hw : IsBlockUT K (rankMap fun i : {i // b i = c} => β i.1)
      (w : Matrix {i // b i = c} {i // b i = c} K)) :
    IsBlockUT K β (extHom b c w : Matrix ι ι K) := by
  intro i j h
  rw [extHom_apply]
  split_ifs with h1 h2
  · exact hw _ _ ((rankMap_lt _ _ _).mpr h)
  · exact absurd (h2 ▸ h) (lt_irrefl _)
  · rfl
end GlobalTheory.CompanionTheory.TyFin.CuspVan
