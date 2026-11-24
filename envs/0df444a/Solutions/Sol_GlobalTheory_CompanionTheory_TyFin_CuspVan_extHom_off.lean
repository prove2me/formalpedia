-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.extHom_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:47:39.025116+00:00
-- url     : https://prove2.me/submissions/d7b1195c-383a-4104-ba2c-cf2564fb31be

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
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
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (c : Fin s) (v : GL {i // b i = c} K) (i j : ι)
    (hij : b i ≠ b j) : (extHom b c v : Matrix ι ι K) i j = 0 := by
  rw [extHom_apply, dif_neg (fun h => hij (h.1.trans h.2.symm)),
    if_neg (fun e => hij (congrArg b e))]
end GlobalTheory.CompanionTheory.TyFin.CuspVan
