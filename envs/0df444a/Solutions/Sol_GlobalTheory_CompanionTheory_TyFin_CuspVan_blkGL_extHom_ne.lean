-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_extHom_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:47:34.725036+00:00
-- url     : https://prove2.me/submissions/0176cfbd-9be2-40d3-a057-73b4e2fb2cd0

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
theorem _root_.solution {s : ℕ} (b : ι → Fin s) {c c' : Fin s} (hc : c' ≠ c)
    (v : GL {i // b i = c} K) (hp : extHom b c v ∈ parab K b) :
    blkGL b c' (extHom b c v) = 1 := by
  simp only [blkGL]
  rw [dif_pos hp]
  apply Units.ext
  refine Matrix.ext ?_
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  change (extHom b c v : Matrix ι ι K) i j = (1 : Matrix {i // b i = c'} {i // b i = c'} K) ⟨i, hi⟩ ⟨j, hj⟩
  rw [extHom_apply, dif_neg (fun h => hc (hi.symm.trans h.1)), Matrix.one_apply]
  simp [Subtype.ext_iff]
end GlobalTheory.CompanionTheory.TyFin.CuspVan
