-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:36.146939+00:00
-- url     : https://prove2.me/submissions/553d7e1b-24a5-4adc-90d7-3072fbbe3275

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_levi_mul

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
theorem _root_.solution {s : ℕ} (b : ι → Fin s) (c : Fin s) {g e : GL ι K} (hg : g ∈ parab K b)
    (he : e ∈ parab K b) : blkGL b c (g * e) = blkGL b c g * blkGL b c e := by
  simp only [blkGL]
  rw [dif_pos hg, dif_pos he, dif_pos (mul_mem hg he)]
  exact levi_mul b c ⟨g, hg⟩ ⟨e, he⟩
end GlobalTheory.CompanionTheory.TyFin.CuspVan
