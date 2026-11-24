-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.rankMap_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:44:13.429163+00:00
-- url     : https://prove2.me/submissions/727d8d4a-865f-48d3-9dd1-c6890fbbcf55

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing

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
theorem _root_.solution {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) :
    Function.Surjective (rankMap β) := by
  intro x
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (((Finset.univ.image β).orderIsoOfFin rfl) x).2
  refine ⟨i, ?_⟩
  simp only [rankMap]
  rw [OrderIso.symm_apply_eq]
  exact Subtype.ext hi
end GlobalTheory.CompanionTheory.TyFin.CuspVan
