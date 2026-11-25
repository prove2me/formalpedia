-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:19:54.854385+00:00
-- url     : https://prove2.me/submissions/349fd92b-e96a-4191-b889-74534fc1da7d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_cuspIso_iff_along
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_iso_transp_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_ip_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.IpIso
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.TyFin.IpIso
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.IpCuspIso := by
  intro K _ _ _ α β _ _ _ _ lam mu e hl hm
  refine ⟨ip_char lam mu e hl hm, ?_⟩
  rw [cuspIso_iff_along lam mu e, iso_transp_iff lam mu e]
end GlobalTheory.CompanionTheory.TyFin.IpIso
