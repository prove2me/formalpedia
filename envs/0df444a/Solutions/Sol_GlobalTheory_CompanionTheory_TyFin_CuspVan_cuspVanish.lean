-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.CuspVan.cuspVanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:50:57.439895+00:00
-- url     : https://prove2.me/submissions/8d7ee51d-8682-400a-93e5-3a9c65686c45

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_vanish

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
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.CuspVanish := by
  intro K _ _ _ ι _ _ s s' b β lam hcusp ⟨i₀, j₀, hb, hβ⟩ H F hH hF
  classical
  exact vanish b β lam hcusp (b i₀) i₀ j₀ rfl hb.symm hβ H F hH hF
end GlobalTheory.CompanionTheory.TyFin.CuspVan
