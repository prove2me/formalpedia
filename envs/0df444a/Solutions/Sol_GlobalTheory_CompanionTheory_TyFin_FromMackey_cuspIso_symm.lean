-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.cuspIso_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:25:59.014516+00:00
-- url     : https://prove2.me/submissions/c5544cfc-5ffb-4993-90c4-71a08219810e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_cuspIsoFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.FromMackey
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
namespace GlobalTheory.CompanionTheory.TyFin.FromMackey
theorem _root_.solution {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)} (h : CuspIso K lam mu) : CuspIso K mu lam := by
  obtain ⟨e, -⟩ := id h
  exact ((GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α β β lam lam mu mu e).1 h
end GlobalTheory.CompanionTheory.TyFin.FromMackey
