-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.cuspIso_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:27.351183+00:00
-- url     : https://prove2.me/submissions/02cc3954-80bb-4485-a1fb-8cf5a0ed2dac

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
theorem _root_.solution {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] {lam : FDRep ℂ (GL α K)} {mu : FDRep ℂ (GL β K)}
    {nu : FDRep ℂ (GL γ K)} (h : CuspIso K lam mu) (h' : CuspIso K mu nu) : CuspIso K lam nu := by
  obtain ⟨e, -⟩ := id h
  exact ((GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α β γ lam lam mu nu e).2.1 h h'
end GlobalTheory.CompanionTheory.TyFin.FromMackey
