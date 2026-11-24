-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.cuspIso_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:29:04.54442+00:00
-- url     : https://prove2.me/submissions/0c961d6d-9a0e-4837-a47b-380999dc2958

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
theorem _root_.solution {α : Type} [Fintype α] [DecidableEq α] (lam : FDRep ℂ (GL α K)) :
    CuspIso K lam lam :=
  (GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts) K α α α lam lam lam lam
    (Equiv.refl α) |>.2.2.1 ⟨Iso.refl _⟩
end GlobalTheory.CompanionTheory.TyFin.FromMackey
