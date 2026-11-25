-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:58.488797+00:00
-- url     : https://prove2.me/submissions/b5975d55-c7f7-40b9-bffc-5375df3f9bd3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_supportUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_sqfreeIrr
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_sqfreeUnique

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
variable {K}
namespace GlobalTheory.CompanionTheory.TyFin.FromMackey
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.FromMackey :=
  fun _ _ _ _ hMk => ⟨supportUnique hMk, sqfreeIrr hMk, sqfreeUnique hMk⟩
end GlobalTheory.CompanionTheory.TyFin.FromMackey
