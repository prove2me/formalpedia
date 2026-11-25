-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.supportUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:17:47.995592+00:00
-- url     : https://prove2.me/submissions/2cb4f77a-9d98-4a40-9e37-e37a943a30df

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Maschke_maschkeFacts


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
theorem _root_.solution (hMk : MackeyCusp K) : SupportUnique K := by
  intro n s s' b b' lam mu τ hτ hl hm
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have h := hM.2.1 (GL (Fin n) K) τ _ _ (hcRep K b lam) (hcRep K b' mu) hτ hl.2.2 hm.2.2
  rw [hMk n s s' b b' lam mu hl.1 hm.1 hl.2.1 hm.2.1] at h
  obtain ⟨⟨π, hπ⟩⟩ := (Nat.card_ne_zero.1 h).1
  exact ⟨π, hπ⟩
end GlobalTheory.CompanionTheory.TyFin.FromMackey
