-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.FromMackey.sqfreeIrr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:18:29.715964+00:00
-- url     : https://prove2.me/submissions/d39fce2a-ea8d-49f3-8da5-ca643ad6d13f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MaschkeProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConsequenceOfMackey
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_FromMackey_cuspIso_refl
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
theorem _root_.solution (hMk : MackeyCusp K) : SqfreeIrr K := by
  intro n s b lam hb hl hd
  have hM : ReciprocityTheory.Ty.Fin.St.MaschkeFacts := GlobalTheory.CompanionTheory.TyFin.Maschke.maschkeFacts
  have hcard := hMk n s s b b lam lam hb hb hl hl
  haveI : Unique {π : Fin s ≃ Fin s // ∀ c, CuspIso K (lam c) (lam (π c))} :=
    { default := ⟨Equiv.refl _, fun c => cuspIso_refl K (lam c)⟩
      uniq := fun ⟨π, h⟩ => Subtype.ext (Equiv.ext fun c => (hd c (π c) (h c)).symm) }
  rw [Nat.card_unique] at hcard
  exact hM.2.2.1 (GL (Fin n) K) _ (hcRep K b lam) hcard
end GlobalTheory.CompanionTheory.TyFin.FromMackey
