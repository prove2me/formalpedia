-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.zIdem_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:09:18.953855+00:00
-- url     : https://prove2.me/submissions/df061dee-5ebe-4d8a-8624-3dc962aae506

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentAction
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CentralIdempotentProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_nonempty_iso_iff_equiv
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_centralIdemAct
import Theorems.Thm_GlobalTheory_T_simple_iff_irreducible
import Theorems.Thm_ReciprocityTheory_Ty_Fin_zIdem_eq_centralIdem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {Γ : Type} [Group Γ] [Fintype Γ]
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ) :
    Representation.asAlgebraHom σ.ρ (zIdem τ) = (open Classical in if Nonempty (τ ≅ σ) then 1 else 0) := by
  have h := centralIdemAct Γ τ σ τ.ρ σ.ρ ((GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 hτ) ((GlobalTheory.T.simple_iff_irreducible.1 Γ σ).1 hσ)
  rw [zIdem_eq_centralIdem, h]
  by_cases hc : Nonempty (τ ≅ σ)
  · rw [if_pos hc, if_pos ((nonempty_iso_iff_equiv τ σ).1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc ((nonempty_iso_iff_equiv τ σ).2 h'))]
end GlobalTheory.CompanionTheory.TyFin
