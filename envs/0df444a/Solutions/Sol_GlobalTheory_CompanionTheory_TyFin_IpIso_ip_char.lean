-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.ip_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:15:25.346719+00:00
-- url     : https://prove2.me/submissions/d7f08eb3-f963-4c6b-8611-5f3717af0623

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_glEquiv_symm_symm
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_cuspIso_iff_along
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_IpIso_iso_transp_symm_iff
import Theorems.Thm_P2M_PI_GreenLabelSurjWork_transp___fec5525b2b85
import Theorems.Thm_PI_GreenLabelSurjWork_transp_simple


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
theorem _root_.solution (lam : FDRep ℂ (GL α K)) (mu : FDRep ℂ (GL β K)) (e : α ≃ β)
    (hl : Simple lam) (hm : Simple mu) :
    ip Set.univ lam.character (fun x => mu.character (glEquiv K e x)) =
      (open Classical in if CuspIso K lam mu then 1 else 0) := by
  classical
  have hT : Simple (transp e.symm mu) := PI.GreenLabelSurjWork.transp_simple e.symm mu hm
  have hc : ∀ g, mu.character (glEquiv K e g) = (transp e.symm mu).character g := by
    intro g
    show _ = LinearMap.trace ℂ _ ((transp e.symm mu).ρ g)
    rw [PI.GreenLabelSurjWork.transp_ρ, glEquiv_symm_symm]
    rfl
  haveI : Invertible (Nat.card (GL α K) : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  have ho := FDRep.char_orthonormal (transp e.symm mu) lam
  have hiff : CuspIso K lam mu ↔ Nonempty (transp e.symm mu ≅ lam) := by
    rw [cuspIso_iff_along lam mu e, ← iso_transp_symm_iff lam mu e]
    exact ⟨fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ => ⟨i.symm⟩⟩
  simp only [ip, Set.ncard_univ, Set.mem_univ, if_true, hc]
  simp only [mul_comm (lam.character _)]
  rw [ho]
  simp only [hiff]
end GlobalTheory.CompanionTheory.TyFin.IpIso
