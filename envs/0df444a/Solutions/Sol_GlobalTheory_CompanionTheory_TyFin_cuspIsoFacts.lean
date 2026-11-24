-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.cuspIsoFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:09:22.976749+00:00
-- url     : https://prove2.me/submissions/a999ef07-dc4a-43c9-aefe-2b4934c6ca69

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalIsomorphismProperties
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_glReindex
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_refl
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_glReindex_symm_apply

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
namespace GlobalTheory.CompanionTheory.TyFin
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.CuspIsoFacts := by
  intro K _ _ _ α β γ _ _ _ _ _ _ lam lam' mu nu e
  refine ⟨?_, ?_, ?_, ?_, fun g => glReindex_symm_apply e g⟩
  · rintro ⟨e, φ, h⟩
    refine ⟨e.symm, φ.symm, fun g x => φ.injective ?_⟩
    rw [φ.apply_symm_apply, h, φ.apply_symm_apply, glReindex_symm_apply]
  · rintro ⟨e₁, φ₁, h₁⟩ ⟨e₂, φ₂, h₂⟩
    refine ⟨e₁.trans e₂, φ₁.trans φ₂, fun g x => ?_⟩
    simp only [LinearEquiv.trans_apply, h₁, h₂, glReindex_glReindex]
  · rintro ⟨i⟩
    refine ⟨Equiv.refl α, FDRep.isoToLinearEquiv i, fun g x => ?_⟩
    rw [glReindex_refl]
    have := FDRep.Iso.conj_ρ i g
    rw [this]
    simp [LinearEquiv.conj_apply]
  · refine ⟨e, LinearEquiv.refl ℂ _, fun g x => ?_⟩
    change lam.ρ g x = lam.ρ ((glEquiv K e).symm (glEquiv K e g)) x
    rw [MulEquiv.symm_apply_apply]
end GlobalTheory.CompanionTheory.TyFin
