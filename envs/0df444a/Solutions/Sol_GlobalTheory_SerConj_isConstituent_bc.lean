-- Prove2me | solution 1 for GlobalTheory.SerConj.isConstituent_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:33:48.876804+00:00
-- url     : https://prove2.me/submissions/ce0a8bdf-6d5c-48af-9692-7ac12fa67644

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_GlobalTheory_SerConj_semiMap_smul
import Theorems.Thm_GlobalTheory_SerConj_semiMap_map
import Theorems.Thm_GlobalTheory_SerConj_symm_smul
import Theorems.Thm_GlobalTheory_SerConj_semiMap_injective
import Theorems.Thm_GlobalTheory_SerConj_bcEquiv_smul
import Theorems.Thm_P2M_GlobalTheory_SerConj_bcEquiv___3b5f4a7a85e0
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_map_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SerConj
theorem _root_.solution (σ : ℂ ≃+* ℂ) {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    {τ : FDRep ℂ (GL ι K)} (h : IsConstituent τ (hcRep K b lam)) :
    IsConstituent (bc σ τ) (hcRep K b fun c => bc σ (lam c)) := by
  obtain ⟨φ, hφ, hne⟩ := h
  let J := semiMap σ.toRingHom (fun c => (bcEquiv σ (lam c)).toAddMonoidHom) fun c => bcEquiv_smul σ (lam c)
  have hJ : Function.Injective J := semiMap_injective σ _ _
  let ψ : bc σ τ →ₗ[ℂ] hcSpace K b fun c => bc σ (lam c) :=
    { toFun := fun w => ⟨fun x => J ((φ ((bcEquiv σ τ).symm w)).1 x), fun p x => by
        refine (congrArg J ((φ ((bcEquiv σ τ).symm w)).2 p x)).trans ?_
        exact semiMap_map _ _ _ _ _ (fun c v => bcEquiv_ρ σ (lam c) _ v) _⟩
      map_add' := fun w w' => by
        ext x
        simp
      map_smul' := fun a w => by
        ext x
        change J ((φ ((bcEquiv σ τ).symm (a • w))).1 x) = a • J ((φ ((bcEquiv σ τ).symm w)).1 x)
        rw [symm_smul σ _ (bcEquiv_smul σ τ), map_smul]
        refine (semiMap_smul _ _ _ _ _).trans ?_
        simp [J] }
  refine ⟨ψ, fun γ => ?_, fun h0 => hne ?_⟩
  · refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
    change J ((φ ((bcEquiv σ τ).symm ((bc σ τ).ρ γ (bcEquiv σ τ v)))).1 x) =
      J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 (x * γ))
    rw [← bcEquiv_ρ, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    have := LinearMap.congr_fun (hφ γ) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    rfl
  · refine LinearMap.ext fun v => Subtype.ext (funext fun x => hJ ?_)
    have := congrFun (congrArg Subtype.val (LinearMap.congr_fun h0 (bcEquiv σ τ v))) x
    change J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 x) = 0 at this
    rw [AddEquiv.symm_apply_apply] at this
    rw [this]
    exact (map_zero J).symm
end GlobalTheory.SerConj
