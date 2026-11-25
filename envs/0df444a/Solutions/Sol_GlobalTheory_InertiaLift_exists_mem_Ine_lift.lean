-- Prove2me | solution 1 for GlobalTheory.InertiaLift.exists_mem_Ine_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:30.220281+00:00
-- url     : https://prove2.me/submissions/278d98e8-9523-474b-984f-2472001f0433

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Theorems.Thm_GlobalTheory_InertiaLift_mem_Ine_of_integral
import Theorems.Thm_GlobalTheory_InertiaLift_exists_smul_eq
import Theorems.Thm_GlobalTheory_InertiaLift_exists_congr
import Theorems.Thm_GlobalTheory_InertiaLift_mem_Dec_of_lt
import Theorems.Thm_ReciprocityTheory_Gal_smul_valuation_lt_one_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise
open GlobalTheory GlobalTheory.InertiaLift
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace GlobalTheory.InertiaLift
theorem _root_.solution (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω]
    [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 → A.valuation ((algebraMap M Ω (τ x)) - (algebraMap M Ω x)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  have hint : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (x : M)) ≤ 1 := fun x =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom))
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := fun x => τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := exists_smul_eq (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x (hint x)
    constructor
    · intro hl
      simpa using Valuation.map_add_lt _ hx hl
    · intro hl
      simpa using Valuation.map_sub_lt _ hl hx)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = (algebraMap M Ω (τ x)) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := exists_congr (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - (algebraMap M Ω (x : M))) < 1
    rw [h₂]
    exact h x (hint x))
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, mem_Ine_of_integral (mem_Dec_of_lt fun y => ?_)
    fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)
end GlobalTheory.InertiaLift
