-- Prove2me | solution 1 for GlobalTheory.exists_isLatticeEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:46:35.746897+00:00
-- url     : https://prove2.me/submissions/fbd7bf01-1c27-471f-a4a6-1d0ccf916139

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
import Theorems.Thm_GlobalTheory_IsLatticeEmb_isBaseChange
import Theorems.Thm_GlobalTheory_IsLatticeEmb_finrank_eq
import Theorems.Thm_GlobalTheory_IsLatticeEmb_extend_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IsLatticeEmb.extend_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']
namespace GlobalTheory
theorem _root_.solution [Module.Finite (𝓞 K) M] [Module.IsTorsionFree (𝓞 K) M]
    (hr : Module.finrank (𝓞 K) M = r) : ∃ φ : M →ₗ[𝓞 K] (Fin r → K), IsLatticeEmb φ := by
  have hb := TensorProduct.isBaseChange (𝓞 K) M K
  have hfin : Module.finrank K (K ⊗[𝓞 K] M) = r := by rw [hb.finrank_eq, hr]
  let e : (K ⊗[𝓞 K] M) ≃ₗ[K] (Fin r → K) := (Module.finBasisOfFinrankEq K _ hfin).equivFun
  have hloc : IsLocalizedModule (𝓞 K)⁰ (TensorProduct.mk (𝓞 K) K M 1) :=
    (isLocalizedModule_iff_isBaseChange (𝓞 K)⁰ K _).mpr hb
  refine ⟨(e.toLinearMap.restrictScalars (𝓞 K)) ∘ₗ TensorProduct.mk (𝓞 K) K M 1, ?_, ?_, ?_⟩
  · refine e.injective.comp ((injective_iff_map_eq_zero _).mpr fun x hx => ?_)
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (𝓞 K)⁰ _).mp hx
    exact (smul_eq_zero.mp hs).resolve_left (nonZeroDivisors.coe_ne_zero s)
  · rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  · rw [LinearMap.range_comp, Submodule.map_coe, LinearMap.coe_restrictScalars,
      ← Submodule.map_span]
    have : Submodule.span K (LinearMap.range (TensorProduct.mk (𝓞 K) K M 1) : Set (K ⊗[𝓞 K] M)) = ⊤ := by
      rw [eq_top_iff]
      rintro z -
      induction z using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul a x =>
        have : a ⊗ₜ[𝓞 K] x = a • (TensorProduct.mk (𝓞 K) K M 1 x) := by
          simp [TensorProduct.smul_tmul']
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
      | add u v hu hv => exact add_mem hu hv
    rw [this, Submodule.map_top, LinearEquiv.range]
end GlobalTheory
