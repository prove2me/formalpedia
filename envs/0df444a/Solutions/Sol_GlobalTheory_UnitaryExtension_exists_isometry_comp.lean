-- Prove2me | solution 1 for GlobalTheory.UnitaryExtension.exists_isometry_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:06:15.998846+00:00
-- url     : https://prove2.me/submissions/f372f6b6-c22a-4e2e-9b8f-7320755bbecb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsUnitaryOfGramEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
open GlobalTheory GlobalTheory.UnitaryExtension
namespace GlobalTheory.UnitaryExtension
theorem _root_.solution {W V : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (a b : W →ₗ[ℂ] V)
    (h : ∀ x, ‖b x‖ = ‖a x‖) : ∃ u : V →ₗᵢ[ℂ] V, ∀ x, u (a x) = b x := by
  have hk : LinearMap.ker a ≤ LinearMap.ker b := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← norm_eq_zero, h, hx, norm_zero]
  let l : LinearMap.range a →ₗ[ℂ] V :=
    ((LinearMap.ker a).liftQ b hk) ∘ₗ (a.quotKerEquivRange.symm : LinearMap.range a →ₗ[ℂ] _)
  have hl : ∀ x, l ⟨a x, LinearMap.mem_range_self a x⟩ = b x := by
    intro x
    simp only [l, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    simp
  let L : LinearMap.range a →ₗᵢ[ℂ] V :=
    { toLinearMap := l
      norm_map' := by
        rintro ⟨y, x, rfl⟩
        rw [hl, h]; rfl }
  refine ⟨L.extend, fun x => ?_⟩
  have := L.extend_apply ⟨a x, LinearMap.mem_range_self a x⟩
  rw [← hl]
  exact this
end GlobalTheory.UnitaryExtension
