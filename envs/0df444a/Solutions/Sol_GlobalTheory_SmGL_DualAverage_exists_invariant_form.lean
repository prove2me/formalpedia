-- Prove2me | solution 1 for GlobalTheory.SmGL.DualAverage.exists_invariant_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:15.706341+00:00
-- url     : https://prove2.me/submissions/48c36d86-d82a-41a2-a31d-cb06250e1091

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Theorems.Thm_GlobalTheory_SmGL_DualAverage_isLocallyConstant_orbit
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
open scoped ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.DualAverage
namespace GlobalTheory.SmGL.DualAverage
theorem _root_.solution (G W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (H : Subgroup G) (hH : IsCompact (H : Set G)) (l₀ : Module.Dual ℂ W) :
    ∃ l : Module.Dual ℂ W, (∀ h ∈ H, ∀ w, l (σ h w) = l w) ∧
      ∀ w, (∀ h ∈ H, σ h w = w) → l w = l₀ w := by
  have : CompactSpace H := isCompact_iff_compactSpace.1 hH
  borelize ↥H
  let η : Measure H := Measure.haar
  have hne : ((η.real Set.univ : ℝ) : ℂ) ≠ 0 := by
    have : η.real Set.univ ≠ 0 := by
      rw [Measure.real, ENNReal.toReal_ne_zero]
      exact ⟨(isOpen_univ.measure_pos η Set.univ_nonempty).ne', measure_ne_top _ _⟩
    exact_mod_cast this
  have hint : ∀ w, Integrable (fun h : H => l₀ (σ ((h : G)⁻¹) w)) η := by
    intro w
    have hc : Continuous fun h : H => l₀ (σ ((h : G)⁻¹) w) :=
      (((isLocallyConstant_orbit hσ w).comp_continuous
        (continuous_subtype_val.inv : Continuous fun h : H => (h : G)⁻¹)).comp l₀).continuous
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let a : Module.Dual ℂ W :=
    { toFun := fun w => ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η
      map_add' := fun v w => by
        simp only [map_add]
        exact integral_add (hint v) (hint w)
      map_smul' := fun c w => by
        simp only [map_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have ha : ∀ w, a w = ∫ h : H, l₀ (σ ((h : G)⁻¹) w) ∂η := fun _ => rfl
  refine ⟨((η.real Set.univ : ℝ) : ℂ)⁻¹ • a, fun h₀ hh₀ w => ?_, fun w hw => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, ha, ha,
      ← integral_mul_left_eq_self (μ := η) (fun h : H => l₀ (σ ((h : G)⁻¹) (σ h₀ w))) ⟨h₀, hh₀⟩]
    congr 2
    funext h
    rw [← Module.End.mul_apply, ← map_mul]
    simp
  · rw [LinearMap.smul_apply, ha]
    have : (fun h : H => l₀ (σ ((h : G)⁻¹) w)) = fun _ => l₀ w :=
      funext fun h => by rw [hw _ (inv_mem h.2)]
    rw [this, integral_const, Complex.real_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
end GlobalTheory.SmGL.DualAverage
