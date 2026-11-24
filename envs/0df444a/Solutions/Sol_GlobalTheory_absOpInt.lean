-- Prove2me | solution 1 for GlobalTheory.absOpInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:28:18.041842+00:00
-- url     : https://prove2.me/submissions/878e2918-ab26-4776-8179-aa96ce210202

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AbsOpIntIntegrable
import Theorems.Thm_GlobalTheory_absOpInt_integrable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ φ : G → ℂ, Integrable φ μ → ∃ P : Hp →L[ℂ] Hp, (∀ y, P y = ∫ g, φ g • π g y ∂μ) ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ := by
  intro G _ _ _ _ _ μ Hp _ _ _ π hn hc φ hφ
  let L : Hp →ₗ[ℂ] Hp :=
    { toFun := fun y => ∫ g, φ g • π g y ∂μ
      map_add' := fun y z => by
        simp only [map_add, smul_add]
        exact integral_add (absOpInt_integrable μ π hn hc φ hφ y)
          (absOpInt_integrable μ π hn hc φ hφ z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (φ _) c]
        exact integral_smul c _ }
  refine ⟨L.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun y => rfl, fun x y => ?_⟩
  · calc ‖L y‖ = ‖∫ g, φ g • π g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • π g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by simp_rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · change ⟪x, ∫ g, φ g • π g y ∂μ⟫_ℂ = _
    rw [← integral_inner (absOpInt_integrable μ π hn hc φ hφ y)]
    simp_rw [inner_smul_right]
end GlobalTheory
