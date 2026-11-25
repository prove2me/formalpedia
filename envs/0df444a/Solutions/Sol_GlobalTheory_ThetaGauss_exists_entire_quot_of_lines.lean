-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_entire_quot_of_lines
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:51.474856+00:00
-- url     : https://prove2.me/submissions/63013d94-2f91-4d5b-aea7-787b1c9a3314

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_ThetaGauss_differentiable_transl
import Theorems.Thm_GlobalTheory_ThetaGauss_not_eventually_zero
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_sphere
import Theorems.Thm_GlobalTheory_ThetaGauss_exists_mean
import Theorems.Thm_GlobalTheory_ThetaGauss_frequently_ne_zero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution {θ N : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (hN : Differentiable ℂ N) (h0 : θ ≠ 0)
    (hl : ∀ z w : Fin g → ℂ, (∃ s : ℂ, θ (z + s • w) ≠ 0) →
      ∃ k : ℂ → ℂ, Differentiable ℂ k ∧ ∀ s, k s * θ (z + s • w) = N (z + s • w)) :
    ∃ ψ : (Fin g → ℂ) → ℂ, Differentiable ℂ ψ ∧ ∀ z, ψ z * θ z = N z := by
  obtain ⟨ℓ, hℓ⟩ := exists_mean
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  have hloc : ∀ a, ∃ Ψ : (Fin g → ℂ) → ℂ, ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ Ψ z ∧ Ψ z * θ z = N z := by
    intro a
    set w := z₀ - a with hw
    have hd : Differentiable ℂ fun s : ℂ => θ (a + s • w) := by fun_prop
    obtain ⟨r, hr, -, hsph⟩ := exists_sphere
      ((hd.analyticAt 0).eventually_eq_zero_or_eventually_ne_zero.resolve_left
        (not_eventually_zero hd ⟨1, by simpa [hw] using hz₀⟩ 0))
    let γ : C(Set.Icc (0 : ℝ) (2 * Real.pi), Fin g → ℂ) :=
      ⟨fun φ => circleMap 0 r φ • w, by fun_prop⟩
    have hunit : IsUnit (transl hθ γ a) :=
      (ContinuousMap.isUnit_iff_forall_ne_zero _).2 fun φ => hsph _ (circleMap_mem_sphere 0 hr.le φ)
    refine ⟨fun z => ℓ (transl hN γ z * Ring.inverse (transl hθ γ z)), ?_⟩
    filter_upwards [(differentiable_transl hθ γ).continuous.continuousAt.preimage_mem_nhds
      (Units.isOpen.mem_nhds hunit)] with z hz
    have hz' : IsUnit (transl hθ γ z) := hz
    refine ⟨ℓ.differentiableAt.comp z ((differentiable_transl hN γ z).mul
      ((differentiableAt_inverse hz').comp z (differentiable_transl hθ γ z))), ?_⟩
    have hne := (ContinuousMap.isUnit_iff_forall_ne_zero _).1 hz'
    obtain ⟨k, hk, hk'⟩ := hl z w ⟨_, hne ⟨0, le_rfl, Real.two_pi_pos.le⟩⟩
    rw [hℓ _ k r hk fun φ => ?_]
    · simpa using hk' 0
    · refine mul_right_cancel₀ (hne φ) ?_
      rw [← ContinuousMap.mul_apply, mul_assoc, Ring.inverse_mul_cancel _ hz', mul_one]
      exact (hk' _).symm
  choose Ψ hΨ using hloc
  let ψ : (Fin g → ℂ) → ℂ := fun z => limUnder (𝓝[{x | θ x ≠ 0}] z) (fun x => N x / θ x)
  have he : ∀ a, ∀ᶠ z in 𝓝 a, ψ z = Ψ a z := fun a => by
    filter_upwards [hΨ a, (hΨ a).eventually_nhds] with z h1 h2
    haveI := frequently_ne_zero hθ h0 z
    refine Tendsto.limUnder_eq ((h1.1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_)
    filter_upwards [h2.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hy hy0
    rw [← hy.2, mul_div_cancel_right₀ _ hy0]
  refine ⟨ψ, fun a => (hΨ a).self_of_nhds.1.congr_of_eventuallyEq (he a), fun a => ?_⟩
  rw [(he a).self_of_nhds, (hΨ a).self_of_nhds.2]
end GlobalTheory.ThetaGauss
