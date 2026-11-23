-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:07:31.05502+00:00
-- url     : https://prove2.me/submissions/b06951df-d002-45eb-99fd-c0a53392e38d

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real ContDiff
open GlobalTheory GlobalTheory.ThetaRational
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {θ : V → W} {f : V → ℂ} {d : ℕ} {Λ K : Set V}
omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] [NormedSpace ℂ V]
namespace GlobalTheory.ThetaRational
theorem _root_.solution (hN : ∀ z, θ z ≠ 0)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    {e e' : ℂ × V} (he : e.1 • θ e.2 ≠ 0) (h : e'.1 • θ e'.2 = e.1 • θ e.2) :
    ∃ T : ℂ × V → ℂ × V, Continuous T ∧ T e' = e ∧ ∀ x, (T x).1 • θ (T x).2 = x.1 • θ x.2 ∧
      (T x).1 ^ d * f (T x).2 = x.1 ^ d * f x.2 := by
  have ht : e.1 ≠ 0 := left_ne_zero_of_smul he
  have h1 : θ e.2 = (e.1⁻¹ * e'.1) • θ e'.2 := by
    rw [mul_smul, h, inv_smul_smul₀ ht]
  obtain ⟨κ, hκc, hκ⟩ := hL _ (hS _ _ _ h1)
  refine ⟨fun x => (x.1 * (κ x.2)⁻¹, x.2 + (e.2 - e'.2)), ?_, ?_, fun x => ⟨?_, ?_⟩⟩
  · exact (continuous_fst.mul ((hκc.comp continuous_snd).inv₀ fun x => (hκ _).1)).prodMk
      (by fun_prop)
  · obtain ⟨h0, h2, -⟩ := hκ e'.2
    rw [add_sub_cancel, h1] at h2
    have h3 := smul_left_injective ℂ (hN e'.2) h2
    refine Prod.ext ?_ (by simp)
    have h4 : e'.1 = e.1 * κ e'.2 := by rw [← h3]; field_simp
    simp only
    rw [h4]
    field_simp
  · obtain ⟨h0, h2, -⟩ := hκ x.2
    simp only
    rw [h2, smul_smul, inv_mul_cancel_right₀ h0]
  · obtain ⟨h0, -, h2⟩ := hκ x.2
    simp only
    rw [h2, mul_pow, inv_pow, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ h0)]
end GlobalTheory.ThetaRational
