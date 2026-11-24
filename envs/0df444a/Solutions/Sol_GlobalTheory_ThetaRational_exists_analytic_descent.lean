-- Prove2me | solution 1 for GlobalTheory.ThetaRational.exists_analytic_descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:06.061773+00:00
-- url     : https://prove2.me/submissions/c12d8d0b-c2dd-483b-908a-250133b66679

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsIntegralAndRationalTheta
import Theorems.Thm_GlobalTheory_ThetaRational_exists_analytic_leftInverse
import Theorems.Thm_GlobalTheory_ThetaRational_exists_transl
import Theorems.Thm_GlobalTheory_ThetaRational_eventually_mem_image
import Theorems.Thm_GlobalTheory_SCV_analyticOnNhd_of_differentiable


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
namespace GlobalTheory.ThetaRational
theorem _root_.solution (hK : IsCompact K) (hθ : Differentiable ℂ θ)
    (hf : Differentiable ℂ f) (hN : ∀ z, θ z ≠ 0)
    (hP : ∀ z, ∃ k ∈ K, z - k ∈ Λ)
    (hL : ∀ l ∈ Λ, ∃ κ : V → ℂ, Continuous κ ∧ ∀ z, κ z ≠ 0 ∧ θ (z + l) = κ z • θ z ∧
      f (z + l) = κ z ^ d * f z)
    (hS : ∀ (z z' : V) (γ : ℂ), θ z = γ • θ z' → z - z' ∈ Λ)
    (hT : ∀ (z ξ : V) (γ : ℂ), fderiv ℂ θ z ξ = γ • θ z → ξ = 0)
    (e : ℂ × V) (he : e.1 • θ e.2 ≠ 0) :
    ∃ G : W → ℂ, AnalyticAt ℂ G (e.1 • θ e.2) ∧
      ∀ᶠ y in 𝓝 (e.1 • θ e.2), ∀ x : ℂ × V, x.1 • θ x.2 = y → x.1 ^ d * f x.2 = G y := by
  have ht : e.1 ≠ 0 := left_ne_zero_of_smul he
  have hΘ : Differentiable ℂ (fun x : ℂ × V => x.1 • θ x.2) := by fun_prop
  have hh : Differentiable ℂ (fun x : ℂ × V => x.1 ^ d * f x.2) := by fun_prop
  have hinj : Function.Injective (fderiv ℂ (fun x : ℂ × V => x.1 • θ x.2) e) := by
    have h1 := (hasFDerivAt_fst (𝕜 := ℂ) (p := e)).smul
      ((hθ e.2).hasFDerivAt.comp e (hasFDerivAt_snd (𝕜 := ℂ) (p := e)))
    have h2 : fderiv ℂ (fun x : ℂ × V => x.1 • θ x.2) e = _ := h1.fderiv
    rw [h2, injective_iff_map_eq_zero]
    intro v hv
    simp at hv
    have h3 : fderiv ℂ θ e.2 v.2 = (-(e.1⁻¹ * v.1)) • θ e.2 := by
      rw [neg_smul, mul_smul, ← smul_neg, ← eq_neg_of_add_eq_zero_left hv, inv_smul_smul₀ ht]
    have h4 := hT _ _ _ h3
    rw [h4] at hv
    simp [hN] at hv
    exact Prod.ext hv h4
  obtain ⟨L, hLa, hLe⟩ := exists_analytic_leftInverse hΘ hinj
  refine ⟨fun y => (L y).1 ^ d * f (L y).2, ?_, ?_⟩
  · exact AnalyticAt.comp (g := fun x : ℂ × V => x.1 ^ d * f x.2) (f := L)
      (GlobalTheory.SCV.analyticOnNhd_of_differentiable hh Set.univ _ trivial) hLa
  · filter_upwards [eventually_mem_image hK hθ.continuous hN hP hL hS he hLe,
      eventually_ne_nhds he] with y hy hy0 x hx
    obtain ⟨x', h1, h2⟩ := hy x hx
    obtain ⟨T, -, hTe, hT⟩ := exists_transl hN hL hS (e := x') (e' := x) (h2 ▸ hy0)
      (hx.trans h2.symm)
    have h3 : L y = x' := h2 ▸ h1
    rw [h3, ← (hT x).2, hTe]
end GlobalTheory.ThetaRational
