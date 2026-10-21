-- Prove2me | solution 1 for ModernOnlineLearning.FTRL.lemma_7_49
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:06:20.759531+00:00
-- url     : https://prove2.me/submissions/b020cb35-f597-4718-8b4f-f269766eadf7

import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.FTRL

private lemma growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (lam : ℝ) (hstrong : StrongConvexOn V lam ψ)
    (θ : E →L[ℝ] ℝ) (x y : E)
    (hx : IsMinimizerOn V (fun z => ψ z + θ z) x) (hy : y ∈ V) :
    lam / 2 * ‖x - y‖ ^ 2 ≤ ψ y + θ y - (ψ x + θ x) := by
  have hsegment : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (lam / 2 * ‖x - y‖ ^ 2) ≤ ψ y + θ y - (ψ x + θ x) := by
    intro t ht ht1
    have ha : 0 ≤ 1 - t := by linarith
    have hab : 1 - t + t = 1 := by ring
    have hv : (1 - t) • x + t • y ∈ V := hstrong.1 hx.1 hy ha ht.le hab
    have hm := hx.2 _ hv
    have hs := hstrong.2 hx.1 hy ha ht.le hab
    simp only [map_add, map_smul, smul_eq_mul] at hm hs
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1 - t) * (lam / 2 * ‖x - y‖ ^ 2))
      (𝓝[>] 0) (𝓝 (lam / 2 * ‖x - y‖ ^ 2)) := by
    have hcont : ContinuousAt (fun t : ℝ => (1 - t) * (lam / 2 * ‖x - y‖ ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
  exact hsegment t ht ht1

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ : E → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (hStrong : StrongConvexOn V lam ψ)
    (θ₁ θ₂ : E →L[ℝ] ℝ) (x₁ x₂ : E)
    (hx₁ : IsMinimizerOn V (fun z => ψ z + θ₁ z) x₁)
    (hx₂ : IsMinimizerOn V (fun z => ψ z + θ₂ z) x₂) :
    ‖x₁ - x₂‖ ≤ (1 / lam) * ‖θ₁ - θ₂‖ := by
  have h1 := growth V ψ lam hStrong θ₁ x₁ x₂ hx₁ hx₂.1
  have h2 := growth V ψ lam hStrong θ₂ x₂ x₁ hx₂ hx₁.1
  rw [norm_sub_rev x₂ x₁] at h2
  have hop := (θ₁ - θ₂).le_opNorm (x₂ - x₁)
  have heval : (θ₁ - θ₂) (x₂ - x₁) ≤ ‖θ₁ - θ₂‖ * ‖x₁ - x₂‖ := by
    calc
      (θ₁ - θ₂) (x₂ - x₁) ≤ ‖(θ₁ - θ₂) (x₂ - x₁)‖ := by
        simpa only [Real.norm_eq_abs] using le_abs_self ((θ₁ - θ₂) (x₂ - x₁))
      _ ≤ ‖θ₁ - θ₂‖ * ‖x₂ - x₁‖ := hop
      _ = ‖θ₁ - θ₂‖ * ‖x₁ - x₂‖ := by rw [norm_sub_rev x₂ x₁]
  simp only [ContinuousLinearMap.sub_apply, map_sub] at heval
  by_cases hz : ‖x₁ - x₂‖ = 0
  · rw [hz]; positivity
  · have hp : 0 < ‖x₁ - x₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ hlam).mpr
    nlinarith

