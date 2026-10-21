-- Prove2me | solution 1 for ModernOnlineLearning.FTRL.lemma_7_7
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:14:23.311968+00:00
-- url     : https://prove2.me/submissions/3635cc17-5119-4ee0-a9a8-9fe0255bff82

import Definitions.Def_ModernOnlineLearning_FTRL_Defs
import Theorems.Thm_ModernOnlineLearning_OMD_theorem_6_9

set_option autoImplicit false
open Filter Topology
open ModernOnlineLearning.FTRL ModernOnlineLearning.OMD

private lemma strong_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : Set E) (f : E → ℝ) (lam : ℝ) (hstrong : StrongConvexOn D lam f)
    (y x : E) (hy : y ∈ D) (hx : x ∈ D) (g : E →L[ℝ] ℝ)
    (hg : IsSubgradientOn D f y g) :
    f y + g (x - y) + lam / 2 * ‖y - x‖ ^ 2 ≤ f x := by
  have hsegment : ∀ t : ℝ, 0 < t → t < 1 →
      (1 - t) * (lam / 2 * ‖y - x‖ ^ 2) ≤ f x - f y - g (x - y) := by
    intro t ht ht1
    have ha : 0 ≤ 1 - t := by linarith
    have hab : 1 - t + t = 1 := by ring
    have hv := hstrong.1 hy hx ha ht.le hab
    have hm := hg _ hv
    have hs := hstrong.2 hy hx ha ht.le hab
    simp only [map_sub, map_add, map_smul, smul_eq_mul] at hm hs ⊢
    nlinarith
  have hl : Tendsto (fun t : ℝ => (1 - t) * (lam / 2 * ‖y - x‖ ^ 2))
      (𝓝[>] 0) (𝓝 (lam / 2 * ‖y - x‖ ^ 2)) := by
    have hcont : ContinuousAt (fun t : ℝ => (1 - t) * (lam / 2 * ‖y - x‖ ^ 2)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : lam / 2 * ‖y - x‖ ^ 2 ≤ f x - f y - g (x - y) := by
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    exact hsegment t ht ht1
  linarith


private lemma min_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (V : Set E) (f : E → ℝ) (lam : ℝ)
    (hV : V.Nonempty) (hlam : 0 < lam) (hc : IsClosedFunctionOn V f)
    (hs : IsSubdifferentiableOn V f) (hstrong : StrongConvexOn V lam f) :
    ∃! x : E, IsMinimizerOn V f x := by
  obtain ⟨y, hy⟩ := hV
  obtain ⟨g, hg⟩ := hs y hy
  exact ModernOnlineLearning.OMD.theorem_6_9 V f lam hlam hc hstrong
    ⟨y, hy, g, fun z _ => hg z⟩

private lemma young_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E →L[ℝ] ℝ) (z : E) (lam : ℝ) (hlam : 0 < lam) :
    g z - lam / 2 * ‖z‖ ^ 2 ≤ ‖g‖ ^ 2 / (2 * lam) := by
  have ho : g z ≤ ‖g‖ * ‖z‖ := by
    have h := g.le_opNorm z
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  apply (le_div_iff₀ (show 0 < 2 * lam by positivity)).mpr
  nlinarith [sq_nonneg (‖g‖ - lam * ‖z‖)]

private lemma F_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ ℓ : ℕ → E → ℝ) (t : ℕ) (ht : 1 ≤ t) (z : E) :
    F ψ ℓ (t + 1) z = F ψ ℓ t z + ℓ t z + ψ (t + 1) z - ψ t z := by
  unfold F
  rw [Finset.sum_Ico_succ_top ht]
  ring

theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ ℓ : ℕ → E → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (lam : ℝ) (hlam : 0 < lam)
    (hFnextClosed : IsClosedFunctionOn V (F ψ ℓ (t + 1)))
    (hFnextSubdiff : IsSubdifferentiableOn V (F ψ ℓ (t + 1)))
    (hFnextStrong : StrongConvexOn V lam (F ψ ℓ (t + 1)))
    (x : E) (hx : IsMinimizerOn V (F ψ ℓ t) x)
    (hprox : IsMinimizerOn V (fun z => ψ (t + 1) z - ψ t z) x) :
    (∃! y : E, IsMinimizerOn V (F ψ ℓ (t + 1)) y) ∧
    ∀ y : E, IsMinimizerOn V (F ψ ℓ (t + 1)) y →
      (∃ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g) →
      ∀ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g →
      F ψ ℓ t x - F ψ ℓ (t + 1) y + ℓ t x ≤
        g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t x - ψ (t + 1) x ∧
      g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t x - ψ (t + 1) x ≤
        ‖g‖ ^ 2 / (2 * lam) + ψ t x - ψ (t + 1) x := by
  constructor
  · exact min_exists V (F ψ ℓ (t + 1)) lam hVnonempty hlam
      hFnextClosed hFnextSubdiff hFnextStrong
  · intro y hy _ g hg
    have hsub : IsSubgradientOn V (F ψ ℓ (t + 1)) x g := by
      intro z hz
      have hm := hx.2 z hz
      have hp := hprox.2 z hz
      have hs := hg z
      rw [F_succ ψ ℓ t ht x, F_succ ψ ℓ t ht z]
      dsimp only at hp
      linarith
    have hq := strong_support V (F ψ ℓ (t + 1)) lam hFnextStrong
      x y hx.1 hy.1 g hsub
    constructor
    · rw [F_succ ψ ℓ t ht x] at hq
      simp only [map_sub] at hq ⊢
      linarith
    · have h := young_bound g (x - y) lam hlam
      linarith

