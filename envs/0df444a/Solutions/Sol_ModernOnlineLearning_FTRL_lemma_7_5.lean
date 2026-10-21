-- Prove2me | solution 1 for ModernOnlineLearning.FTRL.lemma_7_5
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T17:14:06.747178+00:00
-- url     : https://prove2.me/submissions/b346b5a6-f6e8-434f-9a2e-16dfb8ab6712

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
    (hFtClosed : IsClosedFunctionOn V (F ψ ℓ t))
    (hFtSubdiff : IsSubdifferentiableOn V (F ψ ℓ t))
    (hFtStrong : ∃ κ : ℝ, 0 < κ ∧ StrongConvexOn V κ (F ψ ℓ t))
    (hFtlClosed : IsClosedFunctionOn V (fun y => F ψ ℓ t y + ℓ t y))
    (hFtlSubdiff : IsSubdifferentiableOn V (fun y => F ψ ℓ t y + ℓ t y))
    (hFtlStrong : StrongConvexOn V lam (fun y => F ψ ℓ t y + ℓ t y)) :
    (∃! z : E, IsMinimizerOn V (F ψ ℓ t) z) ∧
    ∀ (x y : E), IsMinimizerOn V (F ψ ℓ t) x →
      IsMinimizerOn V (F ψ ℓ (t + 1)) y →
      (∃ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g) →
      ∀ g : E →L[ℝ] ℝ, IsSubgradientAt (ℓ t) x g →
      F ψ ℓ t x - F ψ ℓ (t + 1) y + ℓ t x ≤
        g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t y - ψ (t + 1) y ∧
      g (x - y) - lam / 2 * ‖x - y‖ ^ 2 + ψ t y - ψ (t + 1) y ≤
        ‖g‖ ^ 2 / (2 * lam) + ψ t y - ψ (t + 1) y := by
  constructor
  · obtain ⟨κ, hκ, hstrong⟩ := hFtStrong
    exact min_exists V (F ψ ℓ t) κ hVnonempty hκ hFtClosed hFtSubdiff hstrong
  · intro x y hx hy _ g hg
    have hsub : IsSubgradientOn V (fun z => F ψ ℓ t z + ℓ t z) x g := by
      intro z hz
      have hm := hx.2 z hz
      have hs := hg z
      dsimp only
      linarith
    have hq := strong_support V (fun z => F ψ ℓ t z + ℓ t z) lam hFtlStrong
      x y hx.1 hy.1 g hsub
    constructor
    · rw [F_succ ψ ℓ t ht y]
      simp only [map_sub] at hq ⊢
      linarith
    · have h := young_bound g (x - y) lam hlam
      linarith

