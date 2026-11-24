-- Prove2me | solution 1 for GlobalTheory.ZetaPole.tendsto_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:26.679067+00:00
-- url     : https://prove2.me/submissions/8efe6295-5422-4a98-aa64-33ff491e6b6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.ZetaPole
namespace GlobalTheory.ZetaPole
theorem _root_.solution (F : Type) [Field F] [NumberField F] (C C' : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ)
    (hZ' : IsPartialZeta C' Z')
    (hfe : ∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
        (dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) :
    ∃ L : ℂ, Tendsto (fun s => (s - 1) ^ Module.finrank ℚ F * Z s) (𝓝[≠] 1) (𝓝 L) := by
  set f := Module.finrank ℚ F
  set d : ℂ := (dF F : ℂ)
  have hd0 : d ≠ 0 := by
    simp only [d, dF, ne_eq, ofReal_eq_zero, abs_eq_zero, Int.cast_eq_zero]
    exact discr_ne_zero F
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) ^ f * Z s =
      (d ^ ((1 - s) / 2) / d ^ (s / 2)) * ((Complex.Gammaℝ s)⁻¹) ^ f *
        (-((1 - s) * Complex.Gammaℝ (1 - s))) ^ f * Z' (1 - s) := by
    have hb : Metric.ball (1 : ℂ) 1 ∈ 𝓝[≠] (1 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with s hs hs1
    have hs1' : s ≠ 1 := hs1
    rw [Metric.mem_ball, dist_eq] at hs
    have hre : 0 < s.re := by
      have := abs_re_le_norm (s - 1)
      rw [sub_re, one_re] at this
      linarith [abs_le.mp (this.trans hs.le) |>.1, neg_abs_le (s.re - 1)]
    have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
    have h1 : ∀ n : ℕ, s ≠ -2 * n := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h2 : ∀ n : ℕ, 1 - s ≠ -2 * n := by
      intro n h
      have hs' : s - 1 = 2 * n := by linear_combination -h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hs1' (by simpa [sub_eq_zero] using hs')
      · rw [hs'] at hs
        have : ‖(2 * n : ℂ)‖ = 2 * n := by
          rw [show (2 * n : ℂ) = ((2 * n : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
        rw [this] at hs
        have : (1:ℝ) ≤ n := by exact_mod_cast hn
        linarith
    have e := hfe s h1 h2
    have hds : d ^ (s / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; tauto
    have hZs : Z s = d ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ f * Z' (1 - s) /
        (d ^ (s / 2) * Complex.Gammaℝ s ^ f) := by
      rw [eq_div_iff (mul_ne_zero hds (pow_ne_zero _ hΓ)), ← e]; ring
    rw [hZs, show -((1 - s) * Complex.Gammaℝ (1 - s)) = (s - 1) * Complex.Gammaℝ (1 - s) by ring, mul_pow,
      inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  refine ⟨(d ^ (((1:ℂ) - 1) / 2) / d ^ ((1:ℂ) / 2)) * ((Complex.Gammaℝ 1)⁻¹) ^ f * (-2) ^ f * Z' ((1:ℂ) - 1), ?_⟩
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hc1 : ContinuousAt (fun s : ℂ => d ^ ((1 - s) / 2) / d ^ (s / 2)) 1 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_const_cpow hd0).comp (by fun_prop)
    · exact (continuousAt_const_cpow hd0).comp (by fun_prop)
    · rw [Ne, cpow_eq_zero_iff]; tauto
  have hc2 : ContinuousAt (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹) ^ f) 1 :=
    (Complex.differentiable_Gammaℝ_inv.continuous.pow f).continuousAt
  have hZ'0 : ContinuousAt (fun s : ℂ => Z' (1 - s)) 1 := by
    have : DifferentiableAt ℂ Z' (1 - 1) := by
      refine hZ'.1.differentiableAt (isOpen_compl_singleton.mem_nhds ?_)
      simp
    exact this.continuousAt.comp (by fun_prop)
  have hres : Tendsto (fun s : ℂ => -((1 - s) * Complex.Gammaℝ (1 - s))) (𝓝[≠] 1) (𝓝 (-2)) := by
    have hm : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hs ⊢
        exact fun h => hs h.symm
    exact (Complex.Gammaℝ_residue_zero.comp hm).neg
  exact ((hc1.tendsto.mono_left nhdsWithin_le_nhds).mul (hc2.tendsto.mono_left nhdsWithin_le_nhds) |>.mul
    (hres.pow f)).mul (hZ'0.tendsto.mono_left nhdsWithin_le_nhds)
end GlobalTheory.ZetaPole
