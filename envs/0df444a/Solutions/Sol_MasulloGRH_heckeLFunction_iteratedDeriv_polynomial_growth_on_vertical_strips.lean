-- Prove2me | solution 1 for MasulloGRH.heckeLFunction_iteratedDeriv_polynomial_growth_on_vertical_strips
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T17:39:50.394183+00:00
-- url     : https://prove2.me/submissions/683eb052-ddc4-439e-b799-97a0361af7bf

import Definitions.Def_MasulloGRH_HeckeLFunction
import Mathlib.Analysis.Complex.Liouville
import Theorems.Thm_MasulloGRH_heckeLFunction_exists_meromorphic_continuation
import Theorems.Thm_MasulloGRH_heckeLFunction_polynomial_growth_on_vertical_strips

open Filter Metric Set MasulloGRH
open scoped Topology
set_option autoImplicit false

theorem solution
    (F : Type*) [Field F] [NumberField F] (χ : HeckeCharacter F) (k : ℕ) (a b : ℝ) (hab : a < b) :
    ∃ M C T : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| →
      AnalyticAt ℂ (heckeLFunction χ) s ∧
        ‖iteratedDeriv k (heckeLFunction χ) s‖ ≤ C * |s.im| ^ M := by
  let L := heckeLFunction χ
  have hMer : MeromorphicNFOn L univ := by
    have h := heckeLFunction_exists_meromorphic_continuation F χ
    change MeromorphicNFOn (heckeLFunction χ) univ
    unfold heckeLFunction
    rw [dif_pos h]
    exact h.choose_spec.1
  obtain ⟨M, hM, C, T, hGrowth⟩ :=
    heckeLFunction_polynomial_growth_on_vertical_strips F χ (a - 2) (b + 2) (by linarith)
  let B := max C 0
  let U : Set ℂ := {z | a - 2 < z.re ∧ z.re < b + 2 ∧ max 1 T < |z.im|}
  have hOpen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt continuous_const Complex.continuous_im.abs))
  have hPoly (z : ℂ) (hz : z ∈ U) : ‖L z‖ ≤ B * |z.im| ^ M :=
    (hGrowth z hz.1.le hz.2.1.le ((le_max_right _ _).trans hz.2.2.le)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _))

  -- Local boundedness on the enlarged high strip rules out poles there.
  have hAnalytic : AnalyticOnNhd ℂ L U := by
    intro z hz
    have hNF := hMer (mem_univ z)
    apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hNeg
    have hBlow : Tendsto (fun w => ‖L w‖) (𝓝[≠] z) atTop :=
      tendsto_norm_atTop_iff_cobounded.mpr
        (tendsto_cobounded_of_meromorphicOrderAt_neg hNeg)
    let cap : ℝ := |z.im| + 1
    have hOpenCap : IsOpen {w : ℂ | |w.im| < cap} :=
      isOpen_lt Complex.continuous_im.abs continuous_const
    have hU : ∀ᶠ w in 𝓝[≠] z, w ∈ U :=
      nhdsWithin_le_nhds (hOpen.mem_nhds hz)
    have hCap : ∀ᶠ w in 𝓝[≠] z, |w.im| < cap :=
      nhdsWithin_le_nhds (hOpenCap.mem_nhds (by change |z.im| < |z.im| + 1; linarith))
    have hFalse : ∀ᶠ w in 𝓝[≠] z, False := by
      filter_upwards [hU, hCap, hBlow.eventually_gt_atTop (B * cap ^ M)]
        with w hw hwcap hLarge
      have hP := (hPoly w hw).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hwcap.le hM.le) (le_max_right _ _))
      exact (not_lt_of_ge hP) hLarge
    obtain ⟨_, hf⟩ := hFalse.exists
    exact hf

  refine ⟨M, (k.factorial : ℝ) * (B * 2 ^ M), max 1 T + 2, ?_⟩
  intro s hsA hsB hsT
  have hsOne : 1 ≤ |s.im| := by linarith [le_max_left (1 : ℝ) T]
  have hDisk (z : ℂ) (hz : z ∈ closedBall s 1) :
      z ∈ U ∧ |z.im| ≤ 2 * |s.im| := by
    have hDist : ‖z - s‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hr : |z.re - s.re| ≤ 1 := by
      simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - s)).trans hDist
    have hi : |z.im - s.im| ≤ 1 := by
      simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - s)).trans hDist
    have hUpper := (abs_sub_abs_le_abs_sub z.im s.im).trans hi
    have hLower : |s.im| - |z.im| ≤ 1 := by
      simpa only [abs_sub_comm s.im z.im] using
        (abs_sub_abs_le_abs_sub s.im z.im).trans (show |s.im - z.im| ≤ 1 by rwa [abs_sub_comm])
    change (a - 2 < z.re ∧ z.re < b + 2 ∧ max 1 T < |z.im|) ∧ _
    exact ⟨⟨by linarith [(abs_le.mp hr).1], by linarith [(abs_le.mp hr).2],
      by linarith⟩, by linarith⟩
  have hClosed : AnalyticOnNhd ℂ L (closedBall s 1) :=
    hAnalytic.mono fun z hz => (hDisk z hz).1
  refine ⟨hClosed s (mem_closedBall_self (by norm_num)), ?_⟩
  have hDiff : DiffContOnCl ℂ L (ball s 1) := by
    refine ⟨hClosed.differentiableOn.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball s (by norm_num : (1 : ℝ) ≠ 0)]
    exact hClosed.continuousOn
  have hCauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k (by norm_num) hDiff
    (C := (B * 2 ^ M) * |s.im| ^ M) fun z hz => by
      obtain ⟨hzU, hzIm⟩ := hDisk z (sphere_subset_closedBall hz)
      calc
        ‖L z‖ ≤ B * |z.im| ^ M := hPoly z hzU
        _ ≤ B * (2 * |s.im|) ^ M :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (abs_nonneg _) hzIm hM.le) (le_max_right _ _)
        _ = (B * 2 ^ M) * |s.im| ^ M := by
          rw [Real.mul_rpow (by norm_num) (abs_nonneg _), mul_assoc]
  simpa only [one_pow, div_one, mul_assoc] using hCauchy
