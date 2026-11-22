-- Prove2me | solution 1 for MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T18:15:59.334076+00:00
-- url     : https://prove2.me/submissions/52b7e506-3d72-48f2-b501-914fe75c0175
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_MasulloRH_even_test_omitted_sum_eq_four_mul_upper_right
import Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero_for_interval_positive_test

open MasulloRH MeasureTheory Set Filter Metric
open scoped Topology ContDiff
set_option autoImplicit false

private theorem intervalTest (ψ : ℝ → ℝ)
    (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ))) :
    ∃ (g : ℝ → ℝ) (r : ℝ), 0 < r ∧ r < 1 ∧
      IsRationalTraceTest (fun t => (g t : ℂ)) ∧
      (∀ t : ℝ, 0 < t → g t⁻¹ = g t) ∧
      (∀ t : ℝ, 0 ≤ g t) ∧
      (∀ t : ℝ, 0 < g t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r) ∧
      (∀ t ∈ tsupport (fun t => (ψ t : ℂ)), (t - 1) ^ 2 / (1 + t ^ 2) < r) := by
  have hSupport : tsupport (fun t => (ψ t : ℂ)) = tsupport ψ :=
    tsupport_comp_eq (g := Complex.ofReal) (by simp) ψ
  have hCompact : HasCompactSupport ψ := by
    change IsCompact (tsupport ψ)
    rw [← hSupport]
    exact hψ.2.1.isCompact
  have hPosSupp : tsupport ψ ⊆ Ioi 0 := by
    rw [← hSupport]
    exact hψ.2.2.1
  -- This smooth coordinate is inversion-invariant on the positive reals.
  let u (t : ℝ) := (t - 1) ^ 2 / (1 + t ^ 2)
  have huNonneg (t : ℝ) : 0 ≤ u t := by dsimp [u]; positivity
  have huSmooth : ContDiff ℝ ∞ u := by
    dsimp only [u]
    exact (show ContDiff ℝ ∞ (fun t : ℝ => (t - 1) ^ 2) by fun_prop).div
      (show ContDiff ℝ ∞ (fun t : ℝ => 1 + t ^ 2) by fun_prop)
      (fun t => by positivity)
  have huInv (t : ℝ) (ht : 0 < t) : u t⁻¹ = u t := by
    have hd : 1 + t ^ 2 ≠ 0 := by positivity
    dsimp [u]
    field_simp [ht.ne', hd]
    ring
  have huLt (t : ℝ) (ht : 0 < t) : u t < 1 := by
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith only [ht]
  let K := insert (1 : ℝ) (tsupport ψ)
  have hK : IsCompact K := hCompact.isCompact.insert 1
  have hKne : K.Nonempty := insert_nonempty _ _
  obtain ⟨q, hqK, hq⟩ := hK.exists_isMaxOn hKne huSmooth.continuous.continuousOn
  have hqPos : 0 < q := by
    rcases mem_insert_iff.mp hqK with rfl | h
    · norm_num
    · exact hPosSupp h
  let a : ℝ := max (u q) (1 / 2)
  have ha : a < 1 := max_lt (huLt q hqPos) (by norm_num)
  let bump : ContDiffBump (0 : ℝ) :=
    { rIn := a
      rOut := (a + 1) / 2
      rIn_pos := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_right _ _)
      rIn_lt_rOut := by linarith }
  let g (t : ℝ) := u t * bump (u t)
  have hgNonneg (t : ℝ) : 0 ≤ g t :=
    mul_nonneg (huNonneg t) (bump.nonneg' _)
  have hgSmooth : ContDiff ℝ ∞ g :=
    huSmooth.mul (bump.contDiff.comp huSmooth)
  have hgSupport : tsupport g ⊆ u ⁻¹' closedBall (0 : ℝ) bump.rOut := by
    apply closure_minimal _ (isClosed_closedBall.preimage huSmooth.continuous)
    intro t ht
    have hbu : u t ∈ Function.support bump := by
      intro hn
      exact ht (by simp [g, show bump (u t) = 0 from hn])
    rw [bump.support_eq] at hbu
    exact ball_subset_closedBall hbu
  let δ := 1 - bump.rOut
  have hδ : 0 < δ := by dsimp [δ, bump]; linarith
  have hBounds {t : ℝ} (ht : t ∈ tsupport g) : δ / 2 ≤ t ∧ t ≤ 2 / δ := by
    have hu : u t ≤ bump.rOut := by
      simpa only [mem_preimage, mem_closedBall_zero_iff, Real.norm_eq_abs,
        abs_of_nonneg (huNonneg t)] using hgSupport ht
    have hq := (div_le_iff₀ (by positivity : 0 < 1 + t ^ 2)).mp hu
    have hprod : δ * (1 + t ^ 2) ≤ 2 * t := by
      dsimp [δ]
      nlinarith only [hq]
    have hlo : δ / 2 ≤ t := by nlinarith only [hprod, mul_nonneg hδ.le (sq_nonneg t)]
    have htPos : 0 < t := (half_pos hδ).trans_le hlo
    have hhi : δ * t ≤ 2 := by
      apply le_of_mul_le_mul_right _ htPos
      nlinarith only [hprod, hδ]
    exact ⟨hlo, (le_div_iff₀ hδ).2 (by linarith only [hhi, mul_comm δ t])⟩
  have hgCompact : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) fun _ ht => hBounds ht
  have hgPos : tsupport g ⊆ Ioi 0 := fun _ ht => (half_pos hδ).trans_le (hBounds ht).1
  have hgCSupp : tsupport (fun t => (g t : ℂ)) = tsupport g :=
    tsupport_comp_eq (g := Complex.ofReal) (by simp) g
  have hgTest : IsRationalTraceTest (fun t => (g t : ℂ)) := by
    refine ⟨Complex.ofRealCLM.contDiff.comp hgSmooth, ?_, ?_, by simp [g, u]⟩
    · change IsCompact (tsupport (fun t => (g t : ℂ)))
      rw [hgCSupp]
      exact hgCompact.isCompact
    · rw [hgCSupp]
      exact hgPos
  refine ⟨g, bump.rOut, bump.rOut_pos, (sub_pos.mp hδ), hgTest,
    fun t ht => by simp only [g, huInv t ht], hgNonneg, ?_, ?_⟩
  · intro t
    have huPos : 0 < u t ↔ t ≠ 1 := by
      dsimp [u]
      rw [div_pos_iff_of_pos_right (by positivity)]
      constructor
      · rintro h rfl
        norm_num at h
      · intro ht
        exact sq_pos_of_ne_zero (sub_ne_zero.mpr ht)
    have hBumpPos : 0 < bump (u t) ↔ u t < bump.rOut := by
      have he : bump (u t) ≠ 0 ↔ u t < bump.rOut := by
        change u t ∈ Function.support bump ↔ _
        rw [bump.support_eq, mem_ball_zero_iff, Real.norm_eq_abs, abs_of_nonneg (huNonneg t)]
      exact ⟨fun h => he.mp h.ne', fun h =>
        lt_of_le_of_ne (bump.nonneg' _) (Ne.symm (he.mpr h))⟩
    change 0 < u t * bump (u t) ↔ _
    constructor
    · intro h
      have hu' : 0 < u t := lt_of_le_of_ne (huNonneg t) (Ne.symm (left_ne_zero_of_mul h.ne'))
      have hb' : 0 < bump (u t) :=
        lt_of_le_of_ne (bump.nonneg' _) (Ne.symm (right_ne_zero_of_mul h.ne'))
      exact ⟨huPos.mp hu', hBumpPos.mp hb'⟩
    · rintro ⟨ht, hb⟩
      exact mul_pos (huPos.mpr ht) (hBumpPos.mpr hb)
  · intro t ht
    have htr : t ∈ tsupport ψ := hSupport ▸ ht
    exact ((hq (mem_insert_of_mem _ htr)).trans (le_max_left _ _)).trans_lt bump.rIn_lt_rOut

private theorem testMellinConvergent {φ : ℝ → ℂ} (hφ : IsRationalTraceTest φ) (s : ℂ) :
    MellinConvergent φ s := by
  let f (t : ℝ) := (t : ℂ) ^ (s - 1) • φ t
  have hSupport : tsupport f ⊆ tsupport φ := tsupport_smul_subset_right _ _
  have hfCompact : HasCompactSupport f :=
    hφ.2.1.isCompact.of_isClosed_subset (isClosed_tsupport f) hSupport
  have hfContinuous : Continuous f := continuous_iff_continuousAt.mpr fun t => by
    by_cases ht : t ∈ tsupport φ
    · exact (Complex.continuousAt_ofReal_cpow_const t _ (.inr (hφ.2.2.1 ht).ne')).smul
        hφ.1.continuous.continuousAt
    · refine (show ContinuousAt (fun _ : ℝ => (0 : ℂ)) t from continuousAt_const).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with x hx
      simp [f, show φ x = 0 from hx]
  exact (hfContinuous.integrable_of_hasCompactSupport hfCompact).integrableOn

theorem solution
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hNonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  obtain ⟨g, r, hr, hr1, hg, hge, hgn, hgStrict, hΨSupp⟩ := intervalTest ψ hψ
  let plus (t : ℝ) := g t + ψ t
  have hp : IsRationalTraceTest (fun t => (plus t : ℂ)) := by
    change IsRationalTraceTest (fun t => ((g t + ψ t : ℝ) : ℂ))
    simp only [Complex.ofReal_add]
    refine ⟨hg.1.add hψ.1, hg.2.1.add hψ.2.1, ?_, ?_⟩
    · exact (tsupport_add _ _).trans (union_subset hg.2.2.1 hψ.2.2.1)
    · have hg1 : (g 1 : ℂ) = 0 := hg.2.2.2
      have hψ1 : (ψ 1 : ℂ) = 0 := hψ.2.2.2
      change (g 1 : ℂ) + (ψ 1 : ℂ) = 0
      rw [hg1, hψ1, add_zero]
  have hpe (t : ℝ) (ht : 0 < t) : plus t⁻¹ = plus t := by simp [plus, hge t ht, heven t ht]
  have hpn (t : ℝ) : 0 ≤ plus t := add_nonneg (hgn t) (hNonneg t)
  have hpStrict (t : ℝ) :
      0 < plus t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r := by
    refine ⟨?_, fun h => add_pos_of_pos_of_nonneg ((hgStrict t).2 h) (hNonneg t)⟩
    intro h
    by_contra hBad
    have hgZero : g t = 0 := le_antisymm (le_of_not_gt ((hgStrict t).not.mpr hBad)) (hgn t)
    have hΨZero : ψ t = 0 := by
      by_cases ht : t = 1
      · subst t
        exact Complex.ofReal_eq_zero.mp hψ.2.2.2
      · apply Complex.ofReal_eq_zero.mp
        exact image_eq_zero_of_notMem_tsupport (f := fun u : ℝ => (ψ u : ℂ))
          (fun hs => hBad ⟨ht, hΨSupp t hs⟩)
    have : plus t = 0 := by simp [plus, hgZero, hΨZero]
    linarith
  have hPlusZero := even_real_upper_right_omitted_sum_zero_for_interval_positive_test
    α hα hα2 plus hp hpe hpn r hr hr1 hpStrict hBoundary
  have hGZero := even_real_upper_right_omitted_sum_zero_for_interval_positive_test
    α hα hα2 g hg hge hgn r hr hr1 hgStrict hBoundary
  let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
  let w (f : ℝ → ℝ) (z : Z) : ℝ :=
    (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) *
      (mellin (fun t => (f t : ℂ)) ((z : ℂ) - 1 / 2)).re
  have hPlusSummable : Summable (w plus) :=
    (even_test_omitted_sum_eq_four_mul_upper_right α hα plus hp hpe).1
  have hGSummable : Summable (w g) :=
    (even_test_omitted_sum_eq_four_mul_upper_right α hα g hg hge).1
  have hDiff (z : Z) : w ψ z = w plus z - w g z := by
    let s := (z : ℂ) - 1 / 2
    have hFun : (fun t => (ψ t : ℂ)) = (fun t => (plus t : ℂ) - (g t : ℂ)) := by
      funext t
      simp [plus]
    calc
      w ψ z = (analyticOrderNatAt riemannZeta (z : ℂ) : ℝ) *
          (mellin (fun t => (plus t : ℂ) - (g t : ℂ)) s).re := by
        dsimp only [w]
        rw [hFun]
      _ = w plus z - w g z := by
        rw [(hasMellin_sub (testMellinConvergent hp s) (testMellinConvergent hg s)).2,
          Complex.sub_re]
        simp only [w, s, mul_sub]
  change ∑' z : Z, w ψ z = 0
  simp_rw [hDiff]
  rw [hPlusSummable.tsum_sub hGSummable]
  exact sub_eq_zero.mpr (hPlusZero.trans hGZero.symm)
