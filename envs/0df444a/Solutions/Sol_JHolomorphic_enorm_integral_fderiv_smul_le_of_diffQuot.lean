-- Prove2me | solution 1 for JHolomorphic.enorm_integral_fderiv_smul_le_of_diffQuot
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T20:48:29.280182+00:00
-- url     : https://prove2.me/submissions/8bd2e1c4-52ab-41c4-bcb9-bb239712be10

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_JHolomorphic_tendsto_integral_smul_of_bounded



namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

theorem enorm_integral_fderiv_smul_le_of_diffQuot_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ℝ) (hp : 1 < p) {c : ℂ} {r R : ℝ} (hrR : r < R) {f : ℂ → E}
    (hf : IntegrableOn f (ball c R)) (v : ℂ) (hv : ‖v‖ = 1) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hC : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) (ENNReal.ofReal p)
        (volume.restrict (ball c r)) ≤ ENNReal.ofReal C)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ ball c r) :
    ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
      ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict (ball c r)) := by
  set P := ENNReal.ofReal p
  set Q := ENNReal.ofReal (p / (p - 1))
  have hpq : (p / (p - 1)).HolderConjugate p := (Real.HolderConjugate.conjExponent hp).symm
  haveI : ENNReal.HolderTriple Q P 1 := by
    have := hpq.ennrealOfReal
    exact this
  set K := closedBall c ((r + R) / 2) with hK
  set f' := K.indicator f with hf'
  have hKR : K ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hf'i : Integrable f' := (hf.mono_set hKR).integrable_indicator measurableSet_closedBall
  have hrK : ball c r ⊆ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hφ0 : ∀ x, x ∉ ball c r → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h))
  obtain ⟨M, hM⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  set ε := min (δ / 2) ((R - r) / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  -- G h z = h⁻¹ (φ(z - h v) - φ z)
  set G : ℝ → ℂ → ℝ := fun h z => h⁻¹ * (φ (z - (h : ℂ) * v) - φ z) with hG
  have hshift : ∀ {h : ℝ}, |h| ≤ ε → ∀ z ∈ ball c r, z + (h : ℂ) * v ∈ K := by
    intro h hh z hz
    rw [hK, mem_closedBall]
    have : ‖(h : ℂ) * v‖ = |h| := by rw [norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc dist (z + (h : ℂ) * v) c ≤ dist z c + ‖(h : ℂ) * v‖ := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_right_comm]; exact norm_add_le _ _
      _ ≤ (r + R) / 2 := by
          rw [this]; have := mem_ball.1 hz
          linarith [min_le_right (δ / 2) ((R - r) / 4)]
  -- Step 1: Hölder for each admissible h
  have step1 : ∀ h : ℝ, h ≠ 0 → |h| ≤ ε →
      ‖∫ z, G h z • f' z‖ₑ ≤ ENNReal.ofReal C * eLpNorm φ Q (volume.restrict (ball c r)) := by
    intro h hh0 hhε
    set a : ℂ := (h : ℂ) * v
    have hi1 : Integrable fun w => φ (w - a) • f' w := by
      refine Integrable.mono' (hf'i.norm.const_mul Mφ)
        ((hφ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable.smul
          hf'i.aestronglyMeasurable) (Eventually.of_forall fun w => ?_)
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hMφ _) (norm_nonneg _)
    have hi0 : Integrable fun w => φ w • f' w := by
      refine Integrable.mono' (hf'i.norm.const_mul Mφ)
        (hφ.continuous.aestronglyMeasurable.smul hf'i.aestronglyMeasurable)
        (Eventually.of_forall fun w => ?_)
      rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hMφ _) (norm_nonneg _)
    have hi1' : Integrable fun z => φ z • f' (z + a) := by
      have := hi1.comp_add_right a
      simpa using this
    have htr : ∫ z, φ z • f' (z + a) = ∫ w, φ (w - a) • f' w := by
      have := integral_add_right_eq_self (μ := volume) (fun w => φ (w - a) • f' w) a
      simpa using this
    set D : ℂ → E := fun z => h⁻¹ • (f' (z + a) - f' z) with hD
    have hE : ∫ z, G h z • f' z = ∫ z, φ z • D z := by
      have e1 : ∫ z, φ z • D z = h⁻¹ • ((∫ z, φ z • f' (z + a)) - ∫ z, φ z • f' z) := by
        rw [← integral_sub hi1' hi0, ← integral_smul]
        congr 1; funext z; simp only [hD]; rw [smul_comm, smul_sub]
      have e2 : ∫ z, G h z • f' z = h⁻¹ • ((∫ w, φ (w - a) • f' w) - ∫ z, φ z • f' z) := by
        rw [← integral_sub hi1 hi0, ← integral_smul]
        congr 1; funext z; simp only [hG]; rw [mul_smul, sub_smul]
      rw [e1, e2, htr]
    rw [hE]
    have hsupp : ∀ z ∉ ball c r, φ z • D z = 0 := fun z hz => by rw [hφ0 z hz, zero_smul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    have hDm : AEStronglyMeasurable D (volume.restrict (ball c r)) := by
      refine (AEStronglyMeasurable.const_smul ?_ _).restrict
      exact (hf'i.comp_add_right a).aestronglyMeasurable.sub hf'i.aestronglyMeasurable
    have hDC : eLpNorm D P (volume.restrict (ball c r)) ≤ ENNReal.ofReal C := by
      refine le_trans (le_of_eq (eLpNorm_congr_ae ?_)) (hC h hh0 (lt_of_le_of_lt hhε hεδ))
      refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun z hz => ?_)
      simp only [hD, hf']
      rw [Set.indicator_of_mem (hshift hhε z hz), Set.indicator_of_mem (hrK hz)]
    calc ‖∫ z in ball c r, φ z • D z‖ₑ
        ≤ ∫⁻ z in ball c r, ‖φ z • D z‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (φ • D) 1 (volume.restrict (ball c r)) := by
          rw [eLpNorm_one_eq_lintegral_enorm]; rfl
      _ ≤ eLpNorm φ Q (volume.restrict (ball c r)) * eLpNorm D P (volume.restrict (ball c r)) :=
          eLpNorm_smul_le_mul_eLpNorm hDm hφ.continuous.aestronglyMeasurable
      _ ≤ eLpNorm φ Q (volume.restrict (ball c r)) * ENNReal.ofReal C := by gcongr
      _ = _ := mul_comm _ _
  -- Step 2: the limit h → 0
  set hn : ℕ → ℝ := fun n => ε / (n + 1) with hhn
  have hn0 : ∀ n, 0 < hn n := fun n => div_pos hε0 (by positivity)
  have hnε : ∀ n, |hn n| ≤ ε := by
    intro n; rw [abs_of_pos (hn0 n)]
    exact div_le_self hε0.le (by have : (0:ℝ) ≤ n := n.cast_nonneg; linarith)
  have hnlim : Tendsto hn atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hn0 n).ne'⟩
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
    rw [mul_zero] at this
    refine this.congr fun n => ?_
    simp only [hhn]; rw [mul_one_div]
  have hlim : Tendsto (fun n => ∫ z, G (hn n) z • f' z) atTop
      (𝓝 (∫ z, (-(fderiv ℝ φ z v)) • f' z)) := by
    refine tendsto_integral_smul_of_bounded (K := K) measurableSet_closedBall
      (hf'i.integrableOn) (fun n => G (hn n)) _ (fun n => ?_) ?_ (C := M) ?_ ?_
    · exact continuous_const.mul ((hφ.continuous.comp (continuous_id.sub continuous_const)).sub
        hφ.continuous)
    · refine Eventually.of_forall fun n z hz => ?_
      have hz1 : z ∉ ball c r := fun h => hz (hrK h)
      have hz2 : z - (hn n : ℂ) * v ∉ ball c r := by
        intro h
        apply hz
        have := hshift (hnε n) _ h
        simpa using this
      simp [hG, hφ0 _ hz1, hφ0 _ hz2]
    · intro n z
      have hd : ∀ x ∈ (Set.univ : Set ℂ), DifferentiableAt ℝ φ x :=
        fun x _ => (hφ.differentiable (by simp)).differentiableAt
      have := convex_univ.norm_image_sub_le_of_norm_fderiv_le hd (fun x _ => hM x)
        (Set.mem_univ z) (Set.mem_univ (z - (hn n : ℂ) * v))
      have hnv : ‖z - (hn n : ℂ) * v - z‖ = hn n := by
        rw [sub_sub_cancel_left, norm_neg, norm_mul, hv, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hn0 n)]
      rw [hnv] at this
      simp only [hG, norm_mul, norm_inv, Real.norm_eq_abs, abs_of_pos (hn0 n)]
      rw [inv_mul_le_iff₀ (hn0 n)]
      rw [Real.norm_eq_abs] at this
      linarith
    · intro z
      have hder : HasDerivAt (fun t : ℝ => φ (z - (t : ℂ) * v)) (-(fderiv ℝ φ z v)) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => z - (t : ℂ) * v) (-v) 0 := by
          have := ((hasDerivAt_id (0:ℝ)).ofReal_comp.mul_const v).const_sub z
          simpa using this
        have h2 := ((hφ.differentiable (by simp)).differentiableAt (x := z)).hasFDerivAt
        have h2' : HasFDerivAt φ (fderiv ℝ φ z) (z - ((0:ℝ) : ℂ) * v) := by simpa using h2
        exact (h2'.comp_hasDerivAt (0:ℝ) h1).congr_deriv (by simp)
      have := hder.tendsto_slope_zero.comp hnlim
      refine this.congr fun n => ?_
      simp [hG, smul_eq_mul]
  -- conclusion
  have hΛ : ∫ z, fderiv ℝ φ z v • f z = -∫ z, (-(fderiv ℝ φ z v)) • f' z := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [neg_smul, neg_neg]
    by_cases hz : z ∈ ball c r
    · simp [hf', Set.indicator_of_mem (hrK hz)]
    · have : fderiv ℝ φ z v = 0 := by
        have hz' : z ∉ tsupport φ := fun h => hz (hφU h)
        rw [image_eq_zero_of_notMem_tsupport (fun h => hz' (tsupport_fderiv_subset ℝ h))]; simp
      simp [this]
  rw [hΛ, enorm_neg]
  refine le_of_tendsto' ((continuous_enorm.tendsto _).comp hlim) fun n => ?_
  exact step1 (hn n) (hn0 n).ne' (hnε n)

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (p : ℝ) (hp : 1 < p) {c : ℂ} {r R : ℝ} (hrR : r < R) {f : ℂ → E}
    (hf : IntegrableOn f (ball c R)) (v : ℂ) (hv : ‖v‖ = 1) (δ : ℝ) (hδ : 0 < δ) (C : ℝ)
    (hC : ∀ h : ℝ, h ≠ 0 → |h| < δ →
      eLpNorm (fun z => h⁻¹ • (f (z + (h : ℂ) * v) - f z)) (ENNReal.ofReal p)
        (volume.restrict (ball c r)) ≤ ENNReal.ofReal C)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ ball c r) :
    ‖∫ z, fderiv ℝ φ z v • f z‖ₑ ≤
      ENNReal.ofReal C * eLpNorm φ (ENNReal.ofReal (p / (p - 1))) (volume.restrict (ball c r)) :=
  enorm_integral_fderiv_smul_le_of_diffQuot_aux p hp hrR hf v hv δ hδ C hC φ hφ hφc hφU
