-- Prove2me | solution 1 for JHolomorphic.tendstoCInftyLocOn_of_sobolevNorm_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:00:32.508902+00:00
-- url     : https://prove2.me/submissions/963df3c7-c666-4470-a7c3-28292b5fb533

import Theorems.Thm_JHolomorphic_bounded_iteratedFDeriv_of_sobolevNorm_le
import Mathlib

namespace SobDev

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Landau-type estimate. -/
lemma landau (g : ℂ → F) (z : ℂ) {h ε0 M : ℝ} (hh : 0 < h) (hε0 : 0 ≤ ε0) (hM : 0 ≤ M)
    (hd : ∀ x ∈ closedBall z h, DifferentiableAt ℝ g x)
    (hL : ∀ x ∈ closedBall z h, ‖fderiv ℝ g x - fderiv ℝ g z‖ ≤ M * h)
    (hg : ∀ x ∈ closedBall z h, ‖g x‖ ≤ ε0) :
    ‖fderiv ℝ g z‖ ≤ 2 * ε0 / h + M * h := by
  set A := fderiv ℝ g z
  have key : ∀ y ∈ closedBall z h, ‖A (y - z)‖ ≤ 2 * ε0 + M * h * ‖y - z‖ := by
    intro y hy
    have hz : z ∈ closedBall z h := mem_closedBall_self hh.le
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun x => g x - A x) (f' := fun x => fderiv ℝ g x - A)
      (fun x hx => ((hd x hx).hasFDerivAt.sub A.hasFDerivAt).hasFDerivWithinAt)
      (fun x hx => hL x hx) (convex_closedBall z h) hz hy
    have e1 : A (y - z) = (g y - g z) - ((g y - A y) - (g z - A z)) := by
      rw [map_sub]; abel
    rw [e1]
    calc ‖(g y - g z) - ((g y - A y) - (g z - A z))‖
        ≤ ‖g y - g z‖ + ‖(g y - A y) - (g z - A z)‖ := norm_sub_le _ _
      _ ≤ (‖g y‖ + ‖g z‖) + M * h * ‖y - z‖ := add_le_add (norm_sub_le _ _) hmv
      _ ≤ 2 * ε0 + M * h * ‖y - z‖ := by linarith [hg y hy, hg z hz]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set y := z + ((h / ‖x‖ : ℝ) : ℂ) * x
  have hyz : y - z = ((h / ‖x‖ : ℝ) : ℂ) * x := by simp [y]
  have hny : ‖y - z‖ = h := by
    rw [hyz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hy : y ∈ closedBall z h := by rw [mem_closedBall, dist_eq_norm, hny]
  have k := key y hy
  rw [hny, hyz] at k
  have e2 : A (((h / ‖x‖ : ℝ) : ℂ) * x) = (h / ‖x‖) • A x := by
    rw [← map_smul]; congr 1
  rw [e2, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at k
  have : ‖A x‖ = (‖x‖ / h) * ((h / ‖x‖) * ‖A x‖) := by field_simp
  rw [this]
  calc (‖x‖ / h) * ((h / ‖x‖) * ‖A x‖) ≤ (‖x‖ / h) * (2 * ε0 + M * h * h) :=
        mul_le_mul_of_nonneg_left k (by positivity)
    _ = (2 * ε0 / h + M * h) * ‖x‖ := by field_simp

/-- `L^p` lower bound from a pointwise lower bound on a ball. -/
lemma eLpNorm_ge {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (f : ℂ → F) {z : ℂ} {ρ c : ℝ}
    (hc : 0 ≤ c) (hsub : ball z ρ ⊆ ball 0 1) (hf : ∀ x ∈ ball z ρ, c ≤ ‖f x‖) :
    ENNReal.ofReal c * volume (ball (0 : ℂ) ρ) ^ (1 / p.toReal) ≤
      eLpNorm f p (volume.restrict (ball 0 1)) := by
  have h1 : eLpNorm ((ball z ρ).indicator fun _ => c) p (volume.restrict (ball 0 1)) ≤
      eLpNorm f p (volume.restrict (ball 0 1)) := by
    refine eLpNorm_mono fun x => ?_
    by_cases hx : x ∈ ball z ρ
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hc]; exact hf x hx
    · rw [indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
  rw [eLpNorm_indicator_const measurableSet_ball hp0 hpt] at h1
  rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hsub,
    Measure.addHaar_ball_center volume z ρ, Real.enorm_eq_ofReal hc] at h1
  exact h1

variable [FiniteDimensional ℝ F]

lemma diffAt_iter (w : ℂ → F) (hw : ContDiffOn ℝ ∞ w (ball 0 1)) (m : ℕ) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1) : DifferentiableAt ℝ (iteratedFDeriv ℝ m w) x := by
  have hc : ContDiffAt ℝ ∞ w x := hw.contDiffAt (isOpen_ball.mem_nhds hx)
  have := hc.iteratedFDeriv_right (m := 1) (i := m) (by
    exact_mod_cast le_top)
  exact this.differentiableAt one_ne_zero

/-- Lipschitz estimate for `Dᵐ w` on a closed ball inside the disc. -/
lemma lip_iter (w : ℂ → F) (hw : ContDiffOn ℝ ∞ w (ball 0 1)) (m : ℕ) {z : ℂ} {h M : ℝ}
    (hsub : closedBall z h ⊆ ball 0 1)
    (hM : ∀ x ∈ closedBall z h, ‖iteratedFDeriv ℝ (m + 1) w x‖ ≤ M) {x : ℂ}
    (hx : x ∈ closedBall z h) (hz : z ∈ closedBall z h) :
    ‖iteratedFDeriv ℝ m w x - iteratedFDeriv ℝ m w z‖ ≤ M * ‖x - z‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy => diffAt_iter w hw m (hsub hy))
    (fun y hy => by rw [norm_fderiv_iteratedFDeriv]; exact hM y hy) (convex_closedBall z h) hz hx


lemma thick {K : Set ℂ} (hK : K ⊆ ball 0 1) (hKc : IsCompact K) :
    ∃ δ > 0, cthickening δ K ⊆ ball 0 1 ∧ IsCompact (cthickening δ K) := by
  obtain ⟨δ, hδ, h⟩ := hKc.exists_cthickening_subset_open isOpen_ball hK
  exact ⟨δ, hδ, h, hKc.cthickening⟩

lemma interp {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (w : ℕ → ℂ → F)
    (hw : ∀ ν, ContDiffOn ℝ ∞ (w ν) (ball 0 1))
    (hb : ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ, ∃ M,
      ∀ᶠ ν in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (w ν) z‖ ≤ M)
    (hL : Tendsto (fun ν => eLpNorm (w ν) p (volume.restrict (ball 0 1))) atTop (𝓝 0)) :
    ∀ m : ℕ, ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ ε > 0,
      ∀ᶠ ν in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (w ν) z‖ ≤ ε := by
  intro m
  induction m with
  | zero =>
    intro K hK hKc ε hε
    obtain ⟨δ, hδ, hδK, hK'c⟩ := thick hK hKc
    obtain ⟨L, hL'⟩ := hb _ hδK hK'c 1
    set L0 := max L 0
    have hL0 : 0 ≤ L0 := le_max_right _ _
    set ρ := min δ (ε / (2 * (L0 + 1)))
    have hρ : 0 < ρ := lt_min hδ (by positivity)
    set η := ENNReal.ofReal (ε / 2) * volume (ball (0 : ℂ) ρ) ^ (1 / p.toReal)
    have hη : 0 < η := by
      refine ENNReal.mul_pos (by simpa using hε) ?_
      exact (ENNReal.rpow_pos (measure_ball_pos volume 0 hρ) measure_ball_lt_top.ne).ne'
    filter_upwards [hL', hL.eventually (gt_mem_nhds hη)] with ν hbd hsmall z hz
    rw [norm_iteratedFDeriv_zero]
    by_contra hne
    push Not at hne
    have hcb : closedBall z ρ ⊆ cthickening δ K :=
      (closedBall_subset_closedBall (min_le_left _ _)).trans (closedBall_subset_cthickening hz δ)
    have hlow : ∀ x ∈ ball z ρ, ε / 2 ≤ ‖w ν x‖ := by
      intro x hx
      have hx' : x ∈ closedBall z ρ := ball_subset_closedBall hx
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := w ν) (C := L0)
        (fun y hy => ((hw ν).contDiffAt (isOpen_ball.mem_nhds (hδK (hcb hy)))).differentiableAt
          (by simp))
        (fun y hy => by
          rw [← norm_iteratedFDeriv_one]; exact (hbd y (hcb hy)).trans (le_max_left _ _))
        (convex_closedBall z ρ) (mem_closedBall_self hρ.le) hx'
      have h1 : ‖x - z‖ ≤ ρ := by rw [← dist_eq_norm]; exact (mem_ball.mp hx).le
      have h2 : L0 * ρ ≤ ε / 2 := by
        calc L0 * ρ ≤ L0 * (ε / (2 * (L0 + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hL0
          _ ≤ ε / 2 := by
            rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
      have h3 : ‖w ν z‖ ≤ ‖w ν x‖ + ‖w ν x - w ν z‖ := by
        have := norm_sub_le (w ν x) (w ν x - w ν z); simp at this; linarith [norm_sub_rev (w ν x) (w ν z)]
      nlinarith [mul_le_mul_of_nonneg_left h1 hL0]
    have hsub : ball z ρ ⊆ ball 0 1 := ball_subset_closedBall.trans (hcb.trans hδK)
    have := eLpNorm_ge hp0 hpt (w ν) (by positivity) hsub hlow
    exact absurd (lt_of_le_of_lt this hsmall) (lt_irrefl _)
  | succ m ih =>
    intro K hK hKc ε hε
    obtain ⟨δ, hδ, hδK, hK'c⟩ := thick hK hKc
    obtain ⟨M2, hM2⟩ := hb _ hδK hK'c (m + 2)
    set M0 := max M2 0
    have hM0 : 0 ≤ M0 := le_max_right _ _
    set h := min δ (ε / (2 * (M0 + 1)))
    have hh : 0 < h := lt_min hδ (by positivity)
    have hε0 : 0 < ε * h / 4 := by positivity
    filter_upwards [hM2, ih _ hδK hK'c _ hε0] with ν hbd hsm z hz
    have hcb : closedBall z h ⊆ cthickening δ K :=
      (closedBall_subset_closedBall (min_le_left _ _)).trans (closedBall_subset_cthickening hz δ)
    rw [← norm_fderiv_iteratedFDeriv]
    have hl := landau (iteratedFDeriv ℝ m (w ν)) z hh hε0.le hM0
      (fun x hx => diffAt_iter _ (hw ν) m (hδK (hcb hx)))
      (fun x hx => by
        rw [fderiv_iteratedFDeriv, Function.comp_apply, Function.comp_apply, ← LinearIsometryEquiv.map_sub,
          LinearIsometryEquiv.norm_map]
        have := lip_iter (w ν) (hw ν) (m + 1) (M := M0) (hcb.trans hδK)
          (fun y hy => (hbd y (hcb hy)).trans (le_max_left _ _)) hx (mem_closedBall_self hh.le)
        refine this.trans (mul_le_mul_of_nonneg_left ?_ hM0)
        rw [← dist_eq_norm]; exact hx)
      (fun x hx => hsm x (hcb hx))
    refine hl.trans ?_
    have e1 : 2 * (ε * h / 4) / h = ε / 2 := by field_simp; ring
    have h2 : M0 * h ≤ ε / 2 := by
      calc M0 * h ≤ M0 * (ε / (2 * (M0 + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hM0
        _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    linarith


lemma iter_sub (f g : ℂ → F) (hf : ContDiffOn ℝ ∞ f (ball 0 1)) (hg : ContDiffOn ℝ ∞ g (ball 0 1))
    (m : ℕ) {x : ℂ} (hx : x ∈ ball (0 : ℂ) 1) :
    iteratedFDeriv ℝ m (f - g) x = iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m g x := by
  have hs : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  rw [← iteratedFDerivWithin_of_isOpen (f := f - g) m hs hx,
    ← iteratedFDerivWithin_of_isOpen (f := f) m hs hx,
    ← iteratedFDerivWithin_of_isOpen (f := g) m hs hx]
  exact iteratedFDerivWithin_sub_apply ((hf x hx).of_le (by exact_mod_cast le_top))
    ((hg x hx).of_le (by exact_mod_cast le_top)) hs.uniqueDiffOn hx

lemma bound_iter (f : ℂ → F) (hf : ContDiffOn ℝ ∞ f (ball 0 1)) {K : Set ℂ}
    (hK : K ⊆ ball 0 1) (hKc : IsCompact K) (m : ℕ) :
    ∃ C, ∀ x ∈ K, ‖iteratedFDeriv ℝ m f x‖ ≤ C := by
  have hs : IsOpen (ball (0 : ℂ) 1) := isOpen_ball
  have hc : ContinuousOn (iteratedFDeriv ℝ m f) (ball 0 1) :=
    (hf.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top)
      hs.uniqueDiffOn).congr (fun x hx => (iteratedFDerivWithin_of_isOpen m hs hx).symm)
  exact hKc.exists_bound_of_continuousOn (hc.mono hK)

/-- Change of variables `x ↦ r x` in an `L^p` norm on the unit disc. -/
lemma eLpNorm_comp_smul {p : ℝ≥0∞} (Φ : ℂ → ℝ) (hΦ : Measurable Φ) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) :
    eLpNorm (fun x => Φ (r • x)) p (volume.restrict (ball 0 1)) ≤
      ENNReal.ofReal (|(r ^ 2)⁻¹|) ^ (1 / p).toReal *
        eLpNorm Φ p (volume.restrict (ball 0 1)) := by
  have hmeas : Measurable (fun x : ℂ => r • x) := measurable_const_smul r
  have e1 : eLpNorm (fun x => Φ (r • x)) p (volume.restrict (ball 0 1)) =
      eLpNorm Φ p (Measure.map (fun x : ℂ => r • x) (volume.restrict (ball 0 1))) :=
    (eLpNorm_map_measure hΦ.aestronglyMeasurable hmeas.aemeasurable).symm
  have hpre : (fun x : ℂ => r • x) ⁻¹' ball 0 r = ball 0 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  have hmap : Measure.map (fun x : ℂ => r • x) (volume.restrict (ball 0 1)) ≤
      ENNReal.ofReal (|(r ^ 2)⁻¹|) • volume.restrict (ball 0 1) := by
    have hrm := Measure.restrict_map (μ := volume) hmeas (measurableSet_ball (x := (0 : ℂ)) (ε := r))
    rw [hpre] at hrm
    rw [← hrm, Measure.map_addHaar_smul volume hr0.ne', Complex.finrank_real_complex,
      Measure.restrict_smul]
    intro s; simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (Measure.restrict_mono (ball_subset_ball hr1) le_rfl s) _
  rw [e1]
  refine (eLpNorm_mono_measure _ hmap).trans (le_of_eq ?_)
  have hc : ENNReal.ofReal (|(r ^ 2)⁻¹|) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [eLpNorm_smul_measure_of_ne_zero hc]
  rfl


open JHolomorphic DbarRegularity in
lemma resc_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (v : ℂ → E)
    (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (hlim : Tendsto (fun ν => sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν - v)) atTop
      (𝓝 0)) :
    ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ, ∃ M,
      ∀ᶠ ν in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (u ν) z‖ ≤ M := by
  intro K hK hKc m
  obtain ⟨r0, hr01, hKr0⟩ := exists_lt_subset_ball hKc.isClosed hK
  set r := max r0 (1 / 2)
  have hr0 : 0 < r := lt_max_of_lt_right (by norm_num)
  have hr1 : r < 1 := max_lt hr01 (by norm_num)
  have hKr : K ⊆ ball 0 r := hKr0.trans (ball_subset_ball (le_max_left _ _))
  set e : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ r hr0.ne').toContinuousLinearEquiv
  have he : ∀ z, e z = r • z := fun z => rfl
  set e' : ℂ ≃L[ℝ] ℂ := (LinearEquiv.smulOfNeZero ℝ ℂ r⁻¹ (inv_ne_zero hr0.ne')).toContinuousLinearEquiv
  have he' : ∀ z, e' z = r⁻¹ • z := fun z => rfl
  have heb : ∀ z ∈ ball (0 : ℂ) 1, e z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [he, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
    rw [mem_ball_zero_iff] at hz
    nlinarith [norm_nonneg z]
  set pp := ENNReal.ofReal p
  have hp0 : pp ≠ 0 := by simp [pp]; linarith
  have hpt : pp ≠ ⊤ := ENNReal.ofReal_ne_top
  set μ := volume.restrict (ball (0 : ℂ) 1)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hev : ∀ᶠ ν in atTop, sobolevNorm 1 pp (ball 0 1) (u ν - v) ≤ 1 :=
    hlim.eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set U : ℕ → ℂ → E := fun ν => u (ν + N) ∘ e
  obtain ⟨B0, hB0⟩ := isBounded_iff_forall_norm_le.mp hK₀.isBounded
  obtain ⟨Bv, hBv⟩ := bound_iter v hv (K := closedBall 0 r)
    (closedBall_subset_ball hr1) (isCompact_closedBall 0 r) 1
  have hBv0 : 0 ≤ Bv := (norm_nonneg _).trans (hBv 0 (mem_closedBall_self hr0.le))
  set κ := ‖(e : ℂ →L[ℝ] ℂ)‖
  set c' := ENNReal.ofReal (|(r ^ 2)⁻¹|) ^ (1 / pp).toReal
  set C : ℝ≥0∞ := eLpNorm (fun _ : ℂ => B0) pp μ +
    ‖κ‖ₑ * (c' + eLpNorm (fun _ : ℂ => Bv) pp μ)
  have hc' : c' ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hCfin : C ≠ ⊤ := by
    refine ENNReal.add_ne_top.mpr ⟨(memLp_const B0).eLpNorm_lt_top.ne, ?_⟩
    exact ENNReal.mul_ne_top enorm_ne_top
      (ENNReal.add_ne_top.mpr ⟨hc', (memLp_const Bv).eLpNorm_lt_top.ne⟩)
  -- hypotheses for the rescaled sequence
  have hUs : ∀ ν, ContDiffOn ℝ ∞ (U ν) (ball 0 1) := fun ν =>
    (hu (ν + N)).comp e.contDiff.contDiffOn (fun z hz => heb z hz)
  have hUhol : ∀ ν, IsJHolomorphicOn (Jν (ν + N)) (ball 0 1) (U ν) := by
    intro ν z hz
    obtain ⟨hd, hdb⟩ := hhol (ν + N) (e z) (heb z hz)
    refine ⟨hd.comp z e.differentiableAt, ?_⟩
    simp only [dbarJ] at hdb ⊢
    simp only [U, e.comp_right_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, Function.comp_apply]
    rw [he 1, he Complex.I, map_smul, map_smul, map_smul, ← smul_add, hdb, smul_zero]
  have hUmaps : ∀ ν, Set.MapsTo (U ν) (ball 0 1) K₀ := fun ν z hz => hmaps (ν + N) (heb z hz)
  have hconv' : TendstoCInftyLocOn (fun ν => Jν (ν + N)) J O := by
    intro K hK hKc m W hW
    exact (tendsto_add_atTop_nat N).eventually (hconv K hK hKc m W hW)
  have hUsob : ∀ ν, sobolevNorm 1 pp (ball 0 1) (U ν) ≤ ((C.toNNReal : ℝ≥0) : ℝ≥0∞) := by
    intro ν
    rw [ENNReal.coe_toNNReal hCfin]
    simp only [sobolevNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    refine add_le_add ?_ ?_
    · refine eLpNorm_mono_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact (hB0 _ (hUmaps ν hx)).trans (le_abs_self _)
    · set w := u (ν + N) - v
      have hsob1 : eLpNorm (fderiv ℝ w) pp μ ≤ 1 := by
        have h1 := hN (ν + N) (Nat.le_add_left N ν)
        simp only [sobolevNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h1
        refine le_trans (le_of_eq ?_) (le_trans le_add_self h1)
        exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (norm_iteratedFDeriv_one _).symm)
      have hpt' : ∀ x ∈ ball (0 : ℂ) 1, ‖iteratedFDeriv ℝ 1 (U ν) x‖ ≤
          κ * (‖fderiv ℝ w (r • x)‖ + Bv) := by
        intro x hx
        rw [norm_iteratedFDeriv_one]
        simp only [U, e.comp_right_fderiv]
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hy := heb x hx
        rw [he] at hy ⊢
        have hdu := (hhol (ν + N) _ hy).1
        have hdv : DifferentiableAt ℝ v (r • x) :=
          (hv.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp)
        have hsub : fderiv ℝ w (r • x) = fderiv ℝ (u (ν + N)) (r • x) - fderiv ℝ v (r • x) :=
          fderiv_sub hdu hdv
        have hBv' : ‖fderiv ℝ v (r • x)‖ ≤ Bv := by
          rw [← norm_iteratedFDeriv_one]
          refine hBv _ ?_
          rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
          rw [mem_ball_zero_iff] at hx
          nlinarith [norm_nonneg x]
        have : fderiv ℝ (u (ν + N)) (r • x) = fderiv ℝ w (r • x) + fderiv ℝ v (r • x) := by
          rw [hsub]; abel
        rw [this]
        exact (norm_add_le _ _).trans (by linarith)
      have hκ : 0 ≤ κ := norm_nonneg _
      calc eLpNorm (iteratedFDeriv ℝ 1 (U ν)) pp μ
          ≤ eLpNorm (κ • ((fun x => ‖fderiv ℝ w (r • x)‖) + fun _ => Bv)) pp μ := by
            refine eLpNorm_mono_ae (ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_)
            refine (hpt' x hx).trans (le_of_eq ?_)
            simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Real.norm_eq_abs]
            rw [abs_of_nonneg (mul_nonneg hκ (add_nonneg (norm_nonneg _) hBv0))]
        _ ≤ ‖κ‖ₑ * eLpNorm ((fun x => ‖fderiv ℝ w (r • x)‖) + fun _ => Bv) pp μ :=
            eLpNorm_const_smul_le
        _ ≤ ‖κ‖ₑ * (c' + eLpNorm (fun _ : ℂ => Bv) pp μ) := by
            gcongr
            refine (eLpNorm_add_le ?_ aestronglyMeasurable_const (by
              simp only [pp]; rw [← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal (by linarith))).trans ?_
            · exact ((measurable_fderiv ℝ w).norm.comp (measurable_const_smul r)).aestronglyMeasurable
            gcongr
            refine (eLpNorm_comp_smul (p := pp) (fun y => ‖fderiv ℝ w y‖)
              (measurable_fderiv ℝ w).norm hr0 hr1.le).trans ?_
            rw [eLpNorm_norm]
            calc c' * eLpNorm (fderiv ℝ w) pp μ ≤ c' * 1 := by gcongr
              _ = c' := mul_one _
  have h2a := bounded_iteratedFDeriv_of_sobolevNorm_le p hp J (fun ν => Jν (ν + N)) O K₀ hJ
    (fun ν => hJν _) hconv' hK₀ hK₀O U hUs hUhol hUmaps C.toNNReal hUsob
  have hK'sub : e' '' K ⊆ ball 0 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have := hKr hz
    rw [mem_ball_zero_iff] at this ⊢
    rw [he', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0), inv_mul_lt_one₀ hr0]
    exact this
  obtain ⟨M, hM⟩ := h2a _ hK'sub (hKc.image e'.continuous) m
  refine ⟨M * ‖(e' : ℂ →L[ℝ] ℂ)‖ ^ m, ?_⟩
  filter_upwards [eventually_ge_atTop N] with ν hν z hz
  have hcomp : u ν = U (ν - N) ∘ e' := by
    funext x
    simp only [U, Function.comp_apply, he, he', smul_smul, mul_inv_cancel₀ hr0.ne', one_smul,
      Nat.sub_add_cancel hν]
  rw [hcomp, ← iteratedFDerivWithin_univ, ← preimage_univ (f := e'),
    e'.iteratedFDerivWithin_comp_right _ uniqueDiffOn_univ (mem_univ _),
    iteratedFDerivWithin_univ]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  gcongr
  exact hM (ν - N) _ (mem_image_of_mem _ hz)

end SobDev

open JHolomorphic MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (Jν : ℕ → E → E →L[ℝ] E) (O K₀ : Set E)
    (hJ : IsAlmostComplexOn J O) (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O)
    (hconv : TendstoCInftyLocOn Jν J O) (hK₀ : IsCompact K₀) (hK₀O : K₀ ⊆ O)
    (u : ℕ → ℂ → E) (hu : ∀ ν, ContDiffOn ℝ ∞ (u ν) (ball 0 1))
    (hhol : ∀ ν, IsJHolomorphicOn (Jν ν) (ball 0 1) (u ν))
    (hmaps : ∀ ν, Set.MapsTo (u ν) (ball 0 1) K₀) (v : ℂ → E)
    (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (hlim : Tendsto (fun ν => sobolevNorm 1 (ENNReal.ofReal p) (ball 0 1) (u ν - v)) atTop
      (𝓝 0)) :
    TendstoCInftyLocOn u v (ball 0 1) := by
  have hb := SobDev.resc_bound p hp J Jν O K₀ hJ hJν hconv hK₀ hK₀O u hu hhol hmaps v hv hlim
  set w : ℕ → ℂ → E := fun ν => u ν - v
  have hw : ∀ ν, ContDiffOn ℝ ∞ (w ν) (ball 0 1) := fun ν => (hu ν).sub hv
  have hbw : ∀ K ⊆ ball (0 : ℂ) 1, IsCompact K → ∀ m : ℕ, ∃ M,
      ∀ᶠ ν in atTop, ∀ z ∈ K, ‖iteratedFDeriv ℝ m (w ν) z‖ ≤ M := by
    intro K hK hKc m
    obtain ⟨M, hM⟩ := hb K hK hKc m
    obtain ⟨Cv, hCv⟩ := SobDev.bound_iter v hv hK hKc m
    refine ⟨M + Cv, ?_⟩
    filter_upwards [hM] with ν hν z hz
    rw [SobDev.iter_sub _ _ (hu ν) hv m (hK hz)]
    exact (norm_sub_le _ _).trans (add_le_add (hν z hz) (hCv z hz))
  have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
  have hLw : Tendsto (fun ν => eLpNorm (w ν) (ENNReal.ofReal p) (volume.restrict (ball 0 1)))
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun ν => ?_)
    simp only [sobolevNorm, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    refine le_trans (le_of_eq ?_) le_self_add
    exact eLpNorm_congr_norm_ae (Eventually.of_forall fun x => (norm_iteratedFDeriv_zero).symm)
  have key := SobDev.interp hp0 ENNReal.ofReal_ne_top w hw hbw hLw
  intro K hK hKc m
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [key m K hK hKc (ε / 2) (half_pos hε)] with ν hν z hz
  rw [dist_eq_norm, norm_sub_rev, ← SobDev.iter_sub _ _ (hu ν) hv m (hK hz)]
  exact (hν z hz).trans_lt (half_lt_self hε)

