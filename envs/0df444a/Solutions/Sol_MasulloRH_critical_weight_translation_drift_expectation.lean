-- Prove2me | solution 1 for MasulloRH.critical_weight_translation_drift_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T14:33:34.211203+00:00
-- url     : https://prove2.me/submissions/9df24a99-3e0c-4a90-bac6-89ea3a6757f9

import Mathlib
open MeasureTheory Filter Set Topology
theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (hzero : μ {0} = 0)
    (h : ∀ t : ℝ, Real.exp (-t) ≤ ∫ x : ℝ,
      Real.exp ((|x+t| + 2 * Real.log (1+(x+t)^2)) -
                (|x| + 2 * Real.log (1+x^2))) ∂μ) :
    (∫ x : ℝ, (if x < 0 then (-1:ℝ) else 1) + 4*x/(1+x^2) ∂μ) = -1 := by
  let u : ℝ → ℝ := fun x => 2 * Real.log (1+x^2)
  let l : ℝ → ℝ := fun x => |x|+u x
  let d : ℝ → ℝ := fun x => (if x < 0 then (-1:ℝ) else 1) + 4*x/(1+x^2)
  let F : ℝ → ℝ → ℝ := fun t x => Real.exp (l (x+t)-l x)
  have du (x : ℝ) : HasDerivAt u (4*x/(1+x^2)) x := by
    dsimp [u]
    have hu : HasDerivAt (fun t : ℝ => 1+t^2) (2*x) x := by
      simpa [id] using ((hasDerivAt_id x).pow 2).const_add (1:ℝ)
    have hz : (fun t : ℝ => 1+t^2) x ≠ 0 := by dsimp; positivity
    have hh := (hu.log hz).const_mul (2:ℝ)
    convert hh using 1 <;> first | rfl | (simp [Pi.smul_def, Pi.mul_def, div_eq_mul_inv] <;> ring)
  have bu (x : ℝ) : ‖4*x/(1+x^2)‖ ≤ 2 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · apply (le_div_iff₀ (by positivity)).2
      nlinarith [sq_nonneg (x+1)]
    · apply (div_le_iff₀ (by positivity)).2
      nlinarith [sq_nonneg (x-1)]
  have ulip (x y : ℝ) : |u x-u y| ≤ 2*|x-y| := by
    exact (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (du z).hasDerivWithinAt) (fun z _ => bu z) (Set.mem_univ y) (Set.mem_univ x)
  have llip (x y : ℝ) : |l x-l y| ≤ 3*|x-y| := by
    dsimp [l]
    calc
      _ = |(|x|-|y|)+(u x-u y)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by linarith [abs_abs_sub_abs_le_abs_sub x y, ulip x y]
  have elip {x y : ℝ} (hx : x ≤ 3) (hy : y ≤ 3) :
      |Real.exp x-Real.exp y| ≤ Real.exp 3*|x-y| := by
    exact (convex_Iic (3:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (Real.hasDerivAt_exp z).hasDerivWithinAt)
      (fun z hz => by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hz)
      hy hx
  have fcont (t : ℝ) : Continuous (F t) := by
    dsimp [F,l,u]
    fun_prop (disch := intros; positivity)
  have hd : AEStronglyMeasurable d μ := by
    apply Measurable.aestronglyMeasurable
    dsimp [d]
    exact (Measurable.ite measurableSet_Iio measurable_const measurable_const).add
      (by fun_prop : Measurable (fun x : ℝ => 4*x/(1+x^2)))
  have fl (x : ℝ) : LipschitzOnWith (Real.nnabs (3 * Real.exp 3)) (fun t => F t x) (Ioo (-1) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht v hv
    have sub (s : ℝ) (hs : s ∈ Ioo (-1:ℝ) 1) : l (x+s)-l x ≤ 3 := by
      have h1 := llip (x+s) x
      rw [add_sub_cancel_left] at h1
      linarith [le_abs_self (l (x+s)-l x), (abs_lt.mpr hs : |s| < 1)]
    have h1 := elip (sub t ht) (sub v hv)
    have h2 := llip (x+t) (x+v)
    rw [sub_sub_sub_cancel_right] at h1
    rw [add_sub_add_left_eq_sub] at h2
    simp only [Real.dist_eq, Real.coe_nnabs, abs_of_nonneg (by positivity : 0 ≤ 3*Real.exp 3)]
    change |Real.exp _ - Real.exp _| ≤ _
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos 3).le]
  have hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun t => F t x) (d x) 0 := by
    have hn : ∀ᵐ x ∂μ, x ≠ 0 := by
      rw [ae_iff]
      simpa using hzero
    filter_upwards [hn] with x hx
    have hl : HasDerivAt l (d x) x := by
      rcases hx.lt_or_gt with ha | ha
      · simpa [l,d,ha,Pi.add_def] using (hasDerivAt_abs_neg ha).add (du x)
      · simpa [l,d,not_lt.mpr ha.le,Pi.add_def] using (hasDerivAt_abs_pos ha).add (du x)
    have harg : HasDerivAt (fun t : ℝ => x+t) 1 0 := (hasDerivAt_id 0).const_add x
    have hls : HasDerivAt (fun t : ℝ => l (x+t)) (d x) 0 := by
      simpa [Function.comp_def] using ((show HasDerivAt l (d x) (x+0) by simpa using hl).comp 0 harg)
    simpa [F] using ((hls.sub_const (l x)).exp)
  have hint : HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, d x ∂μ) 0 := by
    exact (hasDerivAt_integral_of_dominated_loc_of_lip (bound := fun _ : ℝ => (3*Real.exp 3))
      (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))
      (Eventually.of_forall fun t => (fcont t).aestronglyMeasurable)
      (by simpa [F] using (integrable_const (μ := μ) (1:ℝ))) hd
      (Eventually.of_forall fl) (integrable_const _) hdiff).2
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).neg.exp)
  have hmin : IsLocalMin (fun t => (∫ x, F t x ∂μ) - Real.exp (-t)) 0 := by
    apply Eventually.of_forall
    intro t
    simpa [F,l,u] using (sub_nonneg.mpr (h t))
  have he := hmin.hasDerivAt_eq_zero (hint.sub hexp)
  change (∫ x, d x ∂μ) = -1
  linarith
