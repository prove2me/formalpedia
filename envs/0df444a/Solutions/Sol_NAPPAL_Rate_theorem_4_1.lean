-- Prove2me | solution 1 for NAPPAL.Rate.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T18:57:22.351179+00:00
-- url     : https://prove2.me/submissions/b4be0574-bcf0-4a02-b82b-1072aa2bd798

import Mathlib
import Definitions.Def_NAPPAL_Rate_Setting
import Theorems.Thm_NAPPAL_Rate_lemma_4_1
import Theorems.Thm_NAPPAL_Rate_lemma_4_3
import Theorems.Thm_NAPPAL_Rate_proposition_3_1

open Filter Topology
open scoped InnerProductSpace

section Helpers

private lemma wdist_nonneg {n d m : ℕ} (w w' : NAPPAL.KL.W n d m) :
    0 ≤ NAPPAL.KL.wdist w w' :=
  Real.sqrt_nonneg _

private lemma norm_fst_le_tnorm {n d m : ℕ} (w : NAPPAL.KL.W n d m) :
    ‖w.1‖ ≤ NAPPAL.KL.tnorm w := by
  unfold NAPPAL.KL.tnorm
  calc ‖w.1‖ = Real.sqrt (‖w.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg ‖w.2.1‖, sq_nonneg ‖w.2.2‖]

private lemma norm_snd_fst_le_tnorm {n d m : ℕ} (w : NAPPAL.KL.W n d m) :
    ‖w.2.1‖ ≤ NAPPAL.KL.tnorm w := by
  unfold NAPPAL.KL.tnorm
  calc ‖w.2.1‖ = Real.sqrt (‖w.2.1‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg ‖w.1‖, sq_nonneg ‖w.2.2‖]

private lemma norm_snd_snd_le_tnorm {n d m : ℕ} (w : NAPPAL.KL.W n d m) :
    ‖w.2.2‖ ≤ NAPPAL.KL.tnorm w := by
  unfold NAPPAL.KL.tnorm
  calc ‖w.2.2‖ = Real.sqrt (‖w.2.2‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖w.1‖ ^ 2 + ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        nlinarith [sq_nonneg ‖w.1‖, sq_nonneg ‖w.2.1‖]

private lemma tnorm_le_sum_norms {n d m : ℕ} (w : NAPPAL.KL.W n d m) :
    NAPPAL.KL.tnorm w ≤ ‖w.1‖ + ‖w.2.1‖ + ‖w.2.2‖ := by
  unfold NAPPAL.KL.tnorm
  have h0 : 0 ≤ ‖w.1‖ + ‖w.2.1‖ + ‖w.2.2‖ := by positivity
  rw [← Real.sqrt_sq h0]
  apply Real.sqrt_le_sqrt
  nlinarith [norm_nonneg w.1, norm_nonneg w.2.1, norm_nonneg w.2.2]

private lemma lamMin_mul_sq_le {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (v : NAPPAL.KL.E d) :
    NAPPAL.KL.lamMin P * ‖v‖ ^ 2 ≤ ‖P.B v‖ ^ 2 := by
  by_cases hv : v = 0
  · simp [hv]
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    set e : NAPPAL.KL.E d := (‖v‖⁻¹) • v
    have he : e ∈ Metric.sphere (0 : NAPPAL.KL.E d) 1 := by
      simp [e, norm_smul, inv_mul_cancel₀ hvn.ne']
    have hbdd : BddBelow ((fun x : NAPPAL.KL.E d => ‖P.B x‖ ^ 2) '' Metric.sphere (0 : NAPPAL.KL.E d) 1) :=
      ⟨0, by rintro _ ⟨x, -, rfl⟩; positivity⟩
    have hle : NAPPAL.KL.lamMin P ≤ ‖P.B e‖ ^ 2 :=
      csInf_le hbdd ⟨e, he, rfl⟩
    have hBe : ‖P.B e‖ ^ 2 = (‖v‖ ^ 2)⁻¹ * ‖P.B v‖ ^ 2 := by
      simp [e, map_smul, norm_smul, mul_pow, inv_pow]
    rw [hBe] at hle
    have hmul := mul_le_mul_of_nonneg_right hle (sq_nonneg ‖v‖)
    have hpos : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 hvn.ne'
    calc NAPPAL.KL.lamMin P * ‖v‖ ^ 2
        ≤ (‖v‖ ^ 2)⁻¹ * ‖P.B v‖ ^ 2 * ‖v‖ ^ 2 := hmul
      _ = ‖P.B v‖ ^ 2 := by field_simp [hpos]

private lemma lamMin_mul_sq_le_adjoint_of_range {n d m : ℕ} (P : NAPPAL.KL.Problem n d m)
    (hlam : 0 < NAPPAL.KL.lamMin P) (y : NAPPAL.KL.E d) :
    NAPPAL.KL.lamMin P * ‖P.B y‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint P.B (P.B y)‖ ^ 2 := by
  by_cases hBy : P.B y = 0
  · simp [hBy]
  · have hpos : 0 < ‖P.B y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hBy)
    have hcs : ‖P.B y‖ ^ 2 ≤ ‖ContinuousLinearMap.adjoint P.B (P.B y)‖ * ‖y‖ := by
      calc ‖P.B y‖ ^ 2 = ⟪P.B y, P.B y⟫_ℝ := (real_inner_self_eq_norm_sq _).symm
        _ = ⟪ContinuousLinearMap.adjoint P.B (P.B y), y⟫_ℝ := by
            rw [ContinuousLinearMap.adjoint_inner_left]
        _ ≤ ‖ContinuousLinearMap.adjoint P.B (P.B y)‖ * ‖y‖ := real_inner_le_norm _ _
    have hsq : (‖P.B y‖ ^ 2) ^ 2 ≤ (‖ContinuousLinearMap.adjoint P.B (P.B y)‖ * ‖y‖) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) hcs 2
    have hlam_y : NAPPAL.KL.lamMin P * ‖y‖ ^ 2 ≤ ‖P.B y‖ ^ 2 := lamMin_mul_sq_le P y
    have h1 : NAPPAL.KL.lamMin P * (‖P.B y‖ ^ 2) ^ 2 ≤
        ‖ContinuousLinearMap.adjoint P.B (P.B y)‖ ^ 2 * ‖P.B y‖ ^ 2 := by
      calc NAPPAL.KL.lamMin P * (‖P.B y‖ ^ 2) ^ 2
          ≤ NAPPAL.KL.lamMin P * (‖ContinuousLinearMap.adjoint P.B (P.B y)‖ ^ 2 * ‖y‖ ^ 2) := by
            nlinarith [hsq, hlam]
        _ = ‖ContinuousLinearMap.adjoint P.B (P.B y)‖ ^ 2 * (NAPPAL.KL.lamMin P * ‖y‖ ^ 2) := by ring
        _ ≤ ‖ContinuousLinearMap.adjoint P.B (P.B y)‖ ^ 2 * ‖P.B y‖ ^ 2 := by
            exact mul_le_mul_of_nonneg_left hlam_y (sq_nonneg _)
    nlinarith

private lemma descent_lemma {k : ℕ} {f : NAPPAL.KL.E k → ℝ} {L : ℝ}
    (hf : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : NAPPAL.KL.E k) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + (L / 2) * ‖y - x‖ ^ 2 := by
  let g : ℝ → ℝ := fun t =>
    f (x + t • (y - x)) - f x - t * ⟪gradient f x, y - x⟫_ℝ - (L / 2) * t ^ 2 * ‖y - x‖ ^ 2
  have hg_deriv : ∀ t : ℝ, HasDerivAt g
      (⟪gradient f (x + t • (y - x)) - gradient f x, y - x⟫_ℝ - L * t * ‖y - x‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • (y - x)) (y - x) t := by
      simpa using (hasDerivAt_id t |>.smul_const (y - x)).const_add x
    have hgrad : HasFDerivAt f
        (InnerProductSpace.toDual ℝ (NAPPAL.KL.E k) (gradient f (x + t • (y - x))))
        (x + t • (y - x)) := (hf (x + t • (y - x))).hasGradientAt.hasFDerivAt
    have hf1 : HasDerivAt (fun s : ℝ => f (x + s • (y - x)))
        (⟪gradient f (x + t • (y - x)), y - x⟫_ℝ) t := by
      refine ((hgrad.comp t hline.hasFDerivAt).hasDerivAt).congr_deriv ?_
      simp
    have hlin : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, y - x⟫_ℝ) (⟪gradient f x, y - x⟫_ℝ) t := by
      simpa using (hasDerivAt_id t).mul_const (⟪gradient f x, y - x⟫_ℝ)
    have hquad : HasDerivAt (fun s : ℝ => (L / 2) * s ^ 2 * ‖y - x‖ ^ 2) (L * t * ‖y - x‖ ^ 2) t := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact ((hsq.const_mul (L / 2)).mul_const (‖y - x‖ ^ 2)).congr_deriv (by ring)
    exact (((hf1.sub_const (f x)).sub hlin).sub hquad).congr_deriv (by rw [inner_sub_left])
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hg_deriv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hg_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hg_deriv t).deriv]
      have h1 : ⟪gradient f (x + t • (y - x)) - gradient f x, y - x⟫_ℝ ≤
          ‖gradient f (x + t • (y - x)) - gradient f x‖ * ‖y - x‖ := real_inner_le_norm _ _
      have h2 : ‖gradient f (x + t • (y - x)) - gradient f x‖ ≤ L * (t * ‖y - x‖) := by
        have h2' : ‖gradient f (x + t • (y - x)) - gradient f x‖ ≤ L * ‖t • (y - x)‖ := by
          simpa [add_sub_cancel_left] using hlip (x + t • (y - x)) x
        rwa [norm_smul, Real.norm_of_nonneg (le_of_lt ht.1)] at h2'
      nlinarith [norm_nonneg (y - x)]
  have h10 : g 1 ≤ g 0 := hanti (by simp) (by simp) (by norm_num)
  simp only [g, one_smul, add_sub_cancel, one_mul, one_pow, zero_smul, add_zero, sub_self,
    zero_mul, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h10
  linarith

private lemma bregman_nonneg {k : ℕ} {K : NAPPAL.KL.E k → ℝ} {β : ℝ}
    (hKd : Differentiable ℝ K) (hβ : 0 < β) (hKsc : StrongConvexOn Set.univ β K)
    (x y : NAPPAL.KL.E k) : 0 ≤ NAPPAL.KL.bregman K x y := by
  have hconv : ConvexOn ℝ Set.univ K := hKsc.convexOn (fun r => by positivity)
  let g : ℝ → ℝ := fun t => K (y + t • (x - y))
  have hg : HasDerivAt g (⟪gradient K y, x - y⟫_ℝ) 0 := by
    have hline : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ) |>.smul_const (x - y)).const_add y
    have hgrad : HasFDerivAt K (InnerProductSpace.toDual ℝ (NAPPAL.KL.E k) (gradient K y))
        (y + (0 : ℝ) • (x - y)) := by
      simpa using (hKd y).hasGradientAt.hasFDerivAt
    exact hgrad.comp_hasDerivAt 0 hline
  have hslope : Tendsto (fun t : ℝ => t⁻¹ * (g t - g 0)) (𝓝[>] 0) (𝓝 (⟪gradient K y, x - y⟫_ℝ)) := by
    have hsub : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun t ht => ne_of_gt ht
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hg).mono_left (nhdsWithin_mono (0 : ℝ) hsub)
    simpa [g, smul_eq_mul] using h
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0, t⁻¹ * (g t - g 0) ≤ K x - K y := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have hpt : y + t • (x - y) = (1 - t) • y + t • x := by module
    have hc := hconv.2 (Set.mem_univ y) (Set.mem_univ x)
      (show (0 : ℝ) ≤ 1 - t by linarith [ht.2]) (show (0 : ℝ) ≤ t by exact le_of_lt ht.1) (by ring)
    simp only [smul_eq_mul] at hc
    have hgt : g t ≤ (1 - t) * K y + t * K x := by
      simpa [g, hpt] using hc
    have htpos : 0 < t := ht.1
    rw [inv_mul_le_iff₀ htpos]
    simp only [g, zero_smul, add_zero]
    linarith
  have hlim : ⟪gradient K y, x - y⟫_ℝ ≤ K x - K y :=
    le_of_tendsto hslope hle
  unfold NAPPAL.KL.bregman
  linarith

private lemma bregman_le {k : ℕ} {K : NAPPAL.KL.E k → ℝ} {LK : ℝ}
    (hKd : Differentiable ℝ K)
    (hlip : ∀ x y, ‖gradient K x - gradient K y‖ ≤ LK * ‖x - y‖)
    (x y : NAPPAL.KL.E k) :
    NAPPAL.KL.bregman K x y ≤ (LK / 2) * ‖x - y‖ ^ 2 := by
  have h := descent_lemma hKd hlip y x
  unfold NAPPAL.KL.bregman
  linarith

private lemma gradV_lipschitz_in_v {n d m : ℕ} {P : NAPPAL.KL.Problem n d m} {LG : ℝ}
    (hG : Differentiable ℝ P.G ∧ 0 ≤ LG ∧
      ∀ u v u' v', ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ^ 2 +
        ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ^ 2 ≤
        LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2))
    (u : NAPPAL.KL.E n) (v v' : NAPPAL.KL.E d) :
    ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u v'‖ ≤ LG * ‖v - v'‖ := by
  have h := hG.2.2 u v u v'
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at h
  have hsq : ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u v'‖ ^ 2 ≤ (LG * ‖v - v'‖) ^ 2 := by
    nlinarith [sq_nonneg ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u v'‖]
  nlinarith [norm_nonneg (NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u v'),
    mul_nonneg hG.2.1 (norm_nonneg (v - v'))]

private lemma gradV_lipschitz_joint {n d m : ℕ} {P : NAPPAL.KL.Problem n d m} {LG : ℝ}
    (hG : Differentiable ℝ P.G ∧ 0 ≤ LG ∧
      ∀ u v u' v', ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ^ 2 +
        ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ^ 2 ≤
        LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2))
    (u : NAPPAL.KL.E n) (v : NAPPAL.KL.E d) (u' : NAPPAL.KL.E n) (v' : NAPPAL.KL.E d) :
    ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ≤ LG * (‖u - u'‖ + ‖v - v'‖) := by
  have h := hG.2.2 u v u' v'
  have hcross : 0 ≤ LG ^ 2 * (‖u - u'‖ * ‖v - v'‖) := by positivity
  have hsq : ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ^ 2 ≤
      (LG * (‖u - u'‖ + ‖v - v'‖)) ^ 2 := by
    have hexp : (LG * (‖u - u'‖ + ‖v - v'‖)) ^ 2 =
        LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) + 2 * (LG ^ 2 * (‖u - u'‖ * ‖v - v'‖)) := by ring
    linarith [sq_nonneg ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖]
  nlinarith [norm_nonneg (NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'),
    mul_nonneg hG.2.1 (add_nonneg (norm_nonneg (u - u')) (norm_nonneg (v - v')))]

private lemma gradU_lipschitz_joint {n d m : ℕ} {P : NAPPAL.KL.Problem n d m} {LG : ℝ}
    (hG : Differentiable ℝ P.G ∧ 0 ≤ LG ∧
      ∀ u v u' v', ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ^ 2 +
        ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖ ^ 2 ≤
        LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2))
    (u : NAPPAL.KL.E n) (v : NAPPAL.KL.E d) (u' : NAPPAL.KL.E n) (v' : NAPPAL.KL.E d) :
    ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ≤ LG * (‖u - u'‖ + ‖v - v'‖) := by
  have h := hG.2.2 u v u' v'
  have hcross : 0 ≤ LG ^ 2 * (‖u - u'‖ * ‖v - v'‖) := by positivity
  have hsq : ‖NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'‖ ^ 2 ≤
      (LG * (‖u - u'‖ + ‖v - v'‖)) ^ 2 := by
    have hexp : (LG * (‖u - u'‖ + ‖v - v'‖)) ^ 2 =
        LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2) + 2 * (LG ^ 2 * (‖u - u'‖ * ‖v - v'‖)) := by ring
    linarith [sq_nonneg ‖NAPPAL.KL.gradV P u v - NAPPAL.KL.gradV P u' v'‖]
  nlinarith [norm_nonneg (NAPPAL.KL.gradU P u v - NAPPAL.KL.gradU P u' v'),
    mul_nonneg hG.2.1 (add_nonneg (norm_nonneg (u - u')) (norm_nonneg (v - v')))]

private lemma F_v_descent {n d m : ℕ} {P : NAPPAL.KL.Problem n d m} {LG LH L0 : ℝ} {LOmj : Fin m → ℝ}
    (hA1 : NAPPAL.KL.Assumption1 P LG LH L0 LOmj)
    (u : NAPPAL.KL.E n) (v vhat : NAPPAL.KL.E d) :
    NAPPAL.KL.F P u vhat ≤ NAPPAL.KL.F P u v +
      ⟪NAPPAL.KL.gradV P u v + gradient P.H v, vhat - v⟫_ℝ +
      ((LG + LH) / 2) * ‖vhat - v‖ ^ 2 := by
  let φ : NAPPAL.KL.E d → ℝ := fun y => P.G (u, y) + P.H y
  have hφ_diff : Differentiable ℝ φ := by
    intro y
    have h1 : DifferentiableAt ℝ (fun y' => P.G (u, y')) y :=
      (hA1.1.1 (u, y)).comp y (differentiableAt_const u |>.prodMk differentiableAt_id)
    exact h1.add (hA1.2.1.1 y)
  have hφ_grad : ∀ y, gradient φ y = NAPPAL.KL.gradV P u y + gradient P.H y := by
    intro y
    have h1 : HasGradientAt (fun y' => P.G (u, y')) (NAPPAL.KL.gradV P u y) y :=
      ((hA1.1.1 (u, y)).comp y (differentiableAt_const u |>.prodMk differentiableAt_id)).hasGradientAt
    have h2 : HasGradientAt P.H (gradient P.H y) y := (hA1.2.1.1 y).hasGradientAt
    have h12 : HasGradientAt φ (NAPPAL.KL.gradV P u y + gradient P.H y) y := by
      rw [hasGradientAt_iff_hasFDerivAt, map_add]
      exact h1.hasFDerivAt.add h2.hasFDerivAt
    exact h12.gradient
  have hφ_lip : ∀ y y', ‖gradient φ y - gradient φ y'‖ ≤ (LG + LH) * ‖y - y'‖ := by
    intro y y'
    rw [hφ_grad y, hφ_grad y']
    have heq : (NAPPAL.KL.gradV P u y + gradient P.H y) - (NAPPAL.KL.gradV P u y' + gradient P.H y') =
        (NAPPAL.KL.gradV P u y - NAPPAL.KL.gradV P u y') + (gradient P.H y - gradient P.H y') := by abel
    rw [heq]
    calc ‖(NAPPAL.KL.gradV P u y - NAPPAL.KL.gradV P u y') + (gradient P.H y - gradient P.H y')‖
        ≤ ‖NAPPAL.KL.gradV P u y - NAPPAL.KL.gradV P u y'‖ + ‖gradient P.H y - gradient P.H y'‖ :=
          norm_add_le _ _
      _ ≤ LG * ‖y - y'‖ + LH * ‖y - y'‖ :=
          add_le_add (gradV_lipschitz_in_v hA1.1 u y y') (hA1.2.1.2.2 y y')
      _ = (LG + LH) * ‖y - y'‖ := by ring
  have hd := descent_lemma hφ_diff hφ_lip v vhat
  rw [hφ_grad v] at hd
  unfold NAPPAL.KL.F
  dsimp only [φ] at hd
  linarith

private lemma fderiv_Om_lipschitz {n d m : ℕ} {P : NAPPAL.KL.Problem n d m} {LG LH L0 : ℝ}
    {LOmj : Fin m → ℝ} (hA1 : NAPPAL.KL.Assumption1 P LG LH L0 LOmj) (u u' : NAPPAL.KL.E n) :
    ‖fderiv ℝ P.Om u - fderiv ℝ P.Om u'‖ ≤ NAPPAL.KL.LOm LOmj * ‖u - u'‖ := by
  have hLOm_nn : 0 ≤ NAPPAL.KL.LOm LOmj :=
    Finset.sum_nonneg (fun j _ => (hA1.2.2.2.2.1 j).1)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hLOm_nn (norm_nonneg _))
  intro y
  have hcoord : ∀ j : Fin m, ((fderiv ℝ P.Om u - fderiv ℝ P.Om u') y) j =
      ⟪gradient (fun x => P.Om x j) u - gradient (fun x => P.Om x j) u', y⟫_ℝ := by
    intro j
    have hproj : ∀ z : NAPPAL.KL.E n,
        (fderiv ℝ P.Om z y) j = ⟪gradient (fun x => P.Om x j) z, y⟫_ℝ := by
      intro z
      let pr : NAPPAL.KL.E m →L[ℝ] ℝ := EuclideanSpace.proj j
      have h1 : HasFDerivAt (fun x => P.Om x j) (pr.comp (fderiv ℝ P.Om z)) z :=
        pr.hasFDerivAt.comp z (hA1.2.2.2.1.1 z).hasFDerivAt
      have h2 : HasFDerivAt (fun x => P.Om x j)
          (InnerProductSpace.toDual ℝ (NAPPAL.KL.E n) (gradient (fun x => P.Om x j) z)) z :=
        h1.differentiableAt.hasGradientAt.hasFDerivAt
      have heq := h1.unique h2
      have := congr_arg (fun L : NAPPAL.KL.E n →L[ℝ] ℝ => L y) heq
      simpa [pr, InnerProductSpace.toDual_apply_apply] using this
    simp only [sub_apply, PiLp.sub_apply, hproj u, hproj u', inner_sub_left]
  have hsq : ‖(fderiv ℝ P.Om u - fderiv ℝ P.Om u') y‖ ^ 2 ≤
      (NAPPAL.KL.LOm LOmj * ‖u - u'‖ * ‖y‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hterm : ∀ j : Fin m, ‖((fderiv ℝ P.Om u - fderiv ℝ P.Om u') y) j‖ ^ 2 ≤
        (LOmj j * ‖u - u'‖ * ‖y‖) ^ 2 := by
      intro j
      rw [hcoord j, Real.norm_eq_abs, sq_abs]
      have hle : |⟪gradient (fun x => P.Om x j) u - gradient (fun x => P.Om x j) u', y⟫_ℝ| ≤
          LOmj j * ‖u - u'‖ * ‖y‖ := by
        calc |⟪gradient (fun x => P.Om x j) u - gradient (fun x => P.Om x j) u', y⟫_ℝ|
            ≤ ‖gradient (fun x => P.Om x j) u - gradient (fun x => P.Om x j) u'‖ * ‖y‖ :=
              abs_real_inner_le_norm _ _
          _ ≤ (LOmj j * ‖u - u'‖) * ‖y‖ :=
              mul_le_mul_of_nonneg_right ((hA1.2.2.2.2.1 j).2 u u') (norm_nonneg y)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    calc ∑ j : Fin m, ‖((fderiv ℝ P.Om u - fderiv ℝ P.Om u') y) j‖ ^ 2
        ≤ ∑ j : Fin m, (LOmj j * ‖u - u'‖ * ‖y‖) ^ 2 := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (∑ j : Fin m, LOmj j ^ 2) * (‖u - u'‖ * ‖y‖) ^ 2 := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl (fun j _ => by ring)
      _ ≤ (∑ j : Fin m, LOmj j) ^ 2 * (‖u - u'‖ * ‖y‖) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => (hA1.2.2.2.2.1 j).1)
      _ = (NAPPAL.KL.LOm LOmj * ‖u - u'‖ * ‖y‖) ^ 2 := by unfold NAPPAL.KL.LOm; ring
  nlinarith [norm_nonneg ((fderiv ℝ P.Om u - fderiv ℝ P.Om u') y),
    mul_nonneg (mul_nonneg hLOm_nn (norm_nonneg (u - u'))) (norm_nonneg y)]

private lemma mu_pos {n d m : ℕ} {P : NAPPAL.KL.Problem n d m} {LG LH L0 LK β γ : ℝ}
    {LOmj : Fin m → ℝ} {K : NAPPAL.KL.E n → ℝ}
    (hA1 : NAPPAL.KL.Assumption1 P LG LH L0 LOmj)
    (hA2 : NAPPAL.KL.Assumption2 P K β LK γ LG LH) :
    0 < (3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2 := by
  have hlam : 0 < NAPPAL.KL.lamMin P := hA1.2.2.2.2.2.1.2
  have hLG : 0 ≤ LG := hA1.1.2.1
  have hLH : 0 ≤ LH := hA1.2.1.2.1
  have hγ_ineq := hA2.2.2.2.2.2
  have hsqrt57 : (7 : ℝ) < Real.sqrt 57 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hmul : (Real.sqrt 57 + 1) / 2 * (LG + LH) < γ * NAPPAL.KL.lamMin P := by
    have h1 := mul_lt_mul_of_pos_right hγ_ineq hlam
    have h2 : (Real.sqrt 57 + 1) / (2 * NAPPAL.KL.lamMin P) * (LG + LH) * NAPPAL.KL.lamMin P =
        (Real.sqrt 57 + 1) / 2 * (LG + LH) := by
      field_simp [hlam.ne']
    linarith
  have h4 : 4 * (LG + LH) ≤ (Real.sqrt 57 + 1) / 2 * (LG + LH) := by
    nlinarith
  nlinarith

private lemma lam_lower_bound {n d m : ℕ} (P : NAPPAL.KL.Problem n d m)
    (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ) (K : NAPPAL.KL.E n → ℝ)
    (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ vhat : NAPPAL.KL.E d,
      NAPPAL.KL.Theta P (u k) + P.B vhat = 0 ∧
      NAPPAL.KL.F P (u k) vhat +
        ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2) * ‖v k - vhat‖ ^ 2 +
        1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 ≤
      NAPPAL.KL.Lam P LG LH L0 γ u v p k := by
  have hA1 := hrun.1
  have hA2 := hrun.2.1
  have hN := hrun.2.2.1
  have hγ : 0 < γ := hN.1
  have hlam : 0 < NAPPAL.KL.lamMin P := hA1.2.2.2.2.2.1.2
  have hrange : Set.range (NAPPAL.KL.Theta P) ⊆ Set.range P.B := hA1.2.2.2.2.2.1.1
  obtain ⟨z, hz⟩ : NAPPAL.KL.Theta P (u k) ∈ Set.range P.B := hrange ⟨u k, rfl⟩
  refine ⟨-z, ?_, ?_⟩
  · simp [hz]
  · set vhat := -z
    have hvhat : NAPPAL.KL.Theta P (u k) + P.B vhat = 0 := by simp [vhat, hz]
    have hres : NAPPAL.KL.Theta P (u k) + P.B (v k) = P.B (v k - vhat) := by
      rw [map_sub]
      have : NAPPAL.KL.Theta P (u k) = -P.B vhat := eq_neg_of_add_eq_zero_left hvhat
      rw [this]; abel
    have h41b := (NAPPAL.Rate.lemma_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hA1 hA2 hN).2.1 k hk
    have hdes := F_v_descent hA1 (u k) (v k) vhat
    set r : NAPPAL.KL.E d :=
      (NAPPAL.KL.gradV P (u k) (v k) - NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))) +
      (gradient P.H (v k) - gradient P.H (v (k - 1))) +
      γ • ContinuousLinearMap.adjoint P.B (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))
    have hr_inner :
        ⟪NAPPAL.KL.gradV P (u k) (v k) + gradient P.H (v k), v k - vhat⟫_ℝ +
        ⟪ContinuousLinearMap.adjoint P.B (p k), v k - vhat⟫_ℝ = ⟪r, v k - vhat⟫_ℝ := by
      rw [h41b, ← inner_add_left]
      congr 1
      dsimp only [r]
      abel
    have hinner_p : ⟪p k, NAPPAL.KL.Theta P (u k) + P.B (v k)⟫_ℝ =
        ⟪ContinuousLinearMap.adjoint P.B (p k), v k - vhat⟫_ℝ := by
      rw [hres, ContinuousLinearMap.adjoint_inner_left]
    have hdes' : NAPPAL.KL.F P (u k) vhat ≤ NAPPAL.KL.F P (u k) (v k) -
        ⟪NAPPAL.KL.gradV P (u k) (v k) + gradient P.H (v k), v k - vhat⟫_ℝ +
        ((LG + LH) / 2) * ‖v k - vhat‖ ^ 2 := by
      have h1 : vhat - v k = -(v k - vhat) := by abel
      rw [h1, inner_neg_right, norm_neg] at hdes
      linarith
    have hr_norm : ‖r‖ ≤ (LG + γ * ‖P.B‖ * L0) * ‖u (k - 1) - u k‖ +
        (LG + LH) * ‖v (k - 1) - v k‖ := by
      have h1 : ‖NAPPAL.KL.gradV P (u k) (v k) - NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))‖ ≤
          LG * (‖u (k - 1) - u k‖ + ‖v (k - 1) - v k‖) := by
        simpa [norm_sub_rev] using gradV_lipschitz_joint hA1.1 (u k) (v k) (u (k - 1)) (v (k - 1))
      have h2 : ‖gradient P.H (v k) - gradient P.H (v (k - 1))‖ ≤ LH * ‖v (k - 1) - v k‖ := by
        simpa [norm_sub_rev] using hA1.2.1.2.2 (v k) (v (k - 1))
      have h3 : ‖γ • ContinuousLinearMap.adjoint P.B
          (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ ≤
          γ * ‖P.B‖ * L0 * ‖u (k - 1) - u k‖ := by
        rw [norm_smul, Real.norm_of_nonneg hγ.le]
        calc γ * ‖ContinuousLinearMap.adjoint P.B
              (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖
            ≤ γ * (‖ContinuousLinearMap.adjoint P.B‖ *
                ‖NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1))‖) := by
              gcongr
              exact ContinuousLinearMap.le_opNorm _ _
          _ = γ * (‖P.B‖ * ‖NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1))‖) := by
              rw [LinearIsometryEquiv.norm_map]
          _ ≤ γ * (‖P.B‖ * (L0 * ‖u (k - 1) - u k‖)) := by
              gcongr
              simpa [norm_sub_rev] using hA1.2.2.2.1.2.2.2 (u k) (u (k - 1))
          _ = γ * ‖P.B‖ * L0 * ‖u (k - 1) - u k‖ := by ring
      calc ‖r‖ ≤ ‖(NAPPAL.KL.gradV P (u k) (v k) - NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))) +
              (gradient P.H (v k) - gradient P.H (v (k - 1)))‖ +
              ‖γ • ContinuousLinearMap.adjoint P.B
                (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ := norm_add_le _ _
        _ ≤ (‖NAPPAL.KL.gradV P (u k) (v k) - NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))‖ +
              ‖gradient P.H (v k) - gradient P.H (v (k - 1))‖) +
              ‖γ • ContinuousLinearMap.adjoint P.B
                (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ := by
              gcongr; exact norm_add_le _ _
        _ ≤ LG * (‖u (k - 1) - u k‖ + ‖v (k - 1) - v k‖) + LH * ‖v (k - 1) - v k‖ +
              γ * ‖P.B‖ * L0 * ‖u (k - 1) - u k‖ := by linarith
        _ = (LG + γ * ‖P.B‖ * L0) * ‖u (k - 1) - u k‖ + (LG + LH) * ‖v (k - 1) - v k‖ := by ring
    have hgl : 0 < γ * NAPPAL.KL.lamMin P := mul_pos hγ hlam
    set A := LG + γ * ‖P.B‖ * L0
    set Bcoef := LG + LH
    set x := ‖u (k - 1) - u k‖
    set y := ‖v (k - 1) - v k‖
    set dvn := ‖v k - vhat‖
    have hr_bound : -⟪r, v k - vhat⟫_ℝ ≤ A * x * dvn + Bcoef * y * dvn := by
      have h1 : -⟪r, v k - vhat⟫_ℝ ≤ (A * x + Bcoef * y) * dvn := by
        calc -⟪r, v k - vhat⟫_ℝ ≤ |⟪r, v k - vhat⟫_ℝ| := neg_le_abs _
          _ ≤ ‖r‖ * dvn := abs_real_inner_le_norm _ _
          _ ≤ (A * x + Bcoef * y) * dvn := mul_le_mul_of_nonneg_right hr_norm (norm_nonneg _)
      linarith
    have hyoung1 : A * x * dvn ≤
        NAPPAL.KL.c1 P LG L0 γ * x ^ 2 + (γ * NAPPAL.KL.lamMin P / 28) * dvn ^ 2 := by
      unfold NAPPAL.KL.c1
      have hsq : 0 ≤ (14 * A * x - γ * NAPPAL.KL.lamMin P * dvn) ^ 2 := sq_nonneg _
      have hmul : 28 * (γ * NAPPAL.KL.lamMin P) * (A * x * dvn) ≤
          28 * (γ * NAPPAL.KL.lamMin P) *
            (7 * A ^ 2 / (γ * NAPPAL.KL.lamMin P) * x ^ 2 +
              γ * NAPPAL.KL.lamMin P / 28 * dvn ^ 2) := by
        have heq : 28 * (γ * NAPPAL.KL.lamMin P) *
            (7 * A ^ 2 / (γ * NAPPAL.KL.lamMin P) * x ^ 2 +
              γ * NAPPAL.KL.lamMin P / 28 * dvn ^ 2) =
            196 * A ^ 2 * x ^ 2 + (γ * NAPPAL.KL.lamMin P) ^ 2 * dvn ^ 2 := by
          field_simp [hgl.ne']
          ring
        rw [heq]
        nlinarith [hsq]
      nlinarith
    have hyoung2 : Bcoef * y * dvn ≤
        NAPPAL.KL.c2 P LG LH γ * y ^ 2 + (γ * NAPPAL.KL.lamMin P / 28) * dvn ^ 2 := by
      unfold NAPPAL.KL.c2
      have hsq : 0 ≤ (14 * Bcoef * y - γ * NAPPAL.KL.lamMin P * dvn) ^ 2 := sq_nonneg _
      have hmul : 28 * (γ * NAPPAL.KL.lamMin P) * (Bcoef * y * dvn) ≤
          28 * (γ * NAPPAL.KL.lamMin P) *
            (7 * Bcoef ^ 2 / (γ * NAPPAL.KL.lamMin P) * y ^ 2 +
              γ * NAPPAL.KL.lamMin P / 28 * dvn ^ 2) := by
        have heq : 28 * (γ * NAPPAL.KL.lamMin P) *
            (7 * Bcoef ^ 2 / (γ * NAPPAL.KL.lamMin P) * y ^ 2 +
              γ * NAPPAL.KL.lamMin P / 28 * dvn ^ 2) =
            196 * Bcoef ^ 2 * y ^ 2 + (γ * NAPPAL.KL.lamMin P) ^ 2 * dvn ^ 2 := by
          field_simp [hgl.ne']
          ring
        rw [heq]
        nlinarith [hsq]
      nlinarith
    have hB_lb : (γ / 2) * (NAPPAL.KL.lamMin P * dvn ^ 2) ≤ (γ / 2) * ‖P.B (v k - vhat)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (lamMin_mul_sq_le P (v k - vhat)) (by positivity)
    have hcoeff : ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2) * dvn ^ 2 =
        (γ / 2) * (NAPPAL.KL.lamMin P * dvn ^ 2) - ((LG + LH) / 2) * dvn ^ 2 -
          (γ * NAPPAL.KL.lamMin P / 28) * dvn ^ 2 - (γ * NAPPAL.KL.lamMin P / 28) * dvn ^ 2 := by
      ring
    show NAPPAL.KL.F P (u k) vhat +
        ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2) * dvn ^ 2 +
        1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 ≤
      NAPPAL.KL.F P (u k) (v k) + ⟪p k, NAPPAL.KL.Theta P (u k) + P.B (v k)⟫_ℝ +
        γ / 2 * ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖ ^ 2 +
        NAPPAL.KL.c1 P LG L0 γ * x ^ 2 + NAPPAL.KL.c2 P LG LH γ * y ^ 2 +
        1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2
    rw [hinner_p, hres, hcoeff]
    linarith [hdes', hr_inner, hr_bound, hyoung1, hyoung2, hB_lb]

/-- One decoupled quadratic-penalty step producing an interior minimizer `(x, y)` and multiplier `b`. -/
private lemma penalty_step {n : ℕ}
    {J : NAPPAL.KL.E n → ℝ} {U : Set (NAPPAL.KL.E n)} {ubar g₀ : NAPPAL.KL.E n}
    {K : NNReal} {r₁ ρ ε : ℝ}
    (hubar : ubar ∈ U) (hU_conv : Convex ℝ U) (hU_closed : IsClosed U)
    (hKball : LipschitzOnWith K J (Metric.closedBall ubar r₁))
    (hε_pos : 0 < ε) (hρ_pos : 0 < ρ) (hρ_le : ρ ≤ r₁)
    (hρ_ineq : ∀ y ∈ U ∩ Metric.closedBall ubar ρ,
      J ubar ≤ J y + ⟪g₀, y - ubar⟫_ℝ + ε * ‖y - ubar‖) :
    ∃ x y b : NAPPAL.KL.E n,
      ‖x - ubar‖ < 2 * ε ∧
      ‖y - ubar‖ < ε ∧
      ‖b‖ ≤ 2 * ((K : ℝ) + ‖g₀‖ + 1) ∧
      NonconvexSplitting.Shared.IsRegularSubgrad (fun z => (J z : EReal)) x (-(g₀ + b)) ∧
      ∀ z ∈ U, ⟪b, z - y⟫_ℝ ≤ (ε + ‖y - ubar‖) * ‖z - y‖ := by
  set C : ℝ := (K : ℝ) + ‖g₀‖ + 1
  have hC_pos : 0 < C := by positivity
  obtain ⟨κ, hκ_pos, hκ1, hκ2, hκ3, hκ4⟩ : ∃ κ : ℝ,
      0 < κ ∧ 8 * C / ρ ≤ κ ∧ 32 * C ^ 2 / ρ ^ 2 ≤ κ ∧
        4 * C / ε ≤ κ ∧ 8 * C ^ 2 / ε ^ 2 ≤ κ := by
    refine ⟨max 1 (max (8 * C / ρ) (max (32 * C ^ 2 / ρ ^ 2)
      (max (4 * C / ε) (8 * C ^ 2 / ε ^ 2)))), ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_of_lt_of_le one_pos (le_max_left _ _)
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    · exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
    · exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _)))
  let Ψ : NAPPAL.KL.E n × NAPPAL.KL.E n → ℝ := fun xy =>
    J xy.1 + ⟪g₀, xy.1 - ubar⟫_ℝ + (κ / 2) * ‖xy.1 - xy.2‖ ^ 2 +
      ε * ‖xy.2 - ubar‖ + (1 / 2) * ‖xy.2 - ubar‖ ^ 2
  set S1 : Set (NAPPAL.KL.E n) := Metric.closedBall ubar ρ
  set S2 : Set (NAPPAL.KL.E n) := U ∩ Metric.closedBall ubar ρ
  set S : Set (NAPPAL.KL.E n × NAPPAL.KL.E n) := S1 ×ˢ S2
  have hS_ne : S.Nonempty := ⟨(ubar, ubar), by
    simp [S, S1, S2, hubar, le_of_lt hρ_pos]⟩
  have hS1_comp : IsCompact S1 := isCompact_closedBall ubar ρ
  have hS2_comp : IsCompact S2 := hS1_comp.inter_left hU_closed
  have hS_comp : IsCompact S := hS1_comp.prod hS2_comp
  have hJ_cont : ContinuousOn J S1 :=
    (hKball.mono (Metric.closedBall_subset_closedBall hρ_le)).continuousOn
  have hΨ_cont : ContinuousOn Ψ S := by
    have h1 : ContinuousOn (fun xy : NAPPAL.KL.E n × NAPPAL.KL.E n => J xy.1) S :=
      hJ_cont.comp continuous_fst.continuousOn (fun _ h => h.1)
    have h2 : ContinuousOn (fun xy : NAPPAL.KL.E n × NAPPAL.KL.E n =>
        ⟪g₀, xy.1 - ubar⟫_ℝ) S := (by fun_prop : Continuous _).continuousOn
    have h3 : ContinuousOn (fun xy : NAPPAL.KL.E n × NAPPAL.KL.E n =>
        (κ / 2) * ‖xy.1 - xy.2‖ ^ 2) S := (by fun_prop : Continuous _).continuousOn
    have h4 : ContinuousOn (fun xy : NAPPAL.KL.E n × NAPPAL.KL.E n =>
        ε * ‖xy.2 - ubar‖) S := (by fun_prop : Continuous _).continuousOn
    have h5 : ContinuousOn (fun xy : NAPPAL.KL.E n × NAPPAL.KL.E n =>
        (1 / 2) * ‖xy.2 - ubar‖ ^ 2) S := (by fun_prop : Continuous _).continuousOn
    exact (((h1.add h2).add h3).add h4).add h5
  obtain ⟨⟨x, y⟩, hxyS, hxy_min⟩ := hS_comp.exists_isMinOn hS_ne hΨ_cont
  have hxS1 : x ∈ S1 := hxyS.1
  have hyS2 : y ∈ S2 := hxyS.2
  have hΨ_le : Ψ (x, y) ≤ J ubar := by
    have hle := hxy_min (show (ubar, ubar) ∈ S by simp [S, S1, S2, hubar, le_of_lt hρ_pos])
    simpa [Ψ] using hle
  have hJ_diff : J y - J x ≤ (K : ℝ) * ‖x - y‖ := by
    have hlip_xy := (hKball.mono (Metric.closedBall_subset_closedBall hρ_le)).dist_le_mul x hxS1 y hyS2.2
    rw [Real.dist_eq, dist_eq_norm] at hlip_xy
    have : J y - J x ≤ |J x - J y| := by rw [abs_sub_comm]; exact le_abs_self _
    linarith
  have hinner_diff : ⟪g₀, y - ubar⟫_ℝ - ⟪g₀, x - ubar⟫_ℝ ≤ ‖g₀‖ * ‖x - y‖ := by
    have heq : ⟪g₀, y - ubar⟫_ℝ - ⟪g₀, x - ubar⟫_ℝ = ⟪g₀, y - x⟫_ℝ := by
      rw [← inner_sub_right]; congr 1; abel
    rw [heq]
    calc ⟪g₀, y - x⟫_ℝ ≤ ‖g₀‖ * ‖y - x‖ := real_inner_le_norm _ _
      _ = ‖g₀‖ * ‖x - y‖ := by rw [norm_sub_rev]
  have hJ_y : J ubar ≤ J y + ⟪g₀, y - ubar⟫_ℝ + ε * ‖y - ubar‖ := hρ_ineq y hyS2
  have hquad : (1 / 2) * ‖y - ubar‖ ^ 2 + (κ / 2) * ‖x - y‖ ^ 2 ≤ C * ‖x - y‖ := by
    dsimp only [Ψ] at hΨ_le
    nlinarith [norm_nonneg (x - y)]
  have hκ_xy : κ * ‖x - y‖ ≤ 2 * C := by
    by_cases h0 : ‖x - y‖ = 0
    · simp [h0]; linarith
    · have hpos : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith [sq_nonneg ‖y - ubar‖]
  have hxy_lt_ρ : ‖x - y‖ < ρ / 2 := by
    have h1 : ‖x - y‖ ≤ 2 * C / κ := (le_div_iff₀ hκ_pos).mpr (by linarith)
    have h2 : 2 * C / κ < ρ / 2 := by
      rw [div_lt_iff₀ hκ_pos]
      have : 8 * C ≤ κ * ρ := (div_le_iff₀ hρ_pos).mp hκ1
      nlinarith
    linarith
  have hxy_lt_ε : ‖x - y‖ < ε := by
    have h1 : ‖x - y‖ ≤ 2 * C / κ := (le_div_iff₀ hκ_pos).mpr (by linarith)
    have h2 : 2 * C / κ < ε := by
      rw [div_lt_iff₀ hκ_pos]
      have : 4 * C ≤ κ * ε := (div_le_iff₀ hε_pos).mp hκ3
      nlinarith
    linarith
  have hy_sq : ‖y - ubar‖ ^ 2 ≤ 4 * C ^ 2 / κ := by
    have h1 : ‖x - y‖ ≤ 2 * C / κ := (le_div_iff₀ hκ_pos).mpr (by linarith)
    have h2 : (1 / 2) * ‖y - ubar‖ ^ 2 ≤ C * ‖x - y‖ := by
      nlinarith [sq_nonneg ‖x - y‖, hκ_pos]
    have h3 : C * ‖x - y‖ ≤ 2 * C ^ 2 / κ := by
      calc C * ‖x - y‖ ≤ C * (2 * C / κ) := mul_le_mul_of_nonneg_left h1 hC_pos.le
        _ = 2 * C ^ 2 / κ := by ring
    have h4 : 2 * (2 * C ^ 2 / κ) = 4 * C ^ 2 / κ := by ring
    linarith
  have hy_lt_ρ : ‖y - ubar‖ < ρ / 2 := by
    have h1 : 4 * C ^ 2 / κ < (ρ / 2) ^ 2 := by
      rw [div_lt_iff₀ hκ_pos]
      have hmul : 32 * C ^ 2 ≤ κ * ρ ^ 2 := (div_le_iff₀ (sq_pos_of_pos hρ_pos)).mp hκ2
      have hpos : 0 < C ^ 2 := sq_pos_of_pos hC_pos
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) (lt_of_le_of_lt hy_sq h1)
  have hy_lt_ε : ‖y - ubar‖ < ε := by
    have h1 : 4 * C ^ 2 / κ < ε ^ 2 := by
      rw [div_lt_iff₀ hκ_pos]
      have hmul : 8 * C ^ 2 ≤ κ * ε ^ 2 := (div_le_iff₀ (sq_pos_of_pos hε_pos)).mp hκ4
      have hpos : 0 < C ^ 2 := sq_pos_of_pos hC_pos
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hε_pos.le (lt_of_le_of_lt hy_sq h1)
  have hx_lt_ρ : ‖x - ubar‖ < ρ := by
    calc ‖x - ubar‖ = ‖(x - y) + (y - ubar)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y - ubar‖ := norm_add_le _ _
      _ < ρ / 2 + ρ / 2 := add_lt_add hxy_lt_ρ hy_lt_ρ
      _ = ρ := add_halves ρ
  have hx_lt_2ε : ‖x - ubar‖ < 2 * ε := by
    calc ‖x - ubar‖ = ‖(x - y) + (y - ubar)‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y - ubar‖ := norm_add_le _ _
      _ < ε + ε := add_lt_add hxy_lt_ε hy_lt_ε
      _ = 2 * ε := by ring
  set b : NAPPAL.KL.E n := κ • (x - y)
  have hb_norm : ‖b‖ ≤ 2 * C := by
    simpa [b, norm_smul, Real.norm_of_nonneg hκ_pos.le] using hκ_xy
  refine ⟨x, y, b, hx_lt_2ε, hy_lt_ε, hb_norm, ?_, ?_⟩
  · refine ⟨EReal.coe_ne_top _, ?_⟩
    intro η hη
    set δ' := min (ρ - ‖x - ubar‖) (2 * η / κ)
    have hδ'_pos : 0 < δ' := lt_min (by linarith) (by positivity)
    rw [Metric.eventually_nhds_iff]
    refine ⟨δ', hδ'_pos, ?_⟩
    intro z hz
    rw [dist_eq_norm] at hz
    have hzS1 : z ∈ S1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖z - ubar‖ = ‖(z - x) + (x - ubar)‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x - ubar‖ := norm_add_le _ _
        _ ≤ δ' + ‖x - ubar‖ := by linarith
        _ ≤ ρ := by linarith [min_le_left (ρ - ‖x - ubar‖) (2 * η / κ)]
    have hmin_z : Ψ (x, y) ≤ Ψ (z, y) := hxy_min ⟨hzS1, hyS2⟩
    have hsq_exp : (κ / 2) * ‖z - y‖ ^ 2 - (κ / 2) * ‖x - y‖ ^ 2 =
        κ * ⟪x - y, z - x⟫_ℝ + (κ / 2) * ‖z - x‖ ^ 2 := by
      have hzy : z - y = (x - y) + (z - x) := by abel
      rw [hzy, norm_add_sq_real]; ring
    have hlin_exp : ⟪g₀, z - ubar⟫_ℝ - ⟪g₀, x - ubar⟫_ℝ = ⟪g₀, z - x⟫_ℝ := by
      rw [← inner_sub_right]; congr 1; abel
    have hquad_small : (κ / 2) * ‖z - x‖ ^ 2 ≤ η * ‖z - x‖ := by
      have hzx_le : ‖z - x‖ ≤ 2 * η / κ := le_trans hz.le (min_le_right _ _)
      have hκzx : κ * ‖z - x‖ ≤ 2 * η := by
        have := (le_div_iff₀ hκ_pos).mp hzx_le
        linarith
      have hmul := mul_le_mul_of_nonneg_right hκzx (norm_nonneg (z - x))
      have heq1 : (κ * ‖z - x‖) * ‖z - x‖ = 2 * ((κ / 2) * ‖z - x‖ ^ 2) := by ring
      have heq2 : (2 * η) * ‖z - x‖ = 2 * (η * ‖z - x‖) := by ring
      linarith
    have hreal : J x + (⟪-(g₀ + b), z - x⟫_ℝ - η * ‖z - x‖) ≤ J z := by
      have hinner_ab : ⟪-(g₀ + b), z - x⟫_ℝ = -⟪g₀, z - x⟫_ℝ - κ * ⟪x - y, z - x⟫_ℝ := by
        simp [b, inner_neg_left, inner_add_left, inner_smul_left]; ring
      rw [hinner_ab]
      dsimp only [Ψ] at hmin_z
      linarith [hmin_z, hsq_exp, hlin_exp, hquad_small]
    dsimp only
    exact_mod_cast hreal
  · intro z hzU
    by_cases hzy : z = y
    · simp [hzy]
    · have hzy_pos : 0 < ‖z - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzy)
      have hbound : ∀ t : ℝ, 0 < t → t ≤ 1 → t * ‖z - y‖ ≤ ρ - ‖y - ubar‖ →
          ⟪b, z - y⟫_ℝ ≤ (ε + ‖y - ubar‖) * ‖z - y‖ + ((κ + 1) / 2 * ‖z - y‖ ^ 2) * t := by
        intro t ht_pos ht_le1 ht_ball
        set yt : NAPPAL.KL.E n := y + t • (z - y)
        have hyt_eq : yt = (1 - t) • y + t • z := by dsimp [yt]; module
        have hytU : yt ∈ U := by
          rw [hyt_eq]
          exact hU_conv hyS2.1 hzU (by linarith) ht_pos.le (by ring)
        have hytB : yt ∈ Metric.closedBall ubar ρ := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          calc ‖yt - ubar‖ = ‖(y - ubar) + t • (z - y)‖ := by dsimp [yt]; congr 1; abel
            _ ≤ ‖y - ubar‖ + ‖t • (z - y)‖ := norm_add_le _ _
            _ = ‖y - ubar‖ + t * ‖z - y‖ := by rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
            _ ≤ ρ := by linarith
        have hmin_t : Ψ (x, y) ≤ Ψ (x, yt) := hxy_min ⟨hxS1, ⟨hytU, hytB⟩⟩
        have hsq1 : (κ / 2) * ‖x - yt‖ ^ 2 - (κ / 2) * ‖x - y‖ ^ 2 =
            -t * (κ * ⟪x - y, z - y⟫_ℝ) + (κ / 2) * ‖z - y‖ ^ 2 * t ^ 2 := by
          have heq : x - yt = (x - y) - t • (z - y) := by dsimp [yt]; abel
          rw [heq, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg ht_pos.le]
          ring
        have htri : ε * ‖yt - ubar‖ - ε * ‖y - ubar‖ ≤ t * (ε * ‖z - y‖) := by
          have h1 : ‖yt - ubar‖ ≤ ‖y - ubar‖ + t * ‖z - y‖ := by
            calc ‖yt - ubar‖ = ‖(y - ubar) + t • (z - y)‖ := by dsimp [yt]; congr 1; abel
              _ ≤ ‖y - ubar‖ + ‖t • (z - y)‖ := norm_add_le _ _
              _ = ‖y - ubar‖ + t * ‖z - y‖ := by rw [norm_smul, Real.norm_of_nonneg ht_pos.le]
          have h2 := mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mpr h1) hε_pos.le
          linarith
        have hsq2 : (1 / 2) * ‖yt - ubar‖ ^ 2 - (1 / 2) * ‖y - ubar‖ ^ 2 =
            t * ⟪y - ubar, z - y⟫_ℝ + (1 / 2) * ‖z - y‖ ^ 2 * t ^ 2 := by
          have heq : yt - ubar = (y - ubar) + t • (z - y) := by dsimp [yt]; abel
          rw [heq, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg ht_pos.le]
          ring
        have hy_cs : t * ⟪y - ubar, z - y⟫_ℝ ≤ t * (‖y - ubar‖ * ‖z - y‖) :=
          mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) ht_pos.le
        have hb_in : ⟪b, z - y⟫_ℝ = κ * ⟪x - y, z - y⟫_ℝ := by
          simp [b, inner_smul_left]
        dsimp only [Ψ] at hmin_t
        have hexp_rhs : t * ((ε + ‖y - ubar‖) * ‖z - y‖ + ((κ + 1) / 2 * ‖z - y‖ ^ 2) * t) =
            t * (ε * ‖z - y‖) + t * (‖y - ubar‖ * ‖z - y‖) +
              (κ / 2) * ‖z - y‖ ^ 2 * t ^ 2 + (1 / 2) * ‖z - y‖ ^ 2 * t ^ 2 := by ring
        have hmul : t * ⟪b, z - y⟫_ℝ ≤
            t * ((ε + ‖y - ubar‖) * ‖z - y‖ + ((κ + 1) / 2 * ‖z - y‖ ^ 2) * t) := by
          rw [hb_in, hexp_rhs]
          linarith [hmin_t, hsq1, htri, hsq2, hy_cs]
        exact le_of_mul_le_mul_left hmul ht_pos
      apply le_of_forall_pos_le_add
      intro η hη
      set M : ℝ := (κ + 1) / 2 * ‖z - y‖ ^ 2
      have hM_pos : 0 < M := by positivity
      set t : ℝ := min 1 (min ((ρ - ‖y - ubar‖) / ‖z - y‖) (η / M))
      have ht_pos : 0 < t := lt_min one_pos (lt_min (div_pos (by linarith) hzy_pos) (div_pos hη hM_pos))
      have ht_le1 : t ≤ 1 := min_le_left _ _
      have ht_ball : t * ‖z - y‖ ≤ ρ - ‖y - ubar‖ := by
        have : t ≤ (ρ - ‖y - ubar‖) / ‖z - y‖ := le_trans (min_le_right _ _) (min_le_left _ _)
        exact (le_div_iff₀ hzy_pos).mp this
      have ht_η : M * t ≤ η := by
        have : t ≤ η / M := le_trans (min_le_right _ _) (min_le_right _ _)
        calc M * t ≤ M * (η / M) := mul_le_mul_of_nonneg_left this hM_pos.le
          _ = η := mul_div_cancel₀ η hM_pos.ne'
      linarith [hbound t ht_pos ht_le1 ht_ball]

/-- Decoupled quadratic-penalty variational principle: if `ubar ∈ U` globally minimizes `f + J`
over a closed convex set `U`, with `f` differentiable at `ubar` (gradient `g₀`) and `J` locally
Lipschitz near `ubar`, then `0 ∈ g₀ + ∂J(ubar) + N_U(ubar)`. -/
private lemma exists_subgrad_normalCone_of_isMinOn {n : ℕ}
    {f J : NAPPAL.KL.E n → ℝ} {U : Set (NAPPAL.KL.E n)} {ubar g₀ : NAPPAL.KL.E n}
    (hubar : ubar ∈ U) (hU_conv : Convex ℝ U) (hU_closed : IsClosed U)
    (hJ_lip : ∃ K : NNReal, ∃ t ∈ 𝓝 ubar, LipschitzOnWith K J t)
    (hf : HasGradientAt f g₀ ubar)
    (hmin : ∀ x ∈ U, f ubar + J ubar ≤ f x + J x) :
    ∃ a ∈ NonconvexSplitting.Shared.LimitingSubdiff (fun x => (J x : EReal)) ubar,
      ∃ b ∈ NAPPAL.KL.normalCone U ubar, g₀ + a + b = 0 := by
  obtain ⟨K, t, ht, hKlip⟩ := hJ_lip
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.mem_nhds_iff.mp ht
  have hKball : LipschitzOnWith K J (Metric.closedBall ubar (r₀ / 2)) :=
    hKlip.mono ((Metric.closedBall_subset_ball (half_lt_self hr₀_pos)).trans hr₀_sub)
  set r₁ := r₀ / 2
  have hr₁_pos : 0 < r₁ := half_pos hr₀_pos
  set C : ℝ := (K : ℝ) + ‖g₀‖ + 1
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r₁ ∧
      ∀ y ∈ U ∩ Metric.closedBall ubar ρ,
        J ubar ≤ J y + ⟪g₀, y - ubar⟫_ℝ + ε * ‖y - ubar‖ := by
    intro ε hε
    have hfderiv := hf.hasFDerivAt
    have ho : ∀ᶠ y in 𝓝 ubar,
        ‖f y - f ubar - ⟪g₀, y - ubar⟫_ℝ‖ ≤ ε * ‖y - ubar‖ := by
      have h1 := hfderiv.isLittleO.bound hε
      filter_upwards [h1] with y hy
      simpa [InnerProductSpace.toDual_apply_apply] using hy
    obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.eventually_nhds_iff.mp ho
    refine ⟨min r₁ (δ / 2), lt_min hr₁_pos (half_pos hδ_pos), min_le_left _ _, ?_⟩
    intro y ⟨hyU, hyB⟩
    have hy_dist : dist y ubar < δ := lt_of_le_of_lt (Metric.mem_closedBall.mp hyB)
      (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ_pos))
    have hfy := hδ_sub hy_dist
    have hfy' : f y - f ubar - ⟪g₀, y - ubar⟫_ℝ ≤ ε * ‖y - ubar‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hfy)
    have hmy := hmin y hyU
    linarith
  have hstep : ∀ m : ℕ, ∃ x y b : NAPPAL.KL.E n,
      ‖x - ubar‖ < 2 * (1 / ((m : ℝ) + 1)) ∧
      ‖y - ubar‖ < 1 / ((m : ℝ) + 1) ∧
      ‖b‖ ≤ 2 * C ∧
      NonconvexSplitting.Shared.IsRegularSubgrad (fun z => (J z : EReal)) x (-(g₀ + b)) ∧
      ∀ z ∈ U, ⟪b, z - y⟫_ℝ ≤ (1 / ((m : ℝ) + 1) + ‖y - ubar‖) * ‖z - y‖ := by
    intro m
    have hε_pos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨ρ, hρ_pos, hρ_le, hρ_ineq⟩ := happrox (1 / ((m : ℝ) + 1)) hε_pos
    exact penalty_step hubar hU_conv hU_closed hKball hε_pos hρ_pos hρ_le hρ_ineq
  choose xs ys bs hxs hys hbs hreg hnc using hstep
  have hbdd_b : ∀ m, bs m ∈ Metric.closedBall (0 : NAPPAL.KL.E n) (2 * C) := by
    intro m; simp [Metric.mem_closedBall, hbs m]
  obtain ⟨b, -, φ, hφ_mono, hφ_lim⟩ := (isCompact_closedBall (0 : NAPPAL.KL.E n) (2 * C)).tendsto_subseq hbdd_b
  have h1m : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hx_lim : Tendsto xs atTop (𝓝 ubar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun m => norm_nonneg _) (fun m => (hxs m).le) ?_
    simpa using h1m.const_mul 2
  have hy_lim : Tendsto ys atTop (𝓝 ubar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun m => norm_nonneg _) (fun m => (hys m).le) h1m
  have hxφ_lim : Tendsto (xs ∘ φ) atTop (𝓝 ubar) := hx_lim.comp hφ_mono.tendsto_atTop
  have hyφ_lim : Tendsto (ys ∘ φ) atTop (𝓝 ubar) := hy_lim.comp hφ_mono.tendsto_atTop
  have hJ_cont_ubar : ContinuousAt J ubar :=
    hKlip.continuousOn.continuousAt ht
  have hJx_lim : Tendsto (fun l => (J (xs (φ l)) : EReal)) atTop (𝓝 (J ubar : EReal)) :=
    (continuous_coe_real_ereal.continuousAt.tendsto.comp (hJ_cont_ubar.tendsto.comp hxφ_lim))
  have ha_lim : Tendsto (fun l => -(g₀ + bs (φ l))) atTop (𝓝 (-(g₀ + b))) :=
    (tendsto_const_nhds.add hφ_lim).neg
  have ha_mem : -(g₀ + b) ∈ NonconvexSplitting.Shared.LimitingSubdiff (fun x => (J x : EReal)) ubar :=
    ⟨EReal.coe_ne_top _, xs ∘ φ, fun l => -(g₀ + bs (φ l)), hxφ_lim, hJx_lim, ha_lim,
      fun l => hreg (φ l)⟩
  have hb_mem : b ∈ NAPPAL.KL.normalCone U ubar := by
    refine ⟨hubar, ?_⟩
    intro z hzU
    have hlhs : Tendsto (fun l => ⟪bs (φ l), z - ys (φ l)⟫_ℝ) atTop (𝓝 ⟪b, z - ubar⟫_ℝ) :=
      hφ_lim.inner (tendsto_const_nhds.sub hyφ_lim)
    have hrhs : Tendsto (fun l => (1 / ((φ l : ℝ) + 1) + ‖ys (φ l) - ubar‖) * ‖z - ys (φ l)‖)
        atTop (𝓝 ((0 + 0) * ‖z - ubar‖)) := by
      refine Tendsto.mul ?_ (tendsto_const_nhds.sub hyφ_lim).norm
      exact (h1m.comp hφ_mono.tendsto_atTop).add (tendsto_iff_norm_sub_tendsto_zero.mp hyφ_lim)
    rw [zero_add, zero_mul] at hrhs
    exact le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall (fun l => hnc (φ l) z hzU))
  exact ⟨-(g₀ + b), ha_mem, b, hb_mem, by abel⟩

private lemma part_v_cluster {n d m : ℕ} (P : NAPPAL.KL.Problem n d m)
    (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ) (K : NAPPAL.KL.E n → ℝ)
    (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p)
    (Λstar Mε : ℝ) (hinv_ε_le : ∀ k, 1 / ε k ≤ Mε)
    (hdu_tendsto : Tendsto (fun k => ‖u k - u (k + 1)‖) atTop (𝓝 0))
    (hdv_tendsto : Tendsto (fun k => ‖v k - v (k + 1)‖) atTop (𝓝 0))
    (hdp_tendsto : Tendsto (fun k => ‖p k - p (k + 1)‖) atTop (𝓝 0))
    (hres_tendsto : Tendsto (fun k => NAPPAL.KL.Theta P (u k) + P.B (v k)) atTop (𝓝 0))
    (haug_tendsto : Tendsto (fun k => NAPPAL.KL.augLag P γ (u k, v k, p k)) atTop (𝓝 Λstar))
    (wbar : NAPPAL.KL.W n d m)
    (hcl : MapClusterPt wbar atTop (fun k => ((u k, v k, p k) : NAPPAL.KL.W n d m))) :
    NAPPAL.KL.IsStationary P γ wbar ∧ NAPPAL.KL.augLag P γ wbar = Λstar := by
  have hA1 := hrun.1
  have hA2 := hrun.2.1
  have hN := hrun.2.2.1
  have hσ : 0 < σ := hN.2.1
  have hβ : 0 < β := hA2.2.1
  have hLK : 0 ≤ LK := hA2.2.2.2.1
  have h41b := (NAPPAL.Rate.lemma_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hA1 hA2 hN).2.1
  rcases wbar with ⟨ubar, vbar, pbar⟩
  obtain ⟨φ0, hφ0_mono, hφ0_lim⟩ := hcl.tendsto_subseq
  let ψ : ℕ → ℕ := fun j => φ0 (j + 1) - 1
  have hψ_succ : ∀ j, ψ j + 1 = φ0 (j + 1) := by
    intro j
    have hge1 : 1 ≤ φ0 (j + 1) := lt_of_le_of_lt (Nat.zero_le _) (hφ0_mono (Nat.zero_lt_succ j))
    exact Nat.sub_add_cancel hge1
  have hψ_tendsto : Tendsto ψ atTop atTop := by
    have h1 : Tendsto (fun j => φ0 (j + 1)) atTop atTop :=
      hφ0_mono.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
    rw [tendsto_atTop] at h1 ⊢
    intro b
    filter_upwards [h1 (b + 1)] with j hj
    have := hψ_succ j
    omega
  have hw_succ : Tendsto (fun j => ((u (ψ j + 1), v (ψ j + 1), p (ψ j + 1)) : NAPPAL.KL.W n d m))
      atTop (𝓝 (ubar, vbar, pbar)) :=
    (hφ0_lim.comp (tendsto_add_atTop_nat 1)).congr (fun j => by simp [hψ_succ])
  have hu_succ : Tendsto (fun j => u (ψ j + 1)) atTop (𝓝 ubar) :=
    continuous_fst.continuousAt.tendsto.comp hw_succ
  have hv_succ : Tendsto (fun j => v (ψ j + 1)) atTop (𝓝 vbar) :=
    (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hw_succ
  have hp_succ : Tendsto (fun j => p (ψ j + 1)) atTop (𝓝 pbar) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp hw_succ
  have hu_lim : Tendsto (fun j => u (ψ j)) atTop (𝓝 ubar) := by
    have hd : Tendsto (fun j => u (ψ j) - u (ψ j + 1)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (hdu_tendsto.comp hψ_tendsto)
    simpa using hd.add hu_succ
  have hv_lim : Tendsto (fun j => v (ψ j)) atTop (𝓝 vbar) := by
    have hd : Tendsto (fun j => v (ψ j) - v (ψ j + 1)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (hdv_tendsto.comp hψ_tendsto)
    simpa using hd.add hv_succ
  have hp_lim : Tendsto (fun j => p (ψ j)) atTop (𝓝 pbar) := by
    have hd : Tendsto (fun j => p (ψ j) - p (ψ j + 1)) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (hdp_tendsto.comp hψ_tendsto)
    simpa using hd.add hp_succ
  have hubar_U : ubar ∈ P.U :=
    hA1.2.2.1.2.2.2.mem_of_tendsto hu_succ (Eventually.of_forall (fun j => (hN.2.2.2 (ψ j)).2.1.1))
  obtain ⟨KJ, tJ, htJ, hKJ⟩ := hA1.2.2.1.2.1 ubar hubar_U
  have hJ_cont : ContinuousAt P.J ubar := hKJ.continuousOn.continuousAt htJ
  have hTheta_cont : Continuous (NAPPAL.KL.Theta P) :=
    (hA1.2.2.2.1.1.add hA1.2.2.2.1.2.1).continuous
  -- 1. Feasibility
  have hfeas : NAPPAL.KL.Theta P ubar + P.B vbar = 0 := by
    have h1 : Tendsto (fun j => NAPPAL.KL.Theta P (u (ψ j + 1)) + P.B (v (ψ j + 1)))
        atTop (𝓝 (NAPPAL.KL.Theta P ubar + P.B vbar)) :=
      (hTheta_cont.continuousAt.tendsto.comp hu_succ).add (P.B.continuous.continuousAt.tendsto.comp hv_succ)
    have h2 : Tendsto (fun j => NAPPAL.KL.Theta P (u (ψ j + 1)) + P.B (v (ψ j + 1)))
        atTop (𝓝 0) :=
      hres_tendsto.comp ((tendsto_add_atTop_nat 1).comp hψ_tendsto)
    exact tendsto_nhds_unique h1 h2
  -- 2. augLag = Λstar
  have haug_eq : NAPPAL.KL.augLag P γ (ubar, vbar, pbar) = Λstar := by
    have h1 : Tendsto (fun j => NAPPAL.KL.augLag P γ (u (ψ j + 1), v (ψ j + 1), p (ψ j + 1)))
        atTop (𝓝 (NAPPAL.KL.augLag P γ (ubar, vbar, pbar))) := by
      unfold NAPPAL.KL.augLag NAPPAL.KL.F
      dsimp only
      have hG_lim : Tendsto (fun j => P.G (u (ψ j + 1), v (ψ j + 1))) atTop (𝓝 (P.G (ubar, vbar))) :=
        hA1.1.1.continuous.continuousAt.tendsto.comp (hu_succ.prodMk_nhds hv_succ)
      have hJ_lim : Tendsto (fun j => P.J (u (ψ j + 1))) atTop (𝓝 (P.J ubar)) :=
        hJ_cont.tendsto.comp hu_succ
      have hH_lim : Tendsto (fun j => P.H (v (ψ j + 1))) atTop (𝓝 (P.H vbar)) :=
        hA1.2.1.1.continuous.continuousAt.tendsto.comp hv_succ
      have hr_lim : Tendsto (fun j => NAPPAL.KL.Theta P (u (ψ j + 1)) + P.B (v (ψ j + 1)))
          atTop (𝓝 (NAPPAL.KL.Theta P ubar + P.B vbar)) :=
        (hTheta_cont.continuousAt.tendsto.comp hu_succ).add (P.B.continuous.continuousAt.tendsto.comp hv_succ)
      exact (((hG_lim.add hJ_lim).add hH_lim).add (hp_succ.inner hr_lim)).add
        ((hr_lim.norm.pow 2).const_mul (γ / 2))
    have h2 : Tendsto (fun j => NAPPAL.KL.augLag P γ (u (ψ j + 1), v (ψ j + 1), p (ψ j + 1)))
        atTop (𝓝 Λstar) :=
      haug_tendsto.comp ((tendsto_add_atTop_nat 1).comp hψ_tendsto)
    exact tendsto_nhds_unique h1 h2
  -- 3. Stationarity in v
  have hgradV_lim : Tendsto (fun j => NAPPAL.KL.gradV P (u (ψ j)) (v (ψ j)))
      atTop (𝓝 (NAPPAL.KL.gradV P ubar vbar)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun j => gradV_lipschitz_joint hA1.1 (u (ψ j)) (v (ψ j)) ubar vbar) ?_
    have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hu_lim
    have h2 := tendsto_iff_norm_sub_tendsto_zero.mp hv_lim
    simpa using (h1.add h2).const_mul LG
  have hgradU_lim : Tendsto (fun j => NAPPAL.KL.gradU P (u (ψ j)) (v (ψ j)))
      atTop (𝓝 (NAPPAL.KL.gradU P ubar vbar)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun j => gradU_lipschitz_joint hA1.1 (u (ψ j)) (v (ψ j)) ubar vbar) ?_
    have h1 := tendsto_iff_norm_sub_tendsto_zero.mp hu_lim
    have h2 := tendsto_iff_norm_sub_tendsto_zero.mp hv_lim
    simpa using (h1.add h2).const_mul LG
  have hgradH_lim : Tendsto (fun j => gradient P.H (v (ψ j))) atTop (𝓝 (gradient P.H vbar)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun j => hA1.2.1.2.2 (v (ψ j)) vbar) ?_
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv_lim).const_mul LH
  have hv_stat : (0 : NAPPAL.KL.E d) = NAPPAL.KL.gradV P ubar vbar + gradient P.H vbar +
      ContinuousLinearMap.adjoint P.B (pbar + γ • (NAPPAL.KL.Theta P ubar + P.B vbar)) := by
    rw [hfeas, smul_zero, add_zero]
    have hlhs : Tendsto (fun j => ContinuousLinearMap.adjoint P.B (p (ψ j + 1)))
        atTop (𝓝 (ContinuousLinearMap.adjoint P.B pbar)) :=
      (ContinuousLinearMap.adjoint P.B).continuous.continuousAt.tendsto.comp hp_succ
    have hrhs : Tendsto (fun j =>
        -NAPPAL.KL.gradV P (u (ψ j)) (v (ψ j)) - gradient P.H (v (ψ j)) +
          γ • ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u (ψ j + 1)) - NAPPAL.KL.Theta P (u (ψ j))))
        atTop (𝓝 (-NAPPAL.KL.gradV P ubar vbar - gradient P.H vbar + 0)) := by
      refine (hgradV_lim.neg.sub hgradH_lim).add ?_
      have hth : Tendsto (fun j => NAPPAL.KL.Theta P (u (ψ j + 1)) - NAPPAL.KL.Theta P (u (ψ j)))
          atTop (𝓝 0) := by
        simpa using (hTheta_cont.continuousAt.tendsto.comp hu_succ).sub
          (hTheta_cont.continuousAt.tendsto.comp hu_lim)
      simpa using ((ContinuousLinearMap.adjoint P.B).continuous.continuousAt.tendsto.comp hth).const_smul γ
    have heq_seq : ∀ j, ContinuousLinearMap.adjoint P.B (p (ψ j + 1)) =
        -NAPPAL.KL.gradV P (u (ψ j)) (v (ψ j)) - gradient P.H (v (ψ j)) +
          γ • ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u (ψ j + 1)) - NAPPAL.KL.Theta P (u (ψ j))) := by
      intro j
      simpa using h41b (ψ j + 1) (Nat.succ_le_succ (Nat.zero_le _))
    have heq : ContinuousLinearMap.adjoint P.B pbar =
        -NAPPAL.KL.gradV P ubar vbar - gradient P.H vbar + 0 :=
      tendsto_nhds_unique hlhs (hrhs.congr (fun j => (heq_seq j).symm))
    rw [heq]; abel
  -- 4. Stationarity in u via subproblem (5) limit + penalty lemma
  have hq_lim : Tendsto (fun j => NAPPAL.Rate.qseq P γ u v p (ψ j)) atTop (𝓝 pbar) := by
    unfold NAPPAL.Rate.qseq
    have hr : Tendsto (fun j => NAPPAL.KL.Theta P (u (ψ j)) + P.B (v (ψ j))) atTop (𝓝 0) :=
      hres_tendsto.comp hψ_tendsto
    simpa using hp_lim.add (hr.const_smul γ)
  have hfderiv_Om_lim : Tendsto (fun j => fderiv ℝ P.Om (u (ψ j)))
      atTop (𝓝 (fderiv ℝ P.Om ubar)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun j => fderiv_Om_lipschitz hA1 (u (ψ j)) ubar) ?_
    simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hu_lim).const_mul (NAPPAL.KL.LOm LOmj)
  let f_lim : NAPPAL.KL.E n → ℝ := fun x =>
    ⟪NAPPAL.KL.gradU P ubar vbar, x⟫_ℝ +
      ⟪pbar, fderiv ℝ P.Om ubar x + P.Phi x⟫_ℝ +
      (LK * Mε / 2) * ‖x - ubar‖ ^ 2
  have hmin_lim : ∀ x ∈ P.U, f_lim ubar + P.J ubar ≤ f_lim x + P.J x := by
    intro x hxU
    have hle_j : ∀ j,
        ⟪NAPPAL.KL.gradU P (u (ψ j)) (v (ψ j)), u (ψ j + 1)⟫_ℝ + P.J (u (ψ j + 1)) +
          ⟪NAPPAL.Rate.qseq P γ u v p (ψ j),
            fderiv ℝ P.Om (u (ψ j)) (u (ψ j + 1)) + P.Phi (u (ψ j + 1))⟫_ℝ ≤
        ⟪NAPPAL.KL.gradU P (u (ψ j)) (v (ψ j)), x⟫_ℝ + P.J x +
          ⟪NAPPAL.Rate.qseq P γ u v p (ψ j),
            fderiv ℝ P.Om (u (ψ j)) x + P.Phi x⟫_ℝ +
          (LK * Mε / 2) * ‖x - u (ψ j)‖ ^ 2 := by
      intro j
      have hobj := (hN.2.2.2 (ψ j)).2.1.2 x hxU
      unfold NAPPAL.Rate.obj5 at hobj
      have hεk_pos : 0 < ε (ψ j) :=
        lt_of_lt_of_le (mul_pos hσ (hN.2.2.2 (ψ j)).1.1) (hN.2.2.2 (ψ j)).1.2.1
      have hbreg_nn : 0 ≤ NAPPAL.KL.bregman K (u (ψ j + 1)) (u (ψ j)) / ε (ψ j) :=
        div_nonneg (bregman_nonneg hA2.1 hβ hA2.2.2.1 _ _) hεk_pos.le
      have hbreg_ub : NAPPAL.KL.bregman K x (u (ψ j)) / ε (ψ j) ≤
          (LK * Mε / 2) * ‖x - u (ψ j)‖ ^ 2 := by
        have hbl := bregman_le hA2.1 hA2.2.2.2.2.1 x (u (ψ j))
        have hdiv : NAPPAL.KL.bregman K x (u (ψ j)) / ε (ψ j) ≤
            ((LK / 2) * ‖x - u (ψ j)‖ ^ 2) * (1 / ε (ψ j)) := by
          rw [div_eq_mul_one_div]
          exact mul_le_mul_of_nonneg_right hbl (one_div_nonneg.mpr hεk_pos.le)
        have hdiv2 : ((LK / 2) * ‖x - u (ψ j)‖ ^ 2) * (1 / ε (ψ j)) ≤
            ((LK / 2) * ‖x - u (ψ j)‖ ^ 2) * Mε :=
          mul_le_mul_of_nonneg_left (hinv_ε_le (ψ j)) (by positivity)
        linarith
      linarith
    have hOm_succ : Tendsto (fun j => fderiv ℝ P.Om (u (ψ j)) (u (ψ j + 1)))
        atTop (𝓝 (fderiv ℝ P.Om ubar ubar)) :=
      (isBoundedBilinearMap_apply.continuous.tendsto (fderiv ℝ P.Om ubar, ubar)).comp
        (hfderiv_Om_lim.prodMk_nhds hu_succ)
    have hOm_x : Tendsto (fun j => fderiv ℝ P.Om (u (ψ j)) x)
        atTop (𝓝 (fderiv ℝ P.Om ubar x)) :=
      (isBoundedBilinearMap_apply.continuous.tendsto (fderiv ℝ P.Om ubar, x)).comp
        (hfderiv_Om_lim.prodMk_nhds tendsto_const_nhds)
    have hPhi_succ : Tendsto (fun j => P.Phi (u (ψ j + 1))) atTop (𝓝 (P.Phi ubar)) :=
      hA1.2.2.2.1.2.1.continuous.continuousAt.tendsto.comp hu_succ
    have hlhs : Tendsto (fun j =>
        ⟪NAPPAL.KL.gradU P (u (ψ j)) (v (ψ j)), u (ψ j + 1)⟫_ℝ + P.J (u (ψ j + 1)) +
          ⟪NAPPAL.Rate.qseq P γ u v p (ψ j),
            fderiv ℝ P.Om (u (ψ j)) (u (ψ j + 1)) + P.Phi (u (ψ j + 1))⟫_ℝ)
        atTop (𝓝 (⟪NAPPAL.KL.gradU P ubar vbar, ubar⟫_ℝ + P.J ubar +
          ⟪pbar, fderiv ℝ P.Om ubar ubar + P.Phi ubar⟫_ℝ)) :=
      ((hgradU_lim.inner hu_succ).add (hJ_cont.tendsto.comp hu_succ)).add
        (hq_lim.inner (hOm_succ.add hPhi_succ))
    have hrhs : Tendsto (fun j =>
        ⟪NAPPAL.KL.gradU P (u (ψ j)) (v (ψ j)), x⟫_ℝ + P.J x +
          ⟪NAPPAL.Rate.qseq P γ u v p (ψ j),
            fderiv ℝ P.Om (u (ψ j)) x + P.Phi x⟫_ℝ +
          (LK * Mε / 2) * ‖x - u (ψ j)‖ ^ 2)
        atTop (𝓝 (⟪NAPPAL.KL.gradU P ubar vbar, x⟫_ℝ + P.J x +
          ⟪pbar, fderiv ℝ P.Om ubar x + P.Phi x⟫_ℝ +
          (LK * Mε / 2) * ‖x - ubar‖ ^ 2)) :=
      (((hgradU_lim.inner tendsto_const_nhds).add tendsto_const_nhds).add
        (hq_lim.inner (hOm_x.add tendsto_const_nhds))).add
        (((tendsto_const_nhds.sub hu_lim).norm.pow 2).const_mul (LK * Mε / 2))
    have hlim := le_of_tendsto_of_tendsto hlhs hrhs (Eventually.of_forall hle_j)
    dsimp only [f_lim]
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero]
    linarith
  have hf_grad : HasGradientAt f_lim
      (NAPPAL.KL.gradU P ubar vbar + ContinuousLinearMap.adjoint (NAPPAL.KL.jac P ubar) pbar)
      ubar := by
    have h1 : HasFDerivAt (fun x : NAPPAL.KL.E n => ⟪NAPPAL.KL.gradU P ubar vbar, x⟫_ℝ)
        (InnerProductSpace.toDual ℝ (NAPPAL.KL.E n) (NAPPAL.KL.gradU P ubar vbar)) ubar :=
      (InnerProductSpace.toDual ℝ (NAPPAL.KL.E n) (NAPPAL.KL.gradU P ubar vbar)).hasFDerivAt
    have h2a : HasFDerivAt (fun x : NAPPAL.KL.E n => fderiv ℝ P.Om ubar x + P.Phi x)
        (fderiv ℝ P.Om ubar + fderiv ℝ P.Phi ubar) ubar :=
      (fderiv ℝ P.Om ubar).hasFDerivAt.add (hA1.2.2.2.1.2.1 ubar).hasFDerivAt
    have hjac_eq : NAPPAL.KL.jac P ubar = fderiv ℝ P.Om ubar + fderiv ℝ P.Phi ubar := by
      unfold NAPPAL.KL.jac NAPPAL.KL.Theta
      exact fderiv_add (hA1.2.2.2.1.1 ubar) (hA1.2.2.2.1.2.1 ubar)
    have h2 : HasFDerivAt (fun x : NAPPAL.KL.E n => ⟪pbar, fderiv ℝ P.Om ubar x + P.Phi x⟫_ℝ)
        (InnerProductSpace.toDual ℝ (NAPPAL.KL.E n)
          (ContinuousLinearMap.adjoint (NAPPAL.KL.jac P ubar) pbar)) ubar := by
      have hc := (InnerProductSpace.toDual ℝ (NAPPAL.KL.E m) pbar).hasFDerivAt.comp ubar h2a
      refine hc.congr_fderiv ?_
      ext w
      rw [hjac_eq]
      simp [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]
    have h3 : HasFDerivAt (fun x : NAPPAL.KL.E n => (LK * Mε / 2) * ‖x - ubar‖ ^ 2)
        (0 : NAPPAL.KL.E n →L[ℝ] ℝ) ubar := by
      have hsub : HasFDerivAt (fun x : NAPPAL.KL.E n => x - ubar)
          (ContinuousLinearMap.id ℝ (NAPPAL.KL.E n)) ubar :=
        (hasFDerivAt_id ubar).sub_const ubar
      have hsq : HasFDerivAt (fun x : NAPPAL.KL.E n => ‖x - ubar‖ ^ 2)
          (0 : NAPPAL.KL.E n →L[ℝ] ℝ) ubar := by
        refine hsub.norm_sq.congr_fderiv ?_
        rw [sub_self, map_zero, ContinuousLinearMap.zero_comp, smul_zero]
      exact (hsq.const_mul (LK * Mε / 2)).congr_fderiv (smul_zero (LK * Mε / 2))
    have hsum : HasFDerivAt f_lim
        (InnerProductSpace.toDual ℝ (NAPPAL.KL.E n) (NAPPAL.KL.gradU P ubar vbar) +
          InnerProductSpace.toDual ℝ (NAPPAL.KL.E n)
            (ContinuousLinearMap.adjoint (NAPPAL.KL.jac P ubar) pbar) + 0) ubar :=
      (h1.add h2).add h3
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hsum.congr_fderiv ?_
    rw [add_zero, map_add]
  obtain ⟨a, ha_mem, b, hb_mem, hab_eq⟩ :=
    exists_subgrad_normalCone_of_isMinOn hubar_U hA1.2.2.1.2.2.1 hA1.2.2.1.2.2.2
      ⟨KJ, tJ, htJ, hKJ⟩ hf_grad hmin_lim
  refine ⟨?_, haug_eq⟩
  refine ⟨a, ha_mem, b, hb_mem, ?_, hv_stat, hfeas.symm⟩
  rw [hfeas, smul_zero, add_zero]
  have : NAPPAL.KL.gradU P ubar vbar + a + b +
      ContinuousLinearMap.adjoint (NAPPAL.KL.jac P ubar) pbar =
      (NAPPAL.KL.gradU P ubar vbar + ContinuousLinearMap.adjoint (NAPPAL.KL.jac P ubar) pbar) + a + b := by
    abel
  rw [this, hab_eq]
  rfl

private lemma iterates_bounded {n d m : ℕ} (P : NAPPAL.KL.Problem n d m)
    (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ) (K : NAPPAL.KL.E n → ℝ)
    (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p)
    (hLam_le1 : ∀ k : ℕ, 1 ≤ k →
      NAPPAL.KL.Lam P LG LH L0 γ u v p k ≤ NAPPAL.KL.Lam P LG LH L0 γ u v p 1) :
    ∃ Ru Rv Rp : ℝ, 0 ≤ Ru ∧ 0 ≤ Rv ∧ 0 ≤ Rp ∧
      (∀ k, ‖u k‖ ≤ Ru) ∧ (∀ k, ‖v k‖ ≤ Rv) ∧ (∀ k, ‖p k‖ ≤ Rp) := by
  have hA1 := hrun.1
  have hA2 := hrun.2.1
  have hN := hrun.2.2.1
  have hγ : 0 < γ := hN.1
  have hlam : 0 < NAPPAL.KL.lamMin P := hA1.2.2.2.2.2.1.2
  have hL0 : 0 ≤ L0 := hA1.2.2.2.1.2.2.1
  have hLG : 0 ≤ LG := hA1.1.2.1
  have hLH : 0 ≤ LH := hA1.2.1.2.1
  have hμ_pos : 0 < (3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2 :=
    mu_pos hA1 hA2
  obtain ⟨cF, hcF⟩ := hA1.2.2.2.2.2.2.1
  have hsublevel_bdd := hA1.2.2.2.2.2.2.2 (NAPPAL.KL.Lam P LG LH L0 γ u v p 1)
  obtain ⟨Rsub, hRsub⟩ := hsublevel_bdd.subset_closedBall (0 : NAPPAL.KL.E n × NAPPAL.KL.E d)
  have huv_bdd_ge1 : ∃ Ru Rv : ℝ, ∀ k : ℕ, 1 ≤ k → ‖u k‖ ≤ Ru ∧ ‖v k‖ ≤ Rv := by
    set Rdiff := Real.sqrt (max 0 ((NAPPAL.KL.Lam P LG LH L0 γ u v p 1 - cF) /
      ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2)))
    refine ⟨max 0 Rsub, max 0 Rsub + Rdiff, ?_⟩
    intro k hk
    obtain ⟨vhat, hvhat, hlb⟩ := lam_lower_bound P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k hk
    have hle1 : NAPPAL.KL.Lam P LG LH L0 γ u v p k ≤ NAPPAL.KL.Lam P LG LH L0 γ u v p 1 :=
      hLam_le1 k hk
    have h2 : 0 ≤ ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2) * ‖v k - vhat‖ ^ 2 :=
      mul_nonneg hμ_pos.le (sq_nonneg _)
    have h3 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 := by positivity
    have hF_le : NAPPAL.KL.F P (u k) vhat ≤ NAPPAL.KL.Lam P LG LH L0 γ u v p 1 := by linarith
    have hmem : ((u k, vhat) : NAPPAL.KL.E n × NAPPAL.KL.E d) ∈ Metric.closedBall 0 Rsub :=
      hRsub ⟨hvhat, hF_le⟩
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hmem
    have hu_le : ‖u k‖ ≤ Rsub := le_trans (le_max_left _ _) hmem
    have hvhat_le : ‖vhat‖ ≤ Rsub := le_trans (le_max_right _ _) hmem
    have hFc : cF ≤ NAPPAL.KL.F P (u k) vhat := hcF (u k) vhat hvhat
    have hdiff_sq : ‖v k - vhat‖ ^ 2 ≤
        (NAPPAL.KL.Lam P LG LH L0 γ u v p 1 - cF) /
          ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2) := by
      rw [le_div_iff₀ hμ_pos]
      linarith
    have hdiff_le : ‖v k - vhat‖ ≤ Rdiff := by
      rw [← Real.sqrt_sq (norm_nonneg (v k - vhat))]
      exact Real.sqrt_le_sqrt (le_trans hdiff_sq (le_max_right _ _))
    have hv_le : ‖v k‖ ≤ max 0 Rsub + Rdiff := by
      calc ‖v k‖ = ‖(v k - vhat) + vhat‖ := by congr 1; abel
        _ ≤ ‖v k - vhat‖ + ‖vhat‖ := norm_add_le _ _
        _ ≤ Rdiff + max 0 Rsub := add_le_add hdiff_le (le_trans hvhat_le (le_max_right _ _))
        _ = max 0 Rsub + Rdiff := add_comm _ _
    exact ⟨le_trans hu_le (le_max_right _ _), hv_le⟩
  obtain ⟨Ru0, Rv0, huv0⟩ := huv_bdd_ge1
  obtain ⟨Ru, hRu_nn, hu_bdd⟩ : ∃ Ru : ℝ, 0 ≤ Ru ∧ ∀ k : ℕ, ‖u k‖ ≤ Ru := by
    refine ⟨max Ru0 ‖u 0‖, le_trans (norm_nonneg (u 0)) (le_max_right _ _), ?_⟩
    intro k
    rcases k with _ | k
    · exact le_max_right _ _
    · exact le_trans (huv0 (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).1 (le_max_left _ _)
  obtain ⟨Rv, hRv_nn, hv_bdd⟩ : ∃ Rv : ℝ, 0 ≤ Rv ∧ ∀ k : ℕ, ‖v k‖ ≤ Rv := by
    refine ⟨max Rv0 ‖v 0‖, le_trans (norm_nonneg (v 0)) (le_max_right _ _), ?_⟩
    intro k
    rcases k with _ | k
    · exact le_max_right _ _
    · exact le_trans (huv0 (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).2 (le_max_left _ _)
  have hp_sub_range : ∀ k : ℕ, p k - p 0 ∈ Set.range P.B := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨y, hy⟩ := ih
      have hstep7 := (hN.2.2.2 k).2.2.2
      obtain ⟨z, hz⟩ : NAPPAL.KL.Theta P (u (k + 1)) ∈ Set.range P.B :=
        hA1.2.2.2.2.2.1.1 ⟨u (k + 1), rfl⟩
      refine ⟨y + γ • (z + v (k + 1)), ?_⟩
      rw [map_add, map_smul, map_add, hy, hz, hstep7]
      abel
  have h41b := (NAPPAL.Rate.lemma_4_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hA1 hA2 hN).2.1
  obtain ⟨M_Bp, hM_Bp_nn, hBp_bdd⟩ : ∃ M_Bp : ℝ, 0 ≤ M_Bp ∧
      ∀ k : ℕ, 1 ≤ k → ‖ContinuousLinearMap.adjoint P.B (p k)‖ ≤ M_Bp := by
    refine ⟨(‖NAPPAL.KL.gradV P 0 0‖ + LG * (Ru + Rv)) +
      (‖gradient P.H 0‖ + LH * Rv) + γ * ‖P.B‖ * (L0 * (Ru + Ru)), by positivity, ?_⟩
    intro k hk
    rw [h41b k hk]
    have h1 : ‖NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))‖ ≤
        ‖NAPPAL.KL.gradV P 0 0‖ + LG * (Ru + Rv) := by
      have hd := gradV_lipschitz_joint hA1.1 (u (k - 1)) (v (k - 1)) 0 0
      simp only [sub_zero] at hd
      calc ‖NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))‖
          = ‖NAPPAL.KL.gradV P 0 0 + (NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1)) - NAPPAL.KL.gradV P 0 0)‖ := by
            congr 1; abel
        _ ≤ ‖NAPPAL.KL.gradV P 0 0‖ + ‖NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1)) - NAPPAL.KL.gradV P 0 0‖ :=
            norm_add_le _ _
        _ ≤ ‖NAPPAL.KL.gradV P 0 0‖ + LG * (‖u (k - 1)‖ + ‖v (k - 1)‖) := by linarith
        _ ≤ ‖NAPPAL.KL.gradV P 0 0‖ + LG * (Ru + Rv) := by
            gcongr; exact hu_bdd _; exact hv_bdd _
    have h2 : ‖gradient P.H (v (k - 1))‖ ≤ ‖gradient P.H 0‖ + LH * Rv := by
      have hd := hA1.2.1.2.2 (v (k - 1)) 0
      simp only [sub_zero] at hd
      calc ‖gradient P.H (v (k - 1))‖
          = ‖gradient P.H 0 + (gradient P.H (v (k - 1)) - gradient P.H 0)‖ := by congr 1; abel
        _ ≤ ‖gradient P.H 0‖ + ‖gradient P.H (v (k - 1)) - gradient P.H 0‖ := norm_add_le _ _
        _ ≤ ‖gradient P.H 0‖ + LH * ‖v (k - 1)‖ := by linarith
        _ ≤ ‖gradient P.H 0‖ + LH * Rv := by gcongr; exact hv_bdd _
    have h3 : ‖γ • ContinuousLinearMap.adjoint P.B
        (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ ≤
        γ * ‖P.B‖ * (L0 * (Ru + Ru)) := by
      rw [norm_smul, Real.norm_of_nonneg hγ.le]
      calc γ * ‖ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖
          ≤ γ * (‖ContinuousLinearMap.adjoint P.B‖ *
              ‖NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1))‖) := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ = γ * (‖P.B‖ * ‖NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1))‖) := by
            rw [LinearIsometryEquiv.norm_map]
        _ ≤ γ * (‖P.B‖ * (L0 * ‖u k - u (k - 1)‖)) := by
            gcongr; exact hA1.2.2.2.1.2.2.2 (u k) (u (k - 1))
        _ ≤ γ * (‖P.B‖ * (L0 * (Ru + Ru))) := by
            gcongr
            calc ‖u k - u (k - 1)‖ ≤ ‖u k‖ + ‖u (k - 1)‖ := norm_sub_le _ _
              _ ≤ Ru + Ru := add_le_add (hu_bdd _) (hu_bdd _)
        _ = γ * ‖P.B‖ * (L0 * (Ru + Ru)) := by ring
    calc ‖-NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1)) - gradient P.H (v (k - 1)) +
          γ • ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖
        ≤ ‖-NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1)) - gradient P.H (v (k - 1))‖ +
          ‖γ • ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ := norm_add_le _ _
      _ ≤ (‖-NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))‖ + ‖gradient P.H (v (k - 1))‖) +
          ‖γ • ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ := by
          gcongr; exact norm_sub_le _ _
      _ = ‖NAPPAL.KL.gradV P (u (k - 1)) (v (k - 1))‖ + ‖gradient P.H (v (k - 1))‖ +
          ‖γ • ContinuousLinearMap.adjoint P.B
            (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P (u (k - 1)))‖ := by rw [norm_neg]
      _ ≤ (‖NAPPAL.KL.gradV P 0 0‖ + LG * (Ru + Rv)) +
          (‖gradient P.H 0‖ + LH * Rv) + γ * ‖P.B‖ * (L0 * (Ru + Ru)) := by linarith
  obtain ⟨Rp, hRp_nn, hp_bdd⟩ : ∃ Rp : ℝ, 0 ≤ Rp ∧ ∀ k : ℕ, ‖p k‖ ≤ Rp := by
    refine ⟨‖p 0‖ + (M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖) /
        Real.sqrt (NAPPAL.KL.lamMin P), by positivity, ?_⟩
    intro k
    rcases k with _ | k
    · have h2 : 0 ≤ (M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖) / Real.sqrt (NAPPAL.KL.lamMin P) := by
        positivity
      linarith
    · obtain ⟨y, hy⟩ := hp_sub_range (k + 1)
      have hlb := lamMin_mul_sq_le_adjoint_of_range P hlam y
      rw [hy] at hlb
      have hBp_k := hBp_bdd (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
      have hBp_diff : ‖ContinuousLinearMap.adjoint P.B (p (k + 1) - p 0)‖ ≤
          M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖ := by
        rw [map_sub]
        have htri := norm_sub_le (ContinuousLinearMap.adjoint P.B (p (k + 1)))
          (ContinuousLinearMap.adjoint P.B (p 0))
        linarith
      have hrhs_nn : 0 ≤ M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖ := by positivity
      have hsq : (Real.sqrt (NAPPAL.KL.lamMin P) * ‖p (k + 1) - p 0‖) ^ 2 ≤
          (M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hlam.le]
        calc NAPPAL.KL.lamMin P * ‖p (k + 1) - p 0‖ ^ 2
            ≤ ‖ContinuousLinearMap.adjoint P.B (p (k + 1) - p 0)‖ ^ 2 := hlb
          _ ≤ (M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hBp_diff 2
      have hsq_lam : Real.sqrt (NAPPAL.KL.lamMin P) * ‖p (k + 1) - p 0‖ ≤
          M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖ :=
        le_of_pow_le_pow_left₀ (by norm_num) hrhs_nn hsq
      have hdiff_p : ‖p (k + 1) - p 0‖ ≤
          (M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖) / Real.sqrt (NAPPAL.KL.lamMin P) :=
        (le_div_iff₀ (Real.sqrt_pos.mpr hlam)).mpr (by linarith)
      calc ‖p (k + 1)‖ = ‖p 0 + (p (k + 1) - p 0)‖ := by congr 1; abel
        _ ≤ ‖p 0‖ + ‖p (k + 1) - p 0‖ := norm_add_le _ _
        _ ≤ ‖p 0‖ + (M_Bp + ‖ContinuousLinearMap.adjoint P.B (p 0)‖) /
              Real.sqrt (NAPPAL.KL.lamMin P) := by linarith
  exact ⟨Ru, Rv, Rp, hRu_nn, hRv_nn, hRp_nn, hu_bdd, hv_bdd, hp_bdd⟩

end Helpers

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    ∃ Λstar : ℝ,
      -- (i)
      (BddBelow (NAPPAL.KL.Lam P LG LH L0 γ u v p '' Set.Ici 1) ∧
        Tendsto (NAPPAL.KL.Lam P LG LH L0 γ u v p) atTop (𝓝 Λstar)) ∧
      -- (ii)
      ((∃ R : ℝ, ∀ k, NAPPAL.KL.tnorm ((u k, v k, p k) : NAPPAL.KL.W n d m) ≤ R) ∧
        Tendsto (fun k => NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))) atTop
          (𝓝 0)) ∧
      -- (iii)
      (Tendsto (fun k => NAPPAL.KL.augLag P γ (u k, v k, p k)) atTop (𝓝 Λstar) ∧
        Tendsto (fun k => NAPPAL.KL.F P (u k) (v k)) atTop (𝓝 Λstar) ∧
        Tendsto (fun k => NAPPAL.KL.Theta P (u k) + P.B (v k)) atTop (𝓝 0)) ∧
      -- (iv)
      ((∃ c5 : ℝ, 0 < c5 ∧ ∀ k, NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u (k + 1), v (k + 1), p (k + 1))) ≤
          ENNReal.ofReal (c5 * NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1)))) ∧
        Tendsto (fun k => NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u k, v k, p k))) atTop (𝓝 0)) ∧
      -- (v)
      (∀ wbar : NAPPAL.KL.W n d m, MapClusterPt wbar atTop (fun k => ((u k, v k, p k) : NAPPAL.KL.W n d m)) →
        NAPPAL.KL.IsStationary P γ wbar ∧ NAPPAL.KL.augLag P γ wbar = Λstar) := by
  have hA1 := hrun.1
  have hA2 := hrun.2.1
  have hN := hrun.2.2.1
  have hδ8 := hrun.2.2.2
  have hγ : 0 < γ := hN.1
  have hσ : 0 < σ := hN.2.1
  have hlam : 0 < NAPPAL.KL.lamMin P := hA1.2.2.2.2.2.1.2
  have hL0 : 0 ≤ L0 := hA1.2.2.2.1.2.2.1
  have hLG : 0 ≤ LG := hA1.1.2.1
  have hLH : 0 ≤ LH := hA1.2.1.2.1
  have hβ : 0 < β := hA2.2.1
  have hLK : 0 ≤ LK := hA2.2.2.2.1
  have hLOm_nn : 0 ≤ NAPPAL.KL.LOm LOmj := Finset.sum_nonneg (fun j _ => (hA1.2.2.2.2.1 j).1)
  obtain ⟨hc4_pos, h43⟩ := NAPPAL.Rate.lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun
  have hc3_pos : 0 < NAPPAL.KL.c3 P LG LH γ := by
    unfold NAPPAL.KL.c3
    exact lt_min (by norm_num) (lt_min hc4_pos (by positivity))
  have hLam_step : ∀ k : ℕ, 1 ≤ k →
      NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1) ≤ NAPPAL.KL.Lam P LG LH L0 γ u v p k := by
    intro k hk
    have h := h43 k hk
    nlinarith [sq_nonneg (NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))), hc3_pos]
  have hLam_anti : Antitone (fun k : ℕ => NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1)) :=
    antitone_nat_of_succ_le (fun k => hLam_step (k + 1) (Nat.succ_le_succ (Nat.zero_le k)))
  have hLam_le1 : ∀ k : ℕ, 1 ≤ k →
      NAPPAL.KL.Lam P LG LH L0 γ u v p k ≤ NAPPAL.KL.Lam P LG LH L0 γ u v p 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    simpa [Nat.add_comm] using hLam_anti (Nat.zero_le j)
  have hμ_pos : 0 < (3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2 :=
    mu_pos hA1 hA2
  obtain ⟨cF, hcF⟩ := hA1.2.2.2.2.2.2.1
  have hLam_bdd : BddBelow (NAPPAL.KL.Lam P LG LH L0 γ u v p '' Set.Ici 1) := by
    refine ⟨cF, ?_⟩
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨vhat, hvhat, hlb⟩ := lam_lower_bound P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k hk
    have hFc : cF ≤ NAPPAL.KL.F P (u k) vhat := hcF (u k) vhat hvhat
    have h2 : 0 ≤ ((3 / 7 : ℝ) * γ * NAPPAL.KL.lamMin P - (LG + LH) / 2) * ‖v k - vhat‖ ^ 2 :=
      mul_nonneg hμ_pos.le (sq_nonneg _)
    have h3 : 0 ≤ 1 / (2 * γ) * ‖p (k - 1) - p k‖ ^ 2 := by positivity
    linarith
  have hLam_shift_bdd : BddBelow (Set.range (fun k : ℕ => NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1))) := by
    obtain ⟨m0, hm0⟩ := hLam_bdd
    refine ⟨m0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hm0 ⟨k + 1, Nat.succ_le_succ (Nat.zero_le k), rfl⟩
  set Λstar : ℝ := ⨅ k : ℕ, NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1)
  have hLam_tendsto_shift : Tendsto (fun k : ℕ => NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1))
      atTop (𝓝 Λstar) :=
    tendsto_atTop_ciInf hLam_anti hLam_shift_bdd
  have hLam_tendsto : Tendsto (NAPPAL.KL.Lam P LG LH L0 γ u v p) atTop (𝓝 Λstar) :=
    (tendsto_add_atTop_iff_nat 1).mp hLam_tendsto_shift
  obtain ⟨Ru, Rv, Rp, hRu_nn, hRv_nn, hRp_nn, hu_bdd, hv_bdd, hp_bdd⟩ :=
    iterates_bounded P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun hLam_le1
  have hw_bdd : ∃ R : ℝ, ∀ k, NAPPAL.KL.tnorm ((u k, v k, p k) : NAPPAL.KL.W n d m) ≤ R := by
    refine ⟨Ru + Rv + Rp, fun k => ?_⟩
    calc NAPPAL.KL.tnorm ((u k, v k, p k) : NAPPAL.KL.W n d m)
        ≤ ‖u k‖ + ‖v k‖ + ‖p k‖ := tnorm_le_sum_norms _
      _ ≤ Ru + Rv + Rp := add_le_add (add_le_add (hu_bdd k) (hv_bdd k)) (hp_bdd k)
  have hwdist_sq_tendsto : Tendsto (fun k =>
      NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1)) ^ 2) atTop (𝓝 0) := by
    have hdiff_lim : Tendsto (fun k =>
        (NAPPAL.KL.Lam P LG LH L0 γ u v p k - NAPPAL.KL.Lam P LG LH L0 γ u v p (k + 1)) /
          NAPPAL.KL.c3 P LG LH γ) atTop (𝓝 0) := by
      have h := (hLam_tendsto.sub hLam_tendsto_shift).div_const (NAPPAL.KL.c3 P LG LH γ)
      simpa using h
    refine squeeze_zero' (Eventually.of_forall (fun k => sq_nonneg _)) ?_ hdiff_lim
    filter_upwards [eventually_ge_atTop 1] with k hk
    have h := h43 k hk
    rw [le_div_iff₀ hc3_pos]
    linarith
  have hwdist_tendsto : Tendsto (fun k =>
      NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hwdist_sq_tendsto
    rw [Real.sqrt_zero] at h
    refine h.congr (fun k => Real.sqrt_sq (wdist_nonneg _ _))
  have hdu_tendsto : Tendsto (fun k => ‖u k - u (k + 1)‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _)
      (fun k => norm_fst_le_tnorm ((u k, v k, p k) - (u (k + 1), v (k + 1), p (k + 1))))
      hwdist_tendsto
  have hdv_tendsto : Tendsto (fun k => ‖v k - v (k + 1)‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _)
      (fun k => norm_snd_fst_le_tnorm ((u k, v k, p k) - (u (k + 1), v (k + 1), p (k + 1))))
      hwdist_tendsto
  have hdp_tendsto : Tendsto (fun k => ‖p k - p (k + 1)‖) atTop (𝓝 0) :=
    squeeze_zero (fun k => norm_nonneg _)
      (fun k => norm_snd_snd_le_tnorm ((u k, v k, p k) - (u (k + 1), v (k + 1), p (k + 1))))
      hwdist_tendsto
  have hres_tendsto : Tendsto (fun k => NAPPAL.KL.Theta P (u k) + P.B (v k)) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1, tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ k, ‖NAPPAL.KL.Theta P (u (k + 1)) + P.B (v (k + 1))‖ =
        (1 / γ) * ‖p k - p (k + 1)‖ := by
      intro k
      have h7 := (hN.2.2.2 k).2.2.2
      have heq : p (k + 1) - p k = γ • (NAPPAL.KL.Theta P (u (k + 1)) + P.B (v (k + 1))) := by
        rw [h7]; abel
      have hnorm' : ‖p k - p (k + 1)‖ = γ * ‖NAPPAL.KL.Theta P (u (k + 1)) + P.B (v (k + 1))‖ := by
        rw [norm_sub_rev, heq, norm_smul, Real.norm_of_nonneg hγ.le]
      rw [hnorm']
      field_simp [hγ.ne']
    simp_rw [hnorm]
    simpa using hdp_tendsto.const_mul (1 / γ)
  have haug_tendsto : Tendsto (fun k => NAPPAL.KL.augLag P γ (u k, v k, p k)) atTop (𝓝 Λstar) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have haux : Tendsto (fun k =>
        NAPPAL.KL.c1 P LG L0 γ * ‖u k - u (k + 1)‖ ^ 2 +
        NAPPAL.KL.c2 P LG LH γ * ‖v k - v (k + 1)‖ ^ 2 +
        1 / (2 * γ) * ‖p k - p (k + 1)‖ ^ 2) atTop (𝓝 0) := by
      have h1 := (hdu_tendsto.pow 2).const_mul (NAPPAL.KL.c1 P LG L0 γ)
      have h2 := (hdv_tendsto.pow 2).const_mul (NAPPAL.KL.c2 P LG LH γ)
      have h3 := (hdp_tendsto.pow 2).const_mul (1 / (2 * γ))
      simpa using (h1.add h2).add h3
    have hsub := hLam_tendsto_shift.sub haux
    rw [sub_zero] at hsub
    refine hsub.congr (fun k => ?_)
    unfold NAPPAL.KL.Lam NAPPAL.KL.wseq
    simp only [Nat.add_sub_cancel]
    ring
  have hF_tendsto : Tendsto (fun k => NAPPAL.KL.F P (u k) (v k)) atTop (𝓝 Λstar) := by
    have hres_norm : Tendsto (fun k => ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp hres_tendsto
    have hinner_lim : Tendsto (fun k => ⟪p k, NAPPAL.KL.Theta P (u k) + P.B (v k)⟫_ℝ) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
        (by simpa using hres_norm.const_mul Rp)
      rw [Real.norm_eq_abs]
      calc |⟪p k, NAPPAL.KL.Theta P (u k) + P.B (v k)⟫_ℝ|
          ≤ ‖p k‖ * ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖ := abs_real_inner_le_norm _ _
        _ ≤ Rp * ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖ :=
            mul_le_mul_of_nonneg_right (hp_bdd k) (norm_nonneg _)
    have hpen_lim : Tendsto (fun k => (γ / 2) * ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖ ^ 2)
        atTop (𝓝 0) := by
      simpa using (hres_norm.pow 2).const_mul (γ / 2)
    have hcomb := (haug_tendsto.sub hinner_lim).sub hpen_lim
    rw [sub_zero, sub_zero] at hcomb
    refine hcomb.congr (fun k => ?_)
    unfold NAPPAL.KL.augLag
    dsimp only
    ring
  set Q : ℝ := Rp + γ * (‖NAPPAL.KL.Theta P 0‖ + L0 * Ru + ‖P.B‖ * Rv)
  have hQ_nn : 0 ≤ Q := by
    have hRp_nn : 0 ≤ Rp := le_trans (norm_nonneg (p 0)) (hp_bdd 0)
    dsimp only [Q]; positivity
  have hq_bdd : ∀ k : ℕ, ‖NAPPAL.Rate.qseq P γ u v p k‖ ≤ Q := by
    intro k
    unfold NAPPAL.Rate.qseq
    have hTh : ‖NAPPAL.KL.Theta P (u k)‖ ≤ ‖NAPPAL.KL.Theta P 0‖ + L0 * Ru := by
      have hd := hA1.2.2.2.1.2.2.2 (u k) 0
      simp only [sub_zero] at hd
      calc ‖NAPPAL.KL.Theta P (u k)‖
          = ‖NAPPAL.KL.Theta P 0 + (NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P 0)‖ := by congr 1; abel
        _ ≤ ‖NAPPAL.KL.Theta P 0‖ + ‖NAPPAL.KL.Theta P (u k) - NAPPAL.KL.Theta P 0‖ := norm_add_le _ _
        _ ≤ ‖NAPPAL.KL.Theta P 0‖ + L0 * ‖u k‖ := by linarith
        _ ≤ ‖NAPPAL.KL.Theta P 0‖ + L0 * Ru := by gcongr; exact hu_bdd k
    have hBv : ‖P.B (v k)‖ ≤ ‖P.B‖ * Rv :=
      le_trans (ContinuousLinearMap.le_opNorm P.B (v k))
        (mul_le_mul_of_nonneg_left (hv_bdd k) (norm_nonneg P.B))
    calc ‖p k + γ • (NAPPAL.KL.Theta P (u k) + P.B (v k))‖
        ≤ ‖p k‖ + ‖γ • (NAPPAL.KL.Theta P (u k) + P.B (v k))‖ := norm_add_le _ _
      _ = ‖p k‖ + γ * ‖NAPPAL.KL.Theta P (u k) + P.B (v k)‖ := by rw [norm_smul, Real.norm_of_nonneg hγ.le]
      _ ≤ Rp + γ * (‖NAPPAL.KL.Theta P (u k)‖ + ‖P.B (v k)‖) := by
          gcongr; exact hp_bdd k; exact norm_add_le _ _
      _ ≤ Q := by dsimp only [Q]; nlinarith
  set denomQ : ℝ := LG + Q * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2 +
    14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / NAPPAL.KL.lamMin P +
    14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * NAPPAL.KL.lamMin P) + 1
  have hdenomQ_pos : 0 < denomQ := by dsimp only [denomQ]; positivity
  have hinv_δ_le : ∀ k : ℕ, 1 / δ k ≤ denomQ / β := by
    intro k
    rw [hδ8 k]
    unfold NAPPAL.KL.delta8
    set dk := LG + ‖NAPPAL.Rate.qseq P γ u v p k‖ * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2 +
      14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / NAPPAL.KL.lamMin P +
      14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * NAPPAL.KL.lamMin P) + 1
    have hdk_le : dk ≤ denomQ := by
      dsimp only [dk, denomQ]
      gcongr
      exact hq_bdd k
    rw [one_div_div]
    exact div_le_div_of_nonneg_right hdk_le hβ.le
  set Hmax : ℝ := max (max (2 * LG + Q * NAPPAL.KL.LOm LOmj + γ * ‖P.B‖ * L0 + γ * L0 ^ 2 +
      LK * (denomQ / β) / σ) (2 * LG + LH + γ * ‖P.B‖ * L0)) (L0 + ‖P.B‖ + 1 / γ)
  have hhfun_le : ∀ k : ℕ,
      NAPPAL.Rate.hfun P LG LH L0 (NAPPAL.KL.LOm LOmj) LK γ σ (NAPPAL.Rate.qseq P γ u v p k) (δ k) ≤
        Hmax := by
    intro k
    unfold NAPPAL.Rate.hfun
    dsimp only [Hmax]
    apply max_le_max _ le_rfl
    apply max_le_max _ le_rfl
    have h1 : ‖NAPPAL.Rate.qseq P γ u v p k‖ * NAPPAL.KL.LOm LOmj ≤ Q * NAPPAL.KL.LOm LOmj :=
      mul_le_mul_of_nonneg_right (hq_bdd k) hLOm_nn
    have h2 : LK / (σ * δ k) ≤ LK * (denomQ / β) / σ := by
      have heq : LK / (σ * δ k) = LK * (1 / δ k) / σ := by ring
      rw [heq]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hinv_δ_le k) hLK) hσ.le
    linarith
  set c5 : ℝ := max 1 (Real.sqrt 3 * Hmax)
  have hc5_pos : 0 < c5 := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hc5_bound : ∀ k : ℕ,
      NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u (k + 1), v (k + 1), p (k + 1))) ≤
        ENNReal.ofReal (c5 * NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))) := by
    intro k
    refine le_trans (NAPPAL.Rate.proposition_3_1 P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun k) ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (wdist_nonneg _ _)
    calc Real.sqrt 3 *
          NAPPAL.Rate.hfun P LG LH L0 (NAPPAL.KL.LOm LOmj) LK γ σ (NAPPAL.Rate.qseq P γ u v p k) (δ k)
        ≤ Real.sqrt 3 * Hmax := mul_le_mul_of_nonneg_left (hhfun_le k) (Real.sqrt_nonneg 3)
      _ ≤ c5 := le_max_right _ _
  have hdist_tendsto : Tendsto (fun k =>
      NAPPAL.KL.distZero (NAPPAL.KL.dAugLag P γ (u k, v k, p k))) atTop (𝓝 0) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have hrhs : Tendsto (fun k =>
        ENNReal.ofReal (c5 * NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun k =>
          c5 * NAPPAL.KL.wdist (u k, v k, p k) (u (k + 1), v (k + 1), p (k + 1))) atTop (𝓝 0) := by
        simpa using hwdist_tendsto.const_mul c5
      have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h1
      rw [ENNReal.ofReal_zero] at h2
      exact h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hrhs
      (fun _ => bot_le) hc5_bound
  set Mε : ℝ := denomQ / (σ * β)
  have hinv_ε_le : ∀ k : ℕ, 1 / ε k ≤ Mε := by
    intro k
    have hδk_pos : 0 < δ k := (hN.2.2.2 k).1.1
    have hσε : σ * δ k ≤ ε k := (hN.2.2.2 k).1.2.1
    have h1 : 1 / ε k ≤ 1 / (σ * δ k) := one_div_le_one_div_of_le (mul_pos hσ hδk_pos) hσε
    have h2 : 1 / (σ * δ k) = (1 / δ k) / σ := by ring
    have h3 : (1 / δ k) / σ ≤ (denomQ / β) / σ :=
      div_le_div_of_nonneg_right (hinv_δ_le k) hσ.le
    have h4 : (denomQ / β) / σ = Mε := by dsimp only [Mε]; ring
    linarith
  have hpart5 := fun wbar hcl =>
    part_v_cluster P LG LH L0 LK β γ σ LOmj K δ ε u v p hrun Λstar Mε hinv_ε_le
      hdu_tendsto hdv_tendsto hdp_tendsto hres_tendsto haug_tendsto wbar hcl
  exact ⟨Λstar, ⟨hLam_bdd, hLam_tendsto⟩, ⟨hw_bdd, hwdist_tendsto⟩,
    ⟨haug_tendsto, hF_tendsto, hres_tendsto⟩, ⟨⟨c5, hc5_pos, hc5_bound⟩, hdist_tendsto⟩, hpart5⟩
