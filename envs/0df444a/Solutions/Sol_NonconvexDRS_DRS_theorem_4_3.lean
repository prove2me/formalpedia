-- Prove2me | solution 1 for NonconvexDRS.DRS.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T04:49:06.945607+00:00
-- url     : https://prove2.me/submissions/763b0518-fe4d-4896-827b-226a13989126

-- Licensed under Apache 2.0. Complete nonconvex Douglas-Rachford convergence theorem.
import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace


namespace DRSConvergenceProof
open Set NonconvexDRS.DRS
open scoped RealInnerProductSpace

lemma convex_fderiv_support {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hc : ConvexOn ℝ Set.univ f) (x y : F)
    (hd : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  have hconv := hc.comp_affineMap (AffineMap.lineMap x y)
  have hline : HasDerivAt (fun t : ℝ => t • (y - x) + x) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hd' : HasFDerivAt f (fderiv ℝ f x) ((0 : ℝ) • (y - x) + x) := by
    simpa using hd.hasFDerivAt
  have hder := hd'.comp_hasDerivAt 0 hline
  have hh := hconv.le_slope_of_hasDerivAt (by trivial) (by trivial)
    (show (0 : ℝ) < 1 by norm_num)
    (by simpa only [Function.comp_def, AffineMap.lineMap_apply_module', zero_smul,
      zero_add] using hder)
  simp [slope] at hh
  rw [map_sub]
  linarith

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

lemma segment_derivative (hf : IsLSmooth f L) (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (gradient f (x + t • v)) v) t := by
  convert (hf.1.differentiableAt.hasGradientAt).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x) using 1 <;>
    first | rfl | simp only [one_smul, InnerProductSpace.toDual_apply_apply, id_eq]

lemma smooth_descent (hf : IsLSmooth f L) (x v : EuclideanSpace ℝ (Fin n)) :
    f (x + v) ≤ f x + inner ℝ (gradient f x) v + (L / 2) * ‖v‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => f (x + t • v)
  let B : ℝ → ℝ := fun t => f x + t * inner ℝ (gradient f x) v +
    (L / 2) * t ^ 2 * ‖v‖ ^ 2
  have hF : ∀ t, HasDerivAt F (inner ℝ (gradient f (x + t • v)) v) t :=
    segment_derivative hf x v
  have hB : ∀ t, HasDerivAt B (inner ℝ (gradient f x) v + L * t * ‖v‖ ^ 2) t := by
    intro t
    convert (((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) v)).const_add (f x)).add
      ((((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖v‖ ^ 2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      inner ℝ (gradient f (x + t • v)) v ≤ inner ℝ (gradient f x) v + L * t * ‖v‖ ^ 2 := by
    intro t ht
    have h1 := real_inner_le_norm (gradient f (x + t • v) - gradient f x) v
    have h2 := hf.2 (x + t • v) x
    change ‖gradient f (x + t • v) - gradient f x‖ ≤ L * ‖(x + t • v) - x‖ at h2
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h2
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    rw [inner_sub_left] at h1
    nlinarith
  have hh := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt)
    (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt) hbound
  simpa [F, B] using hh (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)

lemma gradient_continuous (hf : IsLSmooth f L) (hL : 0 ≤ L) : Continuous (gradient f) := by
  have hh : LipschitzWith ⟨L, hL⟩ (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖
    exact hf.2 x y
  exact hh.continuous

lemma smooth_lower (hf : IsLSmooth f L) (x y : EuclideanSpace ℝ (Fin n)) :
    f x + inner ℝ (gradient f x) (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hn : IsLSmooth (fun z => -f z) L := by
    refine ⟨hf.1.neg, ?_⟩
    intro u v
    have hgu : gradient (fun z => -f z) u = -gradient f u := by
      change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (-f) _) = _
      rw [fderiv_neg, map_neg]
      rfl
    have hgv : gradient (fun z => -f z) v = -gradient f v := by
      change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (-f) _) = _
      rw [fderiv_neg, map_neg]
      rfl
    rw [hgu, hgv, neg_sub_neg, norm_sub_rev]
    exact hf.2 u v
  have hh := smooth_descent hn x (y - x)
  have hg : gradient (fun z => -f z) x = -gradient f x :=
    by
      change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ (-f) x) = _
      rw [fderiv_neg, map_neg]
      rfl
  rw [hg, inner_neg_left] at hh
  have he : x + (y - x) = y := by abel
  rw [he] at hh
  linarith

lemma convex_gradient_support (hf : IsLSmooth f L) (hc : ConvexOn ℝ univ f)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  rw [inner_gradient_left]
  exact convex_fderiv_support hc x y hf.1.differentiableAt

end DRSConvergenceProof


namespace DRSConvergenceProof
open Set NonconvexDRS.DRS
open scoped RealInnerProductSpace

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L σ μ : ℝ}

lemma hypoconvex_support (hf : IsLSmooth f L) (hc : IsHypoconvex f σ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x + inner ℝ (gradient f x) (y - x) + σ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hd := (hf.1.differentiableAt (x := x)).hasFDerivAt.sub
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (σ / 2))
  have hh := convex_fderiv_support hc x y hd.differentiableAt
  have hd' : HasFDerivAt (fun z => f z - σ / 2 * ‖z‖ ^ 2)
      (fderiv ℝ f x - (σ / 2) • (2 • innerSL ℝ x)) x := by
    convert hd using 1 <;> rfl
  rw [hd'.fderiv] at hh
  simp only [sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    ← inner_gradient_left] at hh
  simp only [inner_sub_right, two_smul, real_inner_self_eq_norm_sq] at hh
  rw [norm_sub_sq_real, inner_sub_right]
  have hxy : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [hxy]
  nlinarith

lemma hypoconvex_mono (hc : IsHypoconvex f σ) (hμ : μ ≤ σ) : IsHypoconvex f μ := by
  have hnorm : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin n)))
      (fun x => ‖x‖ ^ 2) := (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  have hh := hc.add (hnorm.smul (show 0 ≤ (σ - μ) / 2 by linarith))
  unfold IsHypoconvex
  have he : (fun x => f x - μ / 2 * ‖x‖ ^ 2) =
      ((fun x => f x - σ / 2 * ‖x‖ ^ 2) + fun x => ((σ - μ) / 2) • ‖x‖ ^ 2) := by
    funext x
    dsimp
    ring
  rw [he]
  exact hh

lemma shifted_gradient (hf : IsLSmooth f L) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun z => f z - μ / 2 * ‖z‖ ^ 2) x = gradient f x - μ • x := by
  have hd := (hf.1.differentiableAt (x := x)).hasFDerivAt.sub
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2))
  have hd' : HasFDerivAt (fun z => f z - μ / 2 * ‖z‖ ^ 2)
      (fderiv ℝ f x - (μ / 2) • (2 • innerSL ℝ x)) x := by
    convert hd using 1 <;> rfl
  have he : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
      (gradient f x - μ • x) = fderiv ℝ f x - (μ / 2) • (2 • innerSL ℝ x) := by
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left,
      sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply, inner_gradient_left]
    ring
  have hg : HasGradientAt (fun z => f z - μ / 2 * ‖z‖ ^ 2) (gradient f x - μ • x) x := by
    rw [hasGradientAt_iff_hasFDerivAt, he]
    exact hd'
  exact hg.gradient

lemma shifted_smooth (hf : IsLSmooth f L) (hμ : μ ≤ 0) :
    IsLSmooth (fun z => f z - μ / 2 * ‖z‖ ^ 2) (L - μ) := by
  refine ⟨fun x => ?_, ?_⟩
  · exact (hf.1 x).sub ((hasStrictFDerivAt_norm_sq x).differentiableAt.const_mul _)
  · intro x y
    rw [shifted_gradient hf, shifted_gradient hf]
    have he : gradient f x - μ • x - (gradient f y - μ • y) =
        (gradient f x - gradient f y) - μ • (x - y) := by module
    rw [he]
    calc
      ‖(gradient f x - gradient f y) - μ • (x - y)‖ ≤
          ‖gradient f x - gradient f y‖ + ‖μ • (x - y)‖ := norm_sub_le _ _
      _ ≤ L * ‖x - y‖ + ‖μ • (x - y)‖ := add_le_add_left (hf.2 x y) _
      _ = (L - μ) * ‖x - y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos hμ]
        ring

end DRSConvergenceProof


namespace DRSConvergenceProof
open Set NonconvexDRS.DRS
open scoped RealInnerProductSpace

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}

lemma convex_bregman_gradient (hf : IsLSmooth f L) (hc : ConvexOn ℝ univ f)
    (hL : 0 < L) (x y : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f y - gradient f x‖ ^ 2 / (2 * L) ≤
      f y - f x - inner ℝ (gradient f x) (y - x) := by
  let d := gradient f y - gradient f x
  let z := y + (-1 / L) • d
  have h1 := convex_gradient_support hf hc x z
  have h2 := smooth_descent hf y ((-1 / L) • d)
  change f z ≤ _ at h2
  have hz : z - x = (y - x) + (-1 / L) • d := by dsimp [z]; abel
  rw [hz, inner_add_right, inner_smul_right] at h1
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h2
  have hi : inner ℝ (gradient f y) d - inner ℝ (gradient f x) d = ‖d‖ ^ 2 := by
    rw [← inner_sub_left]
    exact real_inner_self_eq_norm_sq d
  have h3 : f x + inner ℝ (gradient f x) (y - x) +
      (-1 / L) * inner ℝ (gradient f x) d ≤
      f y + (-1 / L) * inner ℝ (gradient f y) d +
      L / 2 * ((-1 / L) ^ 2 * ‖d‖ ^ 2) := by linarith [h1.trans h2]
  have hc1 : (-1 / L) * inner ℝ (gradient f y) d -
      (-1 / L) * inner ℝ (gradient f x) d = -‖d‖ ^ 2 / L := by
    rw [← mul_sub, hi]
    ring
  have hc2 : L / 2 * ((-1 / L) ^ 2 * ‖d‖ ^ 2) = ‖d‖ ^ 2 / (2 * L) := by
    field_simp [hL.ne']
  rw [hc2] at h3
  have hc3 : ‖d‖ ^ 2 / L = 2 * (‖d‖ ^ 2 / (2 * L)) := by ring
  conv_rhs at hc1 => rw [neg_div, hc3]
  change ‖d‖ ^ 2 / (2 * L) ≤ _
  linarith

lemma nonpositive_bregman (hf : IsLSmooth f L) {σ : ℝ}
    (hc : IsHypoconvex f σ) (hσ : σ ≤ 0) (hL : 0 < L + σ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    σ * L / (2 * (L + σ)) * ‖y - x‖ ^ 2 +
      1 / (2 * (L + σ)) * ‖gradient f y - gradient f x‖ ^ 2 ≤
      f y - f x - inner ℝ (gradient f x) (y - x) := by
  let H := fun z => f z - σ / 2 * ‖z‖ ^ 2
  have hK : 0 < L - σ := by linarith
  have hs : IsLSmooth H (L - σ) := shifted_smooth hf hσ
  have h1 := convex_bregman_gradient hs hc hK x y
  have h2 := convex_bregman_gradient hs hc hK y x
  let d := y - x
  let dg := gradient f y - gradient f x
  have hg1 : gradient H x = gradient f x - σ • x := shifted_gradient hf x
  have hg2 : gradient H y = gradient f y - σ • y := shifted_gradient hf y
  have hgd : gradient H y - gradient H x = dg - σ • d := by
    rw [hg1, hg2]
    dsimp [dg, d]
    module
  have hB : H y - H x - inner ℝ (gradient H x) (y - x) =
      (f y - f x - inner ℝ (gradient f x) d) - σ / 2 * ‖d‖ ^ 2 := by
    rw [hg1, inner_sub_left, real_inner_smul_left]
    dsimp [H, d]
    rw [norm_sub_sq_real]
    simp only [inner_sub_right, real_inner_self_eq_norm_sq]
    have hxy := real_inner_comm x y
    nlinarith
  have hBr : H x - H y - inner ℝ (gradient H y) (x - y) =
      (f x - f y - inner ℝ (gradient f y) (x - y)) - σ / 2 * ‖d‖ ^ 2 := by
    rw [hg2, inner_sub_left, real_inner_smul_left]
    dsimp [H, d]
    rw [norm_sub_sq_real]
    simp only [inner_sub_right, real_inner_self_eq_norm_sq]
    have hxy := real_inner_comm x y
    nlinarith
  have hnorm : ‖dg - σ • d‖ ^ 2 =
      ‖dg‖ ^ 2 - 2 * σ * inner ℝ dg d + σ ^ 2 * ‖d‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hgd, hB, hnorm] at h1
  rw [norm_sub_rev, hgd, hBr, hnorm] at h2
  have hi : (f y - f x - inner ℝ (gradient f x) d) +
      (f x - f y - inner ℝ (gradient f y) (x - y)) = inner ℝ dg d := by
    have he : x - y = -d := by dsimp [d]; abel
    rw [he, inner_neg_right]
    dsimp [dg]
    rw [inner_sub_left]
    ring
  have h1' := (div_le_iff₀ (by positivity : 0 < 2 * (L - σ))).mp h1
  have h2' := (div_le_iff₀ (by positivity : 0 < 2 * (L - σ))).mp h2
  have hco : ‖dg‖ ^ 2 + σ * L * ‖d‖ ^ 2 ≤ (L + σ) * inner ℝ dg d := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hco (show 0 ≤ -σ by linarith)
  have hmain : σ * L * ‖d‖ ^ 2 + ‖dg‖ ^ 2 ≤
      2 * (L + σ) * (f y - f x - inner ℝ (gradient f x) d) := by
    have hz : (L - σ) * (σ * L * ‖d‖ ^ 2 + ‖dg‖ ^ 2 -
        2 * (L + σ) * (f y - f x - inner ℝ (gradient f x) d)) ≤ 0 := by
      nlinarith [mul_le_mul_of_nonneg_left h1' hL.le]
    by_contra hn
    have hp := mul_pos hK (sub_pos.mpr (lt_of_not_ge hn))
    linarith
  have he : σ * L / (2 * (L + σ)) * ‖d‖ ^ 2 +
      1 / (2 * (L + σ)) * ‖dg‖ ^ 2 =
      (σ * L * ‖d‖ ^ 2 + ‖dg‖ ^ 2) / (2 * (L + σ)) := by ring
  change σ * L / (2 * (L + σ)) * ‖d‖ ^ 2 +
      1 / (2 * (L + σ)) * ‖dg‖ ^ 2 ≤ _
  rw [he]
  exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hmain])

end DRSConvergenceProof


namespace DRSConvergenceProof
open NonconvexDRS.DRS

lemma strong_range_quadratic {L σ γ lam : ℝ} (hL : 0 < L)
    (hσ : σ ≤ L) (hγ : 0 < γ) (hs : 0 < σ) (hl : 2 ≤ lam)
    (hlup : lam * (1 + Real.sqrt (1 - σ / L)) < 4)
    (hlo : σ / L * lam - deltaDR L σ lam < 4 * σ * γ)
    (hup : 4 * σ * γ < σ / L * lam + deltaDR L σ lam) :
    γ * L < 1 ∧
      0 < (2 - lam) / (2 * lam * γ) + σ * (1 / 2 - γ * L / lam) := by
  let p := σ / L
  let ξ := γ * L
  have hp : 0 < p := div_pos hs hL
  have hp1 : p ≤ 1 := (div_le_one hL).2 hσ
  have hlpos : 0 < lam := by linarith
  have hl4 : lam < 4 := by
    have := mul_nonneg hlpos.le (Real.sqrt_nonneg (1 - σ / L))
    nlinarith
  have hd : 0 < deltaDR L σ lam := by linarith
  have hrad : 0 < (p * lam) ^ 2 - 8 * p * (lam - 2) := by
    exact Real.sqrt_pos.mp hd
  have hsq : (deltaDR L σ lam) ^ 2 = (p * lam) ^ 2 - 8 * p * (lam - 2) :=
    Real.sq_sqrt hrad.le
  have hid : 4 * σ * γ = 4 * p * ξ := by
    dsimp [p, ξ]
    field_simp
  rw [hid] at hlo hup
  change p * lam - deltaDR L σ lam < 4 * p * ξ at hlo
  change 4 * p * ξ < p * lam + deltaDR L σ lam at hup
  have hprod : 0 < (deltaDR L σ lam - (4 * p * ξ - p * lam)) *
      (deltaDR L σ lam + (4 * p * ξ - p * lam)) :=
    mul_pos (by linarith) (by linarith)
  have hq : 2 * p * ξ ^ 2 - p * lam * ξ + (lam - 2) < 0 := by
    nlinarith
  have hx : ξ < 1 := by
    by_contra hn
    have hx1 : 1 ≤ ξ := le_of_not_gt hn
    have hprod2 : 0 ≤ p * (ξ - 1) * (2 * ξ + 2 - lam) :=
      mul_nonneg (mul_nonneg hp.le (by linarith)) (by linarith)
    have hprod3 : 0 ≤ (lam - 2) * (1 - p) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  refine ⟨hx, ?_⟩
  have he : (2 * lam * γ) *
      ((2 - lam) / (2 * lam * γ) + σ * (1 / 2 - γ * L / lam)) =
      -(2 * p * ξ ^ 2 - p * lam * ξ + (lam - 2)) := by
    dsimp [p, ξ]
    field_simp
    ring
  have hm : 0 < (2 * lam * γ) *
      ((2 - lam) / (2 * lam * γ) + σ * (1 / 2 - γ * L / lam)) := by
    rw [he]
    linarith
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * lam * γ)).mp hm

lemma range_bounds {L σ γ lam : ℝ} (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hγ : 0 < γ) (hr : StepRange L σ γ lam) :
    0 < lam ∧ γ * L < 1 ∧ 0 < 1 + γ * σ := by
  rcases hr with h | h
  · refine ⟨h.1, h.2.2.1, ?_⟩
    have := mul_le_mul_of_nonneg_left hσ.1 hγ.le
    nlinarith [h.2.2.1]
  · have hh := strong_range_quadratic hL hσ.2 hγ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    exact ⟨by linarith [h.2.1], hh.1, by nlinarith [mul_pos hγ h.1]⟩

lemma first_range_inflation {L σ γ lam : ℝ} (hL : 0 < L) (hγ : 0 < γ)
    (hl : 0 < lam) (hl2 : lam < 2) (hγL : γ * L < 1)
    (hneg : 2 * γ * negPartR σ < 2 - lam) :
    let μ := min σ 0
    let M := max L (-2 * μ / (2 - lam))
    0 < M ∧ L ≤ M ∧ μ ≤ σ ∧ μ ≤ 0 ∧ 0 < M + μ ∧
      γ * M < 1 ∧ lam * M ≤ 2 * (M + μ) := by
  dsimp only
  let μ := min σ 0
  let M := max L (-2 * μ / (2 - lam))
  have hμ : μ ≤ 0 := min_le_right _ _
  have hM : L ≤ M := le_max_left _ _
  have hMp : 0 < M := lt_of_lt_of_le hL hM
  have ha : 0 < 2 - lam := by linarith
  have hM2 : -2 * μ ≤ (2 - lam) * M := by
    have hh := le_max_right L (-2 * μ / (2 - lam))
    have hh' := (div_le_iff₀ ha).mp hh
    nlinarith
  have hn : negPartR σ = -μ := by
    dsimp [negPartR, μ]
    rcases le_total σ 0 with hs | hs
    · rw [min_eq_left hs, max_eq_right (by linarith)]
    · rw [min_eq_right hs, max_eq_left (by linarith)]
      simp
  have hfrac : γ * (-2 * μ / (2 - lam)) < 1 := by
    rw [← mul_div_assoc, div_lt_one ha]
    rw [hn] at hneg
    nlinarith
  have hgm : γ * M < 1 := by
    dsimp [M]
    rw [mul_max_of_nonneg _ _ hγ.le]
    exact max_lt hγL hfrac
  have hsum : 0 < M + μ := by
    nlinarith [mul_pos hl hMp]
  exact ⟨hMp, hM, min_le_left _ _, hμ, hsum, hgm, by nlinarith⟩

end DRSConvergenceProof


namespace DRSConvergenceProof
open NonconvexDRS.DRS Set
open scoped RealInnerProductSpace

lemma first_coefficients_pos {M μ γ lam : ℝ} (hM : 0 < M) (_hμ : μ ≤ 0)
    (hs : 0 < M + μ) (hγ : 0 < γ) (hl : 0 < lam) (hl2 : lam < 2)
    (hz : γ * M < 1) (hrel : lam * M ≤ 2 * (M + μ)) :
    0 < (2 - lam) / (2 * lam * γ) + μ * M / (2 * (M + μ)) ∧
    0 < (2 - lam) / (2 * lam * γ) + M / 2 - γ * M ^ 2 / lam := by
  have hden : 0 < 2 * lam * γ := by positivity
  have hbase : (2 - lam) * M / (2 * lam) < (2 - lam) / (2 * lam * γ) := by
    apply (div_lt_div_iff₀ (by positivity) hden).2
    have hh := mul_lt_mul_of_pos_left hz (show 0 < (2 - lam) * (2 * lam) by positivity)
    nlinarith
  have hrest : 0 ≤ (2 - lam) * M / (2 * lam) + μ * M / (2 * (M + μ)) := by
    have he : (2 * lam * (M + μ)) *
        ((2 - lam) * M / (2 * lam) + μ * M / (2 * (M + μ))) =
        M * (2 * (M + μ) - lam * M) := by
      field_simp
      ring
    have hh : 0 ≤ M * (2 * (M + μ) - lam * M) :=
      mul_nonneg hM.le (by linarith)
    rw [← he] at hh
    exact (mul_nonneg_iff_of_pos_left (by positivity)).mp hh
  refine ⟨by linarith, ?_⟩
  have he : (2 * lam * γ) *
      ((2 - lam) / (2 * lam * γ) + M / 2 - γ * M ^ 2 / lam) =
      (1 - γ * M) * (2 - lam + 2 * γ * M) := by
    field_simp
    ring
  have hh : 0 < (1 - γ * M) * (2 - lam + 2 * γ * M) :=
    mul_pos (by linarith) (by positivity)
  rw [← he] at hh
  exact (mul_pos_iff_of_pos_left hden).mp hh

lemma smooth_mono {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L M : ℝ}
    (hf : IsLSmooth f L) (hLM : L ≤ M) : IsLSmooth f M := by
  refine ⟨hf.1, fun x y => (hf.2 x y).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hLM (norm_nonneg _)

lemma bregman_decrease_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {L σ γ lam : ℝ} (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hf : IsLSmooth f L) (hc : IsHypoconvex f σ) (hγ : 0 < γ)
    (hr : StepRange L σ γ lam) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y : EuclideanSpace ℝ (Fin n),
      c * ‖y - x‖ ^ 2 ≤ (2 - lam) / (2 * γ * lam) * ‖y - x‖ ^ 2 -
        γ / lam * ‖gradient f y - gradient f x‖ ^ 2 +
        (f x - f y - inner ℝ (gradient f y) (x - y)) := by
  rcases hr with h | h
  · let μ := min σ 0
    let M := max L (-2 * μ / (2 - lam))
    have hi := first_range_inflation hL hγ h.1 h.2.1 h.2.2.1 h.2.2.2
    change 0 < M ∧ L ≤ M ∧ μ ≤ σ ∧ μ ≤ 0 ∧ 0 < M + μ ∧
      γ * M < 1 ∧ lam * M ≤ 2 * (M + μ) at hi
    have hp := first_coefficients_pos hi.1 hi.2.2.2.1 hi.2.2.2.2.1
      hγ h.1 h.2.1 hi.2.2.2.2.2.1 hi.2.2.2.2.2.2
    let A := (2 - lam) / (2 * lam * γ) + μ * M / (2 * (M + μ))
    let B := (2 - lam) / (2 * lam * γ) + M / 2 - γ * M ^ 2 / lam
    refine ⟨min A B, lt_min hp.1 hp.2, ?_⟩
    intro x y
    have hB := nonpositive_bregman (smooth_mono hf hi.2.1)
      (hypoconvex_mono hc hi.2.2.1) hi.2.2.2.1 hi.2.2.2.2.1 y x
    rw [norm_sub_rev x y, norm_sub_rev (gradient f x) (gradient f y)] at hB
    have hN : ‖gradient f y - gradient f x‖ ^ 2 ≤ M ^ 2 * ‖y - x‖ ^ 2 := by
      have hh := (smooth_mono hf hi.2.1).2 y x
      nlinarith [norm_nonneg (gradient f y - gradient f x),
        mul_nonneg hi.1.le (norm_nonneg (y - x))]
    by_cases hk : 0 ≤ 1 / (2 * (M + μ)) - γ / lam
    · have hm := mul_nonneg hk (sq_nonneg ‖gradient f y - gradient f x‖)
      have hh := mul_le_mul_of_nonneg_right (min_le_left A B) (sq_nonneg ‖y - x‖)
      dsimp [A] at hh
      have he : (2 - lam) / (2 * γ * lam) = (2 - lam) / (2 * lam * γ) := by ring
      rw [he]
      linarith
    · have hm := mul_le_mul_of_nonpos_left hN (le_of_not_ge hk)
      have hh := mul_le_mul_of_nonneg_right (min_le_right A B) (sq_nonneg ‖y - x‖)
      have he : μ * M / (2 * (M + μ)) +
          (1 / (2 * (M + μ)) - γ / lam) * M ^ 2 = M / 2 - γ * M ^ 2 / lam := by
        field_simp [hi.2.2.2.2.1.ne', h.1.ne']
        ring
      have he2 : (2 - lam) / (2 * γ * lam) = (2 - lam) / (2 * lam * γ) := by ring
      rw [he2]
      dsimp [B] at hh
      nlinarith [congrArg (fun z : ℝ => z * ‖y - x‖ ^ 2) he]
  · have hi := strong_range_quadratic hL hσ.2 hγ h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
    have hl : 0 < lam := by linarith [h.2.1]
    let α := 2 * γ * L / lam
    have hα : 0 < α := by dsimp [α]; positivity
    have hα1 : α < 1 := by
      dsimp [α]
      apply (div_lt_one hl).2
      linarith [hi.1, h.2.1]
    let c := (2 - lam) / (2 * lam * γ) + σ * (1 / 2 - γ * L / lam)
    refine ⟨c, hi.2, ?_⟩
    intro x y
    have hs := hypoconvex_support hf hc y x
    have hc0 : ConvexOn ℝ univ f := by
      have hh := hypoconvex_mono hc h.1.le
      simpa only [IsHypoconvex, zero_div, zero_mul, sub_zero] using hh
    have hg := convex_bregman_gradient hf hc0 hL y x
    rw [norm_sub_rev x y] at hs
    rw [norm_sub_rev (gradient f x) (gradient f y)] at hg
    have h1 := mul_le_mul_of_nonneg_left hg hα.le
    have h2 := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1 - α by linarith)
    have he1 : α * (‖gradient f y - gradient f x‖ ^ 2 / (2 * L)) =
        γ / lam * ‖gradient f y - gradient f x‖ ^ 2 := by
      dsimp [α]
      field_simp
    have he2 : (1 - α) * (σ / 2) = σ * (1 / 2 - γ * L / lam) := by
      dsimp [α]
      ring
    have he3 : (2 - lam) / (2 * γ * lam) = (2 - lam) / (2 * lam * γ) := by ring
    rw [he1] at h1
    rw [he3]
    dsimp [c]
    nlinarith [congrArg (fun z : ℝ => z * ‖y - x‖ ^ 2) he2]

end DRSConvergenceProof


namespace DRSConvergenceProof

open Filter Topology

lemma energy_antitone {E r : ℕ → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k) : Antitone E := by
  apply antitone_nat_of_succ_le
  intro k
  have := hstep k
  have := mul_nonneg ha (sq_nonneg (r k))
  linarith

lemma energy_limit {E r : ℕ → ℝ} {a m : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hlower : ∀ k, m ≤ E k) : ∃ e : ℝ, Tendsto E atTop (nhds e) := by
  refine ⟨⨅ k, E k, tendsto_atTop_ciInf (energy_antitone ha hstep) ?_⟩
  exact ⟨m, by rintro _ ⟨k, rfl⟩; exact hlower k⟩

lemma energy_block {E r : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (m n : ℕ) (hb : ∀ i, m ≤ i → i < m + n → b ^ 2 ≤ (r i) ^ 2) :
    a * (n : ℝ) * b ^ 2 ≤ E m - E (m + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hmi hin => hb i hmi (by omega))
    have hlast := hstep (m + n)
    have hmul := mul_le_mul_of_nonneg_left (hb (m + n) (by omega) (by omega)) ha
    push_cast
    rw [show m + (n + 1) = m + n + 1 by omega]
    nlinarith

lemma residual_tendsto_zero {E r : ℕ → ℝ} {a e : ℝ} (ha : 0 < a)
    (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hE : Tendsto E atTop (nhds e)) : Tendsto r atTop (nhds 0) := by
  have hEs : Tendsto (fun k => E (k + 1)) atTop (nhds e) :=
    hE.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun k => (E k - E (k + 1)) / a) atTop (nhds 0) := by
    simpa using (hE.sub hEs).div_const a
  have hsquare : Tendsto (fun k => (r k) ^ 2) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdiff
    · exact fun k => sq_nonneg _
    · intro k
      apply (le_div_iff₀ ha).2
      nlinarith [hstep k]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq (hr _), Real.sqrt_zero] using hh

noncomputable def runningMin (r : ℕ → ℝ) (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one r

lemma runningMin_nonneg {r : ℕ → ℝ} (hr : ∀ k, 0 ≤ r k) (k : ℕ) :
    0 ≤ runningMin r k := by
  exact Finset.le_inf' Finset.nonempty_range_add_one r (fun i _ => hr i)

lemma runningMin_le {r : ℕ → ℝ} {i k : ℕ} (hi : i ≤ k) :
    runningMin r k ≤ r i := by
  exact Finset.inf'_le _ (Finset.mem_range.mpr (by omega))

lemma runningMin_rate {E r : ℕ → ℝ} {a e : ℝ} (ha : 0 < a)
    (hr : ∀ k, 0 ≤ r k)
    (hstep : ∀ k, E (k + 1) + a * (r k) ^ 2 ≤ E k)
    (hE : Tendsto E atTop (nhds e)) :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) * runningMin r k) atTop (nhds 0) := by
  have hh (k : ℕ) : (k : ℝ) * (runningMin r k) ^ 2 ≤
      (2 / a) * (E (k / 2) - E (k + 1)) := by
    have hcount : k / 2 + (k + 1 - k / 2) = k + 1 := by omega
    have hb := energy_block ha.le hstep (k / 2) (k + 1 - k / 2)
      (fun i _ hi => sq_le_sq₀ (runningMin_nonneg hr k) (hr i) |>.2
        (runningMin_le (by omega : i ≤ k)))
    rw [hcount] at hb
    have hc : (k : ℝ) ≤ 2 * ((k + 1 - k / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show k ≤ 2 * (k + 1 - k / 2) by omega)
    have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (runningMin r k))
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ ha).2
    nlinarith [mul_le_mul_of_nonneg_right hm ha.le]
  have hhalf : Tendsto (fun k : ℕ => E (k / 2)) atTop (nhds e) :=
    hE.comp (Nat.tendsto_div_const_atTop (by norm_num))
  have hnext : Tendsto (fun k => E (k + 1)) atTop (nhds e) :=
    hE.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto (fun k => (2 / a) * (E (k / 2) - E (k + 1)))
      atTop (nhds 0) := by simpa using (hhalf.sub hnext).const_mul (2 / a)
  have hsquare : Tendsto (fun k : ℕ => (k : ℝ) * (runningMin r k) ^ 2)
      atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun k => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hh
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_mul (Nat.cast_nonneg _),
    Real.sqrt_sq (runningMin_nonneg hr _), Real.sqrt_zero] using hs

end DRSConvergenceProof


namespace DRSConvergenceProof
open NonconvexDRS.DRS
open scoped RealInnerProductSpace

variable {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
  {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ : ℝ}

lemma prox_ne_top (hh : IsProper h) {s v : EuclideanSpace ℝ (Fin p)}
    (hv : v ∈ proxSet h γ s) : h v ≠ ⊤ := by
  obtain ⟨w, hw⟩ := hh.2
  have hfin : h w + ((‖w - s‖ ^ 2 / (2 * γ) : ℝ) : EReal) ≠ ⊤ := by
    rw [← EReal.coe_toReal hw (hh.1 w), ← EReal.coe_add]
    exact EReal.coe_ne_top _
  intro he
  apply hfin
  exact top_le_iff.mp (by simpa only [he, EReal.top_add_coe] using hv w)

lemma prox_real_comparison {s u : EuclideanSpace ℝ (Fin p)}
    (hu : u ∈ proxSet (fun x => (f x : EReal)) γ s) (w : EuclideanSpace ℝ (Fin p)) :
    f u + ‖u - s‖ ^ 2 / (2 * γ) ≤ f w + ‖w - s‖ ^ 2 / (2 * γ) := by
  have hh := hu w
  simpa only [← EReal.coe_add, EReal.coe_le_coe_iff] using hh

lemma prox_gradient_identity (hf : IsLSmooth f L) (hγ : 0 < γ)
    {s u : EuclideanSpace ℝ (Fin p)}
    (hu : u ∈ proxSet (fun x => (f x : EReal)) γ s) :
    s = u + γ • gradient f u := by
  have hscalar (z : EuclideanSpace ℝ (Fin p)) :
      inner ℝ (gradient f u) z + (2 * inner ℝ (u - s) z) / (2 * γ) = 0 := by
    have hdline : HasDerivAt (fun t : ℝ => u + t • z - s) z 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const z).const_add u).sub_const s
    have hdn := (hasStrictFDerivAt_norm_sq (u - s)).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hdline (by simp)
    have hdn' : HasDerivAt (fun t : ℝ => ‖u + t • z - s‖ ^ 2)
        (2 * inner ℝ (u - s) z) 0 := by
      convert hdn using 1 <;> try rfl
      simp only [two_smul, add_apply, innerSL_apply_apply]
      ring
    have hdf : HasDerivAt (fun t : ℝ => f (u + t • z))
        (inner ℝ (gradient f u) z) 0 := by
      simpa only [zero_smul, add_zero] using segment_derivative hf u z 0
    have hmin : IsLocalMin (fun t : ℝ => f (u + t • z) +
        ‖u + t • z - s‖ ^ 2 / (2 * γ)) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      simpa only [zero_smul, add_zero] using prox_real_comparison hu (u + t • z)
    exact hmin.hasDerivAt_eq_zero (hdf.add (hdn'.div_const (2 * γ)))
  apply ext_inner_right ℝ
  intro z
  have hh := hscalar z
  simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at hh ⊢
  have hz : 2 * γ ≠ 0 := by positivity
  field_simp at hh
  nlinarith

lemma prox_unique (hf : IsLSmooth f L) (hγ : 0 < γ) (hsmall : γ * L < 1)
    {s u w : EuclideanSpace ℝ (Fin p)}
    (hu : u ∈ proxSet (fun x => (f x : EReal)) γ s)
    (hw : w ∈ proxSet (fun x => (f x : EReal)) γ s) : u = w := by
  have h1 := prox_gradient_identity hf hγ hu
  have h2 := prox_gradient_identity hf hγ hw
  have he : u - w = γ • (gradient f w - gradient f u) := by
    calc
      u - w = (u + γ • gradient f u) - (w + γ • gradient f w) +
          γ • (gradient f w - gradient f u) := by module
      _ = γ • (gradient f w - gradient f u) := by rw [← h1, ← h2]; simp
  have hn := congrArg norm he
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at hn
  have hb := mul_le_mul_of_nonneg_left (hf.2 w u) hγ.le
  rw [norm_sub_rev w u] at hb
  have hz : ‖u - w‖ = 0 := by nlinarith [norm_nonneg (u - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end DRSConvergenceProof


namespace DRSConvergenceProof
open NonconvexDRS.DRS
open scoped RealInnerProductSpace

variable {p : ℕ}

noncomputable def model (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (h : EuclideanSpace ℝ (Fin p) → EReal) (γ : ℝ)
    (u w : EuclideanSpace ℝ (Fin p)) : EReal :=
  h w + ((f u + inner ℝ (gradient f u) (w - u) + ‖w - u‖ ^ 2 / (2 * γ) : ℝ) : EReal)

noncomputable def energy (f : EuclideanSpace ℝ (Fin p) → ℝ)
    (h : EuclideanSpace ℝ (Fin p) → EReal) (γ : ℝ)
    (u v : EuclideanSpace ℝ (Fin p)) : ℝ :=
  f u + (h v).toReal + inner ℝ (gradient f u) (v - u) + ‖v - u‖ ^ 2 / (2 * γ)

lemma model_eq_energy {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {γ : ℝ}
    {u v : EuclideanSpace ℝ (Fin p)} (ht : h v ≠ ⊤) (hb : h v ≠ ⊥) :
    model f h γ u v = (energy f h γ u v : EReal) := by
  unfold model energy
  rw [← EReal.coe_toReal ht hb, ← EReal.coe_add]
  simp only [EReal.toReal_coe]
  congr 1
  ring

lemma prox_model_square {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {γ : ℝ} (hγ : 0 < γ) {s u : EuclideanSpace ℝ (Fin p)}
    (hs : s = u + γ • gradient f u) (w : EuclideanSpace ℝ (Fin p)) :
    ‖w - ((2 : ℝ) • u - s)‖ ^ 2 / (2 * γ) =
      inner ℝ (gradient f u) (w - u) + ‖w - u‖ ^ 2 / (2 * γ) +
        γ / 2 * ‖gradient f u‖ ^ 2 := by
  have he : w - ((2 : ℝ) • u - s) = (w - u) + γ • gradient f u := by rw [hs]; module
  rw [he, norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hγ,
    inner_smul_right, real_inner_comm (w - u) (gradient f u)]
  field_simp
  ring

lemma model_minimum {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ : ℝ}
    (hf : IsLSmooth f L) (hh : IsProper h) (hγ : 0 < γ)
    {s u v : EuclideanSpace ℝ (Fin p)}
    (hu : u ∈ proxSet (fun x => (f x : EReal)) γ s)
    (hv : v ∈ proxSet h γ ((2 : ℝ) • u - s)) (w : EuclideanSpace ℝ (Fin p)) :
    (energy f h γ u v : EReal) ≤ model f h γ u w := by
  have hvt := prox_ne_top hh hv
  by_cases hwt : h w = ⊤
  · unfold model
    rw [hwt, EReal.top_add_coe]
    exact le_top
  have hc := hv w
  rw [← EReal.coe_toReal hvt (hh.1 v), ← EReal.coe_toReal hwt (hh.1 w),
    ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hc
  have hs := prox_gradient_identity hf hγ hu
  rw [prox_model_square hγ hs v, prox_model_square hγ hs w] at hc
  rw [model_eq_energy hwt (hh.1 w), EReal.coe_le_coe_iff]
  unfold energy
  linarith

lemma envelope_eq_energy {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ : ℝ}
    (hf : IsLSmooth f L) (hh : IsProper h) (hγ : 0 < γ) (hsmall : γ * L < 1)
    {s u v : EuclideanSpace ℝ (Fin p)}
    (hu : u ∈ proxSet (fun x => (f x : EReal)) γ s)
    (hv : v ∈ proxSet h γ ((2 : ℝ) • u - s)) :
    dre f h γ s = (energy f h γ u v : EReal) := by
  have hinner : dreAt f h γ u = (energy f h γ u v : EReal) := by
    apply le_antisymm
    · exact (iInf_le (fun w => model f h γ u w) v).trans_eq
        (model_eq_energy (prox_ne_top hh hv) (hh.1 v))
    · exact le_iInf (model_minimum hf hh hγ hu hv)
  apply le_antisymm
  · exact (iInf_le_of_le u (iInf_le_of_le hu le_rfl)).trans hinner.le
  · apply le_iInf
    intro w
    apply le_iInf
    intro hw
    have he := prox_unique hf hγ hsmall hw hu
    subst w
    exact hinner.ge

end DRSConvergenceProof


namespace DRSConvergenceProof
open NonconvexDRS.DRS
open scoped RealInnerProductSpace

variable {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
  {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ : ℝ}

lemma minimum_real_lower (hh : IsProper h)
    (hsol : ∃ xs, ∀ x, phi f h xs ≤ phi f h x) :
    ∃ m : ℝ, ∀ x, (m : EReal) ≤ phi f h x := by
  obtain ⟨xs, hxs⟩ := hsol
  obtain ⟨w, hw⟩ := hh.2
  have hxt : h xs ≠ ⊤ := by
    have hc := hxs w
    rw [phi, phi, ← EReal.coe_toReal hw (hh.1 w), ← EReal.coe_add] at hc
    intro he
    rw [he, EReal.coe_add_top] at hc
    exact EReal.coe_ne_top _ (top_le_iff.mp hc)
  refine ⟨f xs + (h xs).toReal, ?_⟩
  intro x
  rw [EReal.coe_add, EReal.coe_toReal hxt (hh.1 xs)]
  exact hxs x

lemma phi_eq_real (hh : IsProper h) {v : EuclideanSpace ℝ (Fin p)} (hv : h v ≠ ⊤) :
    phi f h v = ((f v + (h v).toReal : ℝ) : EReal) := by
  rw [phi, EReal.coe_add, EReal.coe_toReal hv (hh.1 v)]

lemma cost_le_energy (hf : IsLSmooth f L) (hh : IsProper h) (hγ : 0 < γ)
    (hsmall : γ * L < 1) {u v : EuclideanSpace ℝ (Fin p)} (hv : h v ≠ ⊤) :
    phi f h v ≤ (energy f h γ u v : EReal) := by
  rw [phi_eq_real hh hv, EReal.coe_le_coe_iff]
  have hs := smooth_descent hf u (v - u)
  simp only [add_sub_cancel] at hs
  have hc : L / 2 ≤ 1 / (2 * γ) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * γ)).2
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (‖v - u‖))
  unfold energy
  simp only [div_eq_mul_inv, one_mul] at *
  nlinarith

lemma energy_bounded_below (hf : IsLSmooth f L) (hh : IsProper h) (hγ : 0 < γ)
    (hsmall : γ * L < 1) {m : ℝ} (hm : ∀ x, (m : EReal) ≤ phi f h x)
    {u v : EuclideanSpace ℝ (Fin p)} (hv : h v ≠ ⊤) :
    m ≤ energy f h γ u v := by
  exact EReal.coe_le_coe_iff.mp ((hm v).trans (cost_le_energy hf hh hγ hsmall hv))

end DRSConvergenceProof


namespace DRSConvergenceProof
open scoped RealInnerProductSpace

lemma model_difference_identity {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (d q r : F) {γ lam : ℝ} (hγ : γ ≠ 0) (hlam : lam ≠ 0)
    (he : lam • r = d + γ • q) :
    -inner ℝ q r + (‖r‖ ^ 2 - ‖r - d‖ ^ 2) / (2 * γ) =
      (2 - lam) / (2 * γ * lam) * ‖d‖ ^ 2 - γ / lam * ‖q‖ ^ 2 := by
  have hq := congrArg (fun z => inner ℝ q z) he
  have hd := congrArg (fun z => inner ℝ z d) he
  simp only [inner_smul_right, real_inner_smul_left, inner_add_right, inner_add_left,
    real_inner_self_eq_norm_sq] at hq hd
  rw [norm_sub_sq_real]
  field_simp
  nlinarith [congrArg (fun x : ℝ => γ * x) hq]

lemma envelope_difference_identity {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x y v gx gy : F) (fx fy hv : ℝ) {γ lam : ℝ}
    (hγ : γ ≠ 0) (hlam : lam ≠ 0)
    (he : lam • (v - x) = (y - x) + γ • (gy - gx)) :
    (fx + hv + inner ℝ gx (v - x) + ‖v - x‖ ^ 2 / (2 * γ)) -
      (fy + hv + inner ℝ gy (v - y) + ‖v - y‖ ^ 2 / (2 * γ)) =
    (2 - lam) / (2 * γ * lam) * ‖y - x‖ ^ 2 - γ / lam * ‖gy - gx‖ ^ 2 +
      (fx - fy - inner ℝ gy (x - y)) := by
  have hh := model_difference_identity (y - x) (gy - gx) (v - x) hγ hlam he
  have hvy : v - y = (v - x) - (y - x) := by abel
  rw [hvy]
  simp only [inner_sub_right, inner_sub_left] at hh ⊢
  have hneg : inner ℝ gy (x - y) = -inner ℝ gy (y - x) := by
    rw [← neg_sub y x, inner_neg_right]
  simp only [inner_sub_right] at hneg
  rw [sub_div] at hh
  linarith

end DRSConvergenceProof


namespace DRSConvergenceProof
open NonconvexDRS.DRS
open scoped RealInnerProductSpace

lemma run_increment {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ lam : ℝ}
    (hf : IsLSmooth f L) (hγ : 0 < γ)
    {s u v : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : IsDRSRun f h γ lam s u v)
    (k : ℕ) : lam • (v k - u k) = (u (k+1) - u k) +
      γ • (gradient f (u (k+1)) - gradient f (u k)) := by
  have h0 := prox_gradient_identity hf hγ (hrun k).1
  have h1 := prox_gradient_identity hf hγ (hrun (k+1)).1
  have hs := (hrun k).2.2
  rw [h0, h1] at hs
  calc
    lam • (v k - u k) = (u k + γ • gradient f (u k) + lam • (v k-u k)) -
        (u k + γ • gradient f (u k)) := by abel
    _ = (u (k+1) + γ • gradient f (u (k+1))) -
        (u k + γ • gradient f (u k)) := by rw [← hs]
    _ = _ := by module

lemma energy_step_from_coefficient {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ lam c : ℝ}
    (hf : IsLSmooth f L) (hh : IsProper h) (hγ : 0 < γ) (hlam : 0 < lam)
    (hc : ∀ x y : EuclideanSpace ℝ (Fin p), c * ‖y-x‖^2 ≤
      (2-lam)/(2*γ*lam)*‖y-x‖^2 - γ/lam*‖gradient f y-gradient f x‖^2 +
      (f x-f y-inner ℝ (gradient f y) (x-y)))
    {s u v : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : IsDRSRun f h γ lam s u v)
    (k : ℕ) : energy f h γ (u (k+1)) (v (k+1)) +
      c * ‖u (k+1)-u k‖^2 ≤ energy f h γ (u k) (v k) := by
  have hm := model_minimum hf hh hγ (hrun (k+1)).1 (hrun (k+1)).2.1 (v k)
  rw [model_eq_energy (prox_ne_top hh (hrun k).2.1) (hh.1 (v k)),
    EReal.coe_le_coe_iff] at hm
  have he := envelope_difference_identity (u k) (u (k+1)) (v k)
    (gradient f (u k)) (gradient f (u (k+1))) (f (u k)) (f (u (k+1)))
    (h (v k)).toReal hγ.ne' hlam.ne' (run_increment hf hγ hrun k)
  have hb := hc (u k) (u (k+1))
  change energy f h γ (u k) (v k) - energy f h γ (u (k+1)) (v k) = _ at he
  linarith

lemma residual_step_bound {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ lam : ℝ}
    (hf : IsLSmooth f L) (hγ : 0 < γ) (hlam : 0 < lam)
    {s u v : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : IsDRSRun f h γ lam s u v)
    (k : ℕ) : lam * ‖u k-v k‖ ≤ (1+γ*L)*‖u (k+1)-u k‖ := by
  have he := congrArg norm (run_increment hf hγ hrun k)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, norm_sub_rev (v k) (u k)] at he
  have hn := norm_add_le (u (k+1)-u k)
    (γ • (gradient f (u (k+1))-gradient f (u k)))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at hn
  have hg := mul_le_mul_of_nonneg_left (hf.2 (u (k+1)) (u k)) hγ.le
  nlinarith

lemma energy_descent {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L σ γ lam : ℝ}
    (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L) (hf : IsLSmooth f L)
    (hhyp : IsHypoconvex f σ) (hh : IsProper h) (hγ : 0 < γ)
    (hr : StepRange L σ γ lam)
    {s u v : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : IsDRSRun f h γ lam s u v) :
    ∃ a : ℝ, 0 < a ∧ ∀ k, energy f h γ (u (k+1)) (v (k+1)) +
      a * ‖u k-v k‖^2 ≤ energy f h γ (u k) (v k) := by
  have hbounds := range_bounds hL hσ hγ hr
  rcases bregman_decrease_bound hL hσ hf hhyp hγ hr with ⟨c,hc,hcoef⟩
  have hden : 0 < 1+γ*L := by positivity
  refine ⟨c * (lam / (1+γ*L))^2, mul_pos hc (sq_pos_of_pos (div_pos hbounds.1 hden)), ?_⟩
  intro k
  have hs := energy_step_from_coefficient hf hh hγ hbounds.1 hcoef hrun k
  have hb := residual_step_bound hf hγ hbounds.1 hrun k
  have hrb : lam / (1+γ*L) * ‖u k-v k‖ ≤ ‖u (k+1)-u k‖ := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).2 (by nlinarith [hb])
  have hsq := sq_le_sq₀ (mul_nonneg (div_pos hbounds.1 hden).le (norm_nonneg _))
    (norm_nonneg (u (k+1)-u k)) |>.2 hrb
  have hcq := mul_le_mul_of_nonneg_left hsq hc.le
  nlinarith

end DRSConvergenceProof


namespace DRSConvergenceProof
open Filter Topology NonconvexDRS.DRS
open scoped RealInnerProductSpace

variable {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
  {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ : ℝ}

lemma smooth_model_tendsto (hf : IsLSmooth f L) (hL : 0 ≤ L)
    {u v : ℕ → EuclideanSpace ℝ (Fin p)} {y : EuclideanSpace ℝ (Fin p)}
    (hu : Tendsto u atTop (nhds y)) (hv : Tendsto v atTop (nhds y)) :
    Tendsto (fun k => f (u k) + inner ℝ (gradient f (u k)) (v k - u k) +
      ‖v k - u k‖ ^ 2 / (2 * γ)) atTop (nhds (f y)) := by
  have hg := (gradient_continuous hf hL).tendsto y |>.comp hu
  have hd := hv.sub hu
  have ht := ((hf.1.continuous.tendsto y).comp hu).add (hg.inner hd)
  have hh := ht.add (hd.norm.pow 2 |>.div_const (2 * γ))
  simpa using hh

lemma fixed_model_tendsto (hf : IsLSmooth f L) (hL : 0 ≤ L)
    {u : ℕ → EuclideanSpace ℝ (Fin p)} {y : EuclideanSpace ℝ (Fin p)}
    (hu : Tendsto u atTop (nhds y)) :
    Tendsto (fun k => energy f h γ (u k) y) atTop
      (nhds (f y + (h y).toReal)) := by
  have hh := (smooth_model_tendsto (γ := γ) hf hL hu tendsto_const_nhds).add_const
    (h y).toReal
  convert hh using 1
  ext k
  unfold energy
  ring

lemma cluster_value (hf : IsLSmooth f L) (hL : 0 ≤ L) (hh : IsProper h)
    (hlsc : LowerSemicontinuous h) (hγ : 0 < γ)
    {s u v : ℕ → EuclideanSpace ℝ (Fin p)} {y : EuclideanSpace ℝ (Fin p)} {e : ℝ}
    (hup : ∀ k, u k ∈ proxSet (fun x => (f x : EReal)) γ (s k))
    (hvp : ∀ k, v k ∈ proxSet h γ ((2 : ℝ) • u k - s k))
    (hu : Tendsto u atTop (nhds y)) (hv : Tendsto v atTop (nhds y))
    (hE : Tendsto (fun k => energy f h γ (u k) (v k)) atTop (nhds e)) :
    h y ≠ ⊤ ∧ phi f h y = (e : EReal) ∧
      Tendsto (fun k => (h (v k)).toReal) atTop (nhds ((h y).toReal)) := by
  have hreal : Tendsto (fun k => (h (v k)).toReal) atTop (nhds (e - f y)) := by
    have ht := hE.sub (smooth_model_tendsto (γ := γ) hf hL hu hv)
    convert ht using 1
    ext k
    unfold energy
    ring
  have hcoe : Tendsto (fun k => h (v k)) atTop (nhds ((e - f y : ℝ) : EReal)) := by
    have ht := EReal.tendsto_coe.mpr hreal
    simpa only [EReal.coe_toReal (prox_ne_top hh (hvp _)) (hh.1 _)] using ht
  have hle : h y ≤ ((e - f y : ℝ) : EReal) :=
    hlsc.isClosed_epigraph.mem_of_tendsto (hv.prodMk_nhds hcoe)
      (Filter.Eventually.of_forall (fun _ => show h (v _) ≤ h (v _) from le_rfl))
  have hyt : h y ≠ ⊤ := by
    intro he
    rw [he] at hle
    exact EReal.coe_ne_top _ (top_le_iff.mp hle)
  have hlow : f y + (h y).toReal ≤ e := by
    rw [← EReal.coe_toReal hyt (hh.1 y), EReal.coe_le_coe_iff] at hle
    linarith
  have hupper : e ≤ f y + (h y).toReal := by
    apply le_of_tendsto_of_tendsto hE (fixed_model_tendsto (h := h) (γ := γ) hf hL hu)
    apply Filter.Eventually.of_forall
    intro k
    have hm := model_minimum hf hh hγ (hup k) (hvp k) y
    rw [model_eq_energy hyt (hh.1 y), EReal.coe_le_coe_iff] at hm
    exact hm
  have he : e = f y + (h y).toReal := le_antisymm hupper hlow
  refine ⟨hyt, ?_, ?_⟩
  · rw [phi_eq_real hh hyt, he]
  · simpa only [he, add_sub_cancel_left] using hreal

end DRSConvergenceProof


namespace DRSConvergenceProof
open Filter Topology NonconvexDRS.DRS NonconvexSplitting.Shared
open scoped RealInnerProductSpace

lemma regular_of_quadratic_support {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {h : F → EReal} {y : F} {K : ℝ} (hyt : h y ≠ ⊤) (hK : 0 ≤ K)
    (hs : ∀ w, h y + ((-K * ‖w - y‖ ^ 2 : ℝ) : EReal) ≤ h w) :
    IsRegularSubgrad h y 0 := by
  refine ⟨hyt, ?_⟩
  intro ε hε
  filter_upwards [Metric.ball_mem_nhds y (div_pos hε (by linarith : 0 < K + 1))] with w hw
  have hn : ‖w - y‖ < ε / (K + 1) := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hb := (lt_div_iff₀ (by linarith : 0 < K + 1)).mp hn
  have hprod := mul_le_mul_of_nonneg_right hb.le (norm_nonneg (w - y))
  have hc : -ε * ‖w - y‖ ≤ -K * ‖w - y‖ ^ 2 := by nlinarith [sq_nonneg ‖w - y‖]
  simp only [inner_zero_left, zero_sub]
  simpa only [neg_mul] using (add_le_add_right (EReal.coe_le_coe hc) (h y)).trans (hs w)

variable {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
  {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ : ℝ}

lemma model_tendsto_competitor (hf : IsLSmooth f L) (hL : 0 ≤ L)
    {u : ℕ → EuclideanSpace ℝ (Fin p)} {y : EuclideanSpace ℝ (Fin p)}
    (hu : Tendsto u atTop (nhds y)) (w : EuclideanSpace ℝ (Fin p)) :
    Tendsto (fun k => energy f h γ (u k) w) atTop
      (nhds (energy f h γ y w)) := by
  have hg := (gradient_continuous hf hL).tendsto y |>.comp hu
  have hd := tendsto_const_nhds.sub hu (a := w)
  exact (((hf.1.continuous.tendsto y |>.comp hu).add_const (h w).toReal).add
    (hg.inner hd)).add (hd.norm.pow 2 |>.div_const (2 * γ))

lemma cluster_regular (hf : IsLSmooth f L) (hL : 0 ≤ L) (hh : IsProper h)
    (hγ : 0 < γ) {s u v : ℕ → EuclideanSpace ℝ (Fin p)}
    {y : EuclideanSpace ℝ (Fin p)} {e : ℝ}
    (hup : ∀ k, u k ∈ proxSet (fun x => (f x : EReal)) γ (s k))
    (hvp : ∀ k, v k ∈ proxSet h γ ((2 : ℝ) • u k - s k))
    (hu : Tendsto u atTop (nhds y))
    (hE : Tendsto (fun k => energy f h γ (u k) (v k)) atTop (nhds e))
    (hyt : h y ≠ ⊤) (hvalue : phi f h y = (e : EReal)) :
    IsRegularSubgrad (phi f h) y 0 := by
  have he : f y + (h y).toReal = e := by
    rw [phi_eq_real hh hyt] at hvalue
    exact EReal.coe_injective hvalue
  have hpt : phi f h y ≠ ⊤ := by rw [hvalue]; exact EReal.coe_ne_top _
  apply regular_of_quadratic_support hpt (show 0 ≤ (L + 1 / γ) / 2 by positivity)
  intro w
  by_cases hwt : h w = ⊤
  · simp [phi, hwt]
  have hm : e ≤ energy f h γ y w := by
    apply le_of_tendsto_of_tendsto hE (model_tendsto_competitor (h := h) (γ := γ) hf hL hu w)
    apply Filter.Eventually.of_forall
    intro k
    have hc := model_minimum hf hh hγ (hup k) (hvp k) w
    rw [model_eq_energy hwt (hh.1 w), EReal.coe_le_coe_iff] at hc
    exact hc
  have hs := smooth_lower hf y w
  rw [phi_eq_real hh hyt, phi_eq_real hh hwt, ← EReal.coe_add, EReal.coe_le_coe_iff]
  unfold energy at hm
  rw [← he] at hm
  field_simp at *
  nlinarith

end DRSConvergenceProof


namespace DRSConvergenceProof
open Filter Topology NonconvexDRS.DRS NonconvexSplitting.Shared
open scoped RealInnerProductSpace

lemma cluster_sets_equal {F : Type*} [NormedAddCommGroup F] [FirstCountableTopology F]
    {u v : ℕ → F} (hd : Tendsto (fun k => u k-v k) atTop (nhds 0)) :
    {y | MapClusterPt y atTop u} = {y | MapClusterPt y atTop v} := by
  ext y
  constructor
  · intro hy
    obtain ⟨ψ,hψ,hu⟩ := hy.tendsto_subseq
    have hv : Tendsto (v ∘ ψ) atTop (nhds y) := by
      have ht := hu.sub (hd.comp hψ.tendsto_atTop)
      simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using ht
    exact MapClusterPt.of_comp hψ.tendsto_atTop hv.mapClusterPt
  · intro hy
    obtain ⟨ψ,hψ,hv⟩ := hy.tendsto_subseq
    have hu : Tendsto (u ∘ ψ) atTop (nhds y) := by
      have ht := (hd.comp hψ.tendsto_atTop).add hv
      simpa only [Function.comp_def, sub_add_cancel, zero_add] using ht
    exact MapClusterPt.of_comp hψ.tendsto_atTop hu.mapClusterPt

lemma run_cluster_conclusions {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ lam e : ℝ}
    (hf : IsLSmooth f L) (hL : 0 ≤ L) (hh : IsProper h)
    (hlsc : LowerSemicontinuous h) (hγ : 0 < γ)
    {s u v : ℕ → EuclideanSpace ℝ (Fin p)} (hrun : IsDRSRun f h γ lam s u v)
    (hd : Tendsto (fun k => u k-v k) atTop (nhds 0))
    (hE : Tendsto (fun k => energy f h γ (u k) (v k)) atTop (nhds e)) :
    ∀ y, MapClusterPt y atTop u → IsRegularSubgrad (phi f h) y 0 ∧ phi f h y = (e : EReal) := by
  intro y hy
  obtain ⟨ψ,hψ,hu⟩ := hy.tendsto_subseq
  have hv : Tendsto (v ∘ ψ) atTop (nhds y) := by
    have ht := hu.sub (hd.comp hψ.tendsto_atTop)
    simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using ht
  have he := hE.comp hψ.tendsto_atTop
  have hp := cluster_value hf hL hh hlsc hγ
    (fun k => (hrun (ψ k)).1) (fun k => (hrun (ψ k)).2.1) hu hv he
  exact ⟨cluster_regular hf hL hh hγ (fun k => (hrun (ψ k)).1)
    (fun k => (hrun (ψ k)).2.1) hu he hp.1 hp.2.1, hp.2.1⟩

lemma run_bounded {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {h : EuclideanSpace ℝ (Fin p) → EReal} {L γ lam : ℝ}
    (hf : IsLSmooth f L) (hL : 0 ≤ L) (hh : IsProper h) (hγ : 0 < γ)
    (hsmall : γ*L < 1) {s u v : ℕ → EuclideanSpace ℝ (Fin p)}
    (hrun : IsDRSRun f h γ lam s u v)
    (hanti : Antitone (fun k => energy f h γ (u k) (v k)))
    (hd : Tendsto (fun k => u k-v k) atTop (nhds 0)) (hlb : LevelBounded (phi f h)) :
    Bornology.IsBounded (Set.range s) ∧ Bornology.IsBounded (Set.range u) ∧
      Bornology.IsBounded (Set.range v) := by
  have hvb : Bornology.IsBounded (Set.range v) := by
    apply (hlb (energy f h γ (u 0) (v 0))).subset
    rintro _ ⟨k,rfl⟩
    exact (cost_le_energy hf hh hγ hsmall (prox_ne_top hh (hrun k).2.1)).trans
      (EReal.coe_le_coe (hanti (Nat.zero_le k)))
  obtain ⟨B,hB⟩ := hvb.exists_norm_le
  obtain ⟨D,hD⟩ := (hd.cauchySeq.isBounded_range).exists_norm_le
  have huB (k : ℕ) : ‖u k‖ ≤ D+B := by
    have hn := norm_add_le (u k-v k) (v k)
    rw [sub_add_cancel] at hn
    exact hn.trans (add_le_add (hD _ (Set.mem_range_self k)) (hB _ (Set.mem_range_self k)))
  have hub : Bornology.IsBounded (Set.range u) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨D+B, by rintro _ ⟨k,rfl⟩; exact huB k⟩
  refine ⟨?_,hub,hvb⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨D+B+γ*(L*(D+B)+‖gradient f 0‖), ?_⟩
  rintro _ ⟨k,rfl⟩
  rw [prox_gradient_identity hf hγ (hrun k).1]
  have hg := hf.2 (u k) 0
  rw [sub_zero] at hg
  have hgB : ‖gradient f (u k)‖ ≤ L*(D+B)+‖gradient f 0‖ := by
    have hn := norm_add_le (gradient f (u k)-gradient f 0) (gradient f 0)
    rw [sub_add_cancel] at hn
    exact hn.trans (add_le_add_left (hg.trans (mul_le_mul_of_nonneg_left (huB k) hL)) _)
  have hn := norm_add_le (u k) (γ • gradient f (u k))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ] at hn
  exact hn.trans (add_le_add (huB k) (mul_le_mul_of_nonneg_left hgB hγ.le))

end DRSConvergenceProof


namespace DRSConvergenceProof
open Filter Topology NonconvexDRS.DRS NonconvexSplitting.Shared

/-- Theorem 4.3 (Subsequential convergence), p. 13, without the "In fact" sentence of (ii)
(see `theorem_4_3_ii_dist`). -/
theorem full_native_result {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ lam : ℝ) (hγ : 0 < γ) (hrange : StepRange L σ γ lam)
    (s u v : ℕ → EuclideanSpace ℝ (Fin p)) (hrun : IsDRSRun φ₁ φ₂ γ lam s u v) :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) *
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (fun i => ‖u i - v i‖))
      atTop (𝓝 0) ∧
    ({y | MapClusterPt y atTop u} = {y | MapClusterPt y atTop v} ∧
      (∀ y, MapClusterPt y atTop u → IsRegularSubgrad (phi φ₁ φ₂) y 0) ∧
      ∃ φstar : ℝ, Tendsto (fun k => dre φ₁ φ₂ γ (s k)) atTop (𝓝 (φstar : EReal)) ∧
        ∀ y, MapClusterPt y atTop u → phi φ₁ φ₂ y = φstar) ∧
    (LevelBounded (phi φ₁ φ₂) →
      Bornology.IsBounded (Set.range s) ∧ Bornology.IsBounded (Set.range u) ∧
        Bornology.IsBounded (Set.range v)) := by
  have hb := range_bounds hL hσ hγ hrange
  obtain ⟨a,ha,hstep⟩ := energy_descent hL hσ hsmooth hhypo hprop hγ hrange hrun
  obtain ⟨m,hm⟩ := minimum_real_lower (f := φ₁) hprop hsol
  have hlo (k : ℕ) : m ≤ energy φ₁ φ₂ γ (u k) (v k) :=
    energy_bounded_below hsmooth hprop hγ hb.2.1 hm (prox_ne_top hprop (hrun k).2.1)
  obtain ⟨e,he⟩ := energy_limit ha.le hstep hlo
  have hr0 := residual_tendsto_zero ha (fun k => norm_nonneg (u k-v k)) hstep he
  have hd : Tendsto (fun k => u k-v k) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hr0
  have hc := run_cluster_conclusions hsmooth hL.le hprop hlsc hγ hrun hd he
  refine ⟨runningMin_rate ha (fun k => norm_nonneg (u k-v k)) hstep he, ?_, ?_⟩
  · refine ⟨cluster_sets_equal hd, fun y hy => (hc y hy).1, e, ?_, fun y hy => (hc y hy).2⟩
    have hh := EReal.tendsto_coe.mpr he
    convert hh using 1
    ext k
    exact envelope_eq_energy hsmooth hprop hγ hb.2.1 (hrun k).1 (hrun k).2.1
  · exact run_bounded hsmooth hL.le hprop hγ hb.2.1 hrun (energy_antitone ha.le hstep) hd


end DRSConvergenceProof


open Filter Topology NonconvexDRS.DRS NonconvexSplitting.Shared

namespace NonconvexDRS.DRS

/-- Theorem 4.3 (Subsequential convergence), p. 13, without the "In fact" sentence of (ii)
(see `theorem_4_3_ii_dist`). -/
theorem theorem_4_3 {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ lam : ℝ) (hγ : 0 < γ) (hrange : StepRange L σ γ lam)
    (s u v : ℕ → EuclideanSpace ℝ (Fin p)) (hrun : IsDRSRun φ₁ φ₂ γ lam s u v) :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) *
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (fun i => ‖u i - v i‖))
      atTop (𝓝 0) ∧
    ({y | MapClusterPt y atTop u} = {y | MapClusterPt y atTop v} ∧
      (∀ y, MapClusterPt y atTop u → IsRegularSubgrad (phi φ₁ φ₂) y 0) ∧
      ∃ φstar : ℝ, Tendsto (fun k => dre φ₁ φ₂ γ (s k)) atTop (𝓝 (φstar : EReal)) ∧
        ∀ y, MapClusterPt y atTop u → phi φ₁ φ₂ y = φstar) ∧
    (LevelBounded (phi φ₁ φ₂) →
      Bornology.IsBounded (Set.range s) ∧ Bornology.IsBounded (Set.range u) ∧
        Bornology.IsBounded (Set.range v)) := by
  exact DRSConvergenceProof.full_native_result φ₁ φ₂ L σ hL hσ hsmooth hhypo hprop hlsc hsol γ lam hγ hrange s u v hrun

end NonconvexDRS.DRS

open Filter Topology NonconvexDRS.DRS NonconvexSplitting.Shared

theorem solution {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ lam : ℝ) (hγ : 0 < γ) (hrange : StepRange L σ γ lam)
    (s u v : ℕ → EuclideanSpace ℝ (Fin p)) (hrun : IsDRSRun φ₁ φ₂ γ lam s u v) :
    Tendsto (fun k : ℕ => Real.sqrt (k : ℝ) *
        (Finset.range (k + 1)).inf' Finset.nonempty_range_add_one (fun i => ‖u i - v i‖))
      atTop (𝓝 0) ∧
    ({y | MapClusterPt y atTop u} = {y | MapClusterPt y atTop v} ∧
      (∀ y, MapClusterPt y atTop u → IsRegularSubgrad (phi φ₁ φ₂) y 0) ∧
      ∃ φstar : ℝ, Tendsto (fun k => dre φ₁ φ₂ γ (s k)) atTop (𝓝 (φstar : EReal)) ∧
        ∀ y, MapClusterPt y atTop u → phi φ₁ φ₂ y = φstar) ∧
    (LevelBounded (phi φ₁ φ₂) →
      Bornology.IsBounded (Set.range s) ∧ Bornology.IsBounded (Set.range u) ∧
        Bornology.IsBounded (Set.range v)) := NonconvexDRS.DRS.theorem_4_3 φ₁ φ₂ L σ hL hσ hsmooth hhypo hprop hlsc hsol γ lam hγ hrange s u v hrun
