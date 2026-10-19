-- Prove2me | solution 1 for NesterovODE.Restart.theorem_10
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-18T02:36:37.413186+00:00
-- url     : https://prove2.me/submissions/eec48f87-e750-41f0-9dce-1b764ae0552d

-- Licensed under Apache 2.0. Complete speed-restarted singular ODE convergence theorem.
import Mathlib
import Definitions.Def_NesterovODE_Restart_Setting


open Set NesterovODE.WellPosed
open scoped RealInnerProductSpace

namespace SpeedRestartProof

open NesterovODE.StrongCvx

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

variable {n : ℕ} {f : E n → ℝ} {μ : ℝ} {L : NNReal}

lemma gradient_at_minimum (hf : ContDiff ℝ 1 f) {xstar : E n}
    (hmin : ∀ y, f xstar ≤ f y) : gradient f xstar = 0 := by
  have hlocal : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  have hz := hlocal.hasFDerivAt_eq_zero
    ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt)
  simp [gradient, hz]

lemma convex_gradient_support (hf : IsFL f L) (x y : E n) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  rw [inner_gradient_left]
  exact convex_fderiv_support hf.2.1 x y
    ((hf.2.2.1.differentiable one_ne_zero).differentiableAt)

lemma stationary_minimum (hf : IsFL f L) {x : E n} (hg : gradient f x = 0) :
    ∀ y, f x ≤ f y := by
  intro y
  simpa [hg] using convex_gradient_support hf x y

lemma strong_support (hf : InSMuL μ L f) (x y : E n) :
    f x + inner ℝ (gradient f x) (y - x) + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hd := ((hf.2.1.differentiable one_ne_zero).differentiableAt (x := x)).hasFDerivAt.sub
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (μ / 2))
  have hh := convex_fderiv_support hf.2.2 x y hd.differentiableAt
  have hd' : HasFDerivAt (fun z => f z - μ / 2 * ‖z‖ ^ 2)
      (fderiv ℝ f x - (μ / 2) • (2 • innerSL ℝ x)) x := by
    convert hd using 1 <;> rfl
  rw [hd'.fderiv] at hh
  simp only [sub_apply, smul_apply,
    smul_eq_mul, innerSL_apply_apply, ← inner_gradient_left] at hh
  simp only [inner_sub_right, two_smul, real_inner_self_eq_norm_sq] at hh
  rw [norm_sub_sq_real, inner_sub_right]
  have hxy : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [hxy]
  nlinarith

lemma pl_bound (hf : InSMuL μ L f) (hμ : 0 < μ) (x xstar : E n)
    (_hmin : ∀ y, f xstar ≤ f y) :
    2 * μ * (f x - f xstar) ≤ ‖gradient f x‖ ^ 2 := by
  have hs := strong_support hf x xstar
  have hi := real_inner_le_norm (gradient f x) (x - xstar)
  have hn : ‖xstar - x‖ = ‖x - xstar‖ := norm_sub_rev _ _
  have he : inner ℝ (gradient f x) (xstar - x) =
      -inner ℝ (gradient f x) (x - xstar) := by
    rw [← neg_sub x xstar, inner_neg_right]
  rw [hn, he] at hs
  have hmul := mul_le_mul_of_nonneg_left (show f x - f xstar ≤
      ‖gradient f x‖ * ‖x - xstar‖ - μ / 2 * ‖x - xstar‖ ^ 2 by linarith)
    hμ.le
  nlinarith [sq_nonneg (‖gradient f x‖ - μ * ‖x - xstar‖)]

end SpeedRestartProof


open Set NesterovODE.WellPosed
open scoped RealInnerProductSpace

namespace SpeedRestartProof

variable {n : ℕ} {f : E n → ℝ} {L : NNReal}

lemma segment_derivative (hf : IsFL f L) (x v : E n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (gradient f (x + t • v)) v) t := by
  convert ((hf.2.2.1.differentiable one_ne_zero).differentiableAt.hasGradientAt).hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const v).const_add x) using 1 <;>
    first | rfl | simp only [one_smul, InnerProductSpace.toDual_apply_apply, id_eq]

lemma smooth_descent (hf : IsFL f L) (x v : E n) :
    f (x + v) ≤ f x + inner ℝ (gradient f x) v + ((L : ℝ) / 2) * ‖v‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => f (x + t • v)
  let B : ℝ → ℝ := fun t => f x + t * inner ℝ (gradient f x) v +
    ((L : ℝ) / 2) * t ^ 2 * ‖v‖ ^ 2
  have hF : ∀ t, HasDerivAt F (inner ℝ (gradient f (x + t • v)) v) t :=
    segment_derivative hf x v
  have hB : ∀ t, HasDerivAt B (inner ℝ (gradient f x) v + (L : ℝ) * t * ‖v‖ ^ 2) t := by
    intro t
    convert (((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) v)).const_add (f x)).add
      ((((hasDerivAt_id t).pow 2).const_mul ((L : ℝ) / 2)).mul_const (‖v‖ ^ 2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      inner ℝ (gradient f (x + t • v)) v ≤ inner ℝ (gradient f x) v + (L : ℝ) * t * ‖v‖ ^ 2 := by
    intro t ht
    have h1 := real_inner_le_norm (gradient f (x + t • v) - gradient f x) v
    have h2 := hf.2.2.2.dist_le_mul (x + t • v) x
    change ‖gradient f (x + t • v) - gradient f x‖ ≤ (L : ℝ) * ‖(x + t • v) - x‖ at h2
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

lemma initial_gap_bound (hf : IsFL f L) (x xstar : E n)
    (hmin : ∀ y, f xstar ≤ f y) :
    f x - f xstar ≤ (L : ℝ) * ‖x - xstar‖ ^ 2 / 2 := by
  have hg := gradient_at_minimum hf.2.2.1 hmin
  have hs := smooth_descent hf xstar (x - xstar)
  have he : xstar + (x - xstar) = x := by abel
  rw [he, hg, inner_zero_left] at hs
  linarith

end SpeedRestartProof


open Set Filter MeasureTheory
open scoped Topology

namespace SpeedRestartProof

open NesterovODE.WellPosed

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n}

theorem solution_continuous_X (hX : IsSolution f 3 x X V) :
    ContinuousOn X (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases eq_or_lt_of_le ht with rfl | ht
  · exact hX.2.2.1.continuousWithinAt
  · exact (hX.2.2.2.2 t ht).1.continuousAt.continuousWithinAt

theorem solution_continuous_V (hX : IsSolution f 3 x X V) :
    ContinuousOn V (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  rcases eq_or_lt_of_le ht with rfl | ht
  · exact hX.2.2.2.1
  · exact (hX.2.2.2.2 t ht).2.continuousAt.continuousWithinAt

theorem position_integral (hX : IsSolution f 3 x X V) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in 0..t, V u) = X t - x := by
  have hc := (solution_continuous_X hX).mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0)
  have hv := (solution_continuous_V hX).mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0)
  have hi : IntervalIntegrable V volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht hv
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc
    (fun u hu => ((hX.2.2.2.2 u hu.1).1).hasDerivWithinAt) hi
  simpa only [hX.1] using he

end SpeedRestartProof


open Set MeasureTheory

namespace SpeedRestartProof

open NesterovODE.WellPosed

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

theorem weighted_velocity_derivative (hX : IsSolution f 3 x X V)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => u ^ 3 • V u) (-(t ^ 3) • gradient f (X t)) t := by
  have hd := ((hasDerivAt_id t).pow 3).smul ((hX.2.2.2.2 t ht).2)
  convert hd using 1 <;> try rfl
  change -(t ^ 3) • gradient f (X t) =
    t ^ 3 • (-(3 / t) • V t - gradient f (X t)) + (3 * t ^ 2 * 1) • V t
  rw [smul_sub, smul_smul]
  have he : t ^ 3 * (-(3 / t)) = -(3 * t ^ 2) := by
    field_simp
  rw [he]
  module

theorem weighted_velocity_integral (hf : IsFL f L)
    (hX : IsSolution f 3 x X V) {t : ℝ} (ht : 0 ≤ t) :
    (∫ u in 0..t, -(u ^ 3) • gradient f (X u)) = t ^ 3 • V t := by
  have hv := (solution_continuous_V hX).mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0)
  have hx := (solution_continuous_X hX).mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0)
  have hc : ContinuousOn (fun u => u ^ 3 • V u) (Icc 0 t) :=
    (continuous_id.pow 3).continuousOn.smul hv
  have hg : ContinuousOn (fun u => -(u ^ 3) • gradient f (X u)) (Icc 0 t) :=
    (continuous_id.pow 3).neg.continuousOn.smul (hf.2.2.2.continuous.comp_continuousOn hx)
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc
    (fun u hu => (weighted_velocity_derivative hX hu.1).hasDerivWithinAt)
    (ContinuousOn.intervalIntegrable_of_Icc ht hg)
  simpa only [zero_pow (by decide : 3 ≠ 0), zero_smul, sub_zero] using he

end SpeedRestartProof


open Set MeasureTheory

namespace SpeedRestartProof

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_integral_power_bound {g : ℝ → F} {t c : ℝ} (ht : 0 ≤ t)
    (k : ℕ) (hg : ∀ u ∈ Ioc 0 t, ‖g u‖ ≤ c * u ^ k) :
    ‖∫ u in 0..t, g u‖ ≤ c * t ^ (k + 1) / (k + 1) := by
  have hi : IntervalIntegrable (fun u : ℝ => c * u ^ k) volume 0 t :=
    (continuous_const.mul (continuous_id.pow k)).intervalIntegrable _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le ht
    (Filter.Eventually.of_forall hg) hi
  simpa only [intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero k),
    sub_zero, mul_div_assoc] using hb

end SpeedRestartProof


open Set MeasureTheory

namespace SpeedRestartProof

open NesterovODE.WellPosed

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

def velocityRatios (V : ℝ → E n) (t : ℝ) : Set ℝ :=
  (fun u => ‖V u‖ / u) '' Ioc 0 t

noncomputable def velocitySup (V : ℝ → E n) (t : ℝ) : ℝ := sSup (velocityRatios V t)

theorem velocityRatios_nonempty {t : ℝ} (ht : 0 < t) :
    (velocityRatios V t).Nonempty := ⟨_, t, ⟨ht, le_rfl⟩, rfl⟩

theorem velocityRatios_bddAbove (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t : ℝ} (_ht : 0 < t) : BddAbove (velocityRatios V t) := by
  have hx := (solution_continuous_X hX).mono (Icc_subset_Ici_self : Icc 0 t ⊆ Ici 0)
  have hg := (hf.2.2.2.continuous.comp_continuousOn hx).norm
  obtain ⟨G, hG⟩ := isCompact_Icc.bddAbove_image hg
  refine ⟨G / 4, ?_⟩
  rintro y ⟨u, hu, rfl⟩
  have hb := norm_integral_power_bound hu.1.le 3 (g := fun v => -(v ^ 3) • gradient f (X v))
    (c := G) (fun v hv => by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (pow_nonneg hv.1.le _)]
      calc
        v ^ 3 * ‖gradient f (X v)‖ ≤ v ^ 3 * G :=
          mul_le_mul_of_nonneg_left (hG ⟨v, ⟨hv.1.le, hv.2.trans hu.2⟩, rfl⟩)
            (pow_nonneg hv.1.le _)
        _ = G * v ^ 3 := mul_comm _ _)
  rw [weighted_velocity_integral hf hX hu.1.le, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos hu.1 _)] at hb
  have hpos : 0 < u ^ 3 := pow_pos hu.1 _
  apply (div_le_iff₀ hu.1).2
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith [show u ^ 4 = u ^ 3 * u by ring]

theorem velocity_ratio_le_sup (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t u : ℝ} (hu : 0 < u) (hut : u ≤ t) : ‖V u‖ / u ≤ velocitySup V t := by
  exact le_csSup (velocityRatios_bddAbove hf hX (hu.trans_le hut)) ⟨u, ⟨hu, hut⟩, rfl⟩

theorem velocitySup_nonneg (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t : ℝ} (ht : 0 < t) : 0 ≤ velocitySup V t :=
  (div_nonneg (norm_nonneg _) ht.le).trans (velocity_ratio_le_sup hf hX ht le_rfl)

end SpeedRestartProof


open Set MeasureTheory

namespace SpeedRestartProof

open NesterovODE.WellPosed

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

theorem displacement_bound (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (_ht : 0 < t) :
    ‖X u - x‖ ≤ velocitySup V t * u ^ 2 / 2 := by
  have hb := norm_integral_power_bound hu 1 (g := V) (c := velocitySup V t)
    (fun v hv => by
      have hvb := (div_le_iff₀ hv.1).1
        (velocity_ratio_le_sup hf hX hv.1 (hv.2.trans hut))
      simpa only [pow_one] using hvb)
  simpa only [position_integral hX hu, Nat.reduceAdd, Nat.cast_one, one_add_one_eq_two] using hb

theorem gradient_displacement_bound (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (ht : 0 < t) :
    ‖gradient f (X u) - gradient f x‖ ≤ (L : ℝ) * velocitySup V t * u ^ 2 / 2 := by
  have hg : ‖gradient f (X u) - gradient f x‖ ≤ (L : ℝ) * ‖X u - x‖ := by
    simpa only [dist_eq_norm] using hf.2.2.2.dist_le_mul (X u) x
  calc
    _ ≤ (L : ℝ) * ‖X u - x‖ := hg
    _ ≤ (L : ℝ) * (velocitySup V t * u ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (displacement_bound hf hX hu hut ht) L.coe_nonneg
    _ = _ := by ring

end SpeedRestartProof


open Set MeasureTheory

namespace SpeedRestartProof

open NesterovODE.WellPosed

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

theorem velocity_defect_identity (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {u : ℝ} (hu : 0 ≤ u) :
    (∫ v in 0..u, -(v ^ 3) • (gradient f (X v) - gradient f x)) =
      u ^ 3 • (V u + (u / 4) • gradient f x) := by
  have hx := (solution_continuous_X hX).mono (Icc_subset_Ici_self : Icc 0 u ⊆ Ici 0)
  have hi : IntervalIntegrable (fun v => -(v ^ 3) • gradient f (X v)) volume 0 u :=
    ContinuousOn.intervalIntegrable_of_Icc hu
      ((continuous_id.pow 3).neg.continuousOn.smul (hf.2.2.2.continuous.comp_continuousOn hx))
  have hj : IntervalIntegrable (fun v : ℝ => v ^ 3 • gradient f x) volume 0 u :=
    ((continuous_id.pow 3).smul continuous_const).intervalIntegrable _ _
  have he : (fun v : ℝ => -(v ^ 3) • (gradient f (X v) - gradient f x)) =
      (fun v => -(v ^ 3) • gradient f (X v) + v ^ 3 • gradient f x) := by
    funext v
    module
  rw [he, intervalIntegral.integral_add hi hj, weighted_velocity_integral hf hX hu,
    intervalIntegral.integral_smul_const, integral_pow]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, zero_pow (by decide : 4 ≠ 0), sub_zero,
    smul_add, smul_smul]
  congr 1
  congr 1
  ring

theorem velocity_defect_bound (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t u : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    ‖V u + (u / 4) • gradient f x‖ ≤ (L : ℝ) * velocitySup V t * u ^ 3 / 12 := by
  have ht := hu.trans_le hut
  have hb := norm_integral_power_bound hu.le 5
    (g := fun v => -(v ^ 3) • (gradient f (X v) - gradient f x))
    (c := (L : ℝ) * velocitySup V t / 2) (fun v hv => by
      rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (pow_nonneg hv.1.le _)]
      calc
        _ ≤ v ^ 3 * ((L : ℝ) * velocitySup V t * v ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left
            (gradient_displacement_bound hf hX hv.1.le (hv.2.trans hut) ht)
            (pow_nonneg hv.1.le _)
        _ = _ := by ring)
  rw [velocity_defect_identity hf hX hu.le, norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos hu _)] at hb
  have hp : 0 < u ^ 3 := pow_pos hu _
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith [show u ^ 6 = u ^ 3 * u ^ 3 by ring]

end SpeedRestartProof


open Set

namespace SpeedRestartProof

open NesterovODE.WellPosed

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

theorem velocity_norm_from_defect (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t u : ℝ} (hu : 0 < u) (hut : u ≤ t) :
    ‖V u‖ ≤ u * ‖gradient f x‖ / 4 + (L : ℝ) * velocitySup V t * u ^ 3 / 12 := by
  have hb := velocity_defect_bound hf hX hu hut
  have he := norm_sub_le (V u + (u / 4) • gradient f x) ((u / 4) • gradient f x)
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos hu (by norm_num))] at he
  nlinarith

theorem velocitySup_small_bound (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t : ℝ} (ht : 0 < t) (hsmall : (L : ℝ) * t ^ 2 ≤ 1 / 4) :
    velocitySup V t ≤ 12 * ‖gradient f x‖ / 47 := by
  have hM := velocitySup_nonneg hf hX ht
  have hsup : velocitySup V t ≤ ‖gradient f x‖ / 4 + velocitySup V t / 48 := by
    apply csSup_le (velocityRatios_nonempty ht)
    rintro y ⟨u, hu, rfl⟩
    apply (div_le_iff₀ hu.1).2
    have hsq : u ^ 2 ≤ t ^ 2 := sq_le_sq₀ hu.1.le ht.le |>.2 hu.2
    have hlu : (L : ℝ) * u ^ 2 ≤ 1 / 4 :=
      (mul_le_mul_of_nonneg_left hsq L.coe_nonneg).trans hsmall
    have hm := mul_le_mul_of_nonneg_left hlu hM
    have hmu := mul_le_mul_of_nonneg_right hm hu.1.le
    have hb := velocity_norm_from_defect hf hX hu.1 hu.2
    nlinarith [show u ^ 3 = u ^ 2 * u by ring]
  linarith

end SpeedRestartProof


open scoped RealInnerProductSpace

namespace SpeedRestartProof

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem inner_positive_from_errors {g v a : F} {t : ℝ} (ht : 0 < t) (hg : g ≠ 0)
    (hv : ‖v + (t / 4) • g‖ ≤ t * ‖g‖ / 16)
    (ha : ‖a + (1 / 4 : ℝ) • g‖ ≤ ‖g‖ / 8) : 0 < inner ℝ v a := by
  let R := v + (t / 4) • g
  let Q := a + (1 / 4 : ℝ) • g
  have hR : ‖R‖ ≤ t * ‖g‖ / 16 := hv
  have hQ : ‖Q‖ ≤ ‖g‖ / 8 := ha
  have h1 := abs_real_inner_le_norm R g
  have h2 := abs_real_inner_le_norm g Q
  have h3 := abs_real_inner_le_norm R Q
  have hRg := mul_le_mul_of_nonneg_right hR (norm_nonneg g)
  have hgQ := mul_le_mul_of_nonneg_left hQ (norm_nonneg g)
  have hRQ := mul_le_mul hR hQ (norm_nonneg Q) (by positivity : 0 ≤ t * ‖g‖ / 16)
  have hv' : v = R - (t / 4) • g := by dsimp [R]; module
  have ha' : a = Q - (1 / 4 : ℝ) • g := by dsimp [Q]; module
  rw [hv', ha']
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hp : 0 < t * ‖g‖ ^ 2 := mul_pos ht (sq_pos_of_pos (norm_pos_iff.mpr hg))
  have hl1 := (abs_le.mp h1).2
  have hl2 := (abs_le.mp h2).2
  have hl3 := (abs_le.mp h3).1
  have ht2 := mul_le_mul_of_nonneg_left (hl2.trans hgQ) ht.le
  nlinarith

theorem speed_lower_from_error {g v : F} {t : ℝ} (ht : 0 ≤ t)
    (hv : ‖v + (t / 4) • g‖ ≤ t * ‖g‖ / 16) :
    3 * t * ‖g‖ / 16 ≤ ‖v‖ := by
  have he := norm_sub_le (v + (t / 4) • g) v
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg ht (by norm_num))] at he
  linarith

end SpeedRestartProof


open Set
open scoped RealInnerProductSpace

namespace SpeedRestartProof

open NesterovODE.WellPosed NesterovODE.Restart

noncomputable def shortTime (L : NNReal) : ℝ := 1 / (2 * Real.sqrt (L : ℝ))

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

theorem shortTime_pos (hL : 0 < L) : 0 < shortTime L := by
  unfold shortTime
  positivity

theorem shortTime_sq (hL : 0 < L) : shortTime L ^ 2 = 1 / (4 * (L : ℝ)) := by
  have hl : 0 < (L : ℝ) := hL
  have hs := Real.sq_sqrt L.coe_nonneg
  have hp := Real.sqrt_pos.2 hl
  unfold shortTime
  field_simp
  nlinarith

theorem shortTime_small (hL : 0 < L) {t : ℝ} (ht : 0 ≤ t) (hta : t ≤ shortTime L) :
    (L : ℝ) * t ^ 2 ≤ 1 / 4 := by
  have hs := (sq_le_sq₀ ht (shortTime_pos hL).le).mpr hta
  rw [shortTime_sq hL] at hs
  have hm := mul_le_mul_of_nonneg_left hs L.coe_nonneg
  have he : (L : ℝ) * (1 / (4 * (L : ℝ))) = 1 / 4 := by
    have hl : 0 < (L : ℝ) := hL
    field_simp
  exact hm.trans_eq he

theorem small_time_errors (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t : ℝ} (ht : 0 < t) (hta : t ≤ shortTime L) :
    ‖V t + (t / 4) • gradient f x‖ ≤ t * ‖gradient f x‖ / 64 ∧
    ‖(-(3 / t) • V t - gradient f (X t)) + (1 / 4 : ℝ) • gradient f x‖
      ≤ ‖gradient f x‖ / 8 := by
  have hs := shortTime_small hf.1 ht.le hta
  have hm := velocitySup_small_bound hf hX ht hs
  have hm0 := velocitySup_nonneg hf hX ht
  have hprod := mul_le_mul_of_nonneg_left hs hm0
  have hprod' : (L : ℝ) * velocitySup V t * t ^ 2 ≤ 3 * ‖gradient f x‖ / 47 := by
    nlinarith
  have hr := velocity_defect_bound hf hX ht le_rfl
  have hrt := mul_le_mul_of_nonneg_right hprod' ht.le
  have hr' : ‖V t + (t / 4) • gradient f x‖ ≤ t * ‖gradient f x‖ / 64 := by
    nlinarith [show t ^ 3 = t ^ 2 * t by ring, mul_nonneg ht.le (norm_nonneg (gradient f x))]
  have hg := gradient_displacement_bound hf hX ht.le le_rfl ht
  have hg' : ‖gradient f (X t) - gradient f x‖ ≤ ‖gradient f x‖ / 16 := by
    nlinarith [norm_nonneg (gradient f x)]
  refine ⟨hr', ?_⟩
  have hid : (-(3 / t) • V t - gradient f (X t)) + (1 / 4 : ℝ) • gradient f x =
      -(3 / t) • (V t + (t / 4) • gradient f x) - (gradient f (X t) - gradient f x) := by
    have hh : -(3 / t) * (t / 4) = -(3 / 4 : ℝ) := by field_simp
    rw [smul_add, smul_smul, hh]
    module
  rw [hid]
  have hn := norm_sub_le (-(3 / t) • (V t + (t / 4) • gradient f x))
    (gradient f (X t) - gradient f x)
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos (by norm_num) ht)] at hn
  have hb := mul_le_mul_of_nonneg_left hr' (show 0 ≤ (3 : ℝ) / t from div_nonneg (by norm_num) ht.le)
  have he : (3 / t) * (t * ‖gradient f x‖ / 64) = 3 * ‖gradient f x‖ / 64 := by
    field_simp
  nlinarith [norm_nonneg (gradient f x)]

theorem small_time_bounds (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    (hg : gradient f x ≠ 0) :
    shortTime L ∈ restartSet f X V ∧
      ∀ t : ℝ, 0 < t → t ≤ shortTime L → 3 * t * ‖gradient f x‖ / 16 ≤ ‖V t‖ := by
  have herr (t : ℝ) (ht : 0 < t) (hta : t ≤ shortTime L) :
      ‖V t + (t / 4) • gradient f x‖ ≤ t * ‖gradient f x‖ / 16 := by
    have hh := (small_time_errors hf hX ht hta).1
    nlinarith [mul_nonneg ht.le (norm_nonneg (gradient f x))]
  refine ⟨⟨shortTime_pos hf.1, ?_⟩, ?_⟩
  · intro t ht
    exact inner_positive_from_errors ht.1 hg (herr t ht.1 ht.2.le)
      (small_time_errors hf hX ht.1 ht.2.le).2
  · intro t ht hta
    exact speed_lower_from_error ht.le (herr t ht hta)

end SpeedRestartProof


open Set NesterovODE.WellPosed NesterovODE.Restart
open scoped RealInnerProductSpace

namespace SpeedRestartProof

variable {n : ℕ} {f : E n → ℝ} {x : E n} {X V : ℝ → E n} {L : NNReal}

lemma objective_derivative (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => f (X u)) (inner ℝ (gradient f (X t)) (V t)) t := by
  convert ((hf.2.2.1.differentiable one_ne_zero).differentiableAt.hasGradientAt).hasFDerivAt.comp_hasDerivAt t
    (hX.2.2.2.2 t ht).1 using 1 <;> rfl

lemma speed_derivative (hX : IsSolution f 3 x X V) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u => ‖V u‖ ^ 2) (2 * halfSpeedDeriv f X V t) t :=
  (hX.2.2.2.2 t ht).2.norm_sq

lemma objective_speed_identity (t : ℝ) :
    inner ℝ (gradient f (X t)) (V t) =
      -(3 / t) * ‖V t‖ ^ 2 - halfSpeedDeriv f X V t := by
  simp only [halfSpeedDeriv, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq, real_inner_comm (V t) (gradient f (X t))]
  ring

lemma objective_continuous (hf : IsFL f L) (hX : IsSolution f 3 x X V) :
    ContinuousOn (fun u => f (X u)) (Ici 0) :=
  hf.2.2.1.continuous.comp_continuousOn (solution_continuous_X hX)

lemma objective_antitone (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {T : ℝ} (hh : ∀ u ∈ Ioo 0 T, 0 ≤ halfSpeedDeriv f X V u) :
    AntitoneOn (fun u => f (X u)) (Icc 0 T) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    ((objective_continuous hf hX).mono Icc_subset_Ici_self)
    (f' := fun u => inner ℝ (gradient f (X u)) (V u))
  · intro u hu
    rw [interior_Icc] at hu
    exact (objective_derivative hf hX hu.1).hasDerivWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    rw [objective_speed_identity]
    have hp : 0 ≤ (3 / u) * ‖V u‖ ^ 2 := mul_nonneg (div_nonneg (by norm_num) hu.1.le) (sq_nonneg _)
    have := hh u hu
    linarith

lemma speed_monotone (hX : IsSolution f 3 x X V)
    {T : ℝ} (hh : ∀ u ∈ Ioo 0 T, 0 ≤ halfSpeedDeriv f X V u) :
    MonotoneOn (fun u => ‖V u‖ ^ 2) (Icc 0 T) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    ((solution_continuous_V hX).norm.pow 2 |>.mono Icc_subset_Ici_self)
    (f' := fun u => 2 * halfSpeedDeriv f X V u)
  · intro u hu
    rw [interior_Icc] at hu
    exact (speed_derivative hX hu.1).hasDerivWithinAt
  · intro u hu
    rw [interior_Icc] at hu
    exact mul_nonneg (by norm_num) (hh u hu)

lemma quadratic_objective_drop (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hh : ∀ u ∈ Ioo 0 a, 0 ≤ halfSpeedDeriv f X V u)
    (hv : ∀ u, 0 < u → u ≤ a → K * u ≤ ‖V u‖) :
    3 * K ^ 2 * a ^ 2 / 2 ≤ f x - f (X a) := by
  let F : ℝ → ℝ := fun u => f (X u) + (3 * K ^ 2 / 2) * u ^ 2
  have hc : ContinuousOn F (Icc 0 a) :=
    ((objective_continuous hf hX).mono Icc_subset_Ici_self).add
      ((continuous_const.mul (continuous_id.pow 2)).continuousOn)
  have hd : ∀ u ∈ Ioo 0 a, HasDerivAt F
      (inner ℝ (gradient f (X u)) (V u) + 3 * K ^ 2 * u) u := by
    intro u hu
    convert (objective_derivative hf hX hu.1).add
      (((hasDerivAt_id u).pow 2).const_mul (3 * K ^ 2 / 2)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring)
  have hm : AntitoneOn F (Icc 0 a) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 a) hc
      (f' := fun u => inner ℝ (gradient f (X u)) (V u) + 3 * K ^ 2 * u)
    · intro u hu
      exact (hd u (by simpa only [interior_Icc] using hu)).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hsq : (K * u) ^ 2 ≤ ‖V u‖ ^ 2 :=
        sq_le_sq₀ (mul_nonneg hK hu.1.le) (norm_nonneg _) |>.mpr (hv u hu.1 hu.2.le)
      have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3 / u from div_nonneg (by norm_num) hu.1.le)
      have he : (3 / u) * (K * u) ^ 2 = 3 * K ^ 2 * u := by field_simp
      rw [he] at hmul
      rw [objective_speed_identity]
      have := hh u hu
      nlinarith
  have he := hm (show (0 : ℝ) ∈ Icc 0 a by exact ⟨le_rfl, ha⟩)
    (show a ∈ Icc 0 a by exact ⟨ha, le_rfl⟩) ha
  simp only [F, hX.1, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at he
  linarith

end SpeedRestartProof


open Set NesterovODE.WellPosed NesterovODE.Restart
open scoped RealInnerProductSpace

namespace SpeedRestartProof

variable {n : ℕ} {f : E n → ℝ} {x xstar : E n} {X V : ℝ → E n} {L : NNReal}

lemma logarithmic_objective_drop (hf : IsFL f L) (hX : IsSolution f 3 x X V)
    (hmin : ∀ y, f xstar ≤ f y) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b ∈ restartSet f X V) :
    3 * ‖V a‖ ^ 2 * Real.log (b / a) ≤ f x - f xstar := by
  have hh : ∀ u ∈ Ioo 0 b, 0 ≤ halfSpeedDeriv f X V u := fun u hu => (hb.2 u hu).le
  have hmono := speed_monotone hX hh
  let F : ℝ → ℝ := fun u => f (X u) + 3 * ‖V a‖ ^ 2 * Real.log u
  have hc : ContinuousOn F (Icc a b) := by
    apply ((objective_continuous hf hX).mono (fun t ht => ha.le.trans ht.1)).add
    apply continuousOn_const.mul
    intro t ht
    exact (Real.continuousAt_log (ne_of_gt (ha.trans_le ht.1))).continuousWithinAt
  have hd : ∀ u ∈ Ioo a b, HasDerivAt F
      (inner ℝ (gradient f (X u)) (V u) + 3 * ‖V a‖ ^ 2 / u) u := by
    intro u hu
    convert (objective_derivative hf hX (ha.trans hu.1)).add
      ((Real.hasDerivAt_log (ne_of_gt (ha.trans hu.1))).const_mul (3 * ‖V a‖ ^ 2))
      using 1 <;> rfl
  have hm : AntitoneOn F (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hc
      (f' := fun u => inner ℝ (gradient f (X u)) (V u) + 3 * ‖V a‖ ^ 2 / u)
    · intro u hu
      exact (hd u (by simpa only [interior_Icc] using hu)).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu0 := ha.trans hu.1
      have hs := hmono (show a ∈ Icc 0 b from ⟨ha.le, hab⟩)
        (show u ∈ Icc 0 b from ⟨hu0.le, hu.2.le⟩) hu.1.le
      have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 3 / u by positivity)
      have he : (3 / u) * ‖V a‖ ^ 2 = 3 * ‖V a‖ ^ 2 / u := by ring
      rw [he] at hmul
      rw [objective_speed_identity]
      have hp := hh u ⟨hu0, hu.2⟩
      linarith
  have he := hm (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hab
  have hdec := objective_antitone hf hX hh
    (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb.1.le⟩)
    (show a ∈ Icc 0 b from ⟨ha.le, hab⟩) ha.le
  change f (X a) ≤ f (X 0) at hdec
  rw [hX.1] at hdec
  have hlow := hmin (X b)
  rw [Real.log_div (ne_of_gt hb.1) (ne_of_gt ha)]
  dsimp [F] at he
  nlinarith

end SpeedRestartProof


open Set NesterovODE.WellPosed NesterovODE.Restart NesterovODE.StrongCvx

namespace SpeedRestartProof

noncomputable def longTime (μ : ℝ) (L : NNReal) : ℝ :=
  shortTime L * Real.exp (20 * (L : ℝ) / μ)

variable {n : ℕ} {f : E n → ℝ} {x xstar : E n} {X V : ℝ → E n}
    {μ : ℝ} {L : NNReal}

lemma restartSet_upper (hf : InSMuL μ L f) (hμ : 0 < μ)
    (hX : NesterovODE.WellPosed.IsSolution f 3 x X V)
    (hmin : ∀ y, f xstar ≤ f y) (hg : gradient f x ≠ 0) :
    ∀ b ∈ restartSet f X V, b ≤ longTime μ L := by
  have hL : 0 < (L : ℝ) := hf.1.1
  have ha := shortTime_pos hf.1.1
  have ha2 := shortTime_sq hf.1.1
  obtain ⟨_, hspeed⟩ := small_time_bounds hf.1 hX hg
  have hG : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
  have hG2 : 0 < ‖gradient f x‖ ^ 2 := sq_pos_of_pos hG
  intro b hb
  by_cases hba : b < shortTime L
  · apply hba.le.trans
    dsimp [longTime]
    have he : 1 ≤ Real.exp (20 * (L : ℝ) / μ) := Real.one_le_exp_iff.mpr (by positivity)
    simpa using mul_le_mul_of_nonneg_left he ha.le
  · have hab := le_of_not_gt hba
    have hs := hspeed (shortTime L) ha le_rfl
    have hs2 : (3 * shortTime L * ‖gradient f x‖ / 16) ^ 2 ≤ ‖V (shortTime L)‖ ^ 2 :=
      (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hs
    have hcoef : 27 * ‖gradient f x‖ ^ 2 / (1024 * (L : ℝ)) ≤
        3 * ‖V (shortTime L)‖ ^ 2 := by
      have he : (3 * shortTime L * ‖gradient f x‖ / 16) ^ 2 =
          9 * ‖gradient f x‖ ^ 2 / (1024 * (L : ℝ)) := by
        rw [div_pow, mul_pow, mul_pow, ha2]
        ring
      rw [he] at hs2
      convert mul_le_mul_of_nonneg_left hs2 (show (0 : ℝ) ≤ 3 by norm_num) using 1 <;> first | rfl | ring
    have hlog0 : 0 ≤ Real.log (b / shortTime L) :=
      Real.log_nonneg ((one_le_div ha).mpr hab)
    have hlog := logarithmic_objective_drop hf.1 hX hmin ha hab hb
    have hmul := mul_le_mul_of_nonneg_right hcoef hlog0
    have hpl := pl_bound hf hμ x xstar hmin
    have hgap : f x - f xstar ≤ ‖gradient f x‖ ^ 2 / (2 * μ) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * μ)).mpr
      nlinarith
    have hc : 0 < 27 * ‖gradient f x‖ ^ 2 / (1024 * (L : ℝ)) := by positivity
    have hr : Real.log (b / shortTime L) ≤
        (‖gradient f x‖ ^ 2 / (2 * μ)) /
          (27 * ‖gradient f x‖ ^ 2 / (1024 * (L : ℝ))) := by
      apply (le_div_iff₀ hc).mpr
      nlinarith [hlog.trans hgap]
    have he : (‖gradient f x‖ ^ 2 / (2 * μ)) /
          (27 * ‖gradient f x‖ ^ 2 / (1024 * (L : ℝ))) =
        512 * (L : ℝ) / (27 * μ) := by
      field_simp
      ring
    rw [he] at hr
    have hr' : Real.log (b / shortTime L) ≤ 20 * (L : ℝ) / μ := by
      apply hr.trans
      apply (div_le_div_iff₀ (by positivity : 0 < 27 * μ) hμ).mpr
      nlinarith
    have hh := Real.exp_le_exp.mpr hr'
    rw [Real.exp_log (div_pos hb.1 ha)] at hh
    exact (div_le_iff₀ ha).mp hh |>.trans_eq (by dsimp [longTime]; ring)

lemma restartTime_bounds (hf : InSMuL μ L f) (hμ : 0 < μ)
    (hX : NesterovODE.WellPosed.IsSolution f 3 x X V)
    (hmin : ∀ y, f xstar ≤ f y) (hg : gradient f x ≠ 0) :
    shortTime L ≤ restartTime f X V ∧ restartTime f X V ≤ longTime μ L := by
  have ha := (small_time_bounds hf.1 hX hg).1
  have hb := restartSet_upper hf hμ hX hmin hg
  exact ⟨le_csSup ⟨longTime μ L, hb⟩ ha, csSup_le ⟨shortTime L, ha⟩ hb⟩

lemma halfSpeed_positive_before (hf : InSMuL μ L f) (_hμ : 0 < μ)
    (hX : NesterovODE.WellPosed.IsSolution f 3 x X V)
    (_hmin : ∀ y, f xstar ≤ f y) (hg : gradient f x ≠ 0)
    {u : ℝ} (hu : u ∈ Ioo 0 (restartTime f X V)) :
    0 < halfSpeedDeriv f X V u := by
  have ha := (small_time_bounds hf.1 hX hg).1
  obtain ⟨b, hbmem, hub⟩ := exists_lt_of_lt_csSup (show (restartSet f X V).Nonempty from
    ⟨shortTime L, ha⟩) hu.2
  exact hbmem.2 u ⟨hu.1, hub⟩

end SpeedRestartProof


open Set NesterovODE.WellPosed NesterovODE.Restart NesterovODE.StrongCvx

namespace SpeedRestartProof

variable {n : ℕ} {f : E n → ℝ} {x xstar : E n} {X V : ℝ → E n}
    {μ : ℝ} {L : NNReal}

lemma restart_partial_gap (hf : InSMuL μ L f) (hμ : 0 < μ)
    (hX : NesterovODE.WellPosed.IsSolution f 3 x X V)
    (hmin : ∀ y, f xstar ≤ f y) (hg : gradient f x ≠ 0)
    {u : ℝ} (hu : u ∈ Icc 0 (restartTime f X V)) :
    f (X u) ≤ f x := by
  have hh : ∀ t ∈ Ioo 0 (restartTime f X V), 0 ≤ halfSpeedDeriv f X V t :=
    fun t ht => (halfSpeed_positive_before hf hμ hX hmin hg ht).le
  have ht := (shortTime_pos hf.1.1).le.trans (restartTime_bounds hf hμ hX hmin hg).1
  simpa only [hX.1] using objective_antitone hf.1 hX hh ⟨le_rfl, ht⟩ hu hu.1

lemma restart_gap_contraction (hf : InSMuL μ L f) (hμ : 0 < μ)
    (hX : NesterovODE.WellPosed.IsSolution f 3 x X V)
    (hmin : ∀ y, f xstar ≤ f y) (hg : gradient f x ≠ 0) :
    f (X (restartTime f X V)) - f xstar ≤
      (1 - μ / (64 * (L : ℝ))) * (f x - f xstar) := by
  have hL : 0 < (L : ℝ) := hf.1.1
  have ha := shortTime_pos hf.1.1
  have ha2 := shortTime_sq hf.1.1
  obtain ⟨hamem, hspeed⟩ := small_time_bounds hf.1 hX hg
  have hquad := quadratic_objective_drop hf.1 hX ha.le
    (show 0 ≤ 3 * ‖gradient f x‖ / 16 by positivity)
    (fun t ht => (hamem.2 t ht).le)
    (fun t ht hta => by
      convert hspeed t ht hta using 1
      ring)
  have he : 3 * (3 * ‖gradient f x‖ / 16) ^ 2 * shortTime L ^ 2 / 2 =
      27 * ‖gradient f x‖ ^ 2 / (2048 * (L : ℝ)) := by
    rw [ha2]
    ring
  rw [he] at hquad
  have hq := (div_le_iff₀ (show 0 < 2048 * (L : ℝ) by positivity)).mp hquad
  have hp := pl_bound hf hμ x xstar hmin
  have ht := restartTime_bounds hf hμ hX hmin hg
  have hh : ∀ t ∈ Ioo 0 (restartTime f X V), 0 ≤ halfSpeedDeriv f X V t :=
    fun t h => (halfSpeed_positive_before hf hμ hX hmin hg h).le
  have hd := objective_antitone hf.1 hX hh
    (show shortTime L ∈ Icc 0 (restartTime f X V) from ⟨ha.le, ht.1⟩)
    (show restartTime f X V ∈ Icc 0 (restartTime f X V) from
      ⟨ha.le.trans ht.1, le_rfl⟩) ht.1
  have hgap : 0 ≤ f x - f xstar := sub_nonneg.mpr (hmin x)
  apply (mul_le_mul_iff_right₀ (show 0 < 64 * (L : ℝ) by positivity)).mp
  have he' : (64 * (L : ℝ)) * ((1 - μ / (64 * (L : ℝ))) * (f x - f xstar)) =
      (64 * (L : ℝ) - μ) * (f x - f xstar) := by
    field_simp
  rw [he']
  nlinarith [mul_nonneg hμ.le hgap]

end SpeedRestartProof


open Set

namespace SpeedRestartProof

lemma restarted_rate (τ : ℕ → ℝ) (d : ℝ → ℝ) (Q : ℕ → Prop)
    (a B δ : ℝ) (ha : 0 < a) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hτ0 : τ 0 = 0) (hd0 : 0 ≤ d 0)
    (hstop : ∀ i, Q i → τ (i + 1) = τ i ∧ ∀ t, τ i ≤ t → d t = 0)
    (hstep : ∀ i, ¬ Q i →
      a ≤ τ (i + 1) - τ i ∧ τ (i + 1) - τ i ≤ B ∧
      d (τ (i + 1)) ≤ (1 - δ) * d (τ i) ∧
      ∀ t ∈ Icc (τ i) (τ (i + 1)), d t ≤ d (τ i))
    {t : ℝ} (ht : 0 ≤ t) :
    d t ≤ Real.exp δ * Real.exp (-δ * t / B) * d 0 := by
  classical
  have hq : 0 ≤ 1 - δ := sub_nonneg.mpr hδ1
  have hupper : ∀ i, τ i ≤ (i : ℝ) * B := by
    intro i
    induction i with
    | zero => simp [hτ0]
    | succ i hi =>
      by_cases hiq : Q i
      · rw [(hstop i hiq).1]
        push_cast
        nlinarith
      · have hh := (hstep i hiq).2.1
        push_cast
        nlinarith
  have hgap : ∀ i, d (τ i) ≤ (1 - δ) ^ i * d 0 := by
    intro i
    induction i with
    | zero => simp [hτ0]
    | succ i hi =>
      by_cases hiq : Q i
      · rw [(hstop i hiq).1, (hstop i hiq).2 (τ i) le_rfl]
        exact mul_nonneg (pow_nonneg hq _) hd0
      · have hh := (hstep i hiq).2.2.1
        have hm := mul_le_mul_of_nonneg_left hi hq
        rw [pow_succ]
        nlinarith
  by_cases hst : ∃ i, Q i ∧ τ i ≤ t
  · obtain ⟨i, hi, hit⟩ := hst
    rw [(hstop i hi).2 t hit]
    positivity
  · have hex : ∃ i, t < τ i := by
      by_contra hn
      have hall : ∀ i, τ i ≤ t := by simpa only [not_exists, not_lt] using hn
      have hnot : ∀ i, ¬ Q i := by
        intro i hi
        exact hst ⟨i, hi, hall i⟩
      have hlower : ∀ i : ℕ, (i : ℝ) * a ≤ τ i := by
        intro i
        induction i with
        | zero => simp [hτ0]
        | succ i hi =>
          have hh := (hstep i (hnot i)).1
          push_cast
          nlinarith
      obtain ⟨i, hi⟩ := exists_nat_gt (t / a)
      have hh := (div_lt_iff₀ ha).mp hi
      exact (not_lt_of_ge ((hlower i).trans (hall i))) hh
    let j := Nat.find hex
    have hj : t < τ j := Nat.find_spec hex
    have hj0 : 0 < j := by
      by_contra hn
      have he : j = 0 := Nat.eq_zero_of_not_pos hn
      rw [he, hτ0] at hj
      exact (not_lt_of_ge ht) hj
    let k := j - 1
    have hkj : k + 1 = j := by dsimp [k]; omega
    have hklt : k < j := by omega
    have hkt : τ k ≤ t := le_of_not_gt (Nat.find_min hex hklt)
    have hkq : ¬ Q k := fun h => hst ⟨k, h, hkt⟩
    have htk : t ≤ τ (k + 1) := by simpa only [hkj] using hj.le
    have hd := (hstep k hkq).2.2.2 t ⟨hkt, htk⟩
    have hratio : t / B - 1 ≤ (k : ℝ) := by
      have hh := (div_le_iff₀ hB).mpr (htk.trans (hupper (k + 1)))
      push_cast at hh
      linarith
    have hqe : 1 - δ ≤ Real.exp (-δ) := by
      have hh := Real.add_one_le_exp (-δ)
      linarith
    have hp := pow_le_pow_left₀ hq hqe k
    rw [← Real.exp_nat_mul] at hp
    have he : (k : ℝ) * (-δ) ≤ δ + (-δ * t / B) := by
      have hm := mul_le_mul_of_nonneg_left hratio hδ.le
      have heq : δ * (t / B - 1) = δ * t / B - δ := by ring
      rw [heq] at hm
      have heq2 : -δ * t / B = -(δ * t / B) := by ring
      rw [heq2]
      linarith
    have he' := Real.exp_le_exp.mpr he
    rw [Real.exp_add] at he'
    exact hd.trans ((hgap k).trans (mul_le_mul_of_nonneg_right (hp.trans he') hd0))

end SpeedRestartProof


open Set NesterovODE.WellPosed NesterovODE.StrongCvx NesterovODE.Restart

namespace SpeedRestartProof

lemma global_gap_rate {n : ℕ} {f : E n → ℝ} {μ : ℝ} {L : NNReal}
    (hf : InSMuL μ L f) (hμ : 0 < μ) (hμL : μ ≤ (L : ℝ))
    {x₀ xstar : E n} (hmin : ∀ y, f xstar ≤ f y)
    {Xsr : ℝ → E n} (hR : IsSpeedRestarted f x₀ Xsr)
    {t : ℝ} (ht : 0 ≤ t) :
    f (Xsr t) - f xstar ≤ Real.exp (μ / (64 * (L : ℝ))) *
      Real.exp (-(μ / (64 * (L : ℝ))) * t / longTime μ L) *
      (f x₀ - f xstar) := by
  obtain ⟨hx0, τ, Y, W, hτ0, hrun⟩ := hR
  have hL : 0 < (L : ℝ) := hf.1.1
  have ha := shortTime_pos hf.1.1
  have hB : 0 < longTime μ L := mul_pos ha (Real.exp_pos _)
  have hδ : 0 < μ / (64 * (L : ℝ)) := by positivity
  have hδ1 : μ / (64 * (L : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hs := restarted_rate τ (fun t => f (Xsr t) - f xstar)
    (fun i => gradient f (Xsr (τ i)) = 0)
    (shortTime L) (longTime μ L) (μ / (64 * (L : ℝ))) ha hB hδ hδ1 hτ0
    (sub_nonneg.mpr (hmin (Xsr 0)))
    (fun i hi => by
      obtain ⟨he, hfreeze⟩ := (hrun i).2.2 hi
      refine ⟨he, ?_⟩
      intro u hu
      rw [hfreeze u hu]
      exact sub_eq_zero.mpr (le_antisymm
        (stationary_minimum hf.1 hi xstar) (hmin _)))
    (fun i hi => by
      have hX := (hrun i).1
      obtain ⟨he, hmatch⟩ := (hrun i).2.1 hi
      have hlength : τ (i + 1) - τ i = restartTime f (Y i) (W i) := by
        rw [he]; ring
      have hb := restartTime_bounds hf hμ hX hmin hi
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [hlength] using hb.1
      · simpa only [hlength] using hb.2
      · have hT0 : 0 ≤ restartTime f (Y i) (W i) := ha.le.trans hb.1
        have hm := hmatch (restartTime f (Y i) (W i)) (by
          rw [hlength]
          exact ⟨hT0, le_rfl⟩)
        rw [← he] at hm
        rw [hm]
        exact restart_gap_contraction hf hμ hX hmin hi
      · intro u hu
        have huu : u - τ i ∈ Icc 0 (restartTime f (Y i) (W i)) := by
          rw [← hlength]
          constructor <;> linarith [hu.1, hu.2]
        have hm := hmatch (u - τ i) (by simpa only [hlength] using huu)
        have heq : τ i + (u - τ i) = u := by ring
        rw [heq] at hm
        rw [hm]
        exact sub_le_sub_right (restart_partial_gap hf hμ hX hmin hi huu) _)
    ht
  simpa only [hx0] using hs

end SpeedRestartProof


open NesterovODE.WellPosed

namespace SpeedRestartProof

noncomputable def rateC₁ (κ : ℝ) : ℝ := Real.exp (1 / (64 * max 1 κ))
noncomputable def rateC₂ (κ : ℝ) : ℝ := Real.exp (-20 * max 1 κ) / (32 * max 1 κ)

lemma rate_constants_positive (κ : ℝ) : 0 < rateC₁ κ ∧ 0 < rateC₂ κ := by
  have hK : 0 < max 1 κ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  constructor
  · exact Real.exp_pos _
  · exact div_pos (Real.exp_pos _) (mul_pos (by norm_num) hK)

lemma rate_constants_physical {μ : ℝ} {L : NNReal} (hμ : 0 < μ) (hμL : μ ≤ (L : ℝ)) :
    rateC₁ ((L : ℝ) / μ) = Real.exp (μ / (64 * (L : ℝ))) ∧
      rateC₂ ((L : ℝ) / μ) * Real.sqrt (L : ℝ) =
        (μ / (64 * (L : ℝ))) / longTime μ L := by
  have hL : 0 < (L : ℝ) := hμ.trans_le hμL
  have hK : 1 ≤ (L : ℝ) / μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have hs : Real.sqrt (L : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  have he : Real.exp (20 * (L : ℝ) / μ) ≠ 0 := ne_of_gt (Real.exp_pos _)
  constructor
  · unfold rateC₁
    rw [max_eq_right hK]
    congr 1
    field_simp
  · unfold rateC₂ longTime shortTime
    rw [max_eq_right hK]
    have hex : -20 * ((L : ℝ) / μ) = -(20 * (L : ℝ) / μ) := by ring
    rw [hex, Real.exp_neg]
    field_simp
    ring

end SpeedRestartProof


namespace SpeedRestartProof

open NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Theorem 10 (p. 22): there are positive constants `c₁, c₂` depending only on the condition
number `L/μ` (functions of `L/μ`, chosen before the dimension, `f`, `μ`, `L`, `x₀`) such that
every speed restarted trajectory satisfies
`f(Xˢʳ(t)) − f⋆ ≤ (c₁L‖x₀ − x⋆‖²/2) e^{−c₂ t √L}` for all `t ≥ 0`. -/
theorem full_native_result :
    ∃ c₁ c₂ : ℝ → ℝ, (∀ κ : ℝ, 0 < c₁ κ ∧ 0 < c₂ κ) ∧
      ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal),
        0 < μ → μ ≤ L → NesterovODE.StrongCvx.InSMuL μ L f →
        ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) →
        ∀ Xsr : ℝ → NesterovODE.WellPosed.E n, IsSpeedRestarted f x₀ Xsr →
        ∀ t : ℝ, 0 ≤ t →
          f (Xsr t) - f xstar ≤
            c₁ (L / μ) * L * ‖x₀ - xstar‖ ^ 2 / 2 *
              Real.exp (-(c₂ (L / μ)) * t * Real.sqrt L) := by
  refine ⟨rateC₁, rateC₂, rate_constants_positive, ?_⟩
  intro n f μ L hμ hμL hf x₀ xstar hmin Xsr hR t ht
  have hg := global_gap_rate hf hμ hμL hmin hR ht
  have hi := initial_gap_bound hf.1 x₀ xstar hmin
  obtain ⟨hc₁, hc₂⟩ := rate_constants_physical hμ hμL
  rw [hc₁]
  have hex : -(rateC₂ ((L : ℝ) / μ)) * t * Real.sqrt (L : ℝ) =
      -(μ / (64 * (L : ℝ))) * t / longTime μ L := by
    calc
      _ = -(rateC₂ ((L : ℝ) / μ) * Real.sqrt (L : ℝ)) * t := by ring
      _ = _ := by rw [hc₂]; ring
  rw [hex]
  have hm := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ Real.exp (μ / (64 * (L : ℝ))) *
      Real.exp (-(μ / (64 * (L : ℝ))) * t / longTime μ L) by positivity)
  exact hg.trans (by convert hm using 1; ring)

end SpeedRestartProof


open NesterovODE.Restart

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Theorem 10 (p. 22): there are positive constants `c₁, c₂` depending only on the condition
number `L/μ` (functions of `L/μ`, chosen before the dimension, `f`, `μ`, `L`, `x₀`) such that
every speed restarted trajectory satisfies
`f(Xˢʳ(t)) − f⋆ ≤ (c₁L‖x₀ − x⋆‖²/2) e^{−c₂ t √L}` for all `t ≥ 0`. -/
theorem theorem_10 :
    ∃ c₁ c₂ : ℝ → ℝ, (∀ κ : ℝ, 0 < c₁ κ ∧ 0 < c₂ κ) ∧
      ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal),
        0 < μ → μ ≤ L → NesterovODE.StrongCvx.InSMuL μ L f →
        ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) →
        ∀ Xsr : ℝ → NesterovODE.WellPosed.E n, IsSpeedRestarted f x₀ Xsr →
        ∀ t : ℝ, 0 ≤ t →
          f (Xsr t) - f xstar ≤
            c₁ (L / μ) * L * ‖x₀ - xstar‖ ^ 2 / 2 *
              Real.exp (-(c₂ (L / μ)) * t * Real.sqrt L) := by
  exact SpeedRestartProof.full_native_result

end NesterovODE.Restart

open NesterovODE.Restart

theorem solution :
    ∃ c₁ c₂ : ℝ → ℝ, (∀ κ : ℝ, 0 < c₁ κ ∧ 0 < c₂ κ) ∧
      ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (μ : ℝ) (L : NNReal),
        0 < μ → μ ≤ L → NesterovODE.StrongCvx.InSMuL μ L f →
        ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) →
        ∀ Xsr : ℝ → NesterovODE.WellPosed.E n, IsSpeedRestarted f x₀ Xsr →
        ∀ t : ℝ, 0 ≤ t →
          f (Xsr t) - f xstar ≤
            c₁ (L / μ) * L * ‖x₀ - xstar‖ ^ 2 / 2 *
              Real.exp (-(c₂ (L / μ)) * t * Real.sqrt L) := NesterovODE.Restart.theorem_10 
