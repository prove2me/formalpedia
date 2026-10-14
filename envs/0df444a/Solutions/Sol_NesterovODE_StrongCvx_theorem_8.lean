-- Prove2me | solution 1 for NesterovODE.StrongCvx.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:21:57.739771+00:00
-- url     : https://prove2.me/submissions/2aa1011e-fe22-4b9f-b3c3-c42825ca7513

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting

namespace RRAux_NesterovODE_StrongCvx_theorem_8

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem grad_inner [CompleteSpace F] (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem conv_line (φ : F → ℝ) (hc : ConvexOn ℝ Set.univ φ) (x y : F) (d : ℝ)
    (hd : HasDerivAt (fun t : ℝ => φ (x + t • (y - x))) d 0) : φ x + d ≤ φ y := by
  have hg : ConvexOn ℝ Set.univ (φ ∘ AffineMap.lineMap (k := ℝ) x y) := by
    have := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
    simpa using this
  have e : (φ ∘ AffineMap.lineMap (k := ℝ) x y) = fun t : ℝ => φ (x + t • (y - x)) := by
    funext t; simp [AffineMap.lineMap_apply, add_comm]
  rw [e] at hg
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  have e1 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e1, zero_smul, add_zero, sub_zero, div_one] at this
  linarith

theorem sc_grad [CompleteSpace F] (f : F → ℝ) (μ : ℝ)
    (hc : ConvexOn ℝ Set.univ (fun x => f x - μ / 2 * ‖x‖ ^ 2))
    (hd : Differentiable ℝ f) (x y : F) :
    f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • (y - x)) := by
    simpa using (hd x).hasFDerivAt
  have h1 := hfx.comp_hasDerivAt (0:ℝ) hl
  rw [grad_inner f] at h1
  have h2 := (hl.norm_sq).const_mul (μ / 2)
  have h3 := h1.sub h2
  have := conv_line (fun x => f x - μ / 2 * ‖x‖ ^ 2) hc x y _ h3
  simp only [zero_smul, add_zero] at this
  have e : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y - x⟫_ℝ + ‖y - x‖ ^ 2 := by
    have : y = x + (y - x) := by abel
    conv_lhs => rw [this]
    rw [norm_add_sq_real]
  rw [e] at this
  linarith

theorem key5 (Y V g : F) (u r δ : ℝ) (hu : 0 < u) (hr : 3 ≤ r) (hδ : 0 ≤ δ)
    (hG : δ ≤ ⟪g, Y⟫_ℝ) :
    2 / (r - 1) * (2 * u) * δ + 2 / (r - 1) * u ^ 2 * ⟪g, V⟫_ℝ
      + (r - 1) * (2 * ⟪Y + (u / (r - 1)) • V,
          V + (1 / (r - 1)) • V + (u / (r - 1)) • (-(r / u) • V - g)⟫_ℝ) ≤ 0 := by
  have hr1 : 0 < r - 1 := by linarith
  have ev : V + (1 / (r - 1)) • V + (u / (r - 1)) • (-(r / u) • V - g) = -(u / (r - 1)) • g := by
    rw [smul_sub, smul_smul]
    have : u / (r - 1) * -(r / u) = -(1 + 1 / (r - 1)) := by
      field_simp; ring
    rw [this]; module
  rw [ev]
  simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  have e1 : (r - 1) * (2 * (-(u / (r - 1)) * (⟪Y, g⟫_ℝ + u / (r - 1) * ⟪V, g⟫_ℝ)))
      = -2 * u * ⟪Y, g⟫_ℝ - 2 / (r - 1) * u ^ 2 * ⟪V, g⟫_ℝ := by
    field_simp; ring
  rw [real_inner_comm g V] at *
  rw [e1]
  rw [real_inner_comm Y g] at hG
  have h2 : 2 / (r - 1) ≤ 1 := by rw [div_le_one hr1]; linarith
  have h3 : 2 / (r - 1) * (2 * u) * δ ≤ 2 * u * δ := by
    have := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ 2 * u * δ)
    nlinarith
  have h4 : 2 * u * δ ≤ 2 * u * ⟪Y, g⟫_ℝ := mul_le_mul_of_nonneg_left hG (by positivity)
  linarith

theorem phase1 [CompleteSpace F] (f : F → ℝ) (hconv : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y)
    (hd : Differentiable ℝ f) (xstar : F) (hmin : ∀ y, f xstar ≤ f y) (r : ℝ) (hr : 3 ≤ r)
    (x₀ : F) (X V : ℝ → F) (hX0 : X 0 = x₀) (hV0 : V 0 = 0)
    (hXd0 : HasDerivWithinAt X (V 0) (Set.Ici 0) 0) (hVc0 : ContinuousWithinAt V (Set.Ici 0) 0)
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt X (V t) t ∧
      HasDerivAt V (-(r / t) • V t - gradient f (X t)) t) :
    ∀ t, 0 < t → 2 / (r - 1) * t ^ 2 * (f (X t) - f xstar)
      + (r - 1) * ‖X t + (t / (r - 1)) • V t - xstar‖ ^ 2 ≤ (r - 1) * ‖x₀ - xstar‖ ^ 2 := by
  intro t ht
  set E : ℝ → ℝ := fun u => 2 / (r - 1) * u ^ 2 * (f (X u) - f xstar)
      + (r - 1) * ‖X u + (u / (r - 1)) • V u - xstar‖ ^ 2 with hE
  have hder : ∀ u, 0 < u → HasDerivAt E
      (2 / (r - 1) * (2 * u) * (f (X u) - f xstar) + 2 / (r - 1) * u ^ 2 * ⟪gradient f (X u), V u⟫_ℝ
        + (r - 1) * (2 * ⟪X u + (u / (r - 1)) • V u - xstar,
            V u + (1 / (r - 1)) • V u + (u / (r - 1)) • (-(r / u) • V u - gradient f (X u))⟫_ℝ)) u := by
    intro u hu
    obtain ⟨hXu, hVu⟩ := hode u hu
    have h1 : HasDerivAt (fun w => f (X w)) ⟪gradient f (X u), V u⟫_ℝ u := by
      have := (hd (X u)).hasFDerivAt.comp_hasDerivAt u hXu
      rw [grad_inner f] at this
      exact this
    have hp : HasDerivAt (fun w : ℝ => 2 / (r - 1) * w ^ 2) (2 / (r - 1) * (2 * u)) u := by
      have := (hasDerivAt_pow 2 u).const_mul (2 / (r - 1))
      simpa using this
    have hW : HasDerivAt (fun w => X w + (w / (r - 1)) • V w - xstar)
        (V u + (1 / (r - 1)) • V u + (u / (r - 1)) • (-(r / u) • V u - gradient f (X u))) u := by
      have hh : HasDerivAt (fun w : ℝ => w / (r - 1)) (1 / (r - 1)) u := by
        simpa using (hasDerivAt_id u).div_const (r - 1)
      have := (hXu.add (hh.smul hVu)).sub_const xstar
      refine this.congr_deriv ?_
      abel
    exact (hp.mul (h1.sub_const (f xstar))).add ((hW.norm_sq).const_mul (r - 1))
  have hc0 : ContinuousWithinAt E (Set.Ici 0) 0 := by
    have hXc : ContinuousWithinAt X (Set.Ici 0) 0 := hXd0.continuousWithinAt
    have hfX : ContinuousWithinAt (fun w => f (X w)) (Set.Ici 0) 0 :=
      (hd.continuous.continuousAt (x := X 0)).comp_continuousWithinAt hXc
    have hid : ContinuousWithinAt (fun w : ℝ => w) (Set.Ici 0) 0 := continuousWithinAt_id
    have hn : ContinuousWithinAt (fun w => ‖X w + (w / (r - 1)) • V w - xstar‖ ^ 2) (Set.Ici 0) 0 :=
      (((hXc.add ((hid.div_const (r - 1)).smul hVc0)).sub continuousWithinAt_const).norm.pow 2)
    exact ((continuousWithinAt_const.mul (hid.pow 2)).mul (hfX.sub continuousWithinAt_const)).add
      (continuousWithinAt_const.mul hn)
  have hanti : AntitoneOn E (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro u hu
      rcases (Set.mem_Ici.1 hu).eq_or_lt with h | h
      · subst h; exact hc0
      · exact (hder u h).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      exact (hder u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      rw [(hder u hu).deriv]
      have hG : f (X u) - f xstar ≤ ⟪gradient f (X u), X u - xstar⟫_ℝ := by
        have := hconv (X u) xstar
        rw [← neg_sub (X u) xstar, inner_neg_right] at this
        linarith
      have := key5 (X u - xstar) (V u) (gradient f (X u)) u r _ hu hr
        (sub_nonneg.2 (hmin _)) hG
      have e : X u + (u / (r - 1)) • V u - xstar = X u - xstar + (u / (r - 1)) • V u := by abel
      rw [e]; exact this
  have hEt := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht.le
  have hE0 : E 0 = (r - 1) * ‖x₀ - xstar‖ ^ 2 := by
    simp [hE, hX0, hV0]
  rw [hE0] at hEt
  exact hEt

theorem key8 (Y V g : F) (u P α k r μ δ : ℝ) (hu : 0 < u) (hP : 0 ≤ P) (hk : k = 2 * r - α)
    (hk0 : 0 < k) (hα : 2 ≤ α) (hαk : α ≤ k / 2) (hδ : 0 ≤ δ)
    (hsc : δ + μ / 2 * ‖Y‖ ^ 2 ≤ ⟪g, Y⟫_ℝ) (hut : (α - 2) * k ≤ 2 * μ * u ^ 2) :
    (((α - 2) * (P / u)) * u ^ 2 + P * (2 * u)) * δ + (P * u ^ 2) * ⟪g, V⟫_ℝ
      + ((k ^ 2 / 8 * ((α - 2) * (P / u))) * ‖Y + (2 * u / k) • V‖ ^ 2
        + (k ^ 2 / 8 * P) * (2 * ⟪Y + (2 * u / k) • V,
            V + (2 / k) • V + (2 * u / k) • (-(r / u) • V - g)⟫_ℝ))
      - (((α - 2) * k / 8 * ((α - 2) * (P / u))) * ‖Y‖ ^ 2
        + ((α - 2) * k / 8 * P) * (2 * ⟪Y, V⟫_ℝ)) ≤ 0 := by
  have hr : r = (k + α) / 2 := by linarith
  subst hr
  have eq : (((α - 2) * (P / u)) * u ^ 2 + P * (2 * u)) * δ + (P * u ^ 2) * ⟪g, V⟫_ℝ
      + ((k ^ 2 / 8 * ((α - 2) * (P / u))) * ‖Y + (2 * u / k) • V‖ ^ 2
        + (k ^ 2 / 8 * P) * (2 * ⟪Y + (2 * u / k) • V,
            V + (2 / k) • V + (2 * u / k) • (-((k + α) / 2 / u) • V - g)⟫_ℝ))
      - (((α - 2) * k / 8 * ((α - 2) * (P / u))) * ‖Y‖ ^ 2
        + ((α - 2) * k / 8 * P) * (2 * ⟪Y, V⟫_ℝ))
      = α * P * u * δ - k / 2 * P * u * ⟪g, Y⟫_ℝ
        + (α - 2) * k * (k - α + 2) * P / (8 * u) * ‖Y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (Y + _), ← real_inner_self_eq_norm_sq Y]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_sub_right,
      RCLike.conj_to_real]
    rw [real_inner_comm g V, real_inner_comm V Y, real_inner_comm g Y]
    field_simp
    ring
  rw [eq]
  have h1 : k / 2 * P * u * (δ + μ / 2 * ‖Y‖ ^ 2) ≤ k / 2 * P * u * ⟪g, Y⟫_ℝ :=
    mul_le_mul_of_nonneg_left hsc (by positivity)
  have h2 : (α - k / 2) * (P * u * δ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h3 : (α - 2) * k * (k - α + 2) ≤ 2 * μ * u ^ 2 * k := by
    have : (α - 2) * k * (k - α + 2) ≤ (α - 2) * k * k :=
      mul_le_mul_of_nonneg_left (by linarith) (by nlinarith)
    nlinarith
  have h4 : (α - 2) * k * (k - α + 2) * P / (8 * u) * ‖Y‖ ^ 2
      ≤ k / 2 * P * u * (μ / 2 * ‖Y‖ ^ 2) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ P * ‖Y‖ ^ 2)
    nlinarith
  nlinarith

theorem sc_pair [CompleteSpace F] (f : F → ℝ) (μ : ℝ)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) (x xstar : F) :
    f x - f xstar + μ / 2 * ‖x - xstar‖ ^ 2 ≤ ⟪gradient f x, x - xstar⟫_ℝ := by
  have := hsc x xstar
  rw [← neg_sub x xstar, inner_neg_right, norm_neg] at this
  linarith

theorem grad_zero [CompleteSpace F] (f : F → ℝ) (xstar : F) (hmin : ∀ y, f xstar ≤ f y) :
    gradient f xstar = 0 := by
  have hlm : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
  unfold gradient
  rw [hlm.fderiv_eq_zero, map_zero]

theorem sc_min [CompleteSpace F] (f : F → ℝ) (μ : ℝ)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y) (xstar : F)
    (hmin : ∀ y, f xstar ≤ f y) (x : F) :
    μ / 2 * ‖x - xstar‖ ^ 2 ≤ f x - f xstar := by
  have := hsc xstar x
  rw [grad_zero f xstar hmin, inner_zero_left] at this
  linarith

theorem phase2 [CompleteSpace F] (f : F → ℝ) (hd : Differentiable ℝ f) (xstar : F) (μ : ℝ)
    (hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + μ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hmin : ∀ y, f xstar ≤ f y) (r α k : ℝ) (hk : k = 2 * r - α) (hk0 : 0 < k) (hα : 2 ≤ α)
    (hαk : α ≤ k / 2) (X V : ℝ → F)
    (hode : ∀ t : ℝ, 0 < t → HasDerivAt X (V t) t ∧
      HasDerivAt V (-(r / t) • V t - gradient f (X t)) t)
    (hμ : 0 ≤ μ) (T t : ℝ) (hT : 0 < T) (hTt : T ≤ t) (hTμ : (α - 2) * k ≤ 2 * μ * T ^ 2) :
    t ^ (α - 2) * t ^ 2 * (f (X t) - f xstar)
        + k ^ 2 / 8 * t ^ (α - 2) * ‖X t + (2 * t / k) • V t - xstar‖ ^ 2
        - (α - 2) * k / 8 * t ^ (α - 2) * ‖X t - xstar‖ ^ 2
      ≤ T ^ (α - 2) * T ^ 2 * (f (X T) - f xstar)
        + k ^ 2 / 8 * T ^ (α - 2) * ‖X T + (2 * T / k) • V T - xstar‖ ^ 2
        - (α - 2) * k / 8 * T ^ (α - 2) * ‖X T - xstar‖ ^ 2 := by
  set H : ℝ → ℝ := fun u => u ^ (α - 2) * u ^ 2 * (f (X u) - f xstar)
        + k ^ 2 / 8 * u ^ (α - 2) * ‖X u + (2 * u / k) • V u - xstar‖ ^ 2
        - (α - 2) * k / 8 * u ^ (α - 2) * ‖X u - xstar‖ ^ 2 with hH
  have hder : ∀ u, 0 < u → HasDerivAt H
      ((((α - 2) * (u ^ (α - 2) / u)) * u ^ 2 + u ^ (α - 2) * (2 * u)) * (f (X u) - f xstar)
        + (u ^ (α - 2) * u ^ 2) * ⟪gradient f (X u), V u⟫_ℝ
      + ((k ^ 2 / 8 * ((α - 2) * (u ^ (α - 2) / u))) * ‖X u + (2 * u / k) • V u - xstar‖ ^ 2
        + (k ^ 2 / 8 * u ^ (α - 2)) * (2 * ⟪X u + (2 * u / k) • V u - xstar,
            V u + (2 / k) • V u + (2 * u / k) • (-(r / u) • V u - gradient f (X u))⟫_ℝ))
      - (((α - 2) * k / 8 * ((α - 2) * (u ^ (α - 2) / u))) * ‖X u - xstar‖ ^ 2
        + ((α - 2) * k / 8 * u ^ (α - 2)) * (2 * ⟪X u - xstar, V u⟫_ℝ))) u := by
    intro u hu
    obtain ⟨hXu, hVu⟩ := hode u hu
    have h1 : HasDerivAt (fun w => f (X w)) ⟪gradient f (X u), V u⟫_ℝ u := by
      have := (hd (X u)).hasFDerivAt.comp_hasDerivAt u hXu
      rw [grad_inner f] at this
      exact this
    have hp : HasDerivAt (fun w : ℝ => w ^ (α - 2)) ((α - 2) * (u ^ (α - 2) / u)) u := by
      have := Real.hasDerivAt_rpow_const (x := u) (p := α - 2) (Or.inl hu.ne')
      rw [Real.rpow_sub_one hu.ne'] at this
      exact this
    have hsq : HasDerivAt (fun w : ℝ => w ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have hW : HasDerivAt (fun w => X w + (2 * w / k) • V w - xstar)
        (V u + (2 / k) • V u + (2 * u / k) • (-(r / u) • V u - gradient f (X u))) u := by
      have hh : HasDerivAt (fun w : ℝ => 2 * w / k) (2 / k) u := by
        simpa using ((hasDerivAt_id u).const_mul 2).div_const k
      have := (hXu.add (hh.smul hVu)).sub_const xstar
      refine this.congr_deriv ?_
      abel
    have hY : HasDerivAt (fun w => X w - xstar) (V u) u := hXu.sub_const xstar
    exact (((hp.mul hsq).mul (h1.sub_const (f xstar))).add
      ((hp.const_mul (k ^ 2 / 8)).mul hW.norm_sq)).sub
      ((hp.const_mul ((α - 2) * k / 8)).mul hY.norm_sq)
  have hanti : AntitoneOn H (Set.Icc T t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro u hu
      exact (hder u (lt_of_lt_of_le hT hu.1)).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hder u (lt_trans hT hu.1)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have hu0 : 0 < u := lt_trans hT hu.1
      rw [(hder u hu0).deriv]
      have hsc' := sc_pair f μ hsc (X u) xstar
      have hut : (α - 2) * k ≤ 2 * μ * u ^ 2 := by
        have : T ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hT.le hu.1.le 2
        nlinarith
      have e : X u + (2 * u / k) • V u - xstar = X u - xstar + (2 * u / k) • V u := by abel
      rw [e]
      exact key8 (X u - xstar) (V u) (gradient f (X u)) u (u ^ (α - 2)) α k r μ _ hu0
        (Real.rpow_nonneg hu0.le _) hk hk0 hα hαk (sub_nonneg.2 (hmin _))
        (by linarith) hut
  exact hanti (Set.left_mem_Icc.2 hTt) (Set.right_mem_Icc.2 hTt) hTt

theorem num1 (a c d : ℝ) (hc : 0 < c) (h : 2 / c * a ≤ c * d) : a ≤ c ^ 2 / 2 * d := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hc] at h
  nlinarith

theorem sq_two (a b : F) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a b
  have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem norm_sq_smul (c : ℝ) (a : F) : ‖c • a‖ ^ 2 = c ^ 2 * ‖a‖ ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem numA (δ Pt PT m c0 t B : ℝ) (hδ : 0 ≤ δ) (hP : Pt ≤ PT) (hPt : 0 ≤ Pt) (hm : 0 < m)
    (hc : PT * m = c0) (hB : t ^ 2 * δ ≤ B) : δ * (m * (Pt * t ^ 2)) ≤ c0 * B := by
  have h1 : 0 ≤ t ^ 2 * δ := by positivity
  have h2 : m * Pt * (t ^ 2 * δ) ≤ m * PT * (t ^ 2 * δ) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP hm.le) h1
  have h3 : m * PT * (t ^ 2 * δ) ≤ m * PT * B :=
    mul_le_mul_of_nonneg_left hB (mul_nonneg hm.le (hPt.trans hP))
  have e : δ * (m * (Pt * t ^ 2)) = m * Pt * (t ^ 2 * δ) := by ring
  have e2 : c0 * B = m * PT * B := by rw [← hc]; ring
  rw [e, e2]; linarith

theorem numB (Pt t δ w y α k μ : ℝ) (hPt : 0 ≤ Pt) (hw : 0 ≤ w) (hy : 0 ≤ y)
    (hY : μ / 2 * y ≤ δ) (hut : (α - 2) * k ≤ 2 * μ * t ^ 2) :
    Pt * t ^ 2 * δ / 2 ≤ Pt * t ^ 2 * δ + k ^ 2 / 8 * Pt * w - (α - 2) * k / 8 * Pt * y := by
  have h1 : (α - 2) * k * y ≤ 2 * μ * t ^ 2 * y := mul_le_mul_of_nonneg_right hut hy
  have h2 : 2 * μ * t ^ 2 * y ≤ 4 * t ^ 2 * δ := by nlinarith [sq_nonneg t]
  have h3 : Pt * ((α - 2) * k * y) ≤ Pt * (4 * t ^ 2 * δ) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hPt
  have h4 : 0 ≤ k ^ 2 / 8 * Pt * w := by positivity
  nlinarith

theorem numD (Tδ w a y D r k lam q μ T δT : ℝ) (hq : 0 < q) (hD : 0 ≤ D)
    (h1 : T ^ 2 * δT ≤ (r - 1) ^ 2 / 2 * D) (hw : w ≤ 2 * lam ^ 2 * a + 2 * (1 - lam) ^ 2 * y)
    (ha : a ≤ D) (hy : μ / 2 * y ≤ δT) (hμT : μ * T ^ 2 = q) (hTδ : Tδ = T ^ 2 * δT)
    (hy0 : 0 ≤ y) :
    Tδ + k ^ 2 / 8 * w ≤ ((r - 1) ^ 2 / 2 + k ^ 2 / 4 * (lam ^ 2 + (1 - lam) ^ 2 * ((r - 1) ^ 2 / q))) * D := by
  have hyq : y * q ≤ (r - 1) ^ 2 * D := by
    rw [← hμT]
    have : μ * y ≤ 2 * δT := by linarith
    nlinarith [sq_nonneg T]
  have hy' : y ≤ (r - 1) ^ 2 / q * D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]; linarith
  have hk : 0 ≤ k ^ 2 / 8 := by positivity
  have h2 : k ^ 2 / 8 * w ≤ k ^ 2 / 8 * (2 * lam ^ 2 * D + 2 * (1 - lam) ^ 2 * ((r - 1) ^ 2 / q * D)) := by
    apply mul_le_mul_of_nonneg_left _ hk
    have := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 2 * lam ^ 2)
    have := mul_le_mul_of_nonneg_left hy' (by positivity : 0 ≤ 2 * (1 - lam) ^ 2)
    linarith
  rw [hTδ]
  nlinarith

theorem numE (δ m Pt t PT K D c0 HT Ht : ℝ) (hm : 0 < m) (hc : PT * m = c0)
    (hlow : Pt * t ^ 2 * δ / 2 ≤ Ht) (hHt : Ht ≤ HT) (hHT : HT ≤ PT * (K * D)) :
    δ * (m * (Pt * t ^ 2)) ≤ 2 * K * c0 * D := by
  have h : Pt * t ^ 2 * δ ≤ 2 * (PT * (K * D)) := by linarith
  have := mul_le_mul_of_nonneg_left h hm.le
  have e : δ * (m * (Pt * t ^ 2)) = m * (Pt * t ^ 2 * δ) := by ring
  have e2 : 2 * K * c0 * D = m * (2 * (PT * (K * D))) := by rw [← hc]; ring
  rw [e, e2]; exact this

end RRAux_NesterovODE_StrongCvx_theorem_8

open scoped InnerProductSpace
open RRAux_NesterovODE_StrongCvx_theorem_8

open NesterovODE.StrongCvx in
theorem solution (r α : ℝ) (ha : 2 ≤ α) (hr : α ≤ 2 * r / 3) :
    ∃ C : ℝ, ∀ (n : ℕ) (f : NesterovODE.WellPosed.E n → ℝ) (mu : ℝ) (L : NNReal),
      0 < mu → 0 < L → InSMuL mu L f →
      ∀ (x₀ xstar : NesterovODE.WellPosed.E n), (∀ y, f xstar ≤ f y) →
      ∀ (X V : ℝ → NesterovODE.WellPosed.E n), IsSolution f r x₀ X V →
      ∀ t : ℝ, 0 < t →
        f (X t) - f xstar ≤
          C * ‖x₀ - xstar‖ ^ 2 / (mu ^ ((α - 2) / 2) * t ^ α) := by
  have hr3 : 3 ≤ r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hk0 : 0 < 2 * r - α := by linarith
  have hαk : α ≤ (2 * r - α) / 2 := by linarith
  rcases ha.eq_or_lt with h2 | h2
  · subst h2
    refine ⟨(r - 1) ^ 2 / 2, ?_⟩
    intro n f mu L hmu hL hf x₀ xstar hmin X V hX t ht
    obtain ⟨⟨_, hconv, hC1, _⟩, _, _⟩ := hf
    have hd : Differentiable ℝ f := hC1.differentiable (by norm_num)
    obtain ⟨hX0, hV0, hXd0, hVc0, hode⟩ := hX
    have hcg : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
      intro x y
      have := sc_grad f 0 (by simpa using hconv) hd x y
      simpa using this
    have h1 := phase1 f hcg hd xstar hmin r hr3 x₀ X V hX0 hV0 hXd0 hVc0 hode t ht
    have h2 : 2 / (r - 1) * (t ^ 2 * (f (X t) - f xstar)) ≤ (r - 1) * ‖x₀ - xstar‖ ^ 2 := by
      have : 0 ≤ (r - 1) * ‖X t + (t / (r - 1)) • V t - xstar‖ ^ 2 := by positivity
      linarith
    have h3 := num1 _ _ _ hr1 h2
    have e : mu ^ (((2:ℝ) - 2) / 2) * t ^ (2:ℝ) = t ^ 2 := by
      norm_num
    rw [e, le_div_iff₀ (by positivity)]
    linarith
  · set k := 2 * r - α with hk
    set q := (α - 2) * k / 2 with hq
    have hq0 : 0 < q := by rw [hq]; have : 0 < α - 2 := by linarith
                           positivity
    set c0 := q ^ ((α - 2) / 2) with hc0
    set lam := 2 * (r - 1) / k with hlam
    set K := (r - 1) ^ 2 / 2 + k ^ 2 / 4 * (lam ^ 2 + (1 - lam) ^ 2 * ((r - 1) ^ 2 / q)) with hK
    have hc0p : 0 ≤ c0 := Real.rpow_nonneg hq0.le _
    have hKp : 0 ≤ K := by rw [hK]; positivity
    refine ⟨(r - 1) ^ 2 * c0 / 2 + 2 * K * c0, ?_⟩
    intro n f mu L hmu hL hf x₀ xstar hmin X V hX t ht
    obtain ⟨⟨_, hconv, hC1, _⟩, _, hscv⟩ := hf
    have hd : Differentiable ℝ f := hC1.differentiable (by norm_num)
    obtain ⟨hX0, hV0, hXd0, hVc0, hode⟩ := hX
    have hcg : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
      intro x y
      have := sc_grad f 0 (by simpa using hconv) hd x y
      simpa using this
    have hsc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ + mu / 2 * ‖y - x‖ ^ 2 ≤ f y :=
      sc_grad f mu hscv hd
    have ph1 := phase1 f hcg hd xstar hmin r hr3 x₀ X V hX0 hV0 hXd0 hVc0 hode
    set D := ‖x₀ - xstar‖ ^ 2 with hD
    have hD0 : 0 ≤ D := by positivity
    -- bound t² δ ≤ (r-1)²/2 D for all t > 0
    have hδb : ∀ u, 0 < u → u ^ 2 * (f (X u) - f xstar) ≤ (r - 1) ^ 2 / 2 * D := by
      intro u hu
      have h1 := ph1 u hu
      have h2 : 2 / (r - 1) * (u ^ 2 * (f (X u) - f xstar)) ≤ (r - 1) * D := by
        have : 0 ≤ (r - 1) * ‖X u + (u / (r - 1)) • V u - xstar‖ ^ 2 := by positivity
        linarith
      exact num1 _ _ _ hr1 h2
    have hAb : ∀ u, 0 < u → ‖X u + (u / (r - 1)) • V u - xstar‖ ^ 2 ≤ D := by
      intro u hu
      have h1 := ph1 u hu
      have : 0 ≤ 2 / (r - 1) * u ^ 2 * (f (X u) - f xstar) := by
        have := sub_nonneg.2 (hmin (X u)); positivity
      have h3 : (r - 1) * ‖X u + (u / (r - 1)) • V u - xstar‖ ^ 2 ≤ (r - 1) * D := by linarith
      exact le_of_mul_le_mul_left h3 hr1
    set T := Real.sqrt (q / mu) with hT
    have hT0 : 0 < T := Real.sqrt_pos.2 (by positivity)
    have hT2 : T ^ 2 = q / mu := Real.sq_sqrt (by positivity)
    have hμT : mu * T ^ 2 = q := by rw [hT2]; field_simp
    have hme : 0 < mu ^ ((α - 2) / 2) := Real.rpow_pos_of_pos hmu _
    have hTc : T ^ (α - 2) * mu ^ ((α - 2) / 2) = c0 := by
      rw [hT, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity), Real.div_rpow hq0.le hmu.le]
      have e : 1 / 2 * (α - 2) = (α - 2) / 2 := by ring
      rw [e, hc0]
      field_simp
    have htα : t ^ α = t ^ (α - 2) * t ^ 2 := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
      congr 1; push_cast; ring
    have hδ0 : 0 ≤ f (X t) - f xstar := sub_nonneg.2 (hmin _)
    rw [htα, le_div_iff₀ (by have := Real.rpow_pos_of_pos ht (α - 2); positivity)]
    rcases le_or_gt t T with htT | htT
    · have hP : t ^ (α - 2) ≤ T ^ (α - 2) := Real.rpow_le_rpow ht.le htT (by linarith)
      have := numA _ _ _ _ c0 t _ hδ0 hP (Real.rpow_nonneg ht.le _) hme hTc (hδb t ht)
      have hx : 0 ≤ 2 * K * c0 * D := by positivity
      have e : ((r - 1) ^ 2 * c0 / 2 + 2 * K * c0) * D = c0 * ((r - 1) ^ 2 / 2 * D) + 2 * K * c0 * D := by
        ring
      rw [e]; linarith
    · have hTμ : (α - 2) * k ≤ 2 * mu * T ^ 2 := by
        have e : 2 * mu * T ^ 2 = 2 * (mu * T ^ 2) := by ring
        rw [e, hμT, hq]; linarith
      have hp2 := phase2 f hd xstar mu hsc hmin r α k hk hk0 ha hαk X V hode hmu.le T t hT0 htT.le hTμ
      have hut : (α - 2) * k ≤ 2 * mu * t ^ 2 := by
        have : T ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hT0.le htT.le 2
        have := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ 2 * mu)
        linarith
      have hlow := numB (t ^ (α - 2)) t (f (X t) - f xstar)
        (‖X t + (2 * t / k) • V t - xstar‖ ^ 2) (‖X t - xstar‖ ^ 2) α k mu
        (Real.rpow_nonneg ht.le _) (by positivity) (by positivity)
        (sc_min f mu hsc xstar hmin (X t)) hut
      -- W_T = lam • A_T + (1 - lam) • Y_T
      have hWT : ‖X T + (2 * T / k) • V T - xstar‖ ^ 2
          ≤ 2 * lam ^ 2 * ‖X T + (T / (r - 1)) • V T - xstar‖ ^ 2
            + 2 * (1 - lam) ^ 2 * ‖X T - xstar‖ ^ 2 := by
        have e : X T + (2 * T / k) • V T - xstar
            = lam • (X T + (T / (r - 1)) • V T - xstar) + (1 - lam) • (X T - xstar) := by
          have hc : 2 * T / k = lam * (T / (r - 1)) := by
            rw [hlam]; field_simp
          rw [hc]; module
        rw [e]
        have := sq_two (lam • (X T + (T / (r - 1)) • V T - xstar)) ((1 - lam) • (X T - xstar))
        rw [norm_sq_smul, norm_sq_smul] at this
        linarith
      have hD' := numD (T ^ 2 * (f (X T) - f xstar)) _ _ _ D r k lam q mu T _ hq0 hD0
        (hδb T hT0) hWT (hAb T hT0) (sc_min f mu hsc xstar hmin (X T)) hμT rfl (by positivity)
      have hHT : T ^ (α - 2) * T ^ 2 * (f (X T) - f xstar)
          + k ^ 2 / 8 * T ^ (α - 2) * ‖X T + (2 * T / k) • V T - xstar‖ ^ 2
          - (α - 2) * k / 8 * T ^ (α - 2) * ‖X T - xstar‖ ^ 2 ≤ T ^ (α - 2) * (K * D) := by
        have hPT : 0 ≤ T ^ (α - 2) := Real.rpow_nonneg hT0.le _
        have h1 : 0 ≤ (α - 2) * k / 8 * T ^ (α - 2) * ‖X T - xstar‖ ^ 2 := by
          have : 0 ≤ α - 2 := by linarith
          positivity
        have h2 := mul_le_mul_of_nonneg_left hD' hPT
        rw [← hK] at h2
        have e : T ^ (α - 2) * (T ^ 2 * (f (X T) - f xstar)
            + k ^ 2 / 8 * ‖X T + (2 * T / k) • V T - xstar‖ ^ 2)
            = T ^ (α - 2) * T ^ 2 * (f (X T) - f xstar)
              + k ^ 2 / 8 * T ^ (α - 2) * ‖X T + (2 * T / k) • V T - xstar‖ ^ 2 := by ring
        linarith
      have := numE _ _ _ t _ K D c0 _ _ hme hTc hlow hp2 hHT
      have hx : 0 ≤ (r - 1) ^ 2 * c0 / 2 * D := by positivity
      have e : ((r - 1) ^ 2 * c0 / 2 + 2 * K * c0) * D = (r - 1) ^ 2 * c0 / 2 * D + 2 * K * c0 * D := by
        ring
      rw [e]; linarith

#print axioms solution
