-- Prove2me | solution 1 for HessianDamping.IGAHD.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T01:54:25.401971+00:00
-- url     : https://prove2.me/submissions/a55b51dc-832d-4d05-950d-012df455053b

import Mathlib
import Definitions.Def_HessianDamping_IGAHD_Setting

set_option autoImplicit false

namespace IGAHD6Aux

open Set Filter Topology InnerProductSpace HessianDamping.IGAHD

theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) (inner ℝ (G (x + t • w)) w) t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + inner ℝ (G x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * inner ℝ (G x) w - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (inner ℝ (G (x + t • w)) w - inner ℝ (G x) w
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (G x) w) (inner ℝ (G x) w) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (G x) w)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : inner ℝ (G (x + c • w)) w - inner ℝ (G x) w - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : inner ℝ (G (x + c • w)) w - inner ℝ (G x) w = inner ℝ (G (x + c • w) - G x) w := by
      rw [inner_sub_left]
    have e2 := real_inner_le_norm (G (x + c • w) - G x) w
    have e3 := hG (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖G (x + c • w) - G x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

lemma inner_gradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (x v : H) :
    inner ℝ (gradient f x) v = fderiv ℝ f x v := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma convex_first_order {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (hfd : Differentiable ℝ f) (x y : H) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have hc : ConvexOn ℝ Set.univ (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)) := by
    have := hfconv.comp_affineMap (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)
    simpa using this
  have hd : HasDerivAt (f ∘ (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H)) (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasDerivAt (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H) (y - x) 0 :=
      AffineMap.hasDerivAt_lineMap
    have h2 : HasFDerivAt f (fderiv ℝ f x) ((AffineMap.lineMap x y : ℝ →ᵃ[ℝ] H) (0:ℝ)) := by
      simpa using (hfd x).hasFDerivAt
    exact h2.comp_hasDerivAt (0:ℝ) h1
  have := hc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at this
  simp at this
  rw [inner_gradient, map_sub]
  linarith

/-- Cocoercivity-type upper bound for a convex function with `L`-Lipschitz gradient. -/
theorem coco {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (y z : H) :
    f y ≤ f z + inner ℝ (gradient f y) (y - z)
      - (1 / L) / 2 * ‖gradient f z - gradient f y‖ ^ 2 := by
  set ι : ℝ := 1 / L with hιdef
  have hι : ι * L = 1 := by rw [hιdef]; field_simp
  set d := gradient f z - gradient f y with hd
  set w := z - ι • d with hw
  have hF : ∀ u, HasGradientAt f (gradient f u) u := fun u => (hfd u).hasGradientAt
  have h1 := convex_first_order f hfconv hfd y w
  have h2 := descent hF hLip z w
  have i1 : inner ℝ (gradient f y) (w - y)
      = - inner ℝ (gradient f y) (y - z) - ι * inner ℝ (gradient f y) d := by
    simp only [hw, inner_sub_right, real_inner_smul_right]; ring
  have i2 : inner ℝ (gradient f z) (w - z) = - ι * inner ℝ (gradient f z) d := by
    simp only [hw, sub_sub_cancel_left, inner_neg_right, real_inner_smul_right]; ring
  have i3 : ‖w - z‖ ^ 2 = ι ^ 2 * ‖d‖ ^ 2 := by
    simp only [hw, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have i4 : inner ℝ (gradient f z) d - inner ℝ (gradient f y) d = ‖d‖ ^ 2 := by
    rw [← inner_sub_left]; exact real_inner_self_eq_norm_sq d
  have i5 : L / 2 * (ι ^ 2 * ‖d‖ ^ 2) = ι / 2 * ‖d‖ ^ 2 := by
    have : L / 2 * (ι ^ 2 * ‖d‖ ^ 2) = (ι * L) * (ι / 2 * ‖d‖ ^ 2) := by ring
    rw [this, hι, one_mul]
  have i6 := congrArg (ι * ·) i4
  simp only [mul_sub] at i6
  rw [i1] at h1
  rw [i2, i3, i5] at h2
  linarith

/-- One gradient step from `y`, compared with any point `z`. -/
theorem gstep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (s : ℝ) (hs : 0 < s) (hsL : s ≤ 1 / L) (y z : H) :
    f (y - s • gradient f y) ≤ f z + inner ℝ (gradient f y) (y - z)
      - s / 2 * ‖gradient f y‖ ^ 2 - s / 2 * ‖gradient f y - gradient f z‖ ^ 2 := by
  have hF : ∀ u, HasGradientAt f (gradient f u) u := fun u => (hfd u).hasGradientAt
  have D := descent hF hLip y (y - s • gradient f y)
  have e1 : y - s • gradient f y - y = -(s • gradient f y) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at D
  have hLs : s * L ≤ 1 := by rwa [le_div_iff₀ hL] at hsL
  have hX : 0 ≤ s / 2 * ‖gradient f y‖ ^ 2 := by positivity
  have e2 : L / 2 * (s ^ 2 * ‖gradient f y‖ ^ 2) ≤ s / 2 * ‖gradient f y‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hLs hX
    nlinarith
  have C := coco f hfconv hfd L hL hLip y z
  rw [norm_sub_rev (gradient f z)] at C
  have e3 : s / 2 * ‖gradient f y - gradient f z‖ ^ 2
      ≤ (1 / L) / 2 * ‖gradient f y - gradient f z‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  linarith

theorem grad_min_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (s : ℝ) (hs : 0 < s) (hsL : s ≤ 1 / L) (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z) :
    gradient f xstar = 0 := by
  have h1 := gstep f hfconv hfd L hL hLip s hs hsL xstar xstar
  have h2 := hxstar (xstar - s • gradient f xstar)
  simp only [sub_self, inner_zero_right, norm_zero, add_zero] at h1
  have h3 : ‖gradient f xstar‖ ^ 2 ≤ 0 := by nlinarith
  have h4 : ‖gradient f xstar‖ ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

theorem vid1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (xk xk1 xs gk gk1 G yk xn : H) (α s c K : ℝ) (hK : K ≠ 0) (hα : α - 1 ≠ 0)
    (hy : yk = xk + (1 - α / K) • (xk - xk1) - c • (gk - gk1) - (c / K) • gk1)
    (hx : xn = yk - s • G) :
    (xk - xs) + (K / (α - 1)) • (xn - xk + c • gk)
      = ((xk1 - xs) + ((K - 1) / (α - 1)) • (xk - xk1 + c • gk1)) - (s * (K / (α - 1))) • G := by
  subst hx; subst hy
  match_scalars <;> field_simp <;> ring

theorem vid2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (xk xk1 xs gk gk1 yk : H) (α c K : ℝ) (hK : K ≠ 0) (hα : α - 1 ≠ 0)
    (hy : yk = xk + (1 - α / K) • (xk - xk1) - c • (gk - gk1) - (c / K) • gk1) :
    (K / (α - 1) - 1) • (yk - xk) + (yk - xs)
      = ((xk1 - xs) + ((K - 1) / (α - 1)) • (xk - xk1 + c • gk1)) - (K / (α - 1) * c) • gk := by
  subst hy
  match_scalars <;> field_simp <;> ring

/-- Scalar/vector heart of the Lyapunov step `E_{k+1} + t_{k+1} B_k ≤ E_k`. -/
theorem stepAlg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b v vn yk xk xs : H) (τ δ s c F0 F1 : ℝ) (hs : 0 < s) (hτ : 1 ≤ τ)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hF0 : 0 ≤ F0)
    (hA : F1 ≤ F0 + inner ℝ a (yk - xk) - s / 2 * ‖a‖ ^ 2 - s / 2 * ‖a - b‖ ^ 2)
    (hB : F1 ≤ inner ℝ a (yk - xs) - s * ‖a‖ ^ 2)
    (hvn : vn = v - (s * τ) • a)
    (hv2 : (τ - 1) • (yk - xk) + (yk - xs) = v - (τ * c) • b) :
    τ ^ 2 * F1 + 1 / (2 * s) * ‖vn‖ ^ 2
      + τ * (τ * c * inner ℝ a b + s / 2 * (τ - 1) * ‖b - a‖ ^ 2 + s / 2 * ‖a‖ ^ 2)
      ≤ (τ - δ) ^ 2 * F0 + 1 / (2 * s) * ‖v‖ ^ 2 := by
  have e1 : 1 / (2 * s) * ‖vn‖ ^ 2
      = 1 / (2 * s) * ‖v‖ ^ 2 - τ * inner ℝ a v + s * τ ^ 2 / 2 * ‖a‖ ^ 2 := by
    rw [hvn, norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow,
      sq_abs, real_inner_comm a v]
    field_simp
  have e2 : (τ - 1) * inner ℝ a (yk - xk) + inner ℝ a (yk - xs)
      = inner ℝ a v - τ * c * inner ℝ a b := by
    have := congrArg (inner ℝ a) hv2
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right] at this ⊢
    linarith
  have hA' := mul_le_mul_of_nonneg_left hA (show 0 ≤ τ * (τ - 1) by nlinarith)
  have hB' := mul_le_mul_of_nonneg_left hB (show 0 ≤ τ by linarith)
  have e2' := congrArg (τ * ·) e2
  simp only [mul_add, mul_sub] at e2'
  have hq : τ * (τ - 1) * F0 ≤ (τ - δ) ^ 2 * F0 :=
    mul_le_mul_of_nonneg_right (by nlinarith) hF0
  have hab : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
  rw [e1, hab]
  linarith

theorem Bbound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : H) (s c τ γ : ℝ) (hs : 0 < s) (hγ : 0 < γ) (hγc : γ ≤ c) (hγ2 : γ ≤ 2 * s - c)
    (hτ : 4 * s / γ ≤ τ) :
    γ / 4 * τ * (‖a‖ ^ 2 + ‖b‖ ^ 2)
      ≤ τ * c * inner ℝ a b + s / 2 * (τ - 1) * ‖b - a‖ ^ 2 + s / 2 * ‖a‖ ^ 2 := by
  have hτγ : 4 * s ≤ τ * γ := by rwa [div_le_iff₀ hγ] at hτ
  have hτ0 : 0 ≤ τ := by
    have : 0 < 4 * s / γ := by positivity
    linarith
  have e : ‖b - a‖ ^ 2 = ‖b‖ ^ 2 - 2 * inner ℝ a b + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm a b]
  have hp1 : 2 * inner ℝ a b ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have := norm_sub_sq_real a b
    nlinarith [sq_nonneg ‖a - b‖]
  have hp2 : -(‖a‖ ^ 2 + ‖b‖ ^ 2) ≤ 2 * inner ℝ a b := by
    have := norm_add_sq_real a b
    nlinarith [sq_nonneg ‖a + b‖]
  rw [e]
  have hA : 0 ≤ ‖a‖ ^ 2 := sq_nonneg _
  have hB : 0 ≤ ‖b‖ ^ 2 := sq_nonneg _
  rcases le_total 0 (τ * (c - s) + s) with hm | hm
  · have h1 := mul_le_mul_of_nonneg_left hp2 hm
    have hcoef : 0 ≤ τ * (s - c / 2 - γ / 2) := mul_nonneg hτ0 (by linarith)
    have hcA : 0 ≤ τ * (s - c / 2 - γ / 2) + τ * γ / 4 - s / 2 := by linarith
    have hcB : 0 ≤ τ * (s - c / 2 - γ / 2) + τ * γ / 4 - s := by linarith
    nlinarith [mul_nonneg hcA hA, mul_nonneg hcB hB]
  · have h1 := mul_le_mul_of_nonpos_left hp1 hm
    have hcA' : 0 ≤ τ * (c / 2 - γ / 4) := mul_nonneg hτ0 (by linarith)
    nlinarith [mul_nonneg hcA' hA, mul_nonneg hcA' hB, mul_nonneg hs.le hA]

theorem Bunif {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s β : ℝ) (hs : 0 < s) (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s) :
    ∃ ε T : ℝ, 0 ≤ ε ∧ 1 ≤ T ∧ (0 < β → 0 < ε) ∧ ∀ τ, T ≤ τ → ∀ a b : H,
      ε * τ * (‖a‖ ^ 2 + ‖b‖ ^ 2)
        ≤ τ * (β * Real.sqrt s) * inner ℝ a b + s / 2 * (τ - 1) * ‖b - a‖ ^ 2
          + s / 2 * ‖a‖ ^ 2 := by
  rcases hβ0.eq_or_lt with h | h
  · refine ⟨0, 1, le_refl _, le_refl _, fun h' => absurd h' (by rw [← h]; exact lt_irrefl _),
      fun τ hτ a b => ?_⟩
    rw [← h]
    have h1 : 0 ≤ τ - 1 := by linarith
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ s / 2) h1) (sq_nonneg ‖b - a‖),
      mul_nonneg (by positivity : (0:ℝ) ≤ s / 2) (sq_nonneg ‖a‖)]
  · have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
    have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
    have hc : 0 < β * Real.sqrt s := mul_pos h hsp
    have hc2 : β * Real.sqrt s < 2 * s := by nlinarith
    have hγ : 0 < min (β * Real.sqrt s) (2 * s - β * Real.sqrt s) := lt_min hc (by linarith)
    refine ⟨min (β * Real.sqrt s) (2 * s - β * Real.sqrt s) / 4,
      max 1 (4 * s / min (β * Real.sqrt s) (2 * s - β * Real.sqrt s)),
      by positivity, le_max_left _ _, fun _ => by positivity, fun τ hτ a b => ?_⟩
    exact Bbound a b s _ τ _ hs hγ (min_le_left _ _) (min_le_right _ _)
      (le_trans (le_max_right _ _) hτ)

theorem summable_tele (h E : ℕ → ℝ) (k₀ : ℕ) (C : ℝ) (hC : 0 ≤ C) (hh : ∀ n, 0 ≤ h n)
    (hE : ∀ n, 0 ≤ E n) (hle : ∀ n, k₀ ≤ n → h n ≤ C * (E n - E (n + 1))) : Summable h := by
  rw [← summable_nat_add_iff k₀]
  refine summable_of_sum_range_le (c := C * E k₀) (fun n => hh _) (fun N => ?_)
  calc ∑ i ∈ Finset.range N, h (i + k₀)
      ≤ ∑ i ∈ Finset.range N, C * (E (i + k₀) - E (i + 1 + k₀)) := by
        apply Finset.sum_le_sum
        intro i _
        have := hle (i + k₀) (by omega)
        rwa [show i + k₀ + 1 = i + 1 + k₀ by ring] at this
    _ = C * (E (0 + k₀) - E (N + k₀)) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_range_sub' (fun i => E (i + k₀)) N
    _ ≤ C * E k₀ := by
        have := hE (N + k₀)
        simp only [zero_add]
        nlinarith

theorem tK_succ (α : ℝ) (k : ℕ) : tK α (k + 1) = (k : ℝ) / (α - 1) := by
  unfold tK; push_cast; ring

theorem lyap_step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfd : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y) (k : ℕ) (hk : 1 ≤ k)
    (hτ : 1 ≤ tK α (k + 1)) :
    EK f α β s x xstar (k + 1) + tK α (k + 1) * BK f α β s x y k ≤ EK f α β s x xstar k := by
  obtain ⟨hy, hx⟩ := hrun k hk
  have hgx := grad_min_zero f hfconv hfd L hL hLip s hs hsL xstar hxstar
  have hα1 : α - 1 ≠ 0 := (by linarith : (0:ℝ) < α - 1).ne'
  have hK : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htk1 := tK_succ α k
  have hA0 := gstep f hfconv hfd L hL hLip s hs hsL (y k) (x k)
  have hB0 := gstep f hfconv hfd L hL hLip s hs hsL (y k) xstar
  rw [← hx] at hA0 hB0
  rw [hgx, sub_zero] at hB0
  have hvn : vK f α β s x xstar (k + 1)
      = vK f α β s x xstar k - (s * tK α (k + 1)) • gradient f (y k) := by
    unfold vK
    simp only [Nat.add_sub_cancel]
    rw [htk1]
    unfold tK
    exact vid1 (x k) (x (k - 1)) xstar (gradient f (x k)) (gradient f (x (k - 1)))
      (gradient f (y k)) (y k) (x (k + 1)) α s (β * Real.sqrt s) k hK hα1 hy hx
  have hv2 : (tK α (k + 1) - 1) • (y k - x k) + (y k - xstar)
      = vK f α β s x xstar k - (tK α (k + 1) * (β * Real.sqrt s)) • gradient f (x k) := by
    rw [htk1]
    unfold vK tK
    exact vid2 (x k) (x (k - 1)) xstar (gradient f (x k)) (gradient f (x (k - 1)))
      (y k) α (β * Real.sqrt s) k hK hα1 hy
  have hδ : tK α k = tK α (k + 1) - 1 / (α - 1) := by
    rw [htk1]; unfold tK; field_simp
  have hδ1 : 1 / (α - 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hδ0 : 0 ≤ 1 / (α - 1) := by
    have : 0 < α - 1 := by linarith
    positivity
  have hF0 : 0 ≤ f (x k) - f xstar := by linarith [hxstar (x k)]
  have key := stepAlg (gradient f (y k)) (gradient f (x k)) (vK f α β s x xstar k)
    (vK f α β s x xstar (k + 1)) (y k) (x k) xstar (tK α (k + 1)) (1 / (α - 1)) s
    (β * Real.sqrt s) (f (x k) - f xstar) (f (x (k + 1)) - f xstar) hs hτ hδ0 hδ1 hF0
    (by linarith [hA0]) (by linarith [hB0]) hvn hv2
  have eB : BK f α β s x y k = tK α (k + 1) * (β * Real.sqrt s) *
        inner ℝ (gradient f (y k)) (gradient f (x k))
      + s / 2 * (tK α (k + 1) - 1) * ‖gradient f (x k) - gradient f (y k)‖ ^ 2
      + s / 2 * ‖gradient f (y k)‖ ^ 2 := by
    unfold BK; ring
  unfold EK
  rw [hδ, eB]
  linarith

end IGAHD6Aux

open HessianDamping.IGAHD in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (hfdiff : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ u v : H, ‖gradient f u - gradient f v‖ ≤ L * ‖u - v‖)
    (xstar : H) (hxstar : ∀ z : H, f xstar ≤ f z)
    (α β s : ℝ) (hα : 3 ≤ α) (hs : 0 < s) (hsL : s ≤ 1 / L)
    (hβ0 : 0 ≤ β) (hβs : β < 2 * Real.sqrt s)
    (x y : ℕ → H) (hrun : IsIGAHDRun f α β s x y) :
    (∃ k₀ : ℕ, 1 ≤ k₀ ∧ ∀ k ≥ k₀,
      EK f α β s x xstar (k + 1) ≤ EK f α β s x xstar k) ∧
    (fun k : ℕ => f (x k) - f xstar) =O[Filter.atTop]
      (fun k : ℕ => 1 / (k : ℝ) ^ 2) ∧
    (0 < β →
      Summable (fun k : ℕ => (k : ℝ) ^ 2 * ‖gradient f (y k)‖ ^ 2) ∧
      Summable (fun k : ℕ => (k : ℝ) ^ 2 * ‖gradient f (x k)‖ ^ 2)) := by
  have hα1 : 0 < α - 1 := by linarith
  obtain ⟨ε, T, hε0, hT1, hεpos, hBd⟩ := IGAHD6Aux.Bunif (H := H) s β hs hβ0 hβs
  set k₀ : ℕ := ⌈(α - 1) * T⌉₊ + 1 with hk₀
  have hτk : ∀ k, k₀ ≤ k → T ≤ tK α (k + 1) := by
    intro k hk
    rw [IGAHD6Aux.tK_succ, le_div_iff₀ hα1]
    have h1 := Nat.le_ceil ((α - 1) * T)
    have h2 : ((⌈(α - 1) * T⌉₊ : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (by omega : ⌈(α - 1) * T⌉₊ ≤ k)
    linarith [mul_comm T (α - 1)]
  have hdec : ∀ k, k₀ ≤ k → EK f α β s x xstar (k + 1)
      + ε * tK α (k + 1) ^ 2 * (‖gradient f (y k)‖ ^ 2 + ‖gradient f (x k)‖ ^ 2)
      ≤ EK f α β s x xstar k := by
    intro k hk
    have hk1 : 1 ≤ k := by omega
    have hT := hτk k hk
    have hτ1 : 1 ≤ tK α (k + 1) := le_trans hT1 hT
    have h1 := IGAHD6Aux.lyap_step f hfconv hfdiff L hL hLip xstar hxstar α β s hα hs hsL
      x y hrun k hk1 hτ1
    have h2 := hBd _ hT (gradient f (y k)) (gradient f (x k))
    have eB : BK f α β s x y k = tK α (k + 1) * (β * Real.sqrt s) *
          inner ℝ (gradient f (y k)) (gradient f (x k))
        + s / 2 * (tK α (k + 1) - 1) * ‖gradient f (x k) - gradient f (y k)‖ ^ 2
        + s / 2 * ‖gradient f (y k)‖ ^ 2 := by
      unfold BK; ring
    rw [eB] at h1
    have h3 := mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ tK α (k + 1))
    linarith
  have hEnn : ∀ k, 0 ≤ EK f α β s x xstar k := by
    intro k
    unfold EK
    have h1 : 0 ≤ tK α k ^ 2 * (f (x k) - f xstar) :=
      mul_nonneg (sq_nonneg _) (by linarith [hxstar (x k)])
    have h2 : 0 ≤ 1 / (2 * s) * ‖vK f α β s x xstar k‖ ^ 2 := by positivity
    linarith
  have hmono : ∀ k ≥ k₀, EK f α β s x xstar (k + 1) ≤ EK f α β s x xstar k := by
    intro k hk
    have := hdec k hk
    have : 0 ≤ ε * tK α (k + 1) ^ 2 * (‖gradient f (y k)‖ ^ 2 + ‖gradient f (x k)‖ ^ 2) := by
      positivity
    linarith
  have hbound : ∀ n, EK f α β s x xstar (k₀ + n) ≤ EK f α β s x xstar k₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc]
      exact le_trans (hmono (k₀ + n) (by omega)) ih
  refine ⟨⟨k₀, by omega, hmono⟩, ?_, ?_⟩
  · apply Asymptotics.IsBigO.of_bound (4 * EK f α β s x xstar k₀ * (α - 1) ^ 2)
    rw [Filter.eventually_atTop]
    refine ⟨max k₀ 2, fun k hk => ?_⟩
    have hk0 : k₀ ≤ k := le_of_max_le_left hk
    have hk2 : 2 ≤ k := le_of_max_le_right hk
    have hEk : EK f α β s x xstar k ≤ EK f α β s x xstar k₀ := by
      have := hbound (k - k₀)
      rwa [Nat.add_sub_cancel' hk0] at this
    have hF : 0 ≤ f (x k) - f xstar := by linarith [hxstar (x k)]
    have hle : tK α k ^ 2 * (f (x k) - f xstar) ≤ EK f α β s x xstar k := by
      unfold EK
      have : 0 ≤ 1 / (2 * s) * ‖vK f α β s x xstar k‖ ^ 2 := by positivity
      linarith
    have hK2 : (2:ℝ) ≤ k := by exact_mod_cast hk2
    have hKpos : (0:ℝ) < k := by linarith
    have htk : tK α k * (α - 1) = (k : ℝ) - 1 := by
      unfold tK; field_simp
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hF,
      abs_of_pos (div_pos one_pos (pow_pos hKpos 2))]
    rw [mul_one_div, le_div_iff₀ (pow_pos hKpos 2)]
    have h1 : ((k : ℝ) - 1) ^ 2 * (f (x k) - f xstar)
        ≤ EK f α β s x xstar k₀ * (α - 1) ^ 2 := by
      rw [← htk]
      have := mul_le_mul_of_nonneg_left (le_trans hle hEk) (sq_nonneg (α - 1))
      linarith
    have h2 : (k : ℝ) ^ 2 ≤ 4 * ((k : ℝ) - 1) ^ 2 := by nlinarith
    have h3 := mul_le_mul_of_nonneg_right h2 hF
    linarith
  · intro hβ
    have hε := hεpos hβ
    have hC : 0 ≤ (α - 1) ^ 2 / ε := by positivity
    have key : ∀ k, k₀ ≤ k → (k : ℝ) ^ 2 * (‖gradient f (y k)‖ ^ 2 + ‖gradient f (x k)‖ ^ 2)
        ≤ (α - 1) ^ 2 / ε * (EK f α β s x xstar k - EK f α β s x xstar (k + 1)) := by
      intro k hk
      have h1 := hdec k hk
      have hτ : (k : ℝ) = (α - 1) * tK α (k + 1) := by
        rw [IGAHD6Aux.tK_succ]; field_simp
      have e : (k : ℝ) ^ 2 * (‖gradient f (y k)‖ ^ 2 + ‖gradient f (x k)‖ ^ 2)
          = (α - 1) ^ 2 / ε * (ε * tK α (k + 1) ^ 2
            * (‖gradient f (y k)‖ ^ 2 + ‖gradient f (x k)‖ ^ 2)) := by
        rw [hτ]; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) hC
    constructor
    · refine IGAHD6Aux.summable_tele (fun k => (k : ℝ) ^ 2 * ‖gradient f (y k)‖ ^ 2)
        (EK f α β s x xstar) k₀ ((α - 1) ^ 2 / ε) hC (fun n => by positivity) hEnn ?_
      intro n hn
      have h1 := key n hn
      have h2 : 0 ≤ (n : ℝ) ^ 2 * ‖gradient f (x n)‖ ^ 2 := by positivity
      linarith
    · refine IGAHD6Aux.summable_tele (fun k => (k : ℝ) ^ 2 * ‖gradient f (x k)‖ ^ 2)
        (EK f α β s x xstar) k₀ ((α - 1) ^ 2 / ε) hC (fun n => by positivity) hEnn ?_
      intro n hn
      have h1 := key n hn
      have h2 : 0 ≤ (n : ℝ) ^ 2 * ‖gradient f (y n)‖ ^ 2 := by positivity
      linarith
