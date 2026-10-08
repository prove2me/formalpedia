-- Prove2me | solution 1 for NesterovFB.Weak.dist_succ_le_dist_extrap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T12:46:42.224718+00:00
-- url     : https://prove2.me/submissions/ce4cbc5b-00b4-4e82-966e-e59d5b525c05

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Weak_Algorithm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

open Filter Topology NNReal InnerProductSpace

open scoped RealInnerProductSpace in
theorem nfb14_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem nfb14_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [nfb14_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem nfb14_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := nfb14_line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
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

open scoped RealInnerProductSpace in
theorem nfb14_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) : f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • w)) := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => f (x + t • w)) = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using nfb14_line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [nfb14_inner_grad]
  linarith

-- Strong prox inequality from the bare minimiser property plus convexity of `Ψ`.
open scoped RealInnerProductSpace in
theorem nfb14_prox_strong {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Ψ : H → EReal} {s : ℝ} {P : H → H} (hs : 0 < s)
    (hconv : Convex ℝ {q : H × ℝ | Ψ q.1 ≤ (q.2 : EReal)})
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P) (w z p : H) (hpw : P w = p) (a b : ℝ)
    (ha : Ψ p = a) (hb : Ψ z = b) :
    a ≤ b + ⟪p - w, z - p⟫ / s := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      a ≤ b + ⟪p - w, z - p⟫ / s + t * ‖z - p‖ ^ 2 / (2 * s) := by
    intro t ht0 ht1
    have hmem : ((1 - t) • ((p, a) : H × ℝ) + t • ((z, b) : H × ℝ)) ∈
        {q : H × ℝ | Ψ q.1 ≤ (q.2 : EReal)} :=
      hconv (by simp [ha]) (by simp [hb]) (by linarith) ht0.le (by ring)
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hmem
    have hpr := hP w ((1 - t) • p + t • z)
    rw [hpw, ha] at hpr
    have h2 := add_le_add hmem (le_refl ((‖(1 - t) • p + t • z - w‖ ^ 2 / (2 * s) : ℝ) : EReal))
    have h3 := hpr.trans h2
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    have hvec : (1 - t) • p + t • z - w = (p - w) + t • (z - p) := by module
    rw [hvec, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0] at h3
    have e : (‖p - w‖ ^ 2 + 2 * (t * ⟪p - w, z - p⟫) + (t * ‖z - p‖) ^ 2) / (2 * s)
        = ‖p - w‖ ^ 2 / (2 * s) + t * (⟪p - w, z - p⟫ / s + t * ‖z - p‖ ^ 2 / (2 * s)) := by
      field_simp
      ring
    rw [e] at h3
    have h4 : t * a ≤ t * (b + ⟪p - w, z - p⟫ / s + t * ‖z - p‖ ^ 2 / (2 * s)) := by
      nlinarith
    exact le_of_mul_le_mul_left h4 ht0
  apply le_of_forall_pos_le_add
  intro ε hε
  have hc : 0 ≤ ‖z - p‖ ^ 2 := by positivity
  obtain ⟨t, ht0, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t ≤ ε * s / (‖z - p‖ ^ 2 + 1) :=
    ⟨min 1 (ε * s / (‖z - p‖ ^ 2 + 1)), lt_min one_pos (by positivity), min_le_left _ _,
      min_le_right _ _⟩
  have h := key t ht0 ht1
  have h5 : t * (‖z - p‖ ^ 2 + 1) ≤ ε * s := (le_div_iff₀ (by positivity)).mp ht2
  have hes : 0 < ε * s := mul_pos hε hs
  have h6 : t * ‖z - p‖ ^ 2 / (2 * s) ≤ ε := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

-- The real-valued core of the one-step estimate.
open scoped RealInnerProductSpace in
theorem nfb14_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψp Ψz Φp Φy Φz s L : ℝ) (y p z g : H) (hs : 0 < s) (hL0 : 0 ≤ L) (hsL : s * L < 1)
    (hA : Ψp ≤ Ψz + ⟪p - (y - s • g), z - p⟫ / s)
    (hB : Φp ≤ Φy + ⟪g, p - y⟫ + L / 2 * ‖p - y‖ ^ 2)
    (hC : Φy + ⟪g, z - y⟫ ≤ Φz) :
    Ψp + Φp + 1 / (2 * s) * ‖p - z‖ ^ 2 ≤ Ψz + Φz + 1 / (2 * s) * ‖y - z‖ ^ 2 := by
  have e1 : p - (y - s • g) = (p - y) + s • g := by module
  rw [e1, inner_add_left, real_inner_smul_left] at hA
  have e1' : (⟪p - y, z - p⟫ + s * ⟪g, z - p⟫) / s = ⟪p - y, z - p⟫ / s + ⟪g, z - p⟫ := by
    rw [add_div, mul_div_cancel_left₀ _ hs.ne']
  rw [e1'] at hA
  have e2 : z - y = (p - y) + (z - p) := by abel
  rw [e2, inner_add_right] at hC
  have e3 : y - z = -((p - y) + (z - p)) := by abel
  rw [e3, norm_neg, norm_add_sq_real, norm_sub_rev p z]
  have key : L / 2 * ‖p - y‖ ^ 2 ≤ ‖p - y‖ ^ 2 / (2 * s) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_nonneg (sub_nonneg.2 hsL.le) (sq_nonneg ‖p - y‖)
    nlinarith
  have hfin : 1 / (2 * s) * (‖p - y‖ ^ 2 + 2 * ⟪p - y, z - p⟫ + ‖z - p‖ ^ 2)
      = ‖p - y‖ ^ 2 / (2 * s) + ⟪p - y, z - p⟫ / s + 1 / (2 * s) * ‖z - p‖ ^ 2 := by
    field_simp
  rw [hfin]
  linarith

open NNReal in
theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : ℝ≥0) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * (L : ℝ) < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hα : 3 < α)
    (hrun : NesterovFB.Rates.IsAccelFBRun Φ P α s x)
    (xstar : H) (hxstar : ∀ y, NesterovFB.Rates.theta Ψ Φ xstar ≤ NesterovFB.Rates.theta Ψ Φ y) :
    ∀ k : ℕ, 1 ≤ k → ‖x (k + 1) - xstar‖ ^ 2 ≤ ‖NesterovFB.Rates.extrap α x k - xstar‖ ^ 2 := by
  intro k hk
  obtain ⟨hbot, ⟨x0, hx0⟩, -, hconv⟩ := hΨ
  have hdiff : Differentiable ℝ Φ := hΦd.differentiable one_ne_zero
  have hgrad : ∀ a b, ‖gradient Φ a - gradient Φ b‖ ≤ (L : ℝ) * ‖a - b‖ :=
    fun a b => hL.norm_sub_le a b
  set y := NesterovFB.Rates.extrap α x k with hy
  have hxp : P (y - s • gradient Φ y) = x (k + 1) := (hrun k hk).symm
  have htop : Ψ xstar ≠ ⊤ := by
    intro h
    have h1 := hxstar x0
    unfold NesterovFB.Rates.theta at h1
    rw [h, EReal.top_add_coe, top_le_iff] at h1
    obtain ⟨c, hc⟩ : ∃ c : ℝ, Ψ x0 = c :=
      ⟨(Ψ x0).toReal, (EReal.coe_toReal hx0 (hbot x0)).symm⟩
    rw [hc, ← EReal.coe_add] at h1
    exact EReal.coe_ne_top _ h1
  obtain ⟨b, hb⟩ : ∃ b : ℝ, Ψ xstar = b :=
    ⟨(Ψ xstar).toReal, (EReal.coe_toReal htop (hbot xstar)).symm⟩
  have hptop : Ψ (x (k + 1)) ≠ ⊤ := by
    intro h
    have := hP (y - s • gradient Φ y) xstar
    rw [hxp, h, hb, EReal.top_add_coe, ← EReal.coe_add] at this
    exact EReal.coe_ne_top _ (top_le_iff.mp this)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, Ψ (x (k + 1)) = a :=
    ⟨(Ψ (x (k + 1))).toReal, (EReal.coe_toReal hptop (hbot (x (k + 1)))).symm⟩
  have hA := nfb14_prox_strong hs hconv hP _ xstar (x (k + 1)) hxp a b ha hb
  have hB := nfb14_descent hdiff hgrad y (x (k + 1))
  have hC := nfb14_convex_fo hΦc hdiff y xstar
  have hcore := nfb14_core a b (Φ (x (k + 1))) (Φ y) (Φ xstar) s (L : ℝ)
    y (x (k + 1)) xstar (gradient Φ y) hs L.2 hsL hA hB hC
  have hmin := hxstar (x (k + 1))
  unfold NesterovFB.Rates.theta at hmin
  rw [ha, hb, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hmin
  have hq : 0 < 1 / (2 * s) := by positivity
  have : 1 / (2 * s) * ‖x (k + 1) - xstar‖ ^ 2 ≤ 1 / (2 * s) * ‖y - xstar‖ ^ 2 := by linarith
  exact le_of_mul_le_mul_left this hq
