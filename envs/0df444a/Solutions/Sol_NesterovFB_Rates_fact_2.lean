-- Prove2me | solution 1 for NesterovFB.Rates.fact_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:23:25.448107+00:00
-- url     : https://prove2.me/submissions/7f0431a2-6954-4d3d-aee0-5f4f2d893e87

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

open Filter Topology InnerProductSpace

open scoped RealInnerProductSpace in
theorem nfbf2_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem nfbf2_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [nfbf2_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem nfbf2_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := nfbf2_line_deriv hdiff x w t
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
theorem nfbf2_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (by simpa using nfbf2_line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [nfbf2_inner_grad]
  linarith

-- Strong prox inequality from the bare minimiser property plus convexity of `Ψ`.
open scoped RealInnerProductSpace in
theorem nfbf2_prox_strong {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
theorem nfbf2_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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


theorem nfbf2_real_step (s α kk A B N0 N1 : ℝ) (hs : 0 < s) (hα : 3 ≤ α) (hk : 1 ≤ kk)
    (hB : 0 ≤ B)
    (h : A + 1 / (2 * s) * (((α - 1) / (kk + α - 1)) ^ 2 * N1)
      ≤ (1 - (α - 1) / (kk + α - 1)) * B + 1 / (2 * s) * (((α - 1) / (kk + α - 1)) ^ 2 * N0)) :
    2 * s / (α - 1) * (kk + 1 + α - 2) ^ 2 * A + (α - 1) * N1
      ≤ 2 * s / (α - 1) * (kk + α - 2) ^ 2 * B + (α - 1) * N0 := by
  have hα1 : 0 < α - 1 := by linarith
  have hD : 0 < kk + α - 1 := by linarith
  have hM : 0 ≤ 2 * s * (kk + α - 1) ^ 2 / (α - 1) := by positivity
  have hm := mul_le_mul_of_nonneg_left h hM
  have e1 : 2 * s * (kk + α - 1) ^ 2 / (α - 1) *
      (A + 1 / (2 * s) * (((α - 1) / (kk + α - 1)) ^ 2 * N1))
      = 2 * s / (α - 1) * (kk + 1 + α - 2) ^ 2 * A + (α - 1) * N1 := by
    field_simp
    ring
  have e2 : 2 * s * (kk + α - 1) ^ 2 / (α - 1) *
      ((1 - (α - 1) / (kk + α - 1)) * B + 1 / (2 * s) * (((α - 1) / (kk + α - 1)) ^ 2 * N0))
      = 1 / (α - 1) * (2 * s * kk * (kk + α - 1) * B) + (α - 1) * N0 := by
    field_simp
    ring
  rw [e1, e2] at hm
  have hq : 0 < 1 / (α - 1) := one_div_pos.mpr hα1
  have hk0 : 0 ≤ kk := by linarith
  have hpoly : 2 * s * kk * (kk + α - 1) ≤ 2 * s * (kk + α - 2) ^ 2 := by
    nlinarith [mul_nonneg hs.le (mul_nonneg hk0 (by linarith : (0:ℝ) ≤ α - 3)),
      mul_nonneg hs.le (sq_nonneg (α - 2))]
  have h3 : 2 * s * kk * (kk + α - 1) * B ≤ 2 * s * (kk + α - 2) ^ 2 * B :=
    mul_le_mul_of_nonneg_right hpoly hB
  have h4 := mul_le_mul_of_nonneg_left h3 hq.le
  have e3 : 1 / (α - 1) * (2 * s * (kk + α - 2) ^ 2 * B) = 2 * s / (α - 1) * (kk + α - 2) ^ 2 * B := by
    ring
  linarith

theorem nfbf2_vec1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x : ℕ → H) (xs : H) (k : ℕ) (hα : 3 ≤ α) :
    x (k + 1) - ((1 - (α - 1) / ((k : ℝ) + α - 1)) • x k + ((α - 1) / ((k : ℝ) + α - 1)) • xs)
      = ((α - 1) / ((k : ℝ) + α - 1)) • (NesterovFB.Rates.zSeq α x (k + 1) - xs) := by
  have hα1 : α - 1 ≠ 0 := by intro h; linarith
  have hD : (k : ℝ) + α - 1 ≠ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    intro h; linarith
  simp only [NesterovFB.Rates.zSeq, Nat.add_sub_cancel]
  push_cast
  match_scalars <;> field_simp <;> ring

theorem nfbf2_vec0 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x : ℕ → H) (xs : H) (k : ℕ) (hα : 3 ≤ α) :
    NesterovFB.Rates.extrap α x k
      - ((1 - (α - 1) / ((k : ℝ) + α - 1)) • x k + ((α - 1) / ((k : ℝ) + α - 1)) • xs)
      = ((α - 1) / ((k : ℝ) + α - 1)) • (NesterovFB.Rates.zSeq α x k - xs) := by
  have hα1 : α - 1 ≠ 0 := by intro h; linarith
  have hD : (k : ℝ) + α - 1 ≠ 0 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    intro h; linarith
  simp only [NesterovFB.Rates.zSeq, NesterovFB.Rates.extrap]
  match_scalars <;> field_simp <;> ring

open NesterovFB.Rates in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Ψ : H → EReal) (Φ : H → ℝ) (L : NNReal) (s α : ℝ) (P : H → H) (x : ℕ → H)
    (hΨ : ThreeOpSplitting.ConvexRates.IsProperClosedConvex Ψ)
    (hΦc : ConvexOn ℝ Set.univ Φ) (hΦd : ContDiff ℝ 1 Φ)
    (hL : LipschitzWith L (gradient Φ))
    (hs : 0 < s) (hsL : s * L < 1)
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P)
    (hrun : IsAccelFBRun Φ P α s x)
    (hα : 3 ≤ α)
    (xstar : H) (hxstar : ∀ y, theta Ψ Φ xstar ≤ theta Ψ Φ y) :
    ∀ k : ℕ, 1 ≤ k →
      theta Ψ Φ (x k) - theta Ψ Φ xstar
          ≤ (((α - 1) / (2 * s * ((k : ℝ) + α - 2) ^ 2) : ℝ) : EReal) * energy Ψ Φ α s x xstar 1 ∧
        ((‖zSeq α x k - xstar‖ ^ 2 : ℝ) : EReal) ≤ ((1 / (α - 1) : ℝ) : EReal) * energy Ψ Φ α s x xstar 1 := by
  intro k hk
  obtain ⟨hbot, ⟨y0, hy0⟩, -, hconv⟩ := hΨ
  have hα1 : 0 < α - 1 := by linarith
  have hdiff : Differentiable ℝ Φ := hΦd.differentiable one_ne_zero
  have hgrad : ∀ a b, ‖gradient Φ a - gradient Φ b‖ ≤ (L : ℝ) * ‖a - b‖ :=
    fun a b => hL.norm_sub_le a b
  -- Ψ x* is finite
  have hstop : Ψ xstar ≠ ⊤ := by
    intro h
    have h1 := hxstar y0
    have h2 : theta Ψ Φ xstar = ⊤ := by
      show Ψ xstar + ((Φ xstar : ℝ) : EReal) = ⊤
      rw [h, EReal.top_add_coe]
    rw [h2, top_le_iff] at h1
    obtain ⟨c, hc⟩ : ∃ c : ℝ, Ψ y0 = c := ⟨(Ψ y0).toReal, (EReal.coe_toReal hy0 (hbot y0)).symm⟩
    have : theta Ψ Φ y0 = ((c + Φ y0 : ℝ) : EReal) := by
      show Ψ y0 + ((Φ y0 : ℝ) : EReal) = _
      rw [hc, EReal.coe_add]
    rw [this] at h1
    exact EReal.coe_ne_top _ h1
  set b : ℝ := (Ψ xstar).toReal with hbdef
  have hb : Ψ xstar = (b : EReal) := (EReal.coe_toReal hstop (hbot xstar)).symm
  have hths : theta Ψ Φ xstar = ((b + Φ xstar : ℝ) : EReal) := by
    show Ψ xstar + ((Φ xstar : ℝ) : EReal) = _
    rw [hb, EReal.coe_add]
  by_cases h1top : Ψ (x 1) = ⊤
  · -- energy 1 = ⊤
    have hc1 : 0 < 2 * s / (α - 1) * (((1 : ℕ) : ℝ) + α - 2) ^ 2 := by
      have : 0 < ((1 : ℕ) : ℝ) + α - 2 := by push_cast; linarith
      positivity
    have hE : energy Ψ Φ α s x xstar 1 = ⊤ := by
      have ht1 : theta Ψ Φ (x 1) = ⊤ := by
        show Ψ (x 1) + ((Φ (x 1) : ℝ) : EReal) = ⊤
        rw [h1top, EReal.top_add_coe]
      simp only [energy]
      rw [ht1, hths, EReal.top_sub_coe, EReal.coe_mul_top_of_pos hc1, EReal.top_add_coe]
    rw [hE]
    have hp1 : 0 < (α - 1) / (2 * s * ((k : ℝ) + α - 2) ^ 2) := by
      have : 0 < (k : ℝ) + α - 2 := by
        have : (1 : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      positivity
    have hp2 : 0 < 1 / (α - 1) := one_div_pos.mpr hα1
    rw [EReal.coe_mul_top_of_pos hp1, EReal.coe_mul_top_of_pos hp2]
    exact ⟨le_top, le_top⟩
  -- every iterate from 1 on has finite Ψ
  have hfin : ∀ j : ℕ, 1 ≤ j → Ψ (x j) ≠ ⊤ := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have : j = 1 := by omega
      subst this; exact h1top
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hxp : P (extrap α x i - s • gradient Φ (extrap α x i)) = x (i + 1) :=
        (hrun i (by omega)).symm
      intro h
      have := hP (extrap α x i - s • gradient Φ (extrap α x i)) xstar
      rw [hxp, h, hb, EReal.top_add_coe, ← EReal.coe_add] at this
      exact EReal.coe_ne_top _ (top_le_iff.mp this)
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ j, 1 ≤ j → Ψ (x j) = (a j : EReal) :=
    ⟨fun j => (Ψ (x j)).toReal, fun j hj => (EReal.coe_toReal (hfin j hj) (hbot _)).symm⟩
  have htheta : ∀ j, 1 ≤ j → theta Ψ Φ (x j) = ((a j + Φ (x j) : ℝ) : EReal) := by
    intro j hj
    show Ψ (x j) + ((Φ (x j) : ℝ) : EReal) = _
    rw [ha j hj, EReal.coe_add]
  have hmin : ∀ j, 1 ≤ j → b + Φ xstar ≤ a j + Φ (x j) := by
    intro j hj
    have := hxstar (x j)
    rw [hths, htheta j hj, EReal.coe_le_coe_iff] at this
    exact this
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ j, e j = 2 * s / (α - 1) * ((j : ℝ) + α - 2) ^ 2
      * ((a j + Φ (x j)) - (b + Φ xstar)) + (α - 1) * ‖zSeq α x j - xstar‖ ^ 2 :=
    ⟨_, fun j => rfl⟩
  have hEe : ∀ j, 1 ≤ j → energy Ψ Φ α s x xstar j = ((e j : ℝ) : EReal) := by
    intro j hj
    simp only [energy]
    rw [htheta j hj, hths, he j, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add]
  -- one step of the energy
  have hstep : ∀ j, 1 ≤ j → e (j + 1) ≤ e j := by
    intro j hj
    have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    set l : ℝ := (α - 1) / ((j : ℝ) + α - 1) with hl
    have hD : 0 < (j : ℝ) + α - 1 := by linarith
    have hl0 : 0 < l := div_pos hα1 hD
    have hl1 : l ≤ 1 := by rw [hl, div_le_one hD]; linarith
    set z : H := (1 - l) • x j + l • xstar with hz
    have hmem : ((1 - l) • ((x j, a j) : H × ℝ) + l • ((xstar, b) : H × ℝ)) ∈
        {q : H × ℝ | Ψ q.1 ≤ (q.2 : EReal)} :=
      hconv (by simp [ha j hj]) (by simp [hb]) (sub_nonneg.2 hl1) hl0.le (by ring)
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hmem
    have hzt : Ψ z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hmem
    obtain ⟨c, hc⟩ : ∃ c : ℝ, Ψ z = c := ⟨(Ψ z).toReal, (EReal.coe_toReal hzt (hbot z)).symm⟩
    have hcle : c ≤ (1 - l) * a j + l * b := by
      have := hmem
      rw [← hz, hc, EReal.coe_le_coe_iff] at this
      exact this
    have hΦz : Φ z ≤ (1 - l) * Φ (x j) + l * Φ xstar := by
      have := hΦc.2 (Set.mem_univ (x j)) (Set.mem_univ xstar) (sub_nonneg.2 hl1) hl0.le (by ring)
      simpa [smul_eq_mul] using this
    have hxp : P (extrap α x j - s • gradient Φ (extrap α x j)) = x (j + 1) := (hrun j hj).symm
    have hA := nfbf2_prox_strong hs hconv hP _ z (x (j + 1)) hxp (a (j + 1)) c
      (ha (j + 1) (by omega)) hc
    have hB := nfbf2_descent hdiff hgrad (extrap α x j) (x (j + 1))
    have hC := nfbf2_convex_fo hΦc hdiff (extrap α x j) z
    have hcore := nfbf2_core (a (j + 1)) c (Φ (x (j + 1))) (Φ (extrap α x j)) (Φ z) s (L : ℝ)
      (extrap α x j) (x (j + 1)) z (gradient Φ (extrap α x j)) hs L.2 hsL hA hB hC
    have hv1 := nfbf2_vec1 α x xstar j hα
    have hv0 := nfbf2_vec0 α x xstar j hα
    rw [← hl, ← hz] at hv1 hv0
    rw [hv1, hv0] at hcore
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hcore
    have hBnn : 0 ≤ (a j + Φ (x j)) - (b + Φ xstar) := sub_nonneg.2 (hmin j hj)
    have hreal := nfbf2_real_step s α (j : ℝ) ((a (j + 1) + Φ (x (j + 1))) - (b + Φ xstar))
      ((a j + Φ (x j)) - (b + Φ xstar)) (‖zSeq α x j - xstar‖ ^ 2)
      (‖zSeq α x (j + 1) - xstar‖ ^ 2) hs hα hjR hBnn (by rw [← hl]; linarith)
    rw [he, he]
    push_cast
    linarith
  have hmono : ∀ j, 1 ≤ j → e j ≤ e 1 := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hstep n hn).trans ih
  have hk1 := hmono k hk
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hBnn : 0 ≤ (a k + Φ (x k)) - (b + Φ xstar) := sub_nonneg.2 (hmin k hk)
  rw [he] at hk1
  rw [hEe 1 le_rfl, htheta k hk, hths, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul,
    EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
  have hN : 0 ≤ ‖zSeq α x k - xstar‖ ^ 2 := by positivity
  have hck : 0 < 2 * s / (α - 1) * ((k : ℝ) + α - 2) ^ 2 := by
    have : 0 < (k : ℝ) + α - 2 := by linarith
    positivity
  constructor
  · have h1 : 2 * s / (α - 1) * ((k : ℝ) + α - 2) ^ 2 * ((a k + Φ (x k)) - (b + Φ xstar)) ≤ e 1 := by
      nlinarith [mul_nonneg hα1.le hN]
    have e4 : (α - 1) / (2 * s * ((k : ℝ) + α - 2) ^ 2) = 1 / (2 * s / (α - 1) * ((k : ℝ) + α - 2) ^ 2) := by
      field_simp
    rw [e4, one_div_mul_eq_div, le_div_iff₀ hck]
    linarith
  · have h2 : (α - 1) * ‖zSeq α x k - xstar‖ ^ 2 ≤ e 1 := by
      nlinarith [mul_nonneg hck.le hBnn]
    rw [one_div_mul_eq_div, le_div_iff₀ hα1]
    linarith
