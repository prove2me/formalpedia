-- Prove2me | solution 1 for NesterovFB.Rates.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T10:56:03.157082+00:00
-- url     : https://prove2.me/submissions/f1db38dc-db22-4abc-8585-4e16eb87bea8

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_NesterovFB_Rates_Algorithm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.deprecated false

open Filter Topology InnerProductSpace

open scoped RealInnerProductSpace in
theorem nfb1_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem nfb1_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [nfb1_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem nfb1_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := nfb1_line_deriv hdiff x w t
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
theorem nfb1_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
    (by simpa using nfb1_line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [nfb1_inner_grad]
  linarith

-- Strong prox inequality from the bare minimiser property plus convexity of `Ψ`.
open scoped RealInnerProductSpace in
theorem nfb1_prox_strong {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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
theorem nfb1_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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

-- One forward-backward step: Θ(p) ≤ Θ(z) + ⟪y - p, y - z⟫/s - ‖y - p‖²/(2s).
open scoped RealInnerProductSpace in
theorem nfb1_onestep {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Ψ : H → EReal} {Φ : H → ℝ} {s L : ℝ} {P : H → H} (hs : 0 < s)
    (hL0 : 0 ≤ L) (hsL : s * L < 1)
    (hconv : Convex ℝ {q : H × ℝ | Ψ q.1 ≤ (q.2 : EReal)})
    (hP : ThreeOpSplitting.ConvexRates.IsProx s Ψ P) (hΦc : ConvexOn ℝ Set.univ Φ)
    (hdiff : Differentiable ℝ Φ)
    (hgrad : ∀ a b, ‖gradient Φ a - gradient Φ b‖ ≤ L * ‖a - b‖)
    (y z p : H) (hp : P (y - s • gradient Φ y) = p) (a b : ℝ) (ha : Ψ p = a) (hb : Ψ z = b) :
    a + Φ p ≤ b + Φ z + ⟪y - p, y - z⟫ / s - ‖y - p‖ ^ 2 / (2 * s) := by
  set g := gradient Φ y with hg
  have hA := nfb1_prox_strong hs hconv hP (y - s • g) z p hp a b ha hb
  have hB := nfb1_descent hdiff hgrad y p
  have hC := nfb1_convex_fo hΦc hdiff y z
  rw [← hg] at hB hC
  have v1 : p - (y - s • g) = s • g - (y - p) := by abel
  have v2 : z - p = (z - y) + (y - p) := by abel
  have v3 : p - y = -(y - p) := by abel
  have v4 : y - z = -(z - y) := by abel
  rw [v1, v2] at hA
  rw [v3] at hB
  rw [v4]
  clear_value g
  generalize y - p = d at hA hB ⊢
  generalize z - y = e at hA hC ⊢
  rw [inner_add_right, inner_sub_left, inner_sub_left, real_inner_smul_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq] at hA
  rw [inner_neg_right, norm_neg] at hB
  rw [inner_neg_right]
  have hA' : s * a ≤ s * b + (s * ⟪g, e⟫ - ⟪d, e⟫ + (s * ⟪g, d⟫ - ‖d‖ ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hA hs.le
    rwa [mul_add, mul_div_cancel₀ _ hs.ne'] at this
  have key : L / 2 * ‖d‖ ^ 2 ≤ ‖d‖ ^ 2 / (2 * s) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_nonneg (sub_nonneg.2 hsL.le) (sq_nonneg ‖d‖)
    nlinarith
  have hcomm : ⟪g, d⟫ = ⟪d, g⟫ := real_inner_comm _ _
  have hkey2 : s * (L / 2 * ‖d‖ ^ 2) ≤ ‖d‖ ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_left key hs.le
    rwa [show s * (‖d‖ ^ 2 / (2 * s)) = ‖d‖ ^ 2 / 2 by field_simp] at this
  rw [← sub_nonneg]
  have e5 : b + Φ z + -⟪d, e⟫ / s - ‖d‖ ^ 2 / (2 * s) - (a + Φ p)
      = (s * b + s * Φ z - ⟪d, e⟫ - ‖d‖ ^ 2 / 2 - s * (a + Φ p)) / s := by
    field_simp
    ring
  rw [e5]
  apply div_nonneg _ hs.le
  have hB' := mul_le_mul_of_nonneg_left hB hs.le
  have hC' := mul_le_mul_of_nonneg_left hC hs.le
  nlinarith

-- The scalar Lyapunov computation.
theorem nfb1_alg (s α k T0 T1 Ts P1 P2 Q D N N1 : ℝ) (hs : 0 < s) (hα : 3 ≤ α) (hk : 1 ≤ k)
    (hT : Ts ≤ T0) (hD : 0 ≤ D)
    (I1 : T1 ≤ T0 + P1 / s - D / (2 * s)) (I2 : T1 ≤ Ts + P2 / s - D / (2 * s))
    (hP : k * P1 + (α - 1) * P2 = (α - 1) * Q)
    (hN : N1 = N - 2 * ((k + α - 1) / (α - 1)) * Q + ((k + α - 1) / (α - 1)) ^ 2 * D) :
    2 * s / (α - 1) * (k + 1 + α - 2) ^ 2 * (T1 - Ts) + (α - 1) * N1
      ≤ 2 * s / (α - 1) * (k + α - 2) ^ 2 * (T0 - Ts) + (α - 1) * N := by
  have hm : 0 < α - 1 := by linarith
  have I1s : s * T1 ≤ s * T0 + P1 - D / 2 := by
    have := mul_le_mul_of_nonneg_left I1 hs.le
    rwa [show s * (T0 + P1 / s - D / (2 * s)) = s * T0 + P1 - D / 2 by field_simp] at this
  have I2s : s * T1 ≤ s * Ts + P2 - D / 2 := by
    have := mul_le_mul_of_nonneg_left I2 hs.le
    rwa [show s * (Ts + P2 / s - D / (2 * s)) = s * Ts + P2 - D / 2 by field_simp] at this
  have hk0 : 0 ≤ k := by linarith
  have J1 := mul_le_mul_of_nonneg_left I1s hk0
  have J2 := mul_le_mul_of_nonneg_left I2s hm.le
  -- J : (k+m) s T1 ≤ k s T0 + m s Ts + m Q - (k+m) D/2
  have J : (k + α - 1) * (s * T1) ≤ k * (s * T0) + (α - 1) * (s * Ts) + (α - 1) * Q
      - (k + α - 1) * D / 2 := by nlinarith
  have hc : 0 < k + α - 1 := by linarith
  have J' := mul_le_mul_of_nonneg_left J (by linarith : (0:ℝ) ≤ 2 * (k + α - 1))
  have hck : (k + α - 1) * k ≤ (k + α - 2) ^ 2 := by nlinarith
  have hsT : 0 ≤ s * (T0 - Ts) := mul_nonneg hs.le (by linarith)
  have hfin := mul_le_mul_of_nonneg_right hck hsT
  have eL : 2 * s / (α - 1) * (k + 1 + α - 2) ^ 2 * (T1 - Ts) + (α - 1) * N1
      = (2 * s * (k + α - 1) ^ 2 * (T1 - Ts) + (α - 1) ^ 2 * N
          - 2 * (k + α - 1) * (α - 1) * Q + (k + α - 1) ^ 2 * D) / (α - 1) := by
    rw [hN]; field_simp; ring
  have eR : 2 * s / (α - 1) * (k + α - 2) ^ 2 * (T0 - Ts) + (α - 1) * N
      = (2 * s * (k + α - 2) ^ 2 * (T0 - Ts) + (α - 1) ^ 2 * N) / (α - 1) := by
    field_simp
  rw [eL, eR]
  apply div_le_div_of_nonneg_right _ hm.le
  nlinarith

open scoped RealInnerProductSpace in
theorem nfb1_V1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x : ℕ → H) (xstar : H) (k : ℕ) (hα : 3 ≤ α) (hk : 1 ≤ k) :
    (k : ℝ) • (NesterovFB.Rates.extrap α x k - x k) + (α - 1) • (NesterovFB.Rates.extrap α x k - xstar)
      = (α - 1) • (NesterovFB.Rates.zSeq α x k - xstar) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (k : ℝ) + α - 1 ≠ 0 := by linarith
  have h2 : α - 1 ≠ 0 := by linarith
  simp only [NesterovFB.Rates.extrap, NesterovFB.Rates.zSeq]
  match_scalars <;> field_simp <;> ring

open scoped RealInnerProductSpace in
theorem nfb1_V2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (α : ℝ) (x : ℕ → H) (xstar : H) (k : ℕ) (hα : 3 ≤ α) (hk : 1 ≤ k) :
    NesterovFB.Rates.zSeq α x (k + 1) - xstar
      = (NesterovFB.Rates.zSeq α x k - xstar)
        - (((k : ℝ) + α - 1) / (α - 1)) • (NesterovFB.Rates.extrap α x k - x (k + 1)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : (k : ℝ) + α - 1 ≠ 0 := by linarith
  have h2 : α - 1 ≠ 0 := by linarith
  simp only [NesterovFB.Rates.extrap, NesterovFB.Rates.zSeq, Nat.add_sub_cancel]
  push_cast
  match_scalars <;> field_simp <;> ring

open NesterovFB.Rates Filter Topology InnerProductSpace RealInnerProductSpace in
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
    (∀ k : ℕ, 1 ≤ k → energy Ψ Φ α s x xstar (k + 1) ≤ energy Ψ Φ α s x xstar k) ∧
      ∃ l : ℝ, Tendsto (fun k : ℕ => energy Ψ Φ α s x xstar k) atTop (𝓝 (l : EReal)) := by
  obtain ⟨hbot, ⟨x0, hx0⟩, -, hconv⟩ := hΨ
  have hdiff : Differentiable ℝ Φ := hΦd.differentiable one_ne_zero
  have hgrad : ∀ a b, ‖gradient Φ a - gradient Φ b‖ ≤ (L : ℝ) * ‖a - b‖ :=
    fun a b => hL.norm_sub_le a b
  have fin_of : ∀ z, Ψ z ≠ ⊤ → Ψ z = ((Ψ z).toReal : EReal) :=
    fun z hz => (EReal.coe_toReal hz (hbot z)).symm
  have hstar_ne : Ψ xstar ≠ ⊤ := by
    intro h
    have h1 := hxstar x0
    simp only [theta] at h1
    rw [h, EReal.top_add_coe, fin_of x0 hx0, ← EReal.coe_add, top_le_iff] at h1
    exact EReal.coe_ne_top _ h1
  have hnext : ∀ k, 1 ≤ k → Ψ (x (k + 1)) ≠ ⊤ := by
    intro k hk h
    have h1 := hP (extrap α x k - s • gradient Φ (extrap α x k)) x0
    rw [← hrun k hk, h, EReal.top_add_coe, fin_of x0 hx0, ← EReal.coe_add, top_le_iff] at h1
    exact EReal.coe_ne_top _ h1
  set T : ℕ → ℝ := fun k => (Ψ (x k)).toReal + Φ (x k) with hTdef
  set Ts : ℝ := (Ψ xstar).toReal + Φ xstar with hTsdef
  set f : ℕ → ℝ := fun k => 2 * s / (α - 1) * ((k : ℝ) + α - 2) ^ 2 * (T k - Ts)
    + (α - 1) * ‖zSeq α x k - xstar‖ ^ 2 with hfdef
  have hE : ∀ k, Ψ (x k) ≠ ⊤ → energy Ψ Φ α s x xstar k = (f k : EReal) := by
    intro k hk
    simp only [energy, theta, hfdef, hTdef, hTsdef]
    rw [fin_of _ hk, fin_of _ hstar_ne]
    norm_cast
  have hTs : ∀ k, Ψ (x k) ≠ ⊤ → Ts ≤ T k := by
    intro k hk
    have h1 := hxstar (x k)
    simp only [theta] at h1
    rw [fin_of _ hk, fin_of _ hstar_ne] at h1
    norm_cast at h1
  have hEtop : ∀ k, 1 ≤ k → Ψ (x k) = ⊤ → energy Ψ Φ α s x xstar k = ⊤ := by
    intro k hk h
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hr : 0 < 2 * s / (α - 1) * ((k : ℝ) + α - 2) ^ 2 := by
      have : 0 < α - 1 := by linarith
      have : 0 < (k : ℝ) + α - 2 := by linarith
      positivity
    simp only [energy, theta]
    rw [h, EReal.top_add_coe, fin_of _ hstar_ne, ← EReal.coe_add, EReal.top_sub_coe,
      EReal.coe_mul_top_of_pos hr, EReal.top_add_coe]
  have hstep : ∀ k, 1 ≤ k → Ψ (x k) ≠ ⊤ → f (k + 1) ≤ f k := by
    intro k hk hfin
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hxp : P (extrap α x k - s • gradient Φ (extrap α x k)) = x (k + 1) := (hrun k hk).symm
    have I1 := nfb1_onestep hs L.2 hsL hconv hP hΦc hdiff hgrad (extrap α x k) (x k) (x (k + 1))
      hxp _ _ (fin_of _ (hnext k hk)) (fin_of _ hfin)
    have I2 := nfb1_onestep hs L.2 hsL hconv hP hΦc hdiff hgrad (extrap α x k) xstar (x (k + 1))
      hxp _ _ (fin_of _ (hnext k hk)) (fin_of _ hstar_ne)
    set d := extrap α x k - x (k + 1) with hd
    have V1 := congrArg (fun v => ⟪d, v⟫) (nfb1_V1 α x xstar k hα hk)
    simp only [inner_add_right, real_inner_smul_right] at V1
    have V2 := nfb1_V2 α x xstar k hα hk
    rw [← hd] at V2
    have hN : ‖zSeq α x (k + 1) - xstar‖ ^ 2 = ‖zSeq α x k - xstar‖ ^ 2
        - 2 * (((k : ℝ) + α - 1) / (α - 1)) * ⟪d, zSeq α x k - xstar⟫
        + (((k : ℝ) + α - 1) / (α - 1)) ^ 2 * ‖d‖ ^ 2 := by
      rw [V2, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, real_inner_comm]
      ring
    have hA := nfb1_alg s α k (T k) (T (k + 1)) Ts _ _ _ (‖d‖ ^ 2) _ _ hs hα hk' (hTs k hfin)
      (by positivity) (by simp only [hTdef]; linarith)
      (by simp only [hTdef]; linarith) V1 hN
    simp only [hfdef]
    push_cast
    exact hA
  refine ⟨fun k hk => ?_, ?_⟩
  · by_cases h : Ψ (x k) = ⊤
    · rw [hEtop k hk h]; exact le_top
    · rw [hE (k + 1) (hnext k hk), hE k h]
      exact EReal.coe_le_coe_iff.2 (hstep k hk h)
  · have hfin2 : ∀ n : ℕ, Ψ (x (n + 2)) ≠ ⊤ := fun n => hnext (n + 1) (by omega)
    have hg_anti : Antitone (fun n : ℕ => f (n + 2)) :=
      antitone_nat_of_succ_le (fun n => hstep (n + 2) (by omega) (hfin2 n))
    have hg_nonneg : ∀ n : ℕ, 0 ≤ f (n + 2) := by
      intro n
      have h1 := hTs (n + 2) (hfin2 n)
      have : 0 < α - 1 := by linarith
      simp only [hfdef]
      have : 0 ≤ T (n + 2) - Ts := by linarith
      positivity
    have hg_tend := tendsto_atTop_ciInf hg_anti ⟨0, by rintro _ ⟨n, rfl⟩; exact hg_nonneg n⟩
    refine ⟨⨅ n : ℕ, f (n + 2), ?_⟩
    rw [← Filter.tendsto_add_atTop_iff_nat 2]
    have hfun : (fun n : ℕ => energy Ψ Φ α s x xstar (n + 2))
        = fun n : ℕ => ((f (n + 2) : ℝ) : EReal) := funext fun n => hE (n + 2) (hfin2 n)
    rw [hfun]
    exact (continuous_coe_real_ereal.tendsto _).comp hg_tend
