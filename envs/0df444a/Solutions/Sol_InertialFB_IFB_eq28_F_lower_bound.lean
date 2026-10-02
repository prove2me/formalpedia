-- Prove2me | solution 1 for InertialFB.IFB.eq28_F_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:16:46.928606+00:00
-- url     : https://prove2.me/submissions/4f5876cb-cb7d-4bcd-b957-149039faf1cd

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_InertialFB_IFB_Algorithm
import Definitions.Def_InertialFB_IFB_Lyapunov

set_option autoImplicit false

open Filter Topology

/-! ## Real-analysis helpers -/

theorem ifb_deriv_le {f : ℝ → ℝ} {f' c : ℝ} (hf : HasDerivAt f f' 0)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → f t - f 0 ≤ t * c) : f' ≤ c := by
  have ht := hf.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (f (0 + t) - f 0) ≤ c := by
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht'
    rw [zero_add, smul_eq_mul, inv_mul_le_iff₀ ht'.1]
    exact h t ht'.1 ht'.2
  exact le_of_tendsto ht hev

theorem ifb_le_deriv {f : ℝ → ℝ} {f' c : ℝ} (hf : HasDerivAt f f' 0)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → t * c ≤ f t - f 0) : c ≤ f' := by
  have ht := hf.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), c ≤ t⁻¹ • (f (0 + t) - f 0) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht'
    rw [zero_add, smul_eq_mul, le_inv_mul_iff₀ ht'.1]
    exact h t ht'.1 ht'.2
  exact ge_of_tendsto ht hev

theorem ifb_line_deriv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : H → ℝ} (hΨ : Differentiable ℝ Ψ) (x d : H) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => Ψ (x + t • d)) (inner ℝ (gradient Ψ (x + t0 • d)) d) t0 := by
  have h1 : HasFDerivAt Ψ (InnerProductSpace.toDual ℝ H (gradient Ψ (x + t0 • d))) (x + t0 • d) :=
    (hΨ (x + t0 • d)).hasGradientAt.hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => x + t • d) d t0 := by
    simpa using ((hasDerivAt_id t0).smul_const d).const_add x
  have h3 := h1.comp_hasDerivAt t0 h2
  simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h3

theorem ifb_line_deriv0 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : H → ℝ} (hΨ : Differentiable ℝ Ψ) (x d : H) :
    HasDerivAt (fun t : ℝ => Ψ (x + t • d)) (inner ℝ (gradient Ψ x) d) 0 := by
  simpa using ifb_line_deriv hΨ x d 0

theorem ifb_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : H → ℝ} {L : ℝ} (hΨ : Differentiable ℝ Ψ)
    (hL : ∀ x y : H, ‖gradient Ψ x - gradient Ψ y‖ ≤ L * ‖x - y‖) (x y : H) :
    Ψ y ≤ Ψ x + inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  have hf : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ψ (x + t • (y - x)))
      (inner ℝ (gradient Ψ (x + t • (y - x))) (y - x)) t :=
    fun t => ifb_line_deriv hΨ x (y - x) t
  have hB : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => Ψ x + t * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * t ^ 2)
      (inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t)) t := by
    intro t
    have h1 := ((hasDerivAt_id' t).mul_const (inner ℝ (gradient Ψ x) (y - x))).const_add (Ψ x)
    have h2 := (hasDerivAt_pow 2 t).const_mul (L / 2 * ‖y - x‖ ^ 2)
    have h3 : HasDerivAt
        (fun s : ℝ => Ψ x + s * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * s ^ 2)
        (1 * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (↑2 * t ^ (2 - 1))) t :=
      h1.add h2
    exact h3.congr_deriv (by norm_num)
  have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1)
    (f := fun t : ℝ => Ψ (x + t • (y - x)))
    (f' := fun t => inner ℝ (gradient Ψ (x + t • (y - x))) (y - x))
    (B := fun t : ℝ => Ψ x + t * inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * t ^ 2)
    (B' := fun t => inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t))
    (fun t _ => (hf t).continuousAt.continuousWithinAt)
    (fun t _ => (hf t).hasDerivWithinAt)
    (by simp)
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (by
      intro t ht
      have ht0 : 0 ≤ t := ht.1
      show inner ℝ (gradient Ψ (x + t • (y - x))) (y - x) ≤
        inner ℝ (gradient Ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 * (2 * t)
      have e1 : inner ℝ (gradient Ψ (x + t • (y - x))) (y - x) - inner ℝ (gradient Ψ x) (y - x)
          = inner ℝ (gradient Ψ (x + t • (y - x)) - gradient Ψ x) (y - x) := by
        rw [inner_sub_left]
      have e2 := real_inner_le_norm (gradient Ψ (x + t • (y - x)) - gradient Ψ x) (y - x)
      have e3 := hL (x + t • (y - x)) x
      have e4 : ‖x + t • (y - x) - x‖ = t * ‖y - x‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0]
      rw [e4] at e3
      have e5 := mul_le_mul_of_nonneg_right e3 (norm_nonneg (y - x))
      nlinarith)
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num)
  have e6 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e6, one_mul, one_pow, mul_one] at key
  linarith

/-- Abstract contraction: `w_{k+1} ≤ ρ w_k + η_k`, `ρ < 1`, `η → 0` forces `w → 0`. -/
theorem ifb_contract {w η : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hw0 : ∀ k, 0 ≤ w k)
    (hrec : ∀ k, w (k + 1) ≤ ρ * w k + η k) (hη : Tendsto η atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε2 : 0 < (1 - ρ) * (ε / 2) := mul_pos (by linarith) (by linarith)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hη ((1 - ρ) * (ε / 2)) hε2
  have hind : ∀ n : ℕ, w (K + n) ≤ ρ ^ n * w K + ε / 2 := by
    intro n
    induction n with
    | zero => simp only [add_zero, pow_zero, one_mul]; linarith
    | succ n ih =>
      have h1 := hrec (K + n)
      have h2 := hK (K + n) (Nat.le_add_right K n)
      rw [Real.dist_eq, sub_zero] at h2
      have h3 : η (K + n) ≤ (1 - ρ) * (ε / 2) := (le_abs_self _).trans h2.le
      have h4 : ρ * w (K + n) ≤ ρ * (ρ ^ n * w K + ε / 2) := mul_le_mul_of_nonneg_left ih hρ0
      rw [show K + (n + 1) = K + n + 1 from rfl, pow_succ]
      nlinarith
  have hpow : Tendsto (fun n : ℕ => ρ ^ n * w K) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).mul_const (w K)
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.1 hpow (ε / 2) (by linarith)
  refine ⟨K + N1, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = K + m := ⟨n - K, by omega⟩
  have h1 := hind m
  have h2 := hN1 m (by omega)
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  rw [abs_of_nonneg (hw0 _)]
  have := le_abs_self (ρ ^ m * w K)
  linarith

/-- Quasi-Fejér sequences converge. -/
theorem ifb_qfejer {V ε : ℕ → ℝ} {m B : ℝ} (hV : ∀ k, V (k + 1) ≤ V k + ε k)
    (hε : ∀ k, 0 ≤ ε k) (hεB : ∀ N, ∑ k ∈ Finset.range N, ε k ≤ B) (hm : ∀ k, m ≤ V k) :
    ∃ l, Tendsto V atTop (𝓝 l) := by
  have hs : Summable ε := summable_of_sum_range_le hε hεB
  have hAanti : Antitone (fun k => V k - ∑ j ∈ Finset.range k, ε j) := by
    apply antitone_nat_of_succ_le
    intro k
    simp only [Finset.sum_range_succ]
    linarith [hV k]
  have hAbdd : BddBelow (Set.range (fun k => V k - ∑ j ∈ Finset.range k, ε j)) := by
    refine ⟨m - B, ?_⟩
    rintro _ ⟨k, rfl⟩
    simp only
    linarith [hm k, hεB k]
  have h1 := tendsto_atTop_ciInf hAanti hAbdd
  have h2 := hs.hasSum.tendsto_sum_nat
  refine ⟨(⨅ i, (V i - ∑ j ∈ Finset.range i, ε j)) + ∑' k, ε k, ?_⟩
  refine (h1.add h2).congr (fun k => ?_)
  ring

theorem ifb_amgm {κ β s t : ℝ} (hκ : 0 < κ) : β * (s * t) ≤ κ / 4 * t ^ 2 + β ^ 2 / κ * s ^ 2 := by
  have hκ' : κ ≠ 0 := hκ.ne'
  have h : 0 ≤ (κ / 2 * t - β * s) ^ 2 / κ := by positivity
  have e : (κ / 2 * t - β * s) ^ 2 / κ = κ / 4 * t ^ 2 + β ^ 2 / κ * s ^ 2 - β * (s * t) := by
    field_simp
    ring
  linarith

theorem ifb_norm4 {H : Type*} [NormedAddCommGroup H] (A B C D : H) :
    ‖A + B - C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  have t1 := norm_add_le (A + B - C) D
  have t2 := norm_sub_le (A + B) C
  have t3 := norm_add_le A B
  linarith

/-! ## Convex-analysis helpers -/

open InertialFB.IFB in
theorem ifb_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Φ : H → EReal}
    (hP : IsProperFn Φ) {x : H} (hx : Φ x ≠ ⊤) : Φ x = ((Φ x).toReal : EReal) :=
  (EReal.coe_toReal hx (hP.1 x)).symm

open InertialFB.IFB in
theorem ifb_subgrad_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Φ : H → EReal} (hP : IsProperFn Φ) {u g v : H} (hg : IsSubgradient Φ u g) (hv : Φ v ≠ ⊤) :
    (Φ u).toReal + inner ℝ g (v - u) ≤ (Φ v).toReal := by
  have h := hg.2 v
  rw [ifb_fin hP hg.1, ifb_fin hP hv, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  exact h

open InertialFB.IFB in
theorem ifb_theta_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} (hP : IsProperFn Φ) {x : H} (hx : Φ x ≠ ⊤) :
    theta Φ Ψ x = (((Φ x).toReal + Ψ x : ℝ) : EReal) := by
  rw [EReal.coe_add, ← ifb_fin hP hx]
  rfl

open InertialFB.IFB in
theorem ifb_theta_top {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {x : H} (hx : Φ x = ⊤) : theta Φ Ψ x = ⊤ := by
  show Φ x + ((Ψ x : ℝ) : EReal) = ⊤
  rw [hx, EReal.top_add_coe]


/-- The subgradient `g_{k+1} ∈ ∂Φ(u_{k+1})` selected by (IFB). -/
noncomputable def ifbG {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b lam : ℝ) (u y : ℕ → H) (k : ℕ) : H :=
  -((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k)

/-- Scaled energy `bλ² Θ(u_{k+1}) + (1-aλ)/2 ‖u_{k+1}-u_k‖²`. -/
noncomputable def ifbE {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (Ψ : H → ℝ) (a b lam : ℝ) (u : ℕ → H) (k : ℕ) : ℝ :=
  b * lam ^ 2 * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))) + (1 - a * lam) / 2 * ‖u (k + 1) - u k‖ ^ 2

/-- The monotonicity defect `⟪g_{k+2} - g_{k+1}, u_{k+2} - u_{k+1}⟫ ≥ 0`. -/
noncomputable def ifbD {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b lam : ℝ) (u y : ℕ → H) (k : ℕ) : ℝ :=
  inner ℝ (ifbG a b lam u y (k + 1) - ifbG a b lam u y k) (u (k + 1 + 1) - u (k + 1))

/-- The anchored Lyapunov function. -/
noncomputable def ifbV {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b lam : ℝ) (Φ : H → EReal) (u y : ℕ → H) (q : H) (k : ℕ) : ℝ :=
  (a + b) * lam / 2 * ‖u k - q‖ ^ 2 + (1 + b * lam) * inner ℝ (u (k + 1) - u k) (u k - q)
    + lam * (1 + b * lam) * (inner ℝ (ifbG a b lam u y k) (u (k + 1) - q) - (Φ (u (k + 1))).toReal)

open InertialFB.IFB in
theorem ifb_R {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {a b lam : ℝ} {u y : ℕ → H} (hlam : lam ≠ 0)
    (hIFB : IsIFBSeq Φ Ψ a b lam u y) (k : ℕ) :
    (1 + b * lam) • (u (k + 1 + 1) - u (k + 1)) - (1 - a * lam) • (u (k + 1) - u k)
      + (lam * (1 + b * lam)) • ifbG a b lam u y (k + 1) - lam • ifbG a b lam u y k
      + (b * lam ^ 2) • gradient Ψ (u (k + 1)) = 0 := by
  have h := (hIFB k).2
  simp only [ifbG]
  linear_combination (norm := skip) (b * lam ^ 2) • h
  match_scalars <;> field_simp <;> ring

theorem ifb_energy_alg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b lam L : ℝ} (hb : 0 < b) (hlam : 0 < lam) (hal : 0 ≤ 1 - a * lam)
    (X0 X1 G0 G1 N1 : H) (φ0 φ1 ψ0 ψ1 : ℝ)
    (hR : (1 + b * lam) • X1 - (1 - a * lam) • X0 + (lam * (1 + b * lam)) • G1 - lam • G0
      + (b * lam ^ 2) • N1 = 0)
    (h1 : φ1 + inner ℝ G1 (-X1) ≤ φ0) (h0 : φ0 + inner ℝ G0 X1 ≤ φ1)
    (h2 : ψ1 ≤ ψ0 + inner ℝ N1 X1 + L / 2 * ‖X1‖ ^ 2) :
    b * lam ^ 2 * (φ1 + ψ1) + (1 - a * lam) / 2 * ‖X1‖ ^ 2
      + ((a + b) * lam - b * lam ^ 2 * L / 2) * ‖X1‖ ^ 2 + lam * inner ℝ (G1 - G0) X1
      ≤ b * lam ^ 2 * (φ0 + ψ0) + (1 - a * lam) / 2 * ‖X0‖ ^ 2
    ∧ 0 ≤ inner ℝ (G1 - G0) X1 := by
  have hI := congrArg (fun z => inner ℝ z X1) hR
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left] at hI
  rw [inner_neg_right] at h1
  have hXX : inner ℝ X1 X1 = ‖X1‖ ^ 2 := real_inner_self_eq_norm_sq X1
  rw [hXX] at hI
  have hsq : ‖X0 - X1‖ ^ 2 = ‖X0‖ ^ 2 - 2 * inner ℝ X0 X1 + ‖X1‖ ^ 2 := norm_sub_sq_real X0 X1
  have hD : inner ℝ (G1 - G0) X1 = inner ℝ G1 X1 - inner ℝ G0 X1 := inner_sub_left _ _ _
  have hDnn : 0 ≤ inner ℝ (G1 - G0) X1 := by rw [hD]; linarith
  refine ⟨?_, hDnn⟩
  have hbl : 0 ≤ b * lam ^ 2 := by positivity
  have hsum : φ1 + ψ1 - (φ0 + ψ0) ≤ inner ℝ G1 X1 + inner ℝ N1 X1 + L / 2 * ‖X1‖ ^ 2 := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hsum hbl
  have hn : 0 ≤ (1 - a * lam) * (‖X0‖ ^ 2 - 2 * inner ℝ X0 X1 + ‖X1‖ ^ 2) := by
    rw [← hsq]; exact mul_nonneg hal (sq_nonneg _)
  rw [hD]
  linarith

theorem ifb_anchor_alg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b lam : ℝ} (hb : 0 < b) (hlam : 0 < lam)
    (A B C X0 X1 G0 G1 N1 : H) (φ0 φ1 θ0 Θq : ℝ)
    (hB : B = A + X0) (hC : C = B + X1)
    (hR : (1 + b * lam) • X1 - (1 - a * lam) • X0 + (lam * (1 + b * lam)) • G1 - lam • G0
      + (b * lam ^ 2) • N1 = 0)
    (hF1 : θ0 + inner ℝ (G0 + N1) (-B) ≤ Θq)
    (hF3 : φ0 + inner ℝ G0 X1 ≤ φ1) :
    b * lam ^ 2 * (θ0 - Θq) ≤
      ((a + b) * lam / 2 * ‖A‖ ^ 2 + (1 + b * lam) * inner ℝ X0 A
        + lam * (1 + b * lam) * (inner ℝ G0 B - φ0))
      - ((a + b) * lam / 2 * ‖B‖ ^ 2 + (1 + b * lam) * inner ℝ X1 B
        + lam * (1 + b * lam) * (inner ℝ G1 C - φ1))
      + ((a + b) * lam / 2 + (1 - a * lam)) * ‖X0‖ ^ 2
      + lam * (1 + b * lam) * inner ℝ (G1 - G0) X1 := by
  subst hC
  subst hB
  have hI := congrArg (fun z => inner ℝ z (A + X0)) hR
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left,
    inner_add_right] at hI
  simp only [inner_add_left, inner_add_right, inner_neg_right, inner_sub_left] at hF1 ⊢
  rw [norm_add_sq_real, real_inner_comm X0 A]
  rw [real_inner_self_eq_norm_sq X0] at hI
  have hbl : 0 ≤ b * lam ^ 2 := by positivity
  have hlb : 0 ≤ lam * (1 + b * lam) := by positivity
  have hm1 := mul_le_mul_of_nonneg_left hF1 hbl
  have hm3 := mul_le_mul_of_nonneg_left hF3 hlb
  linarith

open InertialFB.IFB in
theorem ifb_energy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) (k : ℕ) :
    ifbE Φ Ψ a b lam u (k + 1)
      + ((a + b) * lam - b * lam ^ 2 * L / 2) * ‖u (k + 1 + 1) - u (k + 1)‖ ^ 2
      + lam * ifbD a b lam u y k ≤ ifbE Φ Ψ a b lam u k ∧ 0 ≤ ifbD a b lam u y k := by
  have hP := hH.phi_proper
  have hs0 : IsSubgradient Φ (u (k + 1)) (ifbG a b lam u y k) := (hIFB k).1
  have hs1 : IsSubgradient Φ (u (k + 1 + 1)) (ifbG a b lam u y (k + 1)) := (hIFB (k + 1)).1
  have h1 := ifb_subgrad_real hP hs1 hs0.1
  have h0 := ifb_subgrad_real hP hs0 hs1.1
  have hd := ifb_descent hH.psi_diff hH.psi_grad_lipschitz (u (k + 1)) (u (k + 1 + 1))
  rw [show u (k + 1) - u (k + 1 + 1) = -(u (k + 1 + 1) - u (k + 1)) from
    (neg_sub _ _).symm] at h1
  have hal : 0 ≤ 1 - a * lam := by
    have := (lt_div_iff₀ hH.a_pos).1 hH.lam_lt_inv_a
    linarith
  have := ifb_energy_alg hH.b_pos hH.lam_pos hal _ _ _ _ _ _ _ _ _
    (ifb_R (ne_of_gt hH.lam_pos) hIFB k) h1 h0 hd
  simp only [ifbE, ifbD]
  exact this

open InertialFB.IFB in
open InertialFB.IFB in
theorem ifb_sums {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    ∃ BX BD : ℝ, (∀ N, ∑ k ∈ Finset.range N, ‖u (k + 1) - u k‖ ^ 2 ≤ BX) ∧
      (∀ N, ∑ k ∈ Finset.range N, ifbD a b lam u y k ≤ BD) ∧ (∀ k, 0 ≤ ifbD a b lam u y k) ∧
      (∀ k, ‖u (k + 1) - u k‖ ^ 2 ≤ BX) ∧ Antitone (ifbE Φ Ψ a b lam u) := by
  obtain ⟨m, hm⟩ := hH.theta_bdd_below
  have hP := hH.phi_proper
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hθm : ∀ k, m ≤ (Φ (u (k + 1))).toReal + Ψ (u (k + 1)) := by
    intro k
    have := hm (u (k + 1))
    rw [ifb_theta_eq hP (hIFB k).1.1, EReal.coe_le_coe_iff] at this
    exact this
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hc' : 0 < (a + b) * lam - b * lam ^ 2 * L / 2 := by
    have h1 := hH.lam_lt_bound
    have hbL : 0 < b * L := mul_pos hb hH.L_pos
    rw [lt_div_iff₀ hbL] at h1
    nlinarith
  have hEm : ∀ k, b * lam ^ 2 * m ≤ ifbE Φ Ψ a b lam u k := by
    intro k
    simp only [ifbE]
    have h1 := mul_le_mul_of_nonneg_left (hθm k) (by positivity : (0:ℝ) ≤ b * lam ^ 2)
    have h2 : 0 ≤ (1 - a * lam) / 2 * ‖u (k + 1) - u k‖ ^ 2 := by
      have := sq_nonneg ‖u (k + 1) - u k‖
      have := mul_nonneg hal.le this
      linarith
    linarith
  have hen := fun k => ifb_energy hH hIFB k
  have hD0 : ∀ k, 0 ≤ ifbD a b lam u y k := fun k => (hen k).2
  have htel : ∀ N, ∑ k ∈ Finset.range N, (((a + b) * lam - b * lam ^ 2 * L / 2)
      * ‖u (k + 1 + 1) - u (k + 1)‖ ^ 2 + lam * ifbD a b lam u y k)
      ≤ ifbE Φ Ψ a b lam u 0 - ifbE Φ Ψ a b lam u N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      linarith [(hen N).1]
  have hS1 : ∀ N, ∑ k ∈ Finset.range N, ‖u (k + 1 + 1) - u (k + 1)‖ ^ 2
      ≤ (ifbE Φ Ψ a b lam u 0 - b * lam ^ 2 * m) / ((a + b) * lam - b * lam ^ 2 * L / 2) := by
    intro N
    rw [le_div_iff₀ hc', Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) ((htel N).trans (by linarith [hEm N]))
    have := hD0 k
    have := mul_nonneg hlam.le this
    nlinarith
  have hS2 : ∀ N, ∑ k ∈ Finset.range N, ifbD a b lam u y k
      ≤ (ifbE Φ Ψ a b lam u 0 - b * lam ^ 2 * m) / lam := by
    intro N
    rw [le_div_iff₀ hlam, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) ((htel N).trans (by linarith [hEm N]))
    have := mul_nonneg hc'.le (sq_nonneg ‖u (k + 1 + 1) - u (k + 1)‖)
    nlinarith
  set BX := ‖u (0 + 1) - u 0‖ ^ 2
    + (ifbE Φ Ψ a b lam u 0 - b * lam ^ 2 * m) / ((a + b) * lam - b * lam ^ 2 * L / 2) with hBX
  have hSX : ∀ N, ∑ k ∈ Finset.range N, ‖u (k + 1) - u k‖ ^ 2 ≤ BX := by
    intro N
    have h1 : ∑ k ∈ Finset.range N, ‖u (k + 1) - u k‖ ^ 2
        ≤ ∑ k ∈ Finset.range (N + 1), ‖u (k + 1) - u k‖ ^ 2 := by
      rw [Finset.sum_range_succ]
      have := sq_nonneg ‖u (N + 1) - u N‖
      linarith
    rw [Finset.sum_range_succ'] at h1
    have := hS1 N
    linarith
  refine ⟨BX, _, hSX, hS2, hD0, fun k => ?_, ?_⟩
  · have h1 := Finset.single_le_sum (f := fun j => ‖u (j + 1) - u j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.self_mem_range_succ k)
    exact h1.trans (hSX (k + 1))
  · apply antitone_nat_of_succ_le
    intro k
    have h1 := (hen k).1
    have h2 := hD0 k
    have h3 := mul_nonneg hlam.le h2
    have h4 := mul_nonneg hc'.le (sq_nonneg ‖u (k + 1 + 1) - u (k + 1)‖)
    linarith

open InertialFB.IFB in

open InertialFB.IFB in
theorem ifb28_z_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a b lam : ℝ) (u y : ℕ → H) (k : ℕ) :
    zSeq a b lam u y (k + 1) = -ifbG a b lam u y k := by
  simp [zSeq, ifbG, xi]

open InertialFB.IFB in
theorem ifb28_xi_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (k : ℕ) : xi u (k + 1) = u (k + 1) - u k := by
  simp [xi]

open InertialFB.IFB in
theorem ifb28_zsum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) (k : ℕ) :
    -∑ i ∈ Finset.Icc 2 (k + 1), inner ℝ (zSeq a b lam u y i) (xi u i)
      ≤ (Φ (u (k + 1))).toReal - (Φ (u 1)).toReal
        + ∑ j ∈ Finset.range k, ifbD a b lam u y j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1 + 1), Finset.sum_range_succ]
    have hz := ifb28_z_eq a b lam u y (k + 1)
    have hx := ifb28_xi_eq u (k + 1)
    rw [hz, hx, inner_neg_left]
    have hs := ifb_subgrad_real hH.phi_proper (hIFB k).1 (hIFB (k + 1)).1.1
    have hD : ifbD a b lam u y k = inner ℝ (ifbG a b lam u y (k + 1)) (u (k + 1 + 1) - u (k + 1))
        - inner ℝ (ifbG a b lam u y k) (u (k + 1 + 1) - u (k + 1)) := by
      simp only [ifbD]; exact inner_sub_left _ _ _
    have hg : ifbG a b lam u y k = -((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) := rfl
    rw [← hg] at hs
    linarith

open InertialFB.IFB in
theorem ifb28_xisum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (k : ℕ) :
    ∑ i ∈ Finset.Icc 2 (k + 1), ‖xi u i‖ ^ 2 ≤ ∑ j ∈ Finset.range (k + 1), ‖u (j + 1) - u j‖ ^ 2 := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.sum_range_one]
    rw [show Finset.Icc 2 1 = (∅ : Finset ℕ) from rfl, Finset.sum_empty]
    positivity
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1 + 1), Finset.sum_range_succ,
      ifb28_xi_eq u (k + 1)]
    linarith

open InertialFB.IFB in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (Ψ : H → ℝ) (L a b lam : ℝ)
    (hH : HypothesisH Φ Ψ L a b lam) (u y : ℕ → H) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    ∀ q : H, Φ q ≠ ⊤ → ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k →
      C + alphaC b lam * ‖u (k + 1) - q‖ ^ 2 -
          (alphaC b lam - (a + b) / (2 * lam)) * ‖u k - q‖ ^ 2 ≤ auxF a b lam u y k q ∧
      C + alphaC b lam * (‖u (k + 1) - q‖ ^ 2 - ‖u k - q‖ ^ 2) ≤
        C + alphaC b lam * ‖u (k + 1) - q‖ ^ 2 -
          (alphaC b lam - (a + b) / (2 * lam)) * ‖u k - q‖ ^ 2 := by
  intro q hq
  obtain ⟨BX, BD, hSX, hSD, hD0, hX1, -⟩ := ifb_sums hH hIFB
  have ha := hH.a_pos
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hα : 0 < alphaC b lam := by unfold alphaC; positivity
  have hδ : 0 < deltaC a b lam := by
    unfold deltaC
    apply div_pos _ (by positivity)
    nlinarith
  have hc : 0 < 1 / lam + b := by positivity
  have hab : 0 ≤ (a + b) / (2 * lam) := by positivity
  refine ⟨-(1 / lam + b) * ((Φ q).toReal - (Φ (u 1)).toReal + BD)
    - deltaC a b lam * BX - alphaC b lam * BX, fun k hk => ⟨?_, ?_⟩⟩
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    -- bound on G_{m+2}
    have hZ := ifb28_zsum hH hIFB (m + 1)
    have hDs : ∑ j ∈ Finset.range (m + 1), ifbD a b lam u y j ≤ BD := hSD (m + 1)
    have hs := ifb_subgrad_real hH.phi_proper (hIFB (m + 1)).1 hq
    have hg : ifbG a b lam u y (m + 1)
        = -((1 / lam) • (u (m + 1 + 1) - u (m + 1)) + a • u (m + 1) - b • y (m + 1)) := rfl
    rw [← hg] at hs
    have hz := ifb28_z_eq a b lam u y (m + 1)
    have hin : inner ℝ (zSeq a b lam u y (m + 1 + 1)) (u (m + 1 + 1) - q)
        = inner ℝ (ifbG a b lam u y (m + 1)) (q - u (m + 1 + 1)) := by
      rw [hz, inner_neg_left, ← inner_neg_right, neg_sub]
    have hG : auxG a b lam u y (m + 1 + 1) q ≤ (Φ q).toReal - (Φ (u 1)).toReal + BD := by
      unfold auxG
      rw [hin]
      linarith
    have hS : ∑ i ∈ Finset.Icc 2 (m + 1), ‖xi u i‖ ^ 2 ≤ BX :=
      (ifb28_xisum u m).trans (hSX (m + 1))
    have hXi : ‖u (m + 1 + 1) - u (m + 1)‖ ^ 2 ≤ BX := hX1 (m + 1)
    have hsq : ‖u (m + 1 + 1) - q‖ ^ 2 = ‖u (m + 1 + 1) - u (m + 1)‖ ^ 2
        + 2 * inner ℝ (u (m + 1 + 1) - u (m + 1)) (u (m + 1) - q) + ‖u (m + 1) - q‖ ^ 2 := by
      rw [show u (m + 1 + 1) - q = (u (m + 1 + 1) - u (m + 1)) + (u (m + 1) - q) by abel]
      exact norm_add_sq_real _ _
    have h1 := mul_le_mul_of_nonneg_left hG hc.le
    have h2 := mul_le_mul_of_nonneg_left hS hδ.le
    have h3 := mul_le_mul_of_nonneg_left hXi hα.le
    unfold auxF
    rw [ifb28_xi_eq u (m + 1)]
    rw [hsq]
    nlinarith
  · have := mul_nonneg hab (sq_nonneg ‖u k - q‖)
    nlinarith
