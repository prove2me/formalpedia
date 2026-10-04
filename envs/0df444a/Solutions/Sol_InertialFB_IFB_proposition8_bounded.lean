-- Prove2me | solution 1 for InertialFB.IFB.proposition8_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:02:51.089298+00:00
-- url     : https://prove2.me/submissions/fa0c8233-492c-430c-9ee3-8c1ad8851059

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

open InertialFB.IFB in
theorem ifb_convex_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : H → EReal} (hF : IsConvexFn F) {x z : H} {α β : ℝ} (hx : F x ≤ (α : EReal))
    (hz : F z ≤ (β : EReal)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    F (x + t • (z - x)) ≤ (((1 - t) * α + t * β : ℝ) : EReal) := by
  have hmem := hF (show (x, α) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} from hx)
    (show (z, β) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} from hz) (sub_nonneg.mpr ht1) ht0
    (by ring)
  have e : (1 - t) • x + t • z = x + t • (z - x) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hmem
  rw [e] at hmem
  exact hmem

open InertialFB.IFB in
theorem ifb_sublevel_convex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : H → EReal} (hF : IsConvexFn F) (c : ℝ) : Convex ℝ {x | F x ≤ (c : EReal)} := by
  intro x hx z hz s t hs ht hst
  have hmem := hF (show (x, c) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} from hx)
    (show (z, c) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} from hz) hs ht hst
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hmem
  have e : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
  rw [e] at hmem
  exact hmem

open InertialFB.IFB in
theorem ifb_theta_lsc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} (hΦ : LowerSemicontinuous Φ) (hΨ : Continuous Ψ) :
    LowerSemicontinuous (theta Φ Ψ) := by
  have h2 : LowerSemicontinuous (fun x => ((Ψ x : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.comp hΨ).lowerSemicontinuous
  exact hΦ.add' h2 (fun x => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _)))

open InertialFB.IFB in
theorem ifb_theta_subgrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} (hP : IsProperFn Φ) (hΨ : Differentiable ℝ Ψ)
    (hΘ : IsConvexFn (theta Φ Ψ)) {u g : H} (hg : IsSubgradient Φ u g) {q : H} (hq : Φ q ≠ ⊤) :
    (Φ u).toReal + Ψ u + inner ℝ (g + gradient Ψ u) (q - u) ≤ (Φ q).toReal + Ψ q := by
  have hu := ifb_theta_eq (Ψ := Ψ) hP hg.1
  have hqe := ifb_theta_eq (Ψ := Ψ) hP hq
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → Ψ (u + t • (q - u)) - Ψ (u + (0:ℝ) • (q - u)) ≤
      t * ((Φ q).toReal + Ψ q - ((Φ u).toReal + Ψ u) - inner ℝ g (q - u)) := by
    intro t ht0 ht1
    have hc := ifb_convex_real hΘ (le_of_eq hu) (le_of_eq hqe) ht0.le ht1
    have hxt : Φ (u + t • (q - u)) ≠ ⊤ := by
      intro htop
      rw [ifb_theta_top htop] at hc
      exact (not_le.2 (EReal.coe_lt_top _)) hc
    rw [ifb_theta_eq hP hxt, EReal.coe_le_coe_iff] at hc
    have hs' := ifb_subgrad_real hP hg hxt
    have e1 : u + t • (q - u) - u = t • (q - u) := by abel
    rw [e1, real_inner_smul_right] at hs'
    rw [zero_smul, add_zero]
    nlinarith
  have := ifb_deriv_le (ifb_line_deriv0 hΨ u (q - u)) key
  rw [inner_add_left]
  linarith

open InertialFB.IFB in
theorem ifb_S_fin {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} (hP : IsProperFn Φ) {p : H} (hp : p ∈ argminSet Φ Ψ) :
    Φ p ≠ ⊤ := by
  obtain ⟨x0, hx0⟩ := hP.2
  have h := hp x0
  rw [ifb_theta_eq hP hx0] at h
  intro htop
  rw [ifb_theta_top htop] at h
  exact (not_le.2 (EReal.coe_lt_top _)) h

open InertialFB.IFB in
theorem ifb_fermat {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} (hP : IsProperFn Φ) (hΦc : IsConvexFn Φ)
    (hΨ : Differentiable ℝ Ψ) {p : H} (hp : p ∈ argminSet Φ Ψ) (hpf : Φ p ≠ ⊤) {v : H}
    (hv : Φ v ≠ ⊤) : (Φ p).toReal + inner ℝ (-gradient Ψ p) (v - p) ≤ (Φ v).toReal := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → t * ((Φ p).toReal - (Φ v).toReal) ≤
      Ψ (p + t • (v - p)) - Ψ (p + (0:ℝ) • (v - p)) := by
    intro t ht0 ht1
    have hc := ifb_convex_real hΦc (le_of_eq (ifb_fin hP hpf)) (le_of_eq (ifb_fin hP hv))
      ht0.le ht1
    have hxt : Φ (p + t • (v - p)) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hc
    rw [ifb_fin hP hxt, EReal.coe_le_coe_iff] at hc
    have hmin := hp (p + t • (v - p))
    rw [ifb_theta_eq hP hpf, ifb_theta_eq hP hxt, EReal.coe_le_coe_iff] at hmin
    rw [zero_smul, add_zero]
    nlinarith
  have := ifb_le_deriv (ifb_line_deriv0 hΨ p (v - p)) key
  rw [inner_neg_left]
  linarith

theorem ifb_subgrad_eq_grad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {φ : H → ℝ} (hφ : Differentiable ℝ φ) {u g : H}
    (h : ∀ v, φ u + inner ℝ g (v - u) ≤ φ v) : g = gradient φ u := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → t * inner ℝ g (g - gradient φ u) ≤
      φ (u + t • (g - gradient φ u)) - φ (u + (0:ℝ) • (g - gradient φ u)) := by
    intro t _ _
    have := h (u + t • (g - gradient φ u))
    rw [add_sub_cancel_left, real_inner_smul_right] at this
    rw [zero_smul, add_zero]
    linarith
  have h1 := ifb_le_deriv (ifb_line_deriv0 hφ u (g - gradient φ u)) key
  have h2 : inner ℝ (g - gradient φ u) (g - gradient φ u) ≤ 0 := by
    rw [inner_sub_left (g) (gradient φ u) (g - gradient φ u)]
    linarith
  rw [real_inner_self_eq_norm_sq] at h2
  have h3 : ‖g - gradient φ u‖ = 0 := by nlinarith [norm_nonneg (g - gradient φ u)]
  exact sub_eq_zero.1 (norm_eq_zero.1 h3)

theorem ifb_convex_grad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Ψ : H → ℝ} (hΨ : Differentiable ℝ Ψ) (hc : ConvexOn ℝ Set.univ Ψ)
    (z w : H) : Ψ z + inner ℝ (gradient Ψ z) (w - z) ≤ Ψ w := by
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      Ψ (z + t • (w - z)) - Ψ (z + (0:ℝ) • (w - z)) ≤ t * (Ψ w - Ψ z) := by
    intro t ht0 ht1
    have h := hc.2 (Set.mem_univ z) (Set.mem_univ w) (sub_nonneg.2 ht1) ht0.le (by ring)
    have e : (1 - t) • z + t • w = z + t • (w - z) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e, smul_eq_mul, smul_eq_mul] at h
    rw [zero_smul, add_zero]
    linarith
  have := ifb_deriv_le (ifb_line_deriv0 hΨ z (w - z)) key
  linarith

theorem ifb_cocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Ψ : H → ℝ} (hΨ : Differentiable ℝ Ψ) (hc : ConvexOn ℝ Set.univ Ψ)
    {L : ℝ} (hL0 : 0 < L) (hL : ∀ x y : H, ‖gradient Ψ x - gradient Ψ y‖ ≤ L * ‖x - y‖)
    (z x : H) :
    Ψ z + inner ℝ (gradient Ψ z) (x - z) + 1 / (2 * L) * ‖gradient Ψ x - gradient Ψ z‖ ^ 2
      ≤ Ψ x := by
  have h1 := ifb_convex_grad hΨ hc z (x - (1 / L) • (gradient Ψ x - gradient Ψ z))
  have h2 := ifb_descent hΨ hL x (x - (1 / L) • (gradient Ψ x - gradient Ψ z))
  have e1 : x - (1 / L) • (gradient Ψ x - gradient Ψ z) - x
      = -((1 / L) • (gradient Ψ x - gradient Ψ z)) := by abel
  have e2 : x - (1 / L) • (gradient Ψ x - gradient Ψ z) - z
      = (x - z) - (1 / L) • (gradient Ψ x - gradient Ψ z) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul] at h2
  rw [e2, inner_sub_right, real_inner_smul_right] at h1
  have e3 : inner ℝ (gradient Ψ x) (gradient Ψ x - gradient Ψ z)
      - inner ℝ (gradient Ψ z) (gradient Ψ x - gradient Ψ z)
      = ‖gradient Ψ x - gradient Ψ z‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have e4 : ‖(1:ℝ) / L‖ = 1 / L := Real.norm_of_nonneg (by positivity)
  rw [e4] at h2
  have e5 : L / 2 * (1 / L * ‖gradient Ψ x - gradient Ψ z‖) ^ 2
      = 1 / (2 * L) * ‖gradient Ψ x - gradient Ψ z‖ ^ 2 := by
    field_simp
  rw [e5] at h2
  have e6 : 1 / L * ‖gradient Ψ x - gradient Ψ z‖ ^ 2
      - 1 / (2 * L) * ‖gradient Ψ x - gradient Ψ z‖ ^ 2
      = 1 / (2 * L) * ‖gradient Ψ x - gradient Ψ z‖ ^ 2 := by
    field_simp
    ring
  have e7 : 1 / L * inner ℝ (gradient Ψ x) (gradient Ψ x - gradient Ψ z)
      - 1 / L * inner ℝ (gradient Ψ z) (gradient Ψ x - gradient Ψ z)
      = 1 / L * ‖gradient Ψ x - gradient Ψ z‖ ^ 2 := by
    rw [← mul_sub, e3]
  linarith

open InertialFB.IFB in
theorem ifb_weak_closed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {C : Set H} (hC : IsClosed C) (hconv : Convex ℝ C) {x : ℕ → H} {p : H}
    (hx : ∀ᶠ j in atTop, x j ∈ C) (hw : WeakTendsto x p) : p ∈ C := by
  obtain ⟨j0, hj0⟩ := hx.exists
  obtain ⟨v, hvC, hv⟩ :=
    exists_norm_eq_iInf_of_complete_convex ⟨x j0, hj0⟩ hC.isComplete hconv p
  have hineq := (norm_eq_iInf_iff_real_inner_le_zero hconv hvC).1 hv
  have ht : Tendsto (fun j => inner ℝ (x j) (p - v) - inner ℝ v (p - v)) atTop
      (𝓝 (inner ℝ p (p - v) - inner ℝ v (p - v))) := (hw (p - v)).sub_const _
  have hle : inner ℝ p (p - v) - inner ℝ v (p - v) ≤ 0 := by
    refine le_of_tendsto ht (hx.mono fun j hj => ?_)
    have := hineq (x j) hj
    linarith [real_inner_comm (x j) (p - v), real_inner_comm v (p - v),
      inner_sub_right (𝕜 := ℝ) (p - v) (x j) v]
  have e : inner ℝ p (p - v) - inner ℝ v (p - v) = ‖p - v‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have h0 : ‖p - v‖ = 0 := by nlinarith [norm_nonneg (p - v)]
  rw [norm_eq_zero, sub_eq_zero] at h0
  rw [h0]
  exact hvC

open InertialFB.IFB in
theorem ifb_weak_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : ℕ → H) (M : ℝ) (hM : ∀ n, ‖x n‖ ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ p : H, WeakTendsto (x ∘ σ) p := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK : IsCompact (Set.univ.pi fun _ : ℕ => Set.Icc (-(M * M)) (M * M)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hF : ∀ n, (fun m => inner ℝ (x n) (x m)) ∈
      Set.univ.pi fun _ : ℕ => Set.Icc (-(M * M)) (M * M) := by
    intro n m _
    have h1 := abs_real_inner_le_norm (x n) (x m)
    have h2 : ‖x n‖ * ‖x m‖ ≤ M * M := mul_le_mul (hM n) (hM m) (norm_nonneg _) hM0
    exact abs_le.1 (h1.trans h2)
  obtain ⟨c, -, σ, hσ, hlim⟩ := hK.tendsto_subseq hF
  refine ⟨σ, hσ, ?_⟩
  have hcoord : ∀ m, Tendsto (fun j => inner ℝ (x (σ j)) (x m)) atTop (𝓝 (c m)) :=
    fun m => (continuous_apply m).continuousAt.tendsto.comp hlim
  have hspan : ∀ v ∈ Submodule.span ℝ (Set.range x),
      ∃ l, Tendsto (fun j => inner ℝ (x (σ j)) v) atTop (𝓝 l) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨m, rfl⟩ := hv
      exact ⟨c m, hcoord m⟩
    | zero => exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨l1, h1⟩ := hv
      obtain ⟨l2, h2⟩ := hw
      exact ⟨l1 + l2, by simpa only [inner_add_right] using h1.add h2⟩
    | smul r v _ hv =>
      obtain ⟨l, h⟩ := hv
      exact ⟨r * l, by simpa only [real_inner_smul_right] using h.const_mul r⟩
  have hcl : ∀ v ∈ closure ((Submodule.span ℝ (Set.range x) : Submodule ℝ H) : Set H),
      ∃ l, Tendsto (fun j => inner ℝ (x (σ j)) v) atTop (𝓝 l) := by
    intro v hv
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0 < ε / (3 * (M + 1)) := by positivity
    obtain ⟨w, hwK, hvw⟩ := Metric.mem_closure_iff.1 hv _ hδ
    obtain ⟨l, hl⟩ := hspan w hwK
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have e1 : ∀ j, |inner ℝ (x (σ j)) v - inner ℝ (x (σ j)) w| ≤ M * (ε / (3 * (M + 1))) := by
      intro j
      rw [← inner_sub_right]
      refine (abs_real_inner_le_norm _ _).trans ?_
      refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
      rw [← dist_eq_norm]
      exact hvw.le
    have e2 : M * (ε / (3 * (M + 1))) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [Real.dist_eq] at h1 ⊢
    have a1 := abs_le.1 ((e1 m).trans e2)
    have a2 := abs_le.1 ((e1 n).trans e2)
    have a3 := abs_lt.1 h1
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have hall : ∀ v : H, ∃ l, Tendsto (fun j => inner ℝ (x (σ j)) v) atTop (𝓝 l) := by
    intro v
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ :=
      (Submodule.span ℝ (Set.range x)).topologicalClosure.exists_add_mem_mem_orthogonal v
    have hy1' : y1 ∈ closure ((Submodule.span ℝ (Set.range x) : Submodule ℝ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hy1
    obtain ⟨l, hl⟩ := hcl y1 hy1'
    refine ⟨l, ?_⟩
    have hz : ∀ j, inner ℝ (x (σ j)) z1 = 0 := fun j =>
      Submodule.inner_right_of_mem_orthogonal
        ((Submodule.span ℝ (Set.range x)).le_topologicalClosure
          (Submodule.subset_span ⟨σ j, rfl⟩)) hz1
    simpa only [inner_add_right, hz, add_zero] using hl
  choose f hf using hall
  have hfadd : ∀ v w, f (v + w) = f v + f w := fun v w =>
    tendsto_nhds_unique (hf (v + w)) (by simpa only [inner_add_right] using (hf v).add (hf w))
  have hfsmul : ∀ (r : ℝ) v, f (r • v) = r * f v := fun r v =>
    tendsto_nhds_unique (hf (r • v))
      (by simpa only [real_inner_smul_right] using (hf v).const_mul r)
  have hfb : ∀ v, ‖f v‖ ≤ M * ‖v‖ := by
    intro v
    refine le_of_tendsto' (hf v).norm (fun j => ?_)
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  let fl : H →ₗ[ℝ] ℝ :=
    { toFun := f
      map_add' := hfadd
      map_smul' := fun r v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact hfsmul r v }
  let fc : StrongDual ℝ H := fl.mkContinuous M hfb
  refine ⟨(InnerProductSpace.toDual ℝ H).symm fc, fun v => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  have e : fc v = f v := rfl
  rw [e]
  exact hf v

/-! ## The algorithm -/

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
theorem ifb_anchor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) {q : H} (hq : Φ q ≠ ⊤)
    (k : ℕ) :
    b * lam ^ 2 * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1)) - ((Φ q).toReal + Ψ q)) ≤
      ifbV a b lam Φ u y q k - ifbV a b lam Φ u y q (k + 1)
      + ((a + b) * lam / 2 + (1 - a * lam)) * ‖u (k + 1) - u k‖ ^ 2
      + lam * (1 + b * lam) * ifbD a b lam u y k := by
  have hP := hH.phi_proper
  have hs0 : IsSubgradient Φ (u (k + 1)) (ifbG a b lam u y k) := (hIFB k).1
  have hs1 : IsSubgradient Φ (u (k + 1 + 1)) (ifbG a b lam u y (k + 1)) := (hIFB (k + 1)).1
  have hF1 := ifb_theta_subgrad hP hH.psi_diff hH.theta_convex hs0 hq
  have hF3 := ifb_subgrad_real hP hs0 hs1.1
  have hR := ifb_R (ne_of_gt hH.lam_pos) hIFB k
  rw [show q - u (k + 1) = -(u (k + 1) - q) from (neg_sub _ _).symm] at hF1
  have := ifb_anchor_alg (a := a) hH.b_pos hH.lam_pos (u k - q) (u (k + 1) - q)
    (u (k + 1 + 1) - q) (u (k + 1) - u k) (u (k + 1 + 1) - u (k + 1)) (ifbG a b lam u y k)
    (ifbG a b lam u y (k + 1)) (gradient Ψ (u (k + 1))) ((Φ (u (k + 1))).toReal)
    ((Φ (u (k + 1 + 1))).toReal) ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))) ((Φ q).toReal + Ψ q)
    (by abel) (by abel) hR hF1 hF3
  simp only [ifbV, ifbD]
  exact this

open InertialFB.IFB in
theorem ifb_Vlower {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) {q : H} (hq : Φ q ≠ ⊤)
    (k : ℕ) :
    (a + b) * lam / 4 * ‖u k - q‖ ^ 2
      - (1 + b * lam) ^ 2 / ((a + b) * lam) * ‖u (k + 1) - u k‖ ^ 2
      - lam * (1 + b * lam) * (Φ q).toReal ≤ ifbV a b lam Φ u y q k := by
  have hP := hH.phi_proper
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hs := ifb_subgrad_real hP (hIFB k).1 hq
  have e1 : inner ℝ (ifbG a b lam u y k) (q - u (k + 1))
      = -inner ℝ (ifbG a b lam u y k) (u (k + 1) - q) := by
    rw [← inner_neg_right, neg_sub]
  have hs' : (Φ (u (k + 1))).toReal - inner ℝ (ifbG a b lam u y k) (u (k + 1) - q)
      ≤ (Φ q).toReal := by
    have := hs
    rw [show ((-((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k)) : H)
      = ifbG a b lam u y k from rfl, e1] at this
    linarith
  have hκ : 0 < (a + b) * lam := by positivity
  have hβ : 0 < 1 + b * lam := by positivity
  have hc := abs_real_inner_le_norm (u (k + 1) - u k) (u k - q)
  have hc' := neg_abs_le (inner ℝ (u (k + 1) - u k) (u k - q))
  have hin : -(‖u (k + 1) - u k‖ * ‖u k - q‖) ≤ inner ℝ (u (k + 1) - u k) (u k - q) := by
    linarith
  have hm1 := mul_le_mul_of_nonneg_left hin hβ.le
  have key := ifb_amgm (β := 1 + b * lam) (s := ‖u (k + 1) - u k‖) (t := ‖u k - q‖) hκ
  have hlb : 0 ≤ lam * (1 + b * lam) := by positivity
  have hm2 := mul_le_mul_of_nonneg_left hs' hlb
  simp only [ifbV]
  nlinarith

open InertialFB.IFB in
theorem ifb_iota_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} (hH : HypothesisH Φ Ψ L a b lam) :
    (⨅ x, theta Φ Ψ x) = (((⨅ x, theta Φ Ψ x).toReal : ℝ) : EReal) := by
  have hP := hH.phi_proper
  obtain ⟨m, hm⟩ := hH.theta_bdd_below
  obtain ⟨x0, hx0⟩ := hP.2
  have h1 : (⨅ x, theta Φ Ψ x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (iInf_le _ x0)
    rw [ifb_theta_eq hP hx0]
    exact EReal.coe_ne_top _
  have h2 : (⨅ x, theta Φ Ψ x) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) (le_iInf hm)
  exact (EReal.coe_toReal h1 h2).symm

open InertialFB.IFB in
theorem ifb_low {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} (hH : HypothesisH Φ Ψ L a b lam) {z : H}
    (hz : Φ z ≠ ⊤) : (⨅ x, theta Φ Ψ x).toReal ≤ (Φ z).toReal + Ψ z := by
  have h : (⨅ x, theta Φ Ψ x) ≤ theta Φ Ψ z := iInf_le _ z
  rw [ifb_iota_eq hH, ifb_theta_eq hH.phi_proper hz, EReal.coe_le_coe_iff] at h
  exact h

open InertialFB.IFB in
theorem ifb_S_val {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} (hH : HypothesisH Φ Ψ L a b lam) {q : H}
    (hq : q ∈ argminSet Φ Ψ) : (Φ q).toReal + Ψ q ≤ (⨅ x, theta Φ Ψ x).toReal := by
  have hP := hH.phi_proper
  have hqf := ifb_S_fin hP hq
  have h1 : theta Φ Ψ q ≤ ⨅ x, theta Φ Ψ x := le_iInf hq
  rw [ifb_iota_eq hH, ifb_theta_eq hP hqf, EReal.coe_le_coe_iff] at h1
  exact h1

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
theorem ifb_anchor_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) {q : H} (hq : Φ q ≠ ⊤)
    (N : ℕ) :
    ∑ k ∈ Finset.range N, b * lam ^ 2 * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))
        - ((Φ q).toReal + Ψ q))
      ≤ ifbV a b lam Φ u y q 0 - ifbV a b lam Φ u y q N
        + ((a + b) * lam / 2 + (1 - a * lam)) * ∑ k ∈ Finset.range N, ‖u (k + 1) - u k‖ ^ 2
        + lam * (1 + b * lam) * ∑ k ∈ Finset.range N, ifbD a b lam u y k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add]
    have := ifb_anchor hH hIFB hq N
    linarith

open InertialFB.IFB in
theorem ifb_theta_lim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    Tendsto (fun k => (Φ (u (k + 1))).toReal + Ψ (u (k + 1))) atTop
      (𝓝 (⨅ x, theta Φ Ψ x).toReal) := by
  have hP := hH.phi_proper
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hι := ifb_iota_eq hH
  obtain ⟨BX, BD, hBX, hBD, hD0, hXk, hEanti⟩ := ifb_sums hH hIFB
  rw [tendsto_order]
  refine ⟨fun a' ha' => Eventually.of_forall fun k => lt_of_lt_of_le ha' (ifb_low hH (hIFB k).1.1),
    fun a' ha' => ?_⟩
  have hε : 0 < a' - (⨅ x, theta Φ Ψ x).toReal := sub_pos.2 ha'
  have hlt : (⨅ x, theta Φ Ψ x)
      < (((⨅ x, theta Φ Ψ x).toReal + (a' - (⨅ x, theta Φ Ψ x).toReal) / 2 : ℝ) : EReal) :=
    lt_of_eq_of_lt hι (EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨q, hq⟩ := iInf_lt_iff.1 hlt
  have hqtop : Φ q ≠ ⊤ := by
    intro htop
    rw [ifb_theta_top htop] at hq
    exact (not_lt.2 le_top) hq
  rw [ifb_theta_eq hP hqtop, EReal.coe_lt_coe_iff] at hq
  have hC2 : 0 ≤ (a + b) * lam / 2 + (1 - a * lam) := by
    have : 0 < (a + b) * lam := by positivity
    linarith
  have hbound : ∀ N : ℕ, ((N : ℝ) + 1) * (b * lam ^ 2 * ((Φ (u (N + 1))).toReal + Ψ (u (N + 1)))
      - b * lam ^ 2 * ((Φ q).toReal + Ψ q)) ≤
      ifbV a b lam Φ u y q 0 + ((1 + b * lam) ^ 2 / ((a + b) * lam) * BX
        + lam * (1 + b * lam) * (Φ q).toReal)
      + ((a + b) * lam / 2 + (1 - a * lam)) * BX + lam * (1 + b * lam) * BD
      + (1 - a * lam) / 2 * BX := by
    intro N
    have hθE : b * lam ^ 2 * ((Φ (u (N + 1))).toReal + Ψ (u (N + 1)))
        ≤ ifbE Φ Ψ a b lam u N := by
      simp only [ifbE]
      have := mul_nonneg hal.le (sq_nonneg ‖u (N + 1) - u N‖)
      linarith
    have h1 : ((N : ℝ) + 1) * (ifbE Φ Ψ a b lam u N - b * lam ^ 2 * ((Φ q).toReal + Ψ q)) ≤
        ∑ k ∈ Finset.range (N + 1),
          (ifbE Φ Ψ a b lam u k - b * lam ^ 2 * ((Φ q).toReal + Ψ q)) := by
      have := Finset.card_nsmul_le_sum (Finset.range (N + 1))
        (fun k => ifbE Φ Ψ a b lam u k - b * lam ^ 2 * ((Φ q).toReal + Ψ q))
        (ifbE Φ Ψ a b lam u N - b * lam ^ 2 * ((Φ q).toReal + Ψ q))
        (fun k hk => by
          have := hEanti (Finset.mem_range_succ_iff.1 hk)
          linarith)
      rw [Finset.card_range, nsmul_eq_mul] at this
      push_cast at this
      exact this
    have h2 : ∑ k ∈ Finset.range (N + 1),
          (ifbE Φ Ψ a b lam u k - b * lam ^ 2 * ((Φ q).toReal + Ψ q)) =
        ∑ k ∈ Finset.range (N + 1), b * lam ^ 2 * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))
          - ((Φ q).toReal + Ψ q))
        + (1 - a * lam) / 2 * ∑ k ∈ Finset.range (N + 1), ‖u (k + 1) - u k‖ ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [ifbE]
      ring
    have h3 := ifb_anchor_sum hH hIFB hqtop (N + 1)
    have h4 := ifb_Vlower hH hIFB hqtop (N + 1)
    have h6 := mul_le_mul_of_nonneg_left (hXk (N + 1))
      (by positivity : (0:ℝ) ≤ (1 + b * lam) ^ 2 / ((a + b) * lam))
    have h7 : 0 ≤ (a + b) * lam / 4 * ‖u (N + 1) - q‖ ^ 2 := by positivity
    have h8 := mul_le_mul_of_nonneg_left (hBX (N + 1)) hC2
    have h9 := mul_le_mul_of_nonneg_left (hBD (N + 1))
      (by positivity : (0:ℝ) ≤ lam * (1 + b * lam))
    have h10 := mul_le_mul_of_nonneg_left (hBX (N + 1)) (by linarith : (0:ℝ) ≤ (1 - a * lam) / 2)
    have h11 := mul_le_mul_of_nonneg_left hθE (by positivity : (0:ℝ) ≤ (N:ℝ) + 1)
    linarith
  have hpos : 0 < b * lam ^ 2 * ((a' - (⨅ x, theta Φ Ψ x).toReal) / 2) :=
    mul_pos (by positivity) (by linarith)
  obtain ⟨N0, hN0⟩ := exists_nat_gt ((ifbV a b lam Φ u y q 0 + ((1 + b * lam) ^ 2 / ((a + b) * lam) * BX
        + lam * (1 + b * lam) * (Φ q).toReal)
      + ((a + b) * lam / 2 + (1 - a * lam)) * BX + lam * (1 + b * lam) * BD
      + (1 - a * lam) / 2 * BX) / (b * lam ^ 2 * ((a' - (⨅ x, theta Φ Ψ x).toReal) / 2)))
  refine eventually_atTop.2 ⟨N0, fun N hN => ?_⟩
  rw [div_lt_iff₀ hpos] at hN0
  have hN' : (N0 : ℝ) ≤ N := Nat.cast_le.2 hN
  have hB := hbound N
  have hmul := mul_le_mul_of_nonneg_right hN' hpos.le
  have h1 : ((N : ℝ) + 1) * (b * lam ^ 2 * ((Φ (u (N + 1))).toReal + Ψ (u (N + 1))
      - ((Φ q).toReal + Ψ q))) < ((N : ℝ) + 1) * (b * lam ^ 2 * ((a' - (⨅ x, theta Φ Ψ x).toReal) / 2)) := by
    nlinarith
  have h2 := lt_of_mul_lt_mul_left h1 (by positivity)
  have h3 := lt_of_mul_lt_mul_left h2 (by positivity)
  linarith

open InertialFB.IFB in
theorem ifb_X_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    Tendsto (fun k => u (k + 1) - u k) atTop (𝓝 0) := by
  obtain ⟨BX, BD, hBX, -, -, -, -⟩ := ifb_sums hH hIFB
  have hs : Summable (fun k => ‖u (k + 1) - u k‖ ^ 2) :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) hBX
  have h1 := hs.tendsto_atTop_zero
  have h2 : Tendsto (fun k => ‖u (k + 1) - u k‖) atTop (𝓝 0) := by
    simpa [Real.sqrt_sq_eq_abs] using h1.sqrt
  exact tendsto_zero_iff_norm_tendsto_zero.2 h2

open InertialFB.IFB in
theorem ifb_W_rec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) (k : ℕ) :
    ifbG a b lam u y (k + 1) + gradient Ψ (u (k + 1 + 1)) =
      (1 / (1 + b * lam)) • (ifbG a b lam u y k + gradient Ψ (u (k + 1)))
      + (gradient Ψ (u (k + 1 + 1)) - gradient Ψ (u (k + 1)))
      - (1 / lam) • (u (k + 1 + 1) - u (k + 1))
      + ((1 - a * lam) / (lam * (1 + b * lam))) • (u (k + 1) - u k) := by
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have hR := ifb_R (ne_of_gt hlam) hIFB k
  have h1 : (1 + b * lam) ≠ 0 := by positivity
  have h2 : lam ≠ 0 := ne_of_gt hlam
  linear_combination (norm := skip) (1 / (lam * (1 + b * lam))) • hR
  match_scalars <;> field_simp <;> ring

open InertialFB.IFB in
theorem ifb_W_tendsto {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    Tendsto (fun k => ifbG a b lam u y k + gradient Ψ (u (k + 1))) atTop (𝓝 0) := by
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hL := hH.L_pos
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hX := ifb_X_tendsto hH hIFB
  have hXn : Tendsto (fun k => ‖u (k + 1) - u k‖) atTop (𝓝 0) := by simpa using hX.norm
  have hXn1 : Tendsto (fun k => ‖u (k + 1 + 1) - u (k + 1)‖) atTop (𝓝 0) :=
    hXn.comp (tendsto_add_atTop_nat 1)
  have hβ : 0 < 1 + b * lam := by positivity
  have hc3 : 0 ≤ (1 - a * lam) / (lam * (1 + b * lam)) := div_nonneg hal.le (by positivity)
  apply tendsto_zero_iff_norm_tendsto_zero.2
  refine ifb_contract (ρ := 1 / (1 + b * lam))
    (η := fun k => L * ‖u (k + 1 + 1) - u (k + 1)‖ + 1 / lam * ‖u (k + 1 + 1) - u (k + 1)‖
      + (1 - a * lam) / (lam * (1 + b * lam)) * ‖u (k + 1) - u k‖)
    (by positivity) ?_ (fun k => norm_nonneg _) ?_ ?_
  · rw [div_lt_one hβ]
    linarith [mul_pos hb hlam]
  · intro k
    rw [ifb_W_rec hH hIFB k]
    refine (ifb_norm4 _ _ _ _).trans ?_
    rw [norm_smul, norm_smul, norm_smul,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (1 + b * lam)),
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / lam), Real.norm_of_nonneg hc3]
    have := hH.psi_grad_lipschitz (u (k + 1 + 1)) (u (k + 1))
    linarith
  · have := ((hXn1.const_mul L).add (hXn1.const_mul (1 / lam))).add
      (hXn.const_mul ((1 - a * lam) / (lam * (1 + b * lam))))
    simpa using this

open InertialFB.IFB in
theorem ifb_cluster_S {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) {σ : ℕ → ℕ}
    (hσ : StrictMono σ) {p : H} (hw : WeakTendsto (u ∘ σ) p) :
    p ∈ argminSet Φ Ψ ∧ WeakTendsto (fun j => u (σ j + 1)) p := by
  have hP := hH.phi_proper
  have hι := ifb_iota_eq hH
  have hlim := ifb_theta_lim hH hIFB
  have hX := ifb_X_tendsto hH hIFB
  have hw1 : WeakTendsto (fun j => u (σ j + 1)) p := by
    intro v
    have h1 := hw v
    have h2 : Tendsto (fun j => inner ℝ (u (σ j + 1) - u (σ j)) v) atTop (𝓝 0) := by
      have := Filter.Tendsto.inner (𝕜 := ℝ) (hX.comp hσ.tendsto_atTop)
        (tendsto_const_nhds (x := v))
      simpa using this
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr (fun j => ?_)
    simp only [Function.comp_apply, inner_sub_left]
    ring
  refine ⟨?_, hw1⟩
  have hlsc := ifb_theta_lsc hH.phi_lsc hH.psi_diff.continuous
  have hle : ∀ ε : ℝ, 0 < ε →
      theta Φ Ψ p ≤ (((⨅ x, theta Φ Ψ x).toReal + ε : ℝ) : EReal) := by
    intro ε hε
    have hC : IsClosed {x | theta Φ Ψ x ≤ (((⨅ x, theta Φ Ψ x).toReal + ε : ℝ) : EReal)} :=
      hlsc.isClosed_preimage _
    have hCc := ifb_sublevel_convex hH.theta_convex ((⨅ x, theta Φ Ψ x).toReal + ε)
    refine ifb_weak_closed hC hCc ?_ hw1
    have hev := (hlim.comp hσ.tendsto_atTop).eventually_lt_const
      (show (⨅ x, theta Φ Ψ x).toReal < (⨅ x, theta Φ Ψ x).toReal + ε by linarith)
    filter_upwards [hev] with j hj
    show theta Φ Ψ (u (σ j + 1)) ≤ _
    rw [ifb_theta_eq hP (hIFB (σ j)).1.1, EReal.coe_le_coe_iff]
    exact hj.le
  have hpι : theta Φ Ψ p ≤ (((⨅ x, theta Φ Ψ x).toReal : ℝ) : EReal) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    have hr : (⨅ x, theta Φ Ψ x).toReal < r := EReal.coe_lt_coe_iff.1 hr1
    have := hle (r - (⨅ x, theta Φ Ψ x).toReal) (by linarith)
    rw [show (⨅ x, theta Φ Ψ x).toReal + (r - (⨅ x, theta Φ Ψ x).toReal) = r by ring] at this
    exact absurd (lt_of_lt_of_le hr2 this) (lt_irrefl _)
  intro z
  calc theta Φ Ψ p ≤ (((⨅ x, theta Φ Ψ x).toReal : ℝ) : EReal) := hpι
    _ = ⨅ x, theta Φ Ψ x := hι.symm
    _ ≤ theta Φ Ψ z := iInf_le _ z

open InertialFB.IFB in
theorem ifb_bounded {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y)
    (hne : (argminSet Φ Ψ).Nonempty) : ∃ M, ∀ k, ‖u k‖ ≤ M := by
  obtain ⟨q, hq⟩ := hne
  have hP := hH.phi_proper
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hκ : 0 < (a + b) * lam := by positivity
  have hqf := ifb_S_fin hP hq
  obtain ⟨BX, BD, hBX, hBD, hD0, hXk, -⟩ := ifb_sums hH hIFB
  have hqv := ifb_S_val hH hq
  have hC2 : 0 ≤ (a + b) * lam / 2 + (1 - a * lam) := by linarith
  have hk : ∀ N, (a + b) * lam / 4 * ‖u N - q‖ ^ 2 ≤
      ifbV a b lam Φ u y q 0 + ((a + b) * lam / 2 + (1 - a * lam)) * BX
      + lam * (1 + b * lam) * BD + (1 + b * lam) ^ 2 / ((a + b) * lam) * BX
      + lam * (1 + b * lam) * (Φ q).toReal := by
    intro N
    have h1 := ifb_anchor_sum hH hIFB hqf N
    have h2 : 0 ≤ ∑ k ∈ Finset.range N, b * lam ^ 2 * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))
        - ((Φ q).toReal + Ψ q)) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity)
        (by linarith [ifb_low hH (hIFB k).1.1])
    have h3 := ifb_Vlower hH hIFB hqf N
    have h4 := mul_le_mul_of_nonneg_left (hBX N) hC2
    have h5 := mul_le_mul_of_nonneg_left (hBD N) (by positivity : (0:ℝ) ≤ lam * (1 + b * lam))
    have h6 := mul_le_mul_of_nonneg_left (hXk N)
      (by positivity : (0:ℝ) ≤ (1 + b * lam) ^ 2 / ((a + b) * lam))
    linarith
  refine ⟨‖q‖ + max 1 (4 * (ifbV a b lam Φ u y q 0 + ((a + b) * lam / 2 + (1 - a * lam)) * BX
      + lam * (1 + b * lam) * BD + (1 + b * lam) ^ 2 / ((a + b) * lam) * BX
      + lam * (1 + b * lam) * (Φ q).toReal) / ((a + b) * lam)), fun N => ?_⟩
  have hN := hk N
  have hr : ‖u N - q‖ ≤ max 1 (4 * (ifbV a b lam Φ u y q 0
      + ((a + b) * lam / 2 + (1 - a * lam)) * BX
      + lam * (1 + b * lam) * BD + (1 + b * lam) ^ 2 / ((a + b) * lam) * BX
      + lam * (1 + b * lam) * (Φ q).toReal) / ((a + b) * lam)) := by
    by_cases h1 : ‖u N - q‖ ≤ 1
    · exact h1.trans (le_max_left _ _)
    · push_neg at h1
      refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hκ]
      have h2 : ‖u N - q‖ ≤ ‖u N - q‖ ^ 2 := by nlinarith
      have h3 := mul_le_mul_of_nonneg_left h2 hκ.le
      nlinarith
  calc ‖u N‖ = ‖(u N - q) + q‖ := by rw [sub_add_cancel]
    _ ≤ ‖u N - q‖ + ‖q‖ := norm_add_le _ _
    _ ≤ _ := by linarith

open InertialFB.IFB in
theorem ifb_V_conv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) {q : H}
    (hq : q ∈ argminSet Φ Ψ) : ∃ l, Tendsto (fun k => ifbV a b lam Φ u y q k) atTop (𝓝 l) := by
  have hP := hH.phi_proper
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hκ : 0 < (a + b) * lam := by positivity
  have hqf := ifb_S_fin hP hq
  obtain ⟨BX, BD, hBX, hBD, hD0, hXk, -⟩ := ifb_sums hH hIFB
  have hqv := ifb_S_val hH hq
  have hC2 : 0 ≤ (a + b) * lam / 2 + (1 - a * lam) := by linarith
  refine ifb_qfejer (V := fun k => ifbV a b lam Φ u y q k)
    (ε := fun k => ((a + b) * lam / 2 + (1 - a * lam)) * ‖u (k + 1) - u k‖ ^ 2
      + lam * (1 + b * lam) * ifbD a b lam u y k)
    (m := -((1 + b * lam) ^ 2 / ((a + b) * lam) * BX) - lam * (1 + b * lam) * (Φ q).toReal)
    (B := ((a + b) * lam / 2 + (1 - a * lam)) * BX + lam * (1 + b * lam) * BD) ?_ ?_ ?_ ?_
  · intro k
    have h1 := ifb_anchor hH hIFB hqf k
    have h2 : 0 ≤ b * lam ^ 2 * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))
        - ((Φ q).toReal + Ψ q)) :=
      mul_nonneg (by positivity) (by linarith [ifb_low hH (hIFB k).1.1])
    linarith
  · intro k
    have h1 := mul_nonneg hC2 (sq_nonneg ‖u (k + 1) - u k‖)
    have h2 := mul_nonneg (by positivity : (0:ℝ) ≤ lam * (1 + b * lam)) (hD0 k)
    linarith
  · intro N
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hBX N) hC2
    have h2 := mul_le_mul_of_nonneg_left (hBD N) (by positivity : (0:ℝ) ≤ lam * (1 + b * lam))
    linarith
  · intro k
    have h1 := ifb_Vlower hH hIFB hqf k
    have h3 := mul_le_mul_of_nonneg_left (hXk k)
      (by positivity : (0:ℝ) ≤ (1 + b * lam) ^ 2 / ((a + b) * lam))
    have h4 : 0 ≤ (a + b) * lam / 4 * ‖u k - q‖ ^ 2 := by positivity
    linarith

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

/-- The partial sum `S_k = Φ(u_{k+1}) + ∑_{i=2}^{k+1} ⟪z_i, ξ_i⟫`. -/
noncomputable def ifb8S {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (a b lam : ℝ) (u y : ℕ → H) (k : ℕ) : ℝ :=
  (Φ (u (k + 1))).toReal +
    ∑ i ∈ Finset.Icc 2 (k + 1), inner ℝ (InertialFB.IFB.zSeq a b lam u y i) (InertialFB.IFB.xi u i)

open InertialFB.IFB in
theorem ifb8_F_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (a b lam : ℝ) (hlam : lam ≠ 0) (u y : ℕ → H) (q : H) (k : ℕ) :
    auxF a b lam u y k q = (ifbV a b lam Φ u y q k + lam * (1 + b * lam) * ifb8S Φ a b lam u y k
      - lam ^ 2 * deltaC a b lam * ∑ i ∈ Finset.Icc 2 k, ‖xi u i‖ ^ 2) / lam ^ 2 := by
  unfold auxF auxG ifbV ifb8S alphaC
  rw [ifb28_z_eq, ifb28_xi_eq, inner_neg_left]
  field_simp
  ring

open InertialFB.IFB in
theorem ifb8_S_conv {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    ∃ l, Tendsto (fun k => ifb8S Φ a b lam u y k) atTop (𝓝 l) := by
  obtain ⟨BX, BD, hBX, hBD, hD0, hXk, -⟩ := ifb_sums hH hIFB
  refine ifb_qfejer (ε := fun _ => 0) (B := 0)
    (m := (Φ (u 1)).toReal - BD) ?_ (fun _ => le_rfl) (fun N => by simp) ?_
  · intro k
    unfold ifb8S
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1 + 1), ifb28_z_eq, ifb28_xi_eq,
      inner_neg_left]
    have hs := ifb_subgrad_real hH.phi_proper (hIFB (k + 1)).1 (hIFB k).1.1
    have hg : ifbG a b lam u y (k + 1)
        = -((1 / lam) • (u (k + 1 + 1) - u (k + 1)) + a • u (k + 1) - b • y (k + 1)) := rfl
    rw [← hg] at hs
    have e : inner ℝ (ifbG a b lam u y (k + 1)) (u (k + 1) - u (k + 1 + 1))
        = -inner ℝ (ifbG a b lam u y (k + 1)) (u (k + 1 + 1) - u (k + 1)) := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at hs
    linarith
  · intro k
    unfold ifb8S
    have h1 := ifb28_zsum hH hIFB k
    have h2 := hBD k
    linarith

open Filter Topology InertialFB.IFB in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (Ψ : H → ℝ) (L a b lam : ℝ)
    (hH : HypothesisH Φ Ψ L a b lam) (u y : ℕ → H) (hIFB : IsIFBSeq Φ Ψ a b lam u y)
    (hS : (argminSet Φ Ψ).Nonempty) :
    (∃ R : ℝ, ∀ k : ℕ, ‖u k‖ ≤ R) ∧
    ∀ q ∈ argminSet Φ Ψ, ∃ ℓ : ℝ, Tendsto (fun k => auxF a b lam u y k q) atTop (𝓝 ℓ) := by
  refine ⟨ifb_bounded hH hIFB hS, fun q hq => ?_⟩
  have hlam := hH.lam_pos
  obtain ⟨BX, BD, hBX, hBD, hD0, hXk, -⟩ := ifb_sums hH hIFB
  obtain ⟨lV, hV⟩ := ifb_V_conv hH hIFB hq
  obtain ⟨lS, hSc⟩ := ifb8_S_conv hH hIFB
  have hT : ∃ lT, Tendsto (fun k => ∑ i ∈ Finset.Icc 2 k, ‖xi u i‖ ^ 2) atTop (𝓝 lT) := by
    obtain ⟨l, hl⟩ := ifb_qfejer (V := fun k => -∑ i ∈ Finset.Icc 2 k, ‖xi u i‖ ^ 2)
      (ε := fun _ => 0) (B := 0) (m := -BX) (fun k => by
        have : ∑ i ∈ Finset.Icc 2 k, ‖xi u i‖ ^ 2 ≤ ∑ i ∈ Finset.Icc 2 (k + 1), ‖xi u i‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl (by omega))
            (fun _ _ _ => by positivity)
        linarith) (fun _ => le_rfl) (fun N => by simp) (fun k => by
        simp only [neg_le_neg_iff]
        cases k with
        | zero =>
          rw [show Finset.Icc 2 0 = (∅ : Finset ℕ) from rfl, Finset.sum_empty]
          have := hBX 0
          simpa using this
        | succ m => exact (ifb28_xisum u m).trans (hBX (m + 1)))
    exact ⟨-l, by simpa using hl.neg⟩
  obtain ⟨lT, hTc⟩ := hT
  refine ⟨(lV + lam * (1 + b * lam) * lS - lam ^ 2 * deltaC a b lam * lT) / lam ^ 2, ?_⟩
  have h := ((hV.add (hSc.const_mul (lam * (1 + b * lam)))).sub
    (hTc.const_mul (lam ^ 2 * deltaC a b lam))).div_const (lam ^ 2)
  refine h.congr (fun k => ?_)
  rw [ifb8_F_eq Φ a b lam hlam.ne' u y q k]
