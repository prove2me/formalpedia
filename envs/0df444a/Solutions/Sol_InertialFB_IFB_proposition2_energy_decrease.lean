-- Prove2me | solution 1 for InertialFB.IFB.proposition2_energy_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T06:11:26.055596+00:00
-- url     : https://prove2.me/submissions/35b34543-1543-49b5-b1cf-c1b54a6d94e6

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
theorem ifb_energy_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Φ : H → EReal} {Ψ : H → ℝ} {L a b lam : ℝ} {u y : ℕ → H}
    (hH : HypothesisH Φ Ψ L a b lam) (hIFB : IsIFBSeq Φ Ψ a b lam u y) (k : ℕ) :
    energy Φ Ψ a b lam u (k + 1) = ((ifbE Φ Ψ a b lam u k / (b * lam ^ 2) : ℝ) : EReal) ∧
    theta Φ Ψ (u (k + 1)) = ((ifbE Φ Ψ a b lam u k / (b * lam ^ 2)
      - gammaC a b lam * ‖u (k + 1) - u k‖ ^ 2 : ℝ) : EReal) := by
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ht := ifb_theta_eq (Ψ := Ψ) hH.phi_proper (hIFB k).1.1
  have hx : xi u (k + 1) = u (k + 1) - u k := by simp [xi]
  have hal : ifbE Φ Ψ a b lam u k / (b * lam ^ 2)
      = (Φ (u (k + 1))).toReal + Ψ (u (k + 1)) + gammaC a b lam * ‖u (k + 1) - u k‖ ^ 2 := by
    simp only [ifbE, gammaC]
    field_simp
  constructor
  · simp only [energy, hx]
    rw [ht, ← EReal.coe_add, hal]
  · rw [ht, hal]
    congr 1
    ring

open Filter Topology InertialFB.IFB in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (Ψ : H → ℝ) (L a b lam : ℝ)
    (hH : HypothesisH Φ Ψ L a b lam) (u y : ℕ → H) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    (∀ k : ℕ, 1 ≤ k → energy Φ Ψ a b lam u (k + 1) ≤ energy Φ Ψ a b lam u k) ∧
    Summable (fun k : ℕ => ‖xi u k‖ ^ 2) ∧
    ∃ E : ℝ, Tendsto (fun k => energy Φ Ψ a b lam u k) atTop (𝓝 (E : EReal)) ∧
      Tendsto (fun k => theta Φ Ψ (u k)) atTop (𝓝 (E : EReal)) := by
  obtain ⟨BX, BD, hSX, -, -, -, hanti⟩ := ifb_sums hH hIFB
  have hb := hH.b_pos
  have hlam := hH.lam_pos
  have ha := hH.a_pos
  have hc : 0 < b * lam ^ 2 := by positivity
  have hal : 0 < 1 - a * lam := by
    have := (lt_div_iff₀ ha).1 hH.lam_lt_inv_a
    linarith
  have hγ : 0 ≤ gammaC a b lam := by
    unfold gammaC
    positivity
  set e : ℕ → ℝ := fun k => ifbE Φ Ψ a b lam u k / (b * lam ^ 2) with he
  have heq : ∀ k, energy Φ Ψ a b lam u (k + 1) = ((e k : ℝ) : EReal) :=
    fun k => (ifb_energy_eq hH hIFB k).1
  have hthe : ∀ k, theta Φ Ψ (u (k + 1))
      = ((e k - gammaC a b lam * ‖u (k + 1) - u k‖ ^ 2 : ℝ) : EReal) :=
    fun k => (ifb_energy_eq hH hIFB k).2
  have eanti : Antitone e := fun i j hij => div_le_div_of_nonneg_right (hanti hij) hc.le
  obtain ⟨m, hm⟩ := hH.theta_bdd_below
  have ebdd : ∀ k, m ≤ e k := by
    intro k
    have h1 := hm (u (k + 1))
    rw [hthe k, EReal.coe_le_coe_iff] at h1
    have := mul_nonneg hγ (sq_nonneg ‖u (k + 1) - u k‖)
    linarith
  have hs1 : Summable (fun k : ℕ => ‖u (k + 1) - u k‖ ^ 2) :=
    summable_of_sum_range_le (fun k => sq_nonneg _) hSX
  have hxs : Summable (fun k : ℕ => ‖xi u k‖ ^ 2) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa [xi] using hs1
  have hlim : Tendsto e atTop (𝓝 (⨅ k, e k)) :=
    tendsto_atTop_ciInf eanti ⟨m, by rintro _ ⟨k, rfl⟩; exact ebdd k⟩
  have h0 : Tendsto (fun k : ℕ => ‖u (k + 1) - u k‖ ^ 2) atTop (𝓝 0) := hs1.tendsto_atTop_zero
  refine ⟨?_, hxs, ⨅ k, e k, ?_, ?_⟩
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [heq, heq, EReal.coe_le_coe_iff]
    exact eanti (Nat.le_succ j)
  · refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [heq]
    exact EReal.tendsto_coe.2 hlim
  · refine (tendsto_add_atTop_iff_nat 1).mp ?_
    simp only [hthe]
    refine EReal.tendsto_coe.2 ?_
    have := hlim.sub (h0.const_mul (gammaC a b lam))
    simpa using this
