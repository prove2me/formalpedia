-- Prove2me | solution 1 for InertialFB.IFB.proposition3_liapunov
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T09:26:02.962501+00:00
-- url     : https://prove2.me/submissions/7f1259e1-0ebf-49f2-b42d-8434504d6f3b

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
theorem ifb_F_diff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (a b lam : ℝ) (hlam : lam ≠ 0) (u y : ℕ → H) (q : H) (k : ℕ) (hk : 1 ≤ k) :
    b * inner ℝ ((1 / lam - a) • xi u (k + 1) + (1 / lam + b) • zeta y (k + 1))
          (u (k + 1) - q) =
        auxF a b lam u y (k + 1) q - auxF a b lam u y k q := by
  have hxi2 : xi u (k + 1 + 1) = u (k + 1 + 1) - u (k + 1) := by simp [xi]
  have hG : auxG a b lam u y (k + 1 + 1) q = auxG a b lam u y (k + 1) q +
      inner ℝ (zSeq a b lam u y (k + 1 + 1) - zSeq a b lam u y (k + 1)) (u (k + 1) - q) := by
    unfold auxG
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ k + 1 + 1)]
    have e1 : u (k + 1 + 1) - q = xi u (k + 1 + 1) + (u (k + 1) - q) := by rw [hxi2]; abel
    rw [e1, inner_add_right, inner_sub_left]
    ring
  have hS : ∑ i ∈ Finset.Icc 2 (k + 1), ‖xi u i‖ ^ 2 =
      ∑ i ∈ Finset.Icc 2 k, ‖xi u i‖ ^ 2 + ‖xi u (k + 1)‖ ^ 2 :=
    Finset.sum_Icc_succ_top (by omega) _
  have hz : zSeq a b lam u y (k + 1 + 1) - zSeq a b lam u y (k + 1) =
      (1 / lam) • xi u (k + 1 + 1) - (1 / lam) • xi u (k + 1) + a • xi u (k + 1) -
        b • zeta y (k + 1) := by
    simp only [zSeq, xi, zeta, Nat.add_sub_cancel]
    module
  have hq : u k - q = (u (k + 1) - q) - xi u (k + 1) := by
    simp only [xi, Nat.add_sub_cancel]; abel
  unfold auxF
  rw [hS, hG, hz, hq]
  generalize xi u (k + 1 + 1) = η
  generalize xi u (k + 1) = ξ
  generalize zeta y (k + 1) = ζ
  generalize u (k + 1) - q = e
  generalize auxG a b lam u y (k + 1) q = G
  generalize ∑ i ∈ Finset.Icc 2 k, ‖xi u i‖ ^ 2 = S
  rw [norm_sub_sq_real e ξ]
  simp only [inner_add_left, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm e ξ]
  unfold alphaC deltaC
  field_simp
  ring

open InertialFB.IFB in
theorem ifb_step_real {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → EReal) (Ψ : H → ℝ) (a b lam : ℝ)
    (hP : IsProperFn Φ) (hΨ : Differentiable ℝ Ψ) (hb : 0 < b)
    (hΘ : IsConvexFn (theta Φ Ψ)) (u y : ℕ → H) (hIFB : IsIFBSeq Φ Ψ a b lam u y)
    (q : H) (k : ℕ) (hq : Φ q ≠ ⊤) :
    b * ((Φ (u (k + 1))).toReal + Ψ (u (k + 1))) +
        b * inner ℝ ((1 / lam - a) • xi u (k + 1) + (1 / lam + b) • zeta y (k + 1))
          (u (k + 1) - q) ≤
      b * ((Φ q).toReal + Ψ q) := by
  obtain ⟨hs, h2⟩ := hIFB k
  have h := ifb_theta_subgrad hP hΨ hΘ hs hq
  have hw : -((1 / lam) • (u (k + 1) - u k) + a • u k - b • y k) + gradient Ψ (u (k + 1)) =
      -((1 / lam - a) • xi u (k + 1) + (1 / lam + b) • zeta y (k + 1)) := by
    simp only [xi, zeta, Nat.add_sub_cancel]
    linear_combination (norm := module) h2
  rw [hw, inner_neg_left, ← neg_sub (u (k + 1)) q, inner_neg_right, neg_neg] at h
  have := mul_le_mul_of_nonneg_left h hb.le
  linarith

open InertialFB.IFB in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → EReal) (Ψ : H → ℝ) (L a b lam : ℝ)
    (hΦ_proper : IsProperFn Φ) (hΦ_lsc : LowerSemicontinuous Φ) (hΦ_convex : IsConvexFn Φ)
    (hΨ_diff : Differentiable ℝ Ψ)
    (hΨ_lip : ∀ x x' : H, ‖gradient Ψ x - gradient Ψ x'‖ ≤ L * ‖x - x'‖)
    (ha : 0 < a) (hb : 0 < b) (hlam : 0 < lam)
    (hΘ_convex : IsConvexFn (theta Φ Ψ))
    (u y : ℕ → H) (hIFB : IsIFBSeq Φ Ψ a b lam u y) :
    (∀ (q : H) (k : ℕ), 1 ≤ k →
      (b : EReal) * theta Φ Ψ (u (k + 1)) +
          ((b * inner ℝ ((1 / lam - a) • xi u (k + 1) + (1 / lam + b) • zeta y (k + 1))
              (u (k + 1) - q) : ℝ) : EReal) ≤
        (b : EReal) * theta Φ Ψ q ∧
      b * inner ℝ ((1 / lam - a) • xi u (k + 1) + (1 / lam + b) • zeta y (k + 1))
          (u (k + 1) - q) =
        auxF a b lam u y (k + 1) q - auxF a b lam u y k q) ∧
    (∀ q ∈ argminSet Φ Ψ, ∀ k : ℕ, 1 ≤ k → auxF a b lam u y (k + 1) q ≤ auxF a b lam u y k q) := by
  refine ⟨fun q k hk => ⟨?_, ifb_F_diff a b lam hlam.ne' u y q k hk⟩, ?_⟩
  · have hu := (hIFB k).1.1
    by_cases hq : Φ q = ⊤
    · rw [ifb_theta_top (Ψ := Ψ) hq, EReal.coe_mul_top_of_pos hb]
      exact le_top
    · rw [ifb_theta_eq hΦ_proper hu, ifb_theta_eq hΦ_proper hq, ← EReal.coe_mul, ← EReal.coe_mul,
        ← EReal.coe_add, EReal.coe_le_coe_iff]
      exact ifb_step_real Φ Ψ a b lam hΦ_proper hΨ_diff hb hΘ_convex u y hIFB q k hq
  · intro q hqS k hk
    have hq := ifb_S_fin hΦ_proper hqS
    have hu := (hIFB k).1.1
    have h1 := ifb_step_real Φ Ψ a b lam hΦ_proper hΨ_diff hb hΘ_convex u y hIFB q k hq
    have hmin := hqS (u (k + 1))
    rw [ifb_theta_eq hΦ_proper hu, ifb_theta_eq hΦ_proper hq, EReal.coe_le_coe_iff] at hmin
    have h2 := mul_le_mul_of_nonneg_left hmin hb.le
    have h3 := ifb_F_diff a b lam hlam.ne' u y q k hk
    nlinarith
