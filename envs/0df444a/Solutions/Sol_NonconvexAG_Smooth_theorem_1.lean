-- Prove2me | solution 1 for NonconvexAG.Smooth.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T07:47:35.524954+00:00
-- url     : https://prove2.me/submissions/9dcfd744-c72f-4083-9bb6-e69d0956135f

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_NonconvexAG_Smooth_AGRun

set_option autoImplicit false

open scoped InnerProductSpace RealInnerProductSpace

namespace AG789

theorem ag_line_deriv {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

theorem ag_descent {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : V) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := ag_line_deriv hF x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪G x, w⟫) ⟪G x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪G x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪G (x + c • w), w⟫ - ⟪G x, w⟫ = ⟪G (x + c • w) - G x, w⟫ := by
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


theorem ag_convex_fo {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] {F : V → ℝ} {G : V → V} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : V) :
    F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x with hw
  let φ : ℝ → ℝ := fun s => F (x + s • w)
  have hφc : ConvexOn ℝ Set.univ φ := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ p q hp hq hpq
    have h := hc.2 (Set.mem_univ (x + a • w)) (Set.mem_univ (x + b • w)) hp hq hpq
    have e : p • (x + a • w) + q • (x + b • w) = x + (p • a + q • b) • w := by
      have : p • (x + a • w) + q • (x + b • w) = (p + q) • x + (p * a + q * b) • w := by
        module
      rw [this, hpq, one_smul, smul_eq_mul, smul_eq_mul]
    show F (x + (p • a + q • b) • w) ≤ p • F (x + a • w) + q • F (x + b • w)
    rw [← e]
    exact h
  have hd := ag_line_deriv hF x w 0
  rw [zero_smul, add_zero] at hd
  have hs := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  rw [slope_def_field] at hs
  have h1 : φ 1 = F y := by
    show F (x + (1:ℝ) • w) = F y
    rw [one_smul, hw, add_sub_cancel]
  have h0 : φ 0 = F x := by
    show F (x + (0:ℝ) • w) = F x
    rw [zero_smul, add_zero]
  rw [h1, h0] at hs
  norm_num at hs
  linarith

open NonconvexAG.Smooth

section run
variable {n : ℕ} (g : E n → E n) (α β lam : ℕ → ℝ) (x0 : E n)

theorem x_succ (k : ℕ) : xSeq g α β lam x0 (k + 1) =
    xSeq g α β lam x0 k - lam (k + 1) • g (xmdSeq g α β lam x0 (k + 1)) := rfl

theorem xag_succ (k : ℕ) : xagSeq g α β lam x0 (k + 1) =
    xmdSeq g α β lam x0 (k + 1) - β (k + 1) • g (xmdSeq g α β lam x0 (k + 1)) := rfl

theorem xmd_succ (k : ℕ) : xmdSeq g α β lam x0 (k + 1) =
    (1 - α (k + 1)) • xagSeq g α β lam x0 k + α (k + 1) • xSeq g α β lam x0 k := rfl

theorem x_zero : xSeq g α β lam x0 0 = x0 := rfl

theorem xag_zero : xagSeq g α β lam x0 0 = x0 := rfl

theorem D_succ (k : ℕ) : xagSeq g α β lam x0 (k + 1) - xSeq g α β lam x0 (k + 1) =
    (1 - α (k + 1)) • (xagSeq g α β lam x0 k - xSeq g α β lam x0 k)
      + (lam (k + 1) - β (k + 1)) • g (xmdSeq g α β lam x0 (k + 1)) := by
  rw [xag_succ, x_succ]
  generalize g (xmdSeq g α β lam x0 (k + 1)) = G
  rw [xmd_succ]
  module

theorem Gamma_zero : Gamma α 0 = 1 := by
  unfold Gamma; rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty]

theorem Gamma_one : Gamma α 1 = 1 := by
  unfold Gamma; rw [Finset.Icc_eq_empty (by norm_num), Finset.prod_empty]

theorem Gamma_succ (k : ℕ) (hk : 1 ≤ k) : Gamma α (k + 1) = Gamma α k * (1 - α (k + 1)) := by
  unfold Gamma; rw [Finset.prod_Icc_succ_top (by omega)]

variable {α β lam} in
theorem alpha_pos (h : AGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) : 0 < α k := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · have : k = 1 := by omega
    subst this; rw [h.1]; norm_num
  · exact (h.2.1 k h2).1

variable {α β lam} in
theorem alpha_le_one (h : AGStepsizes α β lam) (k : ℕ) (hk : 1 ≤ k) : α k ≤ 1 := by
  rcases Nat.lt_or_ge k 2 with h2 | h2
  · have : k = 1 := by omega
    subst this; rw [h.1]
  · exact (h.2.1 k h2).2.le

variable {α β lam} in
theorem Gamma_pos (h : AGStepsizes α β lam) (k : ℕ) : 0 < Gamma α k :=
  Finset.prod_pos fun i hi => by
    have := (h.2.1 i (Finset.mem_Icc.1 hi).1).2
    linarith

noncomputable def S (k : ℕ) : ℝ :=
  ∑ τ ∈ Finset.Icc 1 k, (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2

theorem S_succ (k : ℕ) : S g α β lam x0 (k + 1) = S g α β lam x0 k +
    (lam (k + 1) - β (k + 1)) ^ 2 / (Gamma α (k + 1) * α (k + 1)) *
      ‖g (xmdSeq g α β lam x0 (k + 1))‖ ^ 2 := by
  unfold S; rw [Finset.sum_Icc_succ_top (by omega)]

variable {α β lam} in
theorem S_term_nonneg (h : AGStepsizes α β lam) (τ : ℕ) (hτ : 1 ≤ τ) :
    0 ≤ (lam τ - β τ) ^ 2 / (Gamma α τ * α τ) * ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2 :=
  mul_nonneg (div_nonneg (sq_nonneg _) (mul_pos (Gamma_pos h τ) (alpha_pos h τ hτ)).le)
    (sq_nonneg _)

variable {α β lam} in
theorem S_nonneg (h : AGStepsizes α β lam) (k : ℕ) : 0 ≤ S g α β lam x0 k :=
  Finset.sum_nonneg fun τ hτ => S_term_nonneg g x0 h τ (Finset.mem_Icc.1 hτ).1

variable {α β lam} in
theorem D_bound (h : AGStepsizes α β lam) (k : ℕ) :
    ‖xagSeq g α β lam x0 k - xSeq g α β lam x0 k‖ ^ 2 ≤ Gamma α k * S g α β lam x0 k := by
  induction k with
  | zero => simp [xag_zero, x_zero, S]
  | succ k ih =>
    rw [D_succ, S_succ]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [h.1, Gamma_one, xag_zero, x_zero, S, norm_smul, mul_pow]
    · have ha0 := alpha_pos h (k + 1) (by omega)
      have ha1 : α (k + 1) < 1 := (h.2.1 (k + 1) (by omega)).2
      rw [Gamma_succ α k hk]
      have hΓ := Gamma_pos h k
      have hSk := S_nonneg g x0 h k
      set a := α (k + 1)
      set u := xagSeq g α β lam x0 k - xSeq g α β lam x0 k
      set G := g (xmdSeq g α β lam x0 (k + 1))
      set c := lam (k + 1) - β (k + 1)
      set Γ := Gamma α k
      set Sk := S g α β lam x0 k
      have hne1 : (1 - a) ≠ 0 := (sub_pos.2 ha1).ne'
      have hne2 : a ≠ 0 := ha0.ne'
      have hne3 : Γ ≠ 0 := hΓ.ne'
      have hexp : ‖(1 - a) • u + c • G‖ ^ 2 =
          (1 - a) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - a) * c) * ⟪u, G⟫ + c ^ 2 * ‖G‖ ^ 2 := by
        rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
          mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
        ring
      have h0 : 0 ≤ a ^ 2 * ‖u‖ ^ 2 - 2 * (a * c) * ⟪u, G⟫ + c ^ 2 * ‖G‖ ^ 2 := by
        have : ‖a • u - c • G‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 - 2 * (a * c) * ⟪u, G⟫ + c ^ 2 * ‖G‖ ^ 2 := by
          rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
            mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
          ring
        rw [← this]; positivity
      have hrhs : Γ * (1 - a) * (Sk + c ^ 2 / (Γ * (1 - a) * a) * ‖G‖ ^ 2) =
          (1 - a) * (Γ * Sk) + c ^ 2 * ‖G‖ ^ 2 / a := by
        field_simp
      rw [hexp, hrhs]
      have key : (1 - a) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - a) * c) * ⟪u, G⟫ + c ^ 2 * ‖G‖ ^ 2 ≤
          (1 - a) * ‖u‖ ^ 2 + c ^ 2 * ‖G‖ ^ 2 / a := by
        rw [← sub_nonneg]
        have : (1 - a) * ‖u‖ ^ 2 + c ^ 2 * ‖G‖ ^ 2 / a -
            ((1 - a) ^ 2 * ‖u‖ ^ 2 + 2 * ((1 - a) * c) * ⟪u, G⟫ + c ^ 2 * ‖G‖ ^ 2) =
            (1 - a) / a * (a ^ 2 * ‖u‖ ^ 2 - 2 * (a * c) * ⟪u, G⟫ + c ^ 2 * ‖G‖ ^ 2) := by
          field_simp
          ring
        rw [this]
        exact mul_nonneg (div_nonneg (by linarith) ha0.le) h0
      have := mul_le_mul_of_nonneg_left ih (show (0:ℝ) ≤ 1 - a by linarith)
      linarith

theorem stepA {Ψ : E n → ℝ} {L : ℝ} (hsm : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    (hL : 0 < L) (j : ℕ) (hlam : 0 ≤ lam (j + 1)) :
    Ψ (xSeq g α β lam x0 (j + 1)) ≤ Ψ (xSeq g α β lam x0 j)
      - lam (j + 1) * (1 - L * lam (j + 1)) * ‖g (xmdSeq g α β lam x0 (j + 1))‖ ^ 2
      + L / 2 * (1 - α (j + 1)) ^ 2 * ‖xagSeq g α β lam x0 j - xSeq g α β lam x0 j‖ ^ 2 := by
  have hd := ag_descent hsm.2.1 hsm.2.2 (xSeq g α β lam x0 j) (xSeq g α β lam x0 (j + 1))
  have hmd := xmd_succ g α β lam x0 j
  rw [x_succ] at hd ⊢
  set X := xSeq g α β lam x0 j
  set A := xagSeq g α β lam x0 j
  set md := xmdSeq g α β lam x0 (j + 1)
  set G := g md
  set a := α (j + 1)
  set l := lam (j + 1)
  have e1 : X - l • G - X = -(l • G) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hlam] at hd
  have hXmd : X - md = (1 - a) • (X - A) := by rw [hmd]; module
  have h1 : ‖g X - G‖ ≤ L * (|1 - a| * ‖A - X‖) := by
    have := hsm.2.2 X md
    rwa [hXmd, norm_smul, Real.norm_eq_abs, norm_sub_rev X A] at this
  have h2 : -⟪g X - G, G⟫ ≤ ‖g X - G‖ * ‖G‖ := (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
  have h3 : l * ⟪g X, G⟫ = l * ‖G‖ ^ 2 + l * ⟪g X - G, G⟫ := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
  have key : l * (‖g X - G‖ * ‖G‖) ≤ L * l ^ 2 / 2 * ‖G‖ ^ 2 + ‖g X - G‖ ^ 2 / (2 * L) := by
    rw [← sub_nonneg]
    have : L * l ^ 2 / 2 * ‖G‖ ^ 2 + ‖g X - G‖ ^ 2 / (2 * L) - l * (‖g X - G‖ * ‖G‖) =
        (L * l * ‖G‖ - ‖g X - G‖) ^ 2 / (2 * L) := by
      field_simp; ring
    rw [this]; positivity
  have h4 : ‖g X - G‖ ^ 2 / (2 * L) ≤ L / 2 * (1 - a) ^ 2 * ‖A - X‖ ^ 2 := by
    have hsq : ‖g X - G‖ ^ 2 ≤ (L * (|1 - a| * ‖A - X‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [div_le_iff₀ (by positivity)]
    have : (L * (|1 - a| * ‖A - X‖)) ^ 2 = L / 2 * (1 - a) ^ 2 * ‖A - X‖ ^ 2 * (2 * L) := by
      rw [mul_pow, mul_pow, sq_abs]; field_simp
    linarith
  have h5 := mul_le_mul_of_nonneg_left h2 hlam
  nlinarith [h3, hd, key, h4, h5]

variable {α β lam} in
theorem sumA {Ψ : E n → ℝ} {L : ℝ} (hsm : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    (hL : 0 < L) (h : AGStepsizes α β lam) (N : ℕ) :
    Ψ (xSeq g α β lam x0 N) ≤ Ψ x0
      - ∑ k ∈ Finset.Icc 1 N, lam k * (1 - L * lam k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
      + L / 2 * ∑ k ∈ Finset.Icc 1 N, Gamma α k * S g α β lam x0 k := by
  induction N with
  | zero => simp [x_zero]
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    have hs := stepA g α β lam x0 hsm hL N (h.2.2.2 (N + 1) (by omega)).le
    have hb : (1 - α (N + 1)) ^ 2 * ‖xagSeq g α β lam x0 N - xSeq g α β lam x0 N‖ ^ 2 ≤
        Gamma α (N + 1) * S g α β lam x0 (N + 1) := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simp only [xag_zero, x_zero, sub_self, norm_zero]
        have := mul_nonneg (Gamma_pos h (0 + 1)).le (S_nonneg g x0 h (0 + 1))
        simpa using this
      · have hD := D_bound g x0 h N
        have ha0 := alpha_pos h (N + 1) (by omega)
        have ha1 := alpha_le_one h (N + 1) (by omega)
        have hSmono : S g α β lam x0 N ≤ S g α β lam x0 (N + 1) := by
          rw [S_succ]
          have := S_term_nonneg g x0 h (N + 1) (by omega)
          linarith
        rw [Gamma_succ α N hN]
        have hΓ := Gamma_pos h N
        have hS := S_nonneg g x0 h N
        have hGS : 0 ≤ Gamma α N * S g α β lam x0 N := mul_nonneg hΓ.le hS
        calc (1 - α (N + 1)) ^ 2 * ‖xagSeq g α β lam x0 N - xSeq g α β lam x0 N‖ ^ 2
            ≤ (1 - α (N + 1)) ^ 2 * (Gamma α N * S g α β lam x0 N) :=
              mul_le_mul_of_nonneg_left hD (sq_nonneg _)
          _ ≤ (1 - α (N + 1)) * (Gamma α N * S g α β lam x0 N) :=
              mul_le_mul_of_nonneg_right (by nlinarith) hGS
          _ ≤ Gamma α N * (1 - α (N + 1)) * S g α β lam x0 (N + 1) := by
              have := mul_le_mul_of_nonneg_left hSmono
                (mul_nonneg hΓ.le (show (0:ℝ) ≤ 1 - α (N + 1) by linarith))
              linarith
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ L / 2)
    linarith

theorem swap (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, Gamma α k * S g α β lam x0 k =
    ∑ τ ∈ Finset.Icc 1 N, ((lam τ - β τ) ^ 2 / (Gamma α τ * α τ) *
      ‖g (xmdSeq g α β lam x0 τ)‖ ^ 2) * ∑ k ∈ Finset.Icc τ N, Gamma α k := by
  unfold S
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.Icc 1 N) (s' := fun τ => Finset.Icc τ N)]
  · exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => by ring
  · intro k τ; simp only [Finset.mem_Icc]; omega

theorem stepB {Ψ : E n → ℝ} {L : ℝ} (hsm : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    (hconv : ConvexOn ℝ Set.univ Ψ) (x : E n) (j : ℕ) (ha0 : 0 ≤ α (j + 1))
    (ha1 : α (j + 1) ≤ 1) (hlam : 0 < lam (j + 1)) (hab : α (j + 1) * lam (j + 1) ≤ β (j + 1)) :
    Ψ (xagSeq g α β lam x0 (j + 1)) - Ψ x ≤ (1 - α (j + 1)) * (Ψ (xagSeq g α β lam x0 j) - Ψ x)
      + α (j + 1) / (2 * lam (j + 1)) *
        (‖xSeq g α β lam x0 j - x‖ ^ 2 - ‖xSeq g α β lam x0 (j + 1) - x‖ ^ 2)
      - β (j + 1) / 2 * (1 - L * β (j + 1)) * ‖g (xmdSeq g α β lam x0 (j + 1))‖ ^ 2 := by
  have hd := ag_descent hsm.2.1 hsm.2.2 (xmdSeq g α β lam x0 (j + 1)) (xagSeq g α β lam x0 (j + 1))
  have c1 := ag_convex_fo hsm.2.1 hconv (xmdSeq g α β lam x0 (j + 1)) x
  have c2 := ag_convex_fo hsm.2.1 hconv (xmdSeq g α β lam x0 (j + 1)) (xagSeq g α β lam x0 j)
  have hmd := xmd_succ g α β lam x0 j
  rw [xag_succ] at hd ⊢
  rw [x_succ]
  set X := xSeq g α β lam x0 j
  set A := xagSeq g α β lam x0 j
  set md := xmdSeq g α β lam x0 (j + 1)
  set G := g md
  set a := α (j + 1)
  set l := lam (j + 1)
  set b := β (j + 1)
  have hb : 0 ≤ b := le_trans (mul_nonneg ha0 hlam.le) hab
  have e1 : md - b • G - md = -(b • G) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hb, real_inner_self_eq_norm_sq] at hd
  have hi : ⟪G, md⟫ = (1 - a) * ⟪G, A⟫ + a * ⟪G, X⟫ := by
    rw [hmd, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [inner_sub_right] at c1 c2
  have k1 := mul_le_mul_of_nonneg_left c1 ha0
  have k2 := mul_le_mul_of_nonneg_left c2 (sub_nonneg.2 ha1)
  have k3 := mul_le_mul_of_nonneg_right hab (sq_nonneg ‖G‖)
  have hn : ‖X - l • G - x‖ ^ 2 = ‖X - x‖ ^ 2 - 2 * l * (⟪G, X⟫ - ⟪G, x⟫) + l ^ 2 * ‖G‖ ^ 2 := by
    have : X - l • G - x = (X - x) - l • G := by abel
    rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hlam, real_inner_comm, inner_sub_right]
    ring
  have ht : a / (2 * l) * (‖X - x‖ ^ 2 - ‖X - l • G - x‖ ^ 2) =
      a * (⟪G, X⟫ - ⟪G, x⟫) - a * l / 2 * ‖G‖ ^ 2 := by
    rw [hn]; field_simp; ring
  rw [ht]
  nlinarith [hd, k1, k2, k3, hi]

variable {α β lam} in
theorem telesc {Ψ : E n → ℝ} {L : ℝ} (hsm : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g L)
    (hconv : ConvexOn ℝ Set.univ Ψ) (h : AGStepsizes α β lam) (x : E n) (N : ℕ)
    (h29 : ∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ β k < 1 / L)
    (h210 : ∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
      α k / (lam k * Gamma α k) ≤ α (k - 1) / (lam (k - 1) * Gamma α (k - 1))) :
    ∀ M, 1 ≤ M → M ≤ N →
      (Ψ (xagSeq g α β lam x0 M) - Ψ x) / Gamma α M
        + 1 / 2 * ∑ k ∈ Finset.Icc 1 M,
            (Gamma α k)⁻¹ * β k * (1 - L * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        + 1 / 2 * (α M / (lam M * Gamma α M)) * ‖xSeq g α β lam x0 M - x‖ ^ 2
      ≤ ‖x0 - x‖ ^ 2 / (2 * lam 1) := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro hN1
    have hl1 := h.2.2.2 1 le_rfl
    have hs := stepB g α β lam x0 hsm hconv x 0 (by rw [zero_add, h.1]; norm_num)
      (by rw [zero_add, h.1]) (h.2.2.2 1 le_rfl)
      (by have := (h29 1 (Finset.mem_Icc.2 ⟨le_rfl, hN1⟩)).1; simpa using this)
    simp only [zero_add, h.1, sub_self, zero_mul, x_zero] at hs
    rw [Finset.Icc_self, Finset.sum_singleton, Gamma_one, h.1]
    have e : 1 / (2 * lam 1) * (‖x0 - x‖ ^ 2 - ‖xSeq g α β lam x0 1 - x‖ ^ 2) =
        ‖x0 - x‖ ^ 2 / (2 * lam 1) - 1 / 2 * (1 / (lam 1 * 1)) * ‖xSeq g α β lam x0 1 - x‖ ^ 2 := by
      field_simp
    rw [e] at hs
    simp only [div_one, inv_one, one_mul] at hs ⊢
    linarith
  | succ M hM ih =>
    intro hMN
    have ih' := ih (by omega)
    have hk := Finset.mem_Icc.2 ⟨(by omega : 1 ≤ M + 1), hMN⟩
    have ha0 := alpha_pos h (M + 1) (by omega)
    have ha1 : α (M + 1) < 1 := (h.2.1 (M + 1) (by omega)).2
    have hl := h.2.2.2 (M + 1) (by omega)
    have hs := stepB g α β lam x0 hsm hconv x M ha0.le ha1.le hl (h29 (M + 1) hk).1
    have hmono := h210 (M + 1) hk (by omega)
    simp only [Nat.add_sub_cancel] at hmono
    rw [Finset.sum_Icc_succ_top (by omega)]
    rw [Gamma_succ α M hM] at hmono ⊢
    have hΓ := Gamma_pos h M
    set Γ := Gamma α M
    set a := α (M + 1)
    set l := lam (M + 1)
    set b := β (M + 1)
    set q := ‖g (xmdSeq g α β lam x0 (M + 1))‖ ^ 2
    set eM := ‖xSeq g α β lam x0 M - x‖ ^ 2
    set eM1 := ‖xSeq g α β lam x0 (M + 1) - x‖ ^ 2
    set DA := Ψ (xagSeq g α β lam x0 M) - Ψ x
    have hpos : 0 < Γ * (1 - a) := mul_pos hΓ (by linarith)
    have hdiv := div_le_div_of_nonneg_right hs hpos.le
    have hne1 : (1 - a) ≠ 0 := (sub_pos.2 ha1).ne'
    have heq : ((1 - a) * DA + a / (2 * l) * (eM - eM1) - b / 2 * (1 - L * b) * q) / (Γ * (1 - a))
        = DA / Γ + 1 / 2 * (a / (l * (Γ * (1 - a)))) * eM
          - 1 / 2 * (a / (l * (Γ * (1 - a)))) * eM1
          - 1 / 2 * ((Γ * (1 - a))⁻¹ * b * (1 - L * b) * q) := by
      field_simp
      ring
    rw [heq] at hdiv
    have hw := mul_le_mul_of_nonneg_right hmono (sq_nonneg ‖xSeq g α β lam x0 M - x‖)
    linarith

end run

end AG789

open NonconvexAG.Smooth in
theorem solution {n : ℕ} (Ψ : E n → ℝ) (g : E n → E n) (LΨ : ℝ)
    (hΨ : ConvexOptAlg.SmoothGD.IsBetaSmooth Ψ g LΨ) (hL : 0 < LΨ)
    (α β lam : ℕ → ℝ) (hstep : AGStepsizes α β lam) (x0 : E n)
    (hbdd : BddBelow (Set.range Ψ)) (N : ℕ) (hN : 1 ≤ N) :
    -- a) under (2.7) for `k = 1, …, N`: (2.8)
    ((∀ k ∈ Finset.Icc 1 N, 0 < C LΨ α β lam N k) →
      (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN) (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) ≤
        (Ψ x0 - ⨅ x, Ψ x) / ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k) ∧
    -- b) `Ψ` convex with a minimizer `x*`, under (2.9) and (2.10) for `k = 1, …, N`: (2.11), (2.12)
    (∀ xstar : E n, ConvexOn ℝ Set.univ Ψ → (∀ x, Ψ xstar ≤ Ψ x) →
      (∀ k ∈ Finset.Icc 1 N, α k * lam k ≤ β k ∧ β k < 1 / LΨ) →
      (∀ k ∈ Finset.Icc 1 N, 2 ≤ k →
        α k / (lam k * Gamma α k) ≤ α (k - 1) / (lam (k - 1) * Gamma α (k - 1))) →
      (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN) (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) ≤
          ‖x0 - xstar‖ ^ 2 /
            (lam 1 * ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k)) ∧
        Ψ (xagSeq g α β lam x0 N) - Ψ xstar ≤ Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1)) := by
  refine ⟨fun hC => ?_, fun xstar hconv hmin h29 h210 => ?_⟩
  · have hsum := AG789.sumA g x0 hΨ hL hstep N
    have hinf : (⨅ x, Ψ x) ≤ Ψ (xSeq g α β lam x0 N) := ciInf_le hbdd _
    have hid : ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        = ∑ k ∈ Finset.Icc 1 N, lam k * (1 - LΨ * lam k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
          - LΨ / 2 * ∑ k ∈ Finset.Icc 1 N, Gamma α k * AG789.S g α β lam x0 k := by
      rw [AG789.swap, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 := (Finset.mem_Icc.1 hk).1
      have := hstep.2.2.2 k hk1
      have := AG789.alpha_pos hstep k hk1
      have := AG789.Gamma_pos hstep k
      unfold C
      field_simp
    have hmain : ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        ≤ Ψ x0 - ⨅ x, Ψ x := by linarith
    have hpos : 0 < ∑ k ∈ Finset.Icc 1 N, lam k * C LΨ α β lam N k :=
      Finset.sum_pos (fun k hk => mul_pos (hstep.2.2.2 k (Finset.mem_Icc.1 hk).1) (hC k hk))
        (Finset.nonempty_Icc.mpr hN)
    rw [le_div_iff₀ hpos, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) hmain
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hk)
      (mul_pos (hstep.2.2.2 k (Finset.mem_Icc.1 hk).1) (hC k hk)).le
  · have htel := AG789.telesc g x0 hΨ hconv hstep xstar N h29 h210 N hN le_rfl
    have hΓN := AG789.Gamma_pos hstep N
    have hT : 0 ≤ (Ψ (xagSeq g α β lam x0 N) - Ψ xstar) / Gamma α N :=
      div_nonneg (sub_nonneg.2 (hmin _)) hΓN.le
    have hW : 0 ≤ 1 / 2 * (α N / (lam N * Gamma α N)) * ‖xSeq g α β lam x0 N - xstar‖ ^ 2 := by
      have := AG789.alpha_pos hstep N hN
      have := hstep.2.2.2 N hN
      positivity
    have hl1 := hstep.2.2.2 1 le_rfl
    have hcpos : ∀ k ∈ Finset.Icc 1 N, 0 < (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) := by
      intro k hk
      have h1 := (h29 k hk).2
      have hb := hstep.2.2.1 k (Finset.mem_Icc.1 hk).1
      have h2 : LΨ * β k < 1 := by rwa [lt_div_iff₀ hL, mul_comm] at h1
      have := AG789.Gamma_pos hstep k
      have : 0 < 1 - LΨ * β k := by linarith
      positivity
    have hsumpos : 0 < ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) :=
      Finset.sum_pos hcpos (Finset.nonempty_Icc.mpr hN)
    have hS : ∑ k ∈ Finset.Icc 1 N,
        (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2
        ≤ ‖x0 - xstar‖ ^ 2 / lam 1 := by
      have : ‖x0 - xstar‖ ^ 2 / (2 * lam 1) = 1 / 2 * (‖x0 - xstar‖ ^ 2 / lam 1) := by
        field_simp
      linarith
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ (mul_pos hl1 hsumpos)]
      have hm : (Finset.Icc 1 N).inf' (Finset.nonempty_Icc.mpr hN)
            (fun k => ‖g (xmdSeq g α β lam x0 k)‖ ^ 2) *
            ∑ k ∈ Finset.Icc 1 N, (Gamma α k)⁻¹ * β k * (1 - LΨ * β k)
          ≤ ∑ k ∈ Finset.Icc 1 N,
            (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hk) (hcpos k hk).le
      have h2 := mul_le_mul_of_nonneg_left (hm.trans hS) hl1.le
      rw [mul_div_cancel₀ _ hl1.ne'] at h2
      nlinarith
    · have hq0 : 0 ≤ ∑ k ∈ Finset.Icc 1 N,
          (Gamma α k)⁻¹ * β k * (1 - LΨ * β k) * ‖g (xmdSeq g α β lam x0 k)‖ ^ 2 :=
        Finset.sum_nonneg fun k hk => mul_nonneg (hcpos k hk).le (sq_nonneg _)
      have h3 : (Ψ (xagSeq g α β lam x0 N) - Ψ xstar) / Gamma α N ≤
          ‖x0 - xstar‖ ^ 2 / (2 * lam 1) := by linarith
      rw [div_le_iff₀ hΓN] at h3
      have e : Gamma α N * ‖x0 - xstar‖ ^ 2 / (2 * lam 1) =
          ‖x0 - xstar‖ ^ 2 / (2 * lam 1) * Gamma α N := by ring
      rw [e]
      exact h3
