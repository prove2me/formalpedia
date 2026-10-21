-- Prove2me | solution 1 for HighResODE.NAGC.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T03:50:36.105475+00:00
-- url     : https://prove2.me/submissions/29ec9aa6-7a0a-431b-8d9b-1be8dabbae79

import Mathlib
import Definitions.Def_HighResODE_NAGC_Setting

set_option autoImplicit false

section HlpSec
open scoped InnerProductSpace
open Filter Topology

namespace Hlp
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem inner_grad_eq (f : H → ℝ) (p v : H) : ⟪gradient f p, v⟫_ℝ = fderiv ℝ f p v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem line_hasDeriv {f : H → ℝ} {p : H} (hp : DifferentiableAt ℝ f p) (x v : H) (t : ℝ)
    (hpt : x + t • v = p) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (⟪gradient f p, v⟫_ℝ) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  rw [inner_grad_eq]
  subst hpt
  exact hp.hasFDerivAt.comp_hasDerivAt t h1

theorem convex_ineq {X : Set H} {f : H → ℝ} (hf : ConvexOn ℝ X f)
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have h1 := line_hasDeriv (hd x hx) x (y - x) 0 (by simp)
  have h2 := h1.tendsto_slope_zero_right
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • ((fun s : ℝ => f (x + s • (y - x))) (0 + t) - (fun s : ℝ => f (x + s • (y - x))) 0)
        ≤ f y - f x := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have hc := hf.2 hx hy (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le (by ring : (1 - t) + t = 1)
    have e : (1 - t) • x + t • y = x + t • (y - x) := by module
    rw [e] at hc
    simp only [smul_eq_mul, zero_add, zero_smul, add_zero] at hc ⊢
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto h2 h3
  linarith

theorem line_mem {X : Set (H)} (hX : Convex ℝ X) {x y : H} (hx : x ∈ X) (hy : y ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ X := by
  have := hX hx hy (a := 1 - t) (b := t) (by linarith [ht.2]) ht.1 (by ring)
  convert this using 1
  module

theorem descent {X : Set (H)} (hX : Convex ℝ X) {f : H → ℝ}
    (hd : ∀ x ∈ X, DifferentiableAt ℝ f x) {L : ℝ}
    (hL : ∀ x ∈ X, ∀ y ∈ X, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    {x y : H} (hx : x ∈ X) (hy : y ∈ X) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let g : ℝ → ℝ := fun s => f (x + s • v) - s * ⟪gradient f x, v⟫_ℝ - L / 2 * s ^ 2 * ‖v‖ ^ 2
  have hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g
      (⟪gradient f (x + s • v), v⟫_ℝ - ⟪gradient f x, v⟫_ℝ - L * s * ‖v‖ ^ 2) s := by
    intro s hs
    have hm := Hlp.line_mem hX hx hy hs
    have h1 := Hlp.line_hasDeriv (hd _ hm) x v s rfl
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, v⟫_ℝ) (⟪gradient f x, v⟫_ℝ) s := by
      simpa using (hasDerivAt_id s).mul_const (⟪gradient f x, v⟫_ℝ)
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * s * ‖v‖ ^ 2) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      first | ring | (norm_num; ring) | norm_num
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn g (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s (Set.Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      rw [(hder s hs').deriv]
      have hm := Hlp.line_mem hX hx hy hs'
      have h1 := hL _ hm x hx
      have hn : ‖x + s • v - x‖ = s * ‖v‖ := by
        simp [norm_smul, abs_of_pos hs.1]
      rw [hn] at h1
      have hcs := real_inner_le_norm (gradient f (x + s • v) - gradient f x) v
      rw [inner_sub_left] at hcs
      have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg v)
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have e : x + (1 : ℝ) • v = y := by simp [hv]
  simp only [g, e, zero_smul, add_zero, zero_mul, sub_zero, one_mul, one_pow, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_one] at this
  linarith

theorem cocoercive {f : H → ℝ} (hd : ∀ x, DifferentiableAt ℝ f x) {L : ℝ} (hL0 : 0 < L)
    (hL : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hc : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y) (x y : H) :
    ‖gradient f y - gradient f x‖ ^ 2 ≤ 2 * L * (f y - f x - ⟪gradient f x, y - x⟫_ℝ) := by
  set d := gradient f y - gradient f x with hd'
  set z := y - (1 / L) • d with hz
  have h1 := descent (X := Set.univ) convex_univ (f := f) (fun x _ => hd x) (L := L)
    (fun x _ y _ => hL x y) (x := y) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  have h2 := hc x z
  have e1 : z - y = -((1 / L) • d) := by rw [hz]; abel
  have e2 : z - x = (y - x) - (1 / L) • d := by rw [hz]; abel
  rw [e1] at h1
  rw [e2] at h2
  rw [inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at h1
  rw [inner_sub_right, real_inner_smul_right] at h2
  have h3 : ⟪gradient f y, d⟫_ℝ - ⟪gradient f x, d⟫_ℝ = ‖d‖ ^ 2 := by
    rw [← inner_sub_left, ← hd', real_inner_self_eq_norm_sq]
  have hq : (1 / L) * L = 1 := by field_simp
  have h4 : L * (1 / L) = 1 := by field_simp
  have key : ‖d‖ ^ 2 ≤ 2 * L * (f y - f x - ⟪gradient f x, y - x⟫_ℝ) := by
    have h5 : f x + (⟪gradient f x, y - x⟫_ℝ - 1 / L * ⟪gradient f x, d⟫_ℝ)
        ≤ f y + (-(1 / L * ⟪gradient f y, d⟫_ℝ)) + L / 2 * (1 / L ^ 2 * ‖d‖ ^ 2) := by
      have : (1 / L) ^ 2 = 1 / L ^ 2 := by rw [one_div_pow]
      rw [this] at h1
      linarith
    have h6 : 1 / L * ⟪gradient f y, d⟫_ℝ - 1 / L * ⟪gradient f x, d⟫_ℝ = 1 / L * ‖d‖ ^ 2 := by
      rw [← mul_sub, h3]
    have h7 : L / 2 * (1 / L ^ 2 * ‖d‖ ^ 2) = 1 / (2 * L) * ‖d‖ ^ 2 := by
      field_simp
    have h8 : f x + ⟪gradient f x, y - x⟫_ℝ + 1 / (2 * L) * ‖d‖ ^ 2 ≤ f y := by
      have : 1 / L * ‖d‖ ^ 2 - 1 / (2 * L) * ‖d‖ ^ 2 = 1 / (2 * L) * ‖d‖ ^ 2 := by
        field_simp; ring
      linarith
    have h9 := mul_le_mul_of_nonneg_left h8 (by linarith : (0:ℝ) ≤ 2 * L)
    have h10 : 2 * L * (1 / (2 * L) * ‖d‖ ^ 2) = ‖d‖ ^ 2 := by field_simp
    nlinarith
  exact key


theorem norm_sub_smul_sq (W g : H) (t : ℝ) :
    ‖W - t • g‖ ^ 2 = ‖W‖ ^ 2 - 2 * t * ⟪g, W⟫_ℝ + t ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    ← real_inner_comm W g]
  ring

end Hlp
end HlpSec

open HighResODE.NAGC
open scoped InnerProductSpace

theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : HighResODE.NAGSC.IsF1 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (hsL : s ≤ 1 / (3 * L))
    (x y : ℕ → HighResODE.NAGSC.E n) (hrun : IsNAGC f s x y) :
    ∀ k : ℕ, lyap f s xs x (k + 1) - lyap f s xs x k
      ≤ -(s ^ 2 * (((k : ℝ) + 3) * ((k : ℝ) - 1) - L * s * ((k : ℝ) + 3) * ((k : ℝ) + 1)) / 2)
          * ‖gradient f (x (k + 1))‖ ^ 2 := by
  intro k
  obtain ⟨hLpos, hdiff, hconv, hlip⟩ := hf
  obtain ⟨hinit, hy, hx⟩ := hrun
  have hLs : L * s ≤ 1 / 3 := by
    have := mul_le_mul_of_nonneg_left hsL hLpos.le
    have e : L * (1 / (3 * L)) = 1 / 3 := by field_simp
    linarith
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 < b ∧ s = b ^ 2 :=
    ⟨Real.sqrt s, Real.sqrt_pos.2 hs, (Real.sq_sqrt hs.le).symm⟩
  have hsq : Real.sqrt (b ^ 2) = b := Real.sqrt_sq hb.le
  have hrec : ∀ k : ℕ, x (k + 1 + 1) = x (k + 1) - b ^ 2 • gradient f (x (k + 1))
      + (((k : ℝ) + 1) / ((k : ℝ) + 4)) • (x (k + 1) - x k - b ^ 2 • gradient f (x (k + 1))
        + b ^ 2 • gradient f (x k)) := by
    intro k
    have h := hx (k + 1)
    rw [hy (k + 1), hy k] at h
    rw [h]
    push_cast
    have : ((k : ℝ) + 1 + 3) = (k : ℝ) + 4 := by ring
    rw [this]
    module
  have hk4 : (k : ℝ) + 4 ≠ 0 := by positivity
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨W, hW⟩ : ∃ W : HighResODE.NAGSC.E n, W = ((k : ℝ) + 3) • x (k + 1) - ((k : ℝ) + 1) • x k
      - (2 : ℝ) • xs + (((k : ℝ) + 1) * b ^ 2) • gradient f (x k) := ⟨_, rfl⟩
  have e0 : lyap f (b ^ 2) xs x k
      = b ^ 2 * ((k : ℝ) + 3) * ((k : ℝ) + 1) * (f (x k) - f xs) + 1 / 2 * ‖W‖ ^ 2 := by
    unfold lyap
    simp only [HighResODE.NAGSC.vel, hsq]
    have : (((k : ℝ) + 1) * b) • ((1 / b) • (x (k + 1) - x k)) + (2 : ℝ) • (x (k + 1) - xs)
        + (((k : ℝ) + 1) * b ^ 2) • gradient f (x k) = W := by
      rw [hW]
      match_scalars <;> field_simp <;> ring
    rw [this]
  have e1 : lyap f (b ^ 2) xs x (k + 1)
      = b ^ 2 * ((k : ℝ) + 4) * ((k : ℝ) + 2) * (f (x (k + 1)) - f xs)
        + 1 / 2 * ‖W - (((k : ℝ) + 3) * b ^ 2) • gradient f (x (k + 1))‖ ^ 2 := by
    unfold lyap
    simp only [HighResODE.NAGSC.vel, hsq]
    have : ((((k + 1 : ℕ) : ℝ) + 1) * b) • ((1 / b) • (x (k + 1 + 1) - x (k + 1)))
        + (2 : ℝ) • (x (k + 1 + 1) - xs)
        + ((((k + 1 : ℕ) : ℝ) + 1) * b ^ 2) • gradient f (x (k + 1))
        = W - (((k : ℝ) + 3) * b ^ 2) • gradient f (x (k + 1)) := by
      rw [hrec k, hW]
      push_cast
      match_scalars <;> field_simp <;> ring
    rw [this]
    push_cast
    ring
  rw [e0, e1, Hlp.norm_sub_smul_sq]
  have hWg : inner ℝ (gradient f (x (k + 1))) W = ((k : ℝ) + 3) * inner ℝ (gradient f (x (k + 1))) (x (k + 1))
      - ((k : ℝ) + 1) * inner ℝ (gradient f (x (k + 1))) (x k)
      - 2 * inner ℝ (gradient f (x (k + 1))) xs
      + (((k : ℝ) + 1) * b ^ 2) * inner ℝ (gradient f (x (k + 1))) (gradient f (x k)) := by
    rw [hW]
    simp only [inner_add_right, inner_sub_right, real_inner_smul_right]
  have hP : inner ℝ (gradient f (x (k + 1))) (gradient f (x k))
      = inner ℝ (gradient f (x k)) (gradient f (x (k + 1))) := real_inner_comm _ _
  have hd : ∀ z, DifferentiableAt ℝ f z := fun z => hdiff z
  have F1 := hconv (x (k + 1)) xs
  rw [inner_sub_right] at F1
  have F2 := Hlp.cocoercive hd hLpos hlip hconv (x (k + 1)) (x k)
  rw [inner_sub_right] at F2
  have hn : ‖gradient f (x k) - gradient f (x (k + 1))‖ ^ 2 = ‖gradient f (x k)‖ ^ 2
      - 2 * inner ℝ (gradient f (x k)) (gradient f (x (k + 1))) + ‖gradient f (x (k + 1))‖ ^ 2 :=
    norm_sub_sq_real _ _
  rw [hn] at F2
  have hnn : 0 ≤ ‖gradient f (x k) - (1 - L * b ^ 2) • gradient f (x (k + 1))‖ ^ 2 := sq_nonneg _
  rw [Hlp.norm_sub_smul_sq, hP] at hnn
  have hf_c : f xs ≤ f (x (k + 1)) := hmin _
  have w1 : 0 ≤ 2 * L * ((k : ℝ) + 3) * b ^ 2 := by positivity
  have w2 : 0 ≤ ((k : ℝ) + 3) * ((k : ℝ) + 1) * b ^ 2 / 2 := by positivity
  have G1 := mul_le_mul_of_nonneg_left F1 w1
  have G2 := mul_le_mul_of_nonneg_left F2 w2
  have G3 := mul_nonneg w2 hnn
  have G4 := mul_nonneg (mul_nonneg hLpos.le (sq_nonneg b)) (sub_nonneg.2 hf_c)
  apply le_of_mul_le_mul_left _ hLpos
  rw [hWg, hP]
  linarith [G1, G2, G3, G4]
