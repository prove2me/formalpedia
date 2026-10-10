-- Prove2me | solution 1 for IQCAlg.ConvexIQC.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:38:17.118773+00:00
-- url     : https://prove2.me/submissions/d4841b25-2076-4c8e-a22c-decdd334eb2f

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace RRAux_IQCAlg_ConvexIQC_lemma_10

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem line_hasDerivAt {φ : F → ℝ} {x v : F} {t : ℝ} (h : DifferentiableAt ℝ φ (x + t • v)) :
    HasDerivAt (fun s : ℝ => φ (x + s • v)) ⟪gradient φ (x + t • v), v⟫_ℝ t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h2 := h.hasGradientAt.hasFDerivAt.comp_hasDerivAt t h1
  have h3 : HasDerivAt (fun s : ℝ => φ (x + s • v))
      ((InnerProductSpace.toDual ℝ F (gradient φ (x + t • v))) v) t := h2
  rwa [InnerProductSpace.toDual_apply_apply] at h3

theorem convex_line {S : Set F} {φ : F → ℝ} (hφ : ConvexOn ℝ S φ) {x y : F} (hx : x ∈ S)
    (hy : y ∈ S) : ConvexOn ℝ (Set.Icc 0 1) (fun s : ℝ => φ (x + s • (y - x))) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have h := hφ.2 (hφ.1.add_smul_sub_mem hx hy ha) (hφ.1.add_smul_sub_mem hx hy hb) hα hβ hαβ
  obtain rfl : β = 1 - α := by linarith
  have he : x + (α * a + (1 - α) * b) • (y - x)
      = α • (x + a • (y - x)) + (1 - α) • (x + b • (y - x)) := by module
  simpa [he] using h

theorem convex_first_order_line {S : Set F} {φ : F → ℝ} (hφ : ConvexOn ℝ S φ) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) {D : ℝ}
    (hD : HasDerivAt (fun s : ℝ => φ (x + s • (y - x))) D 0) : φ x + D ≤ φ y := by
  have h := (convex_line hφ hx hy).le_slope_of_hasDerivAt (x := 0) (y := 1)
    (by simp) (by simp) one_pos hD
  rw [slope_def_field] at h
  simp at h
  linarith

theorem convex_first_order {S : Set F} {φ : F → ℝ} (hφ : ConvexOn ℝ S φ) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) (hd : DifferentiableAt ℝ φ x) :
    φ x + ⟪gradient φ x, y - x⟫_ℝ ≤ φ y := by
  have hd' : DifferentiableAt ℝ φ (x + (0:ℝ) • (y - x)) := by simpa using hd
  have := line_hasDerivAt hd'
  simp only [zero_smul, add_zero] at this
  exact convex_first_order_line hφ hx hy this

theorem descent {S : Set F} (hS : Convex ℝ S) {φ : F → ℝ}
    (hd : ∀ z ∈ S, DifferentiableAt ℝ φ z) {L : ℝ}
    (hL : ∀ u ∈ S, ∀ w ∈ S, ‖gradient φ u - gradient φ w‖ ≤ L * ‖u - w‖) {x y : F}
    (hx : x ∈ S) (hy : y ∈ S) :
    φ y ≤ φ x + ⟪gradient φ x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  let h : ℝ → ℝ := fun s => φ (x + s • v) - s * ⟪gradient φ x, v⟫_ℝ - L / 2 * s ^ 2 * ‖v‖ ^ 2
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, x + s • v ∈ S := fun s hs => hS.add_smul_sub_mem hx hy hs
  have hder : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt h
      (⟪gradient φ (x + s • v), v⟫_ℝ - ⟪gradient φ x, v⟫_ℝ - L * s * ‖v‖ ^ 2) s := by
    intro s hs
    have h1 := line_hasDerivAt (hd _ (hmem s hs))
    have h2 := (hasDerivAt_id s).mul_const ⟪gradient φ x, v⟫_ℝ
    have h3 := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
    have h4 := (h1.sub h2).sub h3
    have e : ⟪gradient φ (x + s • v), v⟫_ℝ - 1 * ⟪gradient φ x, v⟫_ℝ
        - L / 2 * ((2:ℕ) * s ^ (2 - 1)) * ‖v‖ ^ 2
        = ⟪gradient φ (x + s • v), v⟫_ℝ - ⟪gradient φ x, v⟫_ℝ - L * s * ‖v‖ ^ 2 := by
      push_cast; ring
    rw [e] at h4
    exact h4
  have hanti : AntitoneOn h (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro s hs; exact (hder s hs).continuousAt.continuousWithinAt
    · intro s hs
      exact (hder s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hs0 : 0 ≤ s := hs'.1
      have hc := real_inner_le_norm (gradient φ (x + s • v) - gradient φ x) v
      have hl := hL _ (hmem s hs') x hx
      have hn : ‖x + s • v - x‖ = s * ‖v‖ := by
        simp [norm_smul, abs_of_nonneg hs0]
      rw [hn] at hl
      rw [← inner_sub_left]
      have hv0 : 0 ≤ ‖v‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hl hv0]
  have := hanti (by simp : (0:ℝ) ∈ Set.Icc (0:ℝ) 1) (by simp : (1:ℝ) ∈ Set.Icc (0:ℝ) 1)
    zero_le_one
  simp only [h, one_smul, zero_smul, add_zero, zero_mul, one_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hxy : x + v = y := by rw [hv]; abel
  rw [hxy] at this
  linarith

-- Cocoercivity from the two-sided first-order bounds.
theorem coco {G : F → ℝ} {a : F → F} {L : ℝ} (hL : 0 < L)
    (hlow : ∀ x z, G x + ⟪a x, z - x⟫_ℝ ≤ G z)
    (hup : ∀ x z, G z ≤ G x + ⟪a x, z - x⟫_ℝ + L / 2 * ‖z - x‖ ^ 2) (x y : F) :
    G x + ⟪a x, y - x⟫_ℝ + ‖a y - a x‖ ^ 2 / (2 * L) ≤ G y := by
  set w := a y - a x
  set z := y - (1 / L) • w
  have h1 := hlow x z
  have h2 := hup y z
  have ez1 : z - x = (y - x) - (1 / L) • w := by simp only [z]; abel
  have ez2 : z - y = -((1 / L) • w) := by simp only [z]; abel
  rw [ez1, inner_sub_right, inner_smul_right] at h1
  rw [ez2, inner_neg_right, inner_smul_right, norm_neg, norm_smul] at h2
  have hw : ⟪a y, w⟫_ℝ - ⟪a x, w⟫_ℝ = ‖w‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / L)] at h2
  have hw' : 1 / L * ⟪a y, w⟫_ℝ - 1 / L * ⟪a x, w⟫_ℝ = 1 / L * ‖w‖ ^ 2 := by
    rw [← mul_sub, hw]
  have key : G x + ⟪a x, y - x⟫_ℝ + 1 / L * ‖w‖ ^ 2 - L / 2 * (1 / L * ‖w‖) ^ 2 ≤ G y := by
    linarith
  have e : 1 / L * ‖w‖ ^ 2 - L / 2 * (1 / L * ‖w‖) ^ 2 = ‖w‖ ^ 2 / (2 * L) := by
    field_simp; ring
  linarith


theorem coco2 {G : F → ℝ} {a : F → F} {L : ℝ} (hL : 0 < L)
    (hlow : ∀ x z, G x + ⟪a x, z - x⟫_ℝ ≤ G z)
    (hup : ∀ x z, G z ≤ G x + ⟪a x, z - x⟫_ℝ + L / 2 * ‖z - x‖ ^ 2) (x y : F) :
    ‖a y - a x‖ ^ 2 / 2 ≤ L * (G y - G x - ⟪a x, y - x⟫_ℝ) := by
  have h := coco hL hlow hup x y
  have h2 : ‖a y - a x‖ ^ 2 / (2 * L) ≤ G y - G x - ⟪a x, y - x⟫_ℝ := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 hL.le
  have e : L * (‖a y - a x‖ ^ 2 / (2 * L)) = ‖a y - a x‖ ^ 2 / 2 := by
    field_simp
  linarith

end RRAux_IQCAlg_ConvexIQC_lemma_10

namespace RRAux_IQCAlg_ConvexIQC_lemma_10
open IQCAlg.ConvexIQC

theorem sc_first_order {d : ℕ} {f : E d → ℝ} {m L : ℝ} (hf : InSmL f m L) (x z : E d) :
    f x + ⟪gradient f x, z - x⟫_ℝ + m / 2 * ‖z - x‖ ^ 2 ≤ f z := by
  have hdiff : Differentiable ℝ f := hf.contDiff.differentiable (by norm_num)
  have hc := (strongConvexOn_iff_convex.mp hf.strongConvex)
  set v := z - x with hv
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have h1 := line_hasDerivAt (φ := f) (x := x) (v := v) (t := 0) (hdiff _)
  simp only [zero_smul, add_zero] at h1
  have h2 := (hl.norm_sq).const_mul (m / 2)
  simp only [zero_smul, add_zero] at h2
  have h3 := h1.sub h2
  have := convex_first_order_line (φ := fun x => f x - m / 2 * ‖x‖ ^ 2) hc
    (Set.mem_univ x) (Set.mem_univ z) (D := ⟪gradient f x, v⟫_ℝ - m / 2 * (2 * ⟪x, v⟫_ℝ)) h3
  have hz : z = x + v := by rw [hv]; abel
  have hn := norm_add_sq_real x v
  rw [← hz] at hn
  have hm : m / 2 * ‖z‖ ^ 2 = m / 2 * ‖x‖ ^ 2 + m * ⟪x, v⟫_ℝ + m / 2 * ‖v‖ ^ 2 := by
    rw [hn]; ring
  linarith

variable {d : ℕ} (f : E d → ℝ) (m : ℝ) (ys : E d)

noncomputable def G (x : E d) : ℝ := f x - m / 2 * ‖x - ys‖ ^ 2
noncomputable def a (x : E d) : E d := gradient f x - m • (x - ys)

theorem bregman_eq (x z : E d) :
    G f m ys z - (G f m ys x + ⟪a f m ys x, z - x⟫_ℝ)
      = f z - (f x + ⟪gradient f x, z - x⟫_ℝ) - m / 2 * ‖z - x‖ ^ 2 := by
  have hn := norm_add_sq_real (x - ys) (z - x)
  have e : x - ys + (z - x) = z - ys := by abel
  rw [e] at hn
  simp only [G, a]
  rw [inner_sub_left, real_inner_smul_left, hn]; ring

theorem G_low {L : ℝ} (hf : InSmL f m L) (x z : E d) :
    G f m ys x + ⟪a f m ys x, z - x⟫_ℝ ≤ G f m ys z := by
  have := bregman_eq f m ys x z
  have := sc_first_order hf x z
  linarith

theorem G_up {L : ℝ} (hf : InSmL f m L) (x z : E d) :
    G f m ys z ≤ G f m ys x + ⟪a f m ys x, z - x⟫_ℝ + (L - m) / 2 * ‖z - x‖ ^ 2 := by
  have h1 := bregman_eq f m ys x z
  have hdiff : Differentiable ℝ f := hf.contDiff.differentiable (by norm_num)
  have h2 := descent (S := Set.univ) convex_univ (φ := f) (fun z _ => hdiff z)
    (L := L) (fun u _ w _ => hf.lipschitz_grad u w) (Set.mem_univ x) (Set.mem_univ z)
  linarith

theorem step_ineq (c1 q0 q1 w r ρ : ℝ) (hc1 : 0 ≤ c1) (hq0 : 0 ≤ q0) (hr : r ≤ ρ ^ 2)
    (hw : q1 - r * q0 ≤ w) : c1 * q1 ≤ (c1 * ρ ^ 2) * q0 + c1 * w := by
  nlinarith [mul_nonneg hc1 hq0, mul_le_mul_of_nonneg_left hw hc1,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hq0) hc1]

theorem combo (Lp I1 I0 J N1 q0 q1 r w : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hw : w = Lp * I1 - r * (Lp * I0) - N1 + r * J)
    (hs : q1 ≤ Lp * I1 - N1) (hp : q1 - q0 ≤ Lp * I1 - Lp * I0 - N1 + J) :
    q1 - r * q0 ≤ w := by
  have h1 := mul_le_mul_of_nonneg_left hp hr0
  have h2 := mul_le_mul_of_nonneg_left hs (by linarith : (0:ℝ) ≤ 1 - r)
  rw [hw]; nlinarith

end RRAux_IQCAlg_ConvexIQC_lemma_10

open RRAux_IQCAlg_ConvexIQC_lemma_10 in
open IQCAlg.ConvexIQC in
theorem solution {d : ℕ} (f : E d → ℝ) (m L : ℝ) (hf : InSmL f m L) (ys : E d)
    (ρbar ρ : ℝ) (hρbar : 0 ≤ ρbar) (hρbarρ : ρbar ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) :
    ∀ (y : ℕ → E d) (k : ℕ),
      0 ≤ sTerm f m L y ys 0
        + ∑ t ∈ Finset.range k, (ρ ^ (2 * (t + 1)))⁻¹ * wTerm f m L ρbar y ys t := by
  intro y k
  have hLp : 0 < L - m := by linarith [hf.m_lt_L]
  have hlow := G_low f m ys hf
  have hup := G_up f m ys hf
  set Lp := L - m with hLpdef
  set A : ℕ → E d := fun t => ut f y ys t - m • yt y ys t with hA
  set e : ℕ → E d := fun t => yt y ys t with he
  have hAa : ∀ t, A t = a f m ys (y t) - a f m ys ys := by
    intro t; simp only [hA, ut, yt, a, sub_self, smul_zero, sub_zero]; abel
  have hey : ∀ t, e t = y t - ys := fun t => rfl
  set P : E d → E d → ℝ := fun x z => G f m ys z - G f m ys x - ⟪a f m ys x, z - x⟫_ℝ with hP
  have hco : ∀ x z, ‖a f m ys z - a f m ys x‖ ^ 2 / 2 ≤ Lp * P x z :=
    fun x z => coco2 hLp hlow hup x z
  set q : ℕ → ℝ := fun t => Lp * P ys (y t) - ‖A t‖ ^ 2 / 2 with hq
  have hq0 : ∀ t, 0 ≤ q t := by
    intro t; have := hco ys (y t); simp only [hq, hAa t]; linarith
  -- sector bound
  have hsec : ∀ t, q t ≤ Lp * ⟪A t, e t⟫_ℝ - ‖A t‖ ^ 2 := by
    intro t
    have h1 := hco (y t) ys
    rw [← norm_neg, neg_sub, ← hAa t] at h1
    have hsum : P ys (y t) + P (y t) ys = ⟪A t, e t⟫_ℝ := by
      simp only [hP, hAa t, hey t, inner_sub_left]
      have : ys - y t = -(y t - ys) := by abel
      rw [this, inner_neg_right]; ring
    have h2 : Lp * P ys (y t) + Lp * P (y t) ys = Lp * ⟪A t, e t⟫_ℝ := by rw [← mul_add, hsum]
    simp only [hq]; linarith
  have hsT : ∀ t, sTerm f m L y ys t = Lp * ⟪A t, e t⟫_ℝ - ‖A t‖ ^ 2 := by
    intro t
    have e1 : L • yt y ys t - ut f y ys t = Lp • e t - A t := by
      simp only [hA, he, hLpdef]; module
    simp only [sTerm]
    rw [e1, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  -- off-by-one bound
  have hoff : ∀ t, q (t + 1) - q t ≤ Lp * ⟪A (t + 1), e (t + 1)⟫_ℝ - Lp * ⟪A (t + 1), e t⟫_ℝ
      - ‖A (t + 1)‖ ^ 2 + ⟪A (t + 1), A t⟫_ℝ := by
    intro t
    have h1 := hco (y (t + 1)) (y t)
    have ediff : a f m ys (y t) - a f m ys (y (t + 1)) = A t - A (t + 1) := by
      rw [hAa, hAa]; abel
    rw [ediff, norm_sub_sq_real] at h1
    have hP2 : P ys (y (t + 1)) - P ys (y t) + P (y (t + 1)) (y t)
        = ⟪A (t + 1), e (t + 1)⟫_ℝ - ⟪A (t + 1), e t⟫_ℝ := by
      simp only [hP, hAa, hey, inner_sub_left, inner_sub_right]
      ring_nf
    have h3 : Lp * P ys (y (t + 1)) - Lp * P ys (y t) + Lp * P (y (t + 1)) (y t)
        = Lp * ⟪A (t + 1), e (t + 1)⟫_ℝ - Lp * ⟪A (t + 1), e t⟫_ℝ := by
      rw [← mul_sub, ← mul_add, hP2]; ring
    have hc : ⟪A t, A (t + 1)⟫_ℝ = ⟪A (t + 1), A t⟫_ℝ := real_inner_comm _ _
    simp only [hq]; linarith
  have hwT : ∀ t, wTerm f m L ρbar y ys t = Lp * ⟪A (t + 1), e (t + 1)⟫_ℝ
      - ρbar ^ 2 * (Lp * ⟪A (t + 1), e t⟫_ℝ) - ‖A (t + 1)‖ ^ 2 + ρbar ^ 2 * ⟪A (t + 1), A t⟫_ℝ := by
    intro t
    have e1 : L • (yt y ys (t + 1) - ρbar ^ 2 • yt y ys t) - (ut f y ys (t + 1) - ρbar ^ 2 • ut f y ys t)
        = Lp • e (t + 1) - (ρbar ^ 2 * Lp) • e t - A (t + 1) + ρbar ^ 2 • A t := by
      simp only [hA, he, hLpdef]; module
    simp only [wTerm]
    change ⟪A (t + 1), _⟫_ℝ = _
    rw [e1, inner_add_right, inner_sub_right, inner_sub_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hr0 : 0 ≤ ρbar ^ 2 := by positivity
  have hrρ : ρbar ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρbar hρbarρ 2
  have hr1 : ρbar ^ 2 ≤ 1 := by nlinarith
  have hw : ∀ t, q (t + 1) - ρbar ^ 2 * q t ≤ wTerm f m L ρbar y ys t := fun t =>
    combo Lp _ _ _ _ (q t) (q (t + 1)) _ _ hr0 hr1 (hwT t) (hsec (t + 1)) (hoff t)
  have main : ∀ k, (ρ ^ (2 * k))⁻¹ * q k ≤ sTerm f m L y ys 0
      + ∑ t ∈ Finset.range k, (ρ ^ (2 * (t + 1)))⁻¹ * wTerm f m L ρbar y ys t := by
    intro k
    induction k with
    | zero => simp only [mul_zero, pow_zero, inv_one, one_mul, Finset.range_zero,
        Finset.sum_empty, add_zero]; rw [hsT]; exact hsec 0
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hc1 : 0 ≤ (ρ ^ (2 * (k + 1)))⁻¹ := by positivity
      have hc0 : (ρ ^ (2 * k))⁻¹ = (ρ ^ (2 * (k + 1)))⁻¹ * ρ ^ 2 := by
        have : ρ ^ (2 * (k + 1)) = ρ ^ (2 * k) * ρ ^ 2 := by ring
        rw [this, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
      have := step_ineq _ (q k) (q (k + 1)) _ _ ρ hc1 (hq0 k) hrρ (hw k)
      rw [← hc0] at this
      linarith
  have := main k
  have : 0 ≤ (ρ ^ (2 * k))⁻¹ * q k := mul_nonneg (by positivity) (hq0 k)
  linarith

#print axioms solution
