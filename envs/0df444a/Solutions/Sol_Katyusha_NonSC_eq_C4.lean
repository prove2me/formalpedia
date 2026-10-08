-- Prove2me | solution 1 for Katyusha.NonSC.eq_C4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T04:58:47.723593+00:00
-- url     : https://prove2.me/submissions/90b9c430-1cb8-4b88-9d9b-28573155afa3

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_Katyusha_NonSC_step
import Definitions.Def_Katyusha_NonSC_run

set_option autoImplicit false

namespace KatB034

open scoped RealInnerProductSpace in
theorem line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (x w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F (x + s • w)) ⟪G (x + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => x + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add x
  have h1 := (hasGradientAt_iff_hasFDerivAt.mp (hF (x + t • w))).comp_hasDerivAt t hl
  rw [InnerProductSpace.toDual_apply_apply] at h1
  exact h1

open scoped RealInnerProductSpace in
theorem descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (x y : E) :
    F y ≤ F x + ⟪G x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => F (x + t • w) - t * ⟪G x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪G (x + t • w), w⟫ - ⟪G x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := line_deriv hF x w t
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

open scoped RealInnerProductSpace in
theorem convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} (hF : ∀ x, HasGradientAt F (G x) x)
    (hc : ConvexOn ℝ Set.univ F) (x y : E) : F x + ⟪G x, y - x⟫ ≤ F y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => F (x + t • w)) := by
    have := hc.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => F (x + t • w)) = F ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using line_deriv hF x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  linarith

-- Co-coercivity: ‖G y - G x‖² ≤ 2L (F y - F x - ⟪G x, y - x⟫).
open scoped RealInnerProductSpace in
theorem cocoercive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {F : E → ℝ} {G : E → E} {L : ℝ} (hL : 0 < L)
    (hF : ∀ x, HasGradientAt F (G x) x)
    (hG : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) (hc : ConvexOn ℝ Set.univ F) (x y : E) :
    ‖G y - G x‖ ^ 2 ≤ 2 * L * (F y - F x - ⟪G x, y - x⟫) := by
  set φ : E → ℝ := fun z => F z - ⟪G x, z⟫ with hφdef
  set H : E → E := fun z => G z - G x with hHdef
  have hφ : ∀ z, HasGradientAt φ (H z) z := by
    intro z
    have h1 := hasGradientAt_iff_hasFDerivAt.mp (hF z)
    have h2 : HasFDerivAt (fun z : E => ⟪G x, z⟫) (InnerProductSpace.toDual ℝ E (G x)) z := by
      have e : (fun z : E => ⟪G x, z⟫) = ⇑(InnerProductSpace.toDual ℝ E (G x)) := by
        funext z; simp [InnerProductSpace.toDual_apply_apply]
      rw [e]; exact ContinuousLinearMap.hasFDerivAt _
    rw [hasGradientAt_iff_hasFDerivAt, map_sub]
    exact h1.sub h2
  have hH : ∀ a b, ‖H a - H b‖ ≤ L * ‖a - b‖ := by
    intro a b; simp only [hHdef, sub_sub_sub_cancel_right]; exact hG a b
  have hmin : ∀ z, φ x ≤ φ z := by
    intro z
    have := convex_fo hF hc x z
    simp only [hφdef, inner_sub_right] at this ⊢
    linarith
  set v := H y
  have hd := descent hφ hH y (y - (1 / L) • v)
  have hm := hmin (y - (1 / L) • v)
  have e1 : y - (1 / L) • v - y = -((1 / L) • v) := by abel
  rw [e1, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / L), real_inner_self_eq_norm_sq] at hd
  have key : ‖v‖ ^ 2 ≤ 2 * L * (φ y - φ x) := by
    have hL' : L ≠ 0 := hL.ne'
    have : φ x ≤ φ y - 1 / (2 * L) * ‖v‖ ^ 2 := by
      have h := hm.trans hd
      have : -(1 / L * ‖v‖ ^ 2) + L / 2 * (1 / L * ‖v‖) ^ 2 = - (1 / (2 * L) * ‖v‖ ^ 2) := by
        field_simp; ring
      linarith
    have h2 : 2 * L * (1 / (2 * L) * ‖v‖ ^ 2) = ‖v‖ ^ 2 := by field_simp
    nlinarith
  have hv : v = G y - G x := rfl
  rw [← hv]
  have : φ y - φ x = F y - F x - ⟪G x, y - x⟫ := by
    simp only [hφdef, inner_sub_right]; ring
  rw [← this]; exact key

lemma var_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} (hn : 0 < n)
    (y : Fin n → E) :
    ∑ j, ‖y j - (1 / (n : ℝ)) • ∑ i, y i‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set m := (1 / (n : ℝ)) • ∑ i, y i with hm
  have hsum : ∑ i, y i = (n : ℝ) • m := by
    rw [hm, smul_smul, mul_one_div_cancel hn', one_smul]
  have h : ∑ j, ‖y j - m‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 - (n : ℝ) * ‖m‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp
    ring
  rw [h]
  have : 0 ≤ (n : ℝ) * ‖m‖ ^ 2 := by positivity
  linarith

open scoped RealInnerProductSpace in
lemma inner_young {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E)
    {L : ℝ} (hL : 0 < L) : ⟪a, b⟫ - L * ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 / (4 * L) := by
  have h0 : 0 ≤ ‖a - (2 * L) • b‖ ^ 2 := by positivity
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 2 * L), mul_pow] at h0
  rw [le_div_iff₀ (by positivity)]
  nlinarith

-- Expansion of the prox objective around `z` for the shifted center `z - γ g`.
open scoped RealInnerProductSpace in
lemma expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {γ : ℝ} (hγ : 0 < γ)
    (q z g : E) :
    1 / (2 * γ) * ‖q - (z - γ • g)‖ ^ 2
      = 1 / (2 * γ) * ‖q - z‖ ^ 2 + ⟪g, q - z⟫ + γ / 2 * ‖g‖ ^ 2 := by
  have e : q - (z - γ • g) = (q - z) + γ • g := by abel
  rw [e, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos hγ,
    mul_pow, real_inner_comm]
  field_simp

-- Three-point property of the prox of a convex function.
open scoped RealInnerProductSpace in
lemma prox3 {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ConvexOn ℝ Set.univ ψ)
    {γ : ℝ} (hγ : 0 < γ) {w p : EuclideanSpace ℝ (Fin d)}
    (hp : SAGA.Convex.IsProxPoint ψ γ w p) (u : EuclideanSpace ℝ (Fin d)) :
    ψ p + 1 / (2 * γ) * ‖p - w‖ ^ 2 + 1 / (2 * γ) * ‖u - p‖ ^ 2
      ≤ ψ u + 1 / (2 * γ) * ‖u - w‖ ^ 2 := by
  set c := 1 / (2 * γ) with hc
  have hc0 : 0 < c := by positivity
  set a := p - w
  set b := u - p
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ (ψ u - ψ p) + 2 * c * ⟪a, b⟫ + t * (c * ‖b‖ ^ 2) := by
    intro t ht0 ht1
    have h1 := hp (p + t • b)
    have h2 : ψ (p + t • b) ≤ (1 - t) * ψ p + t * ψ u := by
      have := hψ.2 (Set.mem_univ p) (Set.mem_univ u) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
        (by ring)
      have e : (1 - t) • p + t • u = p + t • b := by simp only [b]; module
      rw [e] at this
      simpa [smul_eq_mul] using this
    have e2 : p + t • b - w = a + t • b := by simp only [a]; abel
    rw [e2, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0, mul_pow] at h1
    have h3 : 0 ≤ t * ((ψ u - ψ p) + 2 * c * ⟪a, b⟫ + t * (c * ‖b‖ ^ 2)) := by
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp h3
  have hlim : 0 ≤ (ψ u - ψ p) + 2 * c * ⟪a, b⟫ := by
    by_contra hneg
    push Not at hneg
    set e := (ψ u - ψ p) + 2 * c * ⟪a, b⟫ with he
    set K := c * ‖b‖ ^ 2 with hK
    have hK0 : 0 ≤ K := by positivity
    set t := min (1 / 2 : ℝ) (-e / (2 * (K + 1))) with ht
    have ht0 : 0 < t := by
      apply lt_min (by norm_num)
      apply div_pos (by linarith) (by positivity)
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have htK : t * (K + 1) ≤ -e / 2 := by
      have : t ≤ -e / (2 * (K + 1)) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have := key t ht0 ht1
    nlinarith
  have e3 : u - w = a + b := by simp only [a, b]; abel
  rw [e3, norm_add_sq_real]
  nlinarith


-- One inner step of Katyusha (Allen-Zhu, proof of Lemma 2.7), for a fixed index.
open scoped RealInnerProductSpace in
lemma per_step {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    {L τ1 α t2 : ℝ} (hL : 0 < L) (hα : 0 < α) (hτ1 : 0 < τ1) (hτ1lt : τ1 < 1) (ht2 : 0 ≤ t2)
    (hc0 : 0 ≤ 1 - τ1 - t2) (hQ : 3 * L * τ1 ^ 2 / 2 ≤ τ1 / (2 * α))
    (F0 : EuclideanSpace ℝ (Fin d) → ℝ) (x xt y z xs g gb : EuclideanSpace ℝ (Fin d))
    (hx : x = τ1 • z + t2 • xt + (1 - τ1 - t2) • y)
    (hdesc : ∀ u, F0 u ≤ F0 x + ⟪gb, u - x⟫ + L / 2 * ‖u - x‖ ^ 2) :
    F0 (P (1 / (3 * L)) (x - (1 / (3 * L)) • g)) + ψ (P (1 / (3 * L)) (x - (1 / (3 * L)) • g))
      ≤ (F0 x + τ1 / (2 * α) * ‖z - xs‖ ^ 2 + τ1 * ψ xs + t2 * ψ xt + (1 - τ1 - t2) * ψ y)
        - τ1 * ⟪g, z - xs⟫ + ‖gb - g‖ ^ 2 / (4 * L)
        - τ1 / (2 * α) * ‖P α (z - α • g) - xs‖ ^ 2 := by
  set yp := P (1 / (3 * L)) (x - (1 / (3 * L)) • g) with hyp
  set zp := P α (z - α • g) with hzp
  set v := τ1 • zp + t2 • xt + (1 - τ1 - t2) • y with hv
  have hvx : v - x = τ1 • (zp - z) := by rw [hv, hx]; module
  have hγy : (0:ℝ) < 1 / (3 * L) := by positivity
  have hY := hP (1 / (3 * L)) hγy (x - (1 / (3 * L)) • g) v
  rw [← hyp, expand hγy, expand hγy, hvx, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hτ1, mul_pow] at hY
  have hZ := prox3 hψ hα (hP α hα (z - α • g)) xs
  rw [← hzp, expand hα, expand hα, norm_sub_rev xs zp, norm_sub_rev xs z] at hZ
  have e5 : ⟪g, xs - z⟫ = -⟪g, z - xs⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [e5] at hZ
  have hZm := mul_le_mul_of_nonneg_left hZ hτ1.le
  have hψv : ψ v ≤ τ1 * ψ zp + t2 * ψ xt + (1 - τ1 - t2) * ψ y := by
    have hpos : 0 < 1 - τ1 := by linarith
    set w := (t2 / (1 - τ1)) • xt + ((1 - τ1 - t2) / (1 - τ1)) • y with hwdef
    have hw : ψ w ≤ t2 / (1 - τ1) * ψ xt + (1 - τ1 - t2) / (1 - τ1) * ψ y := by
      have := hψ.2 (Set.mem_univ xt) (Set.mem_univ y) (div_nonneg ht2 hpos.le)
        (div_nonneg hc0 hpos.le) (by field_simp; ring)
      simpa [smul_eq_mul] using this
    have c1 : (1 - τ1) * (t2 / (1 - τ1)) = t2 := by field_simp
    have c2 : (1 - τ1) * ((1 - τ1 - t2) / (1 - τ1)) = 1 - τ1 - t2 := by field_simp
    have hv2 : v = τ1 • zp + (1 - τ1) • w := by
      rw [hv, hwdef, smul_add, smul_smul, smul_smul, c1, c2, add_assoc]
    have h1 := hψ.2 (Set.mem_univ zp) (Set.mem_univ w) hτ1.le hpos.le (by ring)
    simp only [smul_eq_mul] at h1
    rw [hv2]
    have h2 := mul_le_mul_of_nonneg_left hw hpos.le
    have e : (1 - τ1) * (t2 / (1 - τ1) * ψ xt + (1 - τ1 - t2) / (1 - τ1) * ψ y)
        = t2 * ψ xt + (1 - τ1 - t2) * ψ y := by
      field_simp
    linarith
  have hD := hdesc yp
  have hYo := inner_young (gb - g) (yp - x) hL
  rw [inner_sub_left] at hYo
  have hQm := mul_le_mul_of_nonneg_right hQ (sq_nonneg ‖zp - z‖)
  have hk : (1 : ℝ) / (2 * (1 / (3 * L))) = 3 * L / 2 := by field_simp
  rw [hk] at hY
  linear_combination hD + hY + hYo + hψv + hZm + hQm

end KatB034

open SAGA.Convex Katyusha.NonSC RealInnerProductSpace in
theorem KatB034.lemma27 {d n : ℕ} (hn : 0 < n)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (τ1 α : ℝ) (hα : 0 < α) (hτ1 : 0 < τ1) (hτ1_half : τ1 ≤ 1 / 2)
    (hτ1α : τ1 ≤ 1 / (3 * α * L))
    (xt y z : EuclideanSpace ℝ (Fin d)) :
    0 ≤ α * (1 - τ1 - tau2) / τ1 * (obj f ψ y - obj f ψ xstar)
        - α / τ1 * ((1 / (n : ℝ)) * (∑ i, obj f ψ (innerStep f' P L τ1 α xt (y, z) i).1)
            - obj f ψ xstar)
        + α * tau2 / τ1 * (obj f ψ xt - obj f ψ xstar)
        + 1 / 2 * ‖z - xstar‖ ^ 2
        - 1 / 2 * ((1 / (n : ℝ)) * ∑ i, ‖(innerStep f' P L τ1 α xt (y, z) i).2 - xstar‖ ^ 2) := by
  have ht2 : tau2 = 1 / 2 := rfl
  have ht20 : (0:ℝ) ≤ tau2 := by rw [ht2]; norm_num
  have hc0 : 0 ≤ 1 - τ1 - tau2 := by rw [ht2]; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn' : (n : ℝ) ≠ 0 := hnR.ne'
  set x := coupling τ1 xt y z with hxdef
  set gb := gradAvg f' x with hgb
  -- smoothness / convexity of the average
  have hdesc : ∀ u, fAvg f u ≤ fAvg f x + ⟪gb, u - x⟫ + L / 2 * ‖u - x‖ ^ 2 := by
    intro u
    have hi : ∀ i, f i u ≤ f i x + ⟪f' i x, u - x⟫ + L / 2 * ‖u - x‖ ^ 2 :=
      fun i => KatB034.descent (hf_grad i) (hf_smooth i) x u
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hg : ⟪gb, u - x⟫ = (1 / (n : ℝ)) * ⟪∑ i, f' i x, u - x⟫ := by
      rw [hgb, gradAvg, real_inner_smul_left]
    unfold fAvg
    rw [hg]
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    have e : (1 / (n : ℝ)) * ((n : ℝ) * (L / 2 * ‖u - x‖ ^ 2)) = L / 2 * ‖u - x‖ ^ 2 := by
      field_simp
    linarith
  have hcvx : ∀ u, fAvg f x + ⟪gb, u - x⟫ ≤ fAvg f u := by
    intro u
    have hi : ∀ i, f i x + ⟪f' i x, u - x⟫ ≤ f i u :=
      fun i => KatB034.convex_fo (hf_grad i) (hf_conv i) x u
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_add_distrib, ← sum_inner] at hs
    have hg : ⟪gb, u - x⟫ = (1 / (n : ℝ)) * ⟪∑ i, f' i x, u - x⟫ := by
      rw [hgb, gradAvg, real_inner_smul_left]
    unfold fAvg
    rw [hg]
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    linarith
  -- the mean of the estimator
  have hsumg : ∑ i, gradEst f' xt x i = (n : ℝ) • gb := by
    simp only [gradEst, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, hgb, gradAvg]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, mul_one_div_cancel hn', one_smul,
      one_smul]
    abel
  -- variance bound
  have hvar : (1 / (n : ℝ)) * ∑ i, ‖gb - gradEst f' xt x i‖ ^ 2
      ≤ 2 * L * (fAvg f xt - fAvg f x - ⟪gb, xt - x⟫) := by
    set a : Fin n → EuclideanSpace ℝ (Fin d) := fun i => f' i x - f' i xt with ha
    have hv := KatB034.var_le hn a
    have hma : (1 / (n : ℝ)) • ∑ j, a j = gb - gradAvg f' xt := by
      simp only [ha, Finset.sum_sub_distrib, smul_sub, hgb, gradAvg]
    have hnorm : ∀ i, ‖gb - gradEst f' xt x i‖ ^ 2 = ‖a i - (1 / (n : ℝ)) • ∑ j, a j‖ ^ 2 := by
      intro i
      rw [hma, ← norm_neg]
      congr 2
      simp only [gradEst, ha]
      abel
    simp_rw [hnorm]
    have hco : ∀ i, ‖a i‖ ^ 2 ≤ 2 * L * (f i xt - f i x - ⟪f' i x, xt - x⟫) := by
      intro i
      have := KatB034.cocoercive hL (hf_grad i) (hf_smooth i) (hf_conv i) x xt
      show ‖f' i x - f' i xt‖ ^ 2 ≤ _
      rw [norm_sub_rev]; exact this
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hco i)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← sum_inner] at hs
    have hg : ⟪gb, xt - x⟫ = (1 / (n : ℝ)) * ⟪∑ i, f' i x, xt - x⟫ := by
      rw [hgb, gradAvg, real_inner_smul_left]
    unfold fAvg
    rw [hg]
    have h1 := mul_le_mul_of_nonneg_left (hv.trans hs) (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    linarith
  have hQ : 3 * L * τ1 ^ 2 / 2 ≤ τ1 / (2 * α) := by
    rw [le_div_iff₀ (by positivity)]
    have := hτ1α
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  -- per-index inequality
  have per : ∀ i, obj f ψ (innerStep f' P L τ1 α xt (y, z) i).1
      ≤ (fAvg f x + τ1 / (2 * α) * ‖z - xstar‖ ^ 2 + τ1 * ψ xstar + tau2 * ψ xt
          + (1 - τ1 - tau2) * ψ y)
        - τ1 * ⟪gradEst f' xt x i, z - xstar⟫ + ‖gb - gradEst f' xt x i‖ ^ 2 / (4 * L)
        - τ1 / (2 * α) * ‖(innerStep f' P L τ1 α xt (y, z) i).2 - xstar‖ ^ 2 :=
    fun i => KatB034.per_step hψ P hP hL hα hτ1 (by linarith) ht20 hc0 hQ (fAvg f) x xt y z xstar
      (gradEst f' xt x i) gb rfl hdesc
  have hav := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => per i)
    (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
  have hR : (1 / (n : ℝ)) * ∑ i, ((fAvg f x + τ1 / (2 * α) * ‖z - xstar‖ ^ 2 + τ1 * ψ xstar
          + tau2 * ψ xt + (1 - τ1 - tau2) * ψ y)
        - τ1 * ⟪gradEst f' xt x i, z - xstar⟫ + ‖gb - gradEst f' xt x i‖ ^ 2 / (4 * L)
        - τ1 / (2 * α) * ‖(innerStep f' P L τ1 α xt (y, z) i).2 - xstar‖ ^ 2)
      = (fAvg f x + τ1 / (2 * α) * ‖z - xstar‖ ^ 2 + τ1 * ψ xstar + tau2 * ψ xt
          + (1 - τ1 - tau2) * ψ y)
        - τ1 * ⟪gb, z - xstar⟫
        + ((1 / (n : ℝ)) * ∑ i, ‖gb - gradEst f' xt x i‖ ^ 2) / (4 * L)
        - τ1 / (2 * α) * ((1 / (n : ℝ)) * ∑ i, ‖(innerStep f' P L τ1 α xt (y, z) i).2 - xstar‖ ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div,
      ← sum_inner]
    rw [hsumg, real_inner_smul_left]
    field_simp
  rw [hR] at hav
  -- coupling identity
  have hcpl : τ1 * ⟪gb, z - xstar⟫ = τ1 * ⟪gb, x - xstar⟫ + tau2 * ⟪gb, x - xt⟫
      + (1 - τ1 - tau2) * ⟪gb, x - y⟫ := by
    have e : τ1 • (z - xstar) = τ1 • (x - xstar) + tau2 • (x - xt) + (1 - τ1 - tau2) • (x - y) := by
      rw [hxdef]; simp only [coupling]; module
    rw [← real_inner_smul_right, e, inner_add_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_right]
  have hc1 := hcvx xstar
  have hc2 := hcvx y
  have e1 : ⟪gb, xstar - x⟫ = -⟪gb, x - xstar⟫ := by rw [← inner_neg_right, neg_sub]
  have e2 : ⟪gb, y - x⟫ = -⟪gb, x - y⟫ := by rw [← inner_neg_right, neg_sub]
  rw [e1] at hc1
  rw [e2] at hc2
  have hc1m := mul_le_mul_of_nonneg_left hc1 hτ1.le
  have hc2m := mul_le_mul_of_nonneg_left hc2 hc0
  have hvd := div_le_div_of_nonneg_right hvar (by positivity : (0:ℝ) ≤ 4 * L)
  have e3 : 2 * L * (fAvg f xt - fAvg f x - ⟪gb, xt - x⟫) / (4 * L)
      = tau2 * (fAvg f xt - fAvg f x - ⟪gb, xt - x⟫) := by
    rw [ht2]; field_simp; ring
  rw [e3] at hvd
  have e4 : ⟪gb, xt - x⟫ = -⟪gb, x - xt⟫ := by rw [← inner_neg_right, neg_sub]
  rw [e4] at hvd
  set A := (1 / (n : ℝ)) * ∑ i, obj f ψ (innerStep f' P L τ1 α xt (y, z) i).1 with hA
  set B := (1 / (n : ℝ)) * ∑ i, ‖(innerStep f' P L τ1 α xt (y, z) i).2 - xstar‖ ^ 2 with hB
  have key : 0 ≤ τ1 * obj f ψ xstar + tau2 * obj f ψ xt + (1 - τ1 - tau2) * obj f ψ y
      + τ1 / (2 * α) * (‖z - xstar‖ ^ 2 - B) - A := by
    unfold obj
    linarith
  have hgoal : α * (1 - τ1 - tau2) / τ1 * (obj f ψ y - obj f ψ xstar)
        - α / τ1 * (A - obj f ψ xstar)
        + α * tau2 / τ1 * (obj f ψ xt - obj f ψ xstar)
        + 1 / 2 * ‖z - xstar‖ ^ 2 - 1 / 2 * B
      = α / τ1 * (τ1 * obj f ψ xstar + tau2 * obj f ψ xt + (1 - τ1 - tau2) * obj f ψ y
      + τ1 / (2 * α) * (‖z - xstar‖ ^ 2 - B) - A) := by
    field_simp
    ring
  rw [hgoal]
  exact mul_nonneg (by positivity) key

namespace KatB034
open SAGA.Convex Katyusha.NonSC

lemma expect_const {n k : ℕ} (hn : 0 < n) (c : ℝ) : expectIdx n k (fun _ => c) = c := by
  unfold expectIdx
  have h : ((n : ℝ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

lemma expect_mono {n k : ℕ} (g h : (Fin k → Fin n) → ℝ) (hgh : ∀ js, g js ≤ h js) :
    expectIdx n k g ≤ expectIdx n k h := by
  unfold expectIdx
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hgh i) (by positivity)

lemma expect_add {n k : ℕ} (g h : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => g js + h js) = expectIdx n k g + expectIdx n k h := by
  unfold expectIdx; rw [Finset.sum_add_distrib, mul_add]

lemma expect_mul {n k : ℕ} (c : ℝ) (g : (Fin k → Fin n) → ℝ) :
    expectIdx n k (fun js => c * g js) = c * expectIdx n k g := by
  unfold expectIdx; rw [← Finset.mul_sum]; ring

lemma avg_lin {n : ℕ} (hn : 0 < n) (u w : Fin n → ℝ) (c1 c2 K C : ℝ) :
    (1 / (n : ℝ)) * ∑ i, (c1 * (u i - K) + c2 * w i + C)
      = c1 * ((1 / (n : ℝ)) * ∑ i, u i - K) + c2 * ((1 / (n : ℝ)) * ∑ i, w i) + C := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Tower property for one uniformly drawn coordinate. -/
lemma tower {m n : ℕ} (hn : 0 < n) (k : Fin m) (H : (Fin m → Fin n) → Fin n → ℝ)
    (hinv : ∀ is i' i, H (Function.update is k i') i = H is i) :
    ∑ is, H is (is k) = ∑ is, (1 / (n : ℝ)) * ∑ i, H is i := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set Φ : (Fin m → Fin n) → ℝ := fun js => H js (js k) with hΦ
  have h1 : ∀ is, ∑ i, H is i = ∑ i, Φ (Function.update is k i) := by
    intro is; apply Finset.sum_congr rfl; intro i _
    simp only [hΦ, Function.update_self, hinv]
  let e : (Fin m → Fin n) × Fin n ≃ (Fin m → Fin n) × Fin n :=
    { toFun := fun p => (Function.update p.1 k p.2, p.1 k)
      invFun := fun p => (Function.update p.1 k p.2, p.1 k)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  have h2 : ∑ p : (Fin m → Fin n) × Fin n, Φ (Function.update p.1 k p.2)
      = ∑ p : (Fin m → Fin n) × Fin n, Φ p.1 :=
    Fintype.sum_equiv e _ _ (fun p => rfl)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  simp_rw [h1]
  rw [← Finset.mul_sum, h2, ← Finset.mul_sum]
  field_simp

lemma epochIter_update {d n m : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (s : ℕ)
    (xt : EuclideanSpace ℝ (Fin d))
    (yz : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (is : Fin m → Fin n)
    (k : Fin m) (i' : Fin n) :
    ∀ j, j ≤ k.1 → epochIter f' P L s xt yz (Function.update is k i') j
      = epochIter f' P L s xt yz is j := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    simp only [epochIter]
    split_ifs with h
    · rw [ih (by omega), Function.update_of_ne]
      intro heq
      have := congrArg Fin.val heq
      simp at this
      omega
    · exact ih (by omega)

lemma epochIter_succ {d n m : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ) (s : ℕ)
    (xt : EuclideanSpace ℝ (Fin d))
    (yz : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (is : Fin m → Fin n)
    (j : ℕ) (h : j < m) :
    epochIter f' P L s xt yz is (j + 1)
      = innerStep f' P L (tau1 s) (alpha L s) xt (epochIter f' P L s xt yz is j) (is ⟨j, h⟩) := by
  simp only [epochIter, dif_pos h]

end KatB034

open SAGA.Convex Katyusha.NonSC in
theorem KatB034.eqC1 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (s : ℕ) (xt y0 z0 : EuclideanSpace ℝ (Fin d)) :
    SAGA.Convex.expectIdx n m (fun is =>
        alpha L s * (1 - tau1 s - tau2) / tau1 s *
            (obj f ψ (epochIter f' P L s xt (y0, z0) is m).1 - obj f ψ xstar)
          + alpha L s * (tau1 s + tau2) / tau1 s *
            ∑ j ∈ Finset.Icc 1 m, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar))
      ≤ alpha L s * (1 - tau1 s - tau2) / tau1 s * (obj f ψ y0 - obj f ψ xstar)
        + alpha L s * tau2 / tau1 s * (m : ℝ) * (obj f ψ xt - obj f ψ xstar)
        + 1 / 2 * ‖z0 - xstar‖ ^ 2
        - 1 / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s xt (y0, z0) is m).2 - xstar‖ ^ 2) := by
  have hτ : 0 < tau1 s := by unfold tau1; positivity
  have hτh : tau1 s ≤ 1 / 2 := by
    unfold tau1; rw [div_le_iff₀ (by positivity)]; have : (0:ℝ) ≤ s := Nat.cast_nonneg s; linarith
  have hα : 0 < alpha L s := by unfold alpha; positivity
  have hτα : tau1 s ≤ 1 / (3 * alpha L s * L) := by
    unfold alpha
    rw [le_div_iff₀ (by positivity)]
    field_simp
    rfl
  have hc : (alpha L s * (1 - tau1 s - tau2) / tau1 s) + (alpha L s * (tau1 s + tau2) / tau1 s) = alpha L s / tau1 s := by field_simp; ring
  set V : (Fin m → Fin n) → ℕ → ℝ := fun is k =>
    ((alpha L s * (1 - tau1 s - tau2) / tau1 s) * (obj f ψ (epochIter f' P L s xt (y0, z0) is k).1 - obj f ψ xstar)
      + (alpha L s * (tau1 s + tau2) / tau1 s) * ∑ j ∈ Finset.Icc 1 k, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar))
      + 1 / 2 * ‖(epochIter f' P L s xt (y0, z0) is k).2 - xstar‖ ^ 2 with hV
  have claim : ∀ k, k ≤ m → expectIdx n m (fun is => V is k)
      ≤ (alpha L s * (1 - tau1 s - tau2) / tau1 s) * (obj f ψ y0 - obj f ψ xstar) + 1 / 2 * ‖z0 - xstar‖ ^ 2 + (k : ℝ) * (alpha L s * tau2 / tau1 s * (obj f ψ xt - obj f ψ xstar)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have : (fun is => V is 0) = fun _ => (alpha L s * (1 - tau1 s - tau2) / tau1 s) * (obj f ψ y0 - obj f ψ xstar)
          + 1 / 2 * ‖z0 - xstar‖ ^ 2 := by
        funext is; simp [hV, epochIter]
      rw [this, KatB034.expect_const hn]
      simp
    | succ k ih =>
      intro hk
      have hkm : k < m := by omega
      set H : (Fin m → Fin n) → Fin n → ℝ := fun is i =>
        ((alpha L s * (1 - tau1 s - tau2) / tau1 s) + (alpha L s * (tau1 s + tau2) / tau1 s)) * (obj f ψ (innerStep f' P L (tau1 s) (alpha L s) xt (epochIter f' P L s xt (y0, z0) is k) i).1 - obj f ψ xstar)
          + 1 / 2 * ‖(innerStep f' P L (tau1 s) (alpha L s) xt (epochIter f' P L s xt (y0, z0) is k) i).2 - xstar‖ ^ 2
          + (alpha L s * (tau1 s + tau2) / tau1 s) * ∑ j ∈ Finset.Icc 1 k, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar) with hH
      have hVH : ∀ is, V is (k + 1) = H is (is ⟨k, hkm⟩) := by
        intro is
        simp only [hV, hH]
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1),
          KatB034.epochIter_succ f' P L s xt (y0, z0) is k hkm]
        ring
      have hinv : ∀ is i' i, H (Function.update is ⟨k, hkm⟩ i') i = H is i := by
        intro is i' i
        simp only [hH]
        have hs : ∑ j ∈ Finset.Icc 1 k,
              (obj f ψ (epochIter f' P L s xt (y0, z0) (Function.update is ⟨k, hkm⟩ i') j).1 - obj f ψ xstar)
            = ∑ j ∈ Finset.Icc 1 k, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar) :=
          Finset.sum_congr rfl (fun j hj => by
            rw [KatB034.epochIter_update f' P L s xt (y0, z0) is ⟨k, hkm⟩ i' j
              (Finset.mem_Icc.mp hj).2])
        rw [KatB034.epochIter_update f' P L s xt (y0, z0) is ⟨k, hkm⟩ i' k le_rfl, hs]
      have hpt : ∀ is, (1 / (n : ℝ)) * ∑ i, H is i ≤ V is k + (alpha L s * tau2 / tau1 s * (obj f ψ xt - obj f ψ xstar)) := by
        intro is
        simp only [hH]
        rw [KatB034.avg_lin hn, hc]
        have L27 := KatB034.lemma27 hn f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar
          (tau1 s) (alpha L s) hα hτ hτh hτα xt (epochIter f' P L s xt (y0, z0) is k).1 (epochIter f' P L s xt (y0, z0) is k).2
        simp only [Prod.mk.eta] at L27
        simp only [hV]
        linarith
      have e1 : expectIdx n m (fun is => V is (k + 1))
          = expectIdx n m (fun is => H is (is ⟨k, hkm⟩)) := by
        congr 1; funext is; exact hVH is
      have e2 : expectIdx n m (fun is => H is (is ⟨k, hkm⟩))
          = expectIdx n m (fun is => (1 / (n : ℝ)) * ∑ i, H is i) := by
        unfold expectIdx; rw [KatB034.tower hn ⟨k, hkm⟩ H hinv]
      have e3 := KatB034.expect_mono _ (fun is => V is k + (alpha L s * tau2 / tau1 s * (obj f ψ xt - obj f ψ xstar))) hpt
      rw [KatB034.expect_add (fun is => V is k) (fun _ => (alpha L s * tau2 / tau1 s * (obj f ψ xt - obj f ψ xstar))), KatB034.expect_const hn] at e3
      have := ih (by omega)
      rw [e1, e2]
      push_cast
      linarith
  have hfin := claim m le_rfl
  have hsplit : expectIdx n m (fun is => V is m)
      = expectIdx n m (fun is =>
        (alpha L s * (1 - tau1 s - tau2) / tau1 s) * (obj f ψ (epochIter f' P L s xt (y0, z0) is m).1 - obj f ψ xstar)
          + (alpha L s * (tau1 s + tau2) / tau1 s) * ∑ j ∈ Finset.Icc 1 m, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar))
        + 1 / 2 * expectIdx n m (fun is => ‖(epochIter f' P L s xt (y0, z0) is m).2 - xstar‖ ^ 2) := by
    rw [← KatB034.expect_mul, ← KatB034.expect_add]
  linarith

open SAGA.Convex Katyusha.NonSC in
theorem KatB034.eqC1s {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (s : ℕ) (xt y0 z0 : EuclideanSpace ℝ (Fin d)) :
    SAGA.Convex.expectIdx n m (fun is =>
        1 / tau1 s ^ 2 * (obj f ψ (epochIter f' P L s xt (y0, z0) is m).1 - obj f ψ xstar)
          + (tau1 s + tau2) / tau1 s ^ 2 *
            ∑ j ∈ Finset.Ico 1 m, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar))
      ≤ (1 - tau1 s - tau2) / tau1 s ^ 2 * (obj f ψ y0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 s ^ 2 * (obj f ψ xt - obj f ψ xstar)
        + 3 * L / 2 * ‖z0 - xstar‖ ^ 2
        - 3 * L / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s xt (y0, z0) is m).2 - xstar‖ ^ 2) := by
  have h := KatB034.eqC1 hn hm f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar s xt y0 z0
  have hτ : 0 < tau1 s := by unfold tau1; positivity
  have hτne : tau1 s ≠ 0 := hτ.ne'
  have hLne : L ≠ 0 := hL.ne'
  have hfun : (fun is : Fin m → Fin n =>
        1 / tau1 s ^ 2 * (obj f ψ (epochIter f' P L s xt (y0, z0) is m).1 - obj f ψ xstar)
          + (tau1 s + tau2) / tau1 s ^ 2 *
            ∑ j ∈ Finset.Ico 1 m, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar))
      = fun is => (3 * L) * (alpha L s * (1 - tau1 s - tau2) / tau1 s *
            (obj f ψ (epochIter f' P L s xt (y0, z0) is m).1 - obj f ψ xstar)
          + alpha L s * (tau1 s + tau2) / tau1 s *
            ∑ j ∈ Finset.Icc 1 m, (obj f ψ (epochIter f' P L s xt (y0, z0) is j).1 - obj f ψ xstar)) := by
    funext is
    rw [Finset.Icc_eq_cons_Ico hm, Finset.sum_cons]
    unfold alpha
    field_simp
    ring
  rw [hfun, KatB034.expect_mul]
  have h3 := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 3 * L)
  have e : (3 * L) * (alpha L s * (1 - tau1 s - tau2) / tau1 s * (obj f ψ y0 - obj f ψ xstar)
        + alpha L s * tau2 / tau1 s * (m : ℝ) * (obj f ψ xt - obj f ψ xstar)
        + 1 / 2 * ‖z0 - xstar‖ ^ 2
        - 1 / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s xt (y0, z0) is m).2 - xstar‖ ^ 2))
      = (1 - tau1 s - tau2) / tau1 s ^ 2 * (obj f ψ y0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 s ^ 2 * (obj f ψ xt - obj f ψ xstar)
        + 3 * L / 2 * ‖z0 - xstar‖ ^ 2
        - 3 * L / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s xt (y0, z0) is m).2 - xstar‖ ^ 2) := by
    unfold alpha
    field_simp
  linarith

open SAGA.Convex Katyusha.NonSC in
theorem KatB034.objJensen {d n m : ℕ} (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i)) (hψ : ConvexOn ℝ Set.univ ψ)
    (yp : ℕ → EuclideanSpace ℝ (Fin d)) :
    obj f ψ ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1))
      ≤ (1 / (m : ℝ)) * ∑ t ∈ Finset.range m, obj f ψ (yp (t + 1)) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hJ : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ConvexOn ℝ Set.univ g →
      g ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1))
        ≤ (1 / (m : ℝ)) * ∑ t ∈ Finset.range m, g (yp (t + 1)) := by
    intro g hg
    have := hg.map_sum_le (t := Finset.range m) (w := fun _ => 1 / (m : ℝ))
      (p := fun t => yp (t + 1)) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
      (fun _ _ => Set.mem_univ _)
    rw [Finset.smul_sum, Finset.mul_sum]
    simpa [smul_eq_mul] using this
  unfold obj fAvg
  have h1 : ∀ i, f i ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1))
      ≤ (1 / (m : ℝ)) * ∑ t ∈ Finset.range m, f i (yp (t + 1)) := fun i => hJ _ (hf_conv i)
  have h2 := hJ ψ hψ
  have h3 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i))
    (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
  have e : (1 / (m : ℝ)) * ∑ t ∈ Finset.range m,
        ((1 / (n : ℝ)) * ∑ i, f i (yp (t + 1)) + ψ (yp (t + 1)))
      = (1 / (n : ℝ)) * ∑ i, ((1 / (m : ℝ)) * ∑ t ∈ Finset.range m, f i (yp (t + 1)))
        + (1 / (m : ℝ)) * ∑ t ∈ Finset.range m, ψ (yp (t + 1)) := by
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro t _
    ring
  linarith

open SAGA.Convex Katyusha.NonSC in
theorem KatB034.eqC2 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (s : ℕ) (hs : 1 ≤ s) (yp : ℕ → EuclideanSpace ℝ (Fin d)) (z0 : EuclideanSpace ℝ (Fin d)) :
    SAGA.Convex.expectIdx n m (fun is =>
        1 / tau1 s ^ 2 * (obj f ψ (epochIter f' P L s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m, z0) is m).1 - obj f ψ xstar)
          + (tau1 s + tau2) / tau1 s ^ 2 *
            ∑ j ∈ Finset.Ico 1 m,
              (obj f ψ (epochIter f' P L s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m, z0) is j).1 - obj f ψ xstar))
      ≤ (1 - tau1 s) / tau1 s ^ 2 * (obj f ψ (yp m) - obj f ψ xstar)
        + tau2 / tau1 s ^ 2 * ∑ j ∈ Finset.Ico 1 m, (obj f ψ (yp j) - obj f ψ xstar)
        + 3 * L / 2 * ‖z0 - xstar‖ ^ 2
        - 3 * L / 2 * SAGA.Convex.expectIdx n m (fun is =>
            ‖(epochIter f' P L s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m, z0) is m).2 - xstar‖ ^ 2) := by
  have h := KatB034.eqC1s hn hm f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar s ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) (yp m) z0
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hJ := KatB034.objJensen hm f ψ hf_conv hψ yp
  have hsum : ∑ t ∈ Finset.range m, (obj f ψ (yp (t + 1)) - obj f ψ xstar)
      = ∑ j ∈ Finset.Ico 1 m, (obj f ψ (yp j) - obj f ψ xstar) + (obj f ψ (yp m) - obj f ψ xstar) := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => obj f ψ (yp j) - obj f ψ xstar) 0 m 1,
      zero_add, Finset.sum_Ico_succ_top hm]
  have hsum2 : ∑ t ∈ Finset.range m, (obj f ψ (yp (t + 1)) - obj f ψ xstar)
      = ∑ t ∈ Finset.range m, obj f ψ (yp (t + 1)) - (m : ℝ) * obj f ψ xstar := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hJm : (m : ℝ) * obj f ψ ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1))
      ≤ ∑ t ∈ Finset.range m, obj f ψ (yp (t + 1)) := by
    have := mul_le_mul_of_nonneg_left hJ hmR.le
    have e : (m : ℝ) * ((1 / (m : ℝ)) * ∑ t ∈ Finset.range m, obj f ψ (yp (t + 1)))
        = ∑ t ∈ Finset.range m, obj f ψ (yp (t + 1)) := by field_simp
    linarith
  have hτ : 0 < tau1 s := by unfold tau1; positivity
  have hc : (0:ℝ) ≤ tau2 / tau1 s ^ 2 := by
    have : (0:ℝ) ≤ tau2 := by unfold tau2; norm_num
    positivity
  have hk := mul_le_mul_of_nonneg_left
    (show (m : ℝ) * (obj f ψ ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) - obj f ψ xstar)
      ≤ ∑ j ∈ Finset.Ico 1 m, (obj f ψ (yp j) - obj f ψ xstar) + (obj f ψ (yp m) - obj f ψ xstar) by
        rw [← hsum, hsum2]; linarith) hc
  have e1 : tau2 * (m : ℝ) / tau1 s ^ 2 *
        (obj f ψ ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) - obj f ψ xstar)
      = tau2 / tau1 s ^ 2 * ((m : ℝ) *
        (obj f ψ ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, yp (t + 1)) - obj f ψ xstar)) := by ring
  have e2 : (1 - tau1 s - tau2) / tau1 s ^ 2 * (obj f ψ (yp m) - obj f ψ xstar)
      + tau2 / tau1 s ^ 2 * (obj f ψ (yp m) - obj f ψ xstar)
      = (1 - tau1 s) / tau1 s ^ 2 * (obj f ψ (yp m) - obj f ψ xstar) := by ring
  linarith

namespace KatB034
open SAGA.Convex Katyusha.NonSC

lemma sum_blocks {n m S : ℕ} (G : (Fin S → Fin m → Fin n) → ℝ) :
    ∑ js : Fin (S * m) → Fin n, G (blocks js) = ∑ B : Fin S → Fin m → Fin n, G B := by
  let e : (Fin (S * m) → Fin n) ≃ (Fin S → Fin m → Fin n) :=
    ((finProdFinEquiv).arrowCongr (Equiv.refl (Fin n))).symm.trans (Equiv.curry _ _ _)
  exact Fintype.sum_equiv e _ _ (fun js => rfl)

lemma sum_snoc {X : Type*} [Fintype X] {S : ℕ} (G : (Fin (S + 1) → X) → ℝ) :
    ∑ B, G B = ∑ B' : Fin S → X, ∑ x : X, G (Fin.snoc B' x : Fin (S + 1) → X) := by
  let e : (Fin (S + 1) → X) ≃ (Fin S → X) × X :=
    { toFun := fun B => (Fin.init B, B (Fin.last S))
      invFun := fun p => (Fin.snoc p.1 p.2 : Fin (S + 1) → X)
      left_inv := fun B => Fin.snoc_init_self B
      right_inv := fun p => by simp }
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ (fun B => by simp [e, Fin.snoc_init_self])

lemma expect_split {n m S : ℕ} (hn : 0 < n) (G : (Fin (S + 1) → Fin m → Fin n) → ℝ) :
    expectIdx n ((S + 1) * m) (fun js => G (blocks js))
      = expectIdx n (S * m) (fun js => expectIdx n m (fun is =>
          G (Fin.snoc (blocks js) is : Fin (S + 1) → Fin m → Fin n))) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold expectIdx
  rw [sum_blocks, sum_snoc, ← Finset.mul_sum]
  have h := sum_blocks (S := S) (m := m) (n := n)
    (fun B' => ∑ is : Fin m → Fin n, G (Fin.snoc B' is : Fin (S + 1) → Fin m → Fin n))
  rw [h, Nat.succ_mul, pow_add]
  field_simp

lemma iterYZ_snoc {d n m : ℕ}
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (x0 : EuclideanSpace ℝ (Fin d)) (S' : ℕ) (B' : Fin (S' + 1) → Fin m → Fin n)
    (is : Fin m → Fin n) (j : ℕ) :
    iterYZ f' P L x0 (Fin.snoc B' is : Fin (S' + 2) → Fin m → Fin n) ⟨S' + 1, by omega⟩ j
      = epochIter f' P L (S' + 1)
          ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, (iterYZ f' P L x0 B' ⟨S', by omega⟩ (t + 1)).1)
          ((iterYZ f' P L x0 B' ⟨S', by omega⟩ m).1, (iterYZ f' P L x0 B' ⟨S', by omega⟩ m).2)
          is j := by
  have hC : (fun t : Fin (S' + 1) => (Fin.snoc B' is : Fin (S' + 2) → Fin m → Fin n)
      (Fin.castLE (by omega) t)) = B' := by
    funext t
    rw [show (Fin.castLE (by omega) t : Fin (S' + 2)) = Fin.castSucc t from Fin.ext rfl,
      Fin.snoc_castSucc]
  have hl : (Fin.snoc B' is : Fin (S' + 2) → Fin m → Fin n) ⟨S' + 1, by omega⟩ = is :=
    Fin.snoc_last (α := fun _ => Fin m → Fin n) (p := B') is
  simp only [iterYZ]
  rw [hC, hl]
  rfl

noncomputable def Phi {d n m : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : ℝ)
    (x0 xstar : EuclideanSpace ℝ (Fin d)) (S' : ℕ) (B : Fin (S' + 1) → Fin m → Fin n) : ℝ :=
  1 / tau1 S' ^ 2 * (obj f ψ (iterYZ f' P L x0 B ⟨S', by omega⟩ m).1 - obj f ψ xstar)
    + (tau1 S' + tau2) / tau1 S' ^ 2 *
      ∑ j ∈ Finset.Ico 1 m, (obj f ψ (iterYZ f' P L x0 B ⟨S', by omega⟩ j).1 - obj f ψ xstar)
    + 3 * L / 2 * ‖(iterYZ f' P L x0 B ⟨S', by omega⟩ m).2 - xstar‖ ^ 2

lemma tau_step (s : ℕ) :
    (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 ≤ 1 / tau1 s ^ 2 ∧
      tau2 / tau1 (s + 1) ^ 2 ≤ (tau1 s + tau2) / tau1 s ^ 2 := by
  have hx : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have h4 : (0 : ℝ) < (s : ℝ) + 4 := by linarith
  have h5 : (0 : ℝ) < (s : ℝ) + 5 := by linarith
  have e0 : tau1 s = 2 / ((s : ℝ) + 4) := rfl
  have e1 : tau1 (s + 1) = 2 / ((s : ℝ) + 5) := by
    unfold tau1; push_cast; ring_nf
  have et : tau2 = 1 / 2 := rfl
  have a1 : 1 / tau1 s ^ 2 = ((s : ℝ) + 4) ^ 2 / 4 := by
    rw [e0]; field_simp; norm_num
  have a2 : (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 = ((s : ℝ) + 3) * ((s : ℝ) + 5) / 4 := by
    rw [e1]; field_simp; ring
  have a3 : (tau1 s + tau2) / tau1 s ^ 2 = (((s : ℝ) + 4) / 2 + ((s : ℝ) + 4) ^ 2 / 8) := by
    rw [e0, et]; field_simp; ring
  have a4 : tau2 / tau1 (s + 1) ^ 2 = ((s : ℝ) + 5) ^ 2 / 8 := by
    rw [e1, et]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [a1, a2]; nlinarith
  · rw [a3, a4]; nlinarith

end KatB034

open SAGA.Convex Katyusha.NonSC in
theorem KatB034.eqC4key {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (x0 : EuclideanSpace ℝ (Fin d)) (S' : ℕ) :
    SAGA.Convex.expectIdx n ((S' + 1) * m) (fun js => KatB034.Phi f f' ψ P L x0 xstar S' (blocks js))
      ≤ (1 - tau1 0 - tau2) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by
  have hD : ∀ u, 0 ≤ obj f ψ u - obj f ψ xstar := fun u => sub_nonneg.mpr (hxstar u)
  induction S' with
  | zero =>
    rw [KatB034.expect_split hn]
    have h3 := KatB034.eqC1s hn hm f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar 0 x0 x0 x0
    have hin : ∀ js : Fin (0 * m) → Fin n, SAGA.Convex.expectIdx n m (fun is =>
        KatB034.Phi f f' ψ P L x0 xstar 0 (Fin.snoc (blocks js) is : Fin (0 + 1) → Fin m → Fin n))
        ≤ (1 - tau1 0 - tau2) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
          + tau2 * (m : ℝ) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
          + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by
      intro js
      have hit : ∀ (is : Fin m → Fin n) (j : ℕ),
          iterYZ f' P L x0 (Fin.snoc (blocks js) is : Fin (0 + 1) → Fin m → Fin n) ⟨0, by omega⟩ j
            = epochIter f' P L 0 x0 (x0, x0) is j := by
        intro is j
        rfl
      have hfun : (fun is => KatB034.Phi f f' ψ P L x0 xstar 0
          (Fin.snoc (blocks js) is : Fin (0 + 1) → Fin m → Fin n))
          = fun is => (1 / tau1 0 ^ 2 * (obj f ψ (epochIter f' P L 0 x0 (x0, x0) is m).1 - obj f ψ xstar)
            + (tau1 0 + tau2) / tau1 0 ^ 2 *
              ∑ j ∈ Finset.Ico 1 m, (obj f ψ (epochIter f' P L 0 x0 (x0, x0) is j).1 - obj f ψ xstar))
            + 3 * L / 2 * ‖(epochIter f' P L 0 x0 (x0, x0) is m).2 - xstar‖ ^ 2 := by
        funext is
        simp only [KatB034.Phi, hit]
      rw [hfun, KatB034.expect_add, KatB034.expect_mul]
      linarith
    exact le_trans (KatB034.expect_mono _ _ hin) (le_of_eq (KatB034.expect_const hn _))
  | succ S' ih =>
    rw [KatB034.expect_split hn]
    refine le_trans (KatB034.expect_mono _ (fun js => KatB034.Phi f f' ψ P L x0 xstar S' (blocks js)) ?_) ih
    intro js
    generalize blocks js = B'
    have h2 := KatB034.eqC2 hn hm f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar (S' + 1) (by omega)
      (fun j => (iterYZ f' P L x0 B' ⟨S', by omega⟩ j).1) (iterYZ f' P L x0 B' ⟨S', by omega⟩ m).2
    simp only at h2
    have hfun : (fun is => KatB034.Phi f f' ψ P L x0 xstar (S' + 1)
          (Fin.snoc B' is : Fin (S' + 1 + 1) → Fin m → Fin n))
        = fun is => (1 / tau1 (S' + 1) ^ 2 * (obj f ψ (epochIter f' P L (S' + 1)
              ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, (iterYZ f' P L x0 B' ⟨S', by omega⟩ (t + 1)).1)
              ((iterYZ f' P L x0 B' ⟨S', by omega⟩ m).1, (iterYZ f' P L x0 B' ⟨S', by omega⟩ m).2)
              is m).1 - obj f ψ xstar)
            + (tau1 (S' + 1) + tau2) / tau1 (S' + 1) ^ 2 * ∑ j ∈ Finset.Ico 1 m,
              (obj f ψ (epochIter f' P L (S' + 1)
              ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, (iterYZ f' P L x0 B' ⟨S', by omega⟩ (t + 1)).1)
              ((iterYZ f' P L x0 B' ⟨S', by omega⟩ m).1, (iterYZ f' P L x0 B' ⟨S', by omega⟩ m).2)
              is j).1 - obj f ψ xstar))
            + 3 * L / 2 * ‖(epochIter f' P L (S' + 1)
              ((1 / (m : ℝ)) • ∑ t ∈ Finset.range m, (iterYZ f' P L x0 B' ⟨S', by omega⟩ (t + 1)).1)
              ((iterYZ f' P L x0 B' ⟨S', by omega⟩ m).1, (iterYZ f' P L x0 B' ⟨S', by omega⟩ m).2)
              is m).2 - xstar‖ ^ 2 := by
      funext is
      simp only [KatB034.Phi, KatB034.iterYZ_snoc]
    rw [hfun, KatB034.expect_add, KatB034.expect_mul]
    obtain ⟨t1, t2⟩ := KatB034.tau_step S'
    have hDm := hD (iterYZ f' P L x0 B' ⟨S', by omega⟩ m).1
    have hDs : 0 ≤ ∑ j ∈ Finset.Ico 1 m, (obj f ψ (iterYZ f' P L x0 B' ⟨S', by omega⟩ j).1 - obj f ψ xstar) :=
      Finset.sum_nonneg (fun j _ => hD _)
    have m1 := mul_le_mul_of_nonneg_right t1 hDm
    have m2 := mul_le_mul_of_nonneg_right t2 hDs
    simp only [KatB034.Phi]
    linarith

open SAGA.Convex Katyusha.NonSC in
theorem KatB034.eqC4 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (x0 : EuclideanSpace ℝ (Fin d)) (S : ℕ) (hS : 1 ≤ S) :
    SAGA.Convex.expectIdx n (S * m) (fun js =>
        1 / tau1 (S - 1) ^ 2 * (obj f ψ (iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ m).1 - obj f ψ xstar)
          + (tau1 (S - 1) + tau2) / tau1 (S - 1) ^ 2 *
            ∑ j ∈ Finset.Ico 1 m, (obj f ψ (iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ j).1 - obj f ψ xstar)
          + 3 * L / 2 * ‖(iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ m).2 - xstar‖ ^ 2)
      ≤ (1 - tau1 0 - tau2) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by
  obtain ⟨S', rfl⟩ : ∃ S', S = S' + 1 := ⟨S - 1, by omega⟩
  exact KatB034.eqC4key hn hm f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar x0 S'

open SAGA.Convex Katyusha.NonSC in
theorem solution {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (x0 : EuclideanSpace ℝ (Fin d)) (S : ℕ) (hS : 1 ≤ S) :
    SAGA.Convex.expectIdx n (S * m) (fun js =>
        1 / tau1 (S - 1) ^ 2 * (obj f ψ (iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ m).1 - obj f ψ xstar)
          + (tau1 (S - 1) + tau2) / tau1 (S - 1) ^ 2 *
            ∑ j ∈ Finset.Ico 1 m, (obj f ψ (iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ j).1 - obj f ψ xstar)
          + 3 * L / 2 * ‖(iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ m).2 - xstar‖ ^ 2)
      ≤ (1 - tau1 0 - tau2) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by
  exact KatB034.eqC4 hn hm f f' ψ L hL hf_grad hf_conv hf_smooth hψ P hP xstar hxstar x0 S hS
