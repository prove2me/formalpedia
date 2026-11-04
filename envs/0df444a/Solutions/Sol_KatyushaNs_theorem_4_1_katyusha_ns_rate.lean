-- Prove2me | solution 1 for KatyushaNs.theorem_4_1_katyusha_ns_rate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T03:45:37.526853+00:00
-- url     : https://prove2.me/submissions/2bfb4673-265c-4347-a3f1-76e59666307b

import Mathlib
import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_IsKatyushaNsRun
import Definitions.Def_KatyushaNs_seqAvg

set_option autoImplicit false
set_option linter.all false

namespace KatNs1fd

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
-- Three-point property of a minimizer of `h + c‖· - w‖²` over a convex set.
open scoped RealInnerProductSpace in
lemma prox3 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {D : Set E} {h : E → ℝ}
    (hh : ConvexOn ℝ D h) {c : ℝ} (hc0 : 0 < c) {w p : E} (hpD : p ∈ D)
    (hp : ∀ u ∈ D, h p + c * ‖p - w‖ ^ 2 ≤ h u + c * ‖u - w‖ ^ 2) {u : E} (hu : u ∈ D) :
    h p + c * ‖p - w‖ ^ 2 + c * ‖u - p‖ ^ 2 ≤ h u + c * ‖u - w‖ ^ 2 := by
  set a := p - w
  set b := u - p
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ (h u - h p) + 2 * c * ⟪a, b⟫ + t * (c * ‖b‖ ^ 2) := by
    intro t ht0 ht1
    have e : (1 - t) • p + t • u = p + t • b := by simp only [b]; module
    have hmem : p + t • b ∈ D := by
      have := hh.1 hpD hu (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      rwa [e] at this
    have h1 := hp (p + t • b) hmem
    have h2 : h (p + t • b) ≤ (1 - t) * h p + t * h u := by
      have := hh.2 hpD hu (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      rw [e] at this
      simpa [smul_eq_mul] using this
    have e2 : p + t • b - w = a + t • b := by simp only [a]; abel
    rw [e2, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0, mul_pow] at h1
    have h3 : 0 ≤ t * ((h u - h p) + 2 * c * ⟪a, b⟫ + t * (c * ‖b‖ ^ 2)) := by
      nlinarith
    exact (mul_nonneg_iff_of_pos_left ht0).mp h3
  have hlim : 0 ≤ (h u - h p) + 2 * c * ⟪a, b⟫ := by
    by_contra hneg
    push Not at hneg
    set e := (h u - h p) + 2 * c * ⟪a, b⟫ with he
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

open scoped RealInnerProductSpace in
lemma linConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {D : Set E}
    (hD : Convex ℝ D) (g : E) : ConvexOn ℝ D (fun w => ⟪g, w⟫) := by
  refine ⟨hD, fun x _ y _ a b _ _ _ => ?_⟩
  simp [inner_add_right, real_inner_smul_right]

open scoped RealInnerProductSpace in
lemma qprox3 {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {κ : ℝ} (hκ : 0 < κ) {c g p : EuclideanSpace ℝ (Fin d)}
    (hp : KatyushaNs.IsQuadProxMin D ψ κ c g p) {u : EuclideanSpace ℝ (Fin d)} (hu : u ∈ D) :
    κ / 2 * ‖p - c‖ ^ 2 + ⟪g, p⟫ + ψ p + κ / 2 * ‖u - p‖ ^ 2
      ≤ κ / 2 * ‖u - c‖ ^ 2 + ⟪g, u⟫ + ψ u := by
  have hh : ConvexOn ℝ D (fun w => ⟪g, w⟫ + ψ w) := (linConvex hψ.1 g).add hψ
  have h3 : ⟪g, p⟫ + ψ p + κ / 2 * ‖p - c‖ ^ 2 + κ / 2 * ‖u - p‖ ^ 2
      ≤ ⟪g, u⟫ + ψ u + κ / 2 * ‖u - c‖ ^ 2 :=
    prox3 hh (c := κ / 2) (by positivity) hp.1
      (fun w hw => by
        show ⟪g, p⟫ + ψ p + κ / 2 * ‖p - c‖ ^ 2 ≤ ⟪g, w⟫ + ψ w + κ / 2 * ‖w - c‖ ^ 2
        have := hp.2 w hw; linarith) hu
  linarith

lemma qprox_unique {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {κ : ℝ} (hκ : 0 < κ) {c g p q : EuclideanSpace ℝ (Fin d)}
    (hp : KatyushaNs.IsQuadProxMin D ψ κ c g p) (hq : KatyushaNs.IsQuadProxMin D ψ κ c g q) :
    p = q := by
  have h1 := qprox3 hψ hκ hp hq.1
  have h2 := hq.2 p hp.1
  have hsq : κ / 2 * ‖q - p‖ ^ 2 ≤ 0 := by linarith
  have h0 : ‖q - p‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖q - p‖]) (sq_nonneg _)
  have : q - p = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    exact norm_eq_zero.mp this
  exact (sub_eq_zero.mp this).symm

open scoped RealInnerProductSpace in
lemma favg_grad {d n : ℕ} {L : ℝ} {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ}
    (hfi : ∀ i, KatyushaNs.IsConvexLSmooth L (fi i)) (u : EuclideanSpace ℝ (Fin d)) :
    gradient (KatyushaNs.favg fi) u = (1 / (n : ℝ)) • ∑ i, gradient (fi i) u := by
  have hG : ∀ i, HasGradientAt (fi i) (gradient (fi i) u) u :=
    fun i => ((hfi i).2.1 u).hasGradientAt
  have hS : HasFDerivAt (fun v => ∑ i, fi i v)
      (∑ i, InnerProductSpace.toDual ℝ _ (gradient (fi i) u)) u :=
    HasFDerivAt.fun_sum (fun i _ => hasGradientAt_iff_hasFDerivAt.mp (hG i))
  have hA : HasGradientAt (KatyushaNs.favg fi) ((1 / (n : ℝ)) • ∑ i, gradient (fi i) u) u := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have e : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
        ((1 / (n : ℝ)) • ∑ i, gradient (fi i) u)
        = (n : ℝ)⁻¹ • ∑ i, InnerProductSpace.toDual ℝ _ (gradient (fi i) u) := by
      rw [map_smulₛₗ, map_sum]; simp [one_div]
    rw [e]
    exact hS.const_mul ((n : ℝ)⁻¹)
  exact hA.gradient

-- One inner step (Allen-Zhu, proof of Lemma 2.7), for a fixed index, prox steps on `D`.
open scoped RealInnerProductSpace in
lemma per_step {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {L τ1 t2 : ℝ} (hL : 0 < L) (hτ1 : 0 < τ1) (hτ1lt : τ1 < 1)
    (ht2 : 0 ≤ t2) (hc0 : 0 ≤ 1 - τ1 - t2)
    (F0 : EuclideanSpace ℝ (Fin d) → ℝ) (x xt y z xs g gb yp zp : EuclideanSpace ℝ (Fin d))
    (hxt : xt ∈ D) (hy : y ∈ D) (hxs : xs ∈ D)
    (hx : x = τ1 • z + t2 • xt + (1 - τ1 - t2) • y)
    (hdesc : ∀ u, F0 u ≤ F0 x + ⟪gb, u - x⟫ + L / 2 * ‖u - x‖ ^ 2)
    (hY : KatyushaNs.IsQuadProxMin D ψ (3 * L) x g yp)
    (hZ : KatyushaNs.IsQuadProxMin D ψ (3 * τ1 * L) z g zp) :
    F0 yp + ψ yp
      ≤ (F0 x + 3 * τ1 ^ 2 * L / 2 * ‖z - xs‖ ^ 2 + τ1 * ψ xs + t2 * ψ xt
          + (1 - τ1 - t2) * ψ y)
        - τ1 * ⟪g, z - xs⟫ + ‖gb - g‖ ^ 2 / (4 * L)
        - 3 * τ1 ^ 2 * L / 2 * ‖zp - xs‖ ^ 2 := by
  have hconv := hψ.1
  have hzp := hZ.1
  set v := τ1 • zp + t2 • xt + (1 - τ1 - t2) • y with hv
  have hpos : 0 < 1 - τ1 := by linarith
  set w := (t2 / (1 - τ1)) • xt + ((1 - τ1 - t2) / (1 - τ1)) • y with hwdef
  have hwD : w ∈ D := hconv hxt hy (div_nonneg ht2 hpos.le) (div_nonneg hc0 hpos.le)
    (by field_simp; ring)
  have c1 : (1 - τ1) * (t2 / (1 - τ1)) = t2 := by field_simp
  have c2 : (1 - τ1) * ((1 - τ1 - t2) / (1 - τ1)) = 1 - τ1 - t2 := by field_simp
  have hv2 : v = τ1 • zp + (1 - τ1) • w := by
    rw [hv, hwdef, smul_add, smul_smul, smul_smul, c1, c2, add_assoc]
  have hvD : v ∈ D := by
    rw [hv2]; exact hconv hzp hwD hτ1.le hpos.le (by ring)
  have hψv : ψ v ≤ τ1 * ψ zp + t2 * ψ xt + (1 - τ1 - t2) * ψ y := by
    have hw : ψ w ≤ t2 / (1 - τ1) * ψ xt + (1 - τ1 - t2) / (1 - τ1) * ψ y := by
      have := hψ.2 hxt hy (div_nonneg ht2 hpos.le) (div_nonneg hc0 hpos.le) (by field_simp; ring)
      simpa [smul_eq_mul] using this
    have h1 := hψ.2 hzp hwD hτ1.le hpos.le (by ring)
    simp only [smul_eq_mul] at h1
    rw [hv2]
    have h2 := mul_le_mul_of_nonneg_left hw hpos.le
    have e : (1 - τ1) * (t2 / (1 - τ1) * ψ xt + (1 - τ1 - t2) / (1 - τ1) * ψ y)
        = t2 * ψ xt + (1 - τ1 - t2) * ψ y := by
      field_simp
    linarith
  have hvx : v - x = τ1 • (zp - z) := by rw [hv, hx]; module
  have hYv := hY.2 v hvD
  have e3 : ⟪g, v⟫ = ⟪g, x⟫ + τ1 * ⟪g, zp⟫ - τ1 * ⟪g, z⟫ := by
    have : v = x + τ1 • (zp - z) := by rw [← hvx]; abel
    rw [this, inner_add_right, real_inner_smul_right, inner_sub_right]; ring
  have e4 : ‖v - x‖ ^ 2 = τ1 ^ 2 * ‖zp - z‖ ^ 2 := by
    rw [hvx, norm_smul, Real.norm_eq_abs, abs_of_pos hτ1, mul_pow]
  rw [e3, e4] at hYv
  have hZ3 := qprox3 hψ (by positivity : (0:ℝ) < 3 * τ1 * L) hZ hxs
  rw [norm_sub_rev xs zp, norm_sub_rev xs z] at hZ3
  have hD := hdesc yp
  have e1 : ⟪gb, yp - x⟫ = ⟪gb, yp⟫ - ⟪gb, x⟫ := inner_sub_right _ _ _
  rw [e1] at hD
  have hYo := inner_young (gb - g) (yp - x) hL
  have e2 : ⟪gb - g, yp - x⟫ = ⟪gb, yp⟫ - ⟪gb, x⟫ - ⟪g, yp⟫ + ⟪g, x⟫ := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [e2] at hYo
  have e5 : ⟪g, z - xs⟫ = ⟪g, z⟫ - ⟪g, xs⟫ := inner_sub_right _ _ _
  rw [e5]
  linear_combination hD + hYv + hYo + hψv + τ1 * hZ3

end KatNs1fd

namespace KatNs1fd

lemma avg_lin2 {n : ℕ} (hn : 0 < n) (u w : Fin n → ℝ) (c1 c2 K : ℝ) :
    (1 / (n : ℝ)) * ∑ i, (c1 * (u i - K) + c2 * w i)
      = c1 * ((1 / (n : ℝ)) * ∑ i, u i - K) + c2 * ((1 / (n : ℝ)) * ∑ i, w i) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end KatNs1fd

-- Lemma 2.7 averaged over the sampled index, in the `1/τ²` scale (α = 1/(3τL)).
open KatyushaNs RealInnerProductSpace in
theorem KatNs1fd.lemma27 {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    (τ1 : ℝ) (hτ1 : 0 < τ1) (hτ1_half : τ1 ≤ 1 / 2)
    (x xt y z : EuclideanSpace ℝ (Fin d)) (hxt : xt ∈ D) (hy : y ∈ D)
    (hx : x = τ1 • z + (1 / 2 : ℝ) • xt + (1 - τ1 - 1 / 2) • y)
    (yp zp : Fin n → EuclideanSpace ℝ (Fin d))
    (hY : ∀ i, IsQuadProxMin D ψ (3 * L) x (svrgEst fi xt x i) (yp i))
    (hZ : ∀ i, IsQuadProxMin D ψ (3 * τ1 * L) z (svrgEst fi xt x i) (zp i)) :
    (1 / (n : ℝ)) * ∑ i, (1 / τ1 ^ 2 * (Fobj fi ψ (yp i) - Fobj fi ψ xstar)
        + 3 * L / 2 * ‖zp i - xstar‖ ^ 2)
      ≤ (1 - τ1 - 1 / 2) / τ1 ^ 2 * (Fobj fi ψ y - Fobj fi ψ xstar)
        + (1 / 2) / τ1 ^ 2 * (Fobj fi ψ xt - Fobj fi ψ xstar)
        + 3 * L / 2 * ‖z - xstar‖ ^ 2 := by
  have ht20 : (0:ℝ) ≤ 1 / 2 := by norm_num
  have hc0 : 0 ≤ 1 - τ1 - 1 / 2 := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn' : (n : ℝ) ≠ 0 := hnR.ne'
  have hgrad : ∀ i u, HasGradientAt (fi i) (gradient (fi i) u) u :=
    fun i u => ((hfi i).2.1 u).hasGradientAt
  have hlip : ∀ i u v, ‖gradient (fi i) u - gradient (fi i) v‖ ≤ L * ‖u - v‖ :=
    fun i => (hfi i).2.2
  have hconv : ∀ i, ConvexOn ℝ Set.univ (fi i) := fun i => (hfi i).1
  have hfavg : ∀ u, favg fi u = (1 / (n : ℝ)) * ∑ i, fi i u := by
    intro u; unfold favg; rw [one_div]
  set gb := (1 / (n : ℝ)) • ∑ i, gradient (fi i) x with hgb
  have hdesc : ∀ u, favg fi u ≤ favg fi x + ⟪gb, u - x⟫ + L / 2 * ‖u - x‖ ^ 2 := by
    intro u
    have hi : ∀ i, fi i u ≤ fi i x + ⟪gradient (fi i) x, u - x⟫ + L / 2 * ‖u - x‖ ^ 2 :=
      fun i => KatNs1fd.descent (hgrad i) (hlip i) x u
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have hg : ⟪gb, u - x⟫ = (1 / (n : ℝ)) * ⟪∑ i, gradient (fi i) x, u - x⟫ := by
      rw [hgb, real_inner_smul_left]
    rw [hfavg u, hfavg x, hg]
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    have e : (1 / (n : ℝ)) * ((n : ℝ) * (L / 2 * ‖u - x‖ ^ 2)) = L / 2 * ‖u - x‖ ^ 2 := by
      field_simp
    linarith
  have hcvx : ∀ u, favg fi x + ⟪gb, u - x⟫ ≤ favg fi u := by
    intro u
    have hi : ∀ i, fi i x + ⟪gradient (fi i) x, u - x⟫ ≤ fi i u :=
      fun i => KatNs1fd.convex_fo (hgrad i) (hconv i) x u
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
    rw [Finset.sum_add_distrib, ← sum_inner] at hs
    have hg : ⟪gb, u - x⟫ = (1 / (n : ℝ)) * ⟪∑ i, gradient (fi i) x, u - x⟫ := by
      rw [hgb, real_inner_smul_left]
    rw [hfavg u, hfavg x, hg]
    have := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    linarith
  have hgxt := KatNs1fd.favg_grad hfi xt
  -- the mean of the estimator
  have hsumg : ∑ i, svrgEst fi xt x i = (n : ℝ) • gb := by
    have e1 : (n : ℝ) • ((1 / (n : ℝ)) • ∑ i, gradient (fi i) xt) = ∑ i, gradient (fi i) xt := by
      rw [smul_smul, mul_one_div_cancel hn', one_smul]
    have e2 : (n : ℝ) • gb = ∑ i, gradient (fi i) x := by
      rw [hgb, smul_smul, mul_one_div_cancel hn', one_smul]
    simp only [svrgEst, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    rw [hgxt, ← Nat.cast_smul_eq_nsmul ℝ, e1, e2]
    abel
  -- variance bound
  have hvar : (1 / (n : ℝ)) * ∑ i, ‖gb - svrgEst fi xt x i‖ ^ 2
      ≤ 2 * L * (favg fi xt - favg fi x - ⟪gb, xt - x⟫) := by
    set a : Fin n → EuclideanSpace ℝ (Fin d) := fun i => gradient (fi i) x - gradient (fi i) xt
      with ha
    have hv := KatNs1fd.var_le hn a
    have hma : (1 / (n : ℝ)) • ∑ j, a j = gb - gradient (favg fi) xt := by
      rw [hgxt]; simp only [ha, Finset.sum_sub_distrib, smul_sub, hgb]
    have hnorm : ∀ i, ‖gb - svrgEst fi xt x i‖ ^ 2 = ‖a i - (1 / (n : ℝ)) • ∑ j, a j‖ ^ 2 := by
      intro i
      rw [hma, ← norm_neg]
      congr 2
      simp only [svrgEst, ha]
      abel
    simp_rw [hnorm]
    have hco : ∀ i, ‖a i‖ ^ 2 ≤ 2 * L * (fi i xt - fi i x - ⟪gradient (fi i) x, xt - x⟫) := by
      intro i
      have := KatNs1fd.cocoercive hL (hgrad i) (hlip i) (hconv i) x xt
      show ‖gradient (fi i) x - gradient (fi i) xt‖ ^ 2 ≤ _
      rw [norm_sub_rev]; exact this
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hco i)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← sum_inner] at hs
    have hg : ⟪gb, xt - x⟫ = (1 / (n : ℝ)) * ⟪∑ i, gradient (fi i) x, xt - x⟫ := by
      rw [hgb, real_inner_smul_left]
    rw [hfavg xt, hfavg x, hg]
    have h1 := mul_le_mul_of_nonneg_left (hv.trans hs) (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
    linarith
  -- per-index inequality
  have per : ∀ i, Fobj fi ψ (yp i)
      ≤ (favg fi x + 3 * τ1 ^ 2 * L / 2 * ‖z - xstar‖ ^ 2 + τ1 * ψ xstar + (1 / 2 : ℝ) * ψ xt
          + (1 - τ1 - (1 / 2 : ℝ)) * ψ y)
        - τ1 * ⟪svrgEst fi xt x i, z - xstar⟫ + ‖gb - svrgEst fi xt x i‖ ^ 2 / (4 * L)
        - 3 * τ1 ^ 2 * L / 2 * ‖zp i - xstar‖ ^ 2 :=
    fun i => KatNs1fd.per_step hψ hL hτ1 (by linarith) ht20 hc0 (favg fi) x xt y z xstar
      (svrgEst fi xt x i) gb (yp i) (zp i) hxt hy hxs hx hdesc (hY i) (hZ i)
  have hav := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => per i)
    (by positivity : (0:ℝ) ≤ 1 / (n : ℝ))
  have hR : (1 / (n : ℝ)) * ∑ i, ((favg fi x + 3 * τ1 ^ 2 * L / 2 * ‖z - xstar‖ ^ 2
          + τ1 * ψ xstar + (1 / 2 : ℝ) * ψ xt + (1 - τ1 - (1 / 2 : ℝ)) * ψ y)
        - τ1 * ⟪svrgEst fi xt x i, z - xstar⟫ + ‖gb - svrgEst fi xt x i‖ ^ 2 / (4 * L)
        - 3 * τ1 ^ 2 * L / 2 * ‖zp i - xstar‖ ^ 2)
      = (favg fi x + 3 * τ1 ^ 2 * L / 2 * ‖z - xstar‖ ^ 2 + τ1 * ψ xstar + (1 / 2 : ℝ) * ψ xt
          + (1 - τ1 - (1 / 2 : ℝ)) * ψ y)
        - τ1 * ⟪gb, z - xstar⟫
        + ((1 / (n : ℝ)) * ∑ i, ‖gb - svrgEst fi xt x i‖ ^ 2) / (4 * L)
        - 3 * τ1 ^ 2 * L / 2 * ((1 / (n : ℝ)) * ∑ i, ‖zp i - xstar‖ ^ 2) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_div,
      ← sum_inner]
    rw [hsumg, real_inner_smul_left]
    field_simp
  rw [hR] at hav
  -- coupling identity
  have hcpl : τ1 * ⟪gb, z - xstar⟫ = τ1 * ⟪gb, x - xstar⟫ + (1 / 2 : ℝ) * ⟪gb, x - xt⟫
      + (1 - τ1 - (1 / 2 : ℝ)) * ⟪gb, x - y⟫ := by
    have e : τ1 • (z - xstar) = τ1 • (x - xstar) + (1 / 2 : ℝ) • (x - xt) + (1 - τ1 - (1 / 2 : ℝ)) • (x - y) := by
      rw [hx]; module
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
  have e3 : 2 * L * (favg fi xt - favg fi x - ⟪gb, xt - x⟫) / (4 * L)
      = (1 / 2 : ℝ) * (favg fi xt - favg fi x - ⟪gb, xt - x⟫) := by
    field_simp; ring
  rw [e3] at hvd
  have e4 : ⟪gb, xt - x⟫ = -⟪gb, x - xt⟫ := by rw [← inner_neg_right, neg_sub]
  rw [e4] at hvd
  set A := (1 / (n : ℝ)) * ∑ i, Fobj fi ψ (yp i) with hA
  set B := (1 / (n : ℝ)) * ∑ i, ‖zp i - xstar‖ ^ 2 with hB
  have key : A ≤ τ1 * Fobj fi ψ xstar + (1 / 2 : ℝ) * Fobj fi ψ xt + (1 - τ1 - (1 / 2 : ℝ)) * Fobj fi ψ y
      + 3 * τ1 ^ 2 * L / 2 * (‖z - xstar‖ ^ 2 - B) := by
    unfold Fobj
    linarith
  rw [avg_lin2 hn (fun i => Fobj fi ψ (yp i)) (fun i => ‖zp i - xstar‖ ^ 2)]
  rw [← hA, ← hB]
  have hk := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ 1 / τ1 ^ 2)
  have hc : 1 / τ1 ^ 2 * τ1 ^ 2 = 1 := by field_simp
  linear_combination hk + (3 * L / 2 * (‖z - xstar‖ ^ 2 - B)) * hc

namespace KatNs1fd
open KatyushaNs

lemma kdecomp {n : ℕ} (hn : 0 < n) (k : ℕ) :
    k / (2 * n) * (2 * n) + k % (2 * n) = k ∧ k % (2 * n) < 2 * n :=
  ⟨Nat.div_add_mod' k (2 * n), Nat.mod_lt _ (by omega)⟩

lemma alpha_inv (L : ℝ) (s : ℕ) : (alphaS L s)⁻¹ = 3 * tau1 s * L := by
  unfold alphaS; rw [one_div, inv_inv]

lemma tau1_pos (s : ℕ) : 0 < tau1 s := by unfold tau1; positivity

lemma tau1_le_half (s : ℕ) : tau1 s ≤ 1 / 2 := by
  unfold tau1; rw [div_le_iff₀ (by positivity)]
  have : (0:ℝ) ≤ s := Nat.cast_nonneg s
  linarith

lemma run_mem_yz {d n : ℕ} (hn : 0 < n) {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (ω : ℕ → Fin n) (k : ℕ) :
    y ω k ∈ D ∧ z ω k ∈ D := by
  cases k with
  | zero =>
    obtain ⟨⟨h1, h2, _⟩, _, _⟩ := hrun ω
    rw [h1, h2]; exact ⟨hx0, hx0⟩
  | succ k =>
    obtain ⟨hk, hj⟩ := kdecomp hn k
    have h := (hrun ω).2.1 (k / (2 * n)) (k % (2 * n)) hj
    rw [hk] at h
    exact ⟨h.2.2.1, h.2.1.1⟩

lemma run_mem_xt {d n : ℕ} (hn : 0 < n) {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} (hD : Convex ℝ D) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (ω : ℕ → Fin n) (s : ℕ) :
    xt ω s ∈ D := by
  cases s with
  | zero => rw [(hrun ω).1.2.2]; exact hx0
  | succ s =>
    rw [(hrun ω).2.2 s, Finset.smul_sum]
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    apply hD.sum_mem
    · intro i _; positivity
    · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
    · intro j _; exact (run_mem_yz hn hx0 hrun ω _).1

lemma xt_congr {d n : ℕ} {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin d)}
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (ω ω' : ℕ → Fin n) (s : ℕ)
    (hy : ∀ t ≤ s * (2 * n), y ω t = y ω' t) : xt ω s = xt ω' s := by
  cases s with
  | zero => rw [(hrun ω).1.2.2, (hrun ω').1.2.2]
  | succ s =>
    rw [(hrun ω).2.2 s, (hrun ω').2.2 s]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply hy
    have := Finset.mem_range.mp hj
    have e : (s + 1) * (2 * n) = s * (2 * n) + 2 * n := by ring
    rw [e]; omega

lemma yz_congr {d n : ℕ} (hn : 0 < n) {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ}
    (hL : 0 < L) {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)}
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    ∀ k (ω ω' : ℕ → Fin n), (∀ j < k, ω j = ω' j) → y ω k = y ω' k ∧ z ω k = z ω' k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro ω ω' hag
  cases k with
  | zero =>
    rw [(hrun ω).1.1, (hrun ω).1.2.1, (hrun ω').1.1, (hrun ω').1.2.1]; exact ⟨rfl, rfl⟩
  | succ k =>
    obtain ⟨hk, hj⟩ := kdecomp hn k
    have hyk : ∀ t ≤ k, y ω t = y ω' t :=
      fun t ht => (ih t (by omega) ω ω' (fun i hi => hag i (by omega))).1
    have hzk := (ih k (by omega) ω ω' (fun i hi => hag i (by omega))).2
    have hxt := xt_congr hrun ω ω' (k / (2 * n)) (fun t ht => hyk t (by omega))
    have hω : ω k = ω' k := hag k (by omega)
    have h := (hrun ω).2.1 (k / (2 * n)) (k % (2 * n)) hj
    have h' := (hrun ω').2.1 (k / (2 * n)) (k % (2 * n)) hj
    rw [hk] at h h'
    have hx : x ω (k + 1) = x ω' (k + 1) := by rw [h.1, h'.1, hzk, hxt, hyk k le_rfl]
    rw [hx, hxt, hω, hzk] at h
    have hapos : 0 < (alphaS L (k / (2 * n)))⁻¹ := by
      rw [alpha_inv]; have := tau1_pos (k / (2 * n)); positivity
    exact ⟨qprox_unique hψ (by positivity) h.2.2 h'.2.2, qprox_unique hψ hapos h.2.1 h'.2.1⟩

/-! Expectations over the uniform indices. -/

def Dep {n : ℕ} (N : ℕ) (X : (ℕ → Fin n) → ℝ) : Prop :=
  ∀ ω ω' : ℕ → Fin n, (∀ j < N, ω j = ω' j) → X ω = X ω'

lemma seqAvg_const {n : ℕ} (hn : 0 < n) (N : ℕ) (c : ℝ) : seqAvg hn N (fun _ => c) = c := by
  unfold seqAvg
  have h : ((n : ℝ)) ^ N ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  field_simp

lemma seqAvg_mono {n : ℕ} (hn : 0 < n) (N : ℕ) (X Y : (ℕ → Fin n) → ℝ) (h : ∀ ω, X ω ≤ Y ω) :
    seqAvg hn N X ≤ seqAvg hn N Y := by
  unfold seqAvg
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun w _ => h _) (by positivity)

lemma seqAvg_add {n : ℕ} (hn : 0 < n) (N : ℕ) (X Y : (ℕ → Fin n) → ℝ) :
    seqAvg hn N (fun ω => X ω + Y ω) = seqAvg hn N X + seqAvg hn N Y := by
  unfold seqAvg; rw [Finset.sum_add_distrib, add_div]

lemma seqAvg_mul {n : ℕ} (hn : 0 < n) (N : ℕ) (c : ℝ) (X : (ℕ → Fin n) → ℝ) :
    seqAvg hn N (fun ω => c * X ω) = c * seqAvg hn N X := by
  unfold seqAvg; rw [← Finset.mul_sum, mul_div_assoc]

lemma seqAvg_sub_const {n : ℕ} (hn : 0 < n) (N : ℕ) (X : (ℕ → Fin n) → ℝ) (c : ℝ) :
    seqAvg hn N (fun ω => X ω - c) = seqAvg hn N X - c := by
  have h := seqAvg_add hn N X (fun _ => -c)
  rw [seqAvg_const hn] at h
  simp only [← sub_eq_add_neg] at h
  exact h

lemma sum_snoc {X : Type*} [Fintype X] {S : ℕ} (G : (Fin (S + 1) → X) → ℝ) :
    ∑ B, G B = ∑ B' : Fin S → X, ∑ x : X, G (Fin.snoc B' x : Fin (S + 1) → X) := by
  let e : (Fin (S + 1) → X) ≃ (Fin S → X) × X :=
    { toFun := fun B => (Fin.init B, B (Fin.last S))
      invFun := fun p => (Fin.snoc p.1 p.2 : Fin (S + 1) → X)
      left_inv := fun B => Fin.snoc_init_self B
      right_inv := fun p => by simp }
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv e _ _ (fun B => by simp [e, Fin.snoc_init_self])

lemma ext_snoc {n N : ℕ} (hn : 0 < n) (w : Fin N → Fin n) (i : Fin n) :
    ∀ j < N + 1, extendSeq hn (Fin.snoc w i : Fin (N + 1) → Fin n) j
      = Function.update (extendSeq hn w) N i j := by
  intro j hj
  rcases Nat.lt_or_ge j N with h | h
  · have hne : j ≠ N := by omega
    rw [Function.update_of_ne hne]
    simp only [extendSeq, dif_pos hj, dif_pos h]
    have : (⟨j, hj⟩ : Fin (N + 1)) = Fin.castSucc ⟨j, h⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  · have hjN : j = N := by omega
    subst hjN
    rw [Function.update_self]
    simp only [extendSeq, dif_pos hj]
    have : (⟨j, hj⟩ : Fin (j + 1)) = Fin.last j := rfl
    rw [this, Fin.snoc_last]

lemma seqAvg_succ {n : ℕ} (hn : 0 < n) (N : ℕ) (X : (ℕ → Fin n) → ℝ) (hX : Dep (N + 1) X) :
    seqAvg hn (N + 1) X
      = seqAvg hn N (fun ω => (1 / (n : ℝ)) * ∑ i, X (Function.update ω N i)) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold seqAvg
  rw [sum_snoc]
  have h : ∀ (w : Fin N → Fin n) (i : Fin n),
      X (extendSeq hn (Fin.snoc w i : Fin (N + 1) → Fin n))
        = X (Function.update (extendSeq hn w) N i) :=
    fun w i => hX _ _ (ext_snoc hn w i)
  simp_rw [h, ← Finset.mul_sum]
  rw [pow_succ]
  field_simp

lemma dep_mono {n : ℕ} {N M : ℕ} (hNM : N ≤ M) {X : (ℕ → Fin n) → ℝ} (hX : Dep N X) :
    Dep M X := fun ω ω' h => hX ω ω' (fun j hj => h j (by omega))

lemma seqAvg_drop {n : ℕ} (hn : 0 < n) (N : ℕ) (X : (ℕ → Fin n) → ℝ) (hX : Dep N X) :
    seqAvg hn (N + 1) X = seqAvg hn N X := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [seqAvg_succ hn N X (dep_mono (by omega) hX)]
  congr 1; funext ω
  have : ∀ i, X (Function.update ω N i) = X ω :=
    fun i => hX _ _ (fun j hj => Function.update_of_ne (by omega) _ _)
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma seqAvg_lift {n : ℕ} (hn : 0 < n) (N : ℕ) (X : (ℕ → Fin n) → ℝ) (hX : Dep N X) :
    ∀ j, seqAvg hn (N + j) X = seqAvg hn N X := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← add_assoc, seqAvg_drop hn (N + j) X (dep_mono (by omega) hX), ih]

end KatNs1fd

-- One inner iteration of the run, averaged over the index it samples.
open KatyushaNs in
theorem KatNs1fd.step_avg {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (s j : ℕ) (hj : j < 2 * n)
    (ω : ℕ → Fin n) :
    (1 / (n : ℝ)) * ∑ i, (1 / tau1 s ^ 2 *
        (Fobj fi ψ (y (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1))
          - Fobj fi ψ xstar)
        + 3 * L / 2 * ‖z (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1) - xstar‖ ^ 2)
      ≤ (1 - tau1 s - 1 / 2) / tau1 s ^ 2 * (Fobj fi ψ (y ω (s * (2 * n) + j)) - Fobj fi ψ xstar)
        + (1 / 2) / tau1 s ^ 2 * (Fobj fi ψ (xt ω s) - Fobj fi ψ xstar)
        + 3 * L / 2 * ‖z ω (s * (2 * n) + j) - xstar‖ ^ 2 := by
  have hag : ∀ i : Fin n, ∀ t < s * (2 * n) + j,
      Function.update ω (s * (2 * n) + j) i t = ω t :=
    fun i t ht => Function.update_of_ne (by omega) _ _
  have hyz : ∀ i : Fin n, ∀ t ≤ s * (2 * n) + j,
      y (Function.update ω (s * (2 * n) + j) i) t = y ω t ∧
        z (Function.update ω (s * (2 * n) + j) i) t = z ω t :=
    fun i t ht => KatNs1fd.yz_congr hn hL hψ hrun t _ ω (fun t' ht' => hag i t' (by omega))
  have hxt : ∀ i : Fin n, xt (Function.update ω (s * (2 * n) + j) i) s = xt ω s :=
    fun i => KatNs1fd.xt_congr hrun _ ω s (fun t ht => (hyz i t (by omega)).1)
  set X0 := tau1 s • z ω (s * (2 * n) + j) + (1 / 2 : ℝ) • xt ω s
    + (1 - tau1 s - 1 / 2) • y ω (s * (2 * n) + j) with hX0
  have hstep : ∀ i : Fin n,
      IsQuadProxMin D ψ (3 * L) X0 (svrgEst fi (xt ω s) X0 i)
          (y (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1)) ∧
        IsQuadProxMin D ψ (3 * tau1 s * L) (z ω (s * (2 * n) + j)) (svrgEst fi (xt ω s) X0 i)
          (z (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1)) := by
    intro i
    have h := (hrun (Function.update ω (s * (2 * n) + j) i)).2.1 s j hj
    have hx : x (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1) = X0 := by
      rw [h.1, (hyz i _ le_rfl).1, (hyz i _ le_rfl).2, hxt i]
    rw [hx, hxt i, Function.update_self, (hyz i _ le_rfl).2, alpha_inv] at h
    exact ⟨h.2.2, h.2.1⟩
  exact KatNs1fd.lemma27 hn hL hfi hψ hxs hmin (tau1 s) (KatNs1fd.tau1_pos s)
    (KatNs1fd.tau1_le_half s) X0 (xt ω s) (y ω (s * (2 * n) + j)) (z ω (s * (2 * n) + j))
    (KatNs1fd.run_mem_xt hn hψ.1 hx0 hrun ω s) (KatNs1fd.run_mem_yz hn hx0 hrun ω _).1 hX0
    _ _ (fun i => (hstep i).1) (fun i => (hstep i).2)

namespace KatNs1fd
open KatyushaNs

/-- The epoch potential after `j` inner steps of epoch `s` (Allen-Zhu, (C.1) in the `1/τ²` scale). -/
noncomputable def Vf {d n : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (xstar : EuclideanSpace ℝ (Fin d))
    (y z : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)) (s j : ℕ) (ω : ℕ → Fin n) : ℝ :=
  (1 - tau1 s - 1 / 2) / tau1 s ^ 2 * (Fobj fi ψ (y ω (s * (2 * n) + j)) - Fobj fi ψ xstar)
    + (tau1 s + 1 / 2) / tau1 s ^ 2 *
      ∑ t ∈ Finset.Icc 1 j, (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar)
    + 3 * L / 2 * ‖z ω (s * (2 * n) + j) - xstar‖ ^ 2

lemma tau_step (s : ℕ) :
    (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 ≤ 1 / tau1 s ^ 2 ∧
      (1 / 2) / tau1 (s + 1) ^ 2 ≤ (tau1 s + 1 / 2) / tau1 s ^ 2 := by
  have hx : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg s
  have h4 : (0 : ℝ) < (s : ℝ) + 4 := by linarith
  have h5 : (0 : ℝ) < (s : ℝ) + 5 := by linarith
  have e0 : tau1 s = 2 / ((s : ℝ) + 4) := rfl
  have e1 : tau1 (s + 1) = 2 / ((s : ℝ) + 5) := by
    unfold tau1; push_cast; ring_nf
  have a1 : 1 / tau1 s ^ 2 = ((s : ℝ) + 4) ^ 2 / 4 := by
    rw [e0]; field_simp; norm_num
  have a2 : (1 - tau1 (s + 1)) / tau1 (s + 1) ^ 2 = ((s : ℝ) + 3) * ((s : ℝ) + 5) / 4 := by
    rw [e1]; field_simp; ring
  have a3 : (tau1 s + 1 / 2) / tau1 s ^ 2 = (((s : ℝ) + 4) / 2 + ((s : ℝ) + 4) ^ 2 / 8) := by
    rw [e0]; field_simp; ring
  have a4 : (1 / 2) / tau1 (s + 1) ^ 2 = ((s : ℝ) + 5) ^ 2 / 8 := by
    rw [e1]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [a1, a2]; nlinarith
  · rw [a3, a4]; nlinarith

theorem objJensen {d n : ℕ} (hn : 0 < n) (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    {D : Set (EuclideanSpace ℝ (Fin d))} (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hconv : ∀ i, ConvexOn ℝ Set.univ (fi i)) (hψ : ConvexOn ℝ D ψ)
    (yp : ℕ → EuclideanSpace ℝ (Fin d)) (hyp : ∀ t, yp t ∈ D) :
    Fobj fi ψ ((1 / (2 * n : ℝ)) • ∑ t ∈ Finset.range (2 * n), yp (t + 1))
      ≤ (1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (yp (t + 1)) := by
  have hmR : (0:ℝ) < 2 * n := by have : (0:ℝ) < n := by exact_mod_cast hn
                                 linarith
  have hJ : ∀ (S : Set (EuclideanSpace ℝ (Fin d))) (g : EuclideanSpace ℝ (Fin d) → ℝ),
      ConvexOn ℝ S g → (∀ t, yp t ∈ S) →
      g ((1 / (2 * n : ℝ)) • ∑ t ∈ Finset.range (2 * n), yp (t + 1))
        ≤ (1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n), g (yp (t + 1)) := by
    intro S g hg hmem
    have := hg.map_sum_le (t := Finset.range (2 * n)) (w := fun _ => 1 / (2 * n : ℝ))
      (p := fun t => yp (t + 1)) (fun _ _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp)
      (fun _ _ => hmem _)
    rw [Finset.smul_sum, Finset.mul_sum]
    simpa [smul_eq_mul] using this
  unfold Fobj favg
  have h1 : ∀ i, fi i ((1 / (2 * n : ℝ)) • ∑ t ∈ Finset.range (2 * n), yp (t + 1))
      ≤ (1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n), fi i (yp (t + 1)) :=
    fun i => hJ Set.univ _ (hconv i) (fun _ => Set.mem_univ _)
  have h2 := hJ D ψ hψ hyp
  have h3 := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h1 i))
    (by positivity : (0:ℝ) ≤ (n : ℝ)⁻¹)
  have e : (1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n),
        ((n : ℝ)⁻¹ * ∑ i, fi i (yp (t + 1)) + ψ (yp (t + 1)))
      = (n : ℝ)⁻¹ * ∑ i, ((1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n), fi i (yp (t + 1)))
        + (1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n), ψ (yp (t + 1)) := by
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro t _
    ring
  linarith

lemma sum_split (m : ℕ) (hm : 1 ≤ m) (G : ℕ → ℝ) :
    ∑ t ∈ Finset.range m, G (t + 1) = ∑ j ∈ Finset.Ico 1 m, G j + G m := by
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' G 0 m 1, zero_add, Finset.sum_Ico_succ_top hm]

lemma Vf_end {d n : ℕ} (hn : 0 < n) (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (xstar : EuclideanSpace ℝ (Fin d))
    (y z : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)) (s : ℕ) (ω : ℕ → Fin n) :
    Vf fi ψ L xstar y z s (2 * n) ω
      = 1 / tau1 s ^ 2 * (Fobj fi ψ (y ω (s * (2 * n) + 2 * n)) - Fobj fi ψ xstar)
        + (tau1 s + 1 / 2) / tau1 s ^ 2 *
          ∑ t ∈ Finset.Ico 1 (2 * n), (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar)
        + 3 * L / 2 * ‖z ω (s * (2 * n) + 2 * n) - xstar‖ ^ 2 := by
  have hτ := (tau1_pos s).ne'
  unfold Vf
  rw [Finset.Icc_eq_cons_Ico (by omega : 1 ≤ 2 * n), Finset.sum_cons]
  field_simp
  ring

end KatNs1fd

-- (C.1) summed over one epoch.
open KatyushaNs in
theorem KatNs1fd.epoch {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (s : ℕ) :
    ∀ j ≤ 2 * n, seqAvg hn (s * (2 * n) + j) (KatNs1fd.Vf fi ψ L xstar y z s j)
      ≤ seqAvg hn (s * (2 * n)) (KatNs1fd.Vf fi ψ L xstar y z s 0)
        + (j : ℝ) * ((1 / 2) / tau1 s ^ 2 *
            seqAvg hn (s * (2 * n)) (fun ω => Fobj fi ψ (xt ω s) - Fobj fi ψ xstar)) := by
  have hyz := KatNs1fd.yz_congr hn hL hψ hrun
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjn : j < 2 * n := by omega
    have hdep : KatNs1fd.Dep (s * (2 * n) + j + 1) (KatNs1fd.Vf fi ψ L xstar y z s (j + 1)) := by
      intro ω ω' hag
      have hy : ∀ t ≤ j + 1, y ω (s * (2 * n) + t) = y ω' (s * (2 * n) + t) :=
        fun t ht => (hyz _ ω ω' (fun i hi => hag i (by omega))).1
      have hz := (hyz (s * (2 * n) + (j + 1)) ω ω' (fun i hi => hag i (by omega))).2
      unfold KatNs1fd.Vf
      rw [hy (j + 1) le_rfl, hz,
        Finset.sum_congr rfl (fun t ht => by rw [hy t (Finset.mem_Icc.mp ht).2])]
    have hdepx : KatNs1fd.Dep (s * (2 * n)) (fun ω => Fobj fi ψ (xt ω s) - Fobj fi ψ xstar) := by
      intro ω ω' hag
      simp only
      rw [KatNs1fd.xt_congr hrun ω ω' s
        (fun t ht => (hyz t ω ω' (fun i hi => hag i (by omega))).1)]
    have hpt : ∀ ω, (1 / (n : ℝ)) * ∑ i, KatNs1fd.Vf fi ψ L xstar y z s (j + 1)
          (Function.update ω (s * (2 * n) + j) i)
        ≤ KatNs1fd.Vf fi ψ L xstar y z s j ω
          + (1 / 2) / tau1 s ^ 2 * (Fobj fi ψ (xt ω s) - Fobj fi ψ xstar) := by
      intro ω
      have hst := KatNs1fd.step_avg hn hL hfi hψ hx0 hxs hmin hrun s j hjn ω
      have hsum : ∀ i : Fin n, ∑ t ∈ Finset.Icc 1 j,
          (Fobj fi ψ (y (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + t))
            - Fobj fi ψ xstar)
          = ∑ t ∈ Finset.Icc 1 j, (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar) := by
        intro i
        apply Finset.sum_congr rfl
        intro t ht
        have htj := (Finset.mem_Icc.mp ht).2
        rw [(hyz (s * (2 * n) + t) (Function.update ω (s * (2 * n) + j) i) ω
          (fun i' hi' => Function.update_of_ne (by omega) _ _)).1]
      have hτ := (KatNs1fd.tau1_pos s).ne'
      have hV : ∀ i : Fin n, KatNs1fd.Vf fi ψ L xstar y z s (j + 1)
            (Function.update ω (s * (2 * n) + j) i)
          = (1 / tau1 s ^ 2 *
              (Fobj fi ψ (y (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1))
                - Fobj fi ψ xstar)
            + 3 * L / 2 *
              ‖z (Function.update ω (s * (2 * n) + j) i) (s * (2 * n) + j + 1) - xstar‖ ^ 2)
            + (tau1 s + 1 / 2) / tau1 s ^ 2 *
              ∑ t ∈ Finset.Icc 1 j, (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar) := by
        intro i
        unfold KatNs1fd.Vf
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ j + 1), hsum i, ← add_assoc]
        field_simp
        ring
      simp_rw [hV]
      rw [Finset.sum_add_distrib, mul_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have e : 1 / (n : ℝ) * ((n : ℝ) * ((tau1 s + 1 / 2) / tau1 s ^ 2 *
          ∑ t ∈ Finset.Icc 1 j, (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar)))
          = (tau1 s + 1 / 2) / tau1 s ^ 2 *
          ∑ t ∈ Finset.Icc 1 j, (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar) := by
        field_simp
      rw [e]
      unfold KatNs1fd.Vf
      linarith
    rw [show s * (2 * n) + (j + 1) = s * (2 * n) + j + 1 from rfl,
      KatNs1fd.seqAvg_succ hn _ _ hdep]
    have h1 := KatNs1fd.seqAvg_mono hn (s * (2 * n) + j) _ _ hpt
    rw [KatNs1fd.seqAvg_add, KatNs1fd.seqAvg_mul hn _ ((1 / 2) / tau1 s ^ 2)
      (fun ω => Fobj fi ψ (xt ω s) - Fobj fi ψ xstar),
      KatNs1fd.seqAvg_lift hn _ _ hdepx j] at h1
    have h2 := ih (by omega)
    push_cast
    linear_combination h1 + h2

-- (C.4): the potential after epoch `s` is bounded by its initial value.
open KatyushaNs in
theorem KatNs1fd.eqC4 {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    ∀ s, seqAvg hn (s * (2 * n) + 2 * n) (KatNs1fd.Vf fi ψ L xstar y z s (2 * n))
      ≤ (1 - tau1 0 - 1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar)
        + ((2 * n : ℕ) : ℝ) * ((1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar))
        + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by
  have hDn : ∀ u ∈ D, 0 ≤ Fobj fi ψ u - Fobj fi ψ xstar :=
    fun u hu => sub_nonneg.mpr (hmin u hu)
  have h0 : Finset.Icc 1 0 = (∅ : Finset ℕ) := Finset.Icc_eq_empty (by norm_num)
  have hlin : ∀ s, seqAvg hn (s * (2 * n)) (KatNs1fd.Vf fi ψ L xstar y z s 0)
        + ((2 * n : ℕ) : ℝ) * ((1 / 2) / tau1 s ^ 2 *
            seqAvg hn (s * (2 * n)) (fun ω => Fobj fi ψ (xt ω s) - Fobj fi ψ xstar))
      = seqAvg hn (s * (2 * n)) (fun ω => KatNs1fd.Vf fi ψ L xstar y z s 0 ω
          + ((2 * n : ℕ) : ℝ) * ((1 / 2) / tau1 s ^ 2 * (Fobj fi ψ (xt ω s) - Fobj fi ψ xstar))) := by
    intro s
    rw [KatNs1fd.seqAvg_add, KatNs1fd.seqAvg_mul, KatNs1fd.seqAvg_mul]
  intro s
  induction s with
  | zero =>
    have hE := KatNs1fd.epoch hn hL hfi hψ hx0 hxs hmin hrun 0 (2 * n) le_rfl
    rw [hlin 0] at hE
    refine le_trans hE ?_
    have hf : (fun ω => KatNs1fd.Vf fi ψ L xstar y z 0 0 ω
          + ((2 * n : ℕ) : ℝ) * ((1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ (xt ω 0) - Fobj fi ψ xstar)))
        = fun _ => (1 - tau1 0 - 1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar)
          + ((2 * n : ℕ) : ℝ) * ((1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar))
          + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by
      funext ω
      simp only [KatNs1fd.Vf, zero_mul, add_zero, (hrun ω).1.1, (hrun ω).1.2.1, (hrun ω).1.2.2,
        h0, Finset.sum_empty, mul_zero]
      ring
    rw [hf, KatNs1fd.seqAvg_const]
  | succ s ih =>
    have hidx : (s + 1) * (2 * n) = s * (2 * n) + 2 * n := by ring
    have hE := KatNs1fd.epoch hn hL hfi hψ hx0 hxs hmin hrun (s + 1) (2 * n) le_rfl
    rw [hlin (s + 1)] at hE
    refine le_trans hE (le_trans (KatNs1fd.seqAvg_mono hn _ _
      (KatNs1fd.Vf fi ψ L xstar y z s (2 * n)) ?_) ?_)
    · intro ω
      rw [KatNs1fd.Vf_end hn]
      simp only [KatNs1fd.Vf, add_zero, h0, Finset.sum_empty, mul_zero, hidx]
      have hJ : Fobj fi ψ (xt ω (s + 1)) ≤ (1 / (2 * n : ℝ)) *
          ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (y ω (s * (2 * n) + (t + 1))) := by
        rw [(hrun ω).2.2 s]
        exact KatNs1fd.objJensen hn fi ψ (fun i => (hfi i).1) hψ (fun t => y ω (s * (2 * n) + t))
          (fun t => (KatNs1fd.run_mem_yz hn hx0 hrun ω _).1)
      have hsp := KatNs1fd.sum_split (2 * n) (by omega)
        (fun t => Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar)
      have hsum2 : ∑ t ∈ Finset.range (2 * n),
            (Fobj fi ψ (y ω (s * (2 * n) + (t + 1))) - Fobj fi ψ xstar)
          = ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (y ω (s * (2 * n) + (t + 1)))
            - ((2 * n : ℕ) : ℝ) * Fobj fi ψ xstar := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hmpos : (0:ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * n)
      have hJ2 : ((2 * n : ℕ) : ℝ) * (Fobj fi ψ (xt ω (s + 1)) - Fobj fi ψ xstar)
          ≤ ∑ t ∈ Finset.Ico 1 (2 * n), (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar)
            + (Fobj fi ψ (y ω (s * (2 * n) + 2 * n)) - Fobj fi ψ xstar) := by
        rw [← hsp, hsum2, mul_sub]
        have h1 := mul_le_mul_of_nonneg_left hJ hmpos.le
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have e : ((2 * n : ℕ) : ℝ) * ((1 / (2 * n : ℝ)) *
            ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (y ω (s * (2 * n) + (t + 1))))
            = ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (y ω (s * (2 * n) + (t + 1))) := by
          push_cast; field_simp
        rw [e] at h1
        linarith
      have hDend := hDn _ (KatNs1fd.run_mem_yz hn hx0 hrun ω (s * (2 * n) + 2 * n)).1
      have hSum : 0 ≤ ∑ t ∈ Finset.Ico 1 (2 * n),
          (Fobj fi ψ (y ω (s * (2 * n) + t)) - Fobj fi ψ xstar) :=
        Finset.sum_nonneg (fun t _ => hDn _ (KatNs1fd.run_mem_yz hn hx0 hrun ω _).1)
      obtain ⟨t1, t2⟩ := KatNs1fd.tau_step s
      have m1 := mul_le_mul_of_nonneg_right t1 hDend
      have m2 := mul_le_mul_of_nonneg_right t2 hSum
      have hc : (0:ℝ) ≤ (1 / 2) / tau1 (s + 1) ^ 2 := by
        have := KatNs1fd.tau1_pos (s + 1); positivity
      have hm := mul_le_mul_of_nonneg_left hJ2 hc
      linear_combination hm + m1 + m2
    · rw [hidx]; exact ih

open KatyushaNs in
theorem KatNs1fd.rate {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (S : ℕ) :
    seqAvg hn (S * (2 * n)) (fun ω => Fobj fi ψ (xt ω S)) - Fobj fi ψ xstar ≤
      16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) / ((S : ℝ) + 3) ^ 2 +
        12 * L * ‖x0 - xstar‖ ^ 2 / ((2 * n : ℝ) * ((S : ℝ) + 3) ^ 2) := by
  have hDn : ∀ u ∈ D, 0 ≤ Fobj fi ψ u - Fobj fi ψ xstar :=
    fun u hu => sub_nonneg.mpr (hmin u hu)
  have hD0 := hDn x0 hx0
  have hN : 0 ≤ ‖x0 - xstar‖ ^ 2 := by positivity
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  rcases Nat.eq_zero_or_pos S with rfl | hS
  · have hf : (fun ω : ℕ → Fin n => Fobj fi ψ (xt ω 0)) = fun _ => Fobj fi ψ x0 := by
      funext ω; rw [(hrun ω).1.2.2]
    rw [hf, KatNs1fd.seqAvg_const hn]
    simp only [Nat.cast_zero, zero_add]
    have h1 : 0 ≤ 12 * L * ‖x0 - xstar‖ ^ 2 / ((2 * n : ℝ) * (3:ℝ) ^ 2) := by positivity
    have h2 : Fobj fi ψ x0 - Fobj fi ψ xstar
        ≤ 16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) / (3:ℝ) ^ 2 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith
    linarith
  · obtain ⟨S', rfl⟩ : ∃ S', S = S' + 1 := ⟨S - 1, by omega⟩
    have hkey := KatNs1fd.eqC4 hn hL hfi hψ hx0 hxs hmin hrun S'
    have hτ := KatNs1fd.tau1_pos S'
    have hc : 0 ≤ tau1 S' ^ 2 / (n : ℝ) := by positivity
    have hpt : ∀ ω, Fobj fi ψ (xt ω (S' + 1)) - Fobj fi ψ xstar
        ≤ tau1 S' ^ 2 / (n : ℝ) * KatNs1fd.Vf fi ψ L xstar y z S' (2 * n) ω := by
      intro ω
      rw [KatNs1fd.Vf_end hn]
      have hJ : Fobj fi ψ (xt ω (S' + 1)) ≤ (1 / (2 * n : ℝ)) *
          ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (y ω (S' * (2 * n) + (t + 1))) := by
        rw [(hrun ω).2.2 S']
        exact KatNs1fd.objJensen hn fi ψ (fun i => (hfi i).1) hψ
          (fun t => y ω (S' * (2 * n) + t)) (fun t => (KatNs1fd.run_mem_yz hn hx0 hrun ω _).1)
      have hsp := KatNs1fd.sum_split (2 * n) (by omega)
        (fun t => Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar)
      have hsum2 : ∑ t ∈ Finset.range (2 * n),
            (Fobj fi ψ (y ω (S' * (2 * n) + (t + 1))) - Fobj fi ψ xstar)
          = ∑ t ∈ Finset.range (2 * n), Fobj fi ψ (y ω (S' * (2 * n) + (t + 1)))
            - ((2 * n : ℕ) : ℝ) * Fobj fi ψ xstar := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hn' : (n : ℝ) ≠ 0 := hnR.ne'
      have hJ2 : Fobj fi ψ (xt ω (S' + 1)) - Fobj fi ψ xstar
          ≤ (1 / (2 * n : ℝ)) * (∑ t ∈ Finset.Ico 1 (2 * n),
              (Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar)
            + (Fobj fi ψ (y ω (S' * (2 * n) + 2 * n)) - Fobj fi ψ xstar)) := by
        rw [← hsp, hsum2]
        have e : (1 / (2 * n : ℝ)) * (∑ t ∈ Finset.range (2 * n),
              Fobj fi ψ (y ω (S' * (2 * n) + (t + 1))) - ((2 * n : ℕ) : ℝ) * Fobj fi ψ xstar)
            = (1 / (2 * n : ℝ)) * ∑ t ∈ Finset.range (2 * n),
              Fobj fi ψ (y ω (S' * (2 * n) + (t + 1))) - Fobj fi ψ xstar := by
          push_cast; field_simp
        rw [e]; linarith
      have hDend := hDn _ (KatNs1fd.run_mem_yz hn hx0 hrun ω (S' * (2 * n) + 2 * n)).1
      have hSum : 0 ≤ ∑ t ∈ Finset.Ico 1 (2 * n),
          (Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar) :=
        Finset.sum_nonneg (fun t _ => hDn _ (KatNs1fd.run_mem_yz hn hx0 hrun ω _).1)
      have e : tau1 S' ^ 2 / (n : ℝ) *
          (1 / tau1 S' ^ 2 * (Fobj fi ψ (y ω (S' * (2 * n) + 2 * n)) - Fobj fi ψ xstar)
            + (tau1 S' + 1 / 2) / tau1 S' ^ 2 * ∑ t ∈ Finset.Ico 1 (2 * n),
              (Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar)
            + 3 * L / 2 * ‖z ω (S' * (2 * n) + 2 * n) - xstar‖ ^ 2)
          = (1 / (n : ℝ)) * (Fobj fi ψ (y ω (S' * (2 * n) + 2 * n)) - Fobj fi ψ xstar)
            + (tau1 S' + 1 / 2) * (1 / (n : ℝ)) * ∑ t ∈ Finset.Ico 1 (2 * n),
              (Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar)
            + tau1 S' ^ 2 * (1 / (n : ℝ)) * (3 * L / 2 * ‖z ω (S' * (2 * n) + 2 * n) - xstar‖ ^ 2) := by
        field_simp
      rw [e]
      have hu : (0:ℝ) ≤ 1 / (n : ℝ) := by positivity
      have q : 0 ≤ 1 / (n : ℝ) / 2 * (Fobj fi ψ (y ω (S' * (2 * n) + 2 * n)) - Fobj fi ψ xstar)
          + tau1 S' * (1 / (n : ℝ)) * ∑ t ∈ Finset.Ico 1 (2 * n),
              (Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar)
          + tau1 S' ^ 2 * (1 / (n : ℝ)) * (3 * L / 2 * ‖z ω (S' * (2 * n) + 2 * n) - xstar‖ ^ 2) := by
        have a1 : 0 ≤ 1 / (n : ℝ) / 2 * (Fobj fi ψ (y ω (S' * (2 * n) + 2 * n)) - Fobj fi ψ xstar) :=
          mul_nonneg (by positivity) hDend
        have a2 : 0 ≤ tau1 S' * (1 / (n : ℝ)) * ∑ t ∈ Finset.Ico 1 (2 * n),
              (Fobj fi ψ (y ω (S' * (2 * n) + t)) - Fobj fi ψ xstar) :=
          mul_nonneg (by positivity) hSum
        have a3 : 0 ≤ tau1 S' ^ 2 * (1 / (n : ℝ)) *
            (3 * L / 2 * ‖z ω (S' * (2 * n) + 2 * n) - xstar‖ ^ 2) := by positivity
        linarith
      linear_combination hJ2 + q
    have hidx : (S' + 1) * (2 * n) = S' * (2 * n) + 2 * n := by ring
    have hE := KatNs1fd.seqAvg_mono hn ((S' + 1) * (2 * n)) _ _ hpt
    rw [KatNs1fd.seqAvg_mul, KatNs1fd.seqAvg_sub_const, hidx] at hE
    rw [hidx]
    have hfin := mul_le_mul_of_nonneg_left hkey hc
    have e3 : tau1 S' ^ 2 / (n : ℝ) *
        ((1 - tau1 0 - 1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar)
          + ((2 * n : ℕ) : ℝ) * ((1 / 2) / tau1 0 ^ 2 * (Fobj fi ψ x0 - Fobj fi ψ xstar))
          + 3 * L / 2 * ‖x0 - xstar‖ ^ 2)
        = 16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) / (((S' + 1 : ℕ) : ℝ) + 3) ^ 2
          + 12 * L * ‖x0 - xstar‖ ^ 2 / ((2 * n : ℝ) * (((S' + 1 : ℕ) : ℝ) + 3) ^ 2) := by
      unfold tau1
      push_cast
      field_simp
      ring
    linarith

open KatyushaNs in
theorem KatNs1fd.complexity {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : ℕ,
        ((S * (2 * n) : ℕ) : ℝ) ≤
            8 * ((n : ℝ) * Real.sqrt (Fobj fi ψ x0 - Fobj fi ψ xstar) / Real.sqrt ε +
              Real.sqrt ((n : ℝ) * L) * ‖x0 - xstar‖ / Real.sqrt ε) ∧
          seqAvg hn (S * (2 * n)) (fun ω => Fobj fi ψ (xt ω S)) - Fobj fi ψ xstar ≤ ε := by
  have hD0 : 0 ≤ Fobj fi ψ x0 - Fobj fi ψ xstar := sub_nonneg.mpr (hmin x0 hx0)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hsD2 : Real.sqrt (Fobj fi ψ x0 - Fobj fi ψ xstar) ^ 2 = Fobj fi ψ x0 - Fobj fi ψ xstar :=
    Real.sq_sqrt hD0
  have hsε2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hsNL2 : Real.sqrt ((n : ℝ) * L) ^ 2 = (n : ℝ) * L := Real.sq_sqrt (by positivity)
  obtain ⟨a, ha⟩ : ∃ a, a = Real.sqrt (Fobj fi ψ x0 - Fobj fi ψ xstar) / Real.sqrt ε := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = Real.sqrt ((n : ℝ) * L) * ‖x0 - xstar‖ / ((n : ℝ) * Real.sqrt ε) :=
    ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  obtain ⟨T, hT⟩ : ∃ T, T = 4 * a + 3 * b := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  refine ⟨⌈T⌉₊ - 3, ?_, ?_⟩
  · have hS : ((⌈T⌉₊ - 3 : ℕ) : ℝ) ≤ T := by
      rcases le_or_gt ⌈T⌉₊ 3 with h | h
      · rw [Nat.sub_eq_zero_of_le h]; simpa using hT0
      · rw [Nat.cast_sub h.le]
        have := Nat.ceil_lt_add_one hT0
        push_cast; linarith
    push_cast
    have h1 : ((⌈T⌉₊ - 3 : ℕ) : ℝ) * (2 * n) ≤ T * (2 * n) :=
      mul_le_mul_of_nonneg_right hS (by positivity)
    have e : T * (2 * n) = 8 * ((n : ℝ) * Real.sqrt (Fobj fi ψ x0 - Fobj fi ψ xstar) / Real.sqrt ε)
        + 6 * (Real.sqrt ((n : ℝ) * L) * ‖x0 - xstar‖ / Real.sqrt ε) := by
      rw [hT, ha, hb]; field_simp; ring
    have h2 : 0 ≤ Real.sqrt ((n : ℝ) * L) * ‖x0 - xstar‖ / Real.sqrt ε := by positivity
    linarith
  · refine le_trans (KatNs1fd.rate hn hL hfi hψ hx0 hxs hmin hrun (⌈T⌉₊ - 3)) ?_
    have hS3 : T ≤ ((⌈T⌉₊ - 3 : ℕ) : ℝ) + 3 := by
      have hc := Nat.le_ceil T
      rcases le_or_gt ⌈T⌉₊ 3 with h | h
      · rw [Nat.sub_eq_zero_of_le h]
        have : (⌈T⌉₊ : ℝ) ≤ 3 := by exact_mod_cast h
        push_cast; linarith
      · rw [Nat.cast_sub h.le]; push_cast; linarith
    obtain ⟨u, hu⟩ : ∃ u, u = ((⌈T⌉₊ - 3 : ℕ) : ℝ) + 3 := ⟨_, rfl⟩
    rw [← hu]
    rw [← hu] at hS3
    have hu0 : 0 < u := by rw [hu]; positivity
    have hTu : T ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hT0 hS3 2
    have ha2 : a ^ 2 * ε = Fobj fi ψ x0 - Fobj fi ψ xstar := by
      rw [ha, div_pow, hsD2, hsε2]; field_simp
    have hb2 : b ^ 2 * ε = L * ‖x0 - xstar‖ ^ 2 / n := by
      rw [hb, div_pow, mul_pow, hsNL2, mul_pow, hsε2]; field_simp
    have hab : 0 ≤ a * b * ε := by positivity
    have hX : 0 ≤ L * ‖x0 - xstar‖ ^ 2 / n := by positivity
    have hT2 : 16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) + 6 * (L * ‖x0 - xstar‖ ^ 2 / n)
        ≤ u ^ 2 * ε := by
      have h1 := mul_le_mul_of_nonneg_right hTu hε.le
      have e : T ^ 2 * ε = 16 * (a ^ 2 * ε) + 24 * (a * b * ε) + 9 * (b ^ 2 * ε) := by
        rw [hT]; ring
      rw [e, ha2, hb2] at h1
      linarith
    have e : 16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) / u ^ 2
        + 12 * L * ‖x0 - xstar‖ ^ 2 / ((2 * n : ℝ) * u ^ 2)
        = (16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) + 6 * (L * ‖x0 - xstar‖ ^ 2 / n)) / u ^ 2 := by
      field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    linarith

open KatyushaNs in
theorem solution {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {x0 : EuclideanSpace ℝ (Fin d)} (hx0 : x0 ∈ D)
    {xstar : EuclideanSpace ℝ (Fin d)} (hxs : xstar ∈ D)
    (hmin : ∀ w ∈ D, Fobj fi ψ xstar ≤ Fobj fi ψ w)
    {x y z xt : (ℕ → Fin n) → ℕ → EuclideanSpace ℝ (Fin d)}
    (hrun : IsKatyushaNsRun fi L D ψ x0 x y z xt) :
    (∀ S : ℕ,
        seqAvg hn (S * (2 * n)) (fun ω => Fobj fi ψ (xt ω S)) - Fobj fi ψ xstar ≤
          16 * (Fobj fi ψ x0 - Fobj fi ψ xstar) / ((S : ℝ) + 3) ^ 2 +
            12 * L * ‖x0 - xstar‖ ^ 2 / ((2 * n : ℝ) * ((S : ℝ) + 3) ^ 2)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ S : ℕ,
        ((S * (2 * n) : ℕ) : ℝ) ≤
            8 * ((n : ℝ) * Real.sqrt (Fobj fi ψ x0 - Fobj fi ψ xstar) / Real.sqrt ε +
              Real.sqrt ((n : ℝ) * L) * ‖x0 - xstar‖ / Real.sqrt ε) ∧
          seqAvg hn (S * (2 * n)) (fun ω => Fobj fi ψ (xt ω S)) - Fobj fi ψ xstar ≤ ε) := by
  exact ⟨fun S => KatNs1fd.rate hn hL hfi hψ hx0 hxs hmin hrun S,
    fun ε hε => KatNs1fd.complexity hn hL hfi hψ hx0 hxs hmin hrun ε hε⟩
