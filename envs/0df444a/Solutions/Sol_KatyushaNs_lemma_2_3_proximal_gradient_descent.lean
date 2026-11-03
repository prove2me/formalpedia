-- Prove2me | solution 1 for KatyushaNs.lemma_2_3_proximal_gradient_descent
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-02T12:27:05.97365+00:00
-- url     : https://prove2.me/submissions/a993338a-0eba-4759-8edb-50b1842b1a24

import Definitions.Def_KatyushaNs_IsConvexLSmooth
import Definitions.Def_KatyushaNs_favg
import Definitions.Def_KatyushaNs_Fobj
import Definitions.Def_KatyushaNs_svrgEst
import Definitions.Def_KatyushaNs_IsQuadProxMin
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Set Matrix
open scoped InnerProductSpace

private lemma scalar_remainder (g g' : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (g' t) t)
    (hbound : ∀ t, 0 ≤ t → |g' t - g' 0| ≤ L * t) :
    |g 1 - g 0 - g' 0| ≤ L / 2 := by
  let u : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 - L / 2 * t ^ 2
  let l : ℝ → ℝ := fun t => g t - g 0 - t * g' 0 + L / 2 * t ^ 2
  have hu (t : ℝ) : HasDerivAt u (g' t - g' 0 - L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [u, id]) <;> ring
  have hl (t : ℝ) : HasDerivAt l (g' t - g' 0 + L * t) t := by
    convert! (((hd t).sub_const (g 0)).sub ((hasDerivAt_id t).mul_const (g' 0))).add
      (((hasDerivAt_id t).pow 2).const_mul (L / 2)) using 1 <;> (try dsimp only [l, id]) <;> ring
  have hanti : AntitoneOn u (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun t _ => (hu t).continuousAt.continuousWithinAt)
      (fun t _ => (hu t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hu t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).2
    linarith
  have hmono : MonotoneOn l (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => (hl t).continuousAt.continuousWithinAt)
      (fun t _ => (hl t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hl t).deriv]
    have ht0 : 0 ≤ t := (interior_subset ht)
    have := (abs_le.mp (hbound t ht0)).1
    linarith
  have hu01 := hanti (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  have hl01 := hmono (show (0 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (1 : ℝ) ∈ Ici 0 from by change (0 : ℝ) ≤ 1; norm_num) zero_le_one
  dsimp [u, l] at hu01 hl01
  apply abs_le.mpr
  constructor <;> linarith

private lemma smooth_upper {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hf : Differentiable ℝ f)
    (hL : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖)
    (x y : EuclideanSpace ℝ (Fin d)) :
    f y ≤ f x + inner ℝ (gradient f x) (y-x) + L/2*‖y-x‖^2 := by
  let h := y-x
  let g : ℝ → ℝ := fun t => f (x+t • h)
  let dg : ℝ → ℝ := fun t => inner ℝ (gradient f (x+t • h)) h
  have hd (t : ℝ) : HasDerivAt g (dg t) t := by
    have hp : HasDerivAt (fun s : ℝ => x+s • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    have hc := (hf (x+t • h)).hasFDerivAt.comp_hasDerivAt t hp
    convert! hc using 1
    simp only [g,dg,inner_gradient_left]
  have hb (t : ℝ) (ht : 0 ≤ t) : |dg t-dg 0| ≤ (L*‖h‖^2)*t := by
    have hl := hL (x+t • h) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hl
    dsimp [dg]
    simp only [zero_smul, add_zero]
    rw [← inner_sub_left]
    calc
      _ ≤ ‖gradient f (x+t • h)-gradient f x‖*‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*(t*‖h‖))*‖h‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
      _ = (L*‖h‖^2)*t := by ring
  have hr := (abs_le.mp (scalar_remainder g dg (L*‖h‖^2) hd hb)).2
  dsimp [g,dg,h] at hr
  simp only [one_smul, zero_smul, add_zero, add_sub_cancel] at hr
  linarith

open KatyushaNs

private lemma avg_upper {d n : ℕ} (hn : 0 < n) {L : ℝ}
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hf : ∀ i, IsConvexLSmooth L (fi i))
    (x y : EuclideanSpace ℝ (Fin d)) :
    favg fi y ≤ favg fi x + inner ℝ (gradient (favg fi) x) (y-x) + L/2*‖y-x‖^2 := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => smooth_upper (fi i) L (hf i).2.1 (hf i).2.2 x y)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hninv : (n : ℝ)⁻¹*(n : ℝ)=1 := inv_mul_cancel₀ hn0
  have hdiff : HasFDerivAt (favg fi)
      ((n : ℝ)⁻¹ • ∑ i : Fin n, fderiv ℝ (fi i) x) x := by
    convert! (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((hf i).2.1 x).hasFDerivAt)).const_mul ((n : ℝ)⁻¹) using 1
  have hinner : inner ℝ (gradient (favg fi) x) (y-x) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, inner ℝ (gradient (fi i) x) (y-x) := by
    rw [inner_gradient_left, hdiff.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      smul_eq_mul, inner_gradient_left]
  have hw := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hw
  rw [favg,favg,hinner]
  nlinarith [show (n : ℝ)⁻¹*((n : ℝ)*(L/2*‖y-x‖^2)) = L/2*‖y-x‖^2 by rw [← mul_assoc,hninv,one_mul]]

theorem solution {d n : ℕ} (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    {fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ} (hfi : ∀ i, IsConvexLSmooth L (fi i))
    {D : Set (EuclideanSpace ℝ (Fin d))} {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hψ : ConvexOn ℝ D ψ) {xt x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ D)
    {yplus : Fin n → EuclideanSpace ℝ (Fin d)}
    (hy : ∀ i, IsQuadProxMin D ψ (3 * L) x (svrgEst fi xt x i) (yplus i)) :
    (∀ i, 0 ≤ -(3 * L / 2 * ‖yplus i - x‖ ^ 2 + inner ℝ (svrgEst fi xt x i) (yplus i - x) +
        ψ (yplus i) - ψ x)) ∧
      (n : ℝ)⁻¹ * ∑ i, -(3 * L / 2 * ‖yplus i - x‖ ^ 2 +
          inner ℝ (svrgEst fi xt x i) (yplus i - x) + ψ (yplus i) - ψ x) -
        1 / (4 * L) * ((n : ℝ)⁻¹ * ∑ i, ‖gradient (favg fi) x - svrgEst fi xt x i‖ ^ 2) ≤
      Fobj fi ψ x - (n : ℝ)⁻¹ * ∑ i, Fobj fi ψ (yplus i) := by
  constructor
  · intro i
    have hi := (hy i).2 x hx
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,zero_add] at hi
    rw [inner_sub_right]
    linarith
  · have hpoint (i : Fin n) :
        -(3*L/2*‖yplus i-x‖^2+inner ℝ (svrgEst fi xt x i) (yplus i-x)+ψ (yplus i)-ψ x) -
          1/(4*L)*‖gradient (favg fi) x-svrgEst fi xt x i‖^2 ≤ Fobj fi ψ x-Fobj fi ψ (yplus i) := by
      have hs := avg_upper hn hfi x (yplus i)
      have hcs := real_inner_le_norm (gradient (favg fi) x-svrgEst fi xt x i) (yplus i-x)
      have hsq := sq_nonneg (‖gradient (favg fi) x-svrgEst fi xt x i‖-2*L*‖yplus i-x‖)
      have hyoung : inner ℝ (gradient (favg fi) x-svrgEst fi xt x i) (yplus i-x) ≤
          L*‖yplus i-x‖^2 + 1/(4*L)*‖gradient (favg fi) x-svrgEst fi xt x i‖^2 := by
        have hden : (4*L)*(1/(4*L)*‖gradient (favg fi) x-svrgEst fi xt x i‖^2) =
            ‖gradient (favg fi) x-svrgEst fi xt x i‖^2 := by
          field_simp [show 4*L ≠ 0 by linarith]
        have hm : (4*L)*(‖gradient (favg fi) x-svrgEst fi xt x i‖*‖yplus i-x‖) ≤
            (4*L)*(L*‖yplus i-x‖^2 + 1/(4*L)*‖gradient (favg fi) x-svrgEst fi xt x i‖^2) := by
          nlinarith
        exact hcs.trans (le_of_mul_le_mul_left hm (show 0 < 4*L by linarith))
      have hnorm : ‖gradient (favg fi) x-svrgEst fi xt x i‖^2/(4*L) =
          1/(4*L)*‖gradient (favg fi) x-svrgEst fi xt x i‖^2 := by ring
      rw [inner_sub_left] at hyoung
      dsimp [Fobj]
      linarith
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
    have hw := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hninv : (n : ℝ)⁻¹*(n : ℝ)=1 := inv_mul_cancel₀ hn0
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hw
    nlinarith [show (n : ℝ)⁻¹*((n : ℝ)*Fobj fi ψ x) = Fobj fi ψ x by rw [← mul_assoc,hninv,one_mul]]

#print axioms solution

