-- Prove2me | solution 1 for NAGFlow.APGM.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:24:32.912236+00:00
-- url     : https://prove2.me/submissions/b749ffa1-a769-4040-b7a8-ed2a0e21ac2a

import Definitions.Def_NAGFlow_APGM_Setting
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open NAGFlow.APGM Set
open scoped InnerProductSpace

private lemma prox_optimality {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D) (η : ℝ) (hη : 0 < η)
    (z p : V) (hp : IsProx g D η z p) :
    (1 / η) • (z - p) ∈ subdiff g D p := by
  refine ⟨hp.1, ?_⟩
  intro y hy
  simp only [real_inner_smul_left]
  let A : ℝ := g y - g p - (1 / η) * ⟪z - p, y - p⟫_ℝ
  let B : ℝ := ‖y - p‖ ^ 2 / (2 * η)
  have hB : 0 ≤ B := div_nonneg (sq_nonneg _) (by positivity)
  have hpoly : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * B := by
    intro t ht ht1
    have hseg := hg.convex.1 hp.1 hy (by linarith : 0 ≤ 1-t) ht.le (by ring : 1-t+t=1)
    have hc := hg.convex.2 hp.1 hy (by linarith : 0 ≤ 1-t) ht.le (by ring : 1-t+t=1)
    have hmin := hp.2 ((1-t) • p + t • y) hseg
    have heq : (1-t) • p + t • y - z = (p-z) + t • (y-p) := by module
    rw [heq, norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hmin
    have hin : ⟪p-z,y-p⟫_ℝ = - ⟪z-p,y-p⟫_ℝ := by rw [← neg_sub p z, inner_neg_left]; simp
    rw [real_inner_smul_right, hin] at hmin
    change g ((1-t) • p + t • y) ≤ (1-t)*g p+t*g y at hc
    have hn : 0 ≤ t * (A+t*B) := by dsimp [A,B]; field_simp at *; nlinarith
    exact (mul_nonneg_iff_of_pos_left ht).mp hn
  have hA : 0 ≤ A := by
    by_contra h
    have hneg : A < 0 := lt_of_not_ge h
    let t : ℝ := min 1 (-A / (2*(B+1)))
    have ht : 0 < t := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
    have ht1 : t ≤ 1 := min_le_left _ _
    have hsmall : t * (2*(B+1)) ≤ -A := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hh := hpoly t ht ht1
    nlinarith
  dsimp [A] at hA
  linarith

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

private lemma smooth_upper {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (x s : V) : h s - h x - ⟪gradh x, s - x⟫_ℝ ≤ L / 2 * ‖s - x‖ ^ 2 := by
  let d := s - x
  let f : ℝ → ℝ := fun t => h (x + t • d)
  let f' : ℝ → ℝ := fun t => ⟪gradh (x + t • d), d⟫_ℝ
  have hd (t : ℝ) : HasDerivAt f (f' t) t := by
    have hp : HasDerivAt (fun r : ℝ => x + r • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hc := (hh.hasGrad (x + t • d)).hasFDerivAt.comp_hasDerivAt t hp
    convert! hc using 1
  have hb (t : ℝ) (ht : 0 ≤ t) : |f' t - f' 0| ≤ (L * ‖d‖ ^ 2) * t := by
    have hg := hh.grad_lip (x + t • d) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hg
    dsimp [f']
    simp only [zero_smul, add_zero]
    rw [← inner_sub_left]
    calc
      _ ≤ ‖gradh (x + t • d) - gradh x‖ * ‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L * (t * ‖d‖)) * ‖d‖ := mul_le_mul_of_nonneg_right hg (norm_nonneg _)
      _ = (L * ‖d‖ ^ 2) * t := by ring
  have hr := (abs_le.mp (scalar_remainder f f' (L * ‖d‖ ^ 2) hd hb)).2
  simpa [f, f', d, mul_div_assoc, div_mul_eq_mul_div] using hr

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D)
    (x y s : V) (hy : y ∈ D) (hs : IsSf gradh g D (1 / L) x s) :
    (h + g) y ≥ (h + g) s + inner ℝ (gradMap (1 / L) x s) (y - x) + μ / 2 * ‖y - x‖ ^ 2
      + 1 / (2 * L) * ‖gradMap (1 / L) x s‖ ^ 2 := by
  have hLpos : 0 < L := hh.L_pos
  have hL : L ≠ 0 := ne_of_gt hLpos
  have hp := prox_optimality g D hg (1/L) (by positivity) (x - (1/L) • gradh x) s hs
  have heq : (1 / (1/L)) • (x - (1/L) • gradh x - s) = gradMap (1/L) x s - gradh x := by
    simp only [gradMap, one_div_one_div]
    simp only [smul_sub, smul_smul, one_div, mul_inv_cancel₀ hL, one_smul]
    module
  rw [heq] at hp
  have hgy := hp.2 y hy
  have hhy := hh.mu_convex y x
  have hhs := smooth_upper h gradh μ L hh x s
  have hin : ⟪gradMap (1/L) x s - gradh x, y-s⟫_ℝ =
      ⟪gradMap (1/L) x s, y-x⟫_ℝ + L * ‖s-x‖^2 - ⟪gradh x,y-x⟫_ℝ + ⟪gradh x,s-x⟫_ℝ := by
    have e : y-s = (y-x) - (s-x) := by module
    rw [e, inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [gradMap, one_div_one_div, real_inner_smul_left]
    have hn : ⟪x-s,s-x⟫_ℝ = - ‖s-x‖^2 := by rw [← neg_sub s x, inner_neg_left, real_inner_self_eq_norm_sq]
    rw [hn]
    simp only [inner_sub_right]
    ring
  have hn : ‖gradMap (1/L) x s‖^2 = L^2 * ‖s-x‖^2 := by
    simp only [gradMap, one_div_one_div, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev]
  rw [hin] at hgy
  simp only [Pi.add_apply]
  rw [hn]
  have hc : 1/(2*L) * (L^2 * ‖s-x‖^2) = L/2 * ‖s-x‖^2 := by field_simp
  rw [hc]
  linarith

#print axioms solution
