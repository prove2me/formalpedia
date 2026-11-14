-- Prove2me | solution 1 for NAGFlow.APGM.eq_117
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-13T12:28:51.553025+00:00
-- url     : https://prove2.me/submissions/112046af-9382-4e94-a566-13b45b3f93b2

import Definitions.Def_NAGFlow_APGM_Setting
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

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

private lemma composite_lower {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
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

private lemma kinetic_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a c b μ : ℝ) (ha : 0 < a) (hc : 0 < c) (hμ : 0 ≤ μ)
    (X Y U W Z G : V)
    (hy : Y-X = a • (U-Y))
    (hv : c • (W-U) = (a*μ) • (Y-W) - a • G)
    (hb : (1+a)*b = c+a*μ) :
    (1+a)*b/2*‖W-Z‖^2-c/2*‖U-Z‖^2 ≤
      ⟪G,X-Y⟫_ℝ + a*⟪G,Z-Y⟫_ℝ + μ/2*‖X-Y‖^2 + a*μ/2*‖Z-Y‖^2 + a^2/(2*c)*‖G‖^2 := by
  have hpol : ‖W-Z‖^2-‖U-Z‖^2 = 2*⟪W-U,W-Z⟫_ℝ-‖W-U‖^2 := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm U W]
    ring
  have hpol2 : 2*⟪Y-W,W-Z⟫_ℝ+‖W-Z‖^2 = ‖Y-Z‖^2-‖Y-W‖^2 := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    ring
  have hip := congrArg (fun q => ⟪q,W-Z⟫_ℝ) hv
  simp only [inner_sub_left, real_inner_smul_left] at hip
  have hs : 0 ≤ ‖c • (W-U) + a • G‖^2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right] at hs
  have hyn : -a*⟪G,W-U⟫_ℝ-c/2*‖W-U‖^2 ≤ a^2/(2*c)*‖G‖^2 := by
    rw [show a^2/(2*c)*‖G‖^2 = (a^2*‖G‖^2)/(2*c) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
    rw [real_inner_comm (W-U) G]
    nlinarith
  have hcancel : ⟪G,X-Y⟫_ℝ+a*⟪G,Z-Y⟫_ℝ = a*⟪G,Z-U⟫_ℝ := by
    have hy' : X-Y = -a • (U-Y) := by rw [← neg_sub Y X, hy, neg_smul]
    rw [hy', real_inner_smul_right]
    simp only [inner_sub_right]
    ring
  have hsplit : ⟪G,W-Z⟫_ℝ = ⟪G,W-U⟫_ℝ - ⟪G,Z-U⟫_ℝ := by simp only [inner_sub_right]; ring
  have hkin : (1+a)*b/2*‖W-Z‖^2-c/2*‖U-Z‖^2 =
      a*μ/2*‖Y-Z‖^2-a*μ/2*‖Y-W‖^2-a*⟪G,W-Z⟫_ℝ-c/2*‖W-U‖^2 := by
    rw [show (1+a)*b/2*‖W-Z‖^2 = (c+a*μ)/2*‖W-Z‖^2 by rw [hb]]
    simp only [inner_sub_left] at hpol hpol2
    linear_combination c / 2 * hpol + a * μ / 2 * hpol2 + hip
  rw [hkin, hsplit, hcancel, norm_sub_rev Z Y]
  have h1 : 0 ≤ a*μ*‖Y-W‖^2 := mul_nonneg (mul_nonneg ha.le hμ) (sq_nonneg _)
  have h2 : 0 ≤ μ*‖X-Y‖^2 := mul_nonneg hμ (sq_nonneg _)
  nlinarith

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (μ L : ℝ) (hh : NAGFlow.PredCorr.IsS11 h gradh μ L)
    (g : V → ℝ) (D : Set V) (hg : IsProperClosedConvex g D)
    (xstar : V) (hxstar : xstar ∈ D) (hmin : ∀ z ∈ D, (h + g) xstar ≤ (h + g) z)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) (hrun : IsSemiImplicitRun gradh g D μ L α γ x y v)
    (hx0 : x 0 ∈ D) (k : ℕ) :
    NAGFlow.PredCorr.lyapHat (h + g) xstar y v γ k - NAGFlow.PredCorr.lyap (h + g) xstar x v γ k ≤
      -α k * NAGFlow.PredCorr.lyapHat (h + g) xstar y v γ k + (1 + α k) * ((h + g) (y k) - (h + g) (x (k + 1)))
        + α k ^ 2 / (2 * γ k) * ‖gradMap (1 / L) (y k) (x (k + 1))‖ ^ 2
        - (1 + α k) / (2 * L) * ‖gradMap (1 / L) (y k) (x (k + 1))‖ ^ 2  := by
  have hγ : ∀ j, 0 < γ j := by
    intro j
    induction j with
    | zero => exact hrun.gamma0_pos
    | succ j ih =>
      have h := (div_eq_iff (ne_of_gt (hrun.alpha_pos j))).mp (hrun.gamma_eq j)
      have hμ := hh.mu_nonneg
      have ha := hrun.alpha_pos j
      nlinarith
  have hx : ∀ j, x j ∈ D := by
    intro j
    cases j with
    | zero => exact hx0
    | succ j => exact (hrun.x_eq j).1
  have hlx := composite_lower h gradh μ L hh g D hg (y k) (x k) (x (k+1)) (hx k) (hrun.x_eq k)
  have hlz := composite_lower h gradh μ L hh g D hg (y k) xstar (x (k+1)) hxstar (hrun.x_eq k)
  have ha := hrun.alpha_pos k
  have hc := hγ k
  have han : α k ≠ 0 := ne_of_gt ha
  have hcn : γ k ≠ 0 := ne_of_gt hc
  have hy : y k-x k = α k • (v k-y k) := by
    have he := congrArg (fun q => α k • q) (hrun.y_eq k)
    simpa [smul_smul, han] using he
  have hv : γ k • (v (k+1)-v k) = (α k*μ) • (y k-v (k+1)) - α k • gradMap (1/L) (y k) (x (k+1)) := by
    have he := congrArg (fun q => (α k*γ k) • q) (hrun.v_eq k)
    simp only [smul_sub, smul_smul] at he
    have e1 : α k * γ k * (1 / α k) = γ k := by field_simp
    have e2 : α k * γ k * (μ / γ k) = α k * μ := by field_simp
    have e3 : α k * γ k * (1 / γ k) = α k := by field_simp
    rw [e1,e2,e3] at he
    simpa only [smul_sub] using he
  have hb : (1+α k)*γ (k+1) = γ k+α k*μ := by
    have he := (div_eq_iff han).mp (hrun.gamma_eq k)
    nlinarith
  have hk := kinetic_bound (α k) (γ k) (γ (k+1)) μ ha hc hh.mu_nonneg
    (x k) (y k) (v k) (v (k+1)) xstar (gradMap (1/L) (y k) (x (k+1))) hy hv hb
  have hlz' := mul_le_mul_of_nonneg_left hlz ha.le
  dsimp [NAGFlow.PredCorr.lyapHat, NAGFlow.PredCorr.lyap, NAGFlow.PredCorr.lyapPt]
  simp only [Pi.add_apply] at hlx hlz'
  linear_combination hlx + hlz' + hk

#print axioms solution

