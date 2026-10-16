-- Prove2me | solution 1 for NAPPAL.Rate.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T09:22:15.893519+00:00
-- url     : https://prove2.me/submissions/4f2ce3b6-b8f1-4676-afee-1116fcac4b4f

import Definitions.Def_NAPPAL_Subreg_Subregularity

set_option autoImplicit false
open NAPPAL.KL NAPPAL.Rate
open scoped InnerProductSpace

namespace QueeliusNappalCost

theorem gradient_three_point {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (L : ℝ) (hL : 0 ≤ L) (hf : Differentiable ℝ f)
    (hLip : ∀ a b, ‖gradient f a - gradient f b‖ ≤ L * ‖a - b‖)
    (x y z : X) :
    ‖f y - f z - ⟪gradient f x, y - z⟫_ℝ‖ ≤
      L * (‖y - x‖ + ‖z - x‖) * ‖y - z‖ := by
  let R := ‖y - x‖ + ‖z - x‖
  have hy : y ∈ Metric.closedBall x R := by
    simp only [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [R]
    linarith [norm_nonneg (z - x)]
  have hz : z ∈ Metric.closedBall x R := by
    simp only [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [R]
    linarith [norm_nonneg (y - x)]
  have hb (a : X) (ha : a ∈ Metric.closedBall x R) :
      ‖fderiv ℝ f a - fderiv ℝ f x‖ ≤ L * R := by
    have hd : ‖a - x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using ha
    have hn : ‖fderiv ℝ f a - fderiv ℝ f x‖ = ‖gradient f a - gradient f x‖ := by
      rw [← toDual_gradient, ← toDual_gradient, ← map_sub]
      exact (InnerProductSpace.toDual ℝ X).norm_map _
    rw [hn]
    exact (hLip a x).trans (mul_le_mul_of_nonneg_left hd hL)
  have hh := (convex_closedBall x R).norm_image_sub_le_of_norm_fderiv_le'
    (fun a _ => hf a) hb hz hy
  simpa only [inner_gradient_left] using hh

theorem bregman_bound {n : ℕ} (K : E n → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hK : Differentiable ℝ K)
    (hLip : ∀ a b, ‖gradient K a - gradient K b‖ ≤ L * ‖a - b‖)
    (x y : E n) : |bregman K y x| ≤ L * ‖y - x‖ ^ 2 := by
  simpa only [bregman, sub_self, norm_zero, add_zero, Real.norm_eq_abs, pow_two, mul_assoc]
    using gradient_three_point K L hL hK hLip x y x

-- Exact algorithmic inequality: no assumption about the subgradient calculus is needed.
theorem cost_decomposition {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ : ℝ) (u ub un : E n) (v vb vn : E d) (p pn q : E m) (eps : ℝ)
    (hfeas : Theta P ub + P.B vb = 0)
    (hu : obj5 P K u v q eps un ≤ obj5 P K u v q eps ub)
    (hv : obj6 P γ u v q vn ≤ obj6 P γ u v q vb) :
    augLag P γ (un, vn, pn) - augLag P γ (ub, vb, p) ≤
      ⟪pn - q, Theta P un + P.B vn⟫_ℝ +
      ⟪q, P.Om un - P.Om ub - fderiv ℝ P.Om u (un - ub)⟫_ℝ +
      (P.G (un, vn) - P.G (ub, vb) - ⟪gradU P u v, un - ub⟫_ℝ -
        ⟪gradV P u v, vn - vb⟫_ℝ) +
      (P.H vn - P.H vb - ⟪gradient P.H v, vn - vb⟫_ℝ) +
      (bregman K ub u - bregman K un u) / eps +
      γ / 2 * (‖P.B (vb - v)‖ ^ 2 - ‖P.B (vn - v)‖ ^ 2 +
        ‖Theta P un + P.B vn‖ ^ 2) := by
  have hzero : ⟪q, P.Om ub⟫_ℝ + ⟪q, P.Phi ub⟫_ℝ + ⟪q, P.B vb⟫_ℝ = 0 := by
    have hh := congrArg (fun z => ⟪q, z⟫_ℝ) hfeas
    simpa only [Theta, inner_add_right, inner_zero_right] using hh
  simp only [obj5, obj6, inner_add_left, inner_add_right, map_sub] at hu hv
  simp only [augLag]
  simp only [hfeas, inner_zero_right, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  simp only [F, Theta, inner_add_right, inner_sub_left, inner_sub_right, map_sub, sub_div,
    mul_add, mul_sub]
  linarith

end QueeliusNappalCost

namespace QueeliusNappalCost

theorem G_derivative {n d m : ℕ} (P : Problem n d m) (hG : Differentiable ℝ P.G)
    (u : E n) (v : E d) (du : E n) (dv : E d) :
    fderiv ℝ P.G (u, v) (du, dv) = ⟪gradU P u v, du⟫_ℝ + ⟪gradV P u v, dv⟫_ℝ := by
  have hu := ((hG (u, v)).hasFDerivAt.comp (f := fun x : E n => (x, v)) u
    ((hasFDerivAt_id u).prodMk (hasFDerivAt_const v u))).fderiv
  have hv := ((hG (u, v)).hasFDerivAt.comp (f := fun x : E d => (u, x)) v
    ((hasFDerivAt_const u v).prodMk (hasFDerivAt_id v))).fderiv
  have hu' := congrArg (fun f : E n →L[ℝ] ℝ => f du) hu
  have hv' := congrArg (fun f : E d →L[ℝ] ℝ => f dv) hv
  simp only [Function.comp_def, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply] at hu' hv'
  rw [gradU, gradV, inner_gradient_left, inner_gradient_left, hu', hv', ← map_add]
  congr 1
  ext <;> simp

theorem fderiv_three_point {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : X → Y) (L : ℝ) (hL : 0 ≤ L) (hf : Differentiable ℝ f)
    (hLip : ∀ a b, ‖fderiv ℝ f a - fderiv ℝ f b‖ ≤ L * ‖a - b‖)
    (x y z : X) :
    ‖f y - f z - fderiv ℝ f x (y - z)‖ ≤
      L * (‖y - x‖ + ‖z - x‖) * ‖y - z‖ := by
  let R := ‖y - x‖ + ‖z - x‖
  have hy : y ∈ Metric.closedBall x R := by
    simp only [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [R]
    linarith [norm_nonneg (z - x)]
  have hz : z ∈ Metric.closedBall x R := by
    simp only [Metric.mem_closedBall, dist_eq_norm]
    dsimp only [R]
    linarith [norm_nonneg (y - x)]
  exact (convex_closedBall x R).norm_image_sub_le_of_norm_fderiv_le'
    (fun a _ => hf a)
    (fun a ha => (hLip a x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using ha) hL)) hz hy

end QueeliusNappalCost

namespace QueeliusNappalCost

theorem G_fderiv_lipschitz {n d m : ℕ} (P : Problem n d m) (LG : ℝ)
    (hG : Differentiable ℝ P.G) (hLG : 0 ≤ LG)
    (hgrad : ∀ u v u' v', ‖gradU P u v - gradU P u' v'‖ ^ 2 +
      ‖gradV P u v - gradV P u' v'‖ ^ 2 ≤
      LG ^ 2 * (‖u - u'‖ ^ 2 + ‖v - v'‖ ^ 2))
    (a b : E n × E d) : ‖fderiv ℝ P.G a - fderiv ℝ P.G b‖ ≤ (4 * LG) * ‖a - b‖ := by
  have ha : ‖a.1 - b.1‖ ≤ ‖a - b‖ := norm_fst_le (a - b)
  have hb : ‖a.2 - b.2‖ ≤ ‖a - b‖ := norm_snd_le (a - b)
  have hh := hgrad a.1 a.2 b.1 b.2
  have hs : ‖a.1 - b.1‖ ^ 2 + ‖a.2 - b.2‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 := by
    nlinarith [norm_nonneg (a.1 - b.1), norm_nonneg (a.2 - b.2), norm_nonneg (a - b)]
  have hsm := mul_le_mul_of_nonneg_left hs (sq_nonneg LG)
  have hU : ‖gradU P a.1 a.2 - gradU P b.1 b.2‖ ≤ 2 * LG * ‖a - b‖ := by
    nlinarith [sq_nonneg ‖gradV P a.1 a.2 - gradV P b.1 b.2‖,
      norm_nonneg (gradU P a.1 a.2 - gradU P b.1 b.2), mul_nonneg hLG (norm_nonneg (a - b))]
  have hV : ‖gradV P a.1 a.2 - gradV P b.1 b.2‖ ≤ 2 * LG * ‖a - b‖ := by
    nlinarith [sq_nonneg ‖gradU P a.1 a.2 - gradU P b.1 b.2‖,
      norm_nonneg (gradV P a.1 a.2 - gradV P b.1 b.2), mul_nonneg hLG (norm_nonneg (a - b))]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hz1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hz2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have hi : (fderiv ℝ P.G a - fderiv ℝ P.G b) z =
      ⟪gradU P a.1 a.2 - gradU P b.1 b.2, z.1⟫_ℝ +
      ⟪gradV P a.1 a.2 - gradV P b.1 b.2, z.2⟫_ℝ := by
    change fderiv ℝ P.G (a.1, a.2) (z.1, z.2) -
      fderiv ℝ P.G (b.1, b.2) (z.1, z.2) = _
    rw [G_derivative P hG, G_derivative P hG, inner_sub_left, inner_sub_left]
    ring
  rw [hi]
  have hi1 := norm_inner_le_norm (𝕜 := ℝ) (gradU P a.1 a.2 - gradU P b.1 b.2) z.1
  have hi2 := norm_inner_le_norm (𝕜 := ℝ) (gradV P a.1 a.2 - gradV P b.1 b.2) z.2
  have hm1 := mul_le_mul hU hz1 (norm_nonneg _) (by positivity : 0 ≤ 2 * LG * ‖a - b‖)
  have hm2 := mul_le_mul hV hz2 (norm_nonneg _) (by positivity : 0 ≤ 2 * LG * ‖a - b‖)
  have hadd := norm_add_le
    (⟪gradU P a.1 a.2 - gradU P b.1 b.2, z.1⟫_ℝ)
    (⟪gradV P a.1 a.2 - gradV P b.1 b.2, z.2⟫_ℝ)
  nlinarith

end QueeliusNappalCost

namespace QueeliusNappalCost
open scoped BigOperators

theorem euclidean_norm_le_sum {m : ℕ} (x : E m) : ‖x‖ ≤ ∑ j, ‖x j‖ := by
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun j : Fin m => ‖x j‖) (fun _ _ => norm_nonneg _)
  have hn := EuclideanSpace.norm_sq_eq x
  have hp : 0 ≤ ∑ j : Fin m, ‖x j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  nlinarith

theorem coordinate_fderiv {n m : ℕ} (f : E n → E m) (hf : Differentiable ℝ f)
    (a z : E n) (j : Fin m) :
    fderiv ℝ (fun x => f x j) a z = (fderiv ℝ f a z) j := by
  have hh := ((PiLp.proj 2 (fun _ : Fin m => ℝ) j).hasFDerivAt.comp a (hf a).hasFDerivAt).fderiv
  exact congrArg (fun F : E n →L[ℝ] ℝ => F z) hh

theorem Om_fderiv_lipschitz {n d m : ℕ} (P : Problem n d m) (L : Fin m → ℝ)
    (hOm : Differentiable ℝ P.Om)
    (hL : ∀ j, 0 ≤ L j ∧ ∀ a b,
      ‖gradient (fun x => P.Om x j) a - gradient (fun x => P.Om x j) b‖ ≤ L j * ‖a - b‖)
    (a b : E n) : ‖fderiv ℝ P.Om a - fderiv ℝ P.Om b‖ ≤ LOm L * ‖a - b‖ := by
  have hn : 0 ≤ LOm L := Finset.sum_nonneg (fun j _ => (hL j).1)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hn (norm_nonneg _))
  intro z
  have hi (j : Fin m) :
      ‖((fderiv ℝ P.Om a - fderiv ℝ P.Om b) z) j‖ ≤ L j * ‖a - b‖ * ‖z‖ := by
    have he : ((fderiv ℝ P.Om a - fderiv ℝ P.Om b) z) j =
        ⟪gradient (fun x => P.Om x j) a - gradient (fun x => P.Om x j) b, z⟫_ℝ := by
      rw [inner_sub_left, inner_gradient_left, inner_gradient_left,
        coordinate_fderiv P.Om hOm, coordinate_fderiv P.Om hOm]
      rfl
    rw [he]
    exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
      (mul_le_mul_of_nonneg_right ((hL j).2 a b) (norm_nonneg z))
  calc
    _ ≤ ∑ j, ‖((fderiv ℝ P.Om a - fderiv ℝ P.Om b) z) j‖ := euclidean_norm_le_sum _
    _ ≤ ∑ j, L j * ‖a - b‖ * ‖z‖ := Finset.sum_le_sum (fun j _ => hi j)
    _ = LOm L * ‖a - b‖ * ‖z‖ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; rfl

end QueeliusNappalCost

namespace QueeliusNappalCost

noncomputable def costUpper {n d m : ℕ} (P : Problem n d m) (LG LH LO LK γ eps : ℝ)
    (u ub un : E n) (v vb vn : E d) (pn q : E m) : ℝ :=
  ‖pn - q‖ * ‖Theta P un + P.B vn‖ +
  ‖q‖ * (LO * (‖un - u‖ + ‖ub - u‖) * ‖un - ub‖) +
  (4 * LG) * (‖(un, vn) - (u, v)‖ + ‖(ub, vb) - (u, v)‖) * ‖(un, vn) - (ub, vb)‖ +
  LH * (‖vn - v‖ + ‖vb - v‖) * ‖vn - vb‖ +
  LK * (‖ub - u‖ ^ 2 + ‖un - u‖ ^ 2) / eps +
  γ / 2 * (‖P.B (vb - v)‖ ^ 2 + ‖Theta P un + P.B vn‖ ^ 2)

theorem one_step_upper {n d m : ℕ} (P : Problem n d m)
    (LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (LK : ℝ) (K : E n → ℝ) (β γ : ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (hA2 : Assumption2 P K β LK γ LG LH)
    (hγ : 0 < γ) (u ub un : E n) (v vb vn : E d) (p pn q : E m) (eps : ℝ)
    (heps : 0 < eps) (hfeas : Theta P ub + P.B vb = 0)
    (hu : obj5 P K u v q eps un ≤ obj5 P K u v q eps ub)
    (hv : obj6 P γ u v q vn ≤ obj6 P γ u v q vb) :
    augLag P γ (un, vn, pn) - augLag P γ (ub, vb, p) ≤
      costUpper P LG LH (LOm LOmj) LK γ eps u ub un v vb vn pn q := by
  rcases hA1 with ⟨⟨hG, hLG, hGradG⟩, ⟨hH, hLH, hGradH⟩, _, ⟨hOm, _, _, _⟩, hLOm, _, _⟩
  rcases hA2 with ⟨hK, _, _, hLK, hGradK, _⟩
  have hLO : 0 ≤ LOm LOmj := Finset.sum_nonneg (fun j _ => (hLOm j).1)
  have hT1 : ⟪pn - q, Theta P un + P.B vn⟫_ℝ ≤ ‖pn - q‖ * ‖Theta P un + P.B vn‖ :=
    real_inner_le_norm _ _
  have hT2 : ⟪q, P.Om un - P.Om ub - fderiv ℝ P.Om u (un - ub)⟫_ℝ ≤
      ‖q‖ * (LOm LOmj * (‖un - u‖ + ‖ub - u‖) * ‖un - ub‖) := by
    exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (fderiv_three_point P.Om (LOm LOmj) hLO hOm (Om_fderiv_lipschitz P LOmj hOm hLOm) u un ub)
      (norm_nonneg q))
  have hT3 : P.G (un, vn) - P.G (ub, vb) - ⟪gradU P u v, un - ub⟫_ℝ -
      ⟪gradV P u v, vn - vb⟫_ℝ ≤
      (4 * LG) * (‖(un, vn) - (u, v)‖ + ‖(ub, vb) - (u, v)‖) * ‖(un, vn) - (ub, vb)‖ := by
    have hh := fderiv_three_point P.G (4 * LG) (by positivity) hG
      (G_fderiv_lipschitz P LG hG hLG hGradG) (u, v) (un, vn) (ub, vb)
    have hid : fderiv ℝ P.G (u, v) ((un, vn) - (ub, vb)) =
        ⟪gradU P u v, un - ub⟫_ℝ + ⟪gradV P u v, vn - vb⟫_ℝ := G_derivative P hG u v _ _
    rw [hid, Real.norm_eq_abs] at hh
    have ha := le_abs_self (P.G (un, vn) - P.G (ub, vb) -
      (⟪gradU P u v, un - ub⟫_ℝ + ⟪gradV P u v, vn - vb⟫_ℝ))
    linarith
  have hT4 : P.H vn - P.H vb - ⟪gradient P.H v, vn - vb⟫_ℝ ≤
      LH * (‖vn - v‖ + ‖vb - v‖) * ‖vn - vb‖ := by
    have hh := gradient_three_point P.H LH hLH hH hGradH v vn vb
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)
  have hT5 : (bregman K ub u - bregman K un u) / eps ≤
      LK * (‖ub - u‖ ^ 2 + ‖un - u‖ ^ 2) / eps := by
    apply (div_le_div_iff_of_pos_right heps).2
    have h1 := bregman_bound K LK hLK hK hGradK u ub
    have h2 := bregman_bound K LK hLK hK hGradK u un
    have ha := le_abs_self (bregman K ub u)
    have hb := neg_le_abs (bregman K un u)
    nlinarith
  have hT6 : γ / 2 * (‖P.B (vb - v)‖ ^ 2 - ‖P.B (vn - v)‖ ^ 2 +
      ‖Theta P un + P.B vn‖ ^ 2) ≤
      γ / 2 * (‖P.B (vb - v)‖ ^ 2 + ‖Theta P un + P.B vn‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith [sq_nonneg ‖P.B (vn - v)‖]
  have hc := cost_decomposition P K γ u ub un v vb vn p pn q eps hfeas hu hv
  unfold costUpper
  linarith

end QueeliusNappalCost

-- Checked one-step upper bound from the exact platform RunHyp.
-- This does not assert the open boundedness or residual theorem.
theorem QueeliusNappalCost.run_upper {n d m : ℕ} (P : Problem n d m)
    (LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (LK : ℝ) (K : E n → ℝ)
    (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : NAPPAL.Subreg.RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : W n d m) (hstat : IsStationary P γ wbar) :
    ∀ k, augLag P γ (wseq u v p (k + 1)) - augLag P γ wbar ≤
      QueeliusNappalCost.costUpper P LG LH (LOm LOmj) LK γ (ε k)
        (u k) wbar.1 (u (k + 1)) (v k) wbar.2.1 (v (k + 1)) (p (k + 1))
        (qseq P γ u v p k) := by
  rcases hstat with ⟨a, _, b, hb, _, _, hfeas⟩
  intro k
  have hAlg := hrun.2.2.1
  have hk := hAlg.2.2.2 k
  have heps : 0 < ε k := lt_of_lt_of_le (mul_pos hAlg.2.1 hk.1) hk.2.1
  have hu := hk.2.2.2.1.2 wbar.1 hb.1
  have hv := hk.2.2.2.2.1 wbar.2.1
  exact QueeliusNappalCost.one_step_upper P LG LH L0 LOmj LK K β γ hrun.1 hrun.2.1 hAlg.1
    (u k) wbar.1 (u (k + 1)) (v k) wbar.2.1 (v (k + 1)) wbar.2.2 (p (k + 1))
    (qseq P γ u v p k) (ε k) heps hfeas.symm hu hv

set_option autoImplicit false
open NAPPAL.KL NAPPAL.Rate Filter Topology
open scoped InnerProductSpace
namespace QueeliusNappalSharp

theorem scalar_upper (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, dg t-dg 0 ≤ L*t) :
    g 1-g 0 ≤ dg 0+L/2 := by
  let f := fun t => g t-dg 0*t-L/2*t^2
  have hf (t : ℝ) : HasDerivAt f (dg t-dg 0-L*t) t := by
    convert! ((hd t).sub ((hasDerivAt_id t).const_mul (dg 0))).sub
      (((hasDerivAt_id t).pow 2).const_mul (L/2)) using 1
    dsimp [f]
    ring
  have ha : AntitoneOn f (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hf t).continuousAt.continuousWithinAt
    · exact fun t _ => (hf t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hf t).deriv]
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      linarith only [hb t ht']
  have h := ha (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  dsimp [f] at h
  norm_num at h
  linarith

theorem two_block_bound (a b c d A : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b)
    (_hc : 0 ≤ c) (_hd : 0 ≤ d) (hA : 0 ≤ A)
    (hs : a^2+b^2 ≤ A^2*(c^2+d^2)) : a*c+b*d ≤ A*(c^2+d^2) := by
  have hcs : (a*c+b*d)^2 ≤ (a^2+b^2)*(c^2+d^2) := by
    nlinarith only [sq_nonneg (a*d-b*c)]
  have hm := mul_le_mul_of_nonneg_right hs (add_nonneg (sq_nonneg c) (sq_nonneg d))
  have hpos : 0 ≤ A*(c^2+d^2) := mul_nonneg hA (add_nonneg (sq_nonneg c) (sq_nonneg d))
  nlinarith only [hcs,hm,hpos]

theorem G_upper {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u un : E n) (v vn : E d) :
    P.G (un,vn)-P.G (u,v)-⟪gradU P u v,un-u⟫_ℝ-⟪gradV P u v,vn-v⟫_ℝ ≤
      LG/2*(‖un-u‖^2+‖vn-v‖^2) := by
  let du := un-u
  let dv := vn-v
  let g := fun t : ℝ => P.G (u+t • du,v+t • dv)
  let dg := fun t : ℝ => ⟪gradU P (u+t • du) (v+t • dv),du⟫_ℝ+
    ⟪gradV P (u+t • du) (v+t • dv),dv⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (dg t) t := by
    have hp := (((hasDerivAt_id t).smul_const du).const_add u).prodMk
      (((hasDerivAt_id t).smul_const dv).const_add v)
    have hh := (hA1.1.1 _).hasFDerivAt.comp_hasDerivAt t hp
    convert! hh using 1
    simpa only [one_smul,id_eq,dg] using (QueeliusNappalCost.G_derivative P hA1.1.1 (u+t • du) (v+t • dv) du dv).symm
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      dg t-dg 0 ≤ (LG*(‖du‖^2+‖dv‖^2))*t := by
    have hs := hA1.1.2.2 (u+t • du) (v+t • dv) u v
    simp only [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1] at hs
    have hs' : ‖gradU P (u+t • du) (v+t • dv)-gradU P u v‖^2+
        ‖gradV P (u+t • du) (v+t • dv)-gradV P u v‖^2 ≤
        (LG*t)^2*(‖du‖^2+‖dv‖^2) := by nlinarith only [hs]
    have hblock := two_block_bound _ _ ‖du‖ ‖dv‖ (LG*t) (norm_nonneg _) (norm_nonneg _)
      (norm_nonneg _) (norm_nonneg _) (mul_nonneg hA1.1.2.1 ht.1) hs'
    have hU := real_inner_le_norm (gradU P (u+t • du) (v+t • dv)-gradU P u v) du
    have hV := real_inner_le_norm (gradV P (u+t • du) (v+t • dv)-gradV P u v) dv
    simp only [inner_sub_left] at hU hV
    dsimp [dg]
    simp only [zero_smul,add_zero]
    nlinarith only [hblock,hU,hV]
  have hh := scalar_upper g dg (LG*(‖du‖^2+‖dv‖^2)) hd hb
  dsimp [g,dg,du,dv] at hh
  simp only [one_smul,zero_smul,add_zero,add_sub_cancel] at hh
  linarith only [hh]


theorem scalar_abs (g dg : ℝ → ℝ) (L : ℝ)
    (hd : ∀ t, HasDerivAt g (dg t) t)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, |dg t-dg 0| ≤ L*t) :
    |g 1-g 0-dg 0| ≤ L/2 := by
  have hu := scalar_upper g dg L hd (fun t ht => (le_abs_self _).trans (hb t ht))
  have hl := scalar_upper (fun t => -g t) (fun t => -dg t) L (fun t => (hd t).neg)
    (fun t ht => by have hh := (abs_le.mp (hb t ht)).1; linarith only [hh])
  apply abs_le.mpr
  constructor <;> linarith

theorem gradient_taylor {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (f : X → ℝ) (L : ℝ) (hf : Differentiable ℝ f)
    (hLip : ∀ x y, ‖gradient f x-gradient f y‖ ≤ L*‖x-y‖) (x y : X) :
    |f y-f x-⟪gradient f x,y-x⟫_ℝ| ≤ L/2*‖y-x‖^2 := by
  let d := y-x
  let g := fun t : ℝ => f (x+t • d)
  let dg := fun t : ℝ => ⟪gradient f (x+t • d),d⟫_ℝ
  have hd (t : ℝ) : HasDerivAt g (dg t) t := by
    have hh := (hf _).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const d).const_add x)
    convert! hh using 1
    simp only [dg,inner_gradient_left,id_eq,one_smul]
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : |dg t-dg 0| ≤ (L*‖d‖^2)*t := by
    dsimp [dg]
    simp only [zero_smul,add_zero,←inner_sub_left]
    calc
      _ ≤ ‖gradient f (x+t • d)-gradient f x‖*‖d‖ := abs_real_inner_le_norm _ _
      _ ≤ (L*‖(x+t • d)-x‖)*‖d‖ := mul_le_mul_of_nonneg_right (hLip _ _) (norm_nonneg _)
      _ = _ := by rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg ht.1]; ring
  have hh := scalar_abs g dg (L*‖d‖^2) hd hb
  dsimp [g,dg,d] at hh
  simp only [zero_smul,one_smul,add_zero,add_sub_cancel] at hh
  convert hh using 1 <;> ring

end QueeliusNappalSharp
#print axioms QueeliusNappalSharp.G_upper

#print axioms QueeliusNappalSharp.gradient_taylor

theorem QueeliusNappalSharp.checked_G_upper {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u un : E n) (v vn : E d) :
    P.G (un,vn)-P.G (u,v)-⟪gradU P u v,un-u⟫_ℝ-⟪gradV P u v,vn-v⟫_ℝ ≤
      LG/2*(‖un-u‖^2+‖vn-v‖^2) := QueeliusNappalSharp.G_upper P LG LH L0 LOmj hA1 u un v vn
#print axioms QueeliusNappalSharp.checked_G_upper

set_option autoImplicit false
open NAPPAL.KL NAPPAL.Rate Filter Topology
open scoped InnerProductSpace
namespace QueeliusNappalDual

theorem quadratic_minimum {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (B : X →L[ℝ] Y) (g : X) (q : Y) (γ : ℝ) (v y : X)
    (hmin : ∀ z, ⟪g,y⟫_ℝ+⟪q,B y⟫_ℝ+γ/2*‖B (y-v)‖^2 ≤
      ⟪g,z⟫_ℝ+⟪q,B z⟫_ℝ+γ/2*‖B (z-v)‖^2) :
    g + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (y-v)) = 0 := by
  let z := g + ContinuousLinearMap.adjoint B q + γ • ContinuousLinearMap.adjoint B (B (y-v))
  have hd := (((innerSL ℝ g).hasFDerivAt).add
    (((innerSL ℝ q).comp B).hasFDerivAt)).add
    (((B.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const v)).norm_sq).const_mul (γ/2))
  have hm : IsLocalMin (fun z => ⟪g,z⟫_ℝ+⟪q,B z⟫_ℝ+γ/2*‖B (z-v)‖^2) y :=
    Filter.Eventually.of_forall hmin
  have hh := congrArg (fun f : X →L[ℝ] ℝ => f z) (hd.fderiv.symm.trans hm.fderiv_eq_zero)
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  change ⟪z,z⟫_ℝ=0
  calc
    _ = ⟪g,z⟫_ℝ+⟪q,B z⟫_ℝ+γ*⟪B (y-v),B z⟫_ℝ := by
      simp only [z,inner_add_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left]
    _ = 0 := by
      simp only [add_apply,smul_apply,
        ContinuousLinearMap.coe_comp,Function.comp_apply,ContinuousLinearMap.id_apply,
        zero_apply,innerSL_apply_apply,smul_eq_mul,nsmul_eq_mul,id_eq] at hh
      nlinarith only [hh]

theorem rayleigh {n d m : ℕ} (P : Problem n d m) (v : E d) :
    lamMin P * ‖v‖^2 ≤ ‖P.B v‖^2 := by
  by_cases hv : v=0
  · simp [hv]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hnorm : ‖‖v‖⁻¹ • v‖=1 := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  have hmem : ‖P.B (‖v‖⁻¹ • v)‖^2 ∈ (fun x => ‖P.B x‖^2) '' Metric.sphere (0 : E d) 1 :=
    ⟨‖v‖⁻¹ • v,by simpa only [Metric.mem_sphere,dist_zero_right] using hnorm,rfl⟩
  have hbb : BddBelow ((fun x : E d => ‖P.B x‖^2) '' Metric.sphere (0 : E d) 1) := by
    refine ⟨0,?_⟩
    rintro _ ⟨x,_,rfl⟩
    positivity
  have hh : lamMin P ≤ ‖P.B (‖v‖⁻¹ • v)‖^2 := csInf_le hbb hmem
  rw [map_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hh
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖v‖)
  field_simp [hn] at hm
  nlinarith only [hm]

theorem adjoint_range_bound {n d m : ℕ} (P : Problem n d m) (hlam : 0 ≤ lamMin P)
    (z : E m) (hz : z ∈ Set.range P.B) :
    lamMin P*‖z‖^2 ≤ ‖ContinuousLinearMap.adjoint P.B z‖^2 := by
  obtain ⟨v,rfl⟩ := hz
  by_cases hb : P.B v=0
  · simp [hb]
  have hbpos : 0 < ‖P.B v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hb)
  have hinner : ‖P.B v‖^2 ≤ ‖v‖*‖ContinuousLinearMap.adjoint P.B (P.B v)‖ := by
    rw [P.B.apply_norm_sq_eq_inner_adjoint_right]
    exact real_inner_le_norm v (ContinuousLinearMap.adjoint P.B (P.B v))
  have hs := mul_self_le_mul_self (sq_nonneg ‖P.B v‖) hinner
  have h1 := mul_le_mul_of_nonneg_left hs hlam
  have h2 := mul_le_mul_of_nonneg_right (rayleigh P v)
    (sq_nonneg ‖ContinuousLinearMap.adjoint P.B (P.B v)‖)
  apply (mul_le_mul_iff_right₀ hbpos).mp
  nlinarith only [h1,h2]

theorem dual_identity {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) :
    ContinuousLinearMap.adjoint P.B (p (k+1)) =
      -gradV P (u k) (v k)-gradient P.H (v k)+
        γ • ContinuousLinearMap.adjoint P.B (Theta P (u (k+1))-Theta P (u k)) := by
  have hk := hrun.2.2.2 k
  have hq := quadratic_minimum P.B (gradV P (u k) (v k)+gradient P.H (v k))
    (qseq P γ u v p k) γ (v k) (v (k+1)) hk.2.2.1
  rw [hk.2.2.2]
  simp only [qseq,map_add,map_smul,map_sub] at hq ⊢
  apply sub_eq_zero.mp
  convert hq using 1
  module


theorem dual_step_lower {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 LOmj)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) :
    lamMin P*‖p k-p (k+1)‖^2 ≤ ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖^2 := by
  apply adjoint_range_bound P hA1.2.2.2.2.2.1.2.le
  obtain ⟨z,hz⟩ := hA1.2.2.2.2.2.1.1 (Set.mem_range_self (u (k+1)))
  refine ⟨(-γ) • (z+v (k+1)),?_⟩
  rw [(hrun.2.2.2 k).2.2.2]
  simp only [map_smul,map_add,hz]
  module

theorem gradV_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) (v v' : E d) :
    ‖gradV P u v-gradV P u' v'‖ ≤ LG*(‖u-u'‖+‖v-v'‖) := by
  have h := hA1.1.2.2 u v u' v'
  have hnn := mul_nonneg (sq_nonneg LG) (mul_nonneg (norm_nonneg (u-u')) (norm_nonneg (v-v')))
  have hLG := hA1.1.2.1
  have hp : 0 ≤ LG*(‖u-u'‖+‖v-v'‖) := mul_nonneg hLG (add_nonneg (norm_nonneg _) (norm_nonneg _))
  nlinarith only [h,hnn,hp,norm_nonneg (gradV P u v-gradV P u' v'),sq_nonneg ‖gradU P u v-gradU P u' v'‖]

theorem adjoint_theta_bound {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) :
    ‖ContinuousLinearMap.adjoint P.B (Theta P u-Theta P u')‖ ≤ ‖P.B‖*L0*‖u-u'‖ := by
  calc
    _ ≤ ‖ContinuousLinearMap.adjoint P.B‖*‖Theta P u-Theta P u'‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖P.B‖*‖Theta P u-Theta P u'‖ := by rw [LinearIsometryEquiv.norm_map]
    _ ≤ ‖P.B‖*(L0*‖u-u'‖) := mul_le_mul_of_nonneg_left (hA1.2.2.2.1.2.2.2 u u') (norm_nonneg _)
    _ = _ := by ring

theorem dual_step_norm {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ LG LH L0 : ℝ) (LOmj : Fin m → ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 LOmj)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) (hk : 1 ≤ k) :
    ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖ ≤
      γ*‖P.B‖*L0*‖u k-u (k+1)‖ + (LG+γ*‖P.B‖*L0)*‖u (k-1)-u k‖+
        (LG+LH)*‖v (k-1)-v k‖ := by
  have hprev := dual_identity P K γ σ δ ε u v p hrun (k-1)
  rw [Nat.sub_add_cancel hk] at hprev
  have hnext := dual_identity P K γ σ δ ε u v p hrun k
  let a := gradV P (u k) (v k)-gradV P (u (k-1)) (v (k-1))
  let b := gradient P.H (v k)-gradient P.H (v (k-1))
  let c := γ • ContinuousLinearMap.adjoint P.B (Theta P (u k)-Theta P (u (k+1)))
  let d' := γ • ContinuousLinearMap.adjoint P.B (Theta P (u k)-Theta P (u (k-1)))
  have hid : ContinuousLinearMap.adjoint P.B (p k-p (k+1)) = a+b+c+d' := by
    rw [map_sub,hprev,hnext]
    dsimp [a,b,c,d']
    simp only [map_sub]
    module
  have htri : ‖a+b+c+d'‖ ≤ ‖a‖+‖b‖+‖c‖+‖d'‖ := by
    linarith only [norm_add_le (a+b+c) d',norm_add_le (a+b) c,norm_add_le a b]
  have ha : ‖a‖ ≤ LG*(‖u (k-1)-u k‖+‖v (k-1)-v k‖) := by
    simpa only [a,norm_sub_rev] using gradV_bound P LG LH L0 LOmj hA1 (u k) (u (k-1)) (v k) (v (k-1))
  have hb : ‖b‖ ≤ LH*‖v (k-1)-v k‖ := by
    simpa only [b,norm_sub_rev] using hA1.2.1.2.2 (v k) (v (k-1))
  have hc : ‖c‖ ≤ γ*‖P.B‖*L0*‖u k-u (k+1)‖ := by
    dsimp [c]
    rw [norm_smul,Real.norm_of_nonneg hrun.1.le]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (adjoint_theta_bound P LG LH L0 LOmj hA1 (u k) (u (k+1))) hrun.1.le
  have hd : ‖d'‖ ≤ γ*‖P.B‖*L0*‖u (k-1)-u k‖ := by
    dsimp [d']
    rw [norm_smul,Real.norm_of_nonneg hrun.1.le]
    simpa only [mul_assoc,norm_sub_rev] using mul_le_mul_of_nonneg_left (adjoint_theta_bound P LG LH L0 LOmj hA1 (u k) (u (k-1))) hrun.1.le
  rw [hid]
  nlinarith only [htri,ha,hb,hc,hd]

end QueeliusNappalDual
#print axioms QueeliusNappalDual.quadratic_minimum
#print axioms QueeliusNappalDual.rayleigh
#print axioms QueeliusNappalDual.adjoint_range_bound
#print axioms QueeliusNappalDual.dual_identity

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Zhu, Zhao and Zhang, arXiv:2007.12219v1, Lemma 4.1.
theorem QueeliusNappalDual.checked_lemma {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ)
    (LOmj : Fin m → ℝ) (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hA1 : NAPPAL.KL.Assumption1 P LG LH L0 LOmj)
    (_hA2 : NAPPAL.KL.Assumption2 P K β LK γ LG LH)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) :
    (∀ k : ℕ, ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖^2 ≥
      NAPPAL.KL.lamMin P*‖p k-p (k+1)‖^2) ∧
    (∀ k : ℕ, 1 ≤ k → ContinuousLinearMap.adjoint P.B (p k) =
      -NAPPAL.KL.gradV P (u (k-1)) (v (k-1))-gradient P.H (v (k-1))+
        γ • ContinuousLinearMap.adjoint P.B (NAPPAL.KL.Theta P (u k)-NAPPAL.KL.Theta P (u (k-1)))) ∧
    (∀ k : ℕ, 1 ≤ k → ‖p k-p (k+1)‖^2 ≤
      3*γ^2*‖P.B‖^2*L0^2/NAPPAL.KL.lamMin P*‖u k-u (k+1)‖^2+
      3*(LG+γ*‖P.B‖*L0)^2/NAPPAL.KL.lamMin P*‖u (k-1)-u k‖^2+
      3*(LG+LH)^2/NAPPAL.KL.lamMin P*‖v (k-1)-v k‖^2) := by
  constructor
  · intro k
    exact QueeliusNappalDual.dual_step_lower P K γ σ LG LH L0 LOmj δ ε u v p hA1 hrun k
  constructor
  · intro k hk
    have hh := QueeliusNappalDual.dual_identity P K γ σ δ ε u v p hrun (k-1)
    simpa only [Nat.sub_add_cancel hk] using hh
  · intro k hk
    let a := γ*‖P.B‖*L0*‖u k-u (k+1)‖
    let b := (LG+γ*‖P.B‖*L0)*‖u (k-1)-u k‖
    let c := (LG+LH)*‖v (k-1)-v k‖
    have hnorm := QueeliusNappalDual.dual_step_norm P K γ σ LG LH L0 LOmj δ ε u v p hA1 hrun k hk
    change ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖ ≤ a+b+c at hnorm
    have hquad : ‖ContinuousLinearMap.adjoint P.B (p k-p (k+1))‖^2 ≤ (a+b+c)^2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hnorm
    have hthree : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
      nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
    have hlow := QueeliusNappalDual.dual_step_lower P K γ σ LG LH L0 LOmj δ ε u v p hA1 hrun k
    have hlam := hA1.2.2.2.2.2.1.2
    calc
      _ ≤ (3*(a^2+b^2+c^2))/lamMin P := (le_div_iff₀ hlam).2 (by
        simpa only [mul_comm] using hlow.trans (hquad.trans hthree))
      _ = _ := by
        dsimp [a,b,c]
        field_simp

#print axioms QueeliusNappalDual.checked_lemma


set_option autoImplicit false
open NAPPAL.KL NAPPAL.Rate Filter Topology
open scoped InnerProductSpace

namespace QueeliusNappalDescent

theorem strong_bregman {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (K : X → ℝ) (β : ℝ) (hK : Differentiable ℝ K)
    (hconv : StrongConvexOn Set.univ β K) (x y : X) :
    β/2*‖y-x‖^2 ≤ K y-K x-⟪gradient K x,y-x⟫_ℝ := by
  let f := fun z : X => K z-β/2*‖z‖^2
  let g := fun t : ℝ => f (x+t • (y-x))
  have hc : ConvexOn ℝ Set.univ f := strongConvexOn_iff_convex.mp hconv
  have hg : ConvexOn ℝ Set.univ g := by
    refine ⟨convex_univ,?_⟩
    intro a _ b _ c d hc0 hd0 hcd
    have hh := hc.2 (Set.mem_univ (x+a • (y-x))) (Set.mem_univ (x+b • (y-x))) hc0 hd0 hcd
    have he : x+(c*a+d*b) • (y-x) = c • (x+a • (y-x))+d • (x+b • (y-x)) := by
      calc
        _ = (c+d) • x+(c*a+d*b) • (y-x) := by rw [hcd,one_smul]
        _ = _ := by module
    simpa only [g,smul_eq_mul,he] using hh
  have hp := ((hasDerivAt_id (0 : ℝ)).smul_const (y-x)).const_add x
  have hd : HasDerivAt g (⟪gradient K x,y-x⟫_ℝ-β*⟪x,y-x⟫_ℝ) 0 := by
    have hh := ((hK (x+(0 : ℝ) • (y-x))).hasFDerivAt.comp_hasDerivAt 0 hp).sub
      ((hp.norm_sq).const_mul (β/2))
    convert! hh using 1
    simp only [id_eq,zero_smul,add_zero,one_smul,inner_gradient_left]
    ring
  have hh := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp only [slope,g,f,sub_zero,inv_one,one_smul,zero_smul,add_zero,add_sub_cancel,
    smul_eq_mul,one_mul] at hh
  simp only [inner_sub_right,real_inner_self_eq_norm_sq,vsub_eq_sub] at hh
  rw [← real_inner_comm x y] at hh
  rw [norm_sub_sq_real,inner_sub_right]
  nlinarith only [hh]

theorem Om_taylor {n d m : ℕ} (P : Problem n d m) (L : Fin m → ℝ)
    (hOm : Differentiable ℝ P.Om)
    (hL : ∀ j, 0 ≤ L j ∧ ∀ a b,
      ‖gradient (fun x => P.Om x j) a-gradient (fun x => P.Om x j) b‖ ≤ L j*‖a-b‖)
    (x y : E n) :
    ‖P.Om y-P.Om x-fderiv ℝ P.Om x (y-x)‖ ≤ LOm L/2*‖y-x‖^2 := by
  have hcoord (j : Fin m) :
      ‖(P.Om y-P.Om x-fderiv ℝ P.Om x (y-x)) j‖ ≤ L j/2*‖y-x‖^2 := by
    have hf : Differentiable ℝ (fun z => P.Om z j) := by
      intro z
      exact ((PiLp.proj 2 (fun _ : Fin m => ℝ) j).hasFDerivAt.comp z (hOm z).hasFDerivAt).differentiableAt
    have ht := QueeliusNappalSharp.gradient_taylor (fun z => P.Om z j) (L j) hf (hL j).2 x y
    rw [inner_gradient_left,QueeliusNappalCost.coordinate_fderiv P.Om hOm] at ht
    simpa only [PiLp.sub_apply,Real.norm_eq_abs] using ht
  calc
    _ ≤ ∑ j, ‖(P.Om y-P.Om x-fderiv ℝ P.Om x (y-x)) j‖ :=
      QueeliusNappalCost.euclidean_norm_le_sum _
    _ ≤ ∑ j, L j/2*‖y-x‖^2 := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = _ := by rw [← Finset.sum_mul,← Finset.sum_div]; rfl

end QueeliusNappalDescent

#print axioms QueeliusNappalDescent.strong_bregman
#print axioms QueeliusNappalDescent.Om_taylor

namespace QueeliusNappalDescent

theorem cross_bound {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (a b r s : X) (h : a+b=r-s) :
    ‖a+b‖^2 ≤ ‖a‖^2+‖b‖^2+‖r‖^2+‖s‖^2 := by
  have he := congrArg (fun z : X => ‖z‖^2) h
  have hab := sq_nonneg ‖a-b‖
  have hrs := sq_nonneg ‖r+s‖
  rw [norm_add_sq_real,norm_sub_sq_real] at he
  rw [norm_sub_sq_real] at hab
  rw [norm_add_sq_real] at hrs ⊢
  nlinarith only [he,hab,hrs]

theorem quadratic_gap {n d m : ℕ} (P : Problem n d m) (γ : ℝ)
    (u : E n) (v vn : E d) (q : E m)
    (hv : ∀ y, obj6 P γ u v q vn ≤ obj6 P γ u v q y) :
    ⟪gradV P u v,vn-v⟫_ℝ+⟪gradient P.H v,vn-v⟫_ℝ+⟪q,P.B (vn-v)⟫_ℝ =
      -γ*‖P.B (vn-v)‖^2 := by
  have he := QueeliusNappalDual.quadratic_minimum P.B (gradV P u v+gradient P.H v) q γ v vn hv
  have hi := congrArg (fun z => ⟪z,vn-v⟫_ℝ) he
  simp only [inner_add_left,real_inner_smul_left,ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq,inner_zero_left] at hi
  linarith only [hi]

theorem lagrangian_change {n d m : ℕ} (P : Problem n d m) (γ : ℝ)
    (u un : E n) (v vn : E d) (p : E m) :
    augLag P γ (un,vn,p)-augLag P γ (u,v,p) =
      F P un vn-F P u v+⟪p+γ • (Theta P u+P.B v),
        (Theta P un+P.B vn)-(Theta P u+P.B v)⟫_ℝ+
      γ/2*‖(Theta P un+P.B vn)-(Theta P u+P.B v)‖^2 := by
  unfold augLag
  generalize Theta P u+P.B v = r
  generalize Theta P un+P.B vn = s
  simp only [inner_add_left,real_inner_smul_left,inner_sub_right,norm_sub_sq_real,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm s r]
  ring

end QueeliusNappalDescent

namespace QueeliusNappalDescent

theorem primal_descent {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ eps : ℝ)
    (L : Fin m → ℝ) (K : E n → ℝ)
    (hA1 : Assumption1 P LG LH L0 L) (hA2 : Assumption2 P K β LK γ LG LH)
    (hγ : 0 < γ) (heps : 0 < eps) (u un : E n) (v vn : E d) (p : E m)
    (hu : obj5 P K u v (p+γ • (Theta P u+P.B v)) eps un ≤
      obj5 P K u v (p+γ • (Theta P u+P.B v)) eps u)
    (hv : ∀ y, obj6 P γ u v (p+γ • (Theta P u+P.B v)) vn ≤
      obj6 P γ u v (p+γ • (Theta P u+P.B v)) y) :
    augLag P γ (un,vn,p)-augLag P γ (u,v,p) ≤
      -(β/(2*eps)-(LG+‖p+γ • (Theta P u+P.B v)‖*LOm L+γ*L0^2)/2)*‖un-u‖^2 -
      (γ*lamMin P-(LG+LH))/2*‖vn-v‖^2 +
      γ/2*(‖Theta P u+P.B v‖^2+‖Theta P un+P.B vn‖^2) := by
  let q := p+γ • (Theta P u+P.B v)
  have hG := QueeliusNappalSharp.G_upper P LG LH L0 L hA1 u un v vn
  have hH := (le_abs_self _).trans
    (QueeliusNappalSharp.gradient_taylor P.H LH hA1.2.1.1 hA1.2.1.2.2 v vn)
  have hO : ⟪q,P.Om un-P.Om u-fderiv ℝ P.Om u (un-u)⟫_ℝ ≤
      ‖q‖*(LOm L/2*‖un-u‖^2) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (Om_taylor P L hA1.2.2.2.1.1 hA1.2.2.2.2.1 u un) (norm_nonneg q))
  have hB : β/2*‖un-u‖^2/eps ≤ bregman K un u/eps :=
    div_le_div_of_nonneg_right (strong_bregman K β hA2.1 hA2.2.2.1 u un) heps.le
  have hV := quadratic_gap P γ u v vn q hv
  have hU : obj5 P K u v q eps un ≤ obj5 P K u v q eps u := hu
  simp only [obj5,bregman,sub_self,inner_zero_right,sub_self,zero_div,add_zero] at hU
  have hbase : F P un vn-F P u v+
      ⟪q,(Theta P un+P.B vn)-(Theta P u+P.B v)⟫_ℝ ≤
      -(β/(2*eps)-(LG+‖q‖*LOm L)/2)*‖un-u‖^2+
      (LG+LH)/2*‖vn-v‖^2-γ*‖P.B (vn-v)‖^2 := by
    simp only [bregman] at hB
    simp only [F,Theta,inner_add_right,inner_sub_right,map_sub] at hO hV hG hH hU hB ⊢
    linear_combination hG+hH+hO+hB+hU+hV
  have hcross := cross_bound (Theta P un-Theta P u) (P.B (vn-v))
    (Theta P un+P.B vn) (Theta P u+P.B v) (by simp only [map_sub]; module)
  have htheta := hA1.2.2.2.1.2.2.2 un u
  have htheta2 : ‖Theta P un-Theta P u‖^2 ≤ L0^2*‖un-u‖^2 := by
    have hh := mul_self_le_mul_self (norm_nonneg _) htheta
    nlinarith only [hh]
  have hray := QueeliusNappalDual.rayleigh P (vn-v)
  have hc := mul_le_mul_of_nonneg_left hcross (show 0 ≤ γ/2 by positivity)
  have ht := mul_le_mul_of_nonneg_left htheta2 (show 0 ≤ γ/2 by positivity)
  have hb := mul_le_mul_of_nonneg_left hray (show 0 ≤ γ/2 by positivity)
  have hid : (Theta P un+P.B vn)-(Theta P u+P.B v) =
      (Theta P un-Theta P u)+P.B (vn-v) := by simp only [map_sub]; module
  rw [lagrangian_change,hid]
  rw [hid] at hbase
  dsimp only [q] at hbase
  nlinarith only [hbase,hc,ht,hb]

end QueeliusNappalDescent
#print axioms QueeliusNappalDescent.primal_descent

namespace QueeliusNappalDescent

theorem residual_norm {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) :
    ‖p k-p (k+1)‖^2 = γ^2*‖Theta P (u (k+1))+P.B (v (k+1))‖^2 := by
  have he : p k-p (k+1) = -γ • (Theta P (u (k+1))+P.B (v (k+1))) := by
    rw [(hrun.2.2.2 k).2.2.2]
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos hrun.1]
  ring

theorem run_primal {n d m : ℕ} (P : Problem n d m) (LG LH L0 LK β γ σ : ℝ) (L : Fin m → ℝ)
    (K : E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 L) (hA2 : Assumption2 P K β LK γ LG LH)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) (hk : 1 ≤ k) :
    augLag P γ (u (k+1),v (k+1),p k)-augLag P γ (u k,v k,p k) ≤
      -(β/(2*ε k)-(LG+‖qseq P γ u v p k‖*LOm L+γ*L0^2)/2)*‖u k-u (k+1)‖^2 -
      (γ*lamMin P-(LG+LH))/2*‖v k-v (k+1)‖^2 +
      1/(2*γ)*(‖p (k-1)-p k‖^2-‖p k-p (k+1)‖^2)+1/γ*‖p k-p (k+1)‖^2 := by
  have heps : 0 < ε k := (mul_pos hrun.2.1 (hrun.2.2.2 k).1.1).trans_le (hrun.2.2.2 k).1.2.1
  have hu : u k ∈ P.U := by
    simpa only [Nat.sub_add_cancel hk] using (hrun.2.2.2 (k-1)).2.1.1
  have hh := primal_descent P LG LH L0 LK β γ (ε k) L K hA1 hA2 hrun.1 heps
    (u k) (u (k+1)) (v k) (v (k+1)) (p k) ((hrun.2.2.2 k).2.1.2 (u k) hu)
    (hrun.2.2.2 k).2.2.1
  have hp := residual_norm P K γ σ δ ε u v p hrun (k-1)
  rw [Nat.sub_add_cancel hk] at hp
  have hn := residual_norm P K γ σ δ ε u v p hrun k
  convert hh using 1
  rw [hp,hn]
  simp only [qseq,norm_sub_rev]
  field_simp
  <;> ring

theorem run_dual {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ)
    (γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (k : ℕ) :
    augLag P γ (u (k+1),v (k+1),p (k+1))-augLag P γ (u (k+1),v (k+1),p k) =
      1/γ*‖p k-p (k+1)‖^2 := by
  have hchange : augLag P γ (u (k+1),v (k+1),p (k+1))-
      augLag P γ (u (k+1),v (k+1),p k) =
      γ*‖Theta P (u (k+1))+P.B (v (k+1))‖^2 := by
    rw [(hrun.2.2.2 k).2.2.2]
    unfold augLag
    generalize Theta P (u (k+1))+P.B (v (k+1)) = r
    simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    ring
  rw [hchange,residual_norm P K γ σ δ ε u v p hrun k]
  field_simp [hrun.1.ne']

end QueeliusNappalDescent


theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 LK β γ σ : ℝ) (LOmj : Fin m → ℝ)
    (K : NAPPAL.KL.E n → ℝ) (δ ε : ℕ → ℝ) (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hA1 : NAPPAL.KL.Assumption1 P LG LH L0 LOmj) (hA2 : NAPPAL.KL.Assumption2 P K β LK γ LG LH)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) :
    (∀ k : ℕ, 1 ≤ k →
      NAPPAL.KL.augLag P γ (u (k + 1), v (k + 1), p k) - NAPPAL.KL.augLag P γ (u k, v k, p k) ≤
        -(β / (2 * ε k) - (LG + ‖qseq P γ u v p k‖ * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2) / 2) *
            ‖u k - u (k + 1)‖ ^ 2 -
          (γ * NAPPAL.KL.lamMin P - (LG + LH)) / 2 * ‖v k - v (k + 1)‖ ^ 2 +
          1 / (2 * γ) * (‖p (k - 1) - p k‖ ^ 2 - ‖p k - p (k + 1)‖ ^ 2) +
          1 / γ * ‖p k - p (k + 1)‖ ^ 2) ∧
    (∀ k : ℕ,
      NAPPAL.KL.augLag P γ (u (k + 1), v (k + 1), p (k + 1)) - NAPPAL.KL.augLag P γ (u (k + 1), v (k + 1), p k) =
        1 / γ * ‖p k - p (k + 1)‖ ^ 2) ∧
    (∀ k : ℕ, 1 ≤ k →
      NAPPAL.KL.augLag P γ (u (k + 1), v (k + 1), p (k + 1)) - NAPPAL.KL.augLag P γ (u k, v k, p k) ≤
        -(β / (2 * ε k) - (LG + ‖qseq P γ u v p k‖ * NAPPAL.KL.LOm LOmj + γ * L0 ^ 2) / 2) *
            ‖u k - u (k + 1)‖ ^ 2 -
          (γ * NAPPAL.KL.lamMin P - (LG + LH)) / 2 * ‖v k - v (k + 1)‖ ^ 2 +
          1 / (2 * γ) * (‖p (k - 1) - p k‖ ^ 2 - ‖p k - p (k + 1)‖ ^ 2) +
          6 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / NAPPAL.KL.lamMin P * ‖u k - u (k + 1)‖ ^ 2 +
          6 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * NAPPAL.KL.lamMin P) * ‖u (k - 1) - u k‖ ^ 2 +
          6 * (LG + LH) ^ 2 / (γ * NAPPAL.KL.lamMin P) * ‖v (k - 1) - v k‖ ^ 2)  := by
  have hfirst := QueeliusNappalDescent.run_primal P LG LH L0 LK β γ σ LOmj K δ ε u v p hA1 hA2 hrun
  have hdual := QueeliusNappalDescent.run_dual P K γ σ δ ε u v p hrun
  refine ⟨hfirst,hdual,?_⟩
  intro k hk
  have hbound := (QueeliusNappalDual.checked_lemma P LG LH L0 LK β γ σ LOmj K δ ε u v p hA1 hA2 hrun).2.2 k hk
  have hb := mul_le_mul_of_nonneg_left hbound (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hrun.1.le)
  have hb' : 2/γ*‖p k-p (k+1)‖^2 ≤
      6*γ*‖P.B‖^2*L0^2/lamMin P*‖u k-u (k+1)‖^2+
      6*(LG+γ*‖P.B‖*L0)^2/(γ*lamMin P)*‖u (k-1)-u k‖^2+
      6*(LG+LH)^2/(γ*lamMin P)*‖v (k-1)-v k‖^2 := by
    convert! hb using 1
    field_simp [hrun.1.ne']
    <;> ring
  linear_combination hfirst k hk + hdual k + hb'



#print axioms solution
