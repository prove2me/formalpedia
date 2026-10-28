-- Prove2me | solution 2 for NAPPAL.Subreg.lemma_6_1_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:40:00.129738+00:00
-- url     : https://prove2.me/submissions/dd72c279-3288-4ba1-9187-0a9d2a94dbec

import Mathlib
import Definitions.Def_NAPPAL_Subreg_Setting
import Theorems.Thm_NAPPAL_Rate_lemma_4_3

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


end QueeliusNappalDual


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


namespace QueeliusNappalDual
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
end QueeliusNappalDual

namespace NASol

theorem toRate {n d m : ℕ} (P : Problem n d m) (K : E n → ℝ) (γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (h : NAPPAL.KL.IsNAPPAL P K γ σ δ ε u v p) : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun k => ?_⟩
  obtain ⟨a, b, c, d, e, f⟩ := h4 k
  exact ⟨⟨a, b, c⟩, d, e, f⟩

theorem fst_le {n d m : ℕ} (x : W n d m) : ‖x.1‖ ≤ tnorm x := by
  unfold tnorm; apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖x.2.1‖, sq_nonneg ‖x.2.2‖]
theorem snd_le {n d m : ℕ} (x : W n d m) : ‖x.2.1‖ ≤ tnorm x := by
  unfold tnorm; apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖x.1‖, sq_nonneg ‖x.2.2‖]
theorem thd_le {n d m : ℕ} (x : W n d m) : ‖x.2.2‖ ≤ tnorm x := by
  unfold tnorm; apply Real.le_sqrt_of_sq_le; nlinarith [sq_nonneg ‖x.2.1‖, sq_nonneg ‖x.1‖]

theorem lamMin_pos {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) : 0 < lamMin P := hA1.2.2.2.2.2.1.2

theorem LOm_nonneg {m : ℕ} (LOmj : Fin m → ℝ) (h : ∀ j, 0 ≤ LOmj j) : 0 ≤ LOm LOmj :=
  Finset.sum_nonneg (fun j _ => h j)

theorem theta_lip {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (hA1 : Assumption1 P LG LH L0 LOmj) (u u' : E n) (v v' : E d) :
    ‖(Theta P u + P.B v) - (Theta P u' + P.B v')‖ ≤ L0 * ‖u - u'‖ + ‖P.B‖ * ‖v - v'‖ := by
  have h1 := hA1.2.2.2.1.2.2.2 u u'
  have h2 : ‖P.B (v - v')‖ ≤ ‖P.B‖ * ‖v - v'‖ := P.B.le_opNorm _
  have he : (Theta P u + P.B v) - (Theta P u' + P.B v') = (Theta P u - Theta P u') + P.B (v - v') := by
    rw [map_sub]; abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

theorem pm_le (x y A B : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ A) (hy0 : 0 ≤ y) (hy : y ≤ B) :
    x * y ≤ A * B := mul_le_mul hx hy hy0 (hx0.trans hx)

theorem prod_norm_le {n d : ℕ} (a : E n) (b : E d) (s : ℝ) (ha : ‖a‖ ≤ s) (hb : ‖b‖ ≤ s) :
    ‖((a, b) : E n × E d)‖ ≤ s := by
  rw [Prod.norm_def]; exact max_le ha hb

/-- Main estimate given a uniform bound on `q^k`. -/
theorem main_est {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 LOmj) (hA2 : Assumption2 P K β LK γ LG LH)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p)
    (hδ : ∀ k, δ k = delta8 P LG L0 (LOm LOmj) β γ (qseq P γ u v p k))
    (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ k, ‖qseq P γ u v p k‖ ≤ Q) :
    ∃ c6 : ℝ, 0 < c6 ∧ ∀ wbar : W n d m, IsStationary P γ wbar → ∀ k : ℕ,
      augLag P γ (wseq u v p (k+1)) - augLag P γ wbar ≤
        c6 * (wdist wbar (wseq u v p (k+1)) ^ 2 + wdist (wseq u v p k) (wseq u v p (k+1)) ^ 2) := by
  have hγ : 0 < γ := hrun.1
  have hσ : 0 < σ := hrun.2.1
  have hβ : 0 < β := hA2.2.1
  have hLK : 0 ≤ LK := hA2.2.2.2.1
  have hLG : 0 ≤ LG := hA1.1.2.1
  have hLH : 0 ≤ LH := hA1.2.1.2.1
  have hL0 : 0 ≤ L0 := hA1.2.2.2.1.2.2.1
  have hlam := lamMin_pos P LG LH L0 LOmj hA1
  have hLO : 0 ≤ LOm LOmj := LOm_nonneg LOmj (fun j => (hA1.2.2.2.2.1 j).1)
  have hBn : 0 ≤ ‖P.B‖ := norm_nonneg _
  set DQ : ℝ := LG + Q * LOm LOmj + γ * L0 ^ 2 + 14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
    14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1 with hDQ
  set CE : ℝ := DQ / (σ * β) with hCE
  have hCE0 : 0 ≤ CE := by
    apply div_nonneg _ (by positivity)
    rw [hDQ]; have := mul_nonneg hQ0 hLO; positivity
  -- 1/ε_k ≤ CE
  have heps : ∀ k, 0 < ε k ∧ 1 / ε k ≤ CE := by
    intro k
    obtain ⟨⟨hd0, hse, _⟩, _⟩ := hrun.2.2.2 k
    have he0 : 0 < ε k := lt_of_lt_of_le (mul_pos hσ hd0) hse
    refine ⟨he0, ?_⟩
    have hdk := hδ k
    unfold delta8 at hdk
    set D : ℝ := LG + ‖qseq P γ u v p k‖ * LOm LOmj + γ * L0 ^ 2 + 14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P +
      14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) + 1 with hD
    have hD1 : 1 ≤ D := by
      rw [hD]; have := mul_nonneg (norm_nonneg (qseq P γ u v p k)) hLO
      have : 0 ≤ 14 * γ * ‖P.B‖ ^ 2 * L0 ^ 2 / lamMin P := by positivity
      have : 0 ≤ 14 * (LG + γ * ‖P.B‖ * L0) ^ 2 / (γ * lamMin P) := by positivity
      have : 0 ≤ γ * L0 ^ 2 := by positivity
      linarith
    have hDle : D ≤ DQ := by
      rw [hD, hDQ]
      have := mul_le_mul_of_nonneg_right (hQ k) hLO
      linarith
    have hD0 : 0 < D := by linarith
    -- σ δ_k = σ β / D ≤ ε k
    have h1 : σ * β / D ≤ ε k := by rw [hdk] at hse; rwa [mul_div_assoc]
    rw [hCE, div_le_div_iff₀ he0 (by positivity)]
    have h2 : σ * β ≤ ε k * D := by rwa [div_le_iff₀ hD0] at h1
    have h3 := mul_le_mul_of_nonneg_left hDle he0.le
    linarith
  set C : ℝ := (L0 + ‖P.B‖) + Q * LOm LOmj + 8 * LG + 2 * LH + 2 * LK * CE +
    γ / 2 * (‖P.B‖ ^ 2 + 1 / γ ^ 2) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; have := mul_nonneg hQ0 hLO; have := mul_nonneg hLK hCE0; positivity
  refine ⟨2 * C + 1, by linarith, ?_⟩
  rintro ⟨ub, vb, pb⟩ hstat k
  obtain ⟨a0, ha0, b0, hb0, h1, h2, h3⟩ := hstat
  have hfeas : Theta P ub + P.B vb = 0 := h3.symm
  have hub : ub ∈ P.U := hb0.1
  obtain ⟨_, ⟨_, hu5⟩, hv6, hp7⟩ := hrun.2.2.2 k
  have hcd := QueeliusNappalCost.cost_decomposition P K γ (u k) ub (u (k+1)) (v k) vb (v (k+1))
    pb (p (k+1)) (qseq P γ u v p k) (ε k) hfeas (hu5 ub hub) (hv6 vb)
  -- notation
  set a := wdist (ub, vb, pb) (wseq u v p (k+1)) with ha
  set b := wdist (wseq u v p k) (wseq u v p (k+1)) with hb
  have ha0' : 0 ≤ a := Real.sqrt_nonneg _
  have hb0' : 0 ≤ b := Real.sqrt_nonneg _
  set s := a + b with hs
  have hs0 : 0 ≤ s := by positivity
  have hA_u : ‖ub - u (k+1)‖ ≤ a := fst_le ((ub, vb, pb) - wseq u v p (k+1))
  have hA_v : ‖vb - v (k+1)‖ ≤ a := snd_le ((ub, vb, pb) - wseq u v p (k+1))
  have hB_u : ‖u k - u (k+1)‖ ≤ b := fst_le (wseq u v p k - wseq u v p (k+1))
  have hB_v : ‖v k - v (k+1)‖ ≤ b := snd_le (wseq u v p k - wseq u v p (k+1))
  have hB_p : ‖p k - p (k+1)‖ ≤ b := thd_le (wseq u v p k - wseq u v p (k+1))
  have e_unu : ‖u (k+1) - u k‖ ≤ s := by rw [norm_sub_rev]; linarith
  have e_vnv : ‖v (k+1) - v k‖ ≤ s := by rw [norm_sub_rev]; linarith
  have e_ubu : ‖ub - u k‖ ≤ s := by
    have := norm_sub_le_norm_sub_add_norm_sub ub (u (k+1)) (u k)
    rw [norm_sub_rev (u (k+1))] at this; linarith
  have e_vbv : ‖vb - v k‖ ≤ s := by
    have := norm_sub_le_norm_sub_add_norm_sub vb (v (k+1)) (v k)
    rw [norm_sub_rev (v (k+1))] at this; linarith
  have e_unub : ‖u (k+1) - ub‖ ≤ s := by rw [norm_sub_rev]; linarith
  have e_vnvb : ‖v (k+1) - vb‖ ≤ s := by rw [norm_sub_rev]; linarith
  have e_p : ‖p (k+1) - p k‖ ≤ s := by rw [norm_sub_rev]; linarith
  clear_value s
  -- T1
  set rn := Theta P (u (k+1)) + P.B (v (k+1)) with hrn
  set rk := Theta P (u k) + P.B (v k) with hrk
  have hpq : p (k+1) - qseq P γ u v p k = γ • (rn - rk) := by
    rw [hp7]; simp only [qseq, smul_sub]; abel
  have hrn_eq : rn = (1/γ) • (p (k+1) - p k) := by
    rw [hp7, add_sub_cancel_left, smul_smul, one_div, inv_mul_cancel₀ hγ.ne', one_smul]
  have hrn_le : ‖rn‖ ≤ s / γ := by
    rw [hrn_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc 1 / γ * ‖p (k+1) - p k‖ = ‖p (k+1) - p k‖ / γ := by ring
      _ ≤ s / γ := by gcongr
  have hpq_le : ‖p (k+1) - qseq P γ u v p k‖ ≤ γ * ((L0 + ‖P.B‖) * s) := by
    rw [hpq, norm_smul, Real.norm_of_nonneg hγ.le]
    apply mul_le_mul_of_nonneg_left _ hγ.le
    have := theta_lip P LG LH L0 LOmj hA1 (u (k+1)) (u k) (v (k+1)) (v k)
    have := mul_le_mul_of_nonneg_left e_unu hL0
    have := mul_le_mul_of_nonneg_left e_vnv hBn
    linarith
  have T1 : ⟪p (k+1) - qseq P γ u v p k, rn⟫_ℝ ≤ (L0 + ‖P.B‖) * s ^ 2 := by
    refine (real_inner_le_norm _ _).trans ?_
    have := pm_le _ _ _ _ (norm_nonneg _) hpq_le (norm_nonneg _) hrn_le
    calc _ ≤ _ := this
      _ = (L0 + ‖P.B‖) * s ^ 2 := by field_simp
  -- T2
  have T2 : ⟪qseq P γ u v p k, P.Om (u (k+1)) - P.Om ub - fderiv ℝ P.Om (u k) (u (k+1) - ub)⟫_ℝ ≤
      Q * LOm LOmj * s ^ 2 := by
    have ho1 := QueeliusNappalDescent.Om_taylor P LOmj hA1.2.2.2.1.1 hA1.2.2.2.2.1 (u k) (u (k+1))
    have ho2 := QueeliusNappalDescent.Om_taylor P LOmj hA1.2.2.2.1.1 hA1.2.2.2.2.1 (u k) ub
    have he : P.Om (u (k+1)) - P.Om ub - fderiv ℝ P.Om (u k) (u (k+1) - ub) =
        (P.Om (u (k+1)) - P.Om (u k) - fderiv ℝ P.Om (u k) (u (k+1) - u k)) -
        (P.Om ub - P.Om (u k) - fderiv ℝ P.Om (u k) (ub - u k)) := by
      simp only [map_sub]; abel
    have hn : ‖P.Om (u (k+1)) - P.Om ub - fderiv ℝ P.Om (u k) (u (k+1) - ub)‖ ≤ LOm LOmj * s ^ 2 := by
      rw [he]
      refine (norm_sub_le _ _).trans ?_
      have h1 : ‖u (k+1) - u k‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e_unu 2
      have h2 : ‖ub - u k‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e_ubu 2
      have := mul_le_mul_of_nonneg_left h1 hLO
      have := mul_le_mul_of_nonneg_left h2 hLO
      linarith
    refine (real_inner_le_norm _ _).trans ?_
    have := pm_le _ _ _ _ (norm_nonneg _) (hQ k) (norm_nonneg _) hn
    linarith
  -- T3
  have T3 : P.G (u (k+1), v (k+1)) - P.G (ub, vb) - ⟪gradU P (u k) (v k), u (k+1) - ub⟫_ℝ -
      ⟪gradV P (u k) (v k), v (k+1) - vb⟫_ℝ ≤ 8 * LG * s ^ 2 := by
    have hf := QueeliusNappalCost.fderiv_three_point P.G (4 * LG) (by positivity) hA1.1.1
      (QueeliusNappalCost.G_fderiv_lipschitz P LG hA1.1.1 hLG hA1.1.2.2) (u k, v k)
      (u (k+1), v (k+1)) (ub, vb)
    have hgd := QueeliusNappalCost.G_derivative P hA1.1.1 (u k) (v k) (u (k+1) - ub) (v (k+1) - vb)
    have hpe : ((u (k+1), v (k+1)) : E n × E d) - (ub, vb) = (u (k+1) - ub, v (k+1) - vb) := rfl
    rw [hpe, hgd] at hf
    have n1 : ‖((u (k+1), v (k+1)) : E n × E d) - (u k, v k)‖ ≤ s := prod_norm_le _ _ _ e_unu e_vnv
    have n2 : ‖((ub, vb) : E n × E d) - (u k, v k)‖ ≤ s := prod_norm_le _ _ _ e_ubu e_vbv
    have n3 : ‖((u (k+1) - ub, v (k+1) - vb) : E n × E d)‖ ≤ s := prod_norm_le _ _ _ e_unub e_vnvb
    have hle := le_abs_self (P.G (u (k+1), v (k+1)) - P.G (ub, vb) -
      (⟪gradU P (u k) (v k), u (k+1) - ub⟫_ℝ + ⟪gradV P (u k) (v k), v (k+1) - vb⟫_ℝ))
    rw [← Real.norm_eq_abs] at hle
    have hm := pm_le _ _ _ _ (by positivity) (mul_le_mul_of_nonneg_left (add_le_add n1 n2)
      (by positivity : (0:ℝ) ≤ 4 * LG)) (norm_nonneg _) n3
    have hfin : 4 * LG * (s + s) * s = 8 * LG * s ^ 2 := by ring
    have hsub : P.G (u (k+1), v (k+1)) - P.G (ub, vb) - ⟪gradU P (u k) (v k), u (k+1) - ub⟫_ℝ -
      ⟪gradV P (u k) (v k), v (k+1) - vb⟫_ℝ = P.G (u (k+1), v (k+1)) - P.G (ub, vb) -
      (⟪gradU P (u k) (v k), u (k+1) - ub⟫_ℝ + ⟪gradV P (u k) (v k), v (k+1) - vb⟫_ℝ) := by ring
    rw [hsub]
    linarith
  -- T4
  have T4 : P.H (v (k+1)) - P.H vb - ⟪gradient P.H (v k), v (k+1) - vb⟫_ℝ ≤ 2 * LH * s ^ 2 := by
    have hf := QueeliusNappalCost.gradient_three_point P.H LH hLH hA1.2.1.1 hA1.2.1.2.2
      (v k) (v (k+1)) vb
    have hle := le_abs_self (P.H (v (k+1)) - P.H vb - ⟪gradient P.H (v k), v (k+1) - vb⟫_ℝ)
    rw [← Real.norm_eq_abs] at hle
    have hm := pm_le _ _ _ _ (by positivity) (mul_le_mul_of_nonneg_left (add_le_add e_vnv e_vbv) hLH)
      (norm_nonneg _) e_vnvb
    have hfin : LH * (s + s) * s = 2 * LH * s ^ 2 := by ring
    linarith
  -- T5
  have T5 : (bregman K ub (u k) - bregman K (u (k+1)) (u k)) / ε k ≤ 2 * LK * CE * s ^ 2 := by
    have hb1 := QueeliusNappalCost.bregman_bound K LK hLK hA2.1 hA2.2.2.2.2.1 (u k) ub
    have hb2 := QueeliusNappalCost.bregman_bound K LK hLK hA2.1 hA2.2.2.2.2.1 (u k) (u (k+1))
    have h1 : ‖u (k+1) - u k‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e_unu 2
    have h2 : ‖ub - u k‖ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e_ubu 2
    have hnum : bregman K ub (u k) - bregman K (u (k+1)) (u k) ≤ 2 * LK * s ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 hLK
      have := mul_le_mul_of_nonneg_left h2 hLK
      have := (abs_le.mp hb1).2
      have := (abs_le.mp hb2).1
      linarith
    obtain ⟨he0, hec⟩ := heps k
    have hn0 : 0 ≤ 2 * LK * s ^ 2 := by positivity
    rw [div_eq_mul_one_div]
    calc _ ≤ 2 * LK * s ^ 2 * (1 / ε k) := mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ 2 * LK * s ^ 2 * CE := mul_le_mul_of_nonneg_left hec hn0
      _ = _ := by ring
  -- T6
  have T6 : γ / 2 * (‖P.B (vb - v k)‖ ^ 2 - ‖P.B (v (k+1) - v k)‖ ^ 2 + ‖rn‖ ^ 2) ≤
      γ / 2 * (‖P.B‖ ^ 2 + 1 / γ ^ 2) * s ^ 2 := by
    have h1 : ‖P.B (vb - v k)‖ ≤ ‖P.B‖ * s :=
      (P.B.le_opNorm _).trans (mul_le_mul_of_nonneg_left e_vbv hBn)
    have h1' : ‖P.B (vb - v k)‖ ^ 2 ≤ ‖P.B‖ ^ 2 * s ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h2' : ‖rn‖ ^ 2 ≤ (s / γ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hrn_le 2
    have h3 : (s / γ) ^ 2 = 1 / γ ^ 2 * s ^ 2 := by field_simp
    rw [h3] at h2'
    have := sq_nonneg ‖P.B (v (k+1) - v k)‖
    have hγ2 : 0 ≤ γ / 2 := by positivity
    have hin : ‖P.B (vb - v k)‖ ^ 2 - ‖P.B (v (k+1) - v k)‖ ^ 2 + ‖rn‖ ^ 2 ≤
      (‖P.B‖ ^ 2 + 1 / γ ^ 2) * s ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_left hin hγ2
    linarith
  have hsum : augLag P γ (wseq u v p (k+1)) - augLag P γ (ub, vb, pb) ≤ C * s ^ 2 := by
    have : augLag P γ (wseq u v p (k+1)) = augLag P γ (u (k+1), v (k+1), p (k+1)) := rfl
    rw [this]
    refine hcd.trans ?_
    rw [hC]
    have : (L0 + ‖P.B‖ + Q * LOm LOmj + 8 * LG + 2 * LH + 2 * LK * CE +
      γ / 2 * (‖P.B‖ ^ 2 + 1 / γ ^ 2)) * s ^ 2 = (L0 + ‖P.B‖) * s ^ 2 + Q * LOm LOmj * s ^ 2 +
      8 * LG * s ^ 2 + 2 * LH * s ^ 2 + 2 * LK * CE * s ^ 2 + γ / 2 * (‖P.B‖ ^ 2 + 1 / γ ^ 2) * s ^ 2 := by ring
    linarith [T1, T2, T3, T4, T5, T6]
  have hs2 : s ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h0 := sq_nonneg (a - b)
    have h1 : s ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by rw [hs]; ring
    have h2 : (a - b) ^ 2 = a ^ 2 - 2 * (a * b) + b ^ 2 := by ring
    linarith
  have : C * s ^ 2 ≤ C * (2 * (a ^ 2 + b ^ 2)) := mul_le_mul_of_nonneg_left hs2 hC0
  have : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have : (2 * C + 1) * (a ^ 2 + b ^ 2) = C * (2 * (a ^ 2 + b ^ 2)) + (a ^ 2 + b ^ 2) := by ring
  linarith

end NASol

namespace NASol

theorem lower_step {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hA1 : Assumption1 P LG LH L0 LOmj) (hA2 : Assumption2 P K β LK γ LG LH)
    (hrun : NAPPAL.Rate.IsNAPPAL P K γ σ δ ε u v p) (j : ℕ) :
    ∃ vt : E d, Theta P (u (j+1)) + P.B vt = 0 ∧
      lamMin P * ‖v (j+1) - vt‖ ^ 2 ≤ ‖Theta P (u (j+1)) + P.B (v (j+1))‖ ^ 2 ∧
      F P (u (j+1)) vt ≤ Lam P LG LH L0 γ u v p (j+1) := by
  have hγ : 0 < γ := hrun.1
  have hLG : 0 ≤ LG := hA1.1.2.1
  have hLH : 0 ≤ LH := hA1.2.1.2.1
  have hL0 : 0 ≤ L0 := hA1.2.2.2.1.2.2.1
  have hlam := lamMin_pos P LG LH L0 LOmj hA1
  have hBn : 0 ≤ ‖P.B‖ := norm_nonneg _
  obtain ⟨z0, hz0⟩ := hA1.2.2.2.2.2.1.1 (Set.mem_range_self (u (j+1)))
  set uk := u (j+1)
  set vk := v (j+1)
  set r := Theta P uk + P.B vk with hr
  set z := vk + z0 with hz
  have hBz : P.B z = r := by rw [hz, map_add, hz0, hr]; abel
  refine ⟨-z0, by rw [map_neg, hz0]; abel, ?_, ?_⟩
  · have : vk - -z0 = z := by rw [hz]; abel
    rw [this, ← hBz]; exact QueeliusNappalDual.rayleigh P z
  have hray : lamMin P * ‖z‖ ^ 2 ≤ ‖r‖ ^ 2 := by rw [← hBz]; exact QueeliusNappalDual.rayleigh P z
  have hvt : -z0 - vk = -z := by rw [hz]; abel
  -- descent in v
  have hG := QueeliusNappalSharp.G_upper P LG LH L0 LOmj hA1 uk uk vk (-z0)
  have hH := QueeliusNappalSharp.gradient_taylor P.H LH hA1.2.1.1 hA1.2.1.2.2 vk (-z0)
  rw [hvt] at hG hH
  simp only [sub_self, inner_zero_right, norm_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_add] at hG
  have hH' := (abs_le.mp hH).2
  rw [norm_neg] at hG hH'
  -- dual identity
  have hdual := QueeliusNappalDual.dual_identity P K γ σ δ ε u v p hrun j
  set g1 := gradV P (u j) (v j) + gradient P.H (v j) with hg1
  set gk := gradV P uk vk + gradient P.H vk with hgk
  set tB := γ • ContinuousLinearMap.adjoint P.B (Theta P uk - Theta P (u j)) with htB
  have hdual' : g1 = -ContinuousLinearMap.adjoint P.B (p (j+1)) + tB := by
    rw [hdual, hg1, htB]; abel
  set e := (gk - g1) + tB with he
  have hgz : ⟪gk, z⟫_ℝ = ⟪e, z⟫_ℝ - ⟪p (j+1), r⟫_ℝ := by
    have : gk = e + (-ContinuousLinearMap.adjoint P.B (p (j+1))) := by
      rw [he, hdual']; abel
    rw [this, inner_add_left, inner_neg_left, ContinuousLinearMap.adjoint_inner_left, hBz]
    ring
  -- bound on e
  set X := ‖u j - uk‖
  set Y := ‖v j - vk‖
  have heb : ‖e‖ ≤ (LG + γ * ‖P.B‖ * L0) * X + (LG + LH) * Y := by
    have h1 := QueeliusNappalDual.gradV_bound P LG LH L0 LOmj hA1 uk (u j) vk (v j)
    have h2 := hA1.2.1.2.2 vk (v j)
    have h3 := QueeliusNappalDual.adjoint_theta_bound P LG LH L0 LOmj hA1 uk (u j)
    rw [norm_sub_rev uk, norm_sub_rev vk] at h1
    rw [norm_sub_rev uk] at h3
    rw [norm_sub_rev vk] at h2
    have h4 : ‖tB‖ ≤ γ * (‖P.B‖ * L0 * X) := by
      rw [htB, norm_smul, Real.norm_of_nonneg hγ.le]; exact mul_le_mul_of_nonneg_left h3 hγ.le
    have hsplit : gk - g1 = (gradV P uk vk - gradV P (u j) (v j)) + (gradient P.H vk - gradient P.H (v j)) := by
      rw [hgk, hg1]; abel
    have := norm_add_le (gk - g1) tB
    have := norm_add_le (gradV P uk vk - gradV P (u j) (v j)) (gradient P.H vk - gradient P.H (v j))
    rw [← hsplit] at this
    rw [he]
    nlinarith
  -- F bound
  have hF : F P uk (-z0) ≤ F P uk vk + ⟪p (j+1), r⟫_ℝ + ‖e‖ * ‖z‖ + (LG + LH) / 2 * ‖z‖ ^ 2 := by
    have hez : -⟪e, z⟫_ℝ ≤ ‖e‖ * ‖z‖ := by
      have := abs_real_inner_le_norm e z; linarith [neg_abs_le ⟪e, z⟫_ℝ]
    have hgv : ⟪gradV P uk vk, -z⟫_ℝ + ⟪gradient P.H vk, -z⟫_ℝ = -⟪gk, z⟫_ℝ := by
      rw [hgk, inner_add_left, inner_neg_right, inner_neg_right]; ring
    unfold F
    linarith
  -- Λ
  have hpj : p (j+1) = p j + γ • r := (hrun.2.2.2 j).2.2.2
  have hpd : ‖p j - p (j+1)‖ = γ * ‖r‖ := by
    rw [hpj, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hγ.le]
  have hLam : Lam P LG LH L0 γ u v p (j+1) = augLag P γ (uk, vk, p (j+1)) +
      c1 P LG L0 γ * X ^ 2 + c2 P LG LH γ * Y ^ 2 + 1 / (2 * γ) * (γ * ‖r‖) ^ 2 := by
    unfold Lam; rw [Nat.add_sub_cancel, ← hpd]; rfl
  have hAL : augLag P γ (uk, vk, p (j+1)) = F P uk vk + ⟪p (j+1), r⟫_ℝ + γ / 2 * ‖r‖ ^ 2 := rfl
  rw [hLam, hAL]
  -- the quadratic inequality
  set α := LG + γ * ‖P.B‖ * L0
  set bb := LG + LH
  have hα : 0 ≤ α := by positivity
  have hbb : 0 ≤ bb := by positivity
  set Z := ‖z‖
  set R := ‖r‖
  have hZ : 0 ≤ Z := norm_nonneg _
  have hX : 0 ≤ X := norm_nonneg _
  have hY : 0 ≤ Y := norm_nonneg _
  set t := γ * lamMin P with ht
  have ht0 : 0 < t := mul_pos hγ hlam
  have hc1 : c1 P LG L0 γ = 7 * α ^ 2 / t := rfl
  have hc2 : c2 P LG LH γ = 7 * bb ^ 2 / t := rfl
  -- β < γ λ
  have hbt : bb ≤ t := by
    have h := hA2.2.2.2.2.2
    have h57 : (1 : ℝ) ≤ Real.sqrt 57 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)] at h
    have h2 := mul_le_mul_of_nonneg_right (show (2:ℝ) ≤ Real.sqrt 57 + 1 by linarith) hbb
    have h3 : γ * (2 * lamMin P) = 2 * t := by rw [ht]; ring
    linarith
  clear_value t Z R α bb X Y
  have hq1 : t * (α * X * Z) ≤ 7 * α ^ 2 * X ^ 2 + t ^ 2 * Z ^ 2 / 28 := by
    have h := sq_nonneg (14 * α * X - t * Z)
    have : (14 * α * X - t * Z) ^ 2 = 196 * α ^ 2 * X ^ 2 - 28 * (t * (α * X * Z)) + t ^ 2 * Z ^ 2 := by ring
    linarith
  have hq2 : t * (bb * Y * Z) ≤ 7 * bb ^ 2 * Y ^ 2 + t ^ 2 * Z ^ 2 / 28 := by
    have h := sq_nonneg (14 * bb * Y - t * Z)
    have : (14 * bb * Y - t * Z) ^ 2 = 196 * bb ^ 2 * Y ^ 2 - 28 * (t * (bb * Y * Z)) + t ^ 2 * Z ^ 2 := by ring
    linarith
  have hRZ : t * Z ^ 2 ≤ γ * R ^ 2 := by
    rw [ht, mul_assoc]; exact mul_le_mul_of_nonneg_left hray hγ.le
  have hkey : t * ((α * X + bb * Y) * Z + bb / 2 * Z ^ 2) ≤
      t * (7 * α ^ 2 / t * X ^ 2 + 7 * bb ^ 2 / t * Y ^ 2 + γ * R ^ 2) := by
    have e1 : t * (7 * α ^ 2 / t * X ^ 2 + 7 * bb ^ 2 / t * Y ^ 2 + γ * R ^ 2) =
        7 * α ^ 2 * X ^ 2 + 7 * bb ^ 2 * Y ^ 2 + t * (γ * R ^ 2) := by field_simp
    rw [e1]
    have hz2 : 0 ≤ Z ^ 2 := sq_nonneg Z
    have h5 : t * (bb / 2 * Z ^ 2) ≤ t * (t / 2 * Z ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hz2) ht0.le
    have h6 : t * (t * Z ^ 2) ≤ t * (γ * R ^ 2) := mul_le_mul_of_nonneg_left hRZ ht0.le
    have h7 : 0 ≤ t ^ 2 * Z ^ 2 := by positivity
    have e2 : t * ((α * X + bb * Y) * Z + bb / 2 * Z ^ 2) = t * (α * X * Z) + t * (bb * Y * Z) +
      t * (bb / 2 * Z ^ 2) := by ring
    have e3 : t * (t / 2 * Z ^ 2) = t ^ 2 * Z ^ 2 / 2 := by ring
    have e4 : t * (t * Z ^ 2) = t ^ 2 * Z ^ 2 := by ring
    linarith
  have hkey' := le_of_mul_le_mul_left hkey ht0
  have hmul : ‖e‖ * Z ≤ (α * X + bb * Y) * Z := mul_le_mul_of_nonneg_right heb hZ
  rw [hc1, hc2]
  have hγR : 1 / (2 * γ) * (γ * R) ^ 2 = γ / 2 * R ^ 2 := by field_simp
  rw [hγR]
  linarith

end NASol

namespace NASol

theorem le_of_sq_le (x M : ℝ) (h : x ^ 2 ≤ M) : x ≤ (1 + M) / 2 := by
  nlinarith [sq_nonneg (x - 1)]

theorem q_bounded {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → E n) (v : ℕ → E d) (p : ℕ → E m)
    (hR : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ k, ‖qseq P γ u v p k‖ ≤ Q := by
  obtain ⟨hc4, hdesc⟩ := NAPPAL.Rate.lemma_4_3 P LG LH L0 LK β γ σ LOmj K δ ε u v p hR
  obtain ⟨hA1, hA2, hrun, _⟩ := hR
  have hγ : 0 < γ := hrun.1
  have hLG : 0 ≤ LG := hA1.1.2.1
  have hLH : 0 ≤ LH := hA1.2.1.2.1
  have hL0 : 0 ≤ L0 := hA1.2.2.2.1.2.2.1
  have hlam := lamMin_pos P LG LH L0 LOmj hA1
  have hBn : 0 ≤ ‖P.B‖ := norm_nonneg _
  have hc3 : 0 < c3 P LG LH γ := by
    unfold c3; apply lt_min (by norm_num) (lt_min hc4 (by positivity))
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℕ → ℝ, Λ = Lam P LG LH L0 γ u v p := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun k => wdist (u k, v k, p k) (u (k+1), v (k+1), p (k+1)) :=
    ⟨_, rfl⟩
  have hb0 : ∀ k, 0 ≤ b k := fun k => by rw [hb]; exact Real.sqrt_nonneg _
  have hcomp : ∀ k, ‖u k - u (k+1)‖ ≤ b k ∧ ‖v k - v (k+1)‖ ≤ b k ∧ ‖p k - p (k+1)‖ ≤ b k :=
    fun k => by
      rw [hb]
      exact ⟨fst_le ((u k, v k, p k) - (u (k+1), v (k+1), p (k+1)) : W n d m),
        snd_le ((u k, v k, p k) - (u (k+1), v (k+1), p (k+1)) : W n d m),
        thd_le ((u k, v k, p k) - (u (k+1), v (k+1), p (k+1)) : W n d m)⟩
  have hd' : ∀ k, 1 ≤ k → Λ (k+1) - Λ k ≤ -c3 P LG LH γ * b k ^ 2 := fun k hk => by
    rw [hb, hΛ]; exact hdesc k hk
  clear hdesc
  -- monotone
  have hmono : ∀ j, Λ (j+1) ≤ Λ 1 := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih =>
      have := hd' (j+1) (by omega)
      have : 0 ≤ c3 P LG LH γ * b (j+1) ^ 2 := by have := hc3.le; positivity
      linarith
  obtain ⟨clow, hclow⟩ := hA1.2.2.2.2.2.2.1
  obtain ⟨Rb, hRb⟩ := isBounded_iff_forall_norm_le.mp (hA1.2.2.2.2.2.2.2 (Λ 1))
  have hlow : ∀ j, ∃ vt : E d, Theta P (u (j+1)) + P.B vt = 0 ∧
      lamMin P * ‖v (j+1) - vt‖ ^ 2 ≤ ‖Theta P (u (j+1)) + P.B (v (j+1))‖ ^ 2 ∧
      clow ≤ Λ (j+1) ∧ ‖u (j+1)‖ ≤ Rb ∧ ‖vt‖ ≤ Rb := by
    intro j
    obtain ⟨vt, h1, h2, h3⟩ := lower_step P LG LH L0 LOmj LK K β γ σ δ ε u v p hA1 hA2 hrun j
    have hmem : ((u (j+1), vt) : E n × E d) ∈
        {x : E n × E d | Theta P x.1 + P.B x.2 = 0 ∧ F P x.1 x.2 ≤ Λ 1} :=
      ⟨h1, h3.trans (by rw [← hΛ]; exact hmono j)⟩
    have hn := hRb _ hmem
    rw [← hΛ] at h3
    exact ⟨vt, h1, h2, (hclow _ _ h1).trans h3, (norm_fst_le _).trans hn, (norm_snd_le _).trans hn⟩
  -- step bound
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = max ((Λ 1 - clow) / c3 P LG LH γ) (b 0 ^ 2) := ⟨_, rfl⟩
  have hbM : ∀ k, b k ^ 2 ≤ Mb := by
    intro k
    rw [hMb]
    rcases k with _ | j
    · exact le_max_right _ _
    · apply le_max_of_le_left
      rw [le_div_iff₀ hc3]
      have h1 := hd' (j+1) (by omega)
      have h2 := hmono j
      obtain ⟨_, _, _, h3, _, _⟩ := hlow (j+1)
      have : b (j+1) ^ 2 * c3 P LG LH γ = c3 P LG LH γ * b (j+1) ^ 2 := by ring
      linarith
  have hMb0 : 0 ≤ Mb := by rw [hMb]; exact le_trans (sq_nonneg _) (le_max_right _ _)
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = (1 + Mb) / 2 := ⟨_, rfl⟩
  have hbs : ∀ k, b k ≤ Bs := fun k => by rw [hBs]; exact le_of_sq_le _ _ (hbM k)
  have hBs0 : 0 ≤ Bs := (hb0 0).trans (hbs 0)
  have hdu : ∀ k, ‖u k - u (k+1)‖ ≤ Bs := fun k => (hcomp k).1.trans (hbs k)
  have hdv : ∀ k, ‖v k - v (k+1)‖ ≤ Bs := fun k => (hcomp k).2.1.trans (hbs k)
  have hdp : ∀ k, ‖p k - p (k+1)‖ ≤ Bs := fun k => (hcomp k).2.2.trans (hbs k)
  -- residual
  have hres : ∀ j, ‖Theta P (u (j+1)) + P.B (v (j+1))‖ ≤ Bs / γ := by
    intro j
    have hpj : p (j+1) = p j + γ • (Theta P (u (j+1)) + P.B (v (j+1))) := (hrun.2.2.2 j).2.2.2
    have : ‖p j - p (j+1)‖ = γ * ‖Theta P (u (j+1)) + P.B (v (j+1))‖ := by
      rw [hpj, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hγ.le]
    rw [le_div_iff₀ hγ, mul_comm, ← this]; exact hdp j
  -- v bound
  obtain ⟨Rv, hRv⟩ : ∃ Rv : ℝ, Rv = Rb + (1 + (Bs / γ) ^ 2 / lamMin P) / 2 := ⟨_, rfl⟩
  have hvb : ∀ j, ‖v (j+1)‖ ≤ Rv := by
    intro j
    obtain ⟨vt, _, h2, _, _, h5⟩ := hlow j
    have hr := hres j
    have h6 : ‖v (j+1) - vt‖ ^ 2 ≤ (Bs / γ) ^ 2 / lamMin P := by
      rw [le_div_iff₀ hlam]
      have := pow_le_pow_left₀ (norm_nonneg _) hr 2
      linarith
    have h7 := le_of_sq_le _ _ h6
    have h8 : ‖v (j+1)‖ ≤ ‖v (j+1) - vt‖ + ‖vt‖ := by
      have := norm_add_le (v (j+1) - vt) vt; rwa [sub_add_cancel] at this
    linarith
  have hub : ∀ j, ‖u (j+1)‖ ≤ Rb := fun j => by obtain ⟨_, _, _, _, h4, _⟩ := hlow j; exact h4
  -- B^T p bound for k ≥ 2
  obtain ⟨CB, hCB⟩ : ∃ CB : ℝ, CB = (‖gradV P 0 0‖ + LG * (Rb + Rv)) + (‖gradient P.H 0‖ + LH * Rv) +
    γ * (‖P.B‖ * L0 * Bs) := ⟨_, rfl⟩
  have hBp : ∀ j, ‖ContinuousLinearMap.adjoint P.B (p (j+2))‖ ≤ CB := by
    intro j
    have hd := QueeliusNappalDual.dual_identity P K γ σ δ ε u v p hrun (j+1)
    rw [hd]
    have h1 := QueeliusNappalDual.gradV_bound P LG LH L0 LOmj hA1 (u (j+1)) 0 (v (j+1)) 0
    have h2 := hA1.2.1.2.2 (v (j+1)) 0
    have h3 := QueeliusNappalDual.adjoint_theta_bound P LG LH L0 LOmj hA1 (u (j+2)) (u (j+1))
    simp only [sub_zero] at h1 h2
    have g1 : ‖gradV P (u (j+1)) (v (j+1))‖ ≤ ‖gradV P 0 0‖ + LG * (Rb + Rv) := by
      have := norm_le_insert' (gradV P (u (j+1)) (v (j+1))) (gradV P 0 0)
      have := mul_le_mul_of_nonneg_left (add_le_add (hub j) (hvb j)) hLG
      linarith
    have g2 : ‖gradient P.H (v (j+1))‖ ≤ ‖gradient P.H 0‖ + LH * Rv := by
      have := norm_le_insert' (gradient P.H (v (j+1))) (gradient P.H 0)
      have := mul_le_mul_of_nonneg_left (hvb j) hLH
      linarith
    have g3 : ‖γ • ContinuousLinearMap.adjoint P.B (Theta P (u (j+2)) - Theta P (u (j+1)))‖ ≤
        γ * (‖P.B‖ * L0 * Bs) := by
      rw [norm_smul, Real.norm_of_nonneg hγ.le]
      apply mul_le_mul_of_nonneg_left _ hγ.le
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [norm_sub_rev]; exact hdu (j+1)
    have t1 := norm_add_le (-gradV P (u (j+1)) (v (j+1)) - gradient P.H (v (j+1)))
      (γ • ContinuousLinearMap.adjoint P.B (Theta P (u (j+2)) - Theta P (u (j+1))))
    have t2 := norm_sub_le (-gradV P (u (j+1)) (v (j+1))) (gradient P.H (v (j+1)))
    rw [norm_neg] at t2
    rw [hCB]; linarith
  -- range
  have hrange : ∀ k, ∃ x : E d, p k - p 0 = P.B x := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨z, hz⟩ := hA1.2.2.2.2.2.1.1 (Set.mem_range_self (u (k+1)))
      refine ⟨x + γ • (z + v (k+1)), ?_⟩
      rw [(hrun.2.2.2 k).2.2.2, map_add, ← hx, map_smul, map_add, hz]
      abel
  obtain ⟨Rp, hRp⟩ : ∃ Rp : ℝ, Rp = ‖p 2‖ + (1 + (2 * CB) ^ 2 / lamMin P) / 2 := ⟨_, rfl⟩
  have hpb : ∀ j, ‖p (j+2)‖ ≤ Rp := by
    intro j
    obtain ⟨x1, hx1⟩ := hrange (j+2)
    obtain ⟨x2, hx2⟩ := hrange 2
    have hmem : p (j+2) - p 2 ∈ Set.range P.B := ⟨x1 - x2, by rw [map_sub, ← hx1, ← hx2]; abel⟩
    have hl := QueeliusNappalDual.adjoint_range_bound P hlam.le _ hmem
    have hn : ‖ContinuousLinearMap.adjoint P.B (p (j+2) - p 2)‖ ≤ 2 * CB := by
      rw [map_sub]
      have := norm_sub_le (ContinuousLinearMap.adjoint P.B (p (j+2))) (ContinuousLinearMap.adjoint P.B (p 2))
      have := hBp j
      have := hBp 0
      linarith
    have h6 : ‖p (j+2) - p 2‖ ^ 2 ≤ (2 * CB) ^ 2 / lamMin P := by
      rw [le_div_iff₀ hlam]
      have := pow_le_pow_left₀ (norm_nonneg _) hn 2
      linarith
    have h7 := le_of_sq_le _ _ h6
    have h8 : ‖p (j+2)‖ ≤ ‖p (j+2) - p 2‖ + ‖p 2‖ := by
      have := norm_add_le (p (j+2) - p 2) (p 2); rwa [sub_add_cancel] at this
    linarith
  refine ⟨max (max ‖qseq P γ u v p 0‖ ‖qseq P γ u v p 1‖) (Rp + Bs), le_max_of_le_left
    (le_max_of_le_left (norm_nonneg _)), ?_⟩
  intro k
  rcases k with _ | _ | j
  · exact le_max_of_le_left (le_max_left _ _)
  · exact le_max_of_le_left (le_max_right _ _)
  · apply le_max_of_le_right
    have h1 := hpb j
    have h2 := hres (j+1)
    have h3 : ‖γ • (Theta P (u (j+2)) + P.B (v (j+2)))‖ ≤ Bs := by
      rw [norm_smul, Real.norm_of_nonneg hγ.le]
      rw [le_div_iff₀ hγ] at h2; linarith
    have := norm_add_le (p (j+2)) (γ • (Theta P (u (j+2)) + P.B (v (j+2))))
    unfold qseq
    linarith

end NASol

open NAPPAL.Rate (qseq)
open NAPPAL.KL (wseq)

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : NAPPAL.KL.E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Subreg.RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p) :
    ∃ c6 : ℝ, 0 < c6 ∧ ∀ wbar : NAPPAL.KL.W n d m, NAPPAL.KL.IsStationary P γ wbar → ∀ k : ℕ,
      NAPPAL.KL.augLag P γ (wseq u v p (k+1)) - NAPPAL.KL.augLag P γ wbar ≤
        c6 * (NAPPAL.KL.wdist wbar (wseq u v p (k+1)) ^ 2 +
          NAPPAL.KL.wdist (wseq u v p k) (wseq u v p (k+1)) ^ 2) := by
  obtain ⟨hA1, hA2, hrun', hδ⟩ := hrun
  have hR : NAPPAL.Rate.RunHyp P LG LH L0 LOmj K β LK γ σ δ ε u v p :=
    ⟨hA1, hA2, NASol.toRate P K γ σ δ ε u v p hrun', hδ⟩
  obtain ⟨Q, hQ0, hQ⟩ := NASol.q_bounded P LG LH L0 LOmj LK K β γ σ δ ε u v p hR
  exact NASol.main_est P LG LH L0 LOmj LK K β γ σ δ ε u v p hA1 hA2 hR.2.2.1 hδ Q hQ0 hQ

