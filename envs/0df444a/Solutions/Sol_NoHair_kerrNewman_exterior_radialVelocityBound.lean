-- Prove2me | solution 1 for NoHair.kerrNewman_exterior_radialVelocityBound
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:44:38.630022+00:00
-- url     : https://prove2.me/submissions/f02357e8-78e7-4e02-bd68-8dbf3b8195b4

import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms

open NoHair NoHair.KNE Set
open scoped BigOperators Manifold ContDiff

noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev G (m a e : ℝ) := kerrNewmanMetricField m a e
private abbrev I4 := 𝓘(ℝ,E4)
private abbrev V3 := Fin 3 → ℝ
private def dot3 (v w : V3) := ∑ i, v i*w i
private def space (v : E4) : V3 := ![v 1,v 2,v 3]
private def axis (a : ℝ) (y : E4) : V3 := ![ksNull a y 1,ksNull a y 2,ksNull a y 3]
private def timeC (v : E4) := v 0

private theorem dot_symm (u v : V3) : dot3 u v = dot3 v u := by simp [dot3, mul_comm]
private theorem dot_add_l (u v w : V3) : dot3 (u+v) w = dot3 u w + dot3 v w := by
  simp [dot3, add_mul, Finset.sum_add_distrib]
private theorem dot_add_r (u v w : V3) : dot3 u (v+w) = dot3 u v + dot3 u w := by
  simp [dot3, mul_add, Finset.sum_add_distrib]
private theorem dot_scale_l (c : ℝ) (u v : V3) : dot3 (c • u) v = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_assoc]
private theorem dot_scale_r (c : ℝ) (u v : V3) : dot3 u (c • v) = c*dot3 u v := by
  simp [dot3, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc]
private theorem dot_cauchy (u v : V3) : (dot3 u v)^2 ≤ dot3 u u * dot3 v v := by
  simpa only [dot3, sq] using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) u v
private theorem axis_unit (a : ℝ) (x : U a) : dot3 (axis a x.val) (axis a x.val) = 1 := by
  simpa [dot3, axis, Fin.sum_univ_three, sq] using ks_rel a x.val x.property

private theorem metric_formula (m a e : ℝ) (x : U a) (v w : E4) :
    G m a e x v w = -(timeC v*timeC w) + dot3 (space v) (space w) +
      ksProfile m a e x.val * (timeC v + dot3 (axis a x.val) (space v)) *
        (timeC w + dot3 (axis a x.val) (space w)) := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a e x.val) (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul, kerrNewmanMetric, Fin.sum_univ_four, ksNull_zero]
  simp [minkowski, dot3, space, timeC, axis, Fin.sum_univ_three] <;> ring

private def radialNormal (a : ℝ) (y : E4) : V3 :=
  let r := ksRadius a y
  let k := axis a y
  let W := Wf a y
  ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]

private theorem normal_geometry (a : ℝ) (x : U a) :
    dot3 (radialNormal a x.val) (axis a x.val) = 1 ∧
    dot3 (radialNormal a x.val) (radialNormal a x.val) = (ksRadius a x.val^2 + a^2)*Wf a x.val := by
  let r := ksRadius a x.val
  let k := axis a x.val
  let W := Wf a x.val
  have hrel : k 0^2+k 1^2+k 2^2=1 := ks_rel a x.val x.property
  have hW : W*(r^2+a^2*k 2^2)=1 := ks_W a x.val x.property
  let n : V3 := ![r^2*k 0*W-r*k 1*W*a, r^2*k 1*W+r*k 0*W*a, (r^2+a^2)*k 2*W]
  change dot3 n k = 1 ∧ dot3 n n = (r^2+a^2)*W
  constructor
  · calc
      dot3 n k = W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2) := by simp [dot3, n, Fin.sum_univ_three]; ring
      _ = 1 := by rw [hrel, mul_one, hW]
  · calc
      dot3 n n = (r^2+a^2)*W*(W*(r^2*(k 0^2+k 1^2+k 2^2)+a^2*k 2^2)) := by
        simp [dot3, n, Fin.sum_univ_three]; ring
      _ = (r^2+a^2)*W := by rw [hrel, mul_one, hW, mul_one]

private theorem radial_derivative (a : ℝ) (x : U a) (v : E4) :
    fderiv ℝ (ksRadius a) x.val v = dot3 (radialNormal a x.val) (space v) := by
  have hv : ∑ i, v i • coordBasis i = v := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four, coordBasis]
  have cp (i : Fin 4) := (hasCP_R a x.val x.property).eq i
  change ∀ (i : Fin 4), fderiv ℝ (ksRadius a) x.val (coordBasis i) = _ at cp
  calc
    _ = fderiv ℝ (ksRadius a) x.val (∑ i, v i • coordBasis i) := congrArg _ hv.symm
    _ = _ := by
      simp only [Fin.sum_univ_four, map_add, map_smul, smul_eq_mul]
      erw [cp 0, cp 1, cp 2, cp 3]
      simp [dot3, radialNormal, space, axis, dRt, Fin.sum_univ_three] <;> ring


private theorem radial_cone_bound (k n s : V3) (f t q : ℝ) (hk : dot3 k k = 1)
    (hnk : dot3 n k = 1) (hn : dot3 n n ≤ f+f*q) (hf : 0 ≤ f) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hv : -t*t + dot3 s s + f*(t+dot3 k s)*(t+dot3 k s) ≤ 0) : dot3 n s ≤ q*t := by
  let c := f/2
  let l := t+dot3 k s
  let τ := t-c*l
  let u := s+(c*l) • k
  let b := n+(-c) • k
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have ff : f=2*c := by dsimp [c]; ring
  have hks := dot_cauchy k s
  rw [hk,one_mul] at hks
  have hspeed : dot3 s s ≤ t^2 := by
    nlinarith only [hv, mul_nonneg hf (sq_nonneg (t+dot3 k s))]
  have habs : |dot3 k s| ≤ t := by
    apply (sq_le_sq₀ (abs_nonneg _) ht).mp
    rw [sq_abs]; exact hks.trans hspeed
  have hl : 0 ≤ l := by dsimp [l]; linarith [neg_abs_le (dot3 k s)]
  have hτ : 0 ≤ τ := by
    by_cases he : l=0
    · simpa [τ,he] using ht
    · have h1 : f*l*l ≤ (t-dot3 k s)*l := by
        dsimp [l]; nlinarith only [hv,hks]
      have h2 := le_of_mul_le_mul_right h1 (lt_of_le_of_ne hl (Ne.symm he))
      dsimp [τ,c,l] at h2 ⊢
      dsimp [l] at hl
      linarith
  have hτt : τ ≤ t := by dsimp only [τ]; linarith only [mul_nonneg hc hl]
  have hu : dot3 u u ≤ τ^2 := by
    have hh : dot3 u u-τ^2 = -t*t+dot3 s s+f*l*l := by
      simp only [u,τ,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hk,dot_symm s k]
      rw [ff]; ring
    change -t*t+dot3 s s+f*l*l ≤ 0 at hv
    linarith only [hh,hv]
  have hb : dot3 b b ≤ (c+q)^2 := by
    simp only [b,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hk,hnk,dot_symm k n]
    rw [ff] at hn
    nlinarith only [hn,sq_nonneg q]
  have he : dot3 n s = dot3 b u - c*τ := by
    simp only [b,u,τ,l,dot_add_l,dot_add_r,dot_scale_l,dot_scale_r,hnk,hk]
    ring
  have hnorm : 0 ≤ dot3 u u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  have hcq : 0 ≤ c+q := add_nonneg hc hq
  have hbound : |dot3 b u| ≤ (c+q)*τ := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hcq hτ)).mp
    rw [sq_abs,mul_pow]
    exact (dot_cauchy b u).trans (mul_le_mul hb hu hnorm (sq_nonneg _))
  rw [he]
  nlinarith only [le_abs_self (dot3 b u),hbound,mul_le_mul_of_nonneg_left hτt hq]

theorem solution (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e) (x : kerrNewmanSpacetime a)
    (hx : kerrNewmanOuterRadius m a e < ksRadius a x.val) (v : E4)
    (ht : 0 ≤ v 0) (hv : kerrNewmanMetricField m a e x v v ≤ 0) :
    m * fderiv ℝ (ksRadius a) x.val v ≤ (ksRadius a x.val - kerrNewmanOuterRadius m a e) * v 0 := by
  let r := ksRadius a x.val
  let b := kerrNewmanOuterRadius m a e
  let d := Real.sqrt (m^2-a^2-e^2)
  let q := (r-b)/m
  let H := 2*m*r-e^2
  let W := Wf a x.val
  have hm := hp.1
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hx.le) hm.le
  have hq_eq : m*q = r-b := by dsimp [q]; field_simp
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = m^2-a^2-e^2 := Real.sq_sqrt (by linarith [hp.2])
  have hbm : 0 ≤ m-d := by
    have hle : d ≤ m := (sq_le_sq₀ hd hm.le).mp (by nlinarith only [hd2,sq_nonneg a,sq_nonneg e])
    linarith
  have hb : b=m+d := rfl
  have hmr : m ≤ r := by change b<r at hx; linarith
  have he2 : e^2 ≤ m^2 := by linarith [hp.2,sq_nonneg a]
  have hH : 0 ≤ H := by dsimp [H]; nlinarith only [mul_le_mul_of_nonneg_left hmr hm.le,he2,sq_nonneg m]
  have hΔ : r^2+a^2-H=(r-b)*(r-(m-d)) := by dsimp [H]; rw [hb]; nlinarith only [hd2]
  have hlin : m*(r-(m-d)) ≤ H := by
    dsimp [H]; nlinarith only [mul_le_mul_of_nonneg_left hmr hm.le,mul_nonneg hm.le hbm,he2]
  have hpoly : r^2+a^2 ≤ H+H*q := by
    have hgap : 0 ≤ r-b := sub_nonneg.mpr hx.le
    have hmul := mul_le_mul_of_nonneg_left hlin hgap
    have fact : m*(r^2+a^2-H) ≤ m*(H*q) := by
      calc
        _ = (r-b)*(m*(r-(m-d))) := by rw [hΔ]; ring
        _ ≤ (r-b)*H := hmul
        _ = m*(H*q) := by rw [← hq_eq]; ring
    linarith only [le_of_mul_le_mul_left fact hm]
  have hW : 0 ≤ W := by dsimp [W,Wf]; positivity
  have hf : ksProfile m a e x.val = H*W := profile_eq m a e x.val x.property
  obtain ⟨hnk,hn⟩ := normal_geometry a x
  have hnn : dot3 (radialNormal a x.val) (radialNormal a x.val) ≤
      ksProfile m a e x.val + ksProfile m a e x.val*q := by
    rw [hn,hf]
    change (r^2+a^2)*W ≤ H*W+H*W*q
    nlinarith only [mul_le_mul_of_nonneg_right hpoly hW]
  erw [metric_formula m a e x v v] at hv
  have h := radial_cone_bound (axis a x.val) (radialNormal a x.val) (space v) (ksProfile m a e x.val)
    (v 0) q (axis_unit a x) hnk hnn (hf ▸ mul_nonneg hH hW) ht hq (by simpa [timeC,neg_mul] using hv)
  rw [radial_derivative]
  calc
    _ ≤ m*(q*v 0) := mul_le_mul_of_nonneg_left h hm.le
    _ = (r-b)*v 0 := by rw [← mul_assoc,hq_eq]
