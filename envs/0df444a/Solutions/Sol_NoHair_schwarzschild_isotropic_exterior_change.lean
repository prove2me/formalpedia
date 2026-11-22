-- Prove2me | solution 1 for NoHair.schwarzschild_isotropic_exterior_change
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:37:57.454829+00:00
-- url     : https://prove2.me/submissions/fc92b88a-5b31-45ef-8cb3-4b5d74f693cf

import Definitions.Def_NoHair_conformalVacuumExterior
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair Set Filter Topology
open scoped ContDiff Manifold

noncomputable section

private abbrev rad (x : E4) : ℝ := ‖conformalSpatialPoint x‖
private def dotS (x y : E4) : ℝ := x 1 * y 1 + x 2 * y 2 + x 3 * y 3
private def pack (t c : ℝ) (x : E4) : E4 := WithLp.toLp 2 ![t, c * x 1, c * x 2, c * x 3]
private def root (b r : ℝ) := Real.sqrt (1 - 4 * b / r)
private def scale (s : ℝ) := (1 + s) ^ 2 / 4
private def factor (b p : ℝ) := 1 + b / p
private def areal (b p : ℝ) := factor b p ^ 2 * p
private def fromKS (b : ℝ) (x : E4) :=
  pack (x 0 - 4 * b * Real.log (rad x - 4 * b)) (scale (root b (rad x))) x
private def toKS (b : ℝ) (x : E4) :=
  pack (x 0 + 4 * b * Real.log (areal b (rad x) - 4 * b)) (factor b (rad x) ^ 2) x

private lemma four (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> decide

private lemma pack_radius (t c : ℝ) (x : E4) : rad (pack t c x) = |c| * rad x := by
  have v : conformalSpatialPoint (pack t c x) = c • conformalSpatialPoint x := by
    ext i
    fin_cases i <;> rfl
  simp only [rad, v, norm_smul, Real.norm_eq_abs]

private lemma pack_comp (t c T C : ℝ) (x : E4) :
    pack t c (pack T C x) = pack t (c * C) x := by
  ext i
  rcases four i with rfl | rfl | rfl | rfl <;>
    simp [pack, Matrix.cons_val, mul_assoc]

private lemma pack_self (x : E4) : pack (x 0) 1 x = x := by
  ext i
  rcases four i with rfl | rfl | rfl | rfl <;> simp [pack, Matrix.cons_val]

private lemma rad_sq (x : E4) : rad x ^ 2 = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := by
  rw [rad, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  rfl

private lemma ks_rad (x : E4) : ksRadius 0 x = rad x := by
  simp only [ksRadius, ← rad_sq x, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_zero, zero_mul,
    add_zero, Real.sqrt_sq (sq_nonneg (rad x))]
  rw [show (rad x ^ 2 + rad x ^ 2) / 2 = rad x ^ 2 by ring, Real.sqrt_sq (norm_nonneg _)]

private lemma sourceSet {b : ℝ} (hb : 0 < b) :
    kerrNewmanDOC (2 * b) 0 0 = {y | 4 * b < rad y} := by
  have hm : 0 < 2 * b := by positivity
  ext y
  simp only [kerrNewmanDOC, mem_setOf_eq, kerrNewmanOuterRadius, zero_pow (by decide : 2 ≠ 0),
    sub_zero, Real.sqrt_sq hm.le, ks_rad]
  constructor <;> intro h <;> linarith

private lemma targetSet {b : ℝ} (hb : 0 < b) :
    conformalExteriorDomain (fun x => 1 + b / ‖x‖) = {y | b < rad y} := by
  ext y
  change (conformalSpatialPoint y ≠ 0 ∧ 1 + b / rad y < 2) ↔ b < rad y
  constructor
  · rintro ⟨hn, hl⟩
    exact (div_lt_one (norm_pos_iff.mpr hn)).mp (by linarith)
  · intro h
    exact ⟨norm_pos_iff.mp (hb.trans h), by linarith only [(div_lt_one (hb.trans h)).mpr h]⟩

private lemma root_data {b r : ℝ} (hb : 0 < b) (hr : 4 * b < r) :
    0 < root b r ∧ 4 * b = r * (1 - root b r ^ 2) := by
  have rp : 0 < r := by linarith
  have hp : 0 < 1 - 4 * b / r := sub_pos.mpr ((div_lt_one rp).mpr hr)
  refine ⟨Real.sqrt_pos.2 hp, ?_⟩
  rw [root, Real.sq_sqrt hp.le]
  field_simp [rp.ne']
  <;> ring

private lemma outward {b p : ℝ} (hb : 0 < b) (hp : b < p) :
    4 * b < areal b p ∧ scale (root b (areal b p)) * factor b p ^ 2 = 1 := by
  have pp := hb.trans hp
  have pb : 0 < p + b := by positivity
  have u : factor b p = (p + b) / p := by dsimp [factor]; field_simp [pp.ne']
  have f : areal b p = (p + b) ^ 2 / p := by
    rw [areal, u]; field_simp [pp.ne'] <;> ring
  have diff : areal b p - 4 * b = (p - b) ^ 2 / p := by
    rw [f]; field_simp [pp.ne'] <;> ring
  have hs : 0 < (p - b) / (p + b) := div_pos (sub_pos.mpr hp) pb
  have sq : 1 - 4 * b / areal b p = ((p - b) / (p + b)) ^ 2 := by
    rw [f]
    field_simp [pp.ne', pb.ne'] <;> ring
  refine ⟨sub_pos.mp (by rw [diff]; exact div_pos (sq_pos_of_pos (sub_pos.mpr hp)) pp), ?_⟩
  rw [root, sq, Real.sqrt_sq hs.le, scale, u]
  field_simp [pb.ne', pp.ne'] <;> ring

private lemma inward_algebra {b r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (rel : 4 * b = r * (1 - s ^ 2)) :
    b < scale s * r ∧ factor b (scale s * r) = 2 / (1 + s) ∧
    factor b (scale s * r) ^ 2 * scale s = 1 := by
  have hb : b = r * (1 - s ^ 2) / 4 := by linarith
  subst b
  have h1 : 0 < 1 + s := by positivity
  have he : scale s * r - r * (1 - s ^ 2) / 4 = r * s * (1 + s) / 2 := by dsimp [scale]; ring
  have fac : factor (r * (1 - s ^ 2) / 4) (scale s * r) = 2 / (1 + s) := by
    dsimp [factor, scale]
    field_simp [hr.ne', h1.ne'] <;> ring
  refine ⟨sub_pos.mp (by rw [he]; positivity), fac, ?_⟩
  rw [fac, scale]
  field_simp [h1.ne'] <;> ring

private lemma smooth_rad {x : E4} (hx : 0 < rad x) : ContDiffAt ℝ ∞ rad x := by
  have hsp : ContDiff ℝ ∞ conformalSpatialPoint := by
    apply (contDiff_piLp 2).2
    intro i
    fin_cases i <;> change ContDiff ℝ ∞ (fun z : E4 => z _) <;> fun_prop
  exact (contDiffAt_norm ℝ (norm_pos_iff.mp hx)).comp x hsp.contDiffAt

private lemma smooth_pack {f g : E4 → ℝ} {x : E4} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) : ContDiffAt ℝ ∞ (fun z => pack (f z) (g z) z) x := by
  apply (contDiffAt_piLp 2).2
  intro i
  rcases four i with rfl | rfl | rfl | rfl
  · exact hf
  all_goals exact hg.mul (by fun_prop)

private lemma smooth_from {b : ℝ} {x : E4} (hb : 0 < b) (hx : 4 * b < rad x) :
    ContDiffAt ℝ ∞ (fromKS b) x := by
  have rp : 0 < rad x := by linarith
  have hrad := smooth_rad rp
  have hlog := (sub_pos.mpr hx).ne'
  have hrt := (sub_pos.mpr ((div_lt_one rp).mpr hx)).ne'
  apply smooth_pack
  · fun_prop (disch := assumption)
  · unfold scale root
    fun_prop (disch := first | assumption | exact rp.ne')

private lemma smooth_to {b : ℝ} {x : E4} (hb : 0 < b) (hx : b < rad x) :
    ContDiffAt ℝ ∞ (toKS b) x := by
  have rp := hb.trans hx
  have hrad := smooth_rad rp
  have hfac : ContDiffAt ℝ ∞ (fun z : E4 => factor b (rad z)) x := by
    unfold factor
    fun_prop (disch := exact rp.ne')
  have harea : ContDiffAt ℝ ∞ (fun z : E4 => areal b (rad z)) x := (hfac.pow 2).mul hrad
  have hlog := (sub_pos.mpr (outward hb hx).1).ne'
  apply smooth_pack
  · fun_prop (disch := assumption)
  · exact hfac.pow 2

private lemma chart {b : ℝ} (hb : 0 < b) : IsDiffeoOnto (fromKS b)
    {y | 4 * b < rad y} {z | b < rad z} := by
  have from_rad (x : E4) (hx : 4 * b < rad x) :
      rad (fromKS b x) = scale (root b (rad x)) * rad x := by
    rw [fromKS, pack_radius, abs_of_nonneg (by dsimp [scale]; positivity)]
  have to_rad (x : E4) : rad (toKS b x) = areal b (rad x) := by
    rw [toKS, pack_radius, abs_of_nonneg (sq_nonneg _)]
    rfl
  refine ⟨toKS b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change 4 * b < rad x at hx
    change b < rad (fromKS b x)
    rw [from_rad x hx]
    exact (inward_algebra (by linarith) (root_data hb hx).1 (root_data hb hx).2).1
  · intro x hx
    change 4 * b < rad (toKS b x)
    rw [to_rad]
    exact (outward hb hx).1
  · intro x hx
    change 4 * b < rad x at hx
    have facts := inward_algebra (by linarith : 0 < rad x) (root_data hb hx).1 (root_data hb hx).2
    have hu : factor b (rad (fromKS b x)) ^ 2 * scale (root b (rad x)) = 1 := by
      rw [from_rad x hx]; exact facts.2.2
    have hrad : areal b (rad (fromKS b x)) = rad x := by
      unfold areal
      nth_rw 2 [from_rad x hx]
      rw [← mul_assoc, hu, one_mul]
    change pack ((fromKS b x) 0 + 4 * b * Real.log (areal b (rad (fromKS b x)) - 4 * b))
      (factor b (rad (fromKS b x)) ^ 2) (fromKS b x) = x
    rw [hrad]
    change pack ((x 0 - 4 * b * Real.log (rad x - 4 * b)) + _)
      _ (pack _ (scale (root b (rad x))) x) = x
    rw [sub_add_cancel, pack_comp, hu, pack_self]
  · intro x hx
    change b < rad x at hx
    change pack ((toKS b x) 0 - 4 * b * Real.log (rad (toKS b x) - 4 * b))
      (scale (root b (rad (toKS b x)))) (toKS b x) = x
    rw [to_rad]
    change pack ((x 0 + 4 * b * Real.log (areal b (rad x) - 4 * b)) - _)
      _ (pack _ (factor b (rad x) ^ 2) x) = x
    rw [add_sub_cancel_right, pack_comp, (outward hb hx).2, pack_self]
  · exact contMDiffOn_iff_contDiffOn.mpr (fun x hx => (smooth_from hb hx).contDiffWithinAt)
  · exact contMDiffOn_iff_contDiffOn.mpr (fun x hx => (smooth_to hb hx).contDiffWithinAt)

private lemma scale_derivative {b r : ℝ} (hb : 0 < b) (hr : 4 * b < r) :
    HasDerivAt (fun t => scale (root b t))
      (scale (root b r) * ((1 / root b r - 1) / r)) r := by
  have rp : 0 < r := by linarith
  have h := ((hasDerivAt_const r (1 : ℝ)).fun_sub
    ((hasDerivAt_const r (4*b)).fun_div (hasDerivAt_id' r) rp.ne')).sqrt
      (sub_pos.mpr ((div_lt_one rp).mpr hr)).ne'
  apply (((h.const_add 1).fun_pow 2).div_const 4).congr_deriv
  obtain ⟨hs, he⟩ := root_data hb hr
  change (2 * (1 + root b r) ^ 1 * ((0 - (0 * r - 4*b*1) / r^2) / (2 * root b r))) / 4 = _
  generalize root b r = s at hs he ⊢
  rw [show b = r * (1 - s^2) / 4 by linarith only [he]]
  unfold scale
  field_simp [rp.ne', hs.ne'] <;> ring

private lemma radius_line (x v : E4) (hx : 0 < rad x) :
    HasDerivAt (fun t : ℝ => rad (x + t • v)) (dotS x v / rad x) 0 := by
  have h := hasDerivAt_ksRadius_line 0 x v ((ks_rad x).symm ▸ hx)
  simp only [ks_rad, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h
  apply h.congr_deriv
  dsimp only [dotS]
  field_simp [hx.ne'] <;> ring

private lemma coord_line (x v : E4) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => (x + t • v) i) (v i) 0 := by
  simpa only [line_apply] using hasDerivAt_line_coord x v i

private abbrev jac (H : E4 → E4) (x : E4) : E4 →L[ℝ] E4 :=
  mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) H x

private lemma differential_entry {H : E4 → E4} {x v : E4} {i : Fin 4} {a : ℝ}
    (hH : DifferentiableAt ℝ H x)
    (hd : HasDerivAt (fun t : ℝ => H (x + t • v) i) a 0) :
    (jac H x v) i = a := by
  unfold jac
  rw [mfderiv_eq_fderiv]
  have pg := (EuclideanSpace.proj i : E4 →L[ℝ] ℝ).hasFDerivAt.comp x hH.hasFDerivAt
  have ev := congrArg (fun L : E4 →L[ℝ] ℝ => L v) pg.fderiv
  have hcp := fderiv_eq_of_line pg.differentiableAt hd
  exact ev.symm.trans hcp

private lemma time_entry {b : ℝ} {x : E4} (hb : 0 < b) (hx : 4*b < rad x) (v : E4) :
    (jac (fromKS b) x v) 0 =
      v 0 - (4*b / (rad x-4*b)) * (dotS x v / rad x) := by
  have rp : 0 < rad x := by linarith
  have dl := ((radius_line x v rp).sub_const (4*b)).log (by
    simpa only [zero_smul, add_zero] using (sub_pos.mpr hx).ne')
  apply differential_entry (i := 0) (v := v) ((smooth_from hb hx).differentiableAt (by simp))
  apply ((coord_line x v 0).fun_sub (dl.const_mul (4*b))).congr_deriv
  simp only [zero_smul, add_zero]
  ring

private lemma spatial_entry {b : ℝ} {x : E4} (hb : 0 < b) (hx : 4*b < rad x)
    (v : E4) (i : Fin 4) (hi : i ≠ 0) :
    (jac (fromKS b) x v) i =
      scale (root b (rad x)) *
        (v i + (1 / root b (rad x) - 1) * (x i / rad x) * (dotS x v / rad x)) := by
  have rp : 0 < rad x := by linarith
  have hc := (scale_derivative hb hx).comp_of_eq 0 (radius_line x v rp) (by simp)
  have e (z : E4) : fromKS b z i = scale (root b (rad z)) * z i := by
    rcases four i with rfl | rfl | rfl | rfl
    · contradiction
    all_goals rfl
  apply differential_entry (i := i) (v := v) ((smooth_from hb hx).differentiableAt (by simp))
  simp only [e]
  apply (hc.fun_mul (coord_line x v i)).congr_deriv
  simp only [Function.comp_apply, zero_smul, add_zero]
  ring

private lemma basis_matrix (i j : Fin 4) : coordBasis i j =
    (!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ) i j := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;> rfl

private lemma flat_matrix (i j : Fin 4) : minkowski i j =
    (!![-1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ) i j := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;> rfl

private lemma v0 {α : Type*} (a b c d : α) : ![a,b,c,d] (0 : Fin 4) = a := rfl
private lemma v1 {α : Type*} (a b c d : α) : ![a,b,c,d] (1 : Fin 4) = b := rfl
private lemma v2 {α : Type*} (a b c d : α) : ![a,b,c,d] (2 : Fin 4) = c := rfl
private lemma v3 {α : Type*} (a b c d : α) : ![a,b,c,d] (3 : Fin 4) = d := rfl

private lemma flat_components (i j : Fin 4) :
    minkowski i j = -(coordBasis i 0) * coordBasis j 0 + dotS (coordBasis i) (coordBasis j) := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;>
    simp only [dotS, flat_matrix, basis_matrix, Matrix.of_apply, v0, v1, v2, v3] <;> norm_num

private lemma null_components (x : E4) (hx : 0 < rad x) (i : Fin 4) :
    ksNull 0 x i = coordBasis i 0 + dotS x (coordBasis i) / rad x := by
  rcases four i with rfl | rfl | rfl | rfl <;>
    simp only [ksNull, ks_rad, dotS, basis_matrix, Matrix.of_apply, v0, v1, v2, v3] <;>
    norm_num <;> field_simp [hx.ne'] <;> ring

private lemma spatial_product {r c t : ℝ} {x v w V W : E4} (hr : 0 < r)
    (hr2 : r^2 = x 1^2 + x 2^2 + x 3^2)
    (hv : ∀ i : Fin 4, i ≠ 0 → V i = c * (v i + t * (x i / r) * (dotS x v / r)))
    (hw : ∀ i : Fin 4, i ≠ 0 → W i = c * (w i + t * (x i / r) * (dotS x w / r))) :
    dotS V W = c^2 * (dotS v w + (2*t+t^2) * (dotS x v / r) * (dotS x w / r)) := by
  let n (i : Fin 4) := x i / r
  let d (a : E4) := dotS x a / r
  have nd (a : E4) : n 1 * a 1 + n 2 * a 2 + n 3 * a 3 = d a := by dsimp [n,d,dotS]; ring
  have nn : n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 = 1 := by
    dsimp only [n]; field_simp [hr.ne']; nlinarith only [hr2]
  calc
    dotS V W = c^2 * (dotS v w +
      t*d v*(n 1*w 1+n 2*w 2+n 3*w 3) + t*d w*(n 1*v 1+n 2*v 2+n 3*v 3) +
      t^2*d v*d w*(n 1^2+n 2^2+n 3^2)) := by
        dsimp only [dotS]
        rw [hv 1 (by decide),hv 2 (by decide),hv 3 (by decide),
          hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
        dsimp only [n,d,dotS]; ring
    _ = _ := by rw [nd w, nd v, nn]; dsimp only [d]; ring

private lemma metric_entry {b : ℝ} {x : E4} (hb : 0 < b) (hx : 4*b < rad x) (i j : Fin 4) :
    conformalStaticForm (1 + b / rad (fromKS b x))
      (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (fromKS b) x (coordBasis i))
      (mfderiv 𝓘(ℝ,E4) 𝓘(ℝ,E4) (fromKS b) x (coordBasis j)) =
        kerrNewmanMetric (2*b) 0 0 x i j := by
  let r := rad x
  let s := root b r
  let c := scale s
  let u := factor b (c*r)
  let V := coordBasis i
  let W := coordBasis j
  let d := fun v : E4 => dotS x v / r
  let J := jac (fromKS b) x
  have rp : 0 < r := by dsimp only [r]; linarith
  obtain ⟨sp, rel⟩ := root_data hb hx
  change 0 < s at sp
  change 4*b = r*(1-s^2) at rel
  have s1 : 0 < 1+s := by positivity
  obtain ⟨_, hu, huc⟩ := inward_algebra rp sp rel
  change u = 2/(1+s) at hu
  change u^2*c = 1 at huc
  have un : 2/u-1 = s := by rw [hu]; field_simp [s1.ne'] <;> ring
  have vol : u^4*c^2=1 := by linear_combination (u^2*c+1)*huc
  have zr : rad (fromKS b x) = c*r := by
    rw [fromKS, pack_radius, abs_of_nonneg (by unfold scale; positivity)]
  have htime (v : E4) : (J v) 0 = v 0 - ((1-s^2)/s^2)*d v := by
    have hden : r-4*b = r*s^2 := by linarith only [rel]
    have q : 4*b/(r-4*b) = (1-s^2)/s^2 := by rw [hden,rel]; field_simp [rp.ne',sp.ne']
    exact (time_entry hb hx v).trans (by change _ - (4*b/(r-4*b))*d v = _; rw [q])
  have hsprod := spatial_product (x := x) (v := V) (w := W) (V := J V) (W := J W)
    (r := r) (c := c) (t := 1/s-1) rp (rad_sq x)
    (spatial_entry hb hx V) (spatial_entry hb hx W)
  have hpr : ksProfile (2*b) 0 0 x = 1-s^2 := by
    simp only [ksProfile, ks_rad, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero, add_zero]
    change r^2*(2*(2*b)*r)/r^4=_
    calc
      _ = 4*b/r := by field_simp [rp.ne'] <;> ring
      _ = _ := (div_eq_iff rp.ne').mpr (by linarith only [rel])
  rw [zr]
  change -(2/u-1)^2*(J V) 0*(J W) 0+u^4*dotS (J V) (J W) = _
  rw [un, htime, htime, hsprod, ← mul_assoc (u^4), vol, one_mul]
  simp only [kerrNewmanMetric, flat_components, null_components x rp, hpr]
  change -(s^2)*(V 0-(1-s^2)/s^2*d V)*(W 0-(1-s^2)/s^2*d W) +
    (dotS V W+(2*(1/s-1)+(1/s-1)^2)*d V*d W) =
    -(V 0)*W 0+dotS V W+(1-s^2)*(V 0+d V)*(W 0+d W)
  field_simp [sp.ne'] <;> ring

theorem solution (b : ℝ) (hb : 0 < b) :
    let U := fun x : EuclideanSpace ℝ (Fin 3) => 1 + b / ‖x‖
    ∃ H : E4 → E4, IsDiffeoOnto H (kerrNewmanDOC (2 * b) 0 0) (conformalExteriorDomain U) ∧
      ∀ y ∈ kerrNewmanDOC (2 * b) 0 0, ∀ i j : Fin 4,
        conformalStaticForm (U (conformalSpatialPoint (H y)))
          (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) H y (coordBasis i))
          (mfderiv 𝓘(ℝ, E4) 𝓘(ℝ, E4) H y (coordBasis j)) =
          kerrNewmanMetric (2 * b) 0 0 y i j := by
  refine ⟨fromKS b, ?_, ?_⟩
  · rw [sourceSet hb, targetSet hb]
    exact chart hb
  · intro y hy i j
    rw [sourceSet hb] at hy
    exact metric_entry hb hy i j
