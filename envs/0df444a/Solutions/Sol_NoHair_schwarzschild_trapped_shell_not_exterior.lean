-- Prove2me | solution 1 for NoHair.schwarzschild_trapped_shell_not_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:54:46.111323+00:00
-- url     : https://prove2.me/submissions/68e00800-2cad-4ae6-910f-4584f87282fb

import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair Set Filter Topology
open scoped ContDiff Manifold BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

private theorem radius_eq (x : E4) : ksRadius 0 x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2) = Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero, Real.sqrt_sq hp]
  congr 1
  ring

private abbrev r := ksRadius 0
private abbrev I4 := 𝓘(ℝ,E4)
private def dotS (x v : E4) := x 1*v 1+x 2*v 2+x 3*v 3
private def rd (x v : E4) := dotS x v / r x

private lemma rsq (x : E4) : r x ^ 2 = x 1^2+x 2^2+x 3^2 := by
  rw [r, radius_eq, spatialRadius, Real.sq_sqrt (by positivity)]

private lemma norm_bound (x v : E4) (hr : 0 < r x) : rd x v ^ 2 ≤ dotS v v := by
  have iden : (r x)^2 * dotS v v - dotS x v ^ 2 =
      (x 1*v 2-x 2*v 1)^2+(x 1*v 3-x 3*v 1)^2+(x 2*v 3-x 3*v 2)^2 := by
    rw [rsq]; unfold dotS; ring
  dsimp only [rd]
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith only [iden, sq_nonneg (x 1*v 2-x 2*v 1), sq_nonneg (x 1*v 3-x 3*v 1),
    sq_nonneg (x 2*v 3-x 3*v 2)]

private lemma radius_diff (x : E4) (hp : 0 < r x) : DifferentiableAt ℝ r x := by
  have q : 0 < x 1^2+x 2^2+x 3^2 := by rw [← rsq]; positivity
  change DifferentiableAt ℝ (ksRadius 0) x
  rw [show ksRadius 0 = spatialRadius from funext radius_eq]
  unfold spatialRadius
  fun_prop (disch := exact q.ne')

private lemma radius_der (x v : E4) (hp : 0 < r x) : fderiv ℝ r x v = rd x v := by
  have d := hasDerivAt_ksRadius_line 0 x v hp
  apply fderiv_eq_of_line (radius_diff x hp)
  apply d.congr_deriv
  change r x * (r x ^ 2 * (x 1 * v 1 + x 2 * v 2) + (r x ^ 2 + 0 ^ 2) * x 3 * v 3) /
    (r x ^ 4 + 0 ^ 2 * x 3 ^ 2) = rd x v
  dsimp only [rd,dotS]
  field_simp [hp.ne'] <;> ring

private lemma profile (m : ℝ) (x : E4) (hp : 0 < r x) : ksProfile m 0 0 x = 2*m/r x := by
  unfold ksProfile
  change r x^2*(2*m*r x-0^2)/(r x^4+0^2*x 3^2) = _
  field_simp [hp.ne'] <;> ring

private lemma matrix_eval (A : Matrix (Fin 4) (Fin 4) ℝ) (v w : E4) :
    matrixBilin A v w = ∑ i, ∑ j, v i * (w j * A i j) := by
  change Matrix.toLinearMap₂' ℝ A (WithLp.ofLp v) (WithLp.ofLp w) = _
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]

private lemma quadratic (x v : E4) (hp : 0 < r x) :
    matrixBilin (kerrNewmanMetric 1 0 0 x) v v =
      -(v 0)^2+dotS v v+(2/r x)*(v 0+rd x v)^2 := by
  have hx1 : ksNull 0 x 1 = x 1/r x := by rw [ksNull_one]; change (r x*x 1+0*x 2)/(r x^2+0^2)=_; field_simp [hp.ne'] <;> ring
  have hx2 : ksNull 0 x 2 = x 2/r x := by rw [ksNull_two]; change (r x*x 2-0*x 1)/(r x^2+0^2)=_; field_simp [hp.ne'] <;> ring
  have hx3 : ksNull 0 x 3 = x 3/r x := ksNull_three 0 x
  have flat : matrixBilin minkowski v v = -(v 0)^2+dotS v v := by
    rw [matrix_eval]
    simp [minkowski, Fin.sum_univ_four, dotS] <;> ring
  rw [← flat, matrix_eval, matrix_eval]
  simp only [kerrNewmanMetric, profile 1 x hp, mul_one, ksNull_zero, hx1, hx2, hx3, Fin.sum_univ_four,
    dotS,rd]
  ring

private lemma trapped (x v : E4) (hp : 0 < r x) (hr : r x ≤ 3/2) {c : ℝ} (hc : 0 < c)
    (hv : matrixBilin (kerrNewmanMetric 1 0 0 x) v v = -c) : c/3 ≤ rd x v ^ 2 := by
  let B := 2/r x-1
  have hB : 1/3 ≤ B := by
    change 1/3 ≤ 2/r x-1
    have hl : 4/3 ≤ 2/r x := (le_div_iff₀ hp).mpr (by linarith)
    linarith
  rw [quadratic x v hp] at hv
  have hcompl : B*(-c)+rd x v^2 =
      B*(dotS v v-rd x v^2)+(B*v 0+(B+1)*rd x v)^2 := by
    rw [← hv]; dsimp only [B]; ring
  nlinarith only [hcompl, mul_nonneg (show 0 ≤ B by linarith) (sub_nonneg.mpr (norm_bound x v hp)),
    sq_nonneg (B*v 0+(B+1)*rd x v), mul_le_mul_of_nonneg_right hB hc.le]

private lemma bounded_radius {f d : ℝ → ℝ} (c : ℝ) (hc : 0 < c)
    (h : ∀ t, 1 < f t) (h0 : f 0 = 3/2) (hd : ∀ t, HasDerivAt f (d t) t)
    (htr : ∀ t, f t ≤ 3/2 → c/3 ≤ d t^2) : False := by
  let e := c/12
  have he : 0 < e := by dsimp only [e]; positivity
  let P := fun t : ℝ => f t+e*t^2
  have diff (t : ℝ) : HasDerivAt P (d t+2*e*t) t := by
    apply ((hd t).add (((hasDerivAt_id' t).fun_pow 2).const_mul e)).congr_deriv
    ring
  let L := 1+1/e
  have hL : 0 < L := by dsimp only [L]; positivity
  have hel : 1 ≤ e*L^2 := by
    have hi : e*(1/e)=1 := by field_simp
    have hh : e*(1/e)^2 ≥ 0 := by positivity
    dsimp only [L]
    nlinarith only [hi, he, hh]
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn
      (show (Icc (-L) L).Nonempty from ⟨0, by constructor <;> linarith⟩)
      (show Continuous P from continuous_iff_continuousAt.mpr (fun t => (diff t).continuousAt)).continuousOn
  have hP : f t+e*t^2 ≤ 3/2 := by
    have hm := hmin (show (0:ℝ) ∈ Icc (-L) L by constructor <;> linarith)
    change f t+e*t^2 ≤ f 0+e*0^2 at hm
    simpa only [P, h0, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using hm
  have hlt₁ : -L < t := ht.1.lt_of_ne (by
    intro eq; rw [← eq] at hP; nlinarith only [hP, h (-L),hel])
  have hlt₂ : t < L := ht.2.lt_of_ne (by
    intro eq; rw [eq] at hP; linarith only [hP, h L,hel])
  have hz := (hmin.isLocalMin (Icc_mem_nhds hlt₁ hlt₂)).hasDerivAt_eq_zero (diff t)
  have htR : f t ≤ 3/2 := by linarith only [hP,mul_nonneg he.le (sq_nonneg t)]
  have hsmall : e*t^2 ≤ 1/2 := by linarith only [h t,hP]
  have ds : d t = -(2*e*t) := by linarith only [hz]
  have hard := htr t htR
  rw [ds] at hard
  have hmul := mul_le_mul_of_nonneg_left hsmall he.le
  change c/3 ≤ (-(2*e*t))^2 at hard
  have hc' : c = 12*e := by dsimp only [e]; ring
  rw [hc'] at hard
  nlinarith only [hard, hmul, he]

private lemma trapped_not_iso (m : ℝ) (hm : 0 < m) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0)
      ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) m 0 0 := by
  rintro ⟨_,ψ,⟨χ,hmap,hinv,_,hrinv,hs,_⟩,hcoeff⟩
  let U := kerrNewmanSpacetime 0
  let z : E4 := WithLp.toLp 2 ![0,3/2,0,0]
  have rz : r z = 3/2 := by
    rw [r,radius_eq]; change Real.sqrt ((3/2)^2+0^2+0^2) = _; norm_num
  let p : U := ⟨z, by change 0 < r z; rw [rz]; norm_num⟩
  have hp : p ∈ (Subtype.val : U → E4) ⁻¹' exteriorRegion 1 := by
    change 1 < spatialRadius z; rw [← radius_eq, ← show r z = ksRadius 0 z from rfl, rz]; norm_num
  let y := χ p
  have hy := hinv hp
  have hψy : ψ y = p := hrinv hp
  have outer : kerrNewmanOuterRadius m 0 0 = 2*m := by simp [kerrNewmanOuterRadius,Real.sqrt_sq hm.le]; ring
  have yr : 2*m < r y := by change kerrNewmanOuterRadius m 0 0 < r y at hy; rwa [outer] at hy
  have yrpos : 0 < r y := by linarith
  let c := 1-2*m/r y
  have hc : 0 < c := sub_pos.mpr ((div_lt_one yrpos).mpr yr)
  let ℓ := fun t : ℝ => y+t • coordBasis 0
  have line (t : ℝ) : HasDerivAt ℓ (coordBasis 0) t := by
    change HasDerivAt (fun s : ℝ => y+s • coordBasis 0) (coordBasis 0) t
    convert! ((hasDerivAt_id' t).smul_const (coordBasis 0)).const_add y using 1 <;> simp
  have rline (t : ℝ) : r (ℓ t) = r y := NoHair.KNE.ksRadius_time 0 y t
  have linemem (t : ℝ) : ℓ t ∈ kerrNewmanDOC m 0 0 := by
    change kerrNewmanOuterRadius m 0 0 < r (ℓ t); rwa [outer,rline]
  have hopen : IsOpen (kerrNewmanDOC m 0 0) := isOpen_lt continuous_const (continuous_ksRadius 0)
  let X := fun t : ℝ => (ψ (ℓ t)).val
  let V := fun t : ℝ => (show E4 from mfderiv I4 I4 ψ (ℓ t) (coordBasis 0))
  have dX (t : ℝ) : HasDerivAt X (V t) t := by
    let P := (Subtype.val : U → E4) ∘ ψ
    have dψ := ((hs (ℓ t) (linemem t)).contMDiffAt (hopen.mem_nhds (linemem t))).mdifferentiableAt (by simp)
    have dv : MDifferentiableAt I4 I4 (Subtype.val : U → E4) (ψ (ℓ t)) :=
      (contMDiff_subtype_val (I := I4) (U := U) (n := ∞)).mdifferentiableAt (by simp)
    have dP : DifferentiableAt ℝ P (ℓ t) := mdifferentiableAt_iff_differentiableAt.mp (dv.comp (ℓ t) dψ)
    have dvId : (mfderiv I4 I4 (Subtype.val : U → E4) (ψ (ℓ t)) : E4 →L[ℝ] E4) = ContinuousLinearMap.id ℝ E4 :=
      mfderiv_extChartAt_self (I := I4) (x := ψ (ℓ t))
    have jP : fderiv ℝ P (ℓ t) = (mfderiv I4 I4 ψ (ℓ t) : E4 →L[ℝ] E4) := by
      have hh := mfderiv_comp (I' := I4) (ℓ t) dv dψ
      rw [dvId, mfderiv_eq_fderiv] at hh
      exact hh
    exact (dP.hasFDerivAt.comp_hasDerivAt t (line t)).congr_deriv (by rw [jP]; rfl)
  have rangeX (t : ℝ) : 1 < r (X t) := by
    rw [r,radius_eq]; exact hmap (linemem t)
  have smoothr (t : ℝ) : HasDerivAt (fun s => r (X s)) (rd (X t) (V t)) t := by
    have pos : 0 < r (X t) := by linarith only [rangeX t]
    exact ((radius_diff (X t) pos).hasFDerivAt.comp_hasDerivAt t (dX t)).congr_deriv (radius_der _ _ pos)
  apply bounded_radius c hc rangeX _ smoothr
  · intro t ht
    apply trapped _ _ (by linarith only [rangeX t]) ht hc
    have cc := congrFun (congrFun (hcoeff (ℓ t) (linemem t)).1 0) 0
    change matrixBilin (kerrNewmanMetric 1 0 0 (X t)) (V t) (V t) = kerrNewmanMetric m 0 0 (ℓ t) 0 0 at cc
    rw [cc]; simp only [kerrNewmanMetric, profile m _ (rline t ▸ yrpos), ksNull_zero, mul_one, rline]
    change -1 + 2*m/r y = -(1-2*m/r y); ring
  · change r ((ψ (y+(0:ℝ) • coordBasis 0)).val) = _
    rw [zero_smul, add_zero,hψy]; exact rz

theorem solution (m : ℝ) (hm : 0 < m) :
    ¬ IsKerrNewmanDOC (kerrNewmanMetricField 1 0 0) (kerrNewmanFieldField 0 0) ((Subtype.val : kerrNewmanSpacetime 0 → E4) ⁻¹' exteriorRegion 1) m 0 0 := trapped_not_iso m hm
