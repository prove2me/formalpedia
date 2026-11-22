-- Prove2me | solution 1 for NoHair.Weyl.kerr_oblate_exterior_differential
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T22:28:35.20572+00:00
-- url     : https://prove2.me/submissions/6941ca81-f29e-445f-9549-8a192bbe81c4

import Definitions.Def_NoHair_kerrWeylModel

noncomputable section

open scoped ContDiff
open NoHair NoHair.Weyl

private theorem ellipsoid (a : ℝ) (y : E4) :
    let r := ksRadius a y
    (r^2+a^2)*(r^2-y 3^2)=r^2*(y 1^2+y 2^2) := by
  let b := y 1^2+y 2^2+y 3^2-a^2
  let d := Real.sqrt (b^2+4*a^2*y 3^2)
  have h₁ : |b| ≤ d := by
    rw [← Real.sqrt_sq_eq_abs b]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (by positivity))
  have h₂ : 0 ≤ (b+d)/2 := by linarith [neg_le_abs b]
  have r2 : ksRadius a y ^ 2=(b+d)/2 := Real.sq_sqrt h₂
  have hsq : d^2=b^2+4*a^2*y 3^2 := Real.sq_sqrt (by positivity)
  dsimp only
  rw [r2]
  dsimp [b] at hsq ⊢
  nlinarith only [hsq]

private theorem smooth_radial {a : ℝ} {y : E4} (hr : 0 < ksRadius a y) :
    ContDiffAt ℝ ∞ (ksRadius a) y := by
  let b := y 1^2+y 2^2+y 3^2-a^2
  have hout : 0 < (b+Real.sqrt (b^2+4*a^2*y 3^2))/2 := Real.sqrt_pos.mp hr
  have hin : b^2+4*a^2*y 3^2 ≠ 0 := by
    intro hz
    have hb : b=0 := by nlinarith [sq_nonneg b,mul_nonneg (sq_nonneg a) (sq_nonneg (y 3))]
    rw [hz,Real.sqrt_zero,hb] at hout
    norm_num at hout
  unfold ksRadius
  fun_prop (disch := first | exact hout.ne' | exact hin)

private theorem along_coord (y v : E4) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => (y+t • v) i) (v i) 0 := by
  simpa [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] using
    (((hasDerivAt_id' (0:ℝ)).mul_const (v i)).const_add (y i))

theorem solution (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (y : E4) (hy : y ∈ offAxisExterior m a) :
    let r := ksRadius a y
    let c := y 3/r
    0 < r ∧ 0 < 1-c^2 ∧ 0 < kerrDelta m a r ∧
    y 1^2+y 2^2=(r^2+a^2)*(1-c^2) ∧ ContDiffAt ℝ ∞ (ksRadius a) y ∧
    ∀ v : E4, (r^2+a^2*c^2)*(fderiv ℝ (ksRadius a) y v) =
      r*(y 1*v 1+y 2*v 2)+(r^2+a^2)*c*v 3 := by
  let r := ksRadius a y
  let c := y 3/r
  let k := Real.sqrt (m^2-a^2)
  have hlarge : m+k<r := by simpa [kerrNewmanDOC,kerrNewmanOuterRadius,r,k] using hy.1
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hr : 0 < r := by linarith [hm.1]
  have hk2 : k^2=m^2-a^2 := Real.sq_sqrt (by nlinarith [hm.2])
  have hd : 0 < kerrDelta m a r := by
    unfold kerrDelta
    nlinarith [mul_pos (show 0 < r-m-k by linarith) (show 0 < r-m+k by linarith)]
  have hZ : y 3 = r*c := by dsimp [c]; field_simp
  have hL : y 1^2+y 2^2=(r^2+a^2)*(1-c^2) := by
    have h := ellipsoid a y
    change (r^2+a^2)*(r^2-y 3^2)=r^2*(y 1^2+y 2^2) at h
    rw [hZ] at h
    apply mul_left_cancel₀ (pow_ne_zero 2 hr.ne')
    linarith only [h]
  have hxy : 0 < y 1^2+y 2^2 := by
    rcases hy.2 with h | h
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h) (sq_nonneg _)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h)
  have hB : 0 < r^2+a^2 := by positivity
  have hS : 0 < 1-c^2 := pos_of_mul_pos_right (hL ▸ hxy) hB.le
  have hsmooth := smooth_radial hr
  refine ⟨hr,hS,hd,hL,hsmooth,?_⟩
  intro v
  let γ := fun t : ℝ => y+t • v
  let R := fun t => ksRadius a (γ t)
  let dr := fderiv ℝ (ksRadius a) y v
  have hγ : HasDerivAt γ v 0 := by
    simpa [γ] using ((hasDerivAt_id' (0:ℝ)).smul_const v).const_add y
  have h0 : γ 0=y := by simp [γ]
  have hR : HasDerivAt R dr 0 := by
    have hF : HasFDerivAt (ksRadius a) (fderiv ℝ (ksRadius a) y) (γ 0) := by
      rw [h0]
      exact (hsmooth.differentiableAt (by norm_num)).hasFDerivAt
    exact hF.comp_hasDerivAt 0 hγ
  have h₁ := (hR.fun_pow 2).add_const (a^2)
  have h₂ := (hR.fun_pow 2).fun_sub ((along_coord y v 3).fun_pow 2)
  have h₃ := ((along_coord y v 1).fun_pow 2).fun_add ((along_coord y v 2).fun_pow 2)
  have ident : (fun t => (R t^2+a^2)*(R t^2-(γ t) 3^2)) =
      fun t => R t^2*((γ t) 1^2+(γ t) 2^2) := funext fun t => ellipsoid a (γ t)
  have lhs := h₁.fun_mul h₂
  change HasDerivAt (fun t => (R t^2+a^2)*(R t^2-(γ t) 3^2)) _ 0 at lhs
  rw [ident] at lhs
  have h := lhs.unique ((hR.fun_pow 2).fun_mul h₃)
  simp only [R,γ,zero_smul,add_zero,show (2:ℕ)-1=1 by decide,Nat.cast_ofNat,pow_one] at h
  change 2*r*dr*(r^2-y 3^2)+(r^2+a^2)*(2*r*dr-2*y 3*v 3) =
    2*r*dr*(y 1^2+y 2^2)+r^2*(2*y 1*v 1+2*y 2*v 2) at h
  rw [hZ,hL] at h
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) hr.ne')
  change (2*r)*((r^2+a^2*c^2)*dr)=(2*r)*(r*(y 1*v 1+y 2*v 2)+(r^2+a^2)*c*v 3)
  linarith only [h]
