-- Prove2me | solution 1 for NoHair.kerr_vacuum_helical_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T10:07:00.503751+00:00
-- url     : https://prove2.me/submissions/7885b99a-7773-481e-b978-a2d4910acc3e

import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair Set
open scoped ContDiff Manifold BigOperators
noncomputable section

private abbrev U (a : ℝ) := kerrNewmanSpacetime a
private abbrev I4 := 𝓘(ℝ,E4)
private def four (t x y z : ℝ) : E4 := WithLp.toLp 2 ![t,x,y,z]
private def move (b c s : ℝ) (y : E4) :=
  four (y 0+b) (c*y 1-s*y 2) (s*y 1+c*y 2) (y 3)
private def rotL (c s : ℝ) : E4 →L[ℝ] E4 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => four (y 0) (c*y 1-s*y 2) (s*y 1+c*y 2) (y 3)
      map_add' := by intro v w; ext i; fin_cases i <;> simp [four] <;> ring
      map_smul' := by intro d w; ext i; fin_cases i <;> simp [four,smul_eq_mul] <;> ring }

private theorem radius_move (a b c s : ℝ) (h : c^2+s^2=1) (y : E4) :
    ksRadius a (move b c s y)=ksRadius a y := by
  have hr : (c*y 1-s*y 2)^2+(s*y 1+c*y 2)^2=y 1^2+y 2^2 := by
    linear_combination (y 1^2+y 2^2)*h
  rw [ksRadius_eq']
  dsimp only [move,four]
  change Real.sqrt (((c*y 1-s*y 2)^2+(s*y 1+c*y 2)^2+y 3^2-a^2+
    Real.sqrt (((c*y 1-s*y 2)^2+(s*y 1+c*y 2)^2+y 3^2-a^2)^2+4*a^2*y 3^2))/2)=_
  rw [hr]

private theorem move_derivative (b c s : ℝ) (y : E4) :
    HasFDerivAt (move b c s) (rotL c s) y := by
  have he : move b c s=(fun z : E4 => rotL c s z+four b 0 0 0) := by
    funext z; ext i; fin_cases i <;> simp [move,rotL,four] <;> ring
  rw [he]
  exact (rotL c s).hasFDerivAt.add_const _

private def kv (a : ℝ) (y v : E4) :=
  v 0+ksNull a y 1*v 1+ksNull a y 2*v 2+ksNull a y 3*v 3
private def flat (v w : E4) := -(v 0*w 0)+v 1*w 1+v 2*w 2+v 3*w 3

private theorem metric_coeff (m a : ℝ) (y v w : E4) :
    matrixBilin (kerrNewmanMetric m a 0 y) v w =
      flat v w+ksProfile m a 0 y*kv a y v*kv a y w := by
  change Matrix.toLinearMap₂' ℝ (kerrNewmanMetric m a 0 y) (WithLp.ofLp v) (WithLp.ofLp w)=_
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul,kerrNewmanMetric,Fin.sum_univ_four,ksNull_zero]
  simp [minkowski,kv,flat] <;> ring

private theorem invariant (m a b c s : ℝ) (h : c^2+s^2=1) (y v w : E4) :
    matrixBilin (kerrNewmanMetric m a 0 (move b c s y)) (rotL c s v) (rotL c s w)=
    matrixBilin (kerrNewmanMetric m a 0 y) v w := by
  let y' := move b c s y
  let L := rotL c s
  have hr : ksRadius a y'=ksRadius a y := radius_move a b c s h y
  have hF : ksProfile m a 0 y'=ksProfile m a 0 y := by
    unfold ksProfile; rw [hr]; rfl
  have h1 : ksNull a y' 1=c*ksNull a y 1-s*ksNull a y 2 := by
    rw [ksNull_one,hr,ksNull_one,ksNull_two]
    change (ksRadius a y*(c*y 1-s*y 2)+a*(s*y 1+c*y 2))/_=_
    ring
  have h2 : ksNull a y' 2=s*ksNull a y 1+c*ksNull a y 2 := by
    rw [ksNull_two,hr,ksNull_one,ksNull_two]
    change (ksRadius a y*(s*y 1+c*y 2)-a*(c*y 1-s*y 2))/_=_
    ring
  have h3 : ksNull a y' 3=ksNull a y 3 := by rw [ksNull_three,ksNull_three,hr]; rfl
  have hk (v : E4) : kv a y' (L v)=kv a y v := by
    change v 0+ksNull a y' 1*(c*v 1-s*v 2)+ksNull a y' 2*(s*v 1+c*v 2)+ksNull a y' 3*v 3=_
    rw [h1,h2,h3]; dsimp [kv]
    linear_combination (ksNull a y 1*v 1+ksNull a y 2*v 2)*h
  have hf : flat (L v) (L w)=flat v w := by
    change -(v 0*w 0)+(c*v 1-s*v 2)*(c*w 1-s*w 2)+(s*v 1+c*v 2)*(s*w 1+c*w 2)+v 3*w 3=_
    dsimp [flat]; linear_combination (v 1*w 1+v 2*w 2)*h
  rw [metric_coeff,metric_coeff]
  change flat (L v) (L w)+ksProfile m a 0 y'*kv a y' (L v)*kv a y' (L w)=_
  rw [hf,hF,hk,hk]

private theorem ambient_velocity {a : ℝ} (γ : ℝ → U a) (hγ : ContMDiff 𝓘(ℝ,ℝ) I4 1 γ) (v : E4)
    (hd : HasDerivAt (fun t => (γ t).val) v 0) : (velocity γ 0 : E4)=v := by
  have hval : ContMDiff I4 I4 1 (Subtype.val : U a → E4) := contMDiff_subtype_val
  have hcomp := mfderiv_comp 0 (hval.mdifferentiableAt (by simp) (x := γ 0)) (hγ.mdifferentiableAt (by simp))
  have hinc : (mfderiv I4 I4 (Subtype.val : U a → E4) (γ 0) : E4 →L[ℝ] E4)=ContinuousLinearMap.id ℝ E4 :=
    mfderiv_extChartAt_self (I := I4) (x := γ 0)
  rw [hinc] at hcomp
  have he : fderiv ℝ (fun t => (γ t).val) 0 = (mfderiv 𝓘(ℝ,ℝ) I4 γ 0 : ℝ →L[ℝ] E4) := by
    rw [← mfderiv_eq_fderiv]; exact hcomp
  exact (congrArg (fun A : ℝ →L[ℝ] E4 => A 1) he).symm.trans hd.deriv

private theorem four_deriv {t x y z : ℝ → ℝ} {dt dx dy dz s : ℝ}
    (ht : HasDerivAt t dt s) (hx : HasDerivAt x dx s) (hy : HasDerivAt y dy s) (hz : HasDerivAt z dz s) :
    HasDerivAt (fun s => four (t s) (x s) (y s) (z s)) (four dt dx dy dz) s := by
  have h : HasDerivAt (fun s => (![t s,x s,y s,z s] : Fin 4 → ℝ)) ![dt,dx,dy,dz] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ht
    · exact hx
    · exact hy
    · exact hz
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt s h

theorem solution (m a Ω : ℝ) :
    let X : VecField (kerrNewmanSpacetime a) := fun x => WithLp.toLp 2 ![1,-Ω*x.val 2,Ω*x.val 1,0]
    ∃ χ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      IsSymmetryFlow (kerrNewmanMetricField m a 0) (kerrNewmanFieldField a 0) χ ∧
      flowGenerator χ = X := by
  let q : ℝ := Ω
  let c := fun t => Real.cos (q*t)
  let s := fun t => Real.sin (q*t)
  have hc (t) : c t^2+s t^2=1 := Real.cos_sq_add_sin_sq _
  let χ (t : ℝ) (x : (U a)) : (U a) := ⟨move t (c t) (s t) x.val,by
    change 0<ksRadius a (move t (c t) (s t) x.val)
    rw [radius_move a _ _ _ (hc t)]; exact x.property⟩
  let H := fun p : ℝ × E4 => move p.1 (c p.1) (s p.1) p.2
  have hH : ContDiff ℝ ∞ H := by
    apply (contDiff_piLp 2).2
    intro i; fin_cases i
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => p.2 0+p.1); fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => c p.1*p.2 1-s p.1*p.2 2); dsimp [c,s]; fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => s p.1*p.2 1+c p.1*p.2 2); dsimp [c,s]; fun_prop
    · change ContDiff ℝ ∞ (fun p : ℝ × E4 => p.2 3); fun_prop
  have hval : ContMDiff I4 I4 ∞ (Subtype.val : (U a) → E4) := contMDiff_subtype_val
  have hχ : ContMDiff (𝓘(ℝ,ℝ).prod I4) I4 ∞ (fun p : ℝ × (U a) => χ p.1 p.2) := by
    apply (ContMDiff.subtypeVal_comp_iff (U a) _).mp
    have pair : ContMDiff (𝓘(ℝ,ℝ).prod I4) 𝓘(ℝ,ℝ × E4) ∞ (fun p : ℝ × (U a) => (p.1,p.2.val)) :=
      (contMDiff_prod_module_iff _).2 ⟨contMDiff_fst,hval.comp contMDiff_snd⟩
    exact hH.contMDiff.comp pair
  have hds (t) (x : (U a)) : (mfderiv I4 I4 (χ t) x : E4 →L[ℝ] E4)=rotL (c t) (s t) := by
    have hd := move_derivative t (c t) (s t) x.val
    have hh : ContMDiff I4 I4 ∞ (χ t) := hχ.comp (contMDiff_const.prodMk contMDiff_id)
    have inc (p : (U a)) : (mfderiv I4 I4 (Subtype.val : (U a) → E4) p : E4 →L[ℝ] E4)=
      ContinuousLinearMap.id ℝ E4 := mfderiv_extChartAt_self (I := I4) (x := p)
    calc
      _=(mfderiv I4 I4 (Subtype.val : (U a) → E4) (χ t x)).comp (mfderiv I4 I4 (χ t) x) := by rw [inc]; rfl
      _=mfderiv I4 I4 ((Subtype.val : (U a) → E4) ∘ χ t) x :=
        (mfderiv_comp x (hval.mdifferentiableAt (by simp)) (hh.mdifferentiableAt (by simp))).symm
      _=(mfderiv I4 I4 (move t (c t) (s t)) x.val).comp (mfderiv I4 I4 (Subtype.val : (U a) → E4) x) :=
        mfderiv_comp x hd.differentiableAt.mdifferentiableAt (hval.mdifferentiableAt (by simp))
      _=_ := by rw [inc,mfderiv_eq_fderiv,hd.fderiv]; rfl
  have f0 (x : (U a)) : kerrNewmanFieldField a 0 x=0 := by
    have he : kerrNewmanField a 0 x.val=0 := by
      ext i j; simp [kerrNewmanField,coordPartial,kerrNewmanPotential]
    change matrixBilin (kerrNewmanField a 0 x.val)=0
    rw [he]; ext v w; simp [matrixBilin,Matrix.toLinearMap₂'_apply]
  refine ⟨χ,⟨?_,?_,hχ,?_,?_⟩,?_⟩
  · intro x
    apply Subtype.ext
    ext i; fin_cases i <;> simp [χ,move,four,c,s]
  · intro t u x
    apply Subtype.ext
    ext i; fin_cases i <;> simp [χ,move,four,c,s,mul_add,Real.sin_add,Real.cos_add] <;> ring
  · intro t x v w
    rw [hds]
    exact invariant m a t (c t) (s t) (hc t) x.val v w
  · intro t x v w; rw [f0,f0]; rfl
  · funext x
    have hh : ContMDiff 𝓘(ℝ,ℝ) I4 1 (fun t => χ t x) :=
      (hχ.comp (contMDiff_id.prodMk contMDiff_const)).of_le (by simp)
    apply ambient_velocity (fun t => χ t x) hh
    have hq : HasDerivAt (fun t : ℝ => q*t) q 0 := by simpa using (hasDerivAt_id' (0:ℝ)).const_mul q
    have hv := four_deriv ((hasDerivAt_id' (0:ℝ)).const_add (x.val 0))
      ((hq.cos.mul_const (x.val 1)).sub (hq.sin.mul_const (x.val 2)))
      ((hq.sin.mul_const (x.val 1)).add (hq.cos.mul_const (x.val 2))) (hasDerivAt_const (0:ℝ) (x.val 3))
    apply hv.congr_deriv
    ext i; fin_cases i <;> simp [four,q] <;> ring
