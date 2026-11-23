-- Prove2me | solution 1 for NoHair.asymptotically_flat_spatial_coordinates_escape
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:19:09.383854+00:00
-- url     : https://prove2.me/submissions/f61dc9fc-58f7-481b-825f-e1a69ede07b0

import Theorems.Thm_NoHair_riemannian_distance_bound_of_differential
import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

open Metric Manifold
open scoped NNReal
private abbrev X := ADMPoint
private abbrev I := 𝓘(ℝ,ADMPoint)
private abbrev J := 𝓘(ℝ,ℝ)

theorem solution (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q) :
    ∃ (R : ℝ) (e : OpenPartialHomeomorph ADMPoint Q), 0<R ∧ e.source={x | R<‖x‖} ∧
      ∀ K : Set Q, IsCompact K → ∃ T : ℝ, ∀ x : ADMPoint, T<‖x‖ → e x ∉ K := by
  classical
  obtain ⟨_,R,C,e,rp,cp,src,_,ce,ci,decay,_⟩ := hend
  let h := riemannianEndCoeffs e
  let L := max R (20*C)
  have lp : 0<L := rp.trans_le (le_max_left _ _)
  have inside {x:X} (hx : L<‖x‖) : x∈e.source := by rw [src]; exact (le_max_left _ _).trans_lt hx
  have lower (x : X) (hx : L < ‖x‖) (v : X) : ‖v‖ ≤ 2*‖mfderiv I I e x v‖ := by
    have r := lp.trans hx
    have scale : C / ‖x‖ ≤ 1/20 := (div_le_iff₀ r).mpr (by linarith only [(max_lt_iff.mp hx).2])
    have af (i j : Fin 3) : |h x i j-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C/‖x‖ := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.add_zero,pow_one] using decay 0 (by decide) x (inside hx) i j
    let δ := (1 : Matrix (Fin 3) (Fin 3) ℝ)
    have vi (i : Fin 3) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
    have comp (i j : Fin 3) : |(h x i j-δ i j)*v i*v j| ≤ (1/20:ℝ)*‖v‖^2 := by
      rw [abs_mul,abs_mul]
      calc _ ≤ ((1/20:ℝ)*‖v‖)*‖v‖ := mul_le_mul
             (mul_le_mul ((af i j).trans scale) (vi i) (abs_nonneg _) (by norm_num))
             (vi j) (abs_nonneg _) (by positivity)
           _ = _ := by ring
    have flat : (∑ i : Fin 3, ∑ j : Fin 3, δ i j*v i*v j) = ‖v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp +decide [Fin.sum_univ_three,δ,Matrix.one_apply] <;> ring
    let H := ∑ i : Fin 3, ∑ j : Fin 3, h x i j*v i*v j
    have dev : |H-‖v‖^2| ≤ 9/20*‖v‖^2 := calc
      _ = |∑ i : Fin 3, ∑ j : Fin 3, (h x i j-δ i j)*v i*v j| := by
        rw [← flat]; dsimp only [H];simp only [sub_mul,Finset.sum_sub_distrib]
      _ ≤ ∑ i : Fin 3, |∑ j : Fin 3, (h x i j-δ i j)*v i*v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (1/20:ℝ)*‖v‖^2 := Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => comp i j)
      _ = _ := by simp [Fin.sum_univ_three]; ring
    have hlow : (1/2:ℝ)*‖v‖^2 ≤ H := by linarith only [(abs_le.mp dev).1,sq_nonneg ‖v‖]
    let D := mfderiv I I e x
    have vrep : (∑ i : Fin 3, v i • EuclideanSpace.single i (1:ℝ)) = v := by
      rw [Fin.sum_univ_three]
      ext j
      fin_cases j <;> simp +decide [EuclideanSpace.single,PiLp.single_apply]
    have drep : D v = ∑ i : Fin 3, v i • D (EuclideanSpace.single i (1:ℝ)) := by
      let P : X →ₗ[ℝ] TangentSpace I (e x) := D.toLinearMap
      change P v = ∑ i : Fin 3, v i • P (EuclideanSpace.single i (1:ℝ))
      calc P v = P (∑ i : Fin 3, v i • EuclideanSpace.single i (1:ℝ)) := congrArg P vrep.symm
           _ = _ := by simp only [map_sum,map_smul]
    have met : ‖D v‖^2=H := by
      rw [←real_inner_self_eq_norm_sq,drep]
      simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [h,riemannianEndCoeffs,D]
      simp only [real_inner_comm]
      ring
    have posD : 0 ≤ ‖D v‖ := norm_nonneg _
    change ‖v‖ ≤ 2*‖D v‖
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*‖D v‖)).mp
    nlinarith only [hlow,met,sq_nonneg ‖v‖]
  let χ : ContDiffBump (0:X) := ⟨1,2,by norm_num,by norm_num⟩
  have smoothB : ContDiff ℝ ∞ χ := χ.contDiff
  obtain ⟨K,lip⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport smoothB (by simp)
  let M : ℝ≥0 := 2*K+1
  have mp : (0:ℝ≥0)<M := by dsimp only [M]; positivity
  let z₀ : X := EuclideanSpace.single 0 (L+1)
  have zlen : ‖z₀‖=L+1 := by simp only [z₀,EuclideanSpace.norm_single,Real.norm_eq_abs,abs_of_pos (by linarith : 0<L+1)]
  have zsrc : z₀ ∈ e.source := inside (by rw [zlen]; linarith)
  let q₀ := e z₀
  refine ⟨R,e,rp,src,?_⟩
  intro V hV
  obtain ⟨D,hD⟩ := hV.isBounded.subset_closedBall q₀
  let T := 4*(L+‖z₀‖+1) + 4*(M:ℝ)*max D 0
  refine ⟨T,?_⟩
  intro x hx hxV
  have mx0 : 0 ≤ (M:ℝ) := M.property
  have big : 4*(L+‖z₀‖+1)<‖x‖ := by
    dsimp only [T] at hx
    linarith only [hx,mul_nonneg mx0 (le_max_right D 0)]
  let b := ‖x‖/4
  have bp : 0<b := by dsimp only [b]; linarith only [big,lp,norm_nonneg z₀]
  let U := closedBall x (2*b)
  have outer {y : X} (hy : y∈U) : L<‖y‖ ∧ ‖z₀‖<‖y‖ := by
    have dist := Metric.mem_closedBall.mp hy
    have tri := dist_triangle (0:X) y x
    simp only [dist_zero_left] at tri
    dsimp only [b] at dist
    constructor <;> linarith only [big,dist,tri,lp,norm_nonneg z₀]
  have ux : x∈U := mem_closedBall_self (by positivity)
  have us : U ⊆ e.source := fun y hy => inside (outer hy).1
  let l := fun y : X => b⁻¹ • (y-x)
  let g := fun y : X => b*χ (l y)
  have cl : ContDiff ℝ ∞ l := by
    change ContDiff ℝ ∞ (fun y : X => (b⁻¹ : ℝ) • (y-x))
    fun_prop
  have cg : ContDiff ℝ ∞ g := contDiff_const.mul (smoothB.comp cl)
  have lg : LipschitzWith K g := by
    apply LipschitzWith.of_dist_le_mul
    intro a t
    have distl : dist (l a) (l t)=b⁻¹*dist a t := by
      simp only [l,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr bp),sub_sub_sub_cancel_right]
    have eg : dist (g a) (g t)= b * dist (χ (l a)) (χ (l t)) := by
      simp only [g,Real.dist_eq,←mul_sub,abs_mul,abs_of_pos bp]
    rw [eg]
    calc _ ≤ b*((K:ℝ)*dist (l a) (l t)) := mul_le_mul_of_nonneg_left (lip.dist_le_mul _ _) bp.le
         _ = _ := by rw [distl]; field_simp
  have gz {y : X} (hy : y∉U) : g y=0 := by
    have ht := lt_of_not_ge (fun z => hy (mem_closedBall.mpr z))
    have large : χ.rOut ≤ dist (l y) 0 := by
      change 2 ≤ dist (b⁻¹ • (y-x)) 0
      rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr bp),inv_mul_eq_div]
      apply (le_div_iff₀ bp).mpr
      simpa only [dist_eq_norm] using ht.le
    simp [g,χ.zero_of_le_dist large]
  let S := e '' U
  have cs : IsCompact S := (isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn.mono us)
  let f := fun q : Q => if q∈e.target then g (e.symm q) else 0
  have out {q:Q} (nq : q∉S) : f q=0 := by
    by_cases t : q∈e.target
    · have h : e.symm q∉U := fun h => nq ⟨_,h,e.right_inv t⟩
      simp only [f,if_pos t,gz h]
    · exact if_neg t
  have outEv {q:Q} (nq : q∉S) : f =ᶠ[𝓝 q] (fun _ => 0) :=
    (show ∀ᶠ y in 𝓝 q, y∉S from cs.isClosed.isOpen_compl.mem_nhds nq).mono fun _ hy => out hy
  have pull {y:X} (hy : y∈e.source) : f (e y)=g y := by simp only [f,if_pos (e.map_source hy),e.left_inv hy]
  have cf : ContMDiff I J 1 f := by
    intro q
    by_cases t : q∈e.target
    · have ev : f =ᶠ[𝓝 q] (g ∘ e.symm) := (show ∀ᶠ y in 𝓝 q, y∈e.target from e.open_target.mem_nhds t).mono
        fun y hy => if_pos hy
      exact (((contMDiff_iff_contDiff.mpr (cg.of_le (by simp))).contMDiffAt).comp q
        ((ci.contMDiffAt (e.open_target.mem_nhds t)).of_le (by simp))).congr_of_eventuallyEq ev
    · have nq : q∉S := by rintro ⟨y,hy,rfl⟩; exact t (e.map_source (us hy))
      exact contMDiffAt_const.congr_of_eventuallyEq (outEv nq)
  have dfbound (q : Q) (v : TangentSpace I q) : ‖mfderiv I J f q v‖ ≤ (M:ℝ)*‖v‖ := by
    by_cases mem : q∈S
    · obtain ⟨y,hy,rfl⟩ := mem
      let φ : PartialDiffeomorph I I X Q ∞ := { e.toPartialEquiv with
        open_source := e.open_source, open_target := e.open_target,contMDiffOn_toFun := ce,contMDiffOn_invFun := ci }
      have localD : IsLocalDiffeomorphAt I I ∞ e y := ⟨φ,us hy,fun _ _ => rfl⟩
      obtain ⟨w,hw⟩ := (localD.mfderivToContinuousLinearEquiv (by simp)).surjective v
      change mfderiv I I e y w = v at hw
      have ev : f ∘ e =ᶠ[𝓝 y] g := (show ∀ᶠ z in 𝓝 y, z∈e.source from e.open_source.mem_nhds (us hy)).mono fun _ hz => pull hz
      have chain := mfderiv_comp (I':=I) y (cf.contMDiffAt.mdifferentiableAt one_ne_zero) (localD.mdifferentiableAt (by simp))
      rw [ev.mfderiv_eq,mfderiv_eq_fderiv] at chain
      have hw' := congrArg (fun A : X →L[ℝ] ℝ => A w) chain
      change fderiv ℝ g y w = mfderiv I J f (e y) (mfderiv I I e y w) at hw'
      rw [hw] at hw'
      have normed : ‖mfderiv I J f (e y) v‖=‖fderiv ℝ g y w‖ := by
        rw [norm_tangentSpace_vectorSpace]; exact congrArg (fun a : ℝ => ‖a‖) hw'.symm
      rw [normed]
      have low := lower y (outer hy).1 (w:X)
      rw [hw] at low
      have hi := norm_fderiv_le_of_lipschitz ℝ lg (x₀:=y)
      let euNorm : X → ℝ := fun z => ‖z‖
      calc _ ≤ ‖fderiv ℝ g y‖*euNorm w := (fderiv ℝ g y).le_opNorm w
           _ ≤ (K:ℝ)*(2*‖v‖) := mul_le_mul hi low (norm_nonneg _) K.property
           _ ≤ _ := by dsimp only [M]; push_cast; nlinarith only [norm_nonneg v]
    · have zero : mfderiv I J f q=0 := by rw [(outEv mem).mfderiv_eq,mfderiv_const] <;> rfl
      rw [zero,ContinuousLinearMap.zero_apply,norm_zero]
      positivity
  have LF := riemannian_distance_bound_of_differential Q f cf M mp dfbound
  have zoff : z₀∉U := fun hh => (outer hh).2.false
  have left : f (e x)=b := by
    rw [pull (us ux)]
    have yes : χ (0:X)=1 := χ.one_of_mem_closedBall (mem_closedBall_self χ.rIn_pos.le)
    simp [g,l,yes]
  have right : f q₀=0 := (pull zsrc).trans (gz zoff)
  have control := LF.dist_le_mul (e x) q₀
  rw [left,right,dist_zero_right,Real.norm_eq_abs,abs_of_pos bp] at control
  have boundD := mem_closedBall.mp (hD hxV)
  have bad := control.trans (mul_le_mul_of_nonneg_left (boundD.trans (le_max_left D 0)) mx0)
  dsimp only [T] at hx
  dsimp only [b] at bad
  linarith only [hx,bad,lp,norm_nonneg z₀]
