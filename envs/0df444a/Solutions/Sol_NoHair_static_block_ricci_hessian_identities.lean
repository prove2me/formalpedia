-- Prove2me | solution 1 for NoHair.static_block_ricci_hessian_identities
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:31:48.057655+00:00
-- url     : https://prove2.me/submissions/6bd8ef4b-ca29-472b-a228-ffbf99234f6f

import Theorems.Thm_NoHair_static_lapse_gradient_covariant_derivative
import Definitions.Def_NoHair_staticHorizonGeometry

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

open scoped Matrix

private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev Mat := Matrix I I ℝ
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev bvec (i : I) : X := EuclideanSpace.single i 1

private lemma sm_pd {f : X → ℝ} {x : X} (c : ContDiffAt ℝ ∞ f x) (i : I) :
    ContDiffAt ℝ ∞ (pd i f) x :=
  (c.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const

private lemma sm_inv {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a b : I) :
    ContDiffAt ℝ ∞ (fun y => (h y)⁻¹ a b) x := by
  classical
  have detS {ι : Type} [Fintype ι] [DecidableEq ι] (G : X → Matrix ι ι ℝ)
      (cG : ∀ k m, ContDiffAt ℝ ∞ (fun y => G y k m) x) :
      ContDiffAt ℝ ∞ (fun y => (G y).det) x := by
    simp_rw [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    have pr (t : Finset ι) : ContDiffAt ℝ ∞ (fun y => ∏ j ∈ t, G y (σ j) j) x := by
      induction t using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : X => (1:ℝ)) x)
      | @insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (cG _ _).mul ih
    exact contDiffAt_const.mul (pr Finset.univ)
  have det0 := ((h x).isUnit_iff_isUnit_det.mp hp.isUnit).ne_zero
  have adj : ContDiffAt ℝ ∞ (fun y => (h y).adjugate a b) x := by
    simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    exact contDiffAt_const.mul (detS (ι:=Fin 2) (fun y => (h y).submatrix b.succAbove a.succAbove)
      (fun k m => hc _ _))
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
  exact ((detS (ι:=I) h hc).inv det0).mul adj

private lemma sm_ch {h : X → Mat} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a i j : I) :
    ContDiffAt ℝ ∞ (fun y => spatialLeviCivita h y a i j) x :=
  contDiffAt_const.mul (ContDiffAt.sum fun l _ => (sm_inv hp hc a l).mul
    (((sm_pd (hc l j) i).add (sm_pd (hc l i) j)).sub (sm_pd (hc i j) l)))

private lemma sm_grad {h : X → Mat} {N : X → ℝ} {x : X} (hp : (h x).PosDef)
    (hc : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (cn : ContDiffAt ℝ ∞ N x) (a : I) :
    ContDiffAt ℝ ∞ (staticRaisedGradient N h a) x :=
  ContDiffAt.sum fun j _ => (sm_inv hp hc a j).mul (sm_pd cn j)

private lemma sym_h {h : X → Mat} {W : Set X} (ow : IsOpen W)
    (hp : ∀ y ∈ W, (h y).PosDef) {x : X} (hx : x ∈ W) (i j k : I) :
    pd i (fun y => h y j k) x = pd i (fun y => h y k j) x := by
  have ev : (fun y => h y j k) =ᶠ[𝓝 x] (fun y => h y k j) := (show ∀ᶠ y in 𝓝 x, y ∈ W from ow.mem_nhds hx).mono
    (fun y hy => by simpa only [star_trivial] using (hp y hy).isHermitian.apply k j)
  exact congrArg (fun L : X →L[ℝ] ℝ => L (bvec i)) ev.fderiv_eq

private lemma pd_sum {f : I → X → ℝ} {x : X} (df : ∀ j, DifferentiableAt ℝ (f j) x) (i : I) :
    pd i (fun y => ∑ j, f j y) x = ∑ j, pd i (f j) x := by
  unfold pd spatialADMPartial
  rw [fderiv_fun_sum (fun j _ => df j)]
  simp

private lemma pd_mul {f g : X → ℝ} {x : X} (df : DifferentiableAt ℝ f x) (dg : DifferentiableAt ℝ g x) (i : I) :
    pd i (fun y => f y*g y) x = pd i f x*g x + f x*pd i g x := by
  have v := (df.hasFDerivAt.mul dg.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f y*g y) x = _ at v
  unfold pd spatialADMPartial
  rw [v]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

private abbrev I3 := Fin 3
private abbrev I4 := Fin 4
private noncomputable abbrev e (i : I4) : X := Fin.cases 0 bvec i
private noncomputable abbrev d (i : I4) (f : X → ℝ) (x : X) := fderiv ℝ f x (e i)

private noncomputable def projS : E4 →L[ℝ] X :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i : I3 => PiLp.proj 2 (fun _ : I4 => ℝ) i.succ))

private lemma proj_eq (z : E4) : projS z = conformalSpatialPoint z := by
  ext i
  fin_cases i <;> rfl

private lemma proj_basis (i : I4) : projS (coordBasis i) = e i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · ext a
    change (EuclideanSpace.single (0:I4) (1:ℝ)) a.succ = 0
    simp [PiLp.single_apply]
  · ext a
    change (EuclideanSpace.single j.succ (1:ℝ)) a.succ = (EuclideanSpace.single j (1:ℝ)) a
    simp [PiLp.single_apply]

private lemma lift_d (f : X → ℝ) (p : I4) (z : E4) (hf : DifferentiableAt ℝ f (projS z)) :
    coordPartial (fun w => f (projS w)) p z = d p f (projS z) := by
  unfold coordPartial d
  have hh := (hf.hasFDerivAt.comp z projS.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f (projS y)) z = _ at hh
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply,proj_basis]

private def blk (t : ℝ) (m : Mat) : Matrix I4 I4 ℝ := fun a b =>
  Fin.cases (Fin.cases t (fun _ => 0) b) (fun i => Fin.cases 0 (fun j => m i j) b) a

private lemma split_four (f : I4 → ℝ) : (∑ l, f l)=f 0+∑ k : I, f k.succ := Fin.sum_univ_succ f

private lemma inverse_block (N : X → ℝ) (h : X → Mat) (z : E4) (nz : N (projS z) ≠ 0)
    (ph : (h (projS z)).PosDef) : invMetric (staticCartesianBlock N h) z =
    blk (-(N (projS z)^2)⁻¹) (h (projS z))⁻¹ := by
  let x := projS z
  have eq : staticCartesianBlock N h z = blk (-(N x)^2) (h x) := by change _ = blk (-(N (projS z))^2) (h (projS z)); rw [proj_eq]; rfl
  have mi := Matrix.mul_nonsing_inv (h x) ((h x).isUnit_iff_isUnit_det.mp ph.isUnit)
  unfold invMetric
  rw [eq]
  apply Matrix.inv_eq_right_inv
  ext a b
  induction a using Fin.cases <;> induction b using Fin.cases
  all_goals rw [Matrix.mul_apply,split_four]
  all_goals simp only [blk,Fin.cases_zero,Fin.cases_succ,zero_mul,mul_zero,Finset.sum_const_zero,
    zero_add,add_zero]
  · change (-(N (projS z))^2) * (-(N (projS z)^2)⁻¹) = _
    simp [nz]
  · simp [Matrix.one_apply,Ne.symm (Fin.succ_ne_zero _)]
  · simp [Matrix.one_apply]
  · rename_i i j
    have e := congrArg (fun A : Mat => A i j) mi
    simpa only [Matrix.mul_apply,Matrix.one_apply,Fin.succ_inj] using e

private def con (N : X → ℝ) (h : X → Mat) (a b c : I4) (x : X) : ℝ :=
  Fin.cases
    (Fin.cases (Fin.cases 0 (fun l => pd l N x / N x) c)
      (fun k => Fin.cases (pd k N x / N x) (fun _ => 0) c) b)
    (fun i => Fin.cases (Fin.cases (N x * staticRaisedGradient N h i x) (fun _ => 0) c)
      (fun k => Fin.cases 0 (fun l => spatialLeviCivita h x i k l) c) b) a

private def uD (p : I4) (f : X → ℝ) (x : X) : ℝ := Fin.cases 0 (fun k => pd k f x) p

private lemma liftUD (f : X → ℝ) (p : I4) (z : E4) (df : DifferentiableAt ℝ f (projS z)) :
    coordPartial (fun y => f (projS y)) p z = uD p f (projS z) := by
  rw [lift_d _ _ _ df]
  refine Fin.cases ?_ (fun _ => rfl) p
  simp [d,e,uD]

private lemma connection_static (N : X → ℝ) (h : X → Mat) (z : E4)
    (cn : ContDiffAt ℝ ∞ N (projS z)) (ch : ∀ a b, ContDiffAt ℝ ∞ (fun y => h y a b) (projS z))
    (ph : (h (projS z)).PosDef) (nz : N (projS z) ≠ 0) (a b c : I4) :
    christoffel (staticCartesianBlock N h) z a b c = con N h a b c (projS z) := by
  let x := projS z
  have val (w : E4) : staticCartesianBlock N h w = blk (-(N (projS w))^2) (h (projS w)) := by rw [proj_eq]; rfl
  have der (i j p : I4) : coordPartial (fun w => staticCartesianBlock N h w i j) p z =
      blk (-2*N x*uD p N x) (fun k l => uD p (fun y => h y k l) x) i j := by
    simp_rw [val]
    induction i using Fin.cases <;> induction j using Fin.cases
    · change coordPartial (fun w => -(N (projS w))^2) p z = _
      have dn := cn.differentiableAt (by simp)
      have ds := (dn.hasFDerivAt.pow 2).neg
      rw [liftUD (fun y => -(N y)^2) p z ds.differentiableAt]
      refine Fin.cases ?_ (fun k => ?_) p
      · change 0 = _ * 0
        ring
      · change fderiv ℝ (fun y => -(N y)^2) x (bvec k) = -2*N x*fderiv ℝ N x (bvec k)
        have dd := ds.fderiv
        change fderiv ℝ (fun y => -(N y)^2) x = _ at dd
        rw [dd]
        simp <;> ring
    · change coordPartial (fun _ => 0) p z = 0
      simp [coordPartial]
    · change coordPartial (fun _ => 0) p z = 0
      simp [coordPartial]
    · rename_i i j
      exact liftUD (fun y => h y i j) p z ((ch i j).differentiableAt (by simp))
  have ib := inverse_block N h z nz ph
  unfold christoffel
  simp only [ib,der,split_four]
  induction a using Fin.cases <;> induction b using Fin.cases <;> induction c using Fin.cases
  all_goals simp only [con,blk,uD,Fin.cases_succ,Fin.cases_zero,zero_add,add_zero,
    zero_sub,sub_zero,zero_mul,mul_zero,Finset.sum_const_zero,mul_neg,neg_mul,neg_neg]
  all_goals try simp only [spatialLeviCivita,staticRaisedGradient,Fin.sum_univ_three,x,pd]
  all_goals field_simp [nz] <;> ring

private lemma smooth_con (N : X → ℝ) (h : X → Mat) (x : X) (cn : ContDiffAt ℝ ∞ N x)
    (ch : ∀ a b, ContDiffAt ℝ ∞ (fun y => h y a b) x) (ph : (h x).PosDef) (nz : N x≠0)
    (a b c : I4) : ContDiffAt ℝ ∞ (con N h a b c) x := by
  induction a using Fin.cases <;> induction b using Fin.cases <;> induction c using Fin.cases
  all_goals first | exact contDiffAt_const | exact (sm_pd cn _).div cn nz |
    exact cn.mul (sm_grad ph ch cn _) | exact sm_ch ph ch _ _ _

theorem solution (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hn : ContDiffOn ℝ ∞ N W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (nz : N x ≠ 0) :
    ricci (staticCartesianBlock N h) (staticTimeZero x) 0 0 =
      N x * ∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian N h i j x ∧
    ∀ i j : Fin 3, ricci (staticCartesianBlock N h) (staticTimeZero x) i.succ j.succ =
      spatialRicciTensor h x i j - staticSpatialHessian N h j i x / N x := by
  classical
  let z := staticTimeZero x
  have px : projS z=x := by ext k; fin_cases k <;> rfl
  have nW := hw.mem_nhds hx
  have cn := hn.contDiffAt nW
  have ch (a b : I) := (hh a b).contDiffAt nW
  have v (a b c : I4) : christoffel (staticCartesianBlock N h) z a b c = con N h a b c x := by
    simpa only [px] using connection_static N h z (px.symm ▸ cn) (px.symm ▸ ch)
      (px.symm ▸ hp x hx) (px.symm ▸ nz) a b c
  have td : Tendsto projS (𝓝 z) (𝓝 x) := px ▸ projS.continuous.continuousAt.tendsto
  have nn : ∀ᶠ y in 𝓝 x, N y ≠ 0 := cn.continuousAt.tendsto (isOpen_compl_singleton.mem_nhds nz)
  have dd (p a b c : I4) : coordPartial (fun w => christoffel (staticCartesianBlock N h) w a b c) p z =
      uD p (con N h a b c) x := by
    have ev : (fun w => christoffel (staticCartesianBlock N h) w a b c) =ᶠ[𝓝 z]
        (fun w => con N h a b c (projS w)) := by
      filter_upwards [td nW,td.eventually nn] with w inW notzero
      exact connection_static N h w (hn.contDiffAt (hw.mem_nhds inW))
        (fun i j => (hh i j).contDiffAt (hw.mem_nhds inW)) (hp _ inW) notzero a b c
    calc
      _ = coordPartial (fun w => con N h a b c (projS w)) p z :=
        congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis p)) ev.fderiv_eq
      _ = _ := by rw [liftUD _ _ _ (px.symm ▸ (smooth_con N h x cn ch (hp x hx) nz a b c).differentiableAt (by simp)),px]
  let U := fun i : I => (fun y => pd i N y / N y)
  let V := staticRaisedGradient N h
  have c000 : con N h 0 0 0 = fun _ => 0 := rfl
  have c0s0 (i : I) : con N h 0 i.succ 0 = U i := rfl
  have c00s (i : I) : con N h 0 0 i.succ = U i := rfl
  have c0ss (i j : I) : con N h 0 i.succ j.succ = fun _ => 0 := rfl
  have cs00 (i : I) : con N h i.succ 0 0 = fun y => N y * V i y := rfl
  have cs0s (i j : I) : con N h i.succ 0 j.succ = fun _ => 0 := rfl
  have css0 (i j : I) : con N h i.succ j.succ 0 = fun _ => 0 := rfl
  have csss (i j k : I) : con N h i.succ j.succ k.succ = fun y => spatialLeviCivita h y i j k := rfl
  have d0 (i : I) : pd i (fun _ => 0) x = 0 := by simp [pd,spatialADMPartial]
  have time :
      ricci (staticCartesianBlock N h) z 0 0 =
      ∑ i : I, (pd i (fun y => N y*V i y) x - N x*V i x*U i x +
        ∑ l : I, spatialLeviCivita h x i i l * (N x*V l x)) := by
    simp only [ricci,riemann,dd,v,split_four,c000,c0s0,c00s,c0ss,cs00,cs0s,css0,csss,d0,uD,Fin.cases_zero,Fin.cases_succ,
      mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero,sub_self,Finset.sum_const_zero,
      Fin.sum_univ_three,U,V]
    ring
  have space (i j : I) : ricci (staticCartesianBlock N h) z i.succ j.succ =
      spatialRicciTensor h x i j - pd j (U i) x +
      (∑ l : I, U l x * spatialLeviCivita h x l j i) - U j x * U i x := by
    simp only [ricci,riemann,dd,v,split_four,spatialRicciTensor,c000,c0s0,c00s,c0ss,cs00,cs0s,css0,csss,d0,uD,Fin.cases_zero,Fin.cases_succ,
      mul_zero,zero_mul,zero_add,add_zero,zero_sub,sub_zero,sub_self,Finset.sum_const_zero,
      Fin.sum_univ_three,U,pd]
    ring
  constructor
  · change ricci (staticCartesianBlock N h) z 0 0 = _
    rw [time,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have eq := (static_lapse_gradient_covariant_derivative N h W hw hn hh hp x hx i).1 i
    change pd i (V i) x + (∑ l : I, spatialLeviCivita h x i i l * V l x) = _ at eq
    rw [←eq,pd_mul (cn.differentiableAt (by simp)) ((sm_grad (hp x hx) ch cn i).differentiableAt (by simp))]
    simp only [U,Fin.sum_univ_three]
    field_simp [nz] <;> ring
  · intro i j
    change ricci (staticCartesianBlock N h) z i.succ j.succ = _
    rw [space]
    have prod : (fun y => U i y * N y) =ᶠ[𝓝 x] pd i N := nn.mono (fun y hy => div_mul_cancel₀ _ hy)
    have dprod := congrArg (fun L : X →L[ℝ] ℝ => L (bvec j)) prod.fderiv_eq
    change pd j (fun y => U i y * N y) x = pd j (pd i N) x at dprod
    have su : DifferentiableAt ℝ (U i) x := ((sm_pd cn i).div cn nz).differentiableAt (by simp)
    rw [pd_mul (f:=U i) (g:=N) su (cn.differentiableAt (by simp)) j] at dprod
    have du : pd j (U i) x = (pd j (pd i N) x * N x - pd i N x * pd j N x)/(N x)^2 := by
      rw [show U i x = pd i N x / N x from rfl] at dprod
      field_simp [nz] at dprod ⊢
      linear_combination dprod
    rw [du]
    simp only [staticSpatialHessian,Fin.sum_univ_three,U,pd]
    field_simp [nz] <;> ring
