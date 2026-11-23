-- Prove2me | solution 1 for NoHair.asymptotic_static_cartesian_ricci_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:53:17.42668+00:00
-- url     : https://prove2.me/submissions/565c08cc-522b-444b-8ca0-f28133c66861

import Definitions.Def_NoHair_staticCartesianRicci

open NoHair Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

private abbrev X := ADMPoint
private abbrev I4 := Fin 4
private abbrev I3 := Fin 3
private abbrev V := I4 → I4 → ℝ
private abbrev M4 := Matrix I4 I4 ℝ
private abbrev M3 := Matrix I3 I3 ℝ
private noncomputable abbrev e (i : I4) : X := Fin.cases 0 (fun a => EuclideanSpace.single a 1) i
private noncomputable abbrev d (i : I4) (f : X → ℝ) (x : X) := fderiv ℝ f x (e i)
private noncomputable abbrev s0 : V := (1 : M4)
private noncomputable def field (N : X → ℝ) (h : X → M3) (x : X) : V :=
  fun i j => Fin.cases (Fin.cases (N x) (fun _ => 0) j)
    (fun a => Fin.cases 0 (fun b => h x a b) j) i
private noncomputable def block (q : V) : M4 :=
  fun i j => if i = 0 ∧ j = 0 then -(q i j)^2 else q i j
private noncomputable def kinSlope (q : V) (a b : I4) : ℝ :=
  if a = 0 ∧ b = 0 then -2 * q a b else 1
private noncomputable def coeff (i l a b : I4) (q : V) : ℝ :=
  (1/2 : ℝ) * (block q)⁻¹ i l * kinSlope q a b

private lemma flat_block : block s0 = minkowski := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [block,minkowski,s0,Matrix.one_apply,Matrix.diagonal_apply]

private lemma flat_inv : (block s0)⁻¹ = minkowski := by
  rw [flat_block]
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [minkowski,Matrix.mul_apply,Matrix.diagonal_apply,
    Matrix.one_apply,Fin.sum_univ_four]

private lemma smooth_block (i j : I4) : ContDiff ℝ ∞ (fun q : V => block q i j) := by
  by_cases t : i=0 ∧ j=0
  · simp_rw [block,if_pos t]; fun_prop
  · simp_rw [block,if_neg t]; fun_prop

private lemma smooth_coeff (i l a b : I4) : ContDiffAt ℝ 1 (coeff i l a b) s0 := by
  have detSmooth {n : Type} [Fintype n] [DecidableEq n] (G : V → Matrix n n ℝ)
      (cG : ∀ k m, ContDiff ℝ ∞ (fun q => G q k m)) :
      ContDiff ℝ ∞ (fun q => (G q).det) := by
    simp_rw [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    have pr (t : Finset n) : ContDiff ℝ ∞ (fun q => ∏ j ∈ t, G q (σ j) j) := by
      induction t using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (contDiff_const : ContDiff ℝ ∞ (fun _ : V => (1:ℝ)))
      | @insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (cG _ _).mul ih
    exact contDiff_const.mul (pr Finset.univ)
  have ds := detSmooth (n:=I4) (fun q => block q) (fun i j => smooth_block i j)
  have det0 : (block s0).det ≠ 0 := by
    rw [flat_block]
    norm_num [minkowski,Matrix.det_diagonal,Fin.prod_univ_succ]
  have adj : ContDiff ℝ ∞ (fun q : V => (block q).adjugate i l) := by
    simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    exact contDiff_const.mul (detSmooth (n:=I3) (fun q => (block q).submatrix l.succAbove i.succAbove)
      (fun k m => smooth_block _ _))
  have inv : ContDiffAt ℝ ∞ (fun q : V => (block q)⁻¹ i l) s0 := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact (ds.contDiffAt.inv det0).mul adj.contDiffAt
  have sl : ContDiff ℝ ∞ (fun q : V => kinSlope q a b) := by
    by_cases t : a=0 ∧ b=0
    · simp_rw [kinSlope,if_pos t]; fun_prop
    · simp_rw [kinSlope,if_neg t]; fun_prop
  exact ((contDiffAt_const.mul inv).mul sl.contDiffAt).of_le (by simp)

private lemma uniform_coeff :
    ∃ ε K : ℝ, 0 < ε ∧ 0 < K ∧ ∀ q : V, ‖q-s0‖ < ε → ∀ i l a b : I4,
      DifferentiableAt ℝ (coeff i l a b) q ∧
      |coeff i l a b q| ≤ K ∧ ‖fderiv ℝ (coeff i l a b) q‖ ≤ K ∧
      |coeff i l a b q - coeff i l a b s0| ≤ K * ‖q-s0‖ := by
  classical
  let I := I4 × I4 × I4 × I4
  let F := fun t : I => coeff t.1 t.2.1 t.2.2.1 t.2.2.2
  have per (t : I) : ∃ k : ℝ, ∀ᶠ q in 𝓝 s0,
      DifferentiableAt ℝ (F t) q ∧ |F t q| ≤ k ∧ ‖fderiv ℝ (F t) q‖ ≤ k ∧
      |F t q-F t s0| ≤ k*‖q-s0‖ := by
    have hf : ContDiffAt ℝ 1 (F t) s0 := smooth_coeff _ _ _ _
    obtain ⟨L,U,hU,hL⟩ := hf.exists_lipschitzOnWith
    let k : ℝ := max (L:ℝ) (max (|F t s0|+1) (‖fderiv ℝ (F t) s0‖+1))
    refine ⟨k,?_⟩
    have v := hf.continuousAt.abs.tendsto.eventually_lt_const (lt_add_one |F t s0|)
    have w := (hf.continuousAt_fderiv (by norm_num)).norm.tendsto.eventually_lt_const
      (lt_add_one ‖fderiv ℝ (F t) s0‖)
    filter_upwards [hf.eventually (by decide),v,w,hU] with q diff val der mem
    refine ⟨diff.differentiableAt one_ne_zero,val.le.trans ((le_max_left _ _).trans (le_max_right _ _)),
      der.le.trans ((le_max_right _ _).trans (le_max_right _ _)),?_⟩
    have h := hL.dist_le_mul q mem s0 (mem_of_mem_nhds hU)
    exact (show |F t q-F t s0| ≤ (L:ℝ)*‖q-s0‖ by simpa only [dist_eq_norm,Real.norm_eq_abs] using h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  choose k hk using per
  let K := (∑ t : I, |k t|)+1
  have Kpos : 0<K := by dsimp only [K]; positivity
  have dom (t : I) : k t ≤ K := by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (k j)) (Finset.mem_univ t)
    dsimp only [K]
    linarith only [le_abs_self (k t),h]
  obtain ⟨ε,εp,hε⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.mpr hk)
  refine ⟨ε,K,εp,Kpos,?_⟩
  intro q hq i l a b
  let t : I := ⟨i,l,a,b⟩
  have h := hε (show q ∈ Metric.ball s0 ε by simpa only [Metric.mem_ball,dist_eq_norm] using hq) t
  exact ⟨h.1,h.2.1.trans (dom t),h.2.2.1.trans (dom t),
    h.2.2.2.trans (mul_le_mul_of_nonneg_right (dom t) (norm_nonneg _))⟩

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

private lemma d_const (p : I4) (u : ℝ) : d p (fun _ => u) = fun _ => 0 := by
  funext x
  simp [d]

private lemma d_time (f : X → ℝ) : d 0 f = fun _ => 0 := by
  funext x
  simp [d,e]

private lemma lift_d (f : X → ℝ) (p : I4) (z : E4) (hf : DifferentiableAt ℝ f (projS z)) :
    coordPartial (fun w => f (projS w)) p z = d p f (projS z) := by
  unfold coordPartial d
  have hh := (hf.hasFDerivAt.comp z projS.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => f (projS y)) z = _ at hh
  rw [hh]
  simp only [ContinuousLinearMap.comp_apply,proj_basis]

private lemma norm_e (i : I4) : ‖e i‖ ≤ 1 := by
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [e]
  · simp [e]

private lemma diff_part {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (p : I4) :
    DifferentiableAt ℝ (d p f) x :=
  ((hf.fderiv_right (m:=∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)

private lemma second_eq {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (p q : I4) :
    d p (d q f) x = iteratedFDeriv ℝ 2 f x ![e p,e q] := by
  have df := (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  unfold d
  rw [fderiv_clm_apply (u:=fun _ : X => e q) df (differentiableAt_const _),
    iteratedFDeriv_two_apply]
  simp

private lemma first_second_bounds {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (u decayConst : ℝ) (h₁ : ‖iteratedFDeriv ℝ 1 (fun y => f y-u) x‖ ≤ decayConst/‖x‖^2)
    (h₂ : ‖iteratedFDeriv ℝ 2 (fun y => f y-u) x‖ ≤ decayConst/‖x‖^3) (p q : I4) :
    |d p f x| ≤ decayConst / ‖x‖^2 ∧ |d p (d q f) x| ≤ decayConst / ‖x‖^3 := by
  simp only [norm_iteratedFDeriv_one,fderiv_sub_const] at h₁
  have df := (fderiv ℝ f x).le_opNorm (e p)
  have b₁ := df.trans (mul_le_of_le_one_right (norm_nonneg _) (norm_e _))
  refine ⟨b₁.trans h₁,?_⟩
  let g := fun y => f y-u
  have de : d q g = d q f := by funext y; simp only [d,g,fderiv_sub_const]
  rw [← de,second_eq (hf.sub contDiffAt_const)]
  have op := (iteratedFDeriv ℝ 2 g x).le_opNorm ![e p,e q]
  have w : (∏ i : Fin 2, ‖(![e p,e q] : Fin 2 → X) i‖) ≤ 1 := by
    simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using
      mul_le_one₀ (norm_e p) (norm_nonneg _) (norm_e q)
  exact (op.trans (mul_le_of_le_one_right (norm_nonneg _) w)).trans h₂

private lemma field_coords (N : X → ℝ) (h : X → M3) (x : X)
    (hn : ContDiffAt ℝ ∞ N x) (hh : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (a b : I4) :
    ContDiffAt ℝ ∞ (fun y => field N h y a b) x := by
  refine Fin.cases ?_ (fun i => ?_) a
  · refine Fin.cases hn (fun j => contDiffAt_const) b
  · refine Fin.cases contDiffAt_const (fun j => hh i j) b

private lemma field_bounds (N : X → ℝ) (h : X → M3) (x : X) (decayConst : ℝ) (cpos : 0<decayConst)
    (hn : ContDiffAt ℝ ∞ N x) (hh : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x)
    (dec : ∀ k : ℕ, k ≤ 2 →
      ‖iteratedFDeriv ℝ k (fun y => N y-1) x‖ ≤ decayConst/‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : M3) i j) x‖ ≤ decayConst/‖x‖^(k+1)) :
    ‖field N h x - s0‖ ≤ decayConst/‖x‖ ∧
    (∀ p : I4, ‖fderiv ℝ (field N h) x (e p)‖ ≤ decayConst/‖x‖^2) ∧
    (∀ p q a b : I4, |d p (fun y => field N h y a b) x| ≤ decayConst/‖x‖^2 ∧
      |d p (d q (fun y => field N h y a b)) x| ≤ decayConst/‖x‖^3) := by
  have h0 := dec 0 (by decide)
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,Nat.zero_add,pow_one] at h0
  have h1 := dec 1 (by decide)
  have h2 := dec 2 (by decide)
  have zbound (p q : I4) : |d p (fun _ => 0) x| ≤ decayConst/‖x‖^2 ∧
      |d p (d q (fun _ => 0)) x| ≤ decayConst/‖x‖^3 := by
    have zp : d p (fun _ => (0:ℝ)) x = 0 := congrFun (d_const p 0) x
    have zz : d p (d q (fun _ => (0:ℝ))) x = 0 := by
      rw [d_const q 0]
      exact zp
    rw [zz,zp,abs_zero]
    constructor <;> positivity
  have jets (p q a b : I4) : |d p (fun y => field N h y a b) x| ≤ decayConst/‖x‖^2 ∧
      |d p (d q (fun y => field N h y a b)) x| ≤ decayConst/‖x‖^3 := by
    refine Fin.cases ?_ (fun i => ?_) a
    · refine Fin.cases (first_second_bounds hn 1 decayConst h1.1 h2.1 p q) (fun _ => zbound p q) b
    · refine Fin.cases (zbound p q) (fun j => first_second_bounds (hh i j) _ decayConst (h1.2 i j) (h2.2 i j) p q) b
  have ca (a b : I4) := field_coords N h x hn hh a b
  have cd : DifferentiableAt ℝ (field N h) x := differentiableAt_pi.mpr
    (fun a => differentiableAt_pi.mpr (fun b => (ca a b).differentiableAt (by simp)))
  constructor
  · apply (pi_norm_le_iff_of_nonempty _).mpr
    intro a
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro b
    change |field N h x a b - (1 : M4) a b| ≤ decayConst/‖x‖
    refine Fin.cases ?_ (fun i => ?_) a
    · refine Fin.cases ?_ (fun j => ?_) b
      · simpa [field,s0,Matrix.one_apply] using h0.1
      · change |(0 : ℝ) - (1 : M4) 0 j.succ| ≤ decayConst/‖x‖
        rw [Matrix.one_apply,if_neg (Fin.succ_ne_zero j).symm,sub_zero,abs_zero]
        exact div_nonneg cpos.le (norm_nonneg _)
    · refine Fin.cases ?_ (fun j => ?_) b
      · change |(0 : ℝ) - (1 : M4) i.succ 0| ≤ decayConst/‖x‖
        rw [Matrix.one_apply,if_neg (Fin.succ_ne_zero i),sub_zero,abs_zero]
        exact div_nonneg cpos.le (norm_nonneg _)
      · simpa [field,s0,Matrix.one_apply] using h0.2 i j
  refine ⟨?_,jets⟩
  intro p
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro a
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro b
  have row := (differentiableAt_pi.mp cd a)
  have comp : d p (fun y => field N h y a b) x = (fderiv ℝ (field N h) x (e p)) a b := by
    unfold d
    rw [fderiv_apply row b,fderiv_apply cd a]
    rfl
  simpa only [comp,Real.norm_eq_abs] using (jets p 0 a b).1

private noncomputable def piece (S : X → V) (i l a b p : I4) (x : X) :=
  coeff i l a b (S x) * d p (fun y => S y a b) x

private noncomputable def gamma (S : X → V) (i j k : I4) (x : X) :=
  ∑ l : I4, (piece S i l l k j x + piece S i l l j k x - piece S i l j k l x)

private noncomputable def flatD (S : X → V) (t i j k : I4) (x : X) :=
  ∑ l : I4, (coeff i l l k s0 * d t (d j (fun y => S y l k)) x +
    coeff i l l j s0 * d t (d k (fun y => S y l j)) x -
    coeff i l j k s0 * d t (d l (fun y => S y j k)) x)

private lemma block_coord (N : X → ℝ) (h : X → M3) (z : E4) :
    staticCartesianBlock N h z = block (field N h (projS z)) := by
  rw [proj_eq]
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i
  · refine Fin.cases ?_ (fun b => ?_) j <;> simp [staticCartesianBlock,field,block]
  · refine Fin.cases ?_ (fun b => ?_) j <;> simp [staticCartesianBlock,field,block]

private lemma gamma_eq (N : X → ℝ) (h : X → M3) (z : E4)
    (hn : ContDiffAt ℝ ∞ N (projS z))
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) (projS z)) (i j k : I4) :
    christoffel (staticCartesianBlock N h) z i j k = gamma (field N h) i j k (projS z) := by
  let S := field N h
  let x := projS z
  have der (a b p : I4) : coordPartial (fun w => staticCartesianBlock N h w a b) p z =
      kinSlope (S x) a b * d p (fun y => S y a b) x := by
    have hf : DifferentiableAt ℝ (fun y => S y a b) x :=
      (field_coords N h x hn hh a b).differentiableAt (by simp)
    have beq : (fun w => staticCartesianBlock N h w a b) =
        (fun w => block (S (projS w)) a b) := funext fun w =>
      congrArg (fun A : M4 => A a b) (block_coord N h w)
    rw [beq]
    by_cases t : a=0 ∧ b=0
    · simp only [block,kinSlope,if_pos t]
      let f := fun y => S y a b
      have hd := (hf.hasFDerivAt.pow 2).neg
      rw [lift_d (fun y => -(f y)^2) p z hd.differentiableAt]
      unfold d
      change fderiv ℝ (fun y => -(f y)^2) x (e p) = _
      have v := hd.fderiv
      change fderiv ℝ (fun y => -(f y)^2) x = _ at v
      rw [v]
      simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      norm_num [f] <;> ring
    · simp only [block,kinSlope,if_neg t,one_mul]
      exact lift_d (fun y => S y a b) p z hf
  unfold christoffel gamma
  apply Finset.sum_congr rfl
  intro l _
  rw [der l k j,der l j k,der j k l]
  have inverse : invMetric (staticCartesianBlock N h) z = (block (S x))⁻¹ :=
    congrArg (fun A : M4 => A⁻¹) (block_coord N h z)
  rw [inverse]
  dsimp only [piece,coeff,S,x]
  ring

private lemma dir_add {f g : X → ℝ} {x : X} (a : DifferentiableAt ℝ f x)
    (b : DifferentiableAt ℝ g x) (p : I4) :
    d p (fun y => f y+g y) x = d p f x + d p g x := by
  unfold d
  rw [fderiv_fun_add a b]
  rfl

private lemma dir_sub {f g : X → ℝ} {x : X} (a : DifferentiableAt ℝ f x)
    (b : DifferentiableAt ℝ g x) (p : I4) :
    d p (fun y => f y-g y) x = d p f x - d p g x := by
  unfold d
  rw [fderiv_fun_sub a b]
  rfl

private lemma dir_sum {f : I4 → X → ℝ} {x : X} (hf : ∀ j, DifferentiableAt ℝ (f j) x) (p : I4) :
    d p (fun y => ∑ j, f j y) x = ∑ j, d p (f j) x := by
  unfold d
  rw [fderiv_fun_sum (fun j _ => hf j)]
  simp

private lemma sum4 (f : I4 → ℝ) (c : ℝ) (h : ∀ i, |f i| ≤ c) : |∑ i, f i| ≤ 4*c := calc
  _ ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
  _ ≤ ∑ _i : I4, c := Finset.sum_le_sum fun i _ => h i
  _ = _ := by simp

private lemma three_bounds {a b c D : ℝ} (ha : |a| ≤ D) (hb : |b| ≤ D) (hc : |c| ≤ D) :
    |a+b-c| ≤ 3*D := by
  linarith only [abs_sub (a+b) c,abs_add_le a b,ha,hb,hc]

private lemma gamma_bounds (S : X → V) (x : X) (decayConst K r : ℝ) (rp : 0<r) (cp : 0<decayConst) (kp : 0<K)
    (smooth : ∀ a b, ContDiffAt ℝ ∞ (fun y => S y a b) x)
    (near : ‖S x-s0‖ ≤ decayConst/r)
    (first : ∀ t : I4, ‖fderiv ℝ S x (e t)‖ ≤ decayConst/r^2)
    (jets : ∀ p q a b : I4, |d p (fun y => S y a b) x| ≤ decayConst/r^2 ∧
      |d p (d q (fun y => S y a b)) x| ≤ decayConst/r^3)
    (co : ∀ i l a b, DifferentiableAt ℝ (coeff i l a b) (S x) ∧ |coeff i l a b (S x)| ≤ K ∧
        ‖fderiv ℝ (coeff i l a b) (S x)‖ ≤ K ∧ |coeff i l a b (S x)-coeff i l a b s0| ≤ K*‖S x-s0‖)
    (p i j k : I4) :
    DifferentiableAt ℝ (gamma S i j k) x ∧ |gamma S i j k x| ≤ 12*K*decayConst/r^2 ∧
    |d p (gamma S i j k) x - flatD S p i j k x| ≤ 24*K*decayConst^2/r^4 := by
  have ds : DifferentiableAt ℝ S x := differentiableAt_pi.mpr (fun a => differentiableAt_pi.mpr
    (fun b => (smooth a b).differentiableAt (by simp)))
  let U := fun (a b:I4) => (fun y => S y a b)
  have pv (l a b q : I4) : DifferentiableAt ℝ (piece S i l a b q) x ∧
      |piece S i l a b q x| ≤ K*decayConst/r^2 ∧
      |d p (piece S i l a b q) x - coeff i l a b s0 * d p (d q (U a b)) x| ≤ 2*K*decayConst^2/r^4 := by
    let f := coeff i l a b
    have h := co i l a b
    have hc : HasFDerivAt (fun y => f (S y)) ((fderiv ℝ f (S x)).comp (fderiv ℝ S x)) x :=
      h.1.hasFDerivAt.comp x ds.hasFDerivAt
    have dq := diff_part (smooth a b) q
    have prod := hc.mul dq.hasFDerivAt
    refine ⟨prod.differentiableAt,?_,?_⟩
    · unfold piece
      rw [abs_mul]
      calc _ ≤ K * (decayConst / r^2) := mul_le_mul h.2.1 (jets q q a b).1 (abs_nonneg _) kp.le
           _ = _ := by ring
    · let A := fderiv ℝ f (S x) (fderiv ℝ S x (e p))
      have hA : |A| ≤ K*(decayConst/r^2) :=
        ((fderiv ℝ f (S x)).le_opNorm _).trans
          (mul_le_mul h.2.2.1 (first p) (norm_nonneg _) kp.le)
      have hB : |f (S x)-f s0| ≤ K*(decayConst/r) := h.2.2.2.trans (mul_le_mul_of_nonneg_left near kp.le)
      have eq : d p (piece S i l a b q) x - f s0 * d p (d q (U a b)) x =
          A * d q (U a b) x + (f (S x)-f s0)*d p (d q (U a b)) x := by
        unfold d
        have v := prod.fderiv
        change fderiv ℝ (piece S i l a b q) x = _ at v
        rw [v]
        simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
          ContinuousLinearMap.comp_apply]
        dsimp only [A, f, U]
        ring
      change |d p (piece S i l a b q) x - f s0 * d p (d q (U a b)) x| ≤ _
      rw [eq]
      apply (abs_add_le _ _).trans
      rw [abs_mul,abs_mul]
      calc _ ≤ (K*(decayConst/r^2))*(decayConst/r^2)+(K*(decayConst/r))*(decayConst/r^3) := add_le_add
               (mul_le_mul hA (jets q q a b).1 (abs_nonneg _) (by positivity))
               (mul_le_mul hB (jets p q a b).2 (abs_nonneg _) (by positivity))
           _ = _ := by field_simp; ring
  let term := fun l (y : X) => piece S i l l k j y + piece S i l l j k y - piece S i l j k l y
  have dt (l : I4) : DifferentiableAt ℝ (term l) x :=
    ((pv l l k j).1.add (pv l l j k).1).sub (pv l j k l).1
  refine ⟨DifferentiableAt.fun_sum (fun l _ => dt l),?_,?_⟩
  · exact (sum4 (fun l => term l x) _ (fun l => three_bounds (pv l l k j).2.1
      (pv l l j k).2.1 (pv l j k l).2.1)).trans_eq (by ring)
  · change |d p (fun y => ∑ l, term l y) x - _| ≤ _
    rw [dir_sum dt,flatD,← Finset.sum_sub_distrib]
    apply (sum4 _ (3*(2*K*decayConst^2/r^4)) ?_).trans_eq (by ring)
    intro l
    have addD : DifferentiableAt ℝ (fun y => piece S i l l k j y+piece S i l l j k y) x :=
      (pv l l k j).1.add (pv l l j k).1
    dsimp only [term]
    rw [dir_sub addD (pv l j k l).1,dir_add (pv l l k j).1 (pv l l j k).1]
    convert three_bounds (pv l l k j).2.2 (pv l l j k).2.2 (pv l j k l).2.2 using 2 <;> ring

private noncomputable def flatR (S : X → V) (i j : I4) (x : X) :=
  ∑ t : I4, (flatD S t t j i x - flatD S j t t i x)

private abbrev Jet := I4 → I4 → I4 → I4 → ℝ

private def baseCoef (i l a b : I4) : ℝ :=
  (1/2 : ℝ) * minkowski i l * (if a=0 ∧ b=0 then -2 else 1)

private lemma coeff0 (i l a b : I4) : coeff i l a b s0 = baseCoef i l a b := by
  unfold coeff baseCoef
  rw [flat_inv]
  by_cases t : a=0 ∧ b=0
  · rcases t with ⟨rfl,rfl⟩
    norm_num [kinSlope,s0,Matrix.one_apply]
  · simp only [kinSlope,t,if_false]

private def dc0 (J : Jet) (t i j k : I4) : ℝ :=
  ∑ l : I4, (baseCoef i l l k * J t j l k + baseCoef i l l j * J t k l j - baseCoef i l j k * J t l j k)

private def r0 (J : Jet) (i j : I4) : ℝ :=
  ∑ t : I4, (dc0 J t t j i - dc0 J j t t i)

private def a0 (J : Jet) (a b : I3) : ℝ :=
  (∑ l : I3, (J l.succ b.succ l.succ a.succ + J a.succ l.succ b.succ l.succ -
    J l.succ l.succ b.succ a.succ - J a.succ b.succ l.succ l.succ))/2 - J a.succ b.succ 0 0

private lemma mink_entry (i l : I4) :
    minkowski i l = if i=l then (if i=0 then -1 else 1) else 0 := by
  fin_cases i <;> fin_cases l <;> rfl

set_option maxHeartbeats 2000000 in
private lemma algebra (J : Jet)
    (dz : ∀ q a b, J 0 q a b=0) (zd : ∀ p a b, J p 0 a b=0)
    (sd : ∀ p q a b, q<p → J p q a b=J q p a b)
    (sm : ∀ p q a b, b<a → J p q a b=J p q b a) :
    r0 J 0 0 = ∑ l : I3, J l.succ l.succ 0 0 ∧
    ∀ a b : I3, r0 J a.succ b.succ = a0 J a b := by
  have d21 (a b : I4) : J 2 1 a b = J 1 2 a b := sd 2 1 a b (by decide)
  have m21 (p q : I4) : J p q 2 1 = J p q 1 2 := sm p q 2 1 (by decide)
  have d31 (a b : I4) : J 3 1 a b = J 1 3 a b := sd 3 1 a b (by decide)
  have m31 (p q : I4) : J p q 3 1 = J p q 1 3 := sm p q 3 1 (by decide)
  have d32 (a b : I4) : J 3 2 a b = J 2 3 a b := sd 3 2 a b (by decide)
  have m32 (p q : I4) : J p q 3 2 = J p q 2 3 := sm p q 3 2 (by decide)
  have s₀ : (0:I3).succ=(1:I4) := rfl
  have s₁ : (1:I3).succ=(2:I4) := rfl
  have s₂ : (2:I3).succ=(3:I4) := rfl
  constructor
  · simp +decide [r0,dc0,baseCoef,mink_entry,Fin.sum_univ_four,Fin.sum_univ_three,s₀,s₁,s₂,dz,zd] <;> ring
  · intro a b
    fin_cases a <;> fin_cases b <;>
      simp +decide [r0,dc0,a0,baseCoef,mink_entry,Fin.sum_univ_four,Fin.sum_univ_three,s₀,s₁,s₂,dz,zd,d21,m21,d31,m31,d32,m32] <;> ring

private lemma flat_components (N : X → ℝ) (h : X → M3) (x : X)
    (hn : ContDiffAt ℝ ∞ N x) (hh : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x)
    (hs : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j=h y j i) :
    flatR (field N h) 0 0 x = flatLapseLaplacian N x ∧ ∀ a b : I3,
      flatR (field N h) a.succ b.succ x = staticPrincipalRicci N h a b x := by
  classical
  let S := field N h
  let J := fun p q (i j : I4) => d p (d q (fun y => S y i j)) x
  have Dform (t i j k : I4) : flatD S t i j k x = dc0 J t i j k := by
    unfold flatD dc0
    simp only [coeff0,J]
  have rf (i j : I4) : flatR S i j x = r0 J i j := by
    unfold flatR r0
    exact Finset.sum_congr rfl fun t _ => congrArg₂ (·-·) (Dform t t j i) (Dform j t t i)
  have dz (q a b : I4) : J 0 q a b = 0 := by simp only [J,d,e,Fin.cases_zero,map_zero]
  have zd (p a b : I4) : J p 0 a b = 0 := by
    change d p (d 0 (fun y => S y a b)) x = 0
    rw [d_time]
    exact congrFun (d_const p 0) x
  have sd (p q a b : I4) (w : q<p) : J p q a b=J q p a b := by
    have sf := field_coords N h x hn hh a b
    change d p (d q (fun y => field N h y a b)) x = d q (d p _) x
    rw [second_eq sf,second_eq sf]
    simp only [iteratedFDeriv_two_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    have sf2 : ContDiffAt ℝ 2 (fun y => field N h y a b) x :=
      sf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    exact sf2.isSymmSndFDerivAt (by simp) _ _
  have sm (p q a b : I4) (w : b<a) : J p q a b=J p q b a := by
    have ev : (fun y => S y a b) =ᶠ[𝓝 x] (fun y => S y b a) := by
      filter_upwards [hs] with y sy
      induction a using Fin.cases <;> induction b using Fin.cases <;> first | rfl | exact sy _ _
    have ds : d q (fun y => S y a b) =ᶠ[𝓝 x] d q (fun y => S y b a) :=
      (ev.fderiv (𝕜:=ℝ)).mono fun y hy => congrArg (fun L : X →L[ℝ] ℝ => L (e q)) hy
    exact congrArg (fun L : X →L[ℝ] ℝ => L (e p)) ds.fderiv_eq
  have eq := algebra J dz zd sd sm
  exact ⟨(rf 0 0).trans eq.1,fun a b => (rf a.succ b.succ).trans (eq.2 a b)⟩

private lemma ric_error (N : X → ℝ) (h : X → M3) (B : ℝ)
    (smooth : ∀ x : X, B < ‖x‖ → ContDiffAt ℝ ∞ N x ∧ ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x)
    (x : X) (far : B < ‖x‖) (r G H : ℝ) (rp : 0<r) (gp : 0<G) (hp : 0<H)
    (bounds : ∀ p i j k : I4, DifferentiableAt ℝ (gamma (field N h) i j k) x ∧
      |gamma (field N h) i j k x| ≤ G/r^2 ∧
      |d p (gamma (field N h) i j k) x - flatD (field N h) p i j k x| ≤ H/r^4)
    (i j : I4) :
    |ricci (staticCartesianBlock N h) (staticTimeZero x) i j - flatR (field N h) i j x| ≤
      (4*(2*H+8*G^2))/r^4 := by
  let S := field N h
  let z := staticTimeZero x
  have px : projS z=x := by ext a; fin_cases a <;> rfl
  have cf := smooth x far
  have val (a b c : I4) : christoffel (staticCartesianBlock N h) z a b c = gamma S a b c x := by
    have h := gamma_eq N h z (px.symm ▸ cf.1) (px.symm ▸ cf.2) a b c
    simpa only [px] using h
  have df (p a b c : I4) : coordPartial (fun w => christoffel (staticCartesianBlock N h) w a b c) p z =
      d p (gamma S a b c) x := by
    have hfar : ∀ᶠ w : E4 in 𝓝 z, B < ‖projS w‖ :=
      (isOpen_lt continuous_const projS.continuous.norm).mem_nhds (show B < ‖projS z‖ by rwa [px])
    have eq : (fun w => christoffel (staticCartesianBlock N h) w a b c) =ᶠ[𝓝 z]
        (fun w => gamma S a b c (projS w)) := hfar.mono fun w hw =>
      gamma_eq N h w (smooth _ hw).1 (smooth _ hw).2 a b c
    calc
      _ = coordPartial (fun w => gamma S a b c (projS w)) p z :=
        congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis p)) eq.fderiv_eq
      _ = _ := by rw [lift_d _ _ _ (px.symm ▸ (bounds p a b c).1),px]
  have prod (a b c v w t : I4) : |gamma S a b c x * gamma S v w t x| ≤ G^2/r^4 := by
    rw [abs_mul]
    calc _ ≤ (G/r^2)*(G/r^2) := mul_le_mul (bounds 0 a b c).2.1 (bounds 0 v w t).2.1 (abs_nonneg _) (by positivity)
         _ = _ := by field_simp <;> ring
  change |ricci (staticCartesianBlock N h) z i j-flatR S i j x| ≤ _
  unfold ricci riemann flatR
  simp only [df,val]
  rw [← Finset.sum_sub_distrib]
  apply (sum4 _ (2*(H/r^4)+8*(G^2/r^4)) ?_).trans_eq (by ring)
  intro t
  let q := fun l : I4 => gamma S t t l x * gamma S l j i x - gamma S t j l x * gamma S l t i x
  have qbound : |∑ l, q l| ≤ 4*(2*(G^2/r^4)) := by
    apply sum4
    intro l
    apply (abs_sub _ _).trans
    linarith only [prod t t l l j i,prod t j l l t i]
  let u := d t (gamma S t j i) x - flatD S t t j i x
  let v := d j (gamma S t t i) x - flatD S j t t i x
  have eu : |u| ≤ H/r^4 := (bounds t t j i).2.2
  have ev : |v| ≤ H/r^4 := (bounds j t t i).2.2
  have eq : d t (gamma S t j i) x - d j (gamma S t t i) x + ∑ l, q l -
      (flatD S t t j i x - flatD S j t t i x) = (u-v) + ∑ l, q l := by dsimp only [u,v]; ring
  change |d t (gamma S t j i) x - d j (gamma S t t i) x + ∑ l, q l -
    (flatD S t t j i x - flatD S j t t i x)| ≤ _
  rw [eq]
  linarith only [abs_add_le (u-v) (∑ l, q l),abs_sub u v,eu,ev,qbound]

theorem solution (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hs : ∃ B : ℝ, ∀ x : ADMPoint, B < ‖x‖ → ContDiffAt ℝ ∞ N x ∧
      (∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) ∧ (∀ i j, h x i j = h x j i))
    (hd : ∀ k : ℕ, k ≤ 2 → ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
      ‖iteratedFDeriv ℝ k (fun y => N y - 1) x‖ ≤ C / ‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) x‖
        ≤ C / ‖x‖^(k+1)) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ x : ADMPoint, R < ‖x‖ →
      |ricci (staticCartesianBlock N h) (staticTimeZero x) 0 0 - flatLapseLaplacian N x| ≤ C / ‖x‖^4 ∧
      ∀ i j : Fin 3, |ricci (staticCartesianBlock N h) (staticTimeZero x) i.succ j.succ -
        staticPrincipalRicci N h i j x| ≤ C / ‖x‖^4 := by
  classical
  obtain ⟨B,bs⟩ := hs
  obtain ⟨R₀,C₀,r₀,c₀,h₀⟩ := hd 0 (by decide)
  obtain ⟨R₁,C₁,r₁,c₁,h₁⟩ := hd 1 (by decide)
  obtain ⟨R₂,C₂,r₂,c₂,h₂⟩ := hd 2 (by decide)
  obtain ⟨ε,K,ep,kp,co⟩ := uniform_coeff
  let decayConst := max C₀ (max C₁ C₂)
  have cp : 0<decayConst := c₀.trans_le (le_max_left _ _)
  let R := max R₀ (max R₁ (max R₂ (max B (decayConst/ε))))
  let G := 12*K*decayConst
  let H := 24*K*decayConst^2
  have gp : 0<G := by dsimp [G]; positivity
  have hp : 0<H := by dsimp [H]; positivity
  refine ⟨R,4*(2*H+8*G^2),r₀.trans_le (le_max_left _ _),by positivity,?_⟩
  intro x hx
  have far := max_lt_iff.mp hx
  have far1 := max_lt_iff.mp far.2
  have far2 := max_lt_iff.mp far1.2
  have far3 := max_lt_iff.mp far2.2
  have rp := r₀.trans far.1
  have s := bs x far3.1
  have weights (k : ℕ) (hk : k ≤ 2) :
      ‖iteratedFDeriv ℝ k (fun y => N y-1) x‖ ≤ decayConst/‖x‖^(k+1) ∧
      ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : M3) i j) x‖ ≤ decayConst/‖x‖^(k+1) := by
    have lift (k : ℕ) (A : ℝ) (hA : A≤decayConst)
        (b : ‖iteratedFDeriv ℝ k (fun y => N y-1) x‖ ≤ A/‖x‖^(k+1) ∧
          ∀ i j, ‖iteratedFDeriv ℝ k (fun y => h y i j - (1 : M3) i j) x‖ ≤ A/‖x‖^(k+1)) :=
      And.intro (b.1.trans (div_le_div_of_nonneg_right hA (by positivity))) (fun i j =>
        (b.2 i j).trans (div_le_div_of_nonneg_right hA (by positivity)))
    interval_cases k
    · exact lift 0 C₀ (le_max_left _ _) (h₀ x far.1)
    · exact lift 1 C₁ ((le_max_left _ _).trans (le_max_right _ _)) (h₁ x far1.1)
    · exact lift 2 C₂ ((le_max_right _ _).trans (le_max_right _ _)) (h₂ x far2.1)
  have w := field_bounds N h x decayConst cp s.1 s.2.1 weights
  have near : ‖field N h x-s0‖ < ε := w.1.trans_lt ((div_lt_iff₀ rp).mpr
    (by linarith only [(div_lt_iff₀ ep).mp far3.2]))
  have bd := gamma_bounds (field N h) x decayConst K ‖x‖ rp cp kp (field_coords N h x s.1 s.2.1)
    w.1 w.2.1 w.2.2 (co _ near)
  have er := ric_error N h B (fun y hy => ⟨(bs y hy).1,(bs y hy).2.1⟩)
    x far3.1 ‖x‖ G H rp gp hp bd
  have beyond : ∀ᶠ y in 𝓝 x, B < ‖y‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds far3.1
  have sy : ∀ᶠ y in 𝓝 x, ∀ i j, h y i j=h y j i := beyond.mono fun y hy => (bs y hy).2.2
  have f := flat_components N h x s.1 s.2.1 sy
  exact ⟨f.1 ▸ er 0 0,fun i j => f.2 i j ▸ er i.succ j.succ⟩
