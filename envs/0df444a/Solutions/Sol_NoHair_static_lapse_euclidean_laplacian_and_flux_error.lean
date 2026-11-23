-- Prove2me | solution 1 for NoHair.static_lapse_euclidean_laplacian_and_flux_error
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:49:40.030811+00:00
-- url     : https://prove2.me/submissions/6713e882-6b72-41c1-a038-2ef25692888f

import Definitions.Def_NoHair_staticHorizonGeometry
import Mathlib.Analysis.InnerProductSpace.Laplacian

open NoHair Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ContDiff Laplacian

noncomputable section

open scoped Matrix
private abbrev X := ADMPoint
private abbrev I := Fin 3
private abbrev V := I → I → ℝ
private abbrev M := Matrix I I ℝ
private noncomputable abbrev e (i : I) : X := EuclideanSpace.single i 1
private noncomputable abbrev d := spatialADMPartial
private noncomputable abbrev s0 : V := (1 : M)
private def mat (q : V) : M := fun i j => q i j
private def coef (t : Bool) (i j : I) (q : V) : ℝ :=
  if t then Real.sqrt (mat q).det * (mat q)⁻¹ i j else (mat q)⁻¹ i j

private lemma sm_coef (t : Bool) (i j : I) : ContDiffAt ℝ 1 (coef t i j) s0 := by
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
  have entry (i j : I) : ContDiff ℝ ∞ (fun q : V => q i j) := by fun_prop
  have ds := detSmooth (n:=I) mat entry
  have det0 : (mat s0).det ≠ 0 := by rw [show mat s0 = (1:M) from rfl,Matrix.det_one]; norm_num
  have adj : ContDiff ℝ ∞ (fun q : V => (mat q).adjugate i j) := by
    simp_rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    exact contDiff_const.mul (detSmooth (n:=Fin 2) (fun q => (mat q).submatrix j.succAbove i.succAbove)
      (fun k m => entry _ _))
  have inv : ContDiffAt ℝ ∞ (fun q : V => (mat q)⁻¹ i j) s0 := by
    simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul]
    exact (ds.contDiffAt.inv det0).mul adj.contDiffAt
  cases t
  · exact inv.of_le (by simp)
  · exact ((ds.contDiffAt.sqrt det0).mul inv).of_le (by simp)

private lemma uniform : ∃ ε K : ℝ, 0<ε ∧ 0<K ∧ ∀ q : V, ‖q-s0‖<ε → ∀ t i j,
    |coef t i j q - (1:M) i j| ≤ K * ‖q-s0‖ := by
  let T := Bool × I × I
  have per (a:T) : ∃ k : ℝ, ∀ᶠ q in 𝓝 s0, |coef a.1 a.2.1 a.2.2 q - (1:M) a.2.1 a.2.2| ≤ k*‖q-s0‖ := by
    obtain ⟨k,U,hU,hk⟩ := (sm_coef a.1 a.2.1 a.2.2).exists_lipschitzOnWith
    refine ⟨k,?_⟩
    filter_upwards [hU] with q hq
    have idc (t : Bool) (i j : I) : coef t i j s0 = (1:M) i j := by cases t <;> simp [coef,show mat s0 = (1:M) from rfl]
    simpa only [dist_eq_norm,Real.norm_eq_abs,idc] using hk.dist_le_mul q hq s0 (mem_of_mem_nhds hU)
  choose k hk using per
  let K := (∑ a : T, |k a|)+1
  have dom (a:T) : k a ≤ K := by
    have h := Finset.single_le_sum (fun j _ => abs_nonneg (k j)) (Finset.mem_univ a)
    dsimp only [K]
    linarith only [le_abs_self (k a),h]
  obtain ⟨ε,ep,he⟩ := Metric.mem_nhds_iff.mp (Filter.eventually_all.mpr hk)
  refine ⟨ε,K,ep,by dsimp only [K]; positivity,?_⟩
  intro q hq t i j
  exact (he (show q ∈ Metric.ball s0 ε by simpa only [Metric.mem_ball,dist_eq_norm] using hq) (t,i,j)).trans
    (mul_le_mul_of_nonneg_right (dom (t,i,j)) (norm_nonneg _))

private lemma norm_e (i : I) : ‖e i‖ ≤ 1 := by simp [e]
private lemma second_eq {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (p q : I) :
    d p (d q f) x = iteratedFDeriv ℝ 2 f x ![e p,e q] := by
  have df := (hf.fderiv_right (m:=∞) (by simp)).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  unfold d spatialADMPartial
  rw [fderiv_clm_apply (u:=fun _ : X => e q) df (differentiableAt_const _),
    iteratedFDeriv_two_apply]
  simp

private lemma first_second_bounds {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x)
    (u decayConst : ℝ)
    (h₂ : ‖iteratedFDeriv ℝ 2 (fun y => f y-u) x‖ ≤ decayConst/‖x‖^3) (p q : I) :
    |d p (d q f) x| ≤ decayConst / ‖x‖^3 := by
  let g := fun y => f y-u
  have de : d q g = d q f := by funext y; simp only [d,spatialADMPartial,g,fderiv_sub_const]
  rw [← de,second_eq (hf.sub contDiffAt_const)]
  have op := (iteratedFDeriv ℝ 2 g x).le_opNorm ![e p,e q]
  have w : (∏ i : Fin 2, ‖(![e p,e q] : Fin 2 → X) i‖) ≤ 1 := by
    simpa only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] using
      mul_le_one₀ (norm_e p) (norm_nonneg _) (norm_e q)
  exact (op.trans (mul_le_of_le_one_right (norm_nonneg _) w)).trans h₂

private lemma sum3 (f : I → ℝ) (A : ℝ) (h : ∀ i, |f i| ≤ A) : |∑ i, f i| ≤ 3*A := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i : I, A := Finset.sum_le_sum fun i _ => h i
       _ = 3*A := by simp [Fin.sum_univ_three] <;> ring

theorem solution (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h) :
    ∃ R C : ℝ, 0<R ∧ 0<C ∧ ∀ x : ADMPoint, R<‖x‖ →
      |(Δ N) x| ≤ C/‖x‖^4 ∧ ∀ i : Fin 3,
        |Real.sqrt (h x).det * staticRaisedGradient N h i x - spatialADMPartial i N x|
          ≤ C/‖x‖^3 := by
  classical
  obtain ⟨r0,c0,r0p,c0p,h0⟩ := c.falloff 0
  obtain ⟨r1,c1,r1p,c1p,h1⟩ := c.falloff 1
  obtain ⟨r2,c2,r2p,c2p,h2⟩ := c.falloff 2
  obtain ⟨r3,kb⟩ := c.compactComplement.isBounded.exists_norm_le
  obtain ⟨ε,K,ep,kp,localK⟩ := uniform
  let R := max (max r0 r1) (max (max r2 r3) (max 1 (c0/ε)))
  let P := K*c0
  let B := 1+P
  let G := 5*B*c1
  let H := 9*(P*c2+3*B*G*c1)
  let C := H+3*P*c1
  have pp : 0<P := mul_pos kp c0p
  have bp : 0<B := by dsimp [B]; positivity
  have gp : 0<G := by dsimp [G]; positivity
  have hp : 0<H := by dsimp [H]; positivity
  refine ⟨R,C,r0p.trans_le ((le_max_left _ _).trans (le_max_left _ _)),by dsimp [C]; positivity,?_⟩
  intro x hx
  have br := max_lt_iff.mp hx
  obtain ⟨h0r,h1r⟩ := max_lt_iff.mp br.1
  obtain ⟨h23,ht⟩ := max_lt_iff.mp br.2
  obtain ⟨h2r,h3r⟩ := max_lt_iff.mp h23
  obtain ⟨one,heps⟩ := max_lt_iff.mp ht
  have xp : 0<‖x‖ := zero_lt_one.trans one
  have ho : x∈Ω := by by_contra hn; exact h3r.not_ge (kb x hn)
  have wx := c.openExtension.mem_nhds (c.extendsAcross (subset_closure ho))
  have cn := c.smoothLapse.contDiffAt wx
  have ch (a b : I) := (c.smoothMetric a b).contDiffAt wx
  let raw : V := fun i j => h x i j
  have close : ‖raw-s0‖ ≤ c0/‖x‖ := by
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro i
    apply (pi_norm_le_iff_of_nonempty _).mpr
    intro j
    change ‖h x i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j‖ ≤ _
    simpa only [norm_iteratedFDeriv_zero,Nat.zero_add,pow_one] using (h0 x h0r).2 i j
  have small : ‖raw-s0‖<ε := close.trans_lt ((div_lt_iff₀ xp).mpr (by
    have z := (div_lt_iff₀ ep).mp heps
    linarith only [z,mul_comm ‖x‖ ε]))
  have invErr (t : Bool) (i j : I) : |coef t i j raw - (1:M) i j| ≤ P/‖x‖ :=
    (localK _ small t i j).trans ((mul_le_mul_of_nonneg_left close kp.le).trans_eq (by dsimp [P]; ring))
  have invB (i j : I) : |(h x)⁻¹ i j| ≤ B := by
    have z := invErr false i j
    change |(h x)⁻¹ i j - (1:M) i j| ≤ P/‖x‖ at z
    have idb : |(1:M) i j| ≤ 1 := by by_cases eq : i=j <;> simp [Matrix.one_apply,eq]
    have z' : P/‖x‖ ≤ P := div_le_self pp.le one.le
    calc |(h x)⁻¹ i j| = |((h x)⁻¹ i j - (1:M) i j) + (1:M) i j| := by rw [sub_add_cancel]
         _ ≤ _ := abs_add_le _ _
         _ ≤ B := by dsimp [B]; linarith
  have dn (i:I) : |d i N x| ≤ c1/‖x‖^2 := by
    have w := (h1 x h1r).1
    simp only [norm_iteratedFDeriv_one,fderiv_sub_const] at w
    exact (((fderiv ℝ N x).le_opNorm (e i)).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_e i))).trans w
  have dh (i j k:I) : |d i (fun y => h y j k) x| ≤ c1/‖x‖^2 := by
    have w := (h1 x h1r).2 j k
    simp only [norm_iteratedFDeriv_one,fderiv_sub_const] at w
    exact (((fderiv ℝ (fun y => h y j k) x).le_opNorm (e i)).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_e i))).trans w
  have d2 (i j:I) : |d i (d j N) x| ≤ c2/‖x‖^3 := by
    exact first_second_bounds cn 1 c2 (h2 x h2r).1 i j
  have gamma (a i j:I) : |spatialLeviCivita h x a i j| ≤ G/‖x‖^2 := by
    have tri (l:I) : |d i (fun y => h y l j) x + d j (fun y => h y l i) x -
          d l (fun y => h y i j) x| ≤ 3*(c1/‖x‖^2) := by
      calc _ ≤ |d i (fun y => h y l j) x + d j (fun y => h y l i) x| + |d l (fun y => h y i j) x| := abs_sub _ _
           _ ≤ _ := by linarith only [abs_add_le (d i (fun y => h y l j) x) (d j (fun y => h y l i) x),dh i l j,dh j l i,dh l i j]
    unfold spatialLeviCivita
    rw [abs_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    have s := sum3 (fun l => (h x)⁻¹ a l * (d i (fun y => h y l j) x+
      d j (fun y => h y l i) x-d l (fun y => h y i j) x)) (B*(3*(c1/‖x‖^2))) (fun l => by
      rw [abs_mul]; exact mul_le_mul (invB _ _) (tri l) (abs_nonneg _) bp.le)
    apply (mul_le_mul_of_nonneg_left s (by norm_num : (0:ℝ) ≤ 1/2)).trans
    dsimp [G]; field_simp; nlinarith only [mul_pos bp c1p]
  have trace : (Δ N) x = ∑ i : I, d i (d i N) x := by
    simpa only [EuclideanSpace.basisFun_apply,←second_eq cn,e] using congrFun
      (laplacian_eq_iteratedFDeriv_orthonormalBasis N (EuclideanSpace.basisFun I ℝ)) x
  have eq := (c.equations x (subset_closure ho)).2
  let E := fun i j : I => ((1:M) i j-(h x)⁻¹ i j)*d i (d j N) x +
    (h x)⁻¹ i j*(∑ l : I, spatialLeviCivita h x l i j * d l N x)
  have tr : (Δ N) x = ∑ i : I, ∑ j : I, E i j := by
    rw [trace]
    simp only [E,staticSpatialHessian,Fin.sum_univ_three,Matrix.one_apply,Fin.isValue] at eq ⊢
    simp +decide only [ite_true,ite_false,zero_sub,one_mul,zero_mul] at *
    dsimp only [d] at eq ⊢
    linear_combination eq
  have eb (i j:I) : |E i j| ≤ (P*c2+3*B*G*c1)/‖x‖^4 := by
    have iv := invErr false i j
    change |(h x)⁻¹ i j-(1:M) i j|≤P/‖x‖ at iv
    have v1 := mul_le_mul (by rwa [abs_sub_comm] : |(1:M) i j-(h x)⁻¹ i j| ≤ P/‖x‖)
      (d2 i j) (abs_nonneg _) (by positivity)
    have v2 := sum3 (fun l => spatialLeviCivita h x l i j*d l N x) ((G/‖x‖^2)*(c1/‖x‖^2)) (fun l => by
      rw [abs_mul]; exact mul_le_mul (gamma l i j) (dn l) (abs_nonneg _) (by positivity))
    unfold E
    apply (abs_add_le _ _).trans
    simp only [abs_mul]
    exact (add_le_add v1 (mul_le_mul (invB _ _) v2 (abs_nonneg _) bp.le)).trans_eq (by ring)
  constructor
  · rw [tr]
    have t := sum3 _ _ (fun i => sum3 _ _ (eb i))
    apply t.trans
    have hs : H≤C := by dsimp only [C]; linarith only [mul_pos pp c1p]
    exact (show 3*(3*((P*c2+3*B*G*c1)/‖x‖^4)) = H/‖x‖^4 by dsimp [H]; ring).le.trans (div_le_div_of_nonneg_right hs (by positivity))
  · intro i
    have delta : (∑ j : I, (1:M) i j*d j N x) = d i N x := by
      simp [Matrix.one_apply,ite_mul]
    have re : Real.sqrt (h x).det*staticRaisedGradient N h i x-d i N x =
        ∑ j : I, (coef true i j raw-(1:M) i j)*d j N x := by
      simp only [coef,if_true,staticRaisedGradient,Finset.mul_sum,sub_mul,Finset.sum_sub_distrib,mul_assoc,delta,show mat raw=h x from rfl]
    rw [re]
    have t := sum3 (fun j => (coef true i j raw-(1:M) i j)*d j N x) ((P/‖x‖)*(c1/‖x‖^2)) (fun j => by
      rw [abs_mul]; exact mul_le_mul (invErr true i j) (dn j) (abs_nonneg _) (by positivity))
    apply t.trans
    have hs : 3*P*c1 ≤ C := by dsimp only [C]; linarith only [hp]
    exact (show 3*((P/‖x‖)*(c1/‖x‖^2))=3*P*c1/‖x‖^3 by ring).le.trans (div_le_div_of_nonneg_right hs (by positivity))
