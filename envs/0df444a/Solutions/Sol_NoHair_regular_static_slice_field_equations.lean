-- Prove2me | solution 1 for NoHair.regular_static_slice_field_equations
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:34:04.644765+00:00
-- url     : https://prove2.me/submissions/c10fac6d-255f-4027-9834-c88528851f66

import Theorems.Thm_NoHair_static_block_ricci_hessian_identities
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

private theorem partial_eq_on_open {s : Set E4} (hs : IsOpen s) {f g : E4 → ℝ}
    (h : EqOn f g s) (k : Fin 4) {z : E4} (hz : z ∈ s) :
    coordPartial f k z = coordPartial g k z :=
  congrArg (fun L : E4 →L[ℝ] ℝ => L (coordBasis k))
    (h.eventuallyEq_of_mem (hs.mem_nhds hz)).fderiv_eq

private lemma block_ricci_congr {s : Set E4} (hs : IsOpen s)
    {G' G : E4 → Matrix (Fin 4) (Fin 4) ℝ}
    (hG : EqOn G' G s) {y : E4} (hy : y ∈ s) (i j : Fin 4) :
    ricci G' y i j = ricci G y i j := by
  have dG (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      coordPartial (fun w => G' w i j) k z = coordPartial (fun w => G w i j) k z :=
    partial_eq_on_open hs (fun w hw => congrArg (fun A : Matrix (Fin 4) (Fin 4) ℝ => A i j) (hG hw)) k hz
  have chr (z : E4) (hz : z ∈ s) (i j k : Fin 4) :
      christoffel G' z i j k = christoffel G z i j k := by
    simp only [christoffel, invMetric, hG hz, dG z hz]
  have dChr (z : E4) (hz : z ∈ s) (i j k l : Fin 4) :
      coordPartial (fun w => christoffel G' w i j k) l z =
      coordPartial (fun w => christoffel G w i j k) l z :=
    partial_eq_on_open hs (fun w hw => chr w hw i j k) l hz
  simp only [ricci, riemann, dChr y hy, chr y hy]

private lemma spatial_cont : Continuous conformalSpatialPoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun x : E4 => x _) <;> fun_prop

private lemma symmetric_pd {f : X → ℝ} {x : X} (hf : ContDiffAt ℝ ∞ f x) (i j : I) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have h2 : ContDiffAt ℝ 2 f x := hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have c := (h2.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  have der (a b : I) : pd a (pd b f) x = fderiv ℝ (fderiv ℝ f) x (bvec a) (bvec b) := by
    unfold pd spatialADMPartial
    rw [fderiv_clm_apply (u := fun _ : X => EuclideanSpace.single b 1) c
      (differentiableAt_const (EuclideanSpace.single b 1))]
    simp [bvec]
  rw [der,der]
  exact h2.isSymmSndFDerivAt (by simp) _ _

theorem solution {M : Type*} [TopologicalSpace M]
    [ChartedSpace E4 M] [IsManifold 𝓘(ℝ, E4) ∞ M] (g : BilinField M) (φ : ℝ → M → M) (D : Set M)
    (c : RegularStaticSliceCoordinates g φ D) :
    StaticSliceEquations c.Ω c.N c.h := by
  classical
  let S := conformalSpatialPoint ⁻¹' c.Ω
  have so : IsOpen S := c.openSlice.preimage spatial_cont
  have eq : EqOn (pullbackCoeffs g c.ψ) (staticCartesianBlock c.N c.h) S := by
    intro z hz
    ext i j
    have v := c.staticMetric z hz (coordBasis i) (coordBasis j)
    change pullbackCoeffs g c.ψ z i j = _ at v
    rw [v]
    fin_cases i <;> fin_cases j <;>
      simp +decide [staticCartesianBlock,coordBasis,PiLp.single_apply,Fin.sum_univ_three] <;> rfl
  have cn {x : X} (wx : x∈c.W) := c.smoothLapse.contDiffAt (c.openExtension.mem_nhds wx)
  have ch {x : X} (wx : x∈c.W) (i j : I) := (c.smoothMetric i j).contDiffAt (c.openExtension.mem_nhds wx)
  have sh {x : X} (wx : x∈c.W) (i j : I) : ContDiffAt ℝ ∞ (staticSpatialHessian c.N c.h i j) x :=
    (sm_pd (sm_pd (cn wx) j) i).sub (ContDiffAt.sum fun k _ =>
      (sm_ch (c.positiveMetric x wx) (ch wx) k i j).mul (sm_pd (cn wx) k))
  have sr {x : X} (wx : x∈c.W) (i j : I) : ContDiffAt ℝ ∞ (fun y => spatialRicciTensor c.h y i j) x := by
    have cg := sm_ch (c.positiveMetric x wx) (ch wx)
    exact ContDiffAt.sum (fun a _ => ((sm_pd (cg a j i) a).sub (sm_pd (cg a a i) j)).add
      (ContDiffAt.sum (fun l _ => ((cg a a l).mul (cg l j i)).sub ((cg a j l).mul (cg l a i)))))
  let L := fun x : X => ∑ i : I, ∑ j : I, (c.h x)⁻¹ i j * staticSpatialHessian c.N c.h i j x
  have sl {x : X} (wx : x∈c.W) : ContDiffAt ℝ ∞ L x :=
    ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => (sm_inv (c.positiveMetric x wx) (ch wx) i j).mul (sh wx i j)
  have inside (x : X) (hx : x∈c.Ω) :
      (∀ i j : I, staticSpatialHessian c.N c.h i j x = c.N x * spatialRicciTensor c.h x i j) ∧ L x=0 := by
    have point : conformalSpatialPoint (staticTimeZero x) = x := by ext k; fin_cases k <;> rfl
    have hxS : staticTimeZero x ∈ S := point ▸ hx
    have vac (a b : Fin 4) : ricci (staticCartesianBlock c.N c.h) (staticTimeZero x) a b = 0 :=
      (block_ricci_congr so eq hxS a b).symm.trans (c.vacuum _ hxS a b)
    have wx := c.extendsAcross (subset_closure hx)
    have nz := ((c.positiveSide x wx).mp hx).ne'
    have F := static_block_ricci_hessian_identities c.N c.h c.W c.openExtension c.smoothLapse c.smoothMetric
      c.positiveMetric x wx nz
    have symG (a i j : I) : spatialLeviCivita c.h x a i j = spatialLeviCivita c.h x a j i := by
      unfold spatialLeviCivita
      congr 1
      apply Finset.sum_congr rfl
      intro l _
      have s : spatialADMPartial l (fun z => c.h z i j) x = spatialADMPartial l (fun z => c.h z j i) x :=
        sym_h c.openExtension c.positiveMetric wx l i j
      rw [s,add_comm (spatialADMPartial i _ _) _]
    have symH (i j : I) : staticSpatialHessian c.N c.h i j x = staticSpatialHessian c.N c.h j i x := by
      change pd i (pd j c.N) x - _ = pd j (pd i c.N) x - _
      rw [symmetric_pd (cn wx) i j]
      congr 1
      exact Finset.sum_congr rfl fun k _ => congrArg (fun t => t * pd k c.N x) (symG k i j)
    constructor
    · intro i j
      have z := F.2 i j
      rw [vac,symH j i] at z
      have h : staticSpatialHessian c.N c.h i j x / c.N x = spatialRicciTensor c.h x i j := by linarith only [z]
      exact ((div_eq_iff nz).mp h).trans (mul_comm _ _)
    · have z := F.1
      rw [vac] at z
      exact (mul_eq_zero.mp z.symm).resolve_left nz
  intro x hx
  constructor
  · intro i j
    have q : EqOn (staticSpatialHessian c.N c.h i j) (fun y => c.N y * spatialRicciTensor c.h y i j) c.Ω :=
      fun y hy => (inside y hy).1 i j
    exact q.of_subset_closure (fun y hy => (sh (c.extendsAcross hy) i j).continuousAt.continuousWithinAt)
      (fun y hy => ((cn (c.extendsAcross hy)).mul (sr (c.extendsAcross hy) i j)).continuousAt.continuousWithinAt)
      subset_closure Subset.rfl hx
  · have q : EqOn L (fun _ => 0) c.Ω := fun y hy => (inside y hy).2
    exact q.of_subset_closure (fun y hy => (sl (c.extendsAcross hy)).continuousAt.continuousWithinAt)
      continuousOn_const subset_closure Subset.rfl hx
