-- Prove2me | solution 1 for NoHair.linear_adm_flux_on_coordinate_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:00:07.310813+00:00
-- url     : https://prove2.me/submissions/adbed2bb-dfbc-4961-a2ea-57d620d50c6c

import Definitions.Def_NoHair_linearADMFlux
import Theorems.Thm_EuclideanSpace_integral_divergence_ball_three
open Set Metric MeasureTheory Filter NoHair
open scoped ContDiff Manifold Topology

private abbrev X := ADMPoint
private noncomputable abbrev pd := spatialADMPartial
private noncomputable abbrev proj (i : Fin 3) : X →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

private lemma smooth_pd {f : X → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin 3) :
    ContDiff ℝ ∞ (pd i f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private lemma pd_sum (f : Fin 3 → X → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (i : Fin 3) (x : X) :
    pd i (fun y => ∑ j, f j y) x = ∑ j, pd i (f j) x := by
  unfold pd spatialADMPartial
  rw [fderiv_fun_sum (fun j _ => (hf j).differentiable (by simp) x)]
  simp

private lemma pd_symmetric {f : X → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (x : X) :
    pd i (pd j f) x = pd j (pd i f) x := by
  have h2 : ContDiff ℝ 2 f := hf.of_le (by exact ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have c := (h2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x
  have der (a b : Fin 3) : pd a (pd b f) x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    unfold pd spatialADMPartial
    rw [fderiv_clm_apply (u := fun _ : X => EuclideanSpace.single b 1) c
      (differentiableAt_const (EuclideanSpace.single b 1))]
    simp
  rw [der,der]
  exact h2.contDiffAt.isSymmSndFDerivAt (by simp) _ _

private lemma flux_skew (P : Fin 3 → Fin 3 → X → ℝ)
    (c : ∀ i j, ContDiff ℝ ∞ (P i j)) (sk : ∀ i j, P i j = -P j i)
    (r : ℝ) (hr : 0 < r) :
    ∫ n : ADMSphere, ∑ j : Fin 3, (∑ l : Fin 3, pd l (P j l) (r • (n:X))) * (n:X) j
        ∂admSurfaceMeasure = 0 := by
  let F := fun x : X => WithLp.toLp 2 (fun j : Fin 3 => ∑ l : Fin 3, pd l (P j l) x)
  have cf : ContDiff ℝ ∞ F := PiLp.contDiff_toLp.comp (contDiff_pi.mpr
    (fun j => ContDiff.sum (fun l _ => smooth_pd (c j l) l)))
  have negp (j : Fin 3) (f : X → ℝ) : pd j (-f) = -pd j f := by
    funext x
    change fderiv ℝ (-f) x (EuclideanSpace.single j 1) = -(fderiv ℝ f x (EuclideanSpace.single j 1))
    rw [fderiv_neg]
    rfl
  have swap (x : X) (i j : Fin 3) : pd i (pd j (P i j)) x = -pd j (pd i (P j i)) x := by
    rw [pd_symmetric (c i j) i j,sk i j,negp,negp]
    rfl
  have divF (x : X) : (∑ i : Fin 3, (fderiv ℝ F x (EuclideanSpace.single i 1)) i) = 0 := by
    have diag (i : Fin 3) : (fderiv ℝ F x (EuclideanSpace.single i 1)) i =
        ∑ j : Fin 3, pd i (pd j (P i j)) x := by
      have deriv := ((proj i).hasFDerivAt.comp x (cf.differentiable (by simp) x).hasFDerivAt).fderiv
      change fderiv ℝ (fun z => ∑ j, pd j (P i j) z) x = (proj i).comp (fderiv ℝ F x) at deriv
      rw [← pd_sum (fun j => pd j (P i j)) (fun j => smooth_pd (c i j) j)]
      exact (congrArg (fun a : X →L[ℝ] ℝ => a (EuclideanSpace.single i 1)) deriv).symm
    simp_rw [diag]
    let q := fun i j => pd i (pd j (P i j)) x
    have e : (∑ i : Fin 3, ∑ j : Fin 3, q i j) = -(∑ i : Fin 3, ∑ j : Fin 3, q i j) := calc
      _ = ∑ i : Fin 3, ∑ j : Fin 3, -q j i := Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => swap x i j
      _ = _ := by simp only [Finset.sum_neg_distrib]; rw [Finset.sum_comm]
    change (∑ i : Fin 3, ∑ j : Fin 3, q i j) = 0
    linarith only [e]
  have eq := EuclideanSpace.integral_divergence_ball_three F (cf.of_le (by simp)) r hr
  simp_rw [divF] at eq
  rw [MeasureTheory.integral_zero] at eq
  have zero := (mul_eq_zero.mp eq.symm).resolve_left (pow_ne_zero 2 hr.ne')
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, F, WithLp.ofLp_toLp, mul_comm] using zero

theorem solution (k : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (hsmooth : ∀ i j, ContDiff ℝ ∞ (fun x => k x i j)) (R : ℝ) (hR : 0 < R) :
    staticADMFlux k R = (∫ n : ADMSphere,
      ∑ j : Fin 3, (∑ i : Fin 3, R^2 * (R • (n : ADMPoint)) i *
        negativeTwiceLinearEinstein k i j (R • (n : ADMPoint))) * (n : ADMPoint) j
        ∂admSurfaceMeasure) / (16 * Real.pi) := by
  classical
  let T := admSuperpotential k
  have ca (j : Fin 3) : ContDiff ℝ ∞ (admVector k j) :=
    ContDiff.sum (fun l _ => (smooth_pd (hsmooth j l) l).sub (smooth_pd (hsmooth l l) j))
  have ct (i j l : Fin 3) : ContDiff ℝ ∞ (T i j l) :=
    ((((smooth_pd (hsmooth j i) l).sub (smooth_pd (hsmooth l i) j)).add
      (contDiff_const.mul (ca l))).sub (contDiff_const.mul (ca j)))
  let P := fun (j l : Fin 3) (x : X) => ∑ i : Fin 3, x i * T i j l x
  have smoothP (j l : Fin 3) : ContDiff ℝ ∞ (P j l) :=
    ContDiff.sum fun i _ => (proj i).contDiff.mul (ct i j l)
  have antisym (j l : Fin 3) : P j l = -P l j := by
    funext x
    dsimp only [P,Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [T,admSuperpotential]
    ring
  have deriv (x : X) (i j l : Fin 3) :
      pd l (fun y : X => y i * T i j l y) x =
        (1 : Matrix (Fin 3) (Fin 3) ℝ) i l * T i j l x + x i * pd l (T i j l) x := by
    have d := ((proj i).hasFDerivAt.mul ((ct i j l).differentiable (by simp) x).hasFDerivAt).fderiv
    change fderiv ℝ (fun y : X => y i * T i j l y) x = _ at d
    unfold pd spatialADMPartial
    rw [d]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    change x i * _ + T i j l x * (EuclideanSpace.single l (1:ℝ)) i = _
    by_cases e : i=l <;> simp [Matrix.one_apply,PiLp.single_apply,e,Ne.symm, mul_comm,add_comm]
  have divP (j : Fin 3) (x : X) : ∑ l : Fin 3, pd l (P j l) x =
      -admVector k j x + ∑ i : Fin 3, x i * negativeTwiceLinearEinstein k i j x := by
    have each (l : Fin 3) : pd l (P j l) x = ∑ i : Fin 3,
        ((1 : Matrix (Fin 3) (Fin 3) ℝ) i l * T i j l x + x i * pd l (T i j l) x) := by
      have ed := pd_sum (fun i (y:X) => y i * T i j l y) (fun i => (proj i).contDiff.mul (ct i j l)) l x
      exact ed.trans (Finset.sum_congr rfl fun i _ => deriv x i j l)
    simp_rw [each]
    simp only [Finset.sum_add_distrib]
    have traceT : (∑ l : Fin 3, ∑ i : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i l * T i j l x) = -admVector k j x := by
      fin_cases j <;> simp +decide [Fin.sum_univ_three,T,admSuperpotential,admVector,Matrix.one_apply] <;> ring
    rw [traceT]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  let A := staticADMDensity k R
  let B := fun n : ADMSphere => ∑ j : Fin 3, (∑ l : Fin 3, pd l (P j l) (R • (n:X))) * (n:X) j
  have z : ∫ n : ADMSphere, B n ∂admSurfaceMeasure = 0 := flux_skew P smoothP antisym R hR
  have ident (n : ADMSphere) :
      (∑ j : Fin 3, (∑ i : Fin 3, R^2*(R • (n:X)) i * negativeTwiceLinearEinstein k i j (R • (n:X))) * (n:X) j) =
      A n + R^2 * B n := by
    dsimp only [A, B, staticADMDensity]
    simp_rw [divP]
    simp only [Fin.sum_univ_three, admVector];ring
  have continu (f : X → ℝ) (c : Continuous f) : Continuous (fun n : ADMSphere => f (R • (n:X))) :=
    c.comp ((continuous_const_smul R).comp continuous_subtype_val)
  have aC : Continuous A := by
    apply continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((continuous_const.mul (continu _ (smooth_pd (hsmooth i j) j).continuous)).sub
      (continuous_const.mul (continu _ (smooth_pd (hsmooth j j) i).continuous))).mul
      ((proj i).continuous.comp continuous_subtype_val)
  have bC : Continuous B := by
    apply continuous_finsetSum _ fun j _ => ?_
    exact (continuous_finsetSum _ (fun l _ => continu _ (smooth_pd (smoothP j l) l).continuous)).mul
      ((proj j).continuous.comp continuous_subtype_val)
  have ia := aC.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
  have ib := bC.integrable_of_hasCompactSupport (μ:=admSurfaceMeasure) (HasCompactSupport.of_compactSpace _)
  simp_rw [ident]
  rw [integral_add ia (ib.const_mul _),integral_const_mul,z,mul_zero,add_zero]
  rfl
