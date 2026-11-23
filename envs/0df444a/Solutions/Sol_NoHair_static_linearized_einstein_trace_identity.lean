-- Prove2me | solution 1 for NoHair.static_linearized_einstein_trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T08:27:05.17487+00:00
-- url     : https://prove2.me/submissions/72d1435d-e073-4971-a526-0a764e2abc4e

import Definitions.Def_NoHair_staticCartesianRicci

open NoHair Set Filter
open scoped ContDiff Manifold Topology

private abbrev X := ADMPoint
private noncomputable abbrev dp := spatialADMPartial
private abbrev Index := Fin 3
private abbrev Mat := Matrix Index Index ℝ

private lemma diff_dp {f : X → ℝ} {x : X} (h : ContDiffAt ℝ ∞ f x) (i : Index) :
    DifferentiableAt ℝ (dp i f) x :=
  (((h.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const) :
    ContDiffAt ℝ ∞ (dp i f) x).differentiableAt (by simp)

private lemma dp_add {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Index) :
    dp i (fun z => f z + g z) x = dp i f x + dp i g x := by
  unfold dp spatialADMPartial
  rw [fderiv_fun_add hf hg]
  rfl

private lemma dp_sub {f g : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Index) :
    dp i (fun z => f z - g z) x = dp i f x - dp i g x := by
  unfold dp spatialADMPartial
  rw [fderiv_fun_sub hf hg]
  rfl

private lemma dp_scale {f : X → ℝ} {x : X} (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Index) :
    dp i (fun z => c * f z) x = c * dp i f x := by
  unfold dp spatialADMPartial
  rw [(hf.hasFDerivAt.const_mul c).fderiv]
  rfl

private lemma dp_sum {f : Index → X → ℝ} {x : X} (hf : ∀ i, DifferentiableAt ℝ (f i) x) (p : Index) :
    dp p (fun y => ∑ j, f j y) x = ∑ j, dp p (f j) x := by
  unfold dp spatialADMPartial
  rw [fderiv_fun_sum (fun j _ => hf j)]
  simp

theorem solution (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (x : ADMPoint) (hN : ContDiffAt ℝ ∞ N x)
    (hh : ∀ i j, ContDiffAt ℝ ∞ (fun y => h y i j) x) (i j : Fin 3) :
    negativeTwiceLinearEinstein (lapseCorrectedADMMetric N h) i j x =
      -2 * staticPrincipalRicci N h i j x + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j *
        ((∑ l : Fin 3, staticPrincipalRicci N h l l x) - flatLapseLaplacian N x) := by
  classical
  let δ := (1 : Mat)
  let K := lapseCorrectedADMMetric N h
  let H := fun a b => (fun y : X => h y a b)
  let U := fun (p q : Index) => dp p (dp q N) x
  let J := fun (p q a b : Index) => dp p (dp q (H a b)) x
  have ck (a b : Index) : ContDiffAt ℝ ∞ (fun y => K y a b) x :=
    (hh a b).add ((contDiffAt_const.mul (hN.sub contDiffAt_const)).mul contDiffAt_const)
  have dk (a b q : Index) := diff_dp (ck a b) q
  have hn1 : ContDiffAt ℝ 1 N x := hN.of_le (by simp)
  have jet (p q a b : Index) :
      dp p (dp q (fun y => K y a b)) x = J p q a b + 2 * δ a b * U p q := by
    have hh1 : ContDiffAt ℝ 1 (H a b) x := (hh a b).of_le (by simp)
    have ev : dp q (fun y => K y a b) =ᶠ[𝓝 x]
        (fun y => dp q (H a b) y + (2 * δ a b) * dp q N y) := by
      filter_upwards [hn1.eventually (by decide),hh1.eventually (by decide)] with y n1 h1
      have eq := ((h1.differentiableAt one_ne_zero).hasFDerivAt.add
        ((((n1.differentiableAt one_ne_zero).hasFDerivAt.sub_const 1).const_mul 2).mul_const (δ a b))).fderiv
      change fderiv ℝ (fun y => K y a b) y = _ at eq
      unfold dp spatialADMPartial
      rw [eq]
      simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      ring
    calc
      _ = dp p (fun y => dp q (H a b) y + (2 * δ a b) * dp q N y) x := congrArg
        (fun L : X →L[ℝ] ℝ => L (EuclideanSpace.single p 1)) ev.fderiv_eq
      _ = _ := by
        rw [dp_add (diff_dp (hh a b) q) ((diff_dp hN q).const_mul _),dp_scale (diff_dp hN q)]
  have da (q : Index) : DifferentiableAt ℝ (admVector K q) x :=
    DifferentiableAt.fun_sum fun l _ => (dk q l l).sub (dk l l q)
  let A := fun (p q : Index) => ∑ m : Index,
    (J p m q m + 2 * δ q m * U p m - (J p q m m + 2 * δ m m * U p q))
  have jetA (p q : Index) : dp p (admVector K q) x = A p q := by
    unfold admVector
    rw [dp_sum (f:=fun (m : Index) (y:X) => dp m (fun z => K z q m) y - dp q (fun z => K z m m) y)
      (fun m => (dk q m m).sub (dk m m q))]
    exact Finset.sum_congr rfl fun m _ => by rw [dp_sub (dk q m m) (dk m m q),jet,jet]
  have jetT (l : Index) : dp l (admSuperpotential K i j l) x =
      (J l l j i + 2 * δ j i * U l l - (J l j l i + 2 * δ l i * U l j)) +
      δ i j * A l l - δ i l * A l j := by
    unfold admSuperpotential
    let f := dp l (fun z => K z j i)
    let g := dp j (fun z => K z l i)
    let u := fun z => δ i j * admVector K l z
    let v := fun z => δ i l * admVector K j z
    have du : DifferentiableAt ℝ u x := (da l).const_mul _
    have dv : DifferentiableAt ℝ v x := (da j).const_mul _
    have ds : DifferentiableAt ℝ (fun z => f z-g z) x := (dk j i l).sub (dk l i j)
    have dh : DifferentiableAt ℝ (fun z => (f z-g z)+u z) x := ds.add du
    rw [dp_sub dh dv,dp_add ds du,dp_sub (dk j i l) (dk l i j)]
    change (dp l (dp l (fun y => K y j i)) x - dp l (dp j (fun y => K y l i)) x +
      dp l (fun y => δ i j * admVector K l y) x - dp l (fun y => δ i l * admVector K j y) x) = _
    rw [dp_scale (da l),dp_scale (da j),jet,jet,jetA,jetA]
  let P := fun a b : Index => (∑ l : Index, (J l b l a + J a l b l - J l l b a - J a b l l))/2 - U a b
  change (∑ l : Index, dp l (admSuperpotential K i j l) x) =
    -2 * P i j + δ i j * ((∑ l : Index, P l l) - ∑ l : Index, U l l)
  simp_rw [jetT]
  fin_cases i <;> fin_cases j <;> simp +decide [P,A,δ,Matrix.one_apply,Fin.sum_univ_three] <;> ring
