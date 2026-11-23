-- Prove2me | solution 1 for NoHair.spatial_conformal_scalar_curvature_three
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T09:58:04.446277+00:00
-- url     : https://prove2.me/submissions/a4fd6f4e-7ae3-4686-855a-880f2f59be08
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NoHair_spatial_conformal_connection
import Theorems.Thm_NoHair_spatial_conformal_ricci_three
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

theorem solution (u : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Set ADMPoint) (hw : IsOpen W) (hu : ContDiffOn ℝ ∞ u W)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) W) (hp : ∀ x ∈ W, (h x).PosDef)
    (x : ADMPoint) (hx : x ∈ W) (hn : u x ≠ 0) :
    u x ^ 5 * spatialScalarCurvature (fun y => (u y ^ 4) • h y) x =
      u x * spatialScalarCurvature h x -
        8 * (∑ i : Fin 3, ∑ j : Fin 3, (h x)⁻¹ i j * staticSpatialHessian u h i j x) := by
  classical
  let B := (h x)⁻¹
  let k : X → Mat := fun y => u y ^ 4 • h y
  let T (A : Mat) := ∑ i : I, ∑ j : I, B i j * A i j
  let H : Mat := fun i j => staticSpatialHessian u h i j x
  let n := fun i : I => pd i u x
  let L := T H
  let E := staticLapseGradientSq u h x
  have hr (i j : I) : spatialRicciTensor k x i j = spatialRicciTensor h x i j - (2/u x)*H i j -
      (2/u x)*h x i j*L + (6/u x^2)*n i*n j - (2/u x^2)*h x i j*E :=
    spatial_conformal_ricci_three u h W hw hu hh hp x hx hn i j
  have inv := (spatial_conformal_connection u h W hw hu hh hp x hx hn).1
  have ib (i j : I) : (k x)⁻¹ i j = (u x^4)⁻¹ * B i j := congrArg (fun m : Mat => m i j) inv
  have sym (i j : I) : h x i j=h x j i := by simpa only [star_trivial] using (hp x hx).isHermitian.apply j i
  have product (i : I) : ∑ j : I, B i j*h x i j = 1 := by
    have E := congrArg (fun A : Mat => A i i)
      (Matrix.nonsing_inv_mul (h x) ((h x).isUnit_iff_isUnit_det.mp (hp x hx).isUnit))
    calc
      _ = ∑ j : I, B i j*h x j i := Finset.sum_congr rfl fun j _ => congrArg (fun t => B i j*t) (sym i j)
      _ = _ := by simpa only [B,Matrix.mul_apply,Matrix.one_apply_eq] using E
  have tM : T (h x)=3 := by simp [T,product]
  have tE : T (fun i j => n i*n j) = E := by
    simp only [T,E,n,pd,B,staticLapseGradientSq,staticRaisedGradient,Fin.sum_univ_three]
    ring
  have contract : spatialScalarCurvature k x = (u x^4)⁻¹ *
      (spatialScalarCurvature h x - (2/u x)*L - (2/u x)*T (h x)*L +
        (6/u x^2)*T (fun i j => n i*n j) - (2/u x^2)*T (h x)*E) := by
    simp only [spatialScalarCurvature,ib,hr,T,L,Fin.sum_univ_three,B]
    ring
  change u x^5 * spatialScalarCurvature k x = u x * spatialScalarCurvature h x - 8*L
  rw [contract,tM,tE]
  field_simp [hn] <;> ring
