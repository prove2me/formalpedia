-- Prove2me | solution 1 for NoHair.spatial_ricci_flat_implies_riemann_flat_three
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:47:21.761298+00:00
-- url     : https://prove2.me/submissions/60aaf14a-8c90-4168-bc1f-b277aec4a382

import Theorems.Thm_NoHair_levi_civita_lowered_curvature_skew
import Theorems.Thm_NoHair_three_dimensional_curvature_determined_by_ricci
import Definitions.Def_NoHair_spatialRiemannCurvature

open NoHair Set Filter Bundle
open scoped Topology ContDiff Manifold

noncomputable section

open scoped Matrix
private abbrev I := Fin 3
private abbrev M := Matrix I I ℝ
theorem solution (W : Set ADMPoint) (op : IsOpen W) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (smooth : ∀ a b, ContDiffOn ℝ ∞ (fun y => h y a b) W)
    (pos : ∀ y∈W, (h y).PosDef) (x : ADMPoint) (hx : x∈W)
    (ric : ∀ b j : Fin 3, spatialRicciTensor h x b j = 0) :
    ∀ a b i j : Fin 3, spatialRiemannCurvature h x a b i j = 0 := by
  let g := h x
  let B := g⁻¹
  let U := spatialRiemannCurvature h x
  let L := fun a b i j : I => ∑ k : I, g a k * U k b i j
  have hdet := (h x).isUnit_iff_isUnit_det.mp (pos x hx).isUnit
  have inv : B*g=1 := Matrix.nonsing_inv_mul _ hdet
  have sym (i j:I) : B i j=B j i := by simpa only [star_trivial] using (pos x hx).inv.isHermitian.apply j i
  have skew2 (k b i j : I) : U k b i j = -U k b j i := by
    simp only [U,spatialRiemannCurvature,Fin.sum_univ_three]
    ring
  have second (a b i j : I) : L a b i j = -L a b j i := by
    change (∑ k : I, g a k*U k b i j) = -(∑ k : I, g a k*U k b j i)
    simp only [←Finset.sum_neg_distrib,←mul_neg]
    exact Finset.sum_congr rfl fun k _ => congrArg (fun s => g a k*s) (skew2 k b i j)
  have raise' (b i j : I) : B *ᵥ (fun a => L a b i j) = fun k => U k b i j := by
    change B *ᵥ (g *ᵥ (fun k => U k b i j)) = _
    rw [Matrix.mulVec_mulVec,inv,Matrix.one_mulVec]
  have contract (b j : I) : (∑ a : I, ∑ i : I, B a i*L a b i j)=0 := by
    rw [Finset.sum_comm]
    have re (i : I) : (∑ a : I, B a i*L a b i j) = U i b i j := by
      simpa only [Matrix.mulVec,dotProduct,show ∀ a:I, B a i=B i a from fun a => sym a i] using congrFun (raise' b i j) i
    simp_rw [re]
    exact ric b j
  have bs : B.IsSymm := Matrix.IsSymm.ext fun i j => sym _ _
  have allzero := three_dimensional_curvature_determined_by_ricci B bs (pos x hx).inv.det_pos.ne' L
    (levi_civita_lowered_curvature_skew W op h smooth pos x hx) second contract
  intro a b i j
  have eq := congrFun (raise' b i j) a
  simpa only [Matrix.mulVec,dotProduct,allzero,mul_zero,Finset.sum_const_zero] using eq.symm
