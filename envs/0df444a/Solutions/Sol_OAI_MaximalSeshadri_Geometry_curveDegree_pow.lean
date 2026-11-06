-- Prove2me | solution 1 for OAI.MaximalSeshadri.Geometry.curveDegree_pow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:59:08.832576+00:00
-- url     : https://prove2.me/submissions/d1813401-40b8-4c40-b95d-013cc94cb374
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MaximalSeshadriConstants
import Definitions.Def_SeshadriPrelim6
import Theorems.Thm_OAI_MaximalSeshadri_Geometry_curveDegree_tensor

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open OAI OAI.MaximalSeshadri.Geometry MaximalSeshadri.Frames

private def cohomologyIso_solution {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars f)
    let _ := Module.compHom (cohomology N n) (baseScalars f)
    cohomology M n ≃ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars f)
  letI := Module.compHom (cohomology N n) (baseScalars f)
  let g := (Ext.mk₀ e.hom).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  let h := (Ext.mk₀ e.inv).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  refine
    { toFun := g
      invFun := h
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars f r) x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (x.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.comp_mk₀_id]
  · intro x
    change (x.comp (Ext.mk₀ e.inv) (add_zero n)).comp (Ext.mk₀ e.hom) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.comp_mk₀_id]

private lemma eulerCharacteristic_iso_solution {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of ℂ)) {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso_solution f e n).finrank_eq

theorem solution (S : Surface) (A : LineBundle S.scheme) (hA : A.IsAmple)
    (L : LineBundle S.scheme) (C : IntegralCurve S) (n : ℕ) :
    curveDegree S (L.pow n) C = (n : ℤ) * curveDegree S L C := by
  induction n with
  | zero =>
    have hi := eulerCharacteristic_iso_solution (C.embedding ≫ S.structureMap)
      (pullbackUnitIso C.embedding) 1
    simp only [Nat.cast_zero, zero_mul]
    unfold curveDegree
    change eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        ((Scheme.Modules.pullback C.embedding).obj
          (SheafOfModules.unit S.scheme.ringCatSheaf)) -
      eulerCharacteristic (C.embedding ≫ S.structureMap) 1
        (SheafOfModules.unit C.scheme.ringCatSheaf) = 0
    exact sub_eq_zero.mpr hi
  | succ n ih =>
    change curveDegree S (L.tensor (L.pow n)) C =
      ((n + 1 : ℕ) : ℤ) * curveDegree S L C
    rw [curveDegree_tensor S A hA L (L.pow n) C, ih]
    push_cast
    ring
