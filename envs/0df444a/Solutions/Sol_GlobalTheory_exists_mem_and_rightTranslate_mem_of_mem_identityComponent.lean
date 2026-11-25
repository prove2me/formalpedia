-- Prove2me | solution 1 for GlobalTheory.exists_mem_and_rightTranslate_mem_of_mem_identityComponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:44.146809+00:00
-- url     : https://prove2.me/submissions/461f3d47-d5f6-4d56-ad0b-fffbf90357bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMemRightTranslateMemIdentityComponent
import Theorems.Thm_GlobalTheory_T_isOpen_isIrreducible_componentOfRationalPoint_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G], Smooth G.hom → ∀ (U : G.left.Opens) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G), (η[G]).left (IsLocalRing.closedPoint k) ∈ U → y.left (IsLocalRing.closedPoint k) ∈ connectedComponent ((η[G]).left (IsLocalRing.closedPoint k)) → ∃ z : G.left, z ∈ U ∧ (𝟙 G * (toUnit G ≫ y) : G ⟶ G).left z ∈ U := by
  intro k _ G _ hs U y hU hy
  set e : G.left := (η[G]).left (IsLocalRing.closedPoint k) with he
  have hirr : IsIrreducible (connectedComponent e) := by
    have h := (GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth k G.left G.hom (η[G]).left hs (Over.w (η[G]))).2
    have hsub : ∀ a : Spec (CommRingCat.of k), a = IsLocalRing.closedPoint k := fun a =>
      Subsingleton.elim (α := PrimeSpectrum k) _ _
    convert h using 1
    ext x
    have h1 : (G.hom ⁻¹' {G.hom x} : Set G.left) = Set.univ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact (hsub _).trans (hsub _).symm
    simp only [Set.mem_ofPred_eq]
    rw [h1, connectedComponentIn_univ, hsub (G.hom x)]
  let T : G ⟶ G := 𝟙 G * (toUnit G ≫ y)
  have hT : (y ≫ ι[G]) ≫ T = η[G] := by
    have h1 : (y ≫ ι[G]) ≫ T = (y ≫ ι[G]) * y := by
      simp only [T]
      rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit, toUnit_unit,
        Category.id_comp]
    rw [h1]
    have h2 : (y ≫ ι[G]) = y⁻¹ := rfl
    rw [h2, inv_mul_cancel, Hom.one_def, toUnit_unit, Category.id_comp]
  have hιe : (ι[G]).left e = e := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    have h2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) this
    exact h2
  have hyi : (ι[G]).left (y.left (IsLocalRing.closedPoint k)) ∈ connectedComponent e := by
    have hc := (ι[G]).left.continuous.image_connectedComponent_subset e
    rw [hιe] at hc
    exact hc ⟨_, hy, rfl⟩
  have hTy : T.left ((ι[G]).left (y.left (IsLocalRing.closedPoint k))) = e := by
    have h2 := congrArg (fun f => f.left (IsLocalRing.closedPoint k)) hT
    exact h2
  obtain ⟨z, -, hz1, hz2⟩ := hirr.isPreirreducible (U : Set G.left) (T.left ⁻¹' (U : Set G.left))
    U.isOpen (U.isOpen.preimage T.left.continuous) ⟨e, mem_connectedComponent, hU⟩
    ⟨_, hyi, by rw [Set.mem_preimage, hTy]; exact hU⟩
  exact ⟨z, hz1, hz2⟩
end GlobalTheory
