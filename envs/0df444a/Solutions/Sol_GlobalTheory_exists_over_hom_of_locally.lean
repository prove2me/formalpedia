-- Prove2me | solution 1 for GlobalTheory.exists_over_hom_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:23.779791+00:00
-- url     : https://prove2.me/submissions/0553a261-0a6e-4e7b-9409-248c838aee0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Theorems.Thm_GlobalTheory_ProjPoint_hom_ext
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_over_hom_eq_iff_forall_field_algebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineX
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_affineY
attribute [local simp] GlobalTheory.WeierstrassCurve.affineMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
variable {R : Type u} [CommRing R]
namespace GlobalTheory
theorem _root_.solution {T Y : Over (Spec (.of R))} [IsReduced T.left]
    [IsSeparated Y.hom]
    (F : ∀ (k : Type u) [Field k] [Algebra R k], (specOver R k ⟶ T) → (specOver R k ⟶ Y))
    (H : ∀ t : T.left, ∃ (U : Over (Spec (.of R))) (j : U ⟶ T) (_ : IsOpenImmersion j.left)
      (f : U ⟶ Y), t ∈ Set.range j.left ∧
        ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ U), x ≫ f = F k (x ≫ j)) :
    ∃ f : T ⟶ Y, ∀ (k : Type u) [Field k] [Algebra R k] (x : specOver R k ⟶ T),
      x ≫ f = F k x := by
  choose U j hj fU hmem hfU using H
  let 𝒰 : T.left.OpenCover :=
    { I₀ := T.left, X i := (U i).left, f i := (j i).left,
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun t ↦ ⟨t, by simpa using hmem t⟩, fun i ↦ hj i⟩ }
  have hcomp : ∀ a b, pullback.fst (j a).left (j b).left ≫ (fU a).left =
      pullback.snd (j a).left (j b).left ≫ (fU b).left := by
    intro a b
    have := hj a
    have := hj b
    let P : Over (Spec (.of R)) :=
      Over.mk (pullback.fst (j a).left (j b).left ≫ (j a).left ≫ T.hom)
    haveI : IsReduced P.left :=
      isReduced_of_isOpenImmersion (pullback.fst (j a).left (j b).left ≫ (j a).left)
    let p₁ : P ⟶ U a := Over.homMk (pullback.fst _ _) (by
      show _ = pullback.fst _ _ ≫ (j a).left ≫ T.hom
      rw [Over.w])
    let p₂ : P ⟶ U b := Over.homMk (pullback.snd _ _) (by
      show _ = pullback.fst _ _ ≫ (j a).left ≫ T.hom
      rw [pullback.condition_assoc, Over.w])
    have hp : p₁ ≫ j a = p₂ ≫ j b := by
      ext
      simp [p₁, p₂, pullback.condition]
    have key : p₁ ≫ fU a = p₂ ≫ fU b := by
      rw [over_hom_eq_iff_forall_field_algebra]
      intro k _ _ x
      rw [← Category.assoc, ← Category.assoc, hfU, hfU, Category.assoc, Category.assoc, hp]
    simpa [p₁, p₂] using congrArg CommaMorphism.left key
  let g₀ : T.left ⟶ Y.left := 𝒰.glueMorphisms (fun t ↦ (fU t).left) hcomp
  have hg : ∀ t, (j t).left ≫ g₀ = (fU t).left := fun t ↦ 𝒰.ι_glueMorphisms _ hcomp t
  have hw : g₀ ≫ Y.hom = T.hom := by
    refine 𝒰.hom_ext _ _ fun t ↦ ?_
    change (j t).left ≫ g₀ ≫ Y.hom = (j t).left ≫ T.hom
    rw [← Category.assoc, hg, Over.w, Over.w]
  refine ⟨Over.homMk g₀ hw, fun k _ _ x ↦ ?_⟩
  set t := x.left (IsLocalRing.closedPoint k) with ht
  have := hj t
  have hr : Set.range x.left ⊆ Set.range (j t).left := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim (α := ↥(Spec (CommRingCat.of k))) p (IsLocalRing.closedPoint k)]
    exact hmem t
  let y₀ : Spec (.of k) ⟶ (U t).left := IsOpenImmersion.lift (j t).left x.left hr
  have hy₀ : y₀ ≫ (j t).left = x.left := IsOpenImmersion.lift_fac _ _ _
  let y : specOver R k ⟶ U t := Over.homMk y₀ (by
    rw [← Over.w (j t), ← Category.assoc, hy₀, Over.w])
  have hxy : x = y ≫ j t := by
    ext
    simp [y, hy₀]
  have hjt : j t ≫ Over.homMk g₀ hw = fU t := by
    ext
    simp [hg]
  rw [hxy, Category.assoc, hjt, hfU]
end GlobalTheory
