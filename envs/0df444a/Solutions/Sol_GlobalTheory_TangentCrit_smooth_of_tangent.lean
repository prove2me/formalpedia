-- Prove2me | solution 1 for GlobalTheory.TangentCrit.smooth_of_tangent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:06.891905+00:00
-- url     : https://prove2.me/submissions/94a0fd40-151f-4863-8e74-9394eef759ab

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Theorems.Thm_GlobalTheory_TangentCrit_formallySmooth_of_dual_lift
import Theorems.Thm_GlobalTheory_TangentCrit_locallyOfFinitePresentation_of_comp
import Theorems.Thm_GlobalTheory_TangentCrit_SpecMap_fromSpecStalk_closedPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace GlobalTheory.TangentCrit
theorem _root_.solution {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S) [Smooth (f ≫ π)]
    [LocallyOfFiniteType π]
    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
      (v : Spec (.of (DualNumber k)) ⟶ Y), dualPt k ≫ v = x ≫ f → v ≫ π = dualBase k ≫ x ≫ f ≫ π →
      ∃ w : Spec (.of (DualNumber k)) ⟶ X, dualPt k ≫ w = x ∧ w ≫ f = v) :
    Smooth f := by
  have := locallyOfFinitePresentation_of_comp f π
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro x -
  let k := AlgebraicClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
  let ξ : X.presheaf.stalk x →+* k := (algebraMap _ k).comp (IsLocalRing.residue _)
  have hξ : IsLocalHom ξ := inferInstance
  have e : (f.stalkMap x).hom.comp (π.stalkMap (f x)).hom = ((f ≫ π).stalkMap x).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  refine formallySmooth_of_dual_lift (π.stalkMap (f x)).hom (f.stalkMap x).hom
    (LocallyOfFiniteType.stalkMap π _) (e ▸ LocallyOfFiniteType.stalkMap (f ≫ π) x)
    (e ▸ (f ≫ π).smoothLocus_eq_top.ge (Set.mem_univ x)) ξ fun ψ h₁ h₂ => ?_
  obtain ⟨w, hw₁, hw₂⟩ := H k (Spec.map (CommRingCat.ofHom ξ) ≫ X.fromSpecStalk x)
    (Spec.map (CommRingCat.ofHom ψ) ≫ Y.fromSpecStalk (f x)) (by
      simp only [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]
      congr 2
      ext a
      exact h₁ a) (by
      rw [Category.assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc,
        ← Scheme.SpecMap_stalkMap_fromSpecStalk]
      simp only [← Spec.map_comp_assoc]
      congr 2
      ext a
      · exact h₁ _
      · exact h₂ a)
  obtain ⟨⟨y, φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (.of (DualNumber k))).symm.surjective w
  change _ ≫ Spec.map φ ≫ X.fromSpecStalk y = _ at hw₁
  change (Spec.map φ ≫ X.fromSpecStalk y) ≫ f = _ at hw₂
  rw [← Spec.map_comp_assoc] at hw₁
  obtain rfl : y = x := by
    have h₃ : IsLocalHom (CommRingCat.ofHom ξ).hom := hξ
    have h₄ : IsLocalHom (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
      ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
    have h₅ : IsLocalHom (φ ≫ CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom).hom :=
      RingHom.isLocalHom_comp _ _
    exact (SpecMap_fromSpecStalk_closedPoint _).symm.trans
      ((congrArg (fun g : Spec (.of k) ⟶ X => g (IsLocalRing.closedPoint k)) hw₁).trans
        (SpecMap_fromSpecStalk_closedPoint _))
  rw [cancel_mono, Spec.map_inj] at hw₁
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, cancel_mono,
    Spec.map_inj] at hw₂
  exact ⟨φ.hom, fun b => congr($hw₁ b), fun a => congr($hw₂ a)⟩
end GlobalTheory.TangentCrit
