-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:13:55.753645+00:00
-- url     : https://prove2.me/submissions/d3f8f35c-8747-4907-b3cf-ee3310d22084

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_hom_eq_iff_forall_field
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_some
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_toAffineLift
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofProjectivePoint_comp_left
import Theorems.Thm_GlobalTheory_WeierstrassCurve_ofAffinePoint_map_left
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_apply
import Theorems.Thm_GlobalTheory_WeierstrassCurve_projectivePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affinePointEquiv_symm_zeroOver
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineX
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_affineY
import Theorems.Thm_GlobalTheory_WeierstrassCurve_affineMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_algebraMap
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originW
import Theorems.Thm_GlobalTheory_WeierstrassCurve_originMap_originZ
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
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_algebraMap
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originW
attribute [local simp] GlobalTheory.WeierstrassCurve.originMap_originZ


attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_zero
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_some
attribute [local simp] GlobalTheory.WeierstrassCurve.ofAffinePoint_toAffineLift
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_apply
attribute [local simp] GlobalTheory.WeierstrassCurve.projectivePointEquiv_symm_zeroOver
attribute [local simp] GlobalTheory.WeierstrassCurve.affinePointEquiv_symm_zeroOver

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution :
    (∀ (A : Type u) [CommRing A] [Algebra R A] (P Q : Fin 3 → A)
      (hP : IsUnimodularSol (W.baseChange A) P) (hQ : IsUnimodularSol (W.baseChange A) Q),
      pt W P hP = pt W Q hQ ↔ ∃ v : Aˣ, Q = (v : A) • P) ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A],
      ∃ e : UnimodularClass (W.baseChange A) ≃
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶ schemeOver W),
        ∀ P h, (e (Quotient.mk _ ⟨P, h⟩)).left = pt W P h) ∧
    (W.IsElliptic →
      ∃ (e : ∀ (k : Type u) [Field k] [Algebra R k], (W.baseChange k).toAffine.Point ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W))
        (e' : ∀ (k : Type u) [Field k] [Algebra R k], (W.baseChange k).toProjective.Point ≃
          (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R k))) ⟶ schemeOver W)),
        (∀ (k : Type u) [Field k] [Algebra R k],
          (e k 0).left = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ zero W ∧
          (e' k 0).left = Spec.map (CommRingCat.ofHom (algebraMap R k)) ≫ zero W ∧
          (∀ a b h, (e k (.some a b h)).left = pt W ![a, b, 1] (isUnimodularSol_some h.left)) ∧
          (∀ (P : Fin 3 → k)
            (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P)),
            (e' k ⟨h⟩).left = pt W P (.of_nonsingular h)) ∧
          (∀ p, e k p.toAffineLift = e' k p)) ∧
        ∀ (k K : Type u) [Field k] [Field K] [Algebra R k] [Algebra R K] [DecidableEq k]
          [DecidableEq K] (f : k →ₐ[R] K),
          (∀ p : (W.baseChange k).toAffine.Point,
            (e K (WeierstrassCurve.Affine.Point.map (W' := W.toAffine) f p)).left =
              Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (e k p).left) ∧
          ∀ (P : Fin 3 → k)
            (h : (W.baseChange k).toProjective.NonsingularLift (Quotient.mk _ P))
            (h' : (W.baseChange K).toProjective.NonsingularLift (Quotient.mk _ (f ∘ P))),
            (e' K ⟨h'⟩).left = Spec.map (CommRingCat.ofHom (f : k →+* K)) ≫ (e' k ⟨h⟩).left) ∧
    (∀ (T Y : Over (Spec (.of R))) [IsReduced T.left] [IsSeparated Y.hom] (f g : T ⟶ Y),
      f = g ↔ ∀ (k : Type u) [Field k] (x : Spec (.of k) ⟶ T.left), x ≫ f.left = x ≫ g.left) :=
  ⟨fun _ _ _ _ _ hP hQ => pt_eq_pt_iff W hP hQ,
    fun A _ _ _ => ⟨ptClassEquiv W A, fun _ _ => rfl⟩,
    fun _ => ⟨fun k _ _ => affinePointEquiv W k, fun k _ _ => projectivePointEquiv W k,
      fun k _ _ => ⟨congrArg (·.left) (ofAffinePoint_zero W k),
        congrArg (·.left) (ofProjectivePoint_zero W k), fun _ _ _ => rfl, fun _ _ => rfl,
        ofAffinePoint_toAffineLift W⟩,
      fun _ _ _ _ _ _ _ _ f => ⟨ofAffinePoint_map_left W f,
        fun _ h h' => ofProjectivePoint_comp_left W f h h'⟩⟩,
    fun _ Y _ _ f g => Iff.trans ⟨fun e => congrArg (·.left) e, fun e => Over.OverMorphism.ext e⟩
      (hom_eq_iff_forall_field Y.hom ((Over.w f).trans (Over.w g).symm))⟩
end GlobalTheory.WeierstrassCurve
