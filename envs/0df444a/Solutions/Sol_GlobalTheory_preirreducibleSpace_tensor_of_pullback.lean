-- Prove2me | solution 1 for GlobalTheory.preirreducibleSpace_tensor_of_pullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:29:51.213388+00:00
-- url     : https://prove2.me/submissions/47e141f8-9c06-41f5-bcb0-a15ed2847d25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleSpaceTensorOfPullback
import Theorems.Thm_GlobalTheory_isPullback_comp_mono_right_of_isPullback

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
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
      (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k]
      [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom →
      PreirreducibleSpace ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  intro X S f V W h hV hW k _ _ _ hA hP
  have sq := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, V) k Γ(X, W))).flip
  have sq2 := sq.of_iso (fst' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
      hW.isoSpec.inv) (snd' := Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom))
    (f' := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W))))
    (g' := Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)))
    (Iso.refl _) hW.isoSpec.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)
  have sq3 := isPullback_comp_mono_right_of_isPullback hV.fromSpec sq2
  have e : (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, W)))) ≫
      hV.fromSpec = W.ι ≫ f := by
    rw [hA, CommRingCat.ofHom_hom, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec f hV hW h,
      ← hW.isoSpec_inv_ι, Category.assoc, Iso.hom_inv_id_assoc]
  rw [e] at sq3
  let φ := sq3.isoPullback
  have hsurj : Function.Surjective (Scheme.homeoOfIso φ.symm) := (Scheme.homeoOfIso φ.symm).surjective
  refine ⟨?_⟩
  have := (PreirreducibleSpace.isPreirreducible_univ (X := ↥(pullback (W.ι ≫ f)
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)))).image
    (Scheme.homeoOfIso φ.symm) (Scheme.homeoOfIso φ.symm).continuous.continuousOn
  rw [Set.image_univ_of_surjective hsurj] at this
  exact this
end GlobalTheory
