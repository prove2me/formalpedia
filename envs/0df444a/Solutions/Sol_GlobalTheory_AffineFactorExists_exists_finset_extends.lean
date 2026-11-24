-- Prove2me | solution 1 for GlobalTheory.AffineFactorExists.exists_finset_extends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:41.018596+00:00
-- url     : https://prove2.me/submissions/bff1480c-7593-4d54-9312-c6cdcf697db3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFactorFractionRing
import Theorems.Thm_GlobalTheory_AffineFactorExists_exists_affine_factor
import Theorems.Thm_GlobalTheory_AffineFactorExists_exists_factor_fractionRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.AffineFactorExists
namespace GlobalTheory.AffineFactorExists
theorem _root_.solution (V F : Type) [CommRing V] [Field F] [Algebra V F]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f]
    (x : Spec (CommRingCat.of F) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V F))) :
    ∃ t : Finset F, ∀ W : Subalgebra V F, ValuationRing W →
      (∀ x ∈ t, ∃ a ∈ W, ∃ b ∈ W, b ≠ (0 : F) ∧ x * b = a) →
      ∃ y : Spec (CommRingCat.of W) ⟶ X,
        y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap V W)) ∧
        Spec.map (CommRingCat.ofHom (algebraMap W F)) ≫ y = x := by
  classical
  obtain ⟨A, ι, hι, φ, hφ⟩ := exists_affine_factor x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (ι ≫ f)
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  have hcomp : ψ ≫ φ = CommRingCat.ofHom (algebraMap V F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← Category.assoc, hφ, hx]
  letI : Algebra V A := ψ.hom.toAlgebra
  have hft' : Algebra.FiniteType V A := hft
  obtain ⟨s, hs⟩ := hft'.out
  let φa : A →ₐ[V] F :=
    { φ.hom with commutes' := fun r => congrArg (fun g => g.hom r) hcomp }
  refine ⟨s.image φ.hom, fun W hW ht => ?_⟩
  obtain ⟨j, φ', hj, hφ'⟩ := exists_factor_fractionRing φa s hs W
    (fun a ha => ht _ (Finset.mem_image_of_mem _ ha))
  have hE : ValuativeCriterion.Existence f := by
    have : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at this
    exact this.1
  have hring : ψ ≫ CommRingCat.ofHom φ' =
      CommRingCat.ofHom (algebraMap V W) ≫
        CommRingCat.ofHom (algebraMap W (FractionRing W)) := by
    ext r
    apply j.injective
    have h1 := RingHom.congr_fun hφ' (ψ.hom r)
    have h2 := RingHom.congr_fun hj (algebraMap V W r)
    exact (h1.trans (φa.commutes r)).trans h2.symm
  have w : (Spec.map (CommRingCat.ofHom φ') ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap W (FractionRing W))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V W)) := by
    rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp, hring]
  obtain ⟨l, hl₁, hl₂⟩ :=
    (hE { R := W, K := FractionRing W, commSq := ⟨w⟩, .. }).exists_lift
  dsimp only at hl₁ hl₂
  refine ⟨l, hl₂, ?_⟩
  have e₁ : CommRingCat.ofHom (algebraMap W F) =
      CommRingCat.ofHom (algebraMap W (FractionRing W)) ≫ CommRingCat.ofHom j := by
    rw [← hj]; rfl
  have e₂ : φ = CommRingCat.ofHom φ' ≫ CommRingCat.ofHom j := by
    ext a
    exact (RingHom.congr_fun hφ' a).symm
  rw [e₁, Spec.map_comp, Category.assoc, hl₁, ← Category.assoc, ← Spec.map_comp, ← e₂, hφ]
end GlobalTheory.AffineFactorExists
