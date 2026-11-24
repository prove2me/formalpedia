-- Prove2me | solution 1 for GlobalTheory.UT.ExactTerm.exists_section_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:42:31.942007+00:00
-- url     : https://prove2.me/submissions/b367c006-a599-443e-8b2e-b491f7bf2445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorsionLift
import Theorems.Thm_GlobalTheory_UT_ExactTerm_exists_ringHom_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.ExactTerm
namespace GlobalTheory.UT.ExactTerm
theorem _root_.solution {F : Type} [Field F] [IsAlgClosed F] (O : ValuationSubring F) {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of O)) [IsFinite f] [Flat f] (p : Spec (CommRingCat.of (ResidueField O)) ⟶ H)
    (hp : p ≫ f = Spec.map (CommRingCat.ofHom (residue O))) :
    ∃ q : Spec (CommRingCat.of O) ⟶ H, q ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue O)) ≫ q = p := by
  have : IsAffine H := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = H.isoSpec.inv ≫ f := ⟨_, Spec.map_preimage _⟩
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hflat : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    exact MorphismProperty.comp_mem @Flat _ _ (inferInstance : Flat H.isoSpec.inv) ‹Flat f›
  obtain ⟨χ, hχ⟩ : ∃ χ, Spec.map χ = p ≫ H.isoSpec.hom := ⟨_, Spec.map_preimage _⟩
  let _ := φ.hom.toAlgebra
  have : Module.Finite O Γ(H, ⊤) := hfin
  have : Module.Flat O Γ(H, ⊤) := hflat
  have hcomp : χ.hom.comp (algebraMap O Γ(H, ⊤)) = residue O := by
    have h1 : Spec.map (φ ≫ χ) = Spec.map (CommRingCat.ofHom (residue O)) := by
      rw [Spec.map_comp, hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc, hp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨ψ, hψ1, hψ2⟩ := exists_ringHom_lift F χ.hom hcomp
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ H.isoSpec.inv, ?_, ?_⟩
  · have h2 : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
      exact CommRingCat.hom_ext hψ1
    rw [Category.assoc, ← hφ, ← Spec.map_comp, h2, Spec.map_id]
  · have h3 : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (residue O) = χ := by
      exact CommRingCat.hom_ext hψ2
    rw [← Category.assoc, ← Spec.map_comp, h3, hχ, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
end GlobalTheory.UT.ExactTerm
