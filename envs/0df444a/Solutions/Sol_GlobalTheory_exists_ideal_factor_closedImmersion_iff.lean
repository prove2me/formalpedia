-- Prove2me | solution 1 for GlobalTheory.exists_ideal_factor_closedImmersion_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:38.031806+00:00
-- url     : https://prove2.me/submissions/c3d860f5-d4ea-4a08-94a0-d18fe67151fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalRingPointsIdealCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A] (X Y : Scheme.{0})
    (a : Spec (CommRingCat.of A) ⟶ X) (j : Y ⟶ X) [IsClosedImmersion j] :
    ∃ I : Ideal A, ∀ (R : Type) [CommRing R] (ψ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ Y, y ≫ j = Spec.map (CommRingCat.ofHom ψ) ≫ a) ↔
        I ≤ RingHom.ker ψ := by
  obtain ⟨I, e, hf⟩ := (IsClosedImmersion.Spec_iff (f := pullback.snd j a)).mp inferInstance
  refine ⟨I, fun R _ ψ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    let z : Spec (CommRingCat.of R) ⟶ pullback j a := pullback.lift y (Spec.map (CommRingCat.ofHom ψ)) hy
    have hz : z ≫ pullback.snd j a = Spec.map (CommRingCat.ofHom ψ) := pullback.lift_snd _ _ _
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (z ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ χ) = Spec.map (CommRingCat.ofHom ψ) := by
      rw [Spec.map_comp, hχ, Category.assoc, ← hf, hz]
    have h2 := Spec.map_injective h1
    intro x hx
    have := congrArg (fun g => g.hom x) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at this
    rw [RingHom.mem_ker, ← this, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ (fun x hx => h hx))) ≫ e.inv ≫ pullback.fst j a, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, hf, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc]
    congr 2
end GlobalTheory
