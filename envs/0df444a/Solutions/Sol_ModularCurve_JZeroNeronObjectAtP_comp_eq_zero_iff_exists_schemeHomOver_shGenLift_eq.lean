-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/aabfdbb2-9970-5c61-bc40-a530e1a7a96c

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (x : ↥(inertiaInvariants A (N₀ * p))) :
    O.comp x = 0 ↔
      ∃ s : SchemeHomOver (𝟙 (shBase A)) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g),
        (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = (barPt A ≫ shPt A) ≫ s.1 := by
  classical
  haveI : Fact p.Prime := inferInstance
  let ιK : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥(invField A)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))
  let ιOK : Spec (CommRingCat.of ↥(invField A)) ⟶ shBase A :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A)))

  have hbar : barPt A ≫ shPt A = ιK ≫ ιOK := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl

  have hP1 : (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 ≫ pullback.fst O.g Λ.shStr = (O.pts (x : JZero (N₀ * p))).1 :=
    pullback.lift_fst _ _ _
  have hP2 : (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 ≫ pullback.snd O.g Λ.shStr = barPt A ≫ shPt A :=
    (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).2
  constructor
  ·
    intro hx
    have hs := (O.comp_eq_zero_iff x).1 hx
    rcases hs with ⟨s₀, hs₀⟩

    let y' : SchemeHomOver (shPt A) (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) := Λ.shLift s₀
    have hy'1 : y'.1 ≫ pullback.fst O.g Λ.shStr = s₀.1 := by
      exact pullback.lift_fst _ _ _
    have hPy : (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = barPt A ≫ y'.1 := by
      apply pullback.hom_ext
      · rw [hP1, Category.assoc, hy'1]; exact hs₀
      · rw [hP2, Category.assoc, y'.2]

    have hinv : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
        Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toRingHom) ≫ (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 := by
      intro σ hσ
      apply pullback.hom_ext
      · rw [Category.assoc, hP1]
        have h := O.pts_galois σ (x : JZero (N₀ * p))
        rw [show σ • (x : JZero (N₀ * p)) = x from (mem_inertiaInvariants (A := A) (M := N₀ * p)).1 x.2 σ hσ] at h
        exact h.symm
      · rw [Category.assoc, hP2, hbar, ← Category.assoc]
        congr 1
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro k
        change σ ((k : ↥(invField A)) : AlgebraicClosure ℚ) = ((k : ↥(invField A)) : AlgebraicClosure ℚ)
        exact (IntermediateField.mem_fixedField_iff _ _).1 k.2 σ hσ
    have hdesc := AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq (A.inertiaSubgroupIn ℚ) (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 hinv
    rcases hdesc with ⟨yK, hyK⟩

    have hyK_over : yK ≫ pullback.snd O.g Λ.shStr = ιOK := by
      have hsurj := Spec.map_surjective (yK ≫ pullback.snd O.g Λ.shStr)
      rcases hsurj with ⟨φ, hφ⟩
      rw [← hφ]
      have h : ιK ≫ Spec.map φ = ιK ≫ ιOK := by
        rw [hφ, ← Category.assoc, hyK, hP2, hbar]
      change Spec.map _ ≫ Spec.map φ = Spec.map _ ≫ Spec.map _ at h
      rw [← Spec.map_comp, ← Spec.map_comp] at h
      have h' := Spec.map_injective h
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      have := congrArg (fun f : CommRingCat.of ↥(shRing A) ⟶ CommRingCat.of (AlgebraicClosure ℚ) => f.hom r) h'
      exact (algebraMap ↥(invField A) (AlgebraicClosure ℚ)).injective this

    have h7056 := ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA
    rcases h7056 with ⟨hDVR, -, -, -⟩
    haveI : IsDiscreteValuationRing ↥(shRing A) := hDVR
    letI : Algebra ↥(shRing A) ↥A := (shToPlace A).toAlgebra
    haveI : IsLocalHom (algebraMap ↥(shRing A) ↥A) := by
      refine ⟨fun a ha => ?_⟩
      obtain ⟨u, hu⟩ := ha
      have hval : ((u : ↥A) : AlgebraicClosure ℚ) = ((a : ↥(invField A)) : AlgebraicClosure ℚ) := by
        rw [hu]; rfl
      have h1 : ((u : ↥A) : AlgebraicClosure ℚ) * (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = 1 := by
        change (((u : ↥A) * ((u⁻¹ : (↥A)ˣ) : ↥A) : ↥A) : AlgebraicClosure ℚ) = 1
        rw [Units.mul_inv]; rfl
      have hane : (a : ↥(invField A)) ≠ 0 := by
        intro h0
        have : ((u : ↥A) : AlgebraicClosure ℚ) = 0 := by rw [hval, h0]; rfl
        exact one_ne_zero (by rw [← h1, this, zero_mul])
      have hinvmem : ((a : ↥(invField A))⁻¹ : ↥(invField A)) ∈ shRing A := by
        change algebraMap ↥(invField A) (AlgebraicClosure ℚ) ((a : ↥(invField A))⁻¹) ∈ A
        rw [map_inv₀]
        change (((a : ↥(invField A)) : AlgebraicClosure ℚ))⁻¹ ∈ A
        rw [← hval, inv_eq_of_mul_eq_one_right h1]
        exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
      exact ⟨⟨a, ⟨(a : ↥(invField A))⁻¹, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hane), Subtype.ext (inv_mul_cancel₀ hane)⟩, rfl⟩
    haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) := by
      haveI := O.separated; exact MorphismProperty.pullback_snd _ _ inferInstance
    haveI : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) := by
      haveI := O.locallyOfFiniteType; exact MorphismProperty.pullback_snd _ _ inferInstance
    haveI : QuasiCompact (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) := by
      haveI := O.quasiCompact; exact MorphismProperty.pullback_snd _ _ inferInstance
    have hED :=
      AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom ↥(invField A)
        (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) yK hyK_over ↥A (AlgebraicClosure ℚ) y'.1 y'.2
        (by rw [hyK]; exact hPy)
    rcases hED with ⟨sO, hsO1, hsO2⟩
    refine ⟨⟨sO, hsO1⟩, ?_⟩
    change (Λ.shGenLift (O.pts (x : JZero (N₀ * p)))).1 = (barPt A ≫ shPt A) ≫ sO
    rw [← hyK, ← hsO2, ← Category.assoc]
    congr 1
    exact hbar.symm
  ·
    rintro ⟨s, hs⟩
    refine (O.comp_eq_zero_iff x).2 ⟨⟨shPt A ≫ s.1 ≫ pullback.fst O.g Λ.shStr, ?_⟩, ?_⟩
    · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc s.1, s.2, Category.id_comp]
      exact Λ.shPt_comp_shStr
    · change (O.pts (x : JZero (N₀ * p))).1 = barPt A ≫ shPt A ≫ s.1 ≫ pullback.fst O.g Λ.shStr
      rw [← hP1, hs, Category.assoc, Category.assoc]

end S_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_comp_eq_zero_iff_exists_schemeHomOver_shGenLift_eq (solution)
