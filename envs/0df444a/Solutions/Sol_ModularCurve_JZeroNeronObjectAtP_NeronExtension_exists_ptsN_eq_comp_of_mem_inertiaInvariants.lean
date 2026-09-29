-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_ptsN_eq_comp_of_mem_inertiaInvariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/577a9ef9-be6d-5927-a488-74819088bff9

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_exists_section_comp_eq
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace DESCENTPTN

variable (A : ValuationSubring (AlgebraicClosure ℚ))

theorem subtype_comp_shToPlace :
    A.subtype.comp (shToPlace A) =
      (algebraMap ↥(invField A) (AlgebraicClosure ℚ)).comp (algebraMap ↥(shRing A) ↥(invField A)) := by
  ext x; rfl

theorem barPt_comp_shPt :
    barPt A ≫ shPt A = Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A))) := by
  show Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (shToPlace A)) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_shToPlace]

theorem comp_algebraMap_invField_of_mem (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (algebraMap ↥(invField A) (AlgebraicClosure ℚ)) =
      algebraMap ↥(invField A) (AlgebraicClosure ℚ) := by
  ext k
  show σ (k : AlgebraicClosure ℚ) = k
  have hk := k.2
  rw [IntermediateField.mem_fixedField_iff] at hk
  exact hk σ hσ

theorem specMap_comp_barPt_shPt_of_mem (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A ≫ shPt A =
      barPt A ≫ shPt A := by
  rw [barPt_comp_shPt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    comp_algebraMap_invField_of_mem A σ hσ]

end DESCENTPTN

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    ∀ x : JZero (N₀ * p), x ∈ inertiaInvariants A (N₀ * p) →
      ∃ s : SchemeHomOver (𝟙 (shBase A)) F.gN, (F.ptsN x).1 = (barPt A ≫ shPt A) ≫ s.1 := by
  intro x hx
  rw [mem_inertiaInvariants] at hx

  haveI : IsDiscreteValuationRing ↥(shRing A) :=
    (ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA).1
  haveI : IsDedekindDomain ↥(shRing A) := inferInstance
  set y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ F.Nfull := (F.ptsN x).1 with hydef
  have hy_over : y ≫ F.gN = barPt A ≫ shPt A := (F.ptsN x).2

  have hinv : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ y = y := by
    intro σ hσ
    have hlift : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        (Λ.shGenLift (O.pts x)).1 = (Λ.shGenLift (O.pts (σ • x))).1 := by
      simp only [LevelData.shGenLift, RelativeGroupLaw.baseChangePointOfBase, castOver]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        exact (O.pts_galois σ x).symm
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
        exact DESCENTPTN.specMap_comp_barPt_shPt_of_mem A σ hσ
    have e1 : y = (Λ.shGenLift (O.pts x)).1 ≫ F.openImm.1 := rfl
    rw [e1, ← Category.assoc, hlift, hx σ hσ]

  have hinv' : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toRingHom) ≫ y = y := by
    intro σ hσ
    have e : (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toRingHom =
        (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) := RingHom.ext fun _ => rfl
    rw [e]; exact hinv σ hσ
  obtain ⟨y₀, hy₀⟩ :=
    AlgebraicGeometry.Scheme.exists_specMap_fixedField_comp_eq_of_forall_comp_eq (A.inertiaSubgroupIn ℚ) y hinv'

  have hy₀_over : y₀ ≫ F.gN = Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A))) := by
    have h1 : Spec.map (Spec.preimage (y₀ ≫ F.gN)) = y₀ ≫ F.gN := Spec.map_preimage _
    have h2 : Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
        Spec.map (Spec.preimage (y₀ ≫ F.gN)) =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A))) := by
      rw [h1, ← Category.assoc, hy₀, hy_over, DESCENTPTN.barPt_comp_shPt]
    rw [← Spec.map_comp, ← Spec.map_comp] at h2
    have h3 := Spec.map_injective h2
    have h4 : Spec.preimage (y₀ ≫ F.gN) = CommRingCat.ofHom (algebraMap ↥(shRing A) ↥(invField A)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      apply (algebraMap ↥(invField A) (AlgebraicClosure ℚ)).injective
      have := congrArg (fun f => (CommRingCat.Hom.hom f) r) h3
      simpa using this
    rw [← h1, h4]

  obtain ⟨s, hs⟩ := NeronModelInfra.NeronModelPropertyBundle.exists_section_comp_eq F.hN y₀ hy₀_over

  refine ⟨s, ?_⟩
  show y = (barPt A ≫ shPt A) ≫ s.1
  rw [DESCENTPTN.barPt_comp_shPt, Category.assoc, hs, hy₀]

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_ptsN_eq_comp_of_mem_inertiaInvariants (solution)
