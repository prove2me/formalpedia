-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/a434b268-6845-5051-ba9f-49e4d843c435

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_XHDRModelAtPCrossingFrame
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))

    (O : Type) [CommRing O] (ρO : R p →+* O)
    (jO : O →+* AlgebraicClosure ℚ) (hjO : jO.comp ρO = algebraMap (R p) (AlgebraicClosure ℚ))
    (ιA : O →+* ↥A) (hιA : A.subtype.comp ιA = jO)
    (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    ∃ sA : Spec (CommRingCat.of ↥A) ⟶ XO (ΓM M H) hj ρO,
      sA ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ιA) ∧
      barPt A ≫ sA = ((𝔛.Meta).pointEquivPlace.symm W).1 ≫ 𝔛.eeta ≫
        (pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
          (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO]) :
          pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO) := by

  haveI : IsProper (toBase p (ΓM M H) hj) := 𝔛.isProper
  haveI : IsProper (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI : UniversallyClosed (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) := inferInstance
  have hE : ValuativeCriterion.Existence (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) := by
      rw [← UniversallyClosed.eq_valuativeCriterion]; infer_instance
    exact h.1

  have hsub : algebraMap (↥A) (AlgebraicClosure ℚ) = A.subtype := RingHom.ext fun _ => rfl
  let y := (𝔛.Meta).pointEquivPlace.symm W
  let prJ : pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) ⟶ XO (ΓM M H) hj ρO :=
    pullback.map (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO)) (𝟙 _) (Spec.map (CommRingCat.ofHom jO)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hjO])
  have hprJ : prJ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom jO) := pullback.lift_snd _ _ _
  let i₁ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ XO (ΓM M H) hj ρO := y.1 ≫ 𝔛.eeta ≫ prJ
  have hsq : CommSq i₁ (Spec.map (CommRingCat.ofHom (algebraMap (↥A) (AlgebraicClosure ℚ))))
      (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom ιA)) := by
    refine ⟨?_⟩
    show (y.1 ≫ 𝔛.eeta ≫ prJ) ≫ pullback.snd _ _ = _
    rw [Category.assoc, Category.assoc, hprJ, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc, y.2, Category.id_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hsub, hιA]
  let S : ValuativeCommSq (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρO))) :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := i₁, i₂ := Spec.map (CommRingCat.ofHom ιA), commSq := hsq }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hE S).exists_lift
  refine ⟨l, hl₂, ?_⟩
  show barPt A ≫ l = y.1 ≫ 𝔛.eeta ≫ prJ
  rw [show barPt A = Spec.map (CommRingCat.ofHom (algebraMap (↥A) (AlgebraicClosure ℚ))) by rw [hsub]]
  exact hl₁

end S_ModularCurve_XHDRModelAtP_exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_section_comp_snd_eq_barPt_comp_eq_pointEquivPlace_symm (solution)
