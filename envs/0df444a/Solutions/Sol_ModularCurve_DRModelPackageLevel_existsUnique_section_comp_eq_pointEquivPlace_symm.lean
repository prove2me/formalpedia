-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b4afe06d-d5b0-511f-b19f-321ea59900cb

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing ModularCurve ModularCurve.DRLevel

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

namespace KcG1a

end KcG1a

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) :
    ∃! s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
          pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) := by
  haveI : IsProper (toBase N₀ p) := 𝔓.isProper
  have hVC : ValuativeCriterion (toBase N₀ p) := by
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) (toBase N₀ p) := by
      rw [← IsProper.eq_valuativeCriterion]; infer_instance
    exact h.1.1.1

  have halg : (algebraMap ↥A (AlgebraicClosure ℚ)) = A.subtype := rfl
  set pt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X N₀ p :=
    ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
      pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) with hpt
  have hsq : CommSq pt (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) (toBase N₀ p)
      (Spec.map (CommRingCat.ofHom ρ)) := by
    constructor
    rw [hpt, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta,
      ← Category.assoc, ((𝔓.Meta.pointEquivPlace).symm V).2, Category.id_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, halg, hρ]
  let S : ValuativeCommSq (toBase N₀ p) :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := pt, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨hU⟩ := hVC S
  let L : hsq.LiftStruct := (default : S.commSq.LiftStruct)
  refine ⟨⟨L.l, L.fac_right⟩, ?_, ?_⟩
  · show Spec.map (CommRingCat.ofHom A.subtype) ≫ L.l = pt
    rw [← halg]; exact L.fac_left
  · rintro ⟨s, hs⟩ hs'
    have hL' : (⟨s, by rw [← halg] at hs'; exact hs', hs⟩ : S.commSq.LiftStruct) = L := Subsingleton.elim _ _
    exact Subtype.ext (congrArg CommSq.LiftStruct.l hL')

end S_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm (solution)
