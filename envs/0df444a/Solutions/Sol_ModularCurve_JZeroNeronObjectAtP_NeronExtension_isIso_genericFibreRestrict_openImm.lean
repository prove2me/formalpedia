-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.isIso_genericFibreRestrict_openImm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/cfa2ffc1-841f-59dc-8cbb-fcb985aebe0a

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_AlgebraicGeometry_isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    IsIso (NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) F.gN
      (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) F.openImm).1 := by
  haveI : IsDiscreteValuationRing ↥(shRing A) :=
    (ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA).1
  have hb : NeronModelPropertyBundle ↥(shRing A) ↥(invField A) F.gN := F.hN
  haveI : LocallyOfFiniteType F.gN := hb.locallyOfFiniteType
  haveI : IsOpenImmersion F.openImm.1 := F.openImm_isOpenImmersion

  have hring : Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫
      specGenericFibreInclusion ↥(shRing A) ↥(invField A) = barPt A ≫ shPt A := by
    rw [specGenericFibreInclusion_eq, ← Spec.map_comp, ← Spec.map_comp]
    rfl

  have heq := NeronModelInfra.genericFibreRestrict_coe_eq_pullbackMap (K := ↥(invField A)) F.gN (RelativeGroupLaw.baseChangeStr Λ.shStr O.g)
    F.openImm (by rw [Category.comp_id]; exact F.openImm.2.symm) (by rw [Category.comp_id, Category.id_comp])
  haveI : IsOpenImmersion (NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) F.gN
      (RelativeGroupLaw.baseChangeStr Λ.shStr O.g) F.openImm).1 := by
    rw [heq]; infer_instance
  refine isIso_of_isOpenImmersion_of_forall_exists_comp_eq_of_isAlgClosed (Ω := AlgebraicClosure ℚ)
    (Limits.pullback.snd F.gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) _ (fun y hy => ?_)

  have hpt : (y ≫ Limits.pullback.fst F.gN (specGenericFibreInclusion ↥(shRing A) ↥(invField A))) ≫ F.gN = barPt A ≫ shPt A := by
    rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hy, hring]

  obtain ⟨x₀, hx₀⟩ := F.openImm_pts_surjective ⟨_, hpt⟩
  have hx₀' := congrArg Subtype.val hx₀
  rw [NeronModelInfra.schemeHomOverComp_coe] at hx₀'
  refine ⟨Limits.pullback.lift (Λ.shGenLift (O.pts x₀)).1
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ)))) ?_, ?_⟩
  · rw [(Λ.shGenLift (O.pts x₀)).2, hring]
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, NeronModelInfra.genericFibreRestrict_coe_comp_fst, ← Category.assoc, Limits.pullback.lift_fst, hx₀']
    · rw [Category.assoc, NeronModelInfra.genericFibreRestrict_coe_comp_snd, Limits.pullback.lift_snd, hy]

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm (solution)
