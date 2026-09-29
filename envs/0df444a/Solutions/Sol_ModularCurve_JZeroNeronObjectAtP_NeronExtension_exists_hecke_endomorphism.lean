-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.NeronExtension.exists_hecke_endomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/90fc0c43-ac0f-5bc1-9451-903ade1ef2e5

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_NeronExtension
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_NeronExtension_isIso_genericFibreRestrict_openImm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 6400000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (F : O.NeronExtension) :
    letI := heckeModuleBar (N₀ * p)
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver F.gN F.gN, ∀ x : JZero (N₀ * p), (F.ptsN (t • x)).1 = (F.ptsN x).1 ≫ φ.1 := by
  letI := heckeModuleBar (N₀ * p)
  intro t

  haveI : IsDiscreteValuationRing ↥(shRing A) :=
    (ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn A p hA).1
  have hb : NeronModelPropertyBundle ↥(shRing A) ↥(invField A) F.gN := F.hN

  set ι := specGenericFibreInclusion ↥(shRing A) ↥(invField A) with hι
  set g' := RelativeGroupLaw.baseChangeStr Λ.shStr O.g with hg'

  set eK := NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) F.gN g' F.openImm with heK
  haveI : IsIso eK.1 := NeronExtension.isIso_genericFibreRestrict_openImm N₀ p hpN₀ A hA Λ O F

  obtain ⟨φ₀, -, hφ₀⟩ := O.hecke t
  let φ₀' : SchemeHomOver g' g' :=
    ⟨Limits.pullback.lift (Limits.pullback.fst O.g Λ.shStr ≫ φ₀.1) (Limits.pullback.snd O.g Λ.shStr)
        (by rw [Category.assoc, φ₀.2, Limits.pullback.condition]), Limits.pullback.lift_snd _ _ _⟩
  have hφ₀'fst : φ₀'.1 ≫ Limits.pullback.fst O.g Λ.shStr = Limits.pullback.fst O.g Λ.shStr ≫ φ₀.1 := Limits.pullback.lift_fst _ _ _
  have hφ₀'snd : φ₀'.1 ≫ Limits.pullback.snd O.g Λ.shStr = Limits.pullback.snd O.g Λ.shStr := Limits.pullback.lift_snd _ _ _
  let φ₀'K := NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) g' g' φ₀'
  have hsnd : inv eK.1 ≫ Limits.pullback.snd g' ι = Limits.pullback.snd F.gN ι := by
    rw [IsIso.inv_comp_eq, eK.2]
  let ψK : SchemeHomOver (Limits.pullback.snd F.gN ι) (Limits.pullback.snd F.gN ι) :=
    ⟨inv eK.1 ≫ φ₀'K.1 ≫ eK.1, by rw [Category.assoc, Category.assoc, eK.2, φ₀'K.2, hsnd]⟩

  obtain ⟨φ, hφ⟩ := (hb.neronMapping F.Nfull F.gN hb.smooth).2 ψK
  refine ⟨φ, fun x => ?_⟩

  have hring : Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) ≫ ι = barPt A ≫ shPt A := by
    rw [hι, specGenericFibreInclusion_eq, ← Spec.map_comp, ← Spec.map_comp]
    rfl

  let LG : JZero (N₀ * p) → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Limits.pullback g' ι) := fun y =>
    Limits.pullback.lift (Λ.shGenLift (O.pts y)).1 (Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))))
      (by rw [(Λ.shGenLift (O.pts y)).2, hring])
  have hLGfst : ∀ y, LG y ≫ Limits.pullback.fst g' ι = (Λ.shGenLift (O.pts y)).1 := fun y => Limits.pullback.lift_fst _ _ _
  have hLGsnd : ∀ y, LG y ≫ Limits.pullback.snd g' ι =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(invField A) (AlgebraicClosure ℚ))) := fun y => Limits.pullback.lift_snd _ _ _

  have hc : ∀ y, (F.ptsN y).1 = LG y ≫ eK.1 ≫ Limits.pullback.fst F.gN ι := fun y => by
    rw [heK, NeronModelInfra.genericFibreRestrict_coe_comp_fst, ← Category.assoc, hLGfst]
    rfl

  have hshGen : ∀ y, (Λ.shGenLift (O.pts y)).1 = Limits.pullback.lift (O.pts y).1 (barPt A ≫ shPt A)
      (by rw [(O.pts y).2]; exact Λ.barPt_shPt_shStr.symm) := fun y => rfl
  have hd : (Λ.shGenLift (O.pts x)).1 ≫ φ₀'.1 = (Λ.shGenLift (O.pts (t • x))).1 := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hφ₀'fst, hshGen, hshGen, Limits.pullback.lift_fst, ← Category.assoc, Limits.pullback.lift_fst]
      exact (hφ₀ x).symm
    · rw [Category.assoc, hφ₀'snd, hshGen, hshGen, Limits.pullback.lift_snd, Limits.pullback.lift_snd]

  have he : LG x ≫ φ₀'K.1 = LG (t • x) := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, NeronModelInfra.genericFibreRestrict_coe_comp_fst, ← Category.assoc, hLGfst, hd, hLGfst]
    · rw [Category.assoc, NeronModelInfra.genericFibreRestrict_coe_comp_snd, hLGsnd, hLGsnd]

  have hφ1 : (NeronModelInfra.genericFibreRestrict ↥(shRing A) ↥(invField A) F.gN F.gN φ).1 = ψK.1 := by rw [hφ]
  calc (F.ptsN (t • x)).1 = LG (t • x) ≫ eK.1 ≫ Limits.pullback.fst F.gN ι := hc _
    _ = LG x ≫ φ₀'K.1 ≫ eK.1 ≫ Limits.pullback.fst F.gN ι := by rw [← Category.assoc (LG x), he]
    _ = LG x ≫ eK.1 ≫ ψK.1 ≫ Limits.pullback.fst F.gN ι := by
        show _ = LG x ≫ eK.1 ≫ (inv eK.1 ≫ φ₀'K.1 ≫ eK.1) ≫ Limits.pullback.fst F.gN ι
        simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    _ = (F.ptsN x).1 ≫ φ.1 := by
        rw [hc x, ← hφ1, Category.assoc, Category.assoc, NeronModelInfra.genericFibreRestrict_coe_comp_fst]

end S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_NeronExtension_exists_hecke_endomorphism (solution)
