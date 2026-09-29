-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ca4a5c24-bc39-576e-a0fc-226f2577de93

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (x : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ X p (ΓM M H) hj)
    (hx : x ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) :
    ∃! s : Spec (CommRingCat.of ↥A) ⟶ X p (ΓM M H) hj,
      s ≫ toBase p (ΓM M H) hj = Spec.map (CommRingCat.ofHom ρ) ∧
        Spec.map (CommRingCat.ofHom A.subtype) ≫ s = x := by

  haveI := 𝔛.isProper
  have hval : ValuativeCriterion (toBase p (ΓM M H) hj) := by
    have h := (congrFun (congrFun (congrFun AlgebraicGeometry.IsProper.eq_valuativeCriterion
      (X p (ΓM M H) hj)) (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj))
    have hP : IsProper (toBase p (ΓM M H) hj) := inferInstance
    rw [h] at hP
    exact hP.1.1.1

  have halg : algebraMap ↥A (AlgebraicClosure ℚ) = A.subtype := rfl
  have hsq : CommSq x (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))))
      (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) := ⟨by
    rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, halg, hρ]⟩
  let S : ValuativeCommSq (toBase p (ΓM M H) hj) :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := hsq }
  obtain ⟨huniq⟩ := hval S
  let l := (default : S.commSq.LiftStruct)
  refine ⟨l.l, ⟨l.fac_right, ?_⟩, ?_⟩
  · exact l.fac_left
  · rintro s ⟨hs₁, hs₂⟩
    have hs₂' : Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ))) ≫ s = x := hs₂
    have : (⟨s, hs₂', hs₁⟩ : S.commSq.LiftStruct) = l := Subsingleton.elim _ _
    exact congrArg CommSq.LiftStruct.l this

#print axioms solution

end S_ModularCurve_XHDRModelAtP_existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_existsUnique_hom_comp_toBase_eq_and_specMap_comp_eq_of_point (solution)
