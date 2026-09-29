-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2007dc17-a099-59ee-b889-111751acc1d5

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (ρ : baseRing p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (baseRing p) (AlgebraicClosure ℚ))
    {X : Scheme.{0}} (f : X ⟶ base p) [IsProper f] (x : SchemeHomOver (genPt p) f) :
    ∃ xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, barPt A ≫ xA.1 = x.1 := by

  have hE : ValuativeCriterion.Existence f := by
    have hUC : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hUC
    exact hUC.1

  have hsq : x.1 ≫ f = Spec.map (CommRingCat.ofHom (algebraMap (↥A) (AlgebraicClosure ℚ))) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) hρ.symm
  let S : ValuativeCommSq f :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := x.1, i₂ := Spec.map (CommRingCat.ofHom ρ), commSq := ⟨hsq⟩ }
  haveI : S.commSq.HasLift := hE S
  exact ⟨⟨S.commSq.lift, S.commSq.fac_right⟩, S.commSq.fac_left⟩

end S_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper (solution)
